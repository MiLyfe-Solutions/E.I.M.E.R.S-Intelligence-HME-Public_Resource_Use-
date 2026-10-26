import V185TrunkScan21Chunk155

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_1901825 : List Nat := [1, 2, 4, 1, 1, 4, 8]
def baseStart_1901825 : Nat := 118140960795 + 1901825 * 2 ^ 59
def prefixEnd_1901825 : Nat := 4983230072969 + 3 ^ 40 * 1901825 * 2
def baseEnd_1901825 : Nat := 48224708431463053562527

theorem tailTrace_1901825 : CollatzResearch.WordTrace tailWord_1901825 prefixEnd_1901825 48224708431463053562527 := by
  unfold tailWord_1901825
  simp only [CollatzResearch.WordTrace]
  refine ⟨69365256335020305695994929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46243504223346870463996619 69365256335020305695994929)
  ·
    refine ⟨52023942251265229271996197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69365256335020305695994929 52023942251265229271996197)
    ·
      refine ⟨9754489172112230488499287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52023942251265229271996197 9754489172112230488499287)
      ·
        refine ⟨14631733758168345732748931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9754489172112230488499287 14631733758168345732748931)
        ·
          refine ⟨21947600637252518599123397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14631733758168345732748931 21947600637252518599123397)
          ·
            refine ⟨4115175119484847237335637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21947600637252518599123397 4115175119484847237335637)
            ·
              refine ⟨48224708431463053562527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4115175119484847237335637 48224708431463053562527)
              ·
                rfl

theorem cell21_1901825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 8].length) (baseStart_1901825 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1901825 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1901825 prefixEnd_1901825 := by exact prefixLift 1901825
  have htrace : WordTrace (prefixWord ++ tailWord_1901825) baseStart_1901825 baseEnd_1901825 := by
    simpa [prefixWord, tailWord_1901825, baseEnd_1901825] using wordTrace_append hprefix tailTrace_1901825
  have hstable : (prefixWord ++ tailWord_1901825).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901825).length < 2 ^ (prefixWord ++ tailWord_1901825).sum := by decide
  have hdescent : baseEnd_1901825 < baseStart_1901825 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901828 : List Nat := [2, 3, 2, 2, 2, 1, 3, 2, 4]
def baseStart_1901828 : Nat := 118140960795 + 1901828 * 2 ^ 59
def prefixEnd_1901828 : Nat := 4983230072969 + 3 ^ 40 * 1901828 * 2
def baseEnd_1901828 : Nat := 434023060524040143512737

theorem tailTrace_1901828 : CollatzResearch.WordTrace tailWord_1901828 prefixEnd_1901828 434023060524040143512737 := by
  unfold tailWord_1901828
  simp only [CollatzResearch.WordTrace]
  refine ⟨34682682877004718604177069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46243577169339624805569425 34682682877004718604177069)
  ·
    refine ⟨13006006078876769476566401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34682682877004718604177069 13006006078876769476566401)
    ·
      refine ⟨9754504559157577107424801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13006006078876769476566401 9754504559157577107424801)
      ·
        refine ⟨7315878419368182830568601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9754504559157577107424801 7315878419368182830568601)
        ·
          refine ⟨5486908814526137122926451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7315878419368182830568601 5486908814526137122926451)
          ·
            refine ⟨8230363221789205684389677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5486908814526137122926451 8230363221789205684389677)
            ·
              refine ⟨3086386208170952131646129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8230363221789205684389677 3086386208170952131646129)
              ·
                refine ⟨2314789656128214098734597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3086386208170952131646129 2314789656128214098734597)
                ·
                  refine ⟨434023060524040143512737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2314789656128214098734597 434023060524040143512737)
                  ·
                    rfl

theorem cell21_1901828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 3, 2, 4].length) (baseStart_1901828 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1901828 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1901828 prefixEnd_1901828 := by exact prefixLift 1901828
  have htrace : WordTrace (prefixWord ++ tailWord_1901828) baseStart_1901828 baseEnd_1901828 := by
    simpa [prefixWord, tailWord_1901828, baseEnd_1901828] using wordTrace_append hprefix tailTrace_1901828
  have hstable : (prefixWord ++ tailWord_1901828).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901828).length < 2 ^ (prefixWord ++ tailWord_1901828).sum := by decide
  have hdescent : baseEnd_1901828 < baseStart_1901828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901949 : List Nat := [1, 4, 1, 1, 2, 2, 3, 4, 3]
def baseStart_1901949 : Nat := 118140960795 + 1901949 * 2 ^ 59
def prefixEnd_1901949 : Nat := 4983230072969 + 3 ^ 40 * 1901949 * 2
def baseEnd_1901949 : Nat := 434050674372570821995823

theorem tailTrace_1901949 : CollatzResearch.WordTrace tailWord_1901949 prefixEnd_1901949 434050674372570821995823 := by
  unfold tailWord_1901949
  simp only [CollatzResearch.WordTrace]
  refine ⟨69369778986571074873508901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46246519324380716582339267 69369778986571074873508901)
  ·
    refine ⟨13006833559982076538782919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69369778986571074873508901 13006833559982076538782919)
    ·
      refine ⟨19510250339973114808174379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13006833559982076538782919 19510250339973114808174379)
      ·
        refine ⟨29265375509959672212261569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19510250339973114808174379 29265375509959672212261569)
        ·
          refine ⟨21949031632469754159196177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29265375509959672212261569 21949031632469754159196177)
          ·
            refine ⟨16461773724352315619397133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21949031632469754159196177 16461773724352315619397133)
            ·
              refine ⟨6173165146632118357273925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16461773724352315619397133 6173165146632118357273925)
              ·
                refine ⟨1157468464993522191988861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6173165146632118357273925 1157468464993522191988861)
                ·
                  refine ⟨434050674372570821995823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1157468464993522191988861 434050674372570821995823)
                  ·
                    rfl

theorem cell21_1901949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 4, 3].length) (baseStart_1901949 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1901949 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1901949 prefixEnd_1901949 := by exact prefixLift 1901949
  have htrace : WordTrace (prefixWord ++ tailWord_1901949) baseStart_1901949 baseEnd_1901949 := by
    simpa [prefixWord, tailWord_1901949, baseEnd_1901949] using wordTrace_append hprefix tailTrace_1901949
  have hstable : (prefixWord ++ tailWord_1901949).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901949).length < 2 ^ (prefixWord ++ tailWord_1901949).sum := by decide
  have hdescent : baseEnd_1901949 < baseStart_1901949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901997 : List Nat := [1, 5, 2, 2, 1, 3, 1, 2, 4]
def baseStart_1901997 : Nat := 118140960795 + 1901997 * 2 ^ 59
def prefixEnd_1901997 : Nat := 4983230072969 + 3 ^ 40 * 1901997 * 2
def baseEnd_1901997 : Nat := 434061628626533405195725

theorem tailTrace_1901997 : CollatzResearch.WordTrace tailWord_1901997 prefixEnd_1901997 434061628626533405195725 := by
  unfold tailWord_1901997
  simp only [CollatzResearch.WordTrace]
  refine ⟨69371529690397179071256245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46247686460264786047504163 69371529690397179071256245)
  ·
    refine ⟨6503580908474735537930273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 69371529690397179071256245 6503580908474735537930273)
    ·
      refine ⟨4877685681356051653447705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6503580908474735537930273 4877685681356051653447705)
      ·
        refine ⟨3658264261017038740085779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4877685681356051653447705 3658264261017038740085779)
        ·
          refine ⟨5487396391525558110128669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3658264261017038740085779 5487396391525558110128669)
          ·
            refine ⟨2057773646822084291298251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5487396391525558110128669 2057773646822084291298251)
            ·
              refine ⟨3086660470233126436947377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2057773646822084291298251 3086660470233126436947377)
              ·
                refine ⟨2314995352674844827710533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3086660470233126436947377 2314995352674844827710533)
                ·
                  refine ⟨434061628626533405195725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2314995352674844827710533 434061628626533405195725)
                  ·
                    rfl

theorem cell21_1901997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 1, 2, 4].length) (baseStart_1901997 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1901997 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1901997 prefixEnd_1901997 := by exact prefixLift 1901997
  have htrace : WordTrace (prefixWord ++ tailWord_1901997) baseStart_1901997 baseEnd_1901997 := by
    simpa [prefixWord, tailWord_1901997, baseEnd_1901997] using wordTrace_append hprefix tailTrace_1901997
  have hstable : (prefixWord ++ tailWord_1901997).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901997).length < 2 ^ (prefixWord ++ tailWord_1901997).sum := by decide
  have hdescent : baseEnd_1901997 < baseStart_1901997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1902042 : List Nat := [3, 1, 1, 2, 3, 4, 1, 3, 3]
def baseStart_1902042 : Nat := 118140960795 + 1902042 * 2 ^ 59
def prefixEnd_1902042 : Nat := 4983230072969 + 3 ^ 40 * 1902042 * 2
def baseEnd_1902042 : Nat := 434071898239623326945633

theorem tailTrace_1902042 : CollatzResearch.WordTrace tailWord_1902042 prefixEnd_1902042 434071898239623326945633 := by
  unfold tailWord_1902042
  simp only [CollatzResearch.WordTrace]
  refine ⟨17343292743808537939161095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46248780650156101171096253 17343292743808537939161095)
  ·
    refine ⟨26014939115712806908741643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17343292743808537939161095 26014939115712806908741643)
    ·
      refine ⟨39022408673569210363112465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26014939115712806908741643 39022408673569210363112465)
      ·
        refine ⟨29266806505176907772334349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39022408673569210363112465 29266806505176907772334349)
        ·
          refine ⟨10975052439441340414625381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29266806505176907772334349 10975052439441340414625381)
          ·
            refine ⟨2057822332395251327742259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10975052439441340414625381 2057822332395251327742259)
            ·
              refine ⟨3086733498592876991613389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2057822332395251327742259 3086733498592876991613389)
              ·
                refine ⟨1157525061972328871855021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3086733498592876991613389 1157525061972328871855021)
                ·
                  refine ⟨434071898239623326945633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1157525061972328871855021 434071898239623326945633)
                  ·
                    rfl

theorem cell21_1902042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 1, 3, 3].length) (baseStart_1902042 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1902042 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1902042 prefixEnd_1902042 := by exact prefixLift 1902042
  have htrace : WordTrace (prefixWord ++ tailWord_1902042) baseStart_1902042 baseEnd_1902042 := by
    simpa [prefixWord, tailWord_1902042, baseEnd_1902042] using wordTrace_append hprefix tailTrace_1902042
  have hstable : (prefixWord ++ tailWord_1902042).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1902042).length < 2 ^ (prefixWord ++ tailWord_1902042).sum := by decide
  have hdescent : baseEnd_1902042 < baseStart_1902042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1902042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1902053 : List Nat := [1, 3, 1, 5, 1, 1, 9]
def baseStart_1902053 : Nat := 118140960795 + 1902053 * 2 ^ 59
def prefixEnd_1902053 : Nat := 4983230072969 + 3 ^ 40 * 1902053 * 2
def baseEnd_1902053 : Nat := 48230489843276639140253

theorem tailTrace_1902053 : CollatzResearch.WordTrace tailWord_1902053 prefixEnd_1902053 48230489843276639140253 := by
  unfold tailWord_1902053
  simp only [CollatzResearch.WordTrace]
  refine ⟨69373572178194300635294813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46249048118796200423529875 69373572178194300635294813)
  ·
    refine ⟨26015089566822862738235555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69373572178194300635294813 26015089566822862738235555)
    ·
      refine ⟨39022634350234294107353333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26015089566822862738235555 39022634350234294107353333)
      ·
        refine ⟨3658371970334465072564375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39022634350234294107353333 3658371970334465072564375)
        ·
          refine ⟨5487557955501697608846563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3658371970334465072564375 5487557955501697608846563)
          ·
            refine ⟨8231336933252546413269845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5487557955501697608846563 8231336933252546413269845)
            ·
              refine ⟨48230489843276639140253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8231336933252546413269845 48230489843276639140253)
              ·
                rfl

theorem cell21_1902053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 9].length) (baseStart_1902053 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1902053 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1902053 prefixEnd_1902053 := by exact prefixLift 1902053
  have htrace : WordTrace (prefixWord ++ tailWord_1902053) baseStart_1902053 baseEnd_1902053 := by
    simpa [prefixWord, tailWord_1902053, baseEnd_1902053] using wordTrace_append hprefix tailTrace_1902053
  have hstable : (prefixWord ++ tailWord_1902053).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1902053).length < 2 ^ (prefixWord ++ tailWord_1902053).sum := by decide
  have hdescent : baseEnd_1902053 < baseStart_1902053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1902053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1902067 : List Nat := [1, 1, 1, 2, 2, 2, 2, 5, 5]
def baseStart_1902067 : Nat := 118140960795 + 1902067 * 2 ^ 59
def prefixEnd_1902067 : Nat := 4983230072969 + 3 ^ 40 * 1902067 * 2
def baseEnd_1902067 : Nat := 434077603580228839028915

theorem tailTrace_1902067 : CollatzResearch.WordTrace tailWord_1902067 prefixEnd_1902067 434077603580228839028915 := by
  unfold tailWord_1902067
  simp only [CollatzResearch.WordTrace]
  refine ⟨69374082800143581026304455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46249388533429054017536303 69374082800143581026304455)
  ·
    refine ⟨104061124200215371539456683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69374082800143581026304455 104061124200215371539456683)
    ·
      refine ⟨156091686300323057309185025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104061124200215371539456683 156091686300323057309185025)
      ·
        refine ⟨117068764725242292981888769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156091686300323057309185025 117068764725242292981888769)
        ·
          refine ⟨87801573543931719736416577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117068764725242292981888769 87801573543931719736416577)
          ·
            refine ⟨65851180157948789802312433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87801573543931719736416577 65851180157948789802312433)
            ·
              refine ⟨49388385118461592351734325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65851180157948789802312433 49388385118461592351734325)
              ·
                refine ⟨4630161104855774282975093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49388385118461592351734325 4630161104855774282975093)
                ·
                  refine ⟨434077603580228839028915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4630161104855774282975093 434077603580228839028915)
                  ·
                    rfl

theorem cell21_1902067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 5, 5].length) (baseStart_1902067 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1902067 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1902067 prefixEnd_1902067 := by exact prefixLift 1902067
  have htrace : WordTrace (prefixWord ++ tailWord_1902067) baseStart_1902067 baseEnd_1902067 := by
    simpa [prefixWord, tailWord_1902067, baseEnd_1902067] using wordTrace_append hprefix tailTrace_1902067
  have hstable : (prefixWord ++ tailWord_1902067).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1902067).length < 2 ^ (prefixWord ++ tailWord_1902067).sum := by decide
  have hdescent : baseEnd_1902067 < baseStart_1902067 := by decide
  rcases family_descends (prefixWord ++ tailWord_1902067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1902070 : List Nat := [5, 1, 1, 1, 2, 3, 2, 6]
def baseStart_1902070 : Nat := 118140960795 + 1902070 * 2 ^ 59
def prefixEnd_1902070 : Nat := 4983230072969 + 3 ^ 40 * 1902070 * 2
def baseEnd_1902070 : Nat := 144692762740367166826303

theorem tailTrace_1902070 : CollatzResearch.WordTrace tailWord_1902070 prefixEnd_1902070 144692762740367166826303 := by
  unfold tailWord_1902070
  simp only [CollatzResearch.WordTrace]
  refine ⟨4335887013695794533666479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46249461479421808359109109 4335887013695794533666479)
  ·
    refine ⟨6503830520543691800499719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4335887013695794533666479 6503830520543691800499719)
    ·
      refine ⟨9755745780815537700749579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6503830520543691800499719 9755745780815537700749579)
      ·
        refine ⟨14633618671223306551124369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9755745780815537700749579 14633618671223306551124369)
        ·
          refine ⟨10975214003417479913343277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14633618671223306551124369 10975214003417479913343277)
          ·
            refine ⟨4115705251281554967503729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10975214003417479913343277 4115705251281554967503729)
            ·
              refine ⟨3086778938461166225627797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4115705251281554967503729 3086778938461166225627797)
              ·
                refine ⟨144692762740367166826303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3086778938461166225627797 144692762740367166826303)
                ·
                  rfl

theorem cell21_1902070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 2, 6].length) (baseStart_1902070 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1902070 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1902070 prefixEnd_1902070 := by exact prefixLift 1902070
  have htrace : WordTrace (prefixWord ++ tailWord_1902070) baseStart_1902070 baseEnd_1902070 := by
    simpa [prefixWord, tailWord_1902070, baseEnd_1902070] using wordTrace_append hprefix tailTrace_1902070
  have hstable : (prefixWord ++ tailWord_1902070).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1902070).length < 2 ^ (prefixWord ++ tailWord_1902070).sum := by decide
  have hdescent : baseEnd_1902070 < baseStart_1902070 := by decide
  rcases family_descends (prefixWord ++ tailWord_1902070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1902110 : List Nat := [4, 3, 3, 1, 1, 2, 2, 2, 3]
def baseStart_1902110 : Nat := 118140960795 + 1902110 * 2 ^ 59
def prefixEnd_1902110 : Nat := 4983230072969 + 3 ^ 40 * 1902110 * 2
def baseEnd_1902110 : Nat := 434087416766070319812161

theorem tailTrace_1902110 : CollatzResearch.WordTrace tailWord_1902110 prefixEnd_1902110 434087416766070319812161 := by
  unfold tailWord_1902110
  simp only [CollatzResearch.WordTrace]
  refine ⟨8671956392373474921264973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46250434092658532913413189 8671956392373474921264973)
  ·
    refine ⟨3251983647140053095474365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8671956392373474921264973 3251983647140053095474365)
    ·
      refine ⟨1219493867677519910802887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3251983647140053095474365 1219493867677519910802887)
      ·
        refine ⟨1829240801516279866204331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1219493867677519910802887 1829240801516279866204331)
        ·
          refine ⟨2743861202274419799306497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1829240801516279866204331 2743861202274419799306497)
          ·
            refine ⟨2057895901705814849479873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2743861202274419799306497 2057895901705814849479873)
            ·
              refine ⟨1543421926279361137109905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2057895901705814849479873 1543421926279361137109905)
              ·
                refine ⟨1157566444709520852832429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1543421926279361137109905 1157566444709520852832429)
                ·
                  refine ⟨434087416766070319812161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1157566444709520852832429 434087416766070319812161)
                  ·
                    rfl

theorem cell21_1902110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 2, 2, 3].length) (baseStart_1902110 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1902110 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1902110 prefixEnd_1902110 := by exact prefixLift 1902110
  have htrace : WordTrace (prefixWord ++ tailWord_1902110) baseStart_1902110 baseEnd_1902110 := by
    simpa [prefixWord, tailWord_1902110, baseEnd_1902110] using wordTrace_append hprefix tailTrace_1902110
  have hstable : (prefixWord ++ tailWord_1902110).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1902110).length < 2 ^ (prefixWord ++ tailWord_1902110).sum := by decide
  have hdescent : baseEnd_1902110 < baseStart_1902110 := by decide
  rcases family_descends (prefixWord ++ tailWord_1902110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1902143 : List Nat := [1, 1, 2, 2, 3, 3, 1, 1, 7]
def baseStart_1902143 : Nat := 118140960795 + 1902143 * 2 ^ 59
def prefixEnd_1902143 : Nat := 4983230072969 + 3 ^ 40 * 1902143 * 2
def baseEnd_1902143 : Nat := 434094947815669595762093

theorem tailTrace_1902143 : CollatzResearch.WordTrace tailWord_1902143 prefixEnd_1902143 434094947815669595762093 := by
  unfold tailWord_1902143
  simp only [CollatzResearch.WordTrace]
  refine ⟨69376854747868246006071083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46251236498578830670714055 69376854747868246006071083)
  ·
    refine ⟨104065282121802369009106625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69376854747868246006071083 104065282121802369009106625)
    ·
      refine ⟨78048961591351776756829969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104065282121802369009106625 78048961591351776756829969)
      ·
        refine ⟨58536721193513832567622477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78048961591351776756829969 58536721193513832567622477)
        ·
          refine ⟨21951270447567687212858429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58536721193513832567622477 21951270447567687212858429)
          ·
            refine ⟨8231726417837882704821911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21951270447567687212858429 8231726417837882704821911)
            ·
              refine ⟨12347589626756824057232867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8231726417837882704821911 12347589626756824057232867)
              ·
                refine ⟨18521384440135236085849301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12347589626756824057232867 18521384440135236085849301)
                ·
                  refine ⟨434094947815669595762093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18521384440135236085849301 434094947815669595762093)
                  ·
                    rfl

theorem cell21_1902143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 1, 7].length) (baseStart_1902143 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1902143 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1902143 prefixEnd_1902143 := by exact prefixLift 1902143
  have htrace : WordTrace (prefixWord ++ tailWord_1902143) baseStart_1902143 baseEnd_1902143 := by
    simpa [prefixWord, tailWord_1902143, baseEnd_1902143] using wordTrace_append hprefix tailTrace_1902143
  have hstable : (prefixWord ++ tailWord_1902143).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1902143).length < 2 ^ (prefixWord ++ tailWord_1902143).sum := by decide
  have hdescent : baseEnd_1902143 < baseStart_1902143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1902143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1902188 : List Nat := [2, 2, 1, 1, 3, 1, 1, 10]
def baseStart_1902188 : Nat := 118140960795 + 1902188 * 2 ^ 59
def prefixEnd_1902188 : Nat := 4983230072969 + 3 ^ 40 * 1902188 * 2
def baseEnd_1902188 : Nat := 144701739142919839170667

theorem tailTrace_1902188 : CollatzResearch.WordTrace tailWord_1902188 prefixEnd_1902188 144701739142919839170667 := by
  unfold tailWord_1902188
  simp only [CollatzResearch.WordTrace]
  refine ⟨34689248016352609345729609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46252330688470145794306145 34689248016352609345729609)
  ·
    refine ⟨26016936012264457009297207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34689248016352609345729609 26016936012264457009297207)
    ·
      refine ⟨39025404018396685513945811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26016936012264457009297207 39025404018396685513945811)
      ·
        refine ⟨58538106027595028270918717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39025404018396685513945811 58538106027595028270918717)
        ·
          refine ⟨21951789760348135601594519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58538106027595028270918717 21951789760348135601594519)
          ·
            refine ⟨32927684640522203402391779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21951789760348135601594519 32927684640522203402391779)
            ·
              refine ⟨49391526960783305103587669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32927684640522203402391779 49391526960783305103587669)
              ·
                refine ⟨144701739142919839170667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 49391526960783305103587669 144701739142919839170667)
                ·
                  rfl

theorem cell21_1902188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 10].length) (baseStart_1902188 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1902188 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1902188 prefixEnd_1902188 := by exact prefixLift 1902188
  have htrace : WordTrace (prefixWord ++ tailWord_1902188) baseStart_1902188 baseEnd_1902188 := by
    simpa [prefixWord, tailWord_1902188, baseEnd_1902188] using wordTrace_append hprefix tailTrace_1902188
  have hstable : (prefixWord ++ tailWord_1902188).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1902188).length < 2 ^ (prefixWord ++ tailWord_1902188).sum := by decide
  have hdescent : baseEnd_1902188 < baseStart_1902188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1902188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1902205 : List Nat := [1, 4, 1, 1, 4, 2, 1, 7]
def baseStart_1902205 : Nat := 118140960795 + 1902205 * 2 ^ 59
def prefixEnd_1902205 : Nat := 4983230072969 + 3 ^ 40 * 1902205 * 2
def baseEnd_1902205 : Nat := 144703032353457088576211

theorem tailTrace_1902205 : CollatzResearch.WordTrace tailWord_1902205 prefixEnd_1902205 144703032353457088576211 := by
  unfold tailWord_1902205
  simp only [CollatzResearch.WordTrace]
  refine ⟨69379116073643630594828069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46252744049095753729885379 69379116073643630594828069)
  ·
    refine ⟨13008584263808180736530263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69379116073643630594828069 13008584263808180736530263)
    ·
      refine ⟨19512876395712271104795395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13008584263808180736530263 19512876395712271104795395)
      ·
        refine ⟨29269314593568406657193093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19512876395712271104795395 29269314593568406657193093)
        ·
          refine ⟨5487996486294076248223705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29269314593568406657193093 5487996486294076248223705)
          ·
            refine ⟨4115997364720557186167779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5487996486294076248223705 4115997364720557186167779)
            ·
              refine ⟨6173996047080835779251669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4115997364720557186167779 6173996047080835779251669)
              ·
                refine ⟨144703032353457088576211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6173996047080835779251669 144703032353457088576211)
                ·
                  rfl

theorem cell21_1902205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 7].length) (baseStart_1902205 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1902205 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1902205 prefixEnd_1902205 := by exact prefixLift 1902205
  have htrace : WordTrace (prefixWord ++ tailWord_1902205) baseStart_1902205 baseEnd_1902205 := by
    simpa [prefixWord, tailWord_1902205, baseEnd_1902205] using wordTrace_append hprefix tailTrace_1902205
  have hstable : (prefixWord ++ tailWord_1902205).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1902205).length < 2 ^ (prefixWord ++ tailWord_1902205).sum := by decide
  have hdescent : baseEnd_1902205 < baseStart_1902205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1902205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1902242 : List Nat := [3, 3, 1, 4, 1, 2, 2, 1, 4]
def baseStart_1902242 : Nat := 118140960795 + 1902242 * 2 ^ 59
def prefixEnd_1902242 : Nat := 4983230072969 + 3 ^ 40 * 1902242 * 2
def baseEnd_1902242 : Nat := 434117540964467423611891

theorem tailTrace_1902242 : CollatzResearch.WordTrace tailWord_1902242 prefixEnd_1902242 434117540964467423611891 := by
  unfold tailWord_1902242
  simp only [CollatzResearch.WordTrace]
  refine ⟨17345116393627396478481245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46253643716339723942616653 17345116393627396478481245)
  ·
    refine ⟨6504418647610273679430467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17345116393627396478481245 6504418647610273679430467)
    ·
      refine ⟨9756627971415410519145701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6504418647610273679430467 9756627971415410519145701)
      ·
        refine ⟨1829367744640389472339819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9756627971415410519145701 1829367744640389472339819)
        ·
          refine ⟨2744051616960584208509729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1829367744640389472339819 2744051616960584208509729)
          ·
            refine ⟨2058038712720438156382297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2744051616960584208509729 2058038712720438156382297)
            ·
              refine ⟨1543529034540328617286723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2058038712720438156382297 1543529034540328617286723)
              ·
                refine ⟨2315293551810492925930085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1543529034540328617286723 2315293551810492925930085)
                ·
                  refine ⟨434117540964467423611891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2315293551810492925930085 434117540964467423611891)
                  ·
                    rfl

theorem cell21_1902242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 2, 1, 4].length) (baseStart_1902242 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1902242 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1902242 prefixEnd_1902242 := by exact prefixLift 1902242
  have htrace : WordTrace (prefixWord ++ tailWord_1902242) baseStart_1902242 baseEnd_1902242 := by
    simpa [prefixWord, tailWord_1902242, baseEnd_1902242] using wordTrace_append hprefix tailTrace_1902242
  have hstable : (prefixWord ++ tailWord_1902242).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1902242).length < 2 ^ (prefixWord ++ tailWord_1902242).sum := by decide
  have hdescent : baseEnd_1902242 < baseStart_1902242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1902242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1902284 : List Nat := [2, 2, 1, 5, 2, 1, 2, 2, 4]
def baseStart_1902284 : Nat := 118140960795 + 1902284 * 2 ^ 59
def prefixEnd_1902284 : Nat := 4983230072969 + 3 ^ 40 * 1902284 * 2
def baseEnd_1902284 : Nat := 434127125936684683911805

theorem tailTrace_1902284 : CollatzResearch.WordTrace tailWord_1902284 prefixEnd_1902284 434127125936684683911805 := by
  unfold tailWord_1902284
  simp only [CollatzResearch.WordTrace]
  refine ⟨34690998720178713543476953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46254664960238284724635937 34690998720178713543476953)
  ·
    refine ⟨26018249040134035157607715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34690998720178713543476953 26018249040134035157607715)
    ·
      refine ⟨39027373560201052736411573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26018249040134035157607715 39027373560201052736411573)
      ·
        refine ⟨3658816271268848694038585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39027373560201052736411573 3658816271268848694038585)
        ·
          refine ⟨2744112203451636520528939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3658816271268848694038585 2744112203451636520528939)
          ·
            refine ⟨4116168305177454780793409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2744112203451636520528939 4116168305177454780793409)
            ·
              refine ⟨3087126228883091085595057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4116168305177454780793409 3087126228883091085595057)
              ·
                refine ⟨2315344671662318314196293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3087126228883091085595057 2315344671662318314196293)
                ·
                  refine ⟨434127125936684683911805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2315344671662318314196293 434127125936684683911805)
                  ·
                    rfl

theorem cell21_1902284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 2, 2, 4].length) (baseStart_1902284 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1902284 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1902284 prefixEnd_1902284 := by exact prefixLift 1902284
  have htrace : WordTrace (prefixWord ++ tailWord_1902284) baseStart_1902284 baseEnd_1902284 := by
    simpa [prefixWord, tailWord_1902284, baseEnd_1902284] using wordTrace_append hprefix tailTrace_1902284
  have hstable : (prefixWord ++ tailWord_1902284).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1902284).length < 2 ^ (prefixWord ++ tailWord_1902284).sum := by decide
  have hdescent : baseEnd_1902284 < baseStart_1902284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1902284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1902295 : List Nat := [1, 1, 3, 2, 1, 3, 2, 3, 5]
def baseStart_1902295 : Nat := 118140960795 + 1902295 * 2 ^ 59
def prefixEnd_1902295 : Nat := 4983230072969 + 3 ^ 40 * 1902295 * 2
def baseEnd_1902295 : Nat := 434129636286551109228449

theorem tailTrace_1902295 : CollatzResearch.WordTrace tailWord_1902295 prefixEnd_1902295 434129636286551109228449 := by
  unfold tailWord_1902295
  simp only [CollatzResearch.WordTrace]
  refine ⟨69382398643317575965604339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46254932428878383977069559 69382398643317575965604339)
  ·
    refine ⟨104073597964976363948406509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69382398643317575965604339 104073597964976363948406509)
    ·
      refine ⟨39027599236866136480652441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104073597964976363948406509 39027599236866136480652441)
      ·
        refine ⟨29270699427649602360489331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39027599236866136480652441 29270699427649602360489331)
        ·
          refine ⟨43906049141474403540733997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29270699427649602360489331 43906049141474403540733997)
          ·
            refine ⟨16464768428052901327775249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43906049141474403540733997 16464768428052901327775249)
            ·
              refine ⟨12348576321039675995831437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16464768428052901327775249 12348576321039675995831437)
              ·
                refine ⟨4630716120389878498436789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12348576321039675995831437 4630716120389878498436789)
                ·
                  refine ⟨434129636286551109228449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4630716120389878498436789 434129636286551109228449)
                  ·
                    rfl

theorem cell21_1902295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 3, 5].length) (baseStart_1902295 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1902295 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1902295 prefixEnd_1902295 := by exact prefixLift 1902295
  have htrace : WordTrace (prefixWord ++ tailWord_1902295) baseStart_1902295 baseEnd_1902295 := by
    simpa [prefixWord, tailWord_1902295, baseEnd_1902295] using wordTrace_append hprefix tailTrace_1902295
  have hstable : (prefixWord ++ tailWord_1902295).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1902295).length < 2 ^ (prefixWord ++ tailWord_1902295).sum := by decide
  have hdescent : baseEnd_1902295 < baseStart_1902295 := by decide
  rcases family_descends (prefixWord ++ tailWord_1902295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1902312 : List Nat := [2, 1, 4, 1, 3, 2, 1, 2, 5]
def baseStart_1902312 : Nat := 118140960795 + 1902312 * 2 ^ 59
def prefixEnd_1902312 : Nat := 4983230072969 + 3 ^ 40 * 1902312 * 2
def baseEnd_1902312 : Nat := 434133515918162857445081

theorem tailTrace_1902312 : CollatzResearch.WordTrace tailWord_1902312 prefixEnd_1902312 434133515918162857445081 := by
  unfold tailWord_1902312
  simp only [CollatzResearch.WordTrace]
  refine ⟨34691509342127993934486595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46255345789503991912648793 34691509342127993934486595)
  ·
    refine ⟨52037264013191990901729893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34691509342127993934486595 52037264013191990901729893)
    ·
      refine ⟨9756987002473498294074355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52037264013191990901729893 9756987002473498294074355)
      ·
        refine ⟨14635480503710247441111533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9756987002473498294074355 14635480503710247441111533)
        ·
          refine ⟨5488305188891342790416825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14635480503710247441111533 5488305188891342790416825)
          ·
            refine ⟨4116228891668507092812619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5488305188891342790416825 4116228891668507092812619)
            ·
              refine ⟨6174343337502760639218929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4116228891668507092812619 6174343337502760639218929)
              ·
                refine ⟨4630757503127070479414197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6174343337502760639218929 4630757503127070479414197)
                ·
                  refine ⟨434133515918162857445081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4630757503127070479414197 434133515918162857445081)
                  ·
                    rfl

theorem cell21_1902312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 2, 5].length) (baseStart_1902312 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1902312 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1902312 prefixEnd_1902312 := by exact prefixLift 1902312
  have htrace : WordTrace (prefixWord ++ tailWord_1902312) baseStart_1902312 baseEnd_1902312 := by
    simpa [prefixWord, tailWord_1902312, baseEnd_1902312] using wordTrace_append hprefix tailTrace_1902312
  have hstable : (prefixWord ++ tailWord_1902312).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1902312).length < 2 ^ (prefixWord ++ tailWord_1902312).sum := by decide
  have hdescent : baseEnd_1902312 < baseStart_1902312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1902312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1902343 : List Nat := [1, 1, 4, 4, 2, 1, 1, 1, 6]
def baseStart_1902343 : Nat := 118140960795 + 1902343 * 2 ^ 59
def prefixEnd_1902343 : Nat := 4983230072969 + 3 ^ 40 * 1902343 * 2
def baseEnd_1902343 : Nat := 434140590540513692428351

theorem tailTrace_1902343 : CollatzResearch.WordTrace tailWord_1902343 prefixEnd_1902343 434140590540513692428351 := by
  unfold tailWord_1902343
  simp only [CollatzResearch.WordTrace]
  refine ⟨69384149347143680163351683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46256099564762453442234455 69384149347143680163351683)
  ·
    refine ⟨104076224020715520245027525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69384149347143680163351683 104076224020715520245027525)
    ·
      refine ⟨19514292003884160045942661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104076224020715520245027525 19514292003884160045942661)
      ·
        refine ⟨3658929750728280008614249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19514292003884160045942661 3658929750728280008614249)
        ·
          refine ⟨2744197313046210006460687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3658929750728280008614249 2744197313046210006460687)
          ·
            refine ⟨4116295969569315009691031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2744197313046210006460687 4116295969569315009691031)
            ·
              refine ⟨6174443954353972514536547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4116295969569315009691031 6174443954353972514536547)
              ·
                refine ⟨9261665931530958771804821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6174443954353972514536547 9261665931530958771804821)
                ·
                  refine ⟨434140590540513692428351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9261665931530958771804821 434140590540513692428351)
                  ·
                    rfl

theorem cell21_1902343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 1, 6].length) (baseStart_1902343 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1902343 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1902343 prefixEnd_1902343 := by exact prefixLift 1902343
  have htrace : WordTrace (prefixWord ++ tailWord_1902343) baseStart_1902343 baseEnd_1902343 := by
    simpa [prefixWord, tailWord_1902343, baseEnd_1902343] using wordTrace_append hprefix tailTrace_1902343
  have hstable : (prefixWord ++ tailWord_1902343).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1902343).length < 2 ^ (prefixWord ++ tailWord_1902343).sum := by decide
  have hdescent : baseEnd_1902343 < baseStart_1902343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1902343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1902371 : List Nat := [1, 1, 1, 4, 2, 1, 4, 2, 5]
def baseStart_1902371 : Nat := 118140960795 + 1902371 * 2 ^ 59
def prefixEnd_1902371 : Nat := 4983230072969 + 3 ^ 40 * 1902371 * 2
def baseEnd_1902371 : Nat := 434146980521991865961627

theorem tailTrace_1902371 : CollatzResearch.WordTrace tailWord_1902371 prefixEnd_1902371 434146980521991865961627 := by
  unfold tailWord_1902371
  simp only [CollatzResearch.WordTrace]
  refine ⟨69385170591042240945370967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46256780394028160630247311 69385170591042240945370967)
  ·
    refine ⟨104077755886563361418056451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69385170591042240945370967 104077755886563361418056451)
    ·
      refine ⟨156116633829845042127084677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104077755886563361418056451 156116633829845042127084677)
      ·
        refine ⟨29271868843095945398828377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 156116633829845042127084677 29271868843095945398828377)
        ·
          refine ⟨21953901632321959049121283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29271868843095945398828377 21953901632321959049121283)
          ·
            refine ⟨32930852448482938573681925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21953901632321959049121283 32930852448482938573681925)
            ·
              refine ⟨6174534834090550982565361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32930852448482938573681925 6174534834090550982565361)
              ·
                refine ⟨4630901125567913236924021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6174534834090550982565361 4630901125567913236924021)
                ·
                  refine ⟨434146980521991865961627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4630901125567913236924021 434146980521991865961627)
                  ·
                    rfl

theorem cell21_1902371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 2, 5].length) (baseStart_1902371 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1902371 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1902371 prefixEnd_1902371 := by exact prefixLift 1902371
  have htrace : WordTrace (prefixWord ++ tailWord_1902371) baseStart_1902371 baseEnd_1902371 := by
    simpa [prefixWord, tailWord_1902371, baseEnd_1902371] using wordTrace_append hprefix tailTrace_1902371
  have hstable : (prefixWord ++ tailWord_1902371).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1902371).length < 2 ^ (prefixWord ++ tailWord_1902371).sum := by decide
  have hdescent : baseEnd_1902371 < baseStart_1902371 := by decide
  rcases family_descends (prefixWord ++ tailWord_1902371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1902405 : List Nat := [1, 3, 1, 1, 1, 2, 7, 2, 3]
def baseStart_1902405 : Nat := 118140960795 + 1902405 * 2 ^ 59
def prefixEnd_1902405 : Nat := 4983230072969 + 3 ^ 40 * 1902405 * 2
def baseEnd_1902405 : Nat := 434154739785215362394891

theorem tailTrace_1902405 : CollatzResearch.WordTrace tailWord_1902405 prefixEnd_1902405 434154739785215362394891 := by
  unfold tailWord_1902405
  simp only [CollatzResearch.WordTrace]
  refine ⟨69386410672919064752108669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46257607115279376501405779 69386410672919064752108669)
  ·
    refine ⟨26019904002344649282040751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69386410672919064752108669 26019904002344649282040751)
    ·
      refine ⟨39029856003516973923061127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26019904002344649282040751 39029856003516973923061127)
      ·
        refine ⟨58544784005275460884591691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39029856003516973923061127 58544784005275460884591691)
        ·
          refine ⟨87817176007913191326887537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58544784005275460884591691 87817176007913191326887537)
          ·
            refine ⟨65862882005934893495165653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87817176007913191326887537 65862882005934893495165653)
            ·
              refine ⟨1543661297014099066292945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 65862882005934893495165653 1543661297014099066292945)
              ·
                refine ⟨1157745972760574299719709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1543661297014099066292945 1157745972760574299719709)
                ·
                  refine ⟨434154739785215362394891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1157745972760574299719709 434154739785215362394891)
                  ·
                    rfl

theorem cell21_1902405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 7, 2, 3].length) (baseStart_1902405 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1902405 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1902405 prefixEnd_1902405 := by exact prefixLift 1902405
  have htrace : WordTrace (prefixWord ++ tailWord_1902405) baseStart_1902405 baseEnd_1902405 := by
    simpa [prefixWord, tailWord_1902405, baseEnd_1902405] using wordTrace_append hprefix tailTrace_1902405
  have hstable : (prefixWord ++ tailWord_1902405).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1902405).length < 2 ^ (prefixWord ++ tailWord_1902405).sum := by decide
  have hdescent : baseEnd_1902405 < baseStart_1902405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1902405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1902464 : List Nat := [2, 1, 1, 2, 1, 2, 5, 4, 3]
def baseStart_1902464 : Nat := 118140960795 + 1902464 * 2 ^ 59
def prefixEnd_1902464 : Nat := 4983230072969 + 3 ^ 40 * 1902464 * 2
def baseEnd_1902464 : Nat := 434168204389044370911437

theorem tailTrace_1902464 : CollatzResearch.WordTrace tailWord_1902464 prefixEnd_1902464 434168204389044370911437 := by
  unfold tailWord_1902464
  simp only [CollatzResearch.WordTrace]
  refine ⟨34694281289852658914253223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46259041719803545219004297 34694281289852658914253223)
  ·
    refine ⟨52041421934778988371379835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34694281289852658914253223 52041421934778988371379835)
    ·
      refine ⟨78062132902168482557069753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52041421934778988371379835 78062132902168482557069753)
      ·
        refine ⟨58546599676626361917802315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78062132902168482557069753 58546599676626361917802315)
        ·
          refine ⟨87819899514939542876703473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58546599676626361917802315 87819899514939542876703473)
          ·
            refine ⟨65864924636204657157527605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87819899514939542876703473 65864924636204657157527605)
            ·
              refine ⟨6174836684644186608518213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65864924636204657157527605 6174836684644186608518213)
              ·
                refine ⟨1157781878370784989097165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6174836684644186608518213 1157781878370784989097165)
                ·
                  refine ⟨434168204389044370911437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1157781878370784989097165 434168204389044370911437)
                  ·
                    rfl

theorem cell21_1902464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 4, 3].length) (baseStart_1902464 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1902464 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1902464 prefixEnd_1902464 := by exact prefixLift 1902464
  have htrace : WordTrace (prefixWord ++ tailWord_1902464) baseStart_1902464 baseEnd_1902464 := by
    simpa [prefixWord, tailWord_1902464, baseEnd_1902464] using wordTrace_append hprefix tailTrace_1902464
  have hstable : (prefixWord ++ tailWord_1902464).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1902464).length < 2 ^ (prefixWord ++ tailWord_1902464).sum := by decide
  have hdescent : baseEnd_1902464 < baseStart_1902464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1902464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1902498 : List Nat := [3, 3, 1, 2, 3, 1, 2, 3, 3]
def baseStart_1902498 : Nat := 118140960795 + 1902498 * 2 ^ 59
def prefixEnd_1902498 : Nat := 4983230072969 + 3 ^ 40 * 1902498 * 2
def baseEnd_1902498 : Nat := 434175963652267867344701

theorem tailTrace_1902498 : CollatzResearch.WordTrace tailWord_1902498 prefixEnd_1902498 434175963652267867344701 := by
  unfold tailWord_1902498
  simp only [CollatzResearch.WordTrace]
  refine ⟨17347450665395535408811037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46259868441054761090162765 17347450665395535408811037)
  ·
    refine ⟨6505293999523325778304139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17347450665395535408811037 6505293999523325778304139)
    ·
      refine ⟨9757940999284988667456209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6505293999523325778304139 9757940999284988667456209)
      ·
        refine ⟨7318455749463741500592157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9757940999284988667456209 7318455749463741500592157)
        ·
          refine ⟨2744420906048903062722059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7318455749463741500592157 2744420906048903062722059)
          ·
            refine ⟨4116631359073354594083089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2744420906048903062722059 4116631359073354594083089)
            ·
              refine ⟨3087473519305015945562317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4116631359073354594083089 3087473519305015945562317)
              ·
                refine ⟨1157802569739380979585869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3087473519305015945562317 1157802569739380979585869)
                ·
                  refine ⟨434175963652267867344701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1157802569739380979585869 434175963652267867344701)
                  ·
                    rfl

theorem cell21_1902498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 2, 3, 3].length) (baseStart_1902498 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1902498 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1902498 prefixEnd_1902498 := by exact prefixLift 1902498
  have htrace : WordTrace (prefixWord ++ tailWord_1902498) baseStart_1902498 baseEnd_1902498 := by
    simpa [prefixWord, tailWord_1902498, baseEnd_1902498] using wordTrace_append hprefix tailTrace_1902498
  have hstable : (prefixWord ++ tailWord_1902498).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1902498).length < 2 ^ (prefixWord ++ tailWord_1902498).sum := by decide
  have hdescent : baseEnd_1902498 < baseStart_1902498 := by decide
  rcases family_descends (prefixWord ++ tailWord_1902498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1902574 : List Nat := [4, 1, 2, 1, 3, 2, 3, 2, 3]
def baseStart_1902574 : Nat := 118140960795 + 1902574 * 2 ^ 59
def prefixEnd_1902574 : Nat := 4983230072969 + 3 ^ 40 * 1902574 * 2
def baseEnd_1902574 : Nat := 434193307887708624077879

theorem tailTrace_1902574 : CollatzResearch.WordTrace tailWord_1902574 prefixEnd_1902574 434193307887708624077879 := by
  unfold tailWord_1902574
  simp only [CollatzResearch.WordTrace]
  refine ⟨8674071826163350826876347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46261716406204537743340517 8674071826163350826876347)
  ·
    refine ⟨13011107739245026240314521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8674071826163350826876347 13011107739245026240314521)
    ·
      refine ⟨9758330804433769680235891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13011107739245026240314521 9758330804433769680235891)
      ·
        refine ⟨14637496206650654520353837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9758330804433769680235891 14637496206650654520353837)
        ·
          refine ⟨5489061077493995445132689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14637496206650654520353837 5489061077493995445132689)
          ·
            refine ⟨4116795808120496583849517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5489061077493995445132689 4116795808120496583849517)
            ·
              refine ⟨1543798428045186218943569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4116795808120496583849517 1543798428045186218943569)
              ·
                refine ⟨1157848821033889664207677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1543798428045186218943569 1157848821033889664207677)
                ·
                  refine ⟨434193307887708624077879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1157848821033889664207677 434193307887708624077879)
                  ·
                    rfl

theorem cell21_1902574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 3, 2, 3].length) (baseStart_1902574 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1902574 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1902574 prefixEnd_1902574 := by exact prefixLift 1902574
  have htrace : WordTrace (prefixWord ++ tailWord_1902574) baseStart_1902574 baseEnd_1902574 := by
    simpa [prefixWord, tailWord_1902574, baseEnd_1902574] using wordTrace_append hprefix tailTrace_1902574
  have hstable : (prefixWord ++ tailWord_1902574).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1902574).length < 2 ^ (prefixWord ++ tailWord_1902574).sum := by decide
  have hdescent : baseEnd_1902574 < baseStart_1902574 := by decide
  rcases family_descends (prefixWord ++ tailWord_1902574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1902616 : List Nat := [2, 1, 2, 3, 2, 1, 2, 5, 3]
def baseStart_1902616 : Nat := 118140960795 + 1902616 * 2 ^ 59
def prefixEnd_1902616 : Nat := 4983230072969 + 3 ^ 40 * 1902616 * 2
def baseEnd_1902616 : Nat := 434202892859925884377793

theorem tailTrace_1902616 : CollatzResearch.WordTrace tailWord_1902616 prefixEnd_1902616 434202892859925884377793 := by
  unfold tailWord_1902616
  simp only [CollatzResearch.WordTrace]
  refine ⟨34697053237577323894019851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46262737650103098525359801 34697053237577323894019851)
  ·
    refine ⟨52045579856365985841029777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34697053237577323894019851 52045579856365985841029777)
    ·
      refine ⟨39034184892274489380772333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52045579856365985841029777 39034184892274489380772333)
      ·
        refine ⟨14637819334602933517789625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39034184892274489380772333 14637819334602933517789625)
        ·
          refine ⟨10978364500952200138342219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14637819334602933517789625 10978364500952200138342219)
          ·
            refine ⟨16467546751428300207513329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10978364500952200138342219 16467546751428300207513329)
            ·
              refine ⟨12350660063571225155634997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16467546751428300207513329 12350660063571225155634997)
              ·
                refine ⟨1157874380959802358340781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12350660063571225155634997 1157874380959802358340781)
                ·
                  refine ⟨434202892859925884377793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1157874380959802358340781 434202892859925884377793)
                  ·
                    rfl

theorem cell21_1902616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 5, 3].length) (baseStart_1902616 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1902616 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1902616 prefixEnd_1902616 := by exact prefixLift 1902616
  have htrace : WordTrace (prefixWord ++ tailWord_1902616) baseStart_1902616 baseEnd_1902616 := by
    simpa [prefixWord, tailWord_1902616, baseEnd_1902616] using wordTrace_append hprefix tailTrace_1902616
  have hstable : (prefixWord ++ tailWord_1902616).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1902616).length < 2 ^ (prefixWord ++ tailWord_1902616).sum := by decide
  have hdescent : baseEnd_1902616 < baseStart_1902616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1902616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1902678 : List Nat := [5, 2, 2, 1, 1, 2, 8]
def baseStart_1902678 : Nat := 118140960795 + 1902678 * 2 ^ 59
def prefixEnd_1902678 : Nat := 4983230072969 + 3 ^ 40 * 1902678 * 2
def baseEnd_1902678 : Nat := 48246338011625283816037

theorem tailTrace_1902678 : CollatzResearch.WordTrace tailWord_1902678 prefixEnd_1902678 48246338011625283816037 := by
  unfold tailWord_1902678
  simp only [CollatzResearch.WordTrace]
  refine ⟨4337272987558127023549793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46264245200620021584531125 4337272987558127023549793)
  ·
    refine ⟨3252954740668595267662345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4337272987558127023549793 3252954740668595267662345)
    ·
      refine ⟨2439716055501446450746759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3252954740668595267662345 2439716055501446450746759)
      ·
        refine ⟨3659574083252169676120139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2439716055501446450746759 3659574083252169676120139)
        ·
          refine ⟨5489361124878254514180209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3659574083252169676120139 5489361124878254514180209)
          ·
            refine ⟨4117020843658690885635157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5489361124878254514180209 4117020843658690885635157)
            ·
              refine ⟨48246338011625283816037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4117020843658690885635157 48246338011625283816037)
              ·
                rfl

theorem cell21_1902678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 8].length) (baseStart_1902678 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1902678 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1902678 prefixEnd_1902678 := by exact prefixLift 1902678
  have htrace : WordTrace (prefixWord ++ tailWord_1902678) baseStart_1902678 baseEnd_1902678 := by
    simpa [prefixWord, tailWord_1902678, baseEnd_1902678] using wordTrace_append hprefix tailTrace_1902678
  have hstable : (prefixWord ++ tailWord_1902678).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1902678).length < 2 ^ (prefixWord ++ tailWord_1902678).sum := by decide
  have hdescent : baseEnd_1902678 < baseStart_1902678 := by decide
  rcases family_descends (prefixWord ++ tailWord_1902678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1902692 : List Nat := [2, 3, 1, 1, 2, 1, 4, 4, 3]
def baseStart_1902692 : Nat := 118140960795 + 1902692 * 2 ^ 59
def prefixEnd_1902692 : Nat := 4983230072969 + 3 ^ 40 * 1902692 * 2
def baseEnd_1902692 : Nat := 434220237095366641110971

theorem tailTrace_1902692 : CollatzResearch.WordTrace tailWord_1902692 prefixEnd_1902692 434220237095366641110971 := by
  unfold tailWord_1902692
  simp only [CollatzResearch.WordTrace]
  refine ⟨34698439211439656383903165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46264585615252875178537553 34698439211439656383903165)
  ·
    refine ⟨13011914704289871143963687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34698439211439656383903165 13011914704289871143963687)
    ·
      refine ⟨19517872056434806715945531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13011914704289871143963687 19517872056434806715945531)
      ·
        refine ⟨29276808084652210073918297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19517872056434806715945531 29276808084652210073918297)
        ·
          refine ⟨21957606063489157555438723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29276808084652210073918297 21957606063489157555438723)
          ·
            refine ⟨32936409095233736333158085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21957606063489157555438723 32936409095233736333158085)
            ·
              refine ⟨6175576705356325562467141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32936409095233736333158085 6175576705356325562467141)
              ·
                refine ⟨1157920632254311042962589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6175576705356325562467141 1157920632254311042962589)
                ·
                  refine ⟨434220237095366641110971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1157920632254311042962589 434220237095366641110971)
                  ·
                    rfl

theorem cell21_1902692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 4, 3].length) (baseStart_1902692 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1902692 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1902692 prefixEnd_1902692 := by exact prefixLift 1902692
  have htrace : WordTrace (prefixWord ++ tailWord_1902692) baseStart_1902692 baseEnd_1902692 := by
    simpa [prefixWord, tailWord_1902692, baseEnd_1902692] using wordTrace_append hprefix tailTrace_1902692
  have hstable : (prefixWord ++ tailWord_1902692).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1902692).length < 2 ^ (prefixWord ++ tailWord_1902692).sum := by decide
  have hdescent : baseEnd_1902692 < baseStart_1902692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1902692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1902779 : List Nat := [1, 1, 1, 1, 1, 2, 5, 9]
def baseStart_1902779 : Nat := 118140960795 + 1902779 * 2 ^ 59
def prefixEnd_1902779 : Nat := 4983230072969 + 3 ^ 40 * 1902779 * 2
def baseEnd_1902779 : Nat := 144746697226891274386931

theorem tailTrace_1902779 : CollatzResearch.WordTrace tailWord_1902779 prefixEnd_1902779 144746697226891274386931 := by
  unfold tailWord_1902779
  simp only [CollatzResearch.WordTrace]
  refine ⟨69400051573564126626223391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46266701049042751084148927 69400051573564126626223391)
  ·
    refine ⟨104100077360346189939335087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69400051573564126626223391 104100077360346189939335087)
    ·
      refine ⟨156150116040519284909002631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104100077360346189939335087 156150116040519284909002631)
      ·
        refine ⟨234225174060778927363503947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156150116040519284909002631 234225174060778927363503947)
        ·
          refine ⟨351337761091168391045255921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234225174060778927363503947 351337761091168391045255921)
          ·
            refine ⟨263503320818376293283941941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 351337761091168391045255921 263503320818376293283941941)
            ·
              refine ⟨24703436326722777495369557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 263503320818376293283941941 24703436326722777495369557)
              ·
                refine ⟨144746697226891274386931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24703436326722777495369557 144746697226891274386931)
                ·
                  rfl

theorem cell21_1902779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 9].length) (baseStart_1902779 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1902779 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1902779 prefixEnd_1902779 := by exact prefixLift 1902779
  have htrace : WordTrace (prefixWord ++ tailWord_1902779) baseStart_1902779 baseEnd_1902779 := by
    simpa [prefixWord, tailWord_1902779, baseEnd_1902779] using wordTrace_append hprefix tailTrace_1902779
  have hstable : (prefixWord ++ tailWord_1902779).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1902779).length < 2 ^ (prefixWord ++ tailWord_1902779).sum := by decide
  have hdescent : baseEnd_1902779 < baseStart_1902779 := by decide
  rcases family_descends (prefixWord ++ tailWord_1902779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1902796 : List Nat := [2, 2, 1, 6, 10]
def baseStart_1902796 : Nat := 118140960795 + 1902796 * 2 ^ 59
def prefixEnd_1902796 : Nat := 4983230072969 + 3 ^ 40 * 1902796 * 2
def baseEnd_1902796 : Nat := 5361036682867723103425

theorem tailTrace_1902796 : CollatzResearch.WordTrace tailWord_1902796 prefixEnd_1902796 5361036682867723103425 := by
  unfold tailWord_1902796
  simp only [CollatzResearch.WordTrace]
  refine ⟨34700335807251269264796121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46267114409668359019728161 34700335807251269264796121)
  ·
    refine ⟨26025251855438451948597091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34700335807251269264796121 26025251855438451948597091)
    ·
      refine ⟨39037877783157677922895637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26025251855438451948597091 39037877783157677922895637)
      ·
        refine ⟨1829900521085516152635733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 39037877783157677922895637 1829900521085516152635733)
        ·
          refine ⟨5361036682867723103425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1829900521085516152635733 5361036682867723103425)
          ·
            rfl

theorem cell21_1902796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 10].length) (baseStart_1902796 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1902796 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1902796 prefixEnd_1902796 := by exact prefixLift 1902796
  have htrace : WordTrace (prefixWord ++ tailWord_1902796) baseStart_1902796 baseEnd_1902796 := by
    simpa [prefixWord, tailWord_1902796, baseEnd_1902796] using wordTrace_append hprefix tailTrace_1902796
  have hstable : (prefixWord ++ tailWord_1902796).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1902796).length < 2 ^ (prefixWord ++ tailWord_1902796).sum := by decide
  have hdescent : baseEnd_1902796 < baseStart_1902796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1902796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1902802 : List Nat := [3, 2, 2, 2, 1, 4, 2, 2, 3]
def baseStart_1902802 : Nat := 118140960795 + 1902802 * 2 ^ 59
def prefixEnd_1902802 : Nat := 4983230072969 + 3 ^ 40 * 1902802 * 2
def baseEnd_1902802 : Nat := 434245340594030894277413

theorem tailTrace_1902802 : CollatzResearch.WordTrace tailWord_1902802 prefixEnd_1902802 434245340594030894277413 := by
  unfold tailWord_1902802
  simp only [CollatzResearch.WordTrace]
  refine ⟨17350222613120200388577665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46267260301653867702873773 17350222613120200388577665)
  ·
    refine ⟨13012666959840150291433249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17350222613120200388577665 13012666959840150291433249)
    ·
      refine ⟨9759500219880112718574937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13012666959840150291433249 9759500219880112718574937)
      ·
        refine ⟨7319625164910084538931203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9759500219880112718574937 7319625164910084538931203)
        ·
          refine ⟨10979437747365126808396805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7319625164910084538931203 10979437747365126808396805)
          ·
            refine ⟨2058644577630961276574401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10979437747365126808396805 2058644577630961276574401)
            ·
              refine ⟨1543983433223220957430801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2058644577630961276574401 1543983433223220957430801)
              ·
                refine ⟨1157987574917415718073101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1543983433223220957430801 1157987574917415718073101)
                ·
                  refine ⟨434245340594030894277413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1157987574917415718073101 434245340594030894277413)
                  ·
                    rfl

theorem cell21_1902802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 2, 2, 3].length) (baseStart_1902802 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1902802 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1902802 prefixEnd_1902802 := by exact prefixLift 1902802
  have htrace : WordTrace (prefixWord ++ tailWord_1902802) baseStart_1902802 baseEnd_1902802 := by
    simpa [prefixWord, tailWord_1902802, baseEnd_1902802] using wordTrace_append hprefix tailTrace_1902802
  have hstable : (prefixWord ++ tailWord_1902802).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1902802).length < 2 ^ (prefixWord ++ tailWord_1902802).sum := by decide
  have hdescent : baseEnd_1902802 < baseStart_1902802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1902802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1902813 : List Nat := [1, 4, 3, 2, 1, 1, 3, 6]
def baseStart_1902813 : Nat := 118140960795 + 1902813 * 2 ^ 59
def prefixEnd_1902813 : Nat := 4983230072969 + 3 ^ 40 * 1902813 * 2
def baseEnd_1902813 : Nat := 144749283647965773198019

theorem tailTrace_1902813 : CollatzResearch.WordTrace tailWord_1902813 prefixEnd_1902813 144749283647965773198019 := by
  unfold tailWord_1902813
  simp only [CollatzResearch.WordTrace]
  refine ⟨69401291655440950432961093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46267527770293966955307395 69401291655440950432961093)
  ·
    refine ⟨13012742185395178206180205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69401291655440950432961093 13012742185395178206180205)
    ·
      refine ⟨4879778319523191827317577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13012742185395178206180205 4879778319523191827317577)
      ·
        refine ⟨3659833739642393870488183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4879778319523191827317577 3659833739642393870488183)
        ·
          refine ⟨5489750609463590805732275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3659833739642393870488183 5489750609463590805732275)
          ·
            refine ⟨8234625914195386208598413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5489750609463590805732275 8234625914195386208598413)
            ·
              refine ⟨3087984717823269828224405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8234625914195386208598413 3087984717823269828224405)
              ·
                refine ⟨144749283647965773198019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3087984717823269828224405 144749283647965773198019)
                ·
                  rfl

theorem cell21_1902813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 3, 6].length) (baseStart_1902813 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1902813 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1902813 prefixEnd_1902813 := by exact prefixLift 1902813
  have htrace : WordTrace (prefixWord ++ tailWord_1902813) baseStart_1902813 baseEnd_1902813 := by
    simpa [prefixWord, tailWord_1902813, baseEnd_1902813] using wordTrace_append hprefix tailTrace_1902813
  have hstable : (prefixWord ++ tailWord_1902813).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1902813).length < 2 ^ (prefixWord ++ tailWord_1902813).sum := by decide
  have hdescent : baseEnd_1902813 < baseStart_1902813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1902813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1902844 : List Nat := [2, 2, 2, 1, 4, 1, 1, 5, 3]
def baseStart_1902844 : Nat := 118140960795 + 1902844 * 2 ^ 59
def prefixEnd_1902844 : Nat := 4983230072969 + 3 ^ 40 * 1902844 * 2
def baseEnd_1902844 : Nat := 434254925566248154577327

theorem tailTrace_1902844 : CollatzResearch.WordTrace tailWord_1902844 prefixEnd_1902844 434254925566248154577327 := by
  unfold tailWord_1902844
  simp only [CollatzResearch.WordTrace]
  refine ⟨34701211159164321363669793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46268281545552428484893057 34701211159164321363669793)
  ·
    refine ⟨26025908369373241022752345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34701211159164321363669793 26025908369373241022752345)
    ·
      refine ⟨19519431277029930767064259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26025908369373241022752345 19519431277029930767064259)
      ·
        refine ⟨29279146915544896150596389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19519431277029930767064259 29279146915544896150596389)
        ·
          refine ⟨5489840046664668028236823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29279146915544896150596389 5489840046664668028236823)
          ·
            refine ⟨8234760069997002042355235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5489840046664668028236823 8234760069997002042355235)
            ·
              refine ⟨12352140104995503063532853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8234760069997002042355235 12352140104995503063532853)
              ·
                refine ⟨1158013134843328412206205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12352140104995503063532853 1158013134843328412206205)
                ·
                  refine ⟨434254925566248154577327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1158013134843328412206205 434254925566248154577327)
                  ·
                    rfl

theorem cell21_1902844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 5, 3].length) (baseStart_1902844 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1902844 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1902844 prefixEnd_1902844 := by exact prefixLift 1902844
  have htrace : WordTrace (prefixWord ++ tailWord_1902844) baseStart_1902844 baseEnd_1902844 := by
    simpa [prefixWord, tailWord_1902844, baseEnd_1902844] using wordTrace_append hprefix tailTrace_1902844
  have hstable : (prefixWord ++ tailWord_1902844).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1902844).length < 2 ^ (prefixWord ++ tailWord_1902844).sum := by decide
  have hdescent : baseEnd_1902844 < baseStart_1902844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1902844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1902858 : List Nat := [3, 1, 2, 2, 1, 1, 5, 2, 4]
def baseStart_1902858 : Nat := 118140960795 + 1902858 * 2 ^ 59
def prefixEnd_1902858 : Nat := 4983230072969 + 3 ^ 40 * 1902858 * 2
def baseEnd_1902858 : Nat := 434258120556987241343965

theorem tailTrace_1902858 : CollatzResearch.WordTrace tailWord_1902858 prefixEnd_1902858 434258120556987241343965 := by
  unfold tailWord_1902858
  simp only [CollatzResearch.WordTrace]
  refine ⟨17350733235069480779587307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46268621960185282078899485 17350733235069480779587307)
  ·
    refine ⟨26026099852604221169380961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17350733235069480779587307 26026099852604221169380961)
    ·
      refine ⟨19519574889453165877035721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26026099852604221169380961 19519574889453165877035721)
      ·
        refine ⟨14639681167089874407776791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19519574889453165877035721 14639681167089874407776791)
        ·
          refine ⟨21959521750634811611665187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14639681167089874407776791 21959521750634811611665187)
          ·
            refine ⟨32939282625952217417497781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21959521750634811611665187 32939282625952217417497781)
            ·
              refine ⟨3088057746183020382890417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32939282625952217417497781 3088057746183020382890417)
              ·
                refine ⟨2316043309637265287167813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3088057746183020382890417 2316043309637265287167813)
                ·
                  refine ⟨434258120556987241343965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2316043309637265287167813 434258120556987241343965)
                  ·
                    rfl

theorem cell21_1902858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 5, 2, 4].length) (baseStart_1902858 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1902858 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1902858 prefixEnd_1902858 := by exact prefixLift 1902858
  have htrace : WordTrace (prefixWord ++ tailWord_1902858) baseStart_1902858 baseEnd_1902858 := by
    simpa [prefixWord, tailWord_1902858, baseEnd_1902858] using wordTrace_append hprefix tailTrace_1902858
  have hstable : (prefixWord ++ tailWord_1902858).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1902858).length < 2 ^ (prefixWord ++ tailWord_1902858).sum := by decide
  have hdescent : baseEnd_1902858 < baseStart_1902858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1902858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1902996 : List Nat := [2, 4, 2, 1, 3, 1, 1, 2, 5]
def baseStart_1902996 : Nat := 118140960795 + 1902996 * 2 ^ 59
def prefixEnd_1902996 : Nat := 4983230072969 + 3 ^ 40 * 1902996 * 2
def baseEnd_1902996 : Nat := 434289614037129668043683

theorem tailTrace_1902996 : CollatzResearch.WordTrace tailWord_1902996 prefixEnd_1902996 434289614037129668043683 := by
  unfold tailWord_1902996
  simp only [CollatzResearch.WordTrace]
  refine ⟨34703983106888986343436421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46271977475851981791248561 34703983106888986343436421)
  ·
    refine ⟨6506996832541684939394329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34703983106888986343436421 6506996832541684939394329)
    ·
      refine ⟨4880247624406263704545747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6506996832541684939394329 4880247624406263704545747)
      ·
        refine ⟨7320371436609395556818621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4880247624406263704545747 7320371436609395556818621)
        ·
          refine ⟨2745139288728523333806983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7320371436609395556818621 2745139288728523333806983)
          ·
            refine ⟨4117708933092785000710475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2745139288728523333806983 4117708933092785000710475)
            ·
              refine ⟨6176563399639177501065713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4117708933092785000710475 6176563399639177501065713)
              ·
                refine ⟨4632422549729383125799285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6176563399639177501065713 4632422549729383125799285)
                ·
                  refine ⟨434289614037129668043683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4632422549729383125799285 434289614037129668043683)
                  ·
                    rfl

theorem cell21_1902996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 2, 5].length) (baseStart_1902996 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1902996 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1902996 prefixEnd_1902996 := by exact prefixLift 1902996
  have htrace : WordTrace (prefixWord ++ tailWord_1902996) baseStart_1902996 baseEnd_1902996 := by
    simpa [prefixWord, tailWord_1902996, baseEnd_1902996] using wordTrace_append hprefix tailTrace_1902996
  have hstable : (prefixWord ++ tailWord_1902996).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1902996).length < 2 ^ (prefixWord ++ tailWord_1902996).sum := by decide
  have hdescent : baseEnd_1902996 < baseStart_1902996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1902996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1903044 : List Nat := [2, 3, 3, 2, 2, 1, 3, 1, 4]
def baseStart_1903044 : Nat := 118140960795 + 1903044 * 2 ^ 59
def prefixEnd_1903044 : Nat := 4983230072969 + 3 ^ 40 * 1903044 * 2
def baseEnd_1903044 : Nat := 434300568291092251243585

theorem tailTrace_1903044 : CollatzResearch.WordTrace tailWord_1903044 prefixEnd_1903044 434300568291092251243585 := by
  unfold tailWord_1903044
  simp only [CollatzResearch.WordTrace]
  refine ⟨34704858458802038442310093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46273144611736051256413457 34704858458802038442310093)
  ·
    refine ⟨13014321922050764415866285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34704858458802038442310093 13014321922050764415866285)
    ·
      refine ⟨4880370720769036655949857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13014321922050764415866285 4880370720769036655949857)
      ·
        refine ⟨3660278040576777491962393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4880370720769036655949857 3660278040576777491962393)
        ·
          refine ⟨2745208530432583118971795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3660278040576777491962393 2745208530432583118971795)
          ·
            refine ⟨4117812795648874678457693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2745208530432583118971795 4117812795648874678457693)
            ·
              refine ⟨1544179798368328004421635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4117812795648874678457693 1544179798368328004421635)
              ·
                refine ⟨2316269697552492006632453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1544179798368328004421635 2316269697552492006632453)
                ·
                  refine ⟨434300568291092251243585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2316269697552492006632453 434300568291092251243585)
                  ·
                    rfl

theorem cell21_1903044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 3, 1, 4].length) (baseStart_1903044 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1903044 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1903044 prefixEnd_1903044 := by exact prefixLift 1903044
  have htrace : WordTrace (prefixWord ++ tailWord_1903044) baseStart_1903044 baseEnd_1903044 := by
    simpa [prefixWord, tailWord_1903044, baseEnd_1903044] using wordTrace_append hprefix tailTrace_1903044
  have hstable : (prefixWord ++ tailWord_1903044).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1903044).length < 2 ^ (prefixWord ++ tailWord_1903044).sum := by decide
  have hdescent : baseEnd_1903044 < baseStart_1903044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1903044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1903069 : List Nat := [1, 4, 3, 1, 1, 1, 1, 1, 8]
def baseStart_1903069 : Nat := 118140960795 + 1903069 * 2 ^ 59
def prefixEnd_1903069 : Nat := 4983230072969 + 3 ^ 40 * 1903069 * 2
def baseEnd_1903069 : Nat := 434306273631697763326867

theorem tailTrace_1903069 : CollatzResearch.WordTrace tailWord_1903069 prefixEnd_1903069 434306273631697763326867 := by
  unfold tailWord_1903069
  simp only [CollatzResearch.WordTrace]
  refine ⟨69410628742513506154280261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46273752495009004102853507 69410628742513506154280261)
  ·
    refine ⟨13014492889221282403927549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69410628742513506154280261 13014492889221282403927549)
    ·
      refine ⟨4880434833457980901472831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13014492889221282403927549 4880434833457980901472831)
      ·
        refine ⟨7320652250186971352209247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4880434833457980901472831 7320652250186971352209247)
        ·
          refine ⟨10980978375280457028313871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7320652250186971352209247 10980978375280457028313871)
          ·
            refine ⟨16471467562920685542470807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10980978375280457028313871 16471467562920685542470807)
            ·
              refine ⟨24707201344381028313706211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16471467562920685542470807 24707201344381028313706211)
              ·
                refine ⟨37060802016571542470559317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24707201344381028313706211 37060802016571542470559317)
                ·
                  refine ⟨434306273631697763326867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37060802016571542470559317 434306273631697763326867)
                  ·
                    rfl

theorem cell21_1903069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 8].length) (baseStart_1903069 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1903069 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1903069 prefixEnd_1903069 := by exact prefixLift 1903069
  have htrace : WordTrace (prefixWord ++ tailWord_1903069) baseStart_1903069 baseEnd_1903069 := by
    simpa [prefixWord, tailWord_1903069, baseEnd_1903069] using wordTrace_append hprefix tailTrace_1903069
  have hstable : (prefixWord ++ tailWord_1903069).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1903069).length < 2 ^ (prefixWord ++ tailWord_1903069).sum := by decide
  have hdescent : baseEnd_1903069 < baseStart_1903069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1903069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1903114 : List Nat := [3, 1, 2, 2, 2, 1, 2, 1, 7]
def baseStart_1903114 : Nat := 118140960795 + 1903114 * 2 ^ 59
def prefixEnd_1903114 : Nat := 4983230072969 + 3 ^ 40 * 1903114 * 2
def baseEnd_1903114 : Nat := 434316543244787685076775

theorem tailTrace_1903114 : CollatzResearch.WordTrace tailWord_1903114 prefixEnd_1903114 434316543244787685076775 := by
  unfold tailWord_1903114
  simp only [CollatzResearch.WordTrace]
  refine ⟨17353067506837619709917099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46274846684900319226445597 17353067506837619709917099)
  ·
    refine ⟨26029601260256429564875649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17353067506837619709917099 26029601260256429564875649)
    ·
      refine ⟨19522200945192322173656737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26029601260256429564875649 19522200945192322173656737)
      ·
        refine ⟨14641650708894241630242553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19522200945192322173656737 14641650708894241630242553)
        ·
          refine ⟨10981238031670681222681915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14641650708894241630242553 10981238031670681222681915)
          ·
            refine ⟨16471857047506021834022873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10981238031670681222681915 16471857047506021834022873)
            ·
              refine ⟨12353892785629516375517155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16471857047506021834022873 12353892785629516375517155)
              ·
                refine ⟨18530839178444274563275733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12353892785629516375517155 18530839178444274563275733)
                ·
                  refine ⟨434316543244787685076775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18530839178444274563275733 434316543244787685076775)
                  ·
                    rfl

theorem cell21_1903114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 1, 7].length) (baseStart_1903114 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1903114 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1903114 prefixEnd_1903114 := by exact prefixLift 1903114
  have htrace : WordTrace (prefixWord ++ tailWord_1903114) baseStart_1903114 baseEnd_1903114 := by
    simpa [prefixWord, tailWord_1903114, baseEnd_1903114] using wordTrace_append hprefix tailTrace_1903114
  have hstable : (prefixWord ++ tailWord_1903114).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1903114).length < 2 ^ (prefixWord ++ tailWord_1903114).sum := by decide
  have hdescent : baseEnd_1903114 < baseStart_1903114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1903114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1903196 : List Nat := [2, 2, 4, 1, 4, 1, 1, 2, 4]
def baseStart_1903196 : Nat := 118140960795 + 1903196 * 2 ^ 59
def prefixEnd_1903196 : Nat := 4983230072969 + 3 ^ 40 * 1903196 * 2
def baseEnd_1903196 : Nat := 434335256761973764709941

theorem tailTrace_1903196 : CollatzResearch.WordTrace tailWord_1903196 prefixEnd_1903196 434335256761973764709941 := by
  unfold tailWord_1903196
  simp only [CollatzResearch.WordTrace]
  refine ⟨34707630406526703422076721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46276840542035604562768961 34707630406526703422076721)
  ·
    refine ⟨26030722804895027566557541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34707630406526703422076721 26030722804895027566557541)
    ·
      refine ⟨4880760525917817668729539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26030722804895027566557541 4880760525917817668729539)
      ·
        refine ⟨7321140788876726503094309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4880760525917817668729539 7321140788876726503094309)
        ·
          refine ⟨1372713897914386219330183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7321140788876726503094309 1372713897914386219330183)
          ·
            refine ⟨2059070846871579328995275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1372713897914386219330183 2059070846871579328995275)
            ·
              refine ⟨3088606270307368993492913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2059070846871579328995275 3088606270307368993492913)
              ·
                refine ⟨2316454702730526745119685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3088606270307368993492913 2316454702730526745119685)
                ·
                  refine ⟨434335256761973764709941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2316454702730526745119685 434335256761973764709941)
                  ·
                    rfl

theorem cell21_1903196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 1, 2, 4].length) (baseStart_1903196 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1903196 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1903196 prefixEnd_1903196 := by exact prefixLift 1903196
  have htrace : WordTrace (prefixWord ++ tailWord_1903196) baseStart_1903196 baseEnd_1903196 := by
    simpa [prefixWord, tailWord_1903196, baseEnd_1903196] using wordTrace_append hprefix tailTrace_1903196
  have hstable : (prefixWord ++ tailWord_1903196).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1903196).length < 2 ^ (prefixWord ++ tailWord_1903196).sum := by decide
  have hdescent : baseEnd_1903196 < baseStart_1903196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1903196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1903252 : List Nat := [2, 4, 2, 2, 1, 1, 9]
def baseStart_1903252 : Nat := 118140960795 + 1903252 * 2 ^ 59
def prefixEnd_1903252 : Nat := 4983230072969 + 3 ^ 40 * 1903252 * 2
def baseEnd_1903252 : Nat := 48260892969436679086277

theorem tailTrace_1903252 : CollatzResearch.WordTrace tailWord_1903252 prefixEnd_1903252 48260892969436679086277 := by
  unfold tailWord_1903252
  simp only [CollatzResearch.WordTrace]
  refine ⟨34708651650425264204096005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46278202200567018938794673 34708651650425264204096005)
  ·
    refine ⟨6507872184454737038268001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34708651650425264204096005 6507872184454737038268001)
    ·
      refine ⟨4880904138341052778701001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6507872184454737038268001 4880904138341052778701001)
      ·
        refine ⟨3660678103755789584025751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4880904138341052778701001 3660678103755789584025751)
        ·
          refine ⟨5491017155633684376038627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3660678103755789584025751 5491017155633684376038627)
          ·
            refine ⟨8236525733450526564057941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5491017155633684376038627 8236525733450526564057941)
            ·
              refine ⟨48260892969436679086277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8236525733450526564057941 48260892969436679086277)
              ·
                rfl

theorem cell21_1903252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 9].length) (baseStart_1903252 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1903252 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1903252 prefixEnd_1903252 := by exact prefixLift 1903252
  have htrace : WordTrace (prefixWord ++ tailWord_1903252) baseStart_1903252 baseEnd_1903252 := by
    simpa [prefixWord, tailWord_1903252, baseEnd_1903252] using wordTrace_append hprefix tailTrace_1903252
  have hstable : (prefixWord ++ tailWord_1903252).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1903252).length < 2 ^ (prefixWord ++ tailWord_1903252).sum := by decide
  have hdescent : baseEnd_1903252 < baseStart_1903252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1903252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1903258 : List Nat := [3, 1, 1, 6, 1, 1, 3, 2, 3]
def baseStart_1903258 : Nat := 118140960795 + 1903258 * 2 ^ 59
def prefixEnd_1903258 : Nat := 4983230072969 + 3 ^ 40 * 1903258 * 2
def baseEnd_1903258 : Nat := 434349406006675434676481

theorem tailTrace_1903258 : CollatzResearch.WordTrace tailWord_1903258 prefixEnd_1903258 434349406006675434676481 := by
  unfold tailWord_1903258
  simp only [CollatzResearch.WordTrace]
  refine ⟨17354380534707197858227607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46278348092552527621940285 17354380534707197858227607)
  ·
    refine ⟨26031570802060796787341411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17354380534707197858227607 26031570802060796787341411)
    ·
      refine ⟨39047356203091195181012117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26031570802060796787341411 39047356203091195181012117)
      ·
        refine ⟨1830344822019899774109943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 39047356203091195181012117 1830344822019899774109943)
        ·
          refine ⟨2745517233029849661164915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1830344822019899774109943 2745517233029849661164915)
          ·
            refine ⟨4118275849544774491747373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2745517233029849661164915 4118275849544774491747373)
            ·
              refine ⟨1544353443579290434405265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4118275849544774491747373 1544353443579290434405265)
              ·
                refine ⟨1158265082684467825803949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1544353443579290434405265 1158265082684467825803949)
                ·
                  refine ⟨434349406006675434676481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1158265082684467825803949 434349406006675434676481)
                  ·
                    rfl

theorem cell21_1903258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 3, 2, 3].length) (baseStart_1903258 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1903258 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1903258 prefixEnd_1903258 := by exact prefixLift 1903258
  have htrace : WordTrace (prefixWord ++ tailWord_1903258) baseStart_1903258 baseEnd_1903258 := by
    simpa [prefixWord, tailWord_1903258, baseEnd_1903258] using wordTrace_append hprefix tailTrace_1903258
  have hstable : (prefixWord ++ tailWord_1903258).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1903258).length < 2 ^ (prefixWord ++ tailWord_1903258).sum := by decide
  have hdescent : baseEnd_1903258 < baseStart_1903258 := by decide
  rcases family_descends (prefixWord ++ tailWord_1903258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1903317 : List Nat := [1, 3, 2, 5, 1, 1, 1, 4, 3]
def baseStart_1903317 : Nat := 118140960795 + 1903317 * 2 ^ 59
def prefixEnd_1903317 : Nat := 4983230072969 + 3 ^ 40 * 1903317 * 2
def baseEnd_1903317 : Nat := 434362870610504443193027

theorem tailTrace_1903317 : CollatzResearch.WordTrace tailWord_1903317 prefixEnd_1903317 434362870610504443193027 := by
  unfold tailWord_1903317
  simp only [CollatzResearch.WordTrace]
  refine ⟨69419674045615044509308205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46279782697076696339538803 69419674045615044509308205)
  ·
    refine ⟨26032377767105641690990577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69419674045615044509308205 26032377767105641690990577)
    ·
      refine ⟨19524283325329231268242933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26032377767105641690990577 19524283325329231268242933)
      ·
        refine ⟨1830401561749615431397775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19524283325329231268242933 1830401561749615431397775)
        ·
          refine ⟨2745602342624423147096663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1830401561749615431397775 2745602342624423147096663)
          ·
            refine ⟨4118403513936634720644995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2745602342624423147096663 4118403513936634720644995)
            ·
              refine ⟨6177605270904952080967493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4118403513936634720644995 6177605270904952080967493)
              ·
                refine ⟨1158300988294678515181405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6177605270904952080967493 1158300988294678515181405)
                ·
                  refine ⟨434362870610504443193027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1158300988294678515181405 434362870610504443193027)
                  ·
                    rfl

theorem cell21_1903317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 4, 3].length) (baseStart_1903317 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1903317 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1903317 prefixEnd_1903317 := by exact prefixLift 1903317
  have htrace : WordTrace (prefixWord ++ tailWord_1903317) baseStart_1903317 baseEnd_1903317 := by
    simpa [prefixWord, tailWord_1903317, baseEnd_1903317] using wordTrace_append hprefix tailTrace_1903317
  have hstable : (prefixWord ++ tailWord_1903317).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1903317).length < 2 ^ (prefixWord ++ tailWord_1903317).sum := by decide
  have hdescent : baseEnd_1903317 < baseStart_1903317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1903317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1903342 : List Nat := [4, 1, 2, 1, 1, 3, 1, 1, 7]
def baseStart_1903342 : Nat := 118140960795 + 1903342 * 2 ^ 59
def prefixEnd_1903342 : Nat := 4983230072969 + 3 ^ 40 * 1903342 * 2
def baseEnd_1903342 : Nat := 434368575951109955276309

theorem tailTrace_1903342 : CollatzResearch.WordTrace tailWord_1903342 prefixEnd_1903342 434368575951109955276309 := by
  unfold tailWord_1903342
  simp only [CollatzResearch.WordTrace]
  refine ⟨8677573233815559222371035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46280390580349649185978853 8677573233815559222371035)
  ·
    refine ⟨13016359850723338833556553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8677573233815559222371035 13016359850723338833556553)
    ·
      refine ⟨9762269888042504125167415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13016359850723338833556553 9762269888042504125167415)
      ·
        refine ⟨14643404832063756187751123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9762269888042504125167415 14643404832063756187751123)
        ·
          refine ⟨21965107248095634281626685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14643404832063756187751123 21965107248095634281626685)
          ·
            refine ⟨8236915218035862855610007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21965107248095634281626685 8236915218035862855610007)
            ·
              refine ⟨12355372827053794283415011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8236915218035862855610007 12355372827053794283415011)
              ·
                refine ⟨18533059240580691425122517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12355372827053794283415011 18533059240580691425122517)
                ·
                  refine ⟨434368575951109955276309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18533059240580691425122517 434368575951109955276309)
                  ·
                    rfl

theorem cell21_1903342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 1, 7].length) (baseStart_1903342 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1903342 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1903342 prefixEnd_1903342 := by exact prefixLift 1903342
  have htrace : WordTrace (prefixWord ++ tailWord_1903342) baseStart_1903342 baseEnd_1903342 := by
    simpa [prefixWord, tailWord_1903342, baseEnd_1903342] using wordTrace_append hprefix tailTrace_1903342
  have hstable : (prefixWord ++ tailWord_1903342).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1903342).length < 2 ^ (prefixWord ++ tailWord_1903342).sum := by decide
  have hdescent : baseEnd_1903342 < baseStart_1903342 := by decide
  rcases family_descends (prefixWord ++ tailWord_1903342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1903421 : List Nat := [1, 4, 1, 4, 3, 1, 7]
def baseStart_1903421 : Nat := 118140960795 + 1903421 * 2 ^ 59
def prefixEnd_1903421 : Nat := 4983230072969 + 3 ^ 40 * 1903421 * 2
def baseEnd_1903421 : Nat := 48265178314158152606609

theorem tailTrace_1903421 : CollatzResearch.WordTrace tailWord_1903421 prefixEnd_1903421 48265178314158152606609 := by
  unfold tailWord_1903421
  simp only [CollatzResearch.WordTrace]
  refine ⟨69423467237238270271094117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46282311491492180180729411 69423467237238270271094117)
  ·
    refine ⟨13016900106982175675830147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69423467237238270271094117 13016900106982175675830147)
    ·
      refine ⟨19525350160473263513745221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13016900106982175675830147 19525350160473263513745221)
      ·
        refine ⟨3661003155088736908827229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19525350160473263513745221 3661003155088736908827229)
        ·
          refine ⟨1372876183158276340810211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3661003155088736908827229 1372876183158276340810211)
          ·
            refine ⟨2059314274737414511215317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1372876183158276340810211 2059314274737414511215317)
            ·
              refine ⟨48265178314158152606609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2059314274737414511215317 48265178314158152606609)
              ·
                rfl

theorem cell21_1903421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 7].length) (baseStart_1903421 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1903421 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1903421 prefixEnd_1903421 := by exact prefixLift 1903421
  have htrace : WordTrace (prefixWord ++ tailWord_1903421) baseStart_1903421 baseEnd_1903421 := by
    simpa [prefixWord, tailWord_1903421, baseEnd_1903421] using wordTrace_append hprefix tailTrace_1903421
  have hstable : (prefixWord ++ tailWord_1903421).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1903421).length < 2 ^ (prefixWord ++ tailWord_1903421).sum := by decide
  have hdescent : baseEnd_1903421 < baseStart_1903421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1903421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1903432 : List Nat := [2, 1, 3, 1, 1, 3, 1, 3, 6]
def baseStart_1903432 : Nat := 118140960795 + 1903432 * 2 ^ 59
def prefixEnd_1903432 : Nat := 4983230072969 + 3 ^ 40 * 1903432 * 2
def baseEnd_1903432 : Nat := 434389115177289798776125

theorem tailTrace_1903432 : CollatzResearch.WordTrace tailWord_1903432 prefixEnd_1903432 434389115177289798776125 := by
  unfold tailWord_1903432
  simp only [CollatzResearch.WordTrace]
  refine ⟨34711934220099209574872275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46282578960132279433163033 34711934220099209574872275)
  ·
    refine ⟨52067901330148814362308413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34711934220099209574872275 52067901330148814362308413)
    ·
      refine ⟨19525462998805805385865655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52067901330148814362308413 19525462998805805385865655)
      ·
        refine ⟨29288194498208708078798483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19525462998805805385865655 29288194498208708078798483)
        ·
          refine ⟨43932291747313062118197725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29288194498208708078798483 43932291747313062118197725)
          ·
            refine ⟨16474609405242398294324147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43932291747313062118197725 16474609405242398294324147)
            ·
              refine ⟨24711914107863597441486221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16474609405242398294324147 24711914107863597441486221)
              ·
                refine ⟨9266967790448849040557333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24711914107863597441486221 9266967790448849040557333)
                ·
                  refine ⟨434389115177289798776125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9266967790448849040557333 434389115177289798776125)
                  ·
                    rfl

theorem cell21_1903432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 3, 6].length) (baseStart_1903432 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1903432 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1903432 prefixEnd_1903432 := by exact prefixLift 1903432
  have htrace : WordTrace (prefixWord ++ tailWord_1903432) baseStart_1903432 baseEnd_1903432 := by
    simpa [prefixWord, tailWord_1903432, baseEnd_1903432] using wordTrace_append hprefix tailTrace_1903432
  have hstable : (prefixWord ++ tailWord_1903432).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1903432).length < 2 ^ (prefixWord ++ tailWord_1903432).sum := by decide
  have hdescent : baseEnd_1903432 < baseStart_1903432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1903432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1903449 : List Nat := [1, 2, 1, 2, 2, 5, 1, 3, 4]
def baseStart_1903449 : Nat := 118140960795 + 1903449 * 2 ^ 59
def prefixEnd_1903449 : Nat := 4983230072969 + 3 ^ 40 * 1903449 * 2
def baseEnd_1903449 : Nat := 434392994808901546992757

theorem tailTrace_1903449 : CollatzResearch.WordTrace tailWord_1903449 prefixEnd_1903449 434392994808901546992757 := by
  unfold tailWord_1903449
  simp only [CollatzResearch.WordTrace]
  refine ⟨69424488481136831053113401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46282992320757887368742267 69424488481136831053113401)
  ·
    refine ⟨52068366360852623289835051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69424488481136831053113401 52068366360852623289835051)
    ·
      refine ⟨78102549541278934934752577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52068366360852623289835051 78102549541278934934752577)
      ·
        refine ⟨58576912155959201201064433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78102549541278934934752577 58576912155959201201064433)
        ·
          refine ⟨43932684116969400900798325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58576912155959201201064433 43932684116969400900798325)
          ·
            refine ⟨4118689135965881334449843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43932684116969400900798325 4118689135965881334449843)
            ·
              refine ⟨6178033703948822001674765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4118689135965881334449843 6178033703948822001674765)
              ·
                refine ⟨2316762638980808250628037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6178033703948822001674765 2316762638980808250628037)
                ·
                  refine ⟨434392994808901546992757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2316762638980808250628037 434392994808901546992757)
                  ·
                    rfl

theorem cell21_1903449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 3, 4].length) (baseStart_1903449 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1903449 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1903449 prefixEnd_1903449 := by exact prefixLift 1903449
  have htrace : WordTrace (prefixWord ++ tailWord_1903449) baseStart_1903449 baseEnd_1903449 := by
    simpa [prefixWord, tailWord_1903449, baseEnd_1903449] using wordTrace_append hprefix tailTrace_1903449
  have hstable : (prefixWord ++ tailWord_1903449).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1903449).length < 2 ^ (prefixWord ++ tailWord_1903449).sum := by decide
  have hdescent : baseEnd_1903449 < baseStart_1903449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1903449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1903463 : List Nat := [1, 1, 5, 1, 2, 2, 2, 7]
def baseStart_1903463 : Nat := 118140960795 + 1903463 * 2 ^ 59
def prefixEnd_1903463 : Nat := 4983230072969 + 3 ^ 40 * 1903463 * 2
def baseEnd_1903463 : Nat := 144798729933213544586465

theorem tailTrace_1903463 : CollatzResearch.WordTrace tailWord_1903463 prefixEnd_1903463 144798729933213544586465 := by
  unfold tailWord_1903463
  simp only [CollatzResearch.WordTrace]
  refine ⟨69424999103086111444123043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46283332735390740962748695 69424999103086111444123043)
  ·
    refine ⟨104137498654629167166184565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69424999103086111444123043 104137498654629167166184565)
    ·
      refine ⟨9762890498871484421829803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 104137498654629167166184565 9762890498871484421829803)
      ·
        refine ⟨14644335748307226632744705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9762890498871484421829803 14644335748307226632744705)
        ·
          refine ⟨10983251811230419974558529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14644335748307226632744705 10983251811230419974558529)
          ·
            refine ⟨8237438858422814980918897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10983251811230419974558529 8237438858422814980918897)
            ·
              refine ⟨6178079143817111235689173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8237438858422814980918897 6178079143817111235689173)
              ·
                refine ⟨144798729933213544586465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6178079143817111235689173 144798729933213544586465)
                ·
                  rfl

theorem cell21_1903463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 7].length) (baseStart_1903463 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1903463 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1903463 prefixEnd_1903463 := by exact prefixLift 1903463
  have htrace : WordTrace (prefixWord ++ tailWord_1903463) baseStart_1903463 baseEnd_1903463 := by
    simpa [prefixWord, tailWord_1903463, baseEnd_1903463] using wordTrace_append hprefix tailTrace_1903463
  have hstable : (prefixWord ++ tailWord_1903463).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1903463).length < 2 ^ (prefixWord ++ tailWord_1903463).sum := by decide
  have hdescent : baseEnd_1903463 < baseStart_1903463 := by decide
  rcases family_descends (prefixWord ++ tailWord_1903463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1903573 : List Nat := [1, 3, 2, 3, 3, 2, 2, 5]
def baseStart_1903573 : Nat := 118140960795 + 1903573 * 2 ^ 59
def prefixEnd_1903573 : Nat := 4983230072969 + 3 ^ 40 * 1903573 * 2
def baseEnd_1903573 : Nat := 144807097766101628975279

theorem tailTrace_1903573 : CollatzResearch.WordTrace tailWord_1903573 prefixEnd_1903573 144807097766101628975279 := by
  unfold tailWord_1903573
  simp only [CollatzResearch.WordTrace]
  refine ⟨69429011132687600230627373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46286007421791733487084915 69429011132687600230627373)
  ·
    refine ⟨26035879174757850086485265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69429011132687600230627373 26035879174757850086485265)
    ·
      refine ⟨19526909381068387564863949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26035879174757850086485265 19526909381068387564863949)
      ·
        refine ⟨7322591017900645336823981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19526909381068387564863949 7322591017900645336823981)
        ·
          refine ⟨2745971631712742001308993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7322591017900645336823981 2745971631712742001308993)
          ·
            refine ⟨2059478723784556500981745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2745971631712742001308993 2059478723784556500981745)
            ·
              refine ⟨1544609042838417375736309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2059478723784556500981745 1544609042838417375736309)
              ·
                refine ⟨144807097766101628975279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1544609042838417375736309 144807097766101628975279)
                ·
                  rfl

theorem cell21_1903573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 2, 5].length) (baseStart_1903573 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1903573 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1903573 prefixEnd_1903573 := by exact prefixLift 1903573
  have htrace : WordTrace (prefixWord ++ tailWord_1903573) baseStart_1903573 baseEnd_1903573 := by
    simpa [prefixWord, tailWord_1903573, baseEnd_1903573] using wordTrace_append hprefix tailTrace_1903573
  have hstable : (prefixWord ++ tailWord_1903573).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1903573).length < 2 ^ (prefixWord ++ tailWord_1903573).sum := by decide
  have hdescent : baseEnd_1903573 < baseStart_1903573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1903573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1903677 : List Nat := [1, 4, 1, 3, 1, 2, 2, 3, 4]
def baseStart_1903677 : Nat := 118140960795 + 1903677 * 2 ^ 59
def prefixEnd_1903677 : Nat := 4983230072969 + 3 ^ 40 * 1903677 * 2
def baseEnd_1903677 : Nat := 434445027515223817192291

theorem tailTrace_1903677 : CollatzResearch.WordTrace tailWord_1903677 prefixEnd_1903677 434445027515223817192291 := by
  unfold tailWord_1903677
  simp only [CollatzResearch.WordTrace]
  refine ⟨69432804324310825992413285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46288536216207217328275523 69432804324310825992413285)
  ·
    refine ⟨13018650810808279873577491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69432804324310825992413285 13018650810808279873577491)
    ·
      refine ⟨19527976216212419810366237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13018650810808279873577491 19527976216212419810366237)
      ·
        refine ⟨7322991081079657428887339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19527976216212419810366237 7322991081079657428887339)
        ·
          refine ⟨10984486621619486143331009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7322991081079657428887339 10984486621619486143331009)
          ·
            refine ⟨8238364966214614607498257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10984486621619486143331009 8238364966214614607498257)
            ·
              refine ⟨6178773724660960955623693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8238364966214614607498257 6178773724660960955623693)
              ·
                refine ⟨2317040146747860358358885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6178773724660960955623693 2317040146747860358358885)
                ·
                  refine ⟨434445027515223817192291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2317040146747860358358885 434445027515223817192291)
                  ·
                    rfl

theorem cell21_1903677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 3, 4].length) (baseStart_1903677 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1903677 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1903677 prefixEnd_1903677 := by exact prefixLift 1903677
  have htrace : WordTrace (prefixWord ++ tailWord_1903677) baseStart_1903677 baseEnd_1903677 := by
    simpa [prefixWord, tailWord_1903677, baseEnd_1903677] using wordTrace_append hprefix tailTrace_1903677
  have hstable : (prefixWord ++ tailWord_1903677).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1903677).length < 2 ^ (prefixWord ++ tailWord_1903677).sum := by decide
  have hdescent : baseEnd_1903677 < baseStart_1903677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1903677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1903722 : List Nat := [3, 1, 3, 2, 2, 1, 1, 3, 5]
def baseStart_1903722 : Nat := 118140960795 + 1903722 * 2 ^ 59
def prefixEnd_1903722 : Nat := 4983230072969 + 3 ^ 40 * 1903722 * 2
def baseEnd_1903722 : Nat := 434455297128313738942199

theorem tailTrace_1903722 : CollatzResearch.WordTrace tailWord_1903722 prefixEnd_1903722 434455297128313738942199 := by
  unfold tailWord_1903722
  simp only [CollatzResearch.WordTrace]
  refine ⟨17358611402286949669450355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46289630406098532451867613 17358611402286949669450355)
  ·
    refine ⟨26037917103430424504175533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17358611402286949669450355 26037917103430424504175533)
    ·
      refine ⟨9764218913786409189065825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26037917103430424504175533 9764218913786409189065825)
      ·
        refine ⟨7323164185339806891799369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9764218913786409189065825 7323164185339806891799369)
        ·
          refine ⟨5492373139004855168849527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7323164185339806891799369 5492373139004855168849527)
          ·
            refine ⟨8238559708507282753274291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5492373139004855168849527 8238559708507282753274291)
            ·
              refine ⟨12357839562760924129911437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8238559708507282753274291 12357839562760924129911437)
              ·
                refine ⟨4634189836035346548716789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12357839562760924129911437 4634189836035346548716789)
                ·
                  refine ⟨434455297128313738942199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4634189836035346548716789 434455297128313738942199)
                  ·
                    rfl

theorem cell21_1903722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 3, 5].length) (baseStart_1903722 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1903722 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1903722 prefixEnd_1903722 := by exact prefixLift 1903722
  have htrace : WordTrace (prefixWord ++ tailWord_1903722) baseStart_1903722 baseEnd_1903722 := by
    simpa [prefixWord, tailWord_1903722, baseEnd_1903722] using wordTrace_append hprefix tailTrace_1903722
  have hstable : (prefixWord ++ tailWord_1903722).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1903722).length < 2 ^ (prefixWord ++ tailWord_1903722).sum := by decide
  have hdescent : baseEnd_1903722 < baseStart_1903722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1903722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1903736 : List Nat := [2, 1, 2, 1, 1, 1, 4, 5, 4]
def baseStart_1903736 : Nat := 118140960795 + 1903736 * 2 ^ 59
def prefixEnd_1903736 : Nat := 4983230072969 + 3 ^ 40 * 1903736 * 2
def baseEnd_1903736 : Nat := 434458492119052825708837

theorem tailTrace_1903736 : CollatzResearch.WordTrace tailWord_1903736 prefixEnd_1903736 434458492119052825708837 := by
  unfold tailWord_1903736
  simp only [CollatzResearch.WordTrace]
  refine ⟨34717478115548539534405531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46289970820731386045874041 34717478115548539534405531)
  ·
    refine ⟨52076217173322809301608297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34717478115548539534405531 52076217173322809301608297)
    ·
      refine ⟨39057162879992106976206223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52076217173322809301608297 39057162879992106976206223)
      ·
        refine ⟨58585744319988160464309335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39057162879992106976206223 58585744319988160464309335)
        ·
          refine ⟨87878616479982240696464003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58585744319988160464309335 87878616479982240696464003)
          ·
            refine ⟨131817924719973361044696005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87878616479982240696464003 131817924719973361044696005)
            ·
              refine ⟨24715860884995005195880501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 131817924719973361044696005 24715860884995005195880501)
              ·
                refine ⟨2317111957968281737113797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24715860884995005195880501 2317111957968281737113797)
                ·
                  refine ⟨434458492119052825708837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2317111957968281737113797 434458492119052825708837)
                  ·
                    rfl

theorem cell21_1903736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 5, 4].length) (baseStart_1903736 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1903736 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1903736 prefixEnd_1903736 := by exact prefixLift 1903736
  have htrace : WordTrace (prefixWord ++ tailWord_1903736) baseStart_1903736 baseEnd_1903736 := by
    simpa [prefixWord, tailWord_1903736, baseEnd_1903736] using wordTrace_append hprefix tailTrace_1903736
  have hstable : (prefixWord ++ tailWord_1903736).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1903736).length < 2 ^ (prefixWord ++ tailWord_1903736).sum := by decide
  have hdescent : baseEnd_1903736 < baseStart_1903736 := by decide
  rcases family_descends (prefixWord ++ tailWord_1903736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1903742 : List Nat := [4, 2, 4, 1, 1, 1, 1, 7]
def baseStart_1903742 : Nat := 118140960795 + 1903742 * 2 ^ 59
def prefixEnd_1903742 : Nat := 4983230072969 + 3 ^ 40 * 1903742 * 2
def baseEnd_1903742 : Nat := 144819953800266049536275

theorem tailTrace_1903742 : CollatzResearch.WordTrace tailWord_1903742 prefixEnd_1903742 144819953800266049536275 := by
  unfold tailWord_1903742
  simp only [CollatzResearch.WordTrace]
  refine ⟨8679396883634417761691185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46290116712716894729019653 8679396883634417761691185)
  ·
    refine ⟨6509547662725813321268389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8679396883634417761691185 6509547662725813321268389)
    ·
      refine ⟨1220540186761089997737823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6509547662725813321268389 1220540186761089997737823)
      ·
        refine ⟨1830810280141634996606735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1220540186761089997737823 1830810280141634996606735)
        ·
          refine ⟨2746215420212452494910103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1830810280141634996606735 2746215420212452494910103)
          ·
            refine ⟨4119323130318678742365155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2746215420212452494910103 4119323130318678742365155)
            ·
              refine ⟨6178984695478018113547733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4119323130318678742365155 6178984695478018113547733)
              ·
                refine ⟨144819953800266049536275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6178984695478018113547733 144819953800266049536275)
                ·
                  rfl

theorem cell21_1903742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 7].length) (baseStart_1903742 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1903742 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1903742 prefixEnd_1903742 := by exact prefixLift 1903742
  have htrace : WordTrace (prefixWord ++ tailWord_1903742) baseStart_1903742 baseEnd_1903742 := by
    simpa [prefixWord, tailWord_1903742, baseEnd_1903742] using wordTrace_append hprefix tailTrace_1903742
  have hstable : (prefixWord ++ tailWord_1903742).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1903742).length < 2 ^ (prefixWord ++ tailWord_1903742).sum := by decide
  have hdescent : baseEnd_1903742 < baseStart_1903742 := by decide
  rcases family_descends (prefixWord ++ tailWord_1903742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1903767 : List Nat := [1, 1, 3, 3, 3, 3, 7]
def baseStart_1903767 : Nat := 118140960795 + 1903767 * 2 ^ 59
def prefixEnd_1903767 : Nat := 4983230072969 + 3 ^ 40 * 1903767 * 2
def baseEnd_1903767 : Nat := 48273951860155962299123

theorem tailTrace_1903767 : CollatzResearch.WordTrace tailWord_1903767 prefixEnd_1903767 48273951860155962299123 := by
  unfold tailWord_1903767
  simp only [CollatzResearch.WordTrace]
  refine ⟨69436086893984771363189555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46290724595989847575459703 69436086893984771363189555)
  ·
    refine ⟨104154130340977157044784333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69436086893984771363189555 104154130340977157044784333)
    ·
      refine ⟨39057798877866433891794125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104154130340977157044784333 39057798877866433891794125)
      ·
        refine ⟨14646674579199912709422797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39057798877866433891794125 14646674579199912709422797)
        ·
          refine ⟨5492502967199967266033549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14646674579199912709422797 5492502967199967266033549)
          ·
            refine ⟨2059688612699987724762581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5492502967199967266033549 2059688612699987724762581)
            ·
              refine ⟨48273951860155962299123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2059688612699987724762581 48273951860155962299123)
              ·
                rfl

theorem cell21_1903767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 7].length) (baseStart_1903767 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1903767 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1903767 prefixEnd_1903767 := by exact prefixLift 1903767
  have htrace : WordTrace (prefixWord ++ tailWord_1903767) baseStart_1903767 baseEnd_1903767 := by
    simpa [prefixWord, tailWord_1903767, baseEnd_1903767] using wordTrace_append hprefix tailTrace_1903767
  have hstable : (prefixWord ++ tailWord_1903767).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1903767).length < 2 ^ (prefixWord ++ tailWord_1903767).sum := by decide
  have hdescent : baseEnd_1903767 < baseStart_1903767 := by decide
  rcases family_descends (prefixWord ++ tailWord_1903767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1903829 : List Nat := [1, 3, 2, 4, 1, 1, 1, 4, 4]
def baseStart_1903829 : Nat := 118140960795 + 1903829 * 2 ^ 59
def prefixEnd_1903829 : Nat := 4983230072969 + 3 ^ 40 * 1903829 * 2
def baseEnd_1903829 : Nat := 434479715986105330658647

theorem tailTrace_1903829 : CollatzResearch.WordTrace tailWord_1903829 prefixEnd_1903829 434479715986105330658647 := by
  unfold tailWord_1903829
  simp only [CollatzResearch.WordTrace]
  refine ⟨69438348219760155951946541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46292232146506770634631027 69438348219760155951946541)
  ·
    refine ⟨26039380582410058481979953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69438348219760155951946541 26039380582410058481979953)
    ·
      refine ⟨19529535436807543861484965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26039380582410058481979953 19529535436807543861484965)
      ·
        refine ⟨3661787894401414474028431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19529535436807543861484965 3661787894401414474028431)
        ·
          refine ⟨5492681841602121711042647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3661787894401414474028431 5492681841602121711042647)
          ·
            refine ⟨8239022762403182566563971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5492681841602121711042647 8239022762403182566563971)
            ·
              refine ⟨12358534143604773849845957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8239022762403182566563971 12358534143604773849845957)
              ·
                refine ⟨2317225151925895096846117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12358534143604773849845957 2317225151925895096846117)
                ·
                  refine ⟨434479715986105330658647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2317225151925895096846117 434479715986105330658647)
                  ·
                    rfl

theorem cell21_1903829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 4, 4].length) (baseStart_1903829 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1903829 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1903829 prefixEnd_1903829 := by exact prefixLift 1903829
  have htrace : WordTrace (prefixWord ++ tailWord_1903829) baseStart_1903829 baseEnd_1903829 := by
    simpa [prefixWord, tailWord_1903829, baseEnd_1903829] using wordTrace_append hprefix tailTrace_1903829
  have hstable : (prefixWord ++ tailWord_1903829).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1903829).length < 2 ^ (prefixWord ++ tailWord_1903829).sum := by decide
  have hdescent : baseEnd_1903829 < baseStart_1903829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1903829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1903942 : List Nat := [6, 1, 1, 3, 2, 1, 1, 1, 5]
def baseStart_1903942 : Nat := 118140960795 + 1903942 * 2 ^ 59
def prefixEnd_1903942 : Nat := 4983230072969 + 3 ^ 40 * 1903942 * 2
def baseEnd_1903942 : Nat := 434505504125642245275083

theorem tailTrace_1903942 : CollatzResearch.WordTrace tailWord_1903942 prefixEnd_1903942 434505504125642245275083 := by
  unfold tailWord_1903942
  simp only [CollatzResearch.WordTrace]
  refine ⟨2170077177135961757837815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 46294979778900517500540053 2170077177135961757837815)
  ·
    refine ⟨3255115765703942636756723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2170077177135961757837815 3255115765703942636756723)
    ·
      refine ⟨4882673648555913955135085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3255115765703942636756723 4882673648555913955135085)
      ·
        refine ⟨1831002618208467733175657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4882673648555913955135085 1831002618208467733175657)
        ·
          refine ⟨1373251963656350799881743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1831002618208467733175657 1373251963656350799881743)
          ·
            refine ⟨2059877945484526199822615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1373251963656350799881743 2059877945484526199822615)
            ·
              refine ⟨3089816918226789299733923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2059877945484526199822615 3089816918226789299733923)
              ·
                refine ⟨4634725377340183949600885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3089816918226789299733923 4634725377340183949600885)
                ·
                  refine ⟨434505504125642245275083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4634725377340183949600885 434505504125642245275083)
                  ·
                    rfl

theorem cell21_1903942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 1, 1, 5].length) (baseStart_1903942 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1903942 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1903942 prefixEnd_1903942 := by exact prefixLift 1903942
  have htrace : WordTrace (prefixWord ++ tailWord_1903942) baseStart_1903942 baseEnd_1903942 := by
    simpa [prefixWord, tailWord_1903942, baseEnd_1903942] using wordTrace_append hprefix tailTrace_1903942
  have hstable : (prefixWord ++ tailWord_1903942).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1903942).length < 2 ^ (prefixWord ++ tailWord_1903942).sum := by decide
  have hdescent : baseEnd_1903942 < baseStart_1903942 := by decide
  rcases family_descends (prefixWord ++ tailWord_1903942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904001 : List Nat := [1, 2, 4, 3, 2, 2, 2, 2, 3]
def baseStart_1904001 : Nat := 118140960795 + 1904001 * 2 ^ 59
def prefixEnd_1904001 : Nat := 4983230072969 + 3 ^ 40 * 1904001 * 2
def baseEnd_1904001 : Nat := 434518968729471253791629

theorem tailTrace_1904001 : CollatzResearch.WordTrace tailWord_1904001 prefixEnd_1904001 434518968729471253791629 := by
  unfold tailWord_1904001
  simp only [CollatzResearch.WordTrace]
  refine ⟨69444621575137029327207857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46296414383424686218138571 69444621575137029327207857)
  ·
    refine ⟨52083466181352771995405893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69444621575137029327207857 52083466181352771995405893)
    ·
      refine ⟨9765649909003644749138605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52083466181352771995405893 9765649909003644749138605)
      ·
        refine ⟨3662118715876366780926977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9765649909003644749138605 3662118715876366780926977)
        ·
          refine ⟨2746589036907275085695233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3662118715876366780926977 2746589036907275085695233)
          ·
            refine ⟨2059941777680456314271425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2746589036907275085695233 2059941777680456314271425)
            ·
              refine ⟨1544956333260342235703569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2059941777680456314271425 1544956333260342235703569)
              ·
                refine ⟨1158717249945256676777677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1544956333260342235703569 1158717249945256676777677)
                ·
                  refine ⟨434518968729471253791629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1158717249945256676777677 434518968729471253791629)
                  ·
                    rfl

theorem cell21_1904001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 2, 2, 3].length) (baseStart_1904001 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1904001 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1904001 prefixEnd_1904001 := by exact prefixLift 1904001
  have htrace : WordTrace (prefixWord ++ tailWord_1904001) baseStart_1904001 baseEnd_1904001 := by
    simpa [prefixWord, tailWord_1904001, baseEnd_1904001] using wordTrace_append hprefix tailTrace_1904001
  have hstable : (prefixWord ++ tailWord_1904001).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904001).length < 2 ^ (prefixWord ++ tailWord_1904001).sum := by decide
  have hdescent : baseEnd_1904001 < baseStart_1904001 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904023 : List Nat := [1, 1, 3, 3, 1, 1, 1, 2, 8]
def baseStart_1904023 : Nat := 118140960795 + 1904023 * 2 ^ 59
def prefixEnd_1904023 : Nat := 4983230072969 + 3 ^ 40 * 1904023 * 2
def baseEnd_1904023 : Nat := 434523989429204104424917

theorem tailTrace_1904023 : CollatzResearch.WordTrace tailWord_1904023 prefixEnd_1904023 434523989429204104424917 := by
  unfold tailWord_1904023
  simp only [CollatzResearch.WordTrace]
  refine ⟨69445423981057327084508723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46296949320704884723005815 69445423981057327084508723)
  ·
    refine ⟨104168135971585990626763085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69445423981057327084508723 104168135971585990626763085)
    ·
      refine ⟨39063050989344746485036157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104168135971585990626763085 39063050989344746485036157)
      ·
        refine ⟨14648644121004279931888559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39063050989344746485036157 14648644121004279931888559)
        ·
          refine ⟨21972966181506419897832839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14648644121004279931888559 21972966181506419897832839)
          ·
            refine ⟨32959449272259629846749259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21972966181506419897832839 32959449272259629846749259)
            ·
              refine ⟨49439173908389444770123889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32959449272259629846749259 49439173908389444770123889)
              ·
                refine ⟨37079380431292083577592917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49439173908389444770123889 37079380431292083577592917)
                ·
                  refine ⟨434523989429204104424917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37079380431292083577592917 434523989429204104424917)
                  ·
                    rfl

theorem cell21_1904023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 8].length) (baseStart_1904023 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1904023 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1904023 prefixEnd_1904023 := by exact prefixLift 1904023
  have htrace : WordTrace (prefixWord ++ tailWord_1904023) baseStart_1904023 baseEnd_1904023 := by
    simpa [prefixWord, tailWord_1904023, baseEnd_1904023] using wordTrace_append hprefix tailTrace_1904023
  have hstable : (prefixWord ++ tailWord_1904023).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904023).length < 2 ^ (prefixWord ++ tailWord_1904023).sum := by decide
  have hdescent : baseEnd_1904023 < baseStart_1904023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904085 : List Nat := [1, 3, 2, 3, 1, 1, 1, 4, 5]
def baseStart_1904085 : Nat := 118140960795 + 1904085 * 2 ^ 59
def prefixEnd_1904085 : Nat := 4983230072969 + 3 ^ 40 * 1904085 * 2
def baseEnd_1904085 : Nat := 434538138673905774391457

theorem tailTrace_1904085 : CollatzResearch.WordTrace tailWord_1904085 prefixEnd_1904085 434538138673905774391457 := by
  unfold tailWord_1904085
  simp only [CollatzResearch.WordTrace]
  refine ⟨69447685306832711673265709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46298456871221807782177139 69447685306832711673265709)
  ·
    refine ⟨26042881990062266877474641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69447685306832711673265709 26042881990062266877474641)
    ·
      refine ⟨19532161492546700158105981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26042881990062266877474641 19532161492546700158105981)
      ·
        refine ⟨7324560559705012559289743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19532161492546700158105981 7324560559705012559289743)
        ·
          refine ⟨10986840839557518838934615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7324560559705012559289743 10986840839557518838934615)
          ·
            refine ⟨16480261259336278258401923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10986840839557518838934615 16480261259336278258401923)
            ·
              refine ⟨24720391889004417387602885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16480261259336278258401923 24720391889004417387602885)
              ·
                refine ⟨4635073479188328260175541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24720391889004417387602885 4635073479188328260175541)
                ·
                  refine ⟨434538138673905774391457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4635073479188328260175541 434538138673905774391457)
                  ·
                    rfl

theorem cell21_1904085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 4, 5].length) (baseStart_1904085 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1904085 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1904085 prefixEnd_1904085 := by exact prefixLift 1904085
  have htrace : WordTrace (prefixWord ++ tailWord_1904085) baseStart_1904085 baseEnd_1904085 := by
    simpa [prefixWord, tailWord_1904085, baseEnd_1904085] using wordTrace_append hprefix tailTrace_1904085
  have hstable : (prefixWord ++ tailWord_1904085).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904085).length < 2 ^ (prefixWord ++ tailWord_1904085).sum := by decide
  have hdescent : baseEnd_1904085 < baseStart_1904085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904302 : List Nat := [4, 1, 4, 1, 2, 1, 1, 3, 4]
def baseStart_1904302 : Nat := 118140960795 + 1904302 * 2 ^ 59
def prefixEnd_1904302 : Nat := 4983230072969 + 3 ^ 40 * 1904302 * 2
def baseEnd_1904302 : Nat := 434587661030361619274347

theorem tailTrace_1904302 : CollatzResearch.WordTrace tailWord_1904302 prefixEnd_1904302 434587661030361619274347 := by
  unfold tailWord_1904302
  simp only [CollatzResearch.WordTrace]
  refine ⟨8681949993380819716739395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46303733298031038489276773 8681949993380819716739395)
  ·
    refine ⟨13022924990071229575109093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8681949993380819716739395 13022924990071229575109093)
    ·
      refine ⟨2441798435638355545332955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13022924990071229575109093 2441798435638355545332955)
      ·
        refine ⟨3662697653457533317999433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2441798435638355545332955 3662697653457533317999433)
        ·
          refine ⟨2747023240093149988499575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3662697653457533317999433 2747023240093149988499575)
          ·
            refine ⟨4120534860139724982749363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2747023240093149988499575 4120534860139724982749363)
            ·
              refine ⟨6180802290209587474124045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4120534860139724982749363 6180802290209587474124045)
              ·
                refine ⟨2317800858828595302796517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6180802290209587474124045 2317800858828595302796517)
                ·
                  refine ⟨434587661030361619274347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2317800858828595302796517 434587661030361619274347)
                  ·
                    rfl

theorem cell21_1904302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 3, 4].length) (baseStart_1904302 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1904302 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1904302 prefixEnd_1904302 := by exact prefixLift 1904302
  have htrace : WordTrace (prefixWord ++ tailWord_1904302) baseStart_1904302 baseEnd_1904302 := by
    simpa [prefixWord, tailWord_1904302, baseEnd_1904302] using wordTrace_append hprefix tailTrace_1904302
  have hstable : (prefixWord ++ tailWord_1904302).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904302).length < 2 ^ (prefixWord ++ tailWord_1904302).sum := by decide
  have hdescent : baseEnd_1904302 < baseStart_1904302 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904341 : List Nat := [1, 3, 2, 15]
def baseStart_1904341 : Nat := 118140960795 + 1904341 * 2 ^ 59
def prefixEnd_1904341 : Nat := 4983230072969 + 3 ^ 40 * 1904341 * 2
def baseEnd_1904341 : Nat := 1788463215480272502569

theorem tailTrace_1904341 : CollatzResearch.WordTrace tailWord_1904341 prefixEnd_1904341 1788463215480272502569 := by
  unfold tailWord_1904341
  simp only [CollatzResearch.WordTrace]
  refine ⟨69457022393905267394584877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46304681595936844929723251 69457022393905267394584877)
  ·
    refine ⟨26046383397714475272969329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69457022393905267394584877 26046383397714475272969329)
    ·
      refine ⟨19534787548285856454726997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26046383397714475272969329 19534787548285856454726997)
      ·
        refine ⟨1788463215480272502569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 15 19534787548285856454726997 1788463215480272502569)
        ·
          rfl

theorem cell21_1904341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 15].length) (baseStart_1904341 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1904341 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1904341 prefixEnd_1904341 := by exact prefixLift 1904341
  have htrace : WordTrace (prefixWord ++ tailWord_1904341) baseStart_1904341 baseEnd_1904341 := by
    simpa [prefixWord, tailWord_1904341, baseEnd_1904341] using wordTrace_append hprefix tailTrace_1904341
  have hstable : (prefixWord ++ tailWord_1904341).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904341).length < 2 ^ (prefixWord ++ tailWord_1904341).sum := by decide
  have hdescent : baseEnd_1904341 < baseStart_1904341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904344 : List Nat := [2, 1, 2, 2, 3, 1, 4, 2, 4]
def baseStart_1904344 : Nat := 118140960795 + 1904344 * 2 ^ 59
def prefixEnd_1904344 : Nat := 4983230072969 + 3 ^ 40 * 1904344 * 2
def baseEnd_1904344 : Nat := 434597246002578879574261

theorem tailTrace_1904344 : CollatzResearch.WordTrace tailWord_1904344 prefixEnd_1904344 434597246002578879574261 := by
  unfold tailWord_1904344
  simp only [CollatzResearch.WordTrace]
  refine ⟨34728565906447199453472043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46304754541929599271296057 34728565906447199453472043)
  ·
    refine ⟨52092848859670799180208065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34728565906447199453472043 52092848859670799180208065)
    ·
      refine ⟨39069636644753099385156049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52092848859670799180208065 39069636644753099385156049)
      ·
        refine ⟨29302227483564824538867037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39069636644753099385156049 29302227483564824538867037)
        ·
          refine ⟨10988335306336809202075139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29302227483564824538867037 10988335306336809202075139)
          ·
            refine ⟨16482502959505213803112709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10988335306336809202075139 16482502959505213803112709)
            ·
              refine ⟨3090469304907227588083633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16482502959505213803112709 3090469304907227588083633)
              ·
                refine ⟨2317851978680420691062725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3090469304907227588083633 2317851978680420691062725)
                ·
                  refine ⟨434597246002578879574261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2317851978680420691062725 434597246002578879574261)
                  ·
                    rfl

theorem cell21_1904344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 4, 2, 4].length) (baseStart_1904344 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1904344 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1904344 prefixEnd_1904344 := by exact prefixLift 1904344
  have htrace : WordTrace (prefixWord ++ tailWord_1904344) baseStart_1904344 baseEnd_1904344 := by
    simpa [prefixWord, tailWord_1904344, baseEnd_1904344] using wordTrace_append hprefix tailTrace_1904344
  have hstable : (prefixWord ++ tailWord_1904344).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904344).length < 2 ^ (prefixWord ++ tailWord_1904344).sum := by decide
  have hdescent : baseEnd_1904344 < baseStart_1904344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904403 : List Nat := [1, 1, 1, 2, 1, 3, 2, 6, 4]
def baseStart_1904403 : Nat := 118140960795 + 1904403 * 2 ^ 59
def prefixEnd_1904403 : Nat := 4983230072969 + 3 ^ 40 * 1904403 * 2
def baseEnd_1904403 : Nat := 434610710606407888090807

theorem tailTrace_1904403 : CollatzResearch.WordTrace tailWord_1904403 prefixEnd_1904403 434610710606407888090807 := by
  unfold tailWord_1904403
  simp only [CollatzResearch.WordTrace]
  refine ⟨69459283719680651983341863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46306189146453767988894575 69459283719680651983341863)
  ·
    refine ⟨104188925579520977975012795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69459283719680651983341863 104188925579520977975012795)
    ·
      refine ⟨156283388369281466962519193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104188925579520977975012795 156283388369281466962519193)
      ·
        refine ⟨117212541276961100221889395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156283388369281466962519193 117212541276961100221889395)
        ·
          refine ⟨175818811915441650332834093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117212541276961100221889395 175818811915441650332834093)
          ·
            refine ⟨65932054468290618874812785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 175818811915441650332834093 65932054468290618874812785)
            ·
              refine ⟨49449040851217964156109589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65932054468290618874812785 49449040851217964156109589)
              ·
                refine ⟨2317923789900842069817637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 49449040851217964156109589 2317923789900842069817637)
                ·
                  refine ⟨434610710606407888090807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2317923789900842069817637 434610710606407888090807)
                  ·
                    rfl

theorem cell21_1904403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 6, 4].length) (baseStart_1904403 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1904403 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1904403 prefixEnd_1904403 := by exact prefixLift 1904403
  have htrace : WordTrace (prefixWord ++ tailWord_1904403) baseStart_1904403 baseEnd_1904403 := by
    simpa [prefixWord, tailWord_1904403, baseEnd_1904403] using wordTrace_append hprefix tailTrace_1904403
  have hstable : (prefixWord ++ tailWord_1904403).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904403).length < 2 ^ (prefixWord ++ tailWord_1904403).sum := by decide
  have hdescent : baseEnd_1904403 < baseStart_1904403 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904434 : List Nat := [3, 2, 1, 1, 3, 3, 1, 7]
def baseStart_1904434 : Nat := 118140960795 + 1904434 * 2 ^ 59
def prefixEnd_1904434 : Nat := 4983230072969 + 3 ^ 40 * 1904434 * 2
def baseEnd_1904434 : Nat := 144872595076252907691359

theorem tailTrace_1904434 : CollatzResearch.WordTrace tailWord_1904434 prefixEnd_1904434 144872595076252907691359 := by
  unfold tailWord_1904434
  simp only [CollatzResearch.WordTrace]
  refine ⟨17365103595642086069430089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46306942921712229518480237 17365103595642086069430089)
  ·
    refine ⟨13023827696731564552072567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17365103595642086069430089 13023827696731564552072567)
    ·
      refine ⟨19535741545097346828108851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13023827696731564552072567 19535741545097346828108851)
      ·
        refine ⟨29303612317646020242163277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19535741545097346828108851 29303612317646020242163277)
        ·
          refine ⟨10988854619117257590811229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29303612317646020242163277 10988854619117257590811229)
          ·
            refine ⟨4120820482168971596554211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10988854619117257590811229 4120820482168971596554211)
            ·
              refine ⟨6181230723253457394831317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4120820482168971596554211 6181230723253457394831317)
              ·
                refine ⟨144872595076252907691359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6181230723253457394831317 144872595076252907691359)
                ·
                  rfl

theorem cell21_1904434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 7].length) (baseStart_1904434 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1904434 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1904434 prefixEnd_1904434 := by exact prefixLift 1904434
  have htrace : WordTrace (prefixWord ++ tailWord_1904434) baseStart_1904434 baseEnd_1904434 := by
    simpa [prefixWord, tailWord_1904434, baseEnd_1904434] using wordTrace_append hprefix tailTrace_1904434
  have hstable : (prefixWord ++ tailWord_1904434).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904434).length < 2 ^ (prefixWord ++ tailWord_1904434).sum := by decide
  have hdescent : baseEnd_1904434 < baseStart_1904434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904465 : List Nat := [1, 2, 2, 1, 5, 1, 3, 1, 5]
def baseStart_1904465 : Nat := 118140960795 + 1904465 * 2 ^ 59
def prefixEnd_1904465 : Nat := 4983230072969 + 3 ^ 40 * 1904465 * 2
def baseEnd_1904465 : Nat := 434624859851109558057347

theorem tailTrace_1904465 : CollatzResearch.WordTrace tailWord_1904465 prefixEnd_1904465 434624859851109558057347 := by
  unfold tailWord_1904465
  simp only [CollatzResearch.WordTrace]
  refine ⟨69461545045456036572098849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46307696696970691048065899 69461545045456036572098849)
  ·
    refine ⟨52096158784092027429074137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69461545045456036572098849 52096158784092027429074137)
    ·
      refine ⟨39072119088069020571805603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52096158784092027429074137 39072119088069020571805603)
      ·
        refine ⟨58608178632103530857708405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39072119088069020571805603 58608178632103530857708405)
        ·
          refine ⟨5494516746759706017910163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58608178632103530857708405 5494516746759706017910163)
          ·
            refine ⟨8241775120139559026865245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5494516746759706017910163 8241775120139559026865245)
            ·
              refine ⟨3090665670052334635074467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8241775120139559026865245 3090665670052334635074467)
              ·
                refine ⟨4635998505078501952611701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3090665670052334635074467 4635998505078501952611701)
                ·
                  refine ⟨434624859851109558057347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4635998505078501952611701 434624859851109558057347)
                  ·
                    rfl

theorem cell21_1904465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 3, 1, 5].length) (baseStart_1904465 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1904465 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1904465 prefixEnd_1904465 := by exact prefixLift 1904465
  have htrace : WordTrace (prefixWord ++ tailWord_1904465) baseStart_1904465 baseEnd_1904465 := by
    simpa [prefixWord, tailWord_1904465, baseEnd_1904465] using wordTrace_append hprefix tailTrace_1904465
  have hstable : (prefixWord ++ tailWord_1904465).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904465).length < 2 ^ (prefixWord ++ tailWord_1904465).sum := by decide
  have hdescent : baseEnd_1904465 < baseStart_1904465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904524 : List Nat := [2, 2, 1, 2, 1, 2, 1, 5, 5]
def baseStart_1904524 : Nat := 118140960795 + 1904524 * 2 ^ 59
def prefixEnd_1904524 : Nat := 4983230072969 + 3 ^ 40 * 1904524 * 2
def baseEnd_1904524 : Nat := 434638324454938566573893

theorem tailTrace_1904524 : CollatzResearch.WordTrace tailWord_1904524 prefixEnd_1904524 434638324454938566573893 := by
  unfold tailWord_1904524
  simp only [CollatzResearch.WordTrace]
  refine ⟨34731848476121144824248313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46309131301494859765664417 34731848476121144824248313)
  ·
    refine ⟨26048886357090858618186235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34731848476121144824248313 26048886357090858618186235)
    ·
      refine ⟨39073329535636287927279353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26048886357090858618186235 39073329535636287927279353)
      ·
        refine ⟨29304997151727215945459515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39073329535636287927279353 29304997151727215945459515)
        ·
          refine ⟨43957495727590823918189273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29304997151727215945459515 43957495727590823918189273)
          ·
            refine ⟨32968121795693117938641955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43957495727590823918189273 32968121795693117938641955)
            ·
              refine ⟨49452182693539676907962933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32968121795693117938641955 49452182693539676907962933)
              ·
                refine ⟨4636142127519344710121525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49452182693539676907962933 4636142127519344710121525)
                ·
                  refine ⟨434638324454938566573893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4636142127519344710121525 434638324454938566573893)
                  ·
                    rfl

theorem cell21_1904524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 5, 5].length) (baseStart_1904524 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1904524 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1904524 prefixEnd_1904524 := by exact prefixLift 1904524
  have htrace : WordTrace (prefixWord ++ tailWord_1904524) baseStart_1904524 baseEnd_1904524 := by
    simpa [prefixWord, tailWord_1904524, baseEnd_1904524] using wordTrace_append hprefix tailTrace_1904524
  have hstable : (prefixWord ++ tailWord_1904524).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904524).length < 2 ^ (prefixWord ++ tailWord_1904524).sum := by decide
  have hdescent : baseEnd_1904524 < baseStart_1904524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904541 : List Nat := [1, 4, 2, 1, 2, 3, 1, 2, 5]
def baseStart_1904541 : Nat := 118140960795 + 1904541 * 2 ^ 59
def prefixEnd_1904541 : Nat := 4983230072969 + 3 ^ 40 * 1904541 * 2
def baseEnd_1904541 : Nat := 434642204086550314790525

theorem tailTrace_1904541 : CollatzResearch.WordTrace tailWord_1904541 prefixEnd_1904541 434642204086550314790525 := by
  unfold tailWord_1904541
  simp only [CollatzResearch.WordTrace]
  refine ⟨69464316993180701551865477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46309544662120467701243651 69464316993180701551865477)
  ·
    refine ⟨13024559436221381540974777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69464316993180701551865477 13024559436221381540974777)
    ·
      refine ⟨9768419577166036155731083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13024559436221381540974777 9768419577166036155731083)
      ·
        refine ⟨14652629365749054233596625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9768419577166036155731083 14652629365749054233596625)
        ·
          refine ⟨10989472024311790675197469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14652629365749054233596625 10989472024311790675197469)
          ·
            refine ⟨4121052009116921503199051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10989472024311790675197469 4121052009116921503199051)
            ·
              refine ⟨6181578013675382254798577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4121052009116921503199051 6181578013675382254798577)
              ·
                refine ⟨4636183510256536691098933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6181578013675382254798577 4636183510256536691098933)
                ·
                  refine ⟨434642204086550314790525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4636183510256536691098933 434642204086550314790525)
                  ·
                    rfl

theorem cell21_1904541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 2, 5].length) (baseStart_1904541 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1904541 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1904541 prefixEnd_1904541 := by exact prefixLift 1904541
  have htrace : WordTrace (prefixWord ++ tailWord_1904541) baseStart_1904541 baseEnd_1904541 := by
    simpa [prefixWord, tailWord_1904541, baseEnd_1904541] using wordTrace_append hprefix tailTrace_1904541
  have hstable : (prefixWord ++ tailWord_1904541).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904541).length < 2 ^ (prefixWord ++ tailWord_1904541).sum := by decide
  have hdescent : baseEnd_1904541 < baseStart_1904541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904569 : List Nat := [1, 2, 1, 4, 2, 1, 10]
def baseStart_1904569 : Nat := 118140960795 + 1904569 * 2 ^ 59
def prefixEnd_1904569 : Nat := 4983230072969 + 3 ^ 40 * 1904569 * 2
def baseEnd_1904569 : Nat := 48294288229780943147089

theorem tailTrace_1904569 : CollatzResearch.WordTrace tailWord_1904569 prefixEnd_1904569 48294288229780943147089 := by
  unfold tailWord_1904569
  simp only [CollatzResearch.WordTrace]
  refine ⟨69465338237079262333884761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46310225491386174889256507 69465338237079262333884761)
  ·
    refine ⟨52099003677809446750413571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69465338237079262333884761 52099003677809446750413571)
    ·
      refine ⟨78148505516714170125620357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52099003677809446750413571 78148505516714170125620357)
      ·
        refine ⟨14652844784383906898553817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78148505516714170125620357 14652844784383906898553817)
        ·
          refine ⟨10989633588287930173915363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14652844784383906898553817 10989633588287930173915363)
          ·
            refine ⟨16484450382431895260873045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10989633588287930173915363 16484450382431895260873045)
            ·
              refine ⟨48294288229780943147089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16484450382431895260873045 48294288229780943147089)
              ·
                rfl

theorem cell21_1904569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 10].length) (baseStart_1904569 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1904569 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1904569 prefixEnd_1904569 := by exact prefixLift 1904569
  have htrace : WordTrace (prefixWord ++ tailWord_1904569) baseStart_1904569 baseEnd_1904569 := by
    simpa [prefixWord, tailWord_1904569, baseEnd_1904569] using wordTrace_append hprefix tailTrace_1904569
  have hstable : (prefixWord ++ tailWord_1904569).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904569).length < 2 ^ (prefixWord ++ tailWord_1904569).sum := by decide
  have hdescent : baseEnd_1904569 < baseStart_1904569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904600 : List Nat := [2, 1, 2, 2, 2, 2, 1, 4, 5]
def baseStart_1904600 : Nat := 118140960795 + 1904600 * 2 ^ 59
def prefixEnd_1904600 : Nat := 4983230072969 + 3 ^ 40 * 1904600 * 2
def baseEnd_1904600 : Nat := 434655668690379323307071

theorem tailTrace_1904600 : CollatzResearch.WordTrace tailWord_1904600 prefixEnd_1904600 434655668690379323307071 := by
  unfold tailWord_1904600
  simp only [CollatzResearch.WordTrace]
  refine ⟨34733234449983477314131627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46310979266644636418842169 34733234449983477314131627)
  ·
    refine ⟨52099851674975215971197441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34733234449983477314131627 52099851674975215971197441)
    ·
      refine ⟨39074888756231411978398081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52099851674975215971197441 39074888756231411978398081)
      ·
        refine ⟨29306166567173558983798561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39074888756231411978398081 29306166567173558983798561)
        ·
          refine ⟨21979624925380169237848921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29306166567173558983798561 21979624925380169237848921)
          ·
            refine ⟨16484718694035126928386691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21979624925380169237848921 16484718694035126928386691)
            ·
              refine ⟨24727078041052690392580037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16484718694035126928386691 24727078041052690392580037)
              ·
                refine ⟨4636327132697379448608757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24727078041052690392580037 4636327132697379448608757)
                ·
                  refine ⟨434655668690379323307071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4636327132697379448608757 434655668690379323307071)
                  ·
                    rfl

theorem cell21_1904600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 4, 5].length) (baseStart_1904600 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1904600 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1904600 prefixEnd_1904600 := by exact prefixLift 1904600
  have htrace : WordTrace (prefixWord ++ tailWord_1904600) baseStart_1904600 baseEnd_1904600 := by
    simpa [prefixWord, tailWord_1904600, baseEnd_1904600] using wordTrace_append hprefix tailTrace_1904600
  have hstable : (prefixWord ++ tailWord_1904600).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904600).length < 2 ^ (prefixWord ++ tailWord_1904600).sum := by decide
  have hdescent : baseEnd_1904600 < baseStart_1904600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904645 : List Nat := [1, 3, 1, 1, 2, 4, 1, 8]
def baseStart_1904645 : Nat := 118140960795 + 1904645 * 2 ^ 59
def prefixEnd_1904645 : Nat := 4983230072969 + 3 ^ 40 * 1904645 * 2
def baseEnd_1904645 : Nat := 144888646101156415018993

theorem tailTrace_1904645 : CollatzResearch.WordTrace tailWord_1904645 prefixEnd_1904645 144888646101156415018993 := by
  unfold tailWord_1904645
  simp only [CollatzResearch.WordTrace]
  refine ⟨69468110184803927313651389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46312073456535951542434259 69468110184803927313651389)
  ·
    refine ⟨26050541319301472742619271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69468110184803927313651389 26050541319301472742619271)
    ·
      refine ⟨39075811978952209113928907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26050541319301472742619271 39075811978952209113928907)
      ·
        refine ⟨58613717968428313670893361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39075811978952209113928907 58613717968428313670893361)
        ·
          refine ⟨43960288476321235253170021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58613717968428313670893361 43960288476321235253170021)
          ·
            refine ⟨8242554089310231609969379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43960288476321235253170021 8242554089310231609969379)
            ·
              refine ⟨12363831133965347414954069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8242554089310231609969379 12363831133965347414954069)
              ·
                refine ⟨144888646101156415018993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12363831133965347414954069 144888646101156415018993)
                ·
                  rfl

theorem cell21_1904645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 8].length) (baseStart_1904645 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1904645 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1904645 prefixEnd_1904645 := by exact prefixLift 1904645
  have htrace : WordTrace (prefixWord ++ tailWord_1904645) baseStart_1904645 baseEnd_1904645 := by
    simpa [prefixWord, tailWord_1904645, baseEnd_1904645] using wordTrace_append hprefix tailTrace_1904645
  have hstable : (prefixWord ++ tailWord_1904645).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904645).length < 2 ^ (prefixWord ++ tailWord_1904645).sum := by decide
  have hdescent : baseEnd_1904645 < baseStart_1904645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904679 : List Nat := [1, 1, 7, 1, 3, 8]
def baseStart_1904679 : Nat := 118140960795 + 1904679 * 2 ^ 59
def prefixEnd_1904679 : Nat := 4983230072969 + 3 ^ 40 * 1904679 * 2
def baseEnd_1904679 : Nat := 16099025835803434870009

theorem tailTrace_1904679 : CollatzResearch.WordTrace tailWord_1904679 prefixEnd_1904679 16099025835803434870009 := by
  unfold tailWord_1904679
  simp only [CollatzResearch.WordTrace]
  refine ⟨69469350266680751120389091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46312900177787167413592727 69469350266680751120389091)
  ·
    refine ⟨104204025400021126680583637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69469350266680751120389091 104204025400021126680583637)
    ·
      refine ⟨2442281845312995156576179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 104204025400021126680583637 2442281845312995156576179)
      ·
        refine ⟨3663422767969492734864269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2442281845312995156576179 3663422767969492734864269)
        ·
          refine ⟨1373783537988559775574101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3663422767969492734864269 1373783537988559775574101)
          ·
            refine ⟨16099025835803434870009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1373783537988559775574101 16099025835803434870009)
            ·
              rfl

theorem cell21_1904679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 8].length) (baseStart_1904679 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1904679 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1904679 prefixEnd_1904679 := by exact prefixLift 1904679
  have htrace : WordTrace (prefixWord ++ tailWord_1904679) baseStart_1904679 baseEnd_1904679 := by
    simpa [prefixWord, tailWord_1904679, baseEnd_1904679] using wordTrace_append hprefix tailTrace_1904679
  have hstable : (prefixWord ++ tailWord_1904679).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904679).length < 2 ^ (prefixWord ++ tailWord_1904679).sum := by decide
  have hdescent : baseEnd_1904679 < baseStart_1904679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904710 : List Nat := [6, 1, 1, 1, 1, 1, 3, 2, 5]
def baseStart_1904710 : Nat := 118140960795 + 1904710 * 2 ^ 59
def prefixEnd_1904710 : Nat := 4983230072969 + 3 ^ 40 * 1904710 * 2
def baseEnd_1904710 : Nat := 434680772189043576473513

theorem tailTrace_1904710 : CollatzResearch.WordTrace tailWord_1904710 prefixEnd_1904710 434680772189043576473513 := by
  unfold tailWord_1904710
  simp only [CollatzResearch.WordTrace]
  refine ⟨2170952529049013856711487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 46313653953045628943178389 2170952529049013856711487)
  ·
    refine ⟨3256428793573520785067231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2170952529049013856711487 3256428793573520785067231)
    ·
      refine ⟨4884643190360281177600847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3256428793573520785067231 4884643190360281177600847)
      ·
        refine ⟨7326964785540421766401271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4884643190360281177600847 7326964785540421766401271)
        ·
          refine ⟨10990447178310632649601907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7326964785540421766401271 10990447178310632649601907)
          ·
            refine ⟨16485670767465948974402861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10990447178310632649601907 16485670767465948974402861)
            ·
              refine ⟨6182126537799730865401073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16485670767465948974402861 6182126537799730865401073)
              ·
                refine ⟨4636594903349798149050805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6182126537799730865401073 4636594903349798149050805)
                ·
                  refine ⟨434680772189043576473513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4636594903349798149050805 434680772189043576473513)
                  ·
                    rfl

theorem cell21_1904710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_1904710 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1904710 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1904710 prefixEnd_1904710 := by exact prefixLift 1904710
  have htrace : WordTrace (prefixWord ++ tailWord_1904710) baseStart_1904710 baseEnd_1904710 := by
    simpa [prefixWord, tailWord_1904710, baseEnd_1904710] using wordTrace_append hprefix tailTrace_1904710
  have hstable : (prefixWord ++ tailWord_1904710).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904710).length < 2 ^ (prefixWord ++ tailWord_1904710).sum := by decide
  have hdescent : baseEnd_1904710 < baseStart_1904710 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904752 : List Nat := [2, 1, 1, 1, 5, 2, 1, 3, 5]
def baseStart_1904752 : Nat := 118140960795 + 1904752 * 2 ^ 59
def prefixEnd_1904752 : Nat := 4983230072969 + 3 ^ 40 * 1904752 * 2
def baseEnd_1904752 : Nat := 434690357161260836773427

theorem tailTrace_1904752 : CollatzResearch.WordTrace tailWord_1904752 prefixEnd_1904752 434690357161260836773427 := by
  unfold tailWord_1904752
  simp only [CollatzResearch.WordTrace]
  refine ⟨34736006397708142293898255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46314675196944189725197673 34736006397708142293898255)
  ·
    refine ⟨52104009596562213440847383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34736006397708142293898255 52104009596562213440847383)
    ·
      refine ⟨78156014394843320161271075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52104009596562213440847383 78156014394843320161271075)
      ·
        refine ⟨117234021592264980241906613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78156014394843320161271075 117234021592264980241906613)
        ·
          refine ⟨10990689524274841897678745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 117234021592264980241906613 10990689524274841897678745)
          ·
            refine ⟨8243017143206131423259059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10990689524274841897678745 8243017143206131423259059)
            ·
              refine ⟨12364525714809197134888589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8243017143206131423259059 12364525714809197134888589)
              ·
                refine ⟨4636697143053448925583221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12364525714809197134888589 4636697143053448925583221)
                ·
                  refine ⟨434690357161260836773427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4636697143053448925583221 434690357161260836773427)
                  ·
                    rfl

theorem cell21_1904752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 3, 5].length) (baseStart_1904752 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1904752 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1904752 prefixEnd_1904752 := by exact prefixLift 1904752
  have htrace : WordTrace (prefixWord ++ tailWord_1904752) baseStart_1904752 baseEnd_1904752 := by
    simpa [prefixWord, tailWord_1904752, baseEnd_1904752] using wordTrace_append hprefix tailTrace_1904752
  have hstable : (prefixWord ++ tailWord_1904752).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904752).length < 2 ^ (prefixWord ++ tailWord_1904752).sum := by decide
  have hdescent : baseEnd_1904752 < baseStart_1904752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904797 : List Nat := [1, 4, 2, 1, 1, 3, 9]
def baseStart_1904797 : Nat := 118140960795 + 1904797 * 2 ^ 59
def prefixEnd_1904797 : Nat := 4983230072969 + 3 ^ 40 * 1904797 * 2
def baseEnd_1904797 : Nat := 48300069641594528724815

theorem tailTrace_1904797 : CollatzResearch.WordTrace tailWord_1904797 prefixEnd_1904797 48300069641594528724815 := by
  unfold tailWord_1904797
  simp only [CollatzResearch.WordTrace]
  refine ⟨69473654080253257273184645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46315769386835504848789763 69473654080253257273184645)
  ·
    refine ⟨13026310140047485738722121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69473654080253257273184645 13026310140047485738722121)
    ·
      refine ⟨9769732605035614304041591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13026310140047485738722121 9769732605035614304041591)
      ·
        refine ⟨14654598907553421456062387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9769732605035614304041591 14654598907553421456062387)
        ·
          refine ⟨21981898361330132184093581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14654598907553421456062387 21981898361330132184093581)
          ·
            refine ⟨8243211885498799569035093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21981898361330132184093581 8243211885498799569035093)
            ·
              refine ⟨48300069641594528724815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8243211885498799569035093 48300069641594528724815)
              ·
                rfl

theorem cell21_1904797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 9].length) (baseStart_1904797 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1904797 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1904797 prefixEnd_1904797 := by exact prefixLift 1904797
  have htrace : WordTrace (prefixWord ++ tailWord_1904797) baseStart_1904797 baseEnd_1904797 := by
    simpa [prefixWord, tailWord_1904797, baseEnd_1904797] using wordTrace_append hprefix tailTrace_1904797
  have hstable : (prefixWord ++ tailWord_1904797).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904797).length < 2 ^ (prefixWord ++ tailWord_1904797).sum := by decide
  have hdescent : baseEnd_1904797 < baseStart_1904797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904890 : List Nat := [3, 1, 1, 1, 1, 6, 3, 5]
def baseStart_1904890 : Nat := 118140960795 + 1904890 * 2 ^ 59
def prefixEnd_1904890 : Nat := 4983230072969 + 3 ^ 40 * 1904890 * 2
def baseEnd_1904890 : Nat := 144907283547134421157715

theorem tailTrace_1904890 : CollatzResearch.WordTrace tailWord_1904890 prefixEnd_1904890 144907283547134421157715 := by
  unfold tailWord_1904890
  simp only [CollatzResearch.WordTrace]
  refine ⟨17369261517229083539080031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46318030712610889437546749 17369261517229083539080031)
  ·
    refine ⟨26053892275843625308620047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17369261517229083539080031 26053892275843625308620047)
    ·
      refine ⟨39080838413765437962930071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26053892275843625308620047 39080838413765437962930071)
      ·
        refine ⟨58621257620648156944395107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39080838413765437962930071 58621257620648156944395107)
        ·
          refine ⟨87931886430972235416592661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58621257620648156944395107 87931886430972235416592661)
          ·
            refine ⟨4121807176451823535152781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 87931886430972235416592661 4121807176451823535152781)
            ·
              refine ⟨1545677691169433825682293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4121807176451823535152781 1545677691169433825682293)
              ·
                refine ⟨144907283547134421157715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1545677691169433825682293 144907283547134421157715)
                ·
                  rfl

theorem cell21_1904890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 3, 5].length) (baseStart_1904890 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1904890 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1904890 prefixEnd_1904890 := by exact prefixLift 1904890
  have htrace : WordTrace (prefixWord ++ tailWord_1904890) baseStart_1904890 baseEnd_1904890 := by
    simpa [prefixWord, tailWord_1904890, baseEnd_1904890] using wordTrace_append hprefix tailTrace_1904890
  have hstable : (prefixWord ++ tailWord_1904890).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904890).length < 2 ^ (prefixWord ++ tailWord_1904890).sum := by decide
  have hdescent : baseEnd_1904890 < baseStart_1904890 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904941 : List Nat := [1, 5, 3, 1, 3, 1, 2, 5]
def baseStart_1904941 : Nat := 118140960795 + 1904941 * 2 ^ 59
def prefixEnd_1904941 : Nat := 4983230072969 + 3 ^ 40 * 1904941 * 2
def baseEnd_1904941 : Nat := 144911163178746169374347

theorem tailTrace_1904941 : CollatzResearch.WordTrace tailWord_1904941 prefixEnd_1904941 144911163178746169374347 := by
  unfold tailWord_1904941
  simp only [CollatzResearch.WordTrace]
  refine ⟨69478906191731569866426677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46319270794487713244284451 69478906191731569866426677)
  ·
    refine ⟨6513647455474834674977501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 69478906191731569866426677 6513647455474834674977501)
    ·
      refine ⟨2442617795803063003116563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6513647455474834674977501 2442617795803063003116563)
      ·
        refine ⟨3663926693704594504674845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2442617795803063003116563 3663926693704594504674845)
        ·
          refine ⟨1373972510139222939253067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3663926693704594504674845 1373972510139222939253067)
          ·
            refine ⟨2060958765208834408879601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1373972510139222939253067 2060958765208834408879601)
            ·
              refine ⟨1545719073906625806659701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2060958765208834408879601 1545719073906625806659701)
              ·
                refine ⟨144911163178746169374347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1545719073906625806659701 144911163178746169374347)
                ·
                  rfl

theorem cell21_1904941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 2, 5].length) (baseStart_1904941 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1904941 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1904941 prefixEnd_1904941 := by exact prefixLift 1904941
  have htrace : WordTrace (prefixWord ++ tailWord_1904941) baseStart_1904941 baseEnd_1904941 := by
    simpa [prefixWord, tailWord_1904941, baseEnd_1904941] using wordTrace_append hprefix tailTrace_1904941
  have hstable : (prefixWord ++ tailWord_1904941).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904941).length < 2 ^ (prefixWord ++ tailWord_1904941).sum := by decide
  have hdescent : baseEnd_1904941 < baseStart_1904941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904949 : List Nat := [1, 3, 3, 1, 2, 1, 3, 7]
def baseStart_1904949 : Nat := 118140960795 + 1904949 * 2 ^ 59
def prefixEnd_1904949 : Nat := 4983230072969 + 3 ^ 40 * 1904949 * 2
def baseEnd_1904949 : Nat := 144911771748410757329897

theorem tailTrace_1904949 : CollatzResearch.WordTrace tailWord_1904949 prefixEnd_1904949 144911771748410757329897 := by
  unfold tailWord_1904949
  simp only [CollatzResearch.WordTrace]
  refine ⟨69479197975702587232717901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46319465317135058155145267 69479197975702587232717901)
  ·
    refine ⟨26054699240888470212269213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69479197975702587232717901 26054699240888470212269213)
    ·
      refine ⟨9770512215333176329600955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26054699240888470212269213 9770512215333176329600955)
      ·
        refine ⟨14655768322999764494401433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9770512215333176329600955 14655768322999764494401433)
        ·
          refine ⟨10991826242249823370801075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14655768322999764494401433 10991826242249823370801075)
          ·
            refine ⟨16487739363374735056201613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10991826242249823370801075 16487739363374735056201613)
            ·
              refine ⟨6182902261265525646075605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16487739363374735056201613 6182902261265525646075605)
              ·
                refine ⟨144911771748410757329897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6182902261265525646075605 144911771748410757329897)
                ·
                  rfl

theorem cell21_1904949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 7].length) (baseStart_1904949 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1904949 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1904949 prefixEnd_1904949 := by exact prefixLift 1904949
  have htrace : WordTrace (prefixWord ++ tailWord_1904949) baseStart_1904949 baseEnd_1904949 := by
    simpa [prefixWord, tailWord_1904949, baseEnd_1904949] using wordTrace_append hprefix tailTrace_1904949
  have hstable : (prefixWord ++ tailWord_1904949).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904949).length < 2 ^ (prefixWord ++ tailWord_1904949).sum := by decide
  have hdescent : baseEnd_1904949 < baseStart_1904949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904963 : List Nat := [1, 1, 1, 3, 1, 3, 2, 2, 7]
def baseStart_1904963 : Nat := 118140960795 + 1904963 * 2 ^ 59
def prefixEnd_1904963 : Nat := 4983230072969 + 3 ^ 40 * 1904963 * 2
def baseEnd_1904963 : Nat := 434738510235971358756329

theorem tailTrace_1904963 : CollatzResearch.WordTrace tailWord_1904963 prefixEnd_1904963 434738510235971358756329 := by
  unfold tailWord_1904963
  simp only [CollatzResearch.WordTrace]
  refine ⟨69479708597651867623727543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46319805731767911749151695 69479708597651867623727543)
  ·
    refine ⟨104219562896477801435591315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69479708597651867623727543 104219562896477801435591315)
    ·
      refine ⟨156329344344716702153386973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104219562896477801435591315 156329344344716702153386973)
      ·
        refine ⟨58623504129268763307520115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156329344344716702153386973 58623504129268763307520115)
        ·
          refine ⟨87935256193903144961280173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58623504129268763307520115 87935256193903144961280173)
          ·
            refine ⟨32975721072713679360480065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87935256193903144961280173 32975721072713679360480065)
            ·
              refine ⟨24731790804535259520360049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32975721072713679360480065 24731790804535259520360049)
              ·
                refine ⟨18548843103401444640270037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24731790804535259520360049 18548843103401444640270037)
                ·
                  refine ⟨434738510235971358756329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18548843103401444640270037 434738510235971358756329)
                  ·
                    rfl

theorem cell21_1904963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 7].length) (baseStart_1904963 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1904963 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1904963 prefixEnd_1904963 := by exact prefixLift 1904963
  have htrace : WordTrace (prefixWord ++ tailWord_1904963) baseStart_1904963 baseEnd_1904963 := by
    simpa [prefixWord, tailWord_1904963, baseEnd_1904963] using wordTrace_append hprefix tailTrace_1904963
  have hstable : (prefixWord ++ tailWord_1904963).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904963).length < 2 ^ (prefixWord ++ tailWord_1904963).sum := by decide
  have hdescent : baseEnd_1904963 < baseStart_1904963 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1905025 : List Nat := [1, 2, 4, 3, 1, 10]
def baseStart_1905025 : Nat := 118140960795 + 1905025 * 2 ^ 59
def prefixEnd_1905025 : Nat := 4983230072969 + 3 ^ 40 * 1905025 * 2
def baseEnd_1905025 : Nat := 16101950351136038100847

theorem tailTrace_1905025 : CollatzResearch.WordTrace tailWord_1905025 prefixEnd_1905025 16101950351136038100847 := by
  unfold tailWord_1905025
  simp only [CollatzResearch.WordTrace]
  refine ⟨69481969923427252212484529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46321313282284834808323019 69481969923427252212484529)
  ·
    refine ⟨52111477442570439159363397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69481969923427252212484529 52111477442570439159363397)
    ·
      refine ⟨9770902020481957342380637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52111477442570439159363397 9770902020481957342380637)
      ·
        refine ⟨3664088257680734003392739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9770902020481957342380637 3664088257680734003392739)
        ·
          refine ⟨5496132386521101005089109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3664088257680734003392739 5496132386521101005089109)
          ·
            refine ⟨16101950351136038100847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5496132386521101005089109 16101950351136038100847)
            ·
              rfl

theorem cell21_1905025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 10].length) (baseStart_1905025 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1905025 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1905025 prefixEnd_1905025 := by exact prefixLift 1905025
  have htrace : WordTrace (prefixWord ++ tailWord_1905025) baseStart_1905025 baseEnd_1905025 := by
    simpa [prefixWord, tailWord_1905025, baseEnd_1905025] using wordTrace_append hprefix tailTrace_1905025
  have hstable : (prefixWord ++ tailWord_1905025).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1905025).length < 2 ^ (prefixWord ++ tailWord_1905025).sum := by decide
  have hdescent : baseEnd_1905025 < baseStart_1905025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1905025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1905056 : List Nat := [2, 1, 1, 4, 1, 4, 1, 2, 5]
def baseStart_1905056 : Nat := 118140960795 + 1905056 * 2 ^ 59
def prefixEnd_1905056 : Nat := 4983230072969 + 3 ^ 40 * 1905056 * 2
def baseEnd_1905056 : Nat := 434759734103023863706139

theorem tailTrace_1905056 : CollatzResearch.WordTrace tailWord_1905056 prefixEnd_1905056 434759734103023863706139 := by
  unfold tailWord_1905056
  simp only [CollatzResearch.WordTrace]
  refine ⟨34741550293157472253431511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46322067057543296337908681 34741550293157472253431511)
  ·
    refine ⟨52112325439736208380147267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34741550293157472253431511 52112325439736208380147267)
    ·
      refine ⟨78168488159604312570220901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52112325439736208380147267 78168488159604312570220901)
      ·
        refine ⟨14656591529925808606916419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78168488159604312570220901 14656591529925808606916419)
        ·
          refine ⟨21984887294888712910374629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14656591529925808606916419 21984887294888712910374629)
          ·
            refine ⟨4122166367791633670695243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21984887294888712910374629 4122166367791633670695243)
            ·
              refine ⟨6183249551687450506042865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4122166367791633670695243 6183249551687450506042865)
              ·
                refine ⟨4637437163765587879532149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6183249551687450506042865 4637437163765587879532149)
                ·
                  refine ⟨434759734103023863706139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4637437163765587879532149 434759734103023863706139)
                  ·
                    rfl

theorem cell21_1905056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 2, 5].length) (baseStart_1905056 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1905056 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1905056 prefixEnd_1905056 := by exact prefixLift 1905056
  have htrace : WordTrace (prefixWord ++ tailWord_1905056) baseStart_1905056 baseEnd_1905056 := by
    simpa [prefixWord, tailWord_1905056, baseEnd_1905056] using wordTrace_append hprefix tailTrace_1905056
  have hstable : (prefixWord ++ tailWord_1905056).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1905056).length < 2 ^ (prefixWord ++ tailWord_1905056).sum := by decide
  have hdescent : baseEnd_1905056 < baseStart_1905056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1905056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1905073 : List Nat := [1, 2, 2, 4, 1, 2, 1, 5, 3]
def baseStart_1905073 : Nat := 118140960795 + 1905073 * 2 ^ 59
def prefixEnd_1905073 : Nat := 4983230072969 + 3 ^ 40 * 1905073 * 2
def baseEnd_1905073 : Nat := 434763613734635611922771

theorem tailTrace_1905073 : CollatzResearch.WordTrace tailWord_1905073 prefixEnd_1905073 434763613734635611922771 := by
  unfold tailWord_1905073
  simp only [CollatzResearch.WordTrace]
  refine ⟨69483720627253356410231873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46322480418168904273487915 69483720627253356410231873)
  ·
    refine ⟨52112790470440017307673905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69483720627253356410231873 52112790470440017307673905)
    ·
      refine ⟨39084592852830012980755429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52112790470440017307673905 39084592852830012980755429)
      ·
        refine ⟨7328361159905627433891643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39084592852830012980755429 7328361159905627433891643)
        ·
          refine ⟨10992541739858441150837465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7328361159905627433891643 10992541739858441150837465)
          ·
            refine ⟨8244406304893830863128099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10992541739858441150837465 8244406304893830863128099)
            ·
              refine ⟨12366609457340746294692149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8244406304893830863128099 12366609457340746294692149)
              ·
                refine ⟨1159369636625694965127389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12366609457340746294692149 1159369636625694965127389)
                ·
                  refine ⟨434763613734635611922771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1159369636625694965127389 434763613734635611922771)
                  ·
                    rfl

theorem cell21_1905073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 5, 3].length) (baseStart_1905073 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1905073 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1905073 prefixEnd_1905073 := by exact prefixLift 1905073
  have htrace : WordTrace (prefixWord ++ tailWord_1905073) baseStart_1905073 baseEnd_1905073 := by
    simpa [prefixWord, tailWord_1905073, baseEnd_1905073] using wordTrace_append hprefix tailTrace_1905073
  have hstable : (prefixWord ++ tailWord_1905073).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1905073).length < 2 ^ (prefixWord ++ tailWord_1905073).sum := by decide
  have hdescent : baseEnd_1905073 < baseStart_1905073 := by decide
  rcases family_descends (prefixWord ++ tailWord_1905073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1905163 : List Nat := [1, 1, 1, 1, 7, 2, 1, 3, 4]
def baseStart_1905163 : Nat := 118140960795 + 1905163 * 2 ^ 59
def prefixEnd_1905163 : Nat := 4983230072969 + 3 ^ 40 * 1905163 * 2
def baseEnd_1905163 : Nat := 434784152960815455422587

theorem tailTrace_1905163 : CollatzResearch.WordTrace tailWord_1905163 prefixEnd_1905163 434784152960815455422587 := by
  unfold tailWord_1905163
  simp only [CollatzResearch.WordTrace]
  refine ⟨69487003196927301781008143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46324668797951534520672095 69487003196927301781008143)
  ·
    refine ⟨104230504795390952671512215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69487003196927301781008143 104230504795390952671512215)
    ·
      refine ⟨156345757193086429007268323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104230504795390952671512215 156345757193086429007268323)
      ·
        refine ⟨234518635789629643510902485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156345757193086429007268323 234518635789629643510902485)
        ·
          refine ⟨5496530526319444769786777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 234518635789629643510902485 5496530526319444769786777)
          ·
            refine ⟨4122397894739583577340083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5496530526319444769786777 4122397894739583577340083)
            ·
              refine ⟨6183596842109375366010125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4122397894739583577340083 6183596842109375366010125)
              ·
                refine ⟨2318848815791015762253797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6183596842109375366010125 2318848815791015762253797)
                ·
                  refine ⟨434784152960815455422587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2318848815791015762253797 434784152960815455422587)
                  ·
                    rfl

theorem cell21_1905163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 3, 4].length) (baseStart_1905163 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1905163 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1905163 prefixEnd_1905163 := by exact prefixLift 1905163
  have htrace : WordTrace (prefixWord ++ tailWord_1905163) baseStart_1905163 baseEnd_1905163 := by
    simpa [prefixWord, tailWord_1905163, baseEnd_1905163] using wordTrace_append hprefix tailTrace_1905163
  have hstable : (prefixWord ++ tailWord_1905163).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1905163).length < 2 ^ (prefixWord ++ tailWord_1905163).sum := by decide
  have hdescent : baseEnd_1905163 < baseStart_1905163 := by decide
  rcases family_descends (prefixWord ++ tailWord_1905163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1905253 : List Nat := [1, 3, 1, 3, 4, 1, 8]
def baseStart_1905253 : Nat := 118140960795 + 1905253 * 2 ^ 59
def prefixEnd_1905253 : Nat := 4983230072969 + 3 ^ 40 * 1905253 * 2
def baseEnd_1905253 : Nat := 48311632465221699880267

theorem tailTrace_1905253 : CollatzResearch.WordTrace tailWord_1905253 prefixEnd_1905253 48311632465221699880267 := by
  unfold tailWord_1905253
  simp only [CollatzResearch.WordTrace]
  refine ⟨69490285766601247151784413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46326857177734164767856275 69490285766601247151784413)
  ·
    refine ⟨26058857162475467681919155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69490285766601247151784413 26058857162475467681919155)
    ·
      refine ⟨39088285743713201522878733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26058857162475467681919155 39088285743713201522878733)
      ·
        refine ⟨14658107153892450571079525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39088285743713201522878733 14658107153892450571079525)
        ·
          refine ⟨2748395091354834482077411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14658107153892450571079525 2748395091354834482077411)
          ·
            refine ⟨4122592637032251723116117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2748395091354834482077411 4122592637032251723116117)
            ·
              refine ⟨48311632465221699880267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4122592637032251723116117 48311632465221699880267)
              ·
                rfl

theorem cell21_1905253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 8].length) (baseStart_1905253 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1905253 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1905253 prefixEnd_1905253 := by exact prefixLift 1905253
  have htrace : WordTrace (prefixWord ++ tailWord_1905253) baseStart_1905253 baseEnd_1905253 := by
    simpa [prefixWord, tailWord_1905253, baseEnd_1905253] using wordTrace_append hprefix tailTrace_1905253
  have hstable : (prefixWord ++ tailWord_1905253).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1905253).length < 2 ^ (prefixWord ++ tailWord_1905253).sum := by decide
  have hdescent : baseEnd_1905253 < baseStart_1905253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1905253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1905284 : List Nat := [2, 3, 2, 1, 3, 1, 2, 2, 5]
def baseStart_1905284 : Nat := 118140960795 + 1905284 * 2 ^ 59
def prefixEnd_1905284 : Nat := 4983230072969 + 3 ^ 40 * 1905284 * 2
def baseEnd_1905284 : Nat := 434811766809346133905673

theorem tailTrace_1905284 : CollatzResearch.WordTrace tailWord_1905284 prefixEnd_1905284 434811766809346133905673 := by
  unfold tailWord_1905284
  simp only [CollatzResearch.WordTrace]
  refine ⟨34745708214744469723081453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46327610952992626297441937 34745708214744469723081453)
  ·
    refine ⟨13029640580529176146155545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34745708214744469723081453 13029640580529176146155545)
    ·
      refine ⟨9772230435396882109616659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13029640580529176146155545 9772230435396882109616659)
      ·
        refine ⟨14658345653095323164424989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9772230435396882109616659 14658345653095323164424989)
        ·
          refine ⟨5496879619910746186659371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14658345653095323164424989 5496879619910746186659371)
          ·
            refine ⟨8245319429866119279989057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5496879619910746186659371 8245319429866119279989057)
            ·
              refine ⟨6183989572399589459991793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8245319429866119279989057 6183989572399589459991793)
              ·
                refine ⟨4637992179299692094993845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6183989572399589459991793 4637992179299692094993845)
                ·
                  refine ⟨434811766809346133905673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4637992179299692094993845 434811766809346133905673)
                  ·
                    rfl

theorem cell21_1905284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 2, 5].length) (baseStart_1905284 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1905284 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1905284 prefixEnd_1905284 := by exact prefixLift 1905284
  have htrace : WordTrace (prefixWord ++ tailWord_1905284) baseStart_1905284 baseEnd_1905284 := by
    simpa [prefixWord, tailWord_1905284, baseEnd_1905284] using wordTrace_append hprefix tailTrace_1905284
  have hstable : (prefixWord ++ tailWord_1905284).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1905284).length < 2 ^ (prefixWord ++ tailWord_1905284).sum := by decide
  have hdescent : baseEnd_1905284 < baseStart_1905284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1905284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1905377 : List Nat := [1, 2, 3, 1, 4, 2, 1, 4, 3]
def baseStart_1905377 : Nat := 118140960795 + 1905377 * 2 ^ 59
def prefixEnd_1905377 : Nat := 4983230072969 + 3 ^ 40 * 1905377 * 2
def baseEnd_1905377 : Nat := 434832990676398638855483

theorem tailTrace_1905377 : CollatzResearch.WordTrace tailWord_1905377 prefixEnd_1905377 434832990676398638855483 := by
  unfold tailWord_1905377
  simp only [CollatzResearch.WordTrace]
  refine ⟨69494808418152016329298385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46329872278768010886198923 69494808418152016329298385)
  ·
    refine ⟨52121106313614012246973789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69494808418152016329298385 52121106313614012246973789)
    ·
      refine ⟨19545414867605254592615171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52121106313614012246973789 19545414867605254592615171)
      ·
        refine ⟨29318122301407881888922757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19545414867605254592615171 29318122301407881888922757)
        ·
          refine ⟨5497147931513977854173017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29318122301407881888922757 5497147931513977854173017)
          ·
            refine ⟨4122860948635483390629763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5497147931513977854173017 4122860948635483390629763)
            ·
              refine ⟨6184291422953225085944645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4122860948635483390629763 6184291422953225085944645)
              ·
                refine ⟨1159554641803729703614621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6184291422953225085944645 1159554641803729703614621)
                ·
                  refine ⟨434832990676398638855483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1159554641803729703614621 434832990676398638855483)
                  ·
                    rfl

theorem cell21_1905377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 4, 3].length) (baseStart_1905377 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1905377 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1905377 prefixEnd_1905377 := by exact prefixLift 1905377
  have htrace : WordTrace (prefixWord ++ tailWord_1905377) baseStart_1905377 baseEnd_1905377 := by
    simpa [prefixWord, tailWord_1905377, baseEnd_1905377] using wordTrace_append hprefix tailTrace_1905377
  have hstable : (prefixWord ++ tailWord_1905377).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1905377).length < 2 ^ (prefixWord ++ tailWord_1905377).sum := by decide
  have hdescent : baseEnd_1905377 < baseStart_1905377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1905377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1905405 : List Nat := [1, 4, 1, 1, 1, 1, 7, 5]
def baseStart_1905405 : Nat := 118140960795 + 1905405 * 2 ^ 59
def prefixEnd_1905405 : Nat := 4983230072969 + 3 ^ 40 * 1905405 * 2
def baseEnd_1905405 : Nat := 144946460219292270796253

theorem tailTrace_1905405 : CollatzResearch.WordTrace tailWord_1905405 prefixEnd_1905405 144946460219292270796253 := by
  unfold tailWord_1905405
  simp only [CollatzResearch.WordTrace]
  refine ⟨69495829662050577111317669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46330553108033718074211779 69495829662050577111317669)
  ·
    refine ⟨13030468061634483208372063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69495829662050577111317669 13030468061634483208372063)
    ·
      refine ⟨19545702092451724812558095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13030468061634483208372063 19545702092451724812558095)
      ·
        refine ⟨29318553138677587218837143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19545702092451724812558095 29318553138677587218837143)
        ·
          refine ⟨43977829708016380828255715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29318553138677587218837143 43977829708016380828255715)
          ·
            refine ⟨65966744562024571242383573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43977829708016380828255715 65966744562024571242383573)
            ·
              refine ⟨1546095575672450888493365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 65966744562024571242383573 1546095575672450888493365)
              ·
                refine ⟨144946460219292270796253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1546095575672450888493365 144946460219292270796253)
                ·
                  rfl

theorem cell21_1905405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 7, 5].length) (baseStart_1905405 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1905405 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1905405 prefixEnd_1905405 := by exact prefixLift 1905405
  have htrace : WordTrace (prefixWord ++ tailWord_1905405) baseStart_1905405 baseEnd_1905405 := by
    simpa [prefixWord, tailWord_1905405, baseEnd_1905405] using wordTrace_append hprefix tailTrace_1905405
  have hstable : (prefixWord ++ tailWord_1905405).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1905405).length < 2 ^ (prefixWord ++ tailWord_1905405).sum := by decide
  have hdescent : baseEnd_1905405 < baseStart_1905405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1905405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1905436 : List Nat := [2, 2, 3, 1, 1, 4, 2, 1, 5]
def baseStart_1905436 : Nat := 118140960795 + 1905436 * 2 ^ 59
def prefixEnd_1905436 : Nat := 4983230072969 + 3 ^ 40 * 1905436 * 2
def baseEnd_1905436 : Nat := 434846455280227647372029

theorem tailTrace_1905436 : CollatzResearch.WordTrace tailWord_1905436 prefixEnd_1905436 434846455280227647372029 := by
  unfold tailWord_1905436
  simp only [CollatzResearch.WordTrace]
  refine ⟨34748480162469134702848081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46331306883292179603797441 34748480162469134702848081)
  ·
    refine ⟨26061360121851851027136061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34748480162469134702848081 26061360121851851027136061)
    ·
      refine ⟨9773010045694444135176023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26061360121851851027136061 9773010045694444135176023)
      ·
        refine ⟨14659515068541666202764035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9773010045694444135176023 14659515068541666202764035)
        ·
          refine ⟨21989272602812499304146053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14659515068541666202764035 21989272602812499304146053)
          ·
            refine ⟨4122988613027343619527385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21989272602812499304146053 4122988613027343619527385)
            ·
              refine ⟨3092241459770507714645539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4122988613027343619527385 3092241459770507714645539)
              ·
                refine ⟨4638362189655761571968309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3092241459770507714645539 4638362189655761571968309)
                ·
                  refine ⟨434846455280227647372029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4638362189655761571968309 434846455280227647372029)
                  ·
                    rfl

theorem cell21_1905436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 2, 1, 5].length) (baseStart_1905436 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1905436 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1905436 prefixEnd_1905436 := by exact prefixLift 1905436
  have htrace : WordTrace (prefixWord ++ tailWord_1905436) baseStart_1905436 baseEnd_1905436 := by
    simpa [prefixWord, tailWord_1905436, baseEnd_1905436] using wordTrace_append hprefix tailTrace_1905436
  have hstable : (prefixWord ++ tailWord_1905436).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1905436).length < 2 ^ (prefixWord ++ tailWord_1905436).sum := by decide
  have hdescent : baseEnd_1905436 < baseStart_1905436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1905436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1905464 : List Nat := [2, 1, 2, 1, 3, 2, 3, 7]
def baseStart_1905464 : Nat := 118140960795 + 1905464 * 2 ^ 59
def prefixEnd_1905464 : Nat := 4983230072969 + 3 ^ 40 * 1905464 * 2
def baseEnd_1905464 : Nat := 144950948420568606968435

theorem tailTrace_1905464 : CollatzResearch.WordTrace tailWord_1905464 prefixEnd_1905464 144950948420568606968435 := by
  unfold tailWord_1905464
  simp only [CollatzResearch.WordTrace]
  refine ⟨34748990784418415093857723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46331987712557886791810297 34748990784418415093857723)
  ·
    refine ⟨52123486176627622640786585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34748990784418415093857723 52123486176627622640786585)
    ·
      refine ⟨39092614632470716980589939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52123486176627622640786585 39092614632470716980589939)
      ·
        refine ⟨58638921948706075470884909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39092614632470716980589939 58638921948706075470884909)
        ·
          refine ⟨21989595730764778301581841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58638921948706075470884909 21989595730764778301581841)
          ·
            refine ⟨16492196798073583726186381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21989595730764778301581841 16492196798073583726186381)
            ·
              refine ⟨6184573799277593897319893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16492196798073583726186381 6184573799277593897319893)
              ·
                refine ⟨144950948420568606968435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6184573799277593897319893 144950948420568606968435)
                ·
                  rfl

theorem cell21_1905464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 7].length) (baseStart_1905464 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1905464 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1905464 prefixEnd_1905464 := by exact prefixLift 1905464
  have htrace : WordTrace (prefixWord ++ tailWord_1905464) baseStart_1905464 baseEnd_1905464 := by
    simpa [prefixWord, tailWord_1905464, baseEnd_1905464] using wordTrace_append hprefix tailTrace_1905464
  have hstable : (prefixWord ++ tailWord_1905464).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1905464).length < 2 ^ (prefixWord ++ tailWord_1905464).sum := by decide
  have hdescent : baseEnd_1905464 < baseStart_1905464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1905464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1905543 : List Nat := [1, 1, 4, 2, 3, 2, 2, 2, 4]
def baseStart_1905543 : Nat := 118140960795 + 1905543 * 2 ^ 59
def prefixEnd_1905543 : Nat := 4983230072969 + 3 ^ 40 * 1905543 * 2
def baseEnd_1905543 : Nat := 434870874138019239088477

theorem tailTrace_1905543 : CollatzResearch.WordTrace tailWord_1905543 prefixEnd_1905543 434870874138019239088477 := by
  unfold tailWord_1905543
  simp only [CollatzResearch.WordTrace]
  refine ⟨69500862935550626679841283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46333908623700417786560855 69500862935550626679841283)
  ·
    refine ⟨104251294403325940019761925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69500862935550626679841283 104251294403325940019761925)
    ·
      refine ⟨19547117700623613753705361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104251294403325940019761925 19547117700623613753705361)
      ·
        refine ⟨14660338275467710315279021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19547117700623613753705361 14660338275467710315279021)
        ·
          refine ⟨5497626853300391368229633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14660338275467710315279021 5497626853300391368229633)
          ·
            refine ⟨4123220139975293526172225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5497626853300391368229633 4123220139975293526172225)
            ·
              refine ⟨3092415104981470144629169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4123220139975293526172225 3092415104981470144629169)
              ·
                refine ⟨2319311328736102608471877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3092415104981470144629169 2319311328736102608471877)
                ·
                  refine ⟨434870874138019239088477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2319311328736102608471877 434870874138019239088477)
                  ·
                    rfl

theorem cell21_1905543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 2, 2, 4].length) (baseStart_1905543 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1905543 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1905543 prefixEnd_1905543 := by exact prefixLift 1905543
  have htrace : WordTrace (prefixWord ++ tailWord_1905543) baseStart_1905543 baseEnd_1905543 := by
    simpa [prefixWord, tailWord_1905543, baseEnd_1905543] using wordTrace_append hprefix tailTrace_1905543
  have hstable : (prefixWord ++ tailWord_1905543).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1905543).length < 2 ^ (prefixWord ++ tailWord_1905543).sum := by decide
  have hdescent : baseEnd_1905543 < baseStart_1905543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1905543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1905546 : List Nat := [3, 1, 2, 4, 1, 1, 4, 2, 3]
def baseStart_1905546 : Nat := 118140960795 + 1905546 * 2 ^ 59
def prefixEnd_1905546 : Nat := 4983230072969 + 3 ^ 40 * 1905546 * 2
def baseEnd_1905546 : Nat := 434871558778891900538471

theorem tailTrace_1905546 : CollatzResearch.WordTrace tailWord_1905546 prefixEnd_1905546 434871558778891900538471 := by
  unfold tailWord_1905546
  simp only [CollatzResearch.WordTrace]
  refine ⟨17375243088634939548050123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46333981569693172128133661 17375243088634939548050123)
  ·
    refine ⟨26062864632952409322075185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17375243088634939548050123 26062864632952409322075185)
    ·
      refine ⟨19547148474714306991556389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26062864632952409322075185 19547148474714306991556389)
      ·
        refine ⟨3665090339008932560916823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19547148474714306991556389 3665090339008932560916823)
        ·
          refine ⟨5497635508513398841375235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3665090339008932560916823 5497635508513398841375235)
          ·
            refine ⟨8246453262770098262062853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5497635508513398841375235 8246453262770098262062853)
            ·
              refine ⟨1546209986769393424136785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8246453262770098262062853 1546209986769393424136785)
              ·
                refine ⟨1159657490077045068102589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1546209986769393424136785 1159657490077045068102589)
                ·
                  refine ⟨434871558778891900538471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1159657490077045068102589 434871558778891900538471)
                  ·
                    rfl

theorem cell21_1905546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 4, 2, 3].length) (baseStart_1905546 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1905546 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1905546 prefixEnd_1905546 := by exact prefixLift 1905546
  have htrace : WordTrace (prefixWord ++ tailWord_1905546) baseStart_1905546 baseEnd_1905546 := by
    simpa [prefixWord, tailWord_1905546, baseEnd_1905546] using wordTrace_append hprefix tailTrace_1905546
  have hstable : (prefixWord ++ tailWord_1905546).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1905546).length < 2 ^ (prefixWord ++ tailWord_1905546).sum := by decide
  have hdescent : baseEnd_1905546 < baseStart_1905546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1905546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1905557 : List Nat := [1, 3, 2, 1, 1, 6, 1, 6]
def baseStart_1905557 : Nat := 118140960795 + 1905557 * 2 ^ 59
def prefixEnd_1905557 : Nat := 4983230072969 + 3 ^ 40 * 1905557 * 2
def baseEnd_1905557 : Nat := 144958023042919441951705

theorem tailTrace_1905557 : CollatzResearch.WordTrace tailWord_1905557 prefixEnd_1905557 144958023042919441951705 := by
  unfold tailWord_1905557
  simp only [CollatzResearch.WordTrace]
  refine ⟨69501373557499907070850925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46334249038333271380567283 69501373557499907070850925)
  ·
    refine ⟨26063015084062465151569097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69501373557499907070850925 26063015084062465151569097)
    ·
      refine ⟨19547261313046848863676823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26063015084062465151569097 19547261313046848863676823)
      ·
        refine ⟨29320891969570273295515235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19547261313046848863676823 29320891969570273295515235)
        ·
          refine ⟨43981337954355409943272853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29320891969570273295515235 43981337954355409943272853)
          ·
            refine ⟨2061625216610409841090915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 43981337954355409943272853 2061625216610409841090915)
            ·
              refine ⟨3092437824915614761636373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2061625216610409841090915 3092437824915614761636373)
              ·
                refine ⟨144958023042919441951705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3092437824915614761636373 144958023042919441951705)
                ·
                  rfl

theorem cell21_1905557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 1, 6].length) (baseStart_1905557 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1905557 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1905557 prefixEnd_1905557 := by exact prefixLift 1905557
  have htrace : WordTrace (prefixWord ++ tailWord_1905557) baseStart_1905557 baseEnd_1905557 := by
    simpa [prefixWord, tailWord_1905557, baseEnd_1905557] using wordTrace_append hprefix tailTrace_1905557
  have hstable : (prefixWord ++ tailWord_1905557).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1905557).length < 2 ^ (prefixWord ++ tailWord_1905557).sum := by decide
  have hdescent : baseEnd_1905557 < baseStart_1905557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1905557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1905650 : List Nat := [3, 2, 1, 5, 1, 2, 7]
def baseStart_1905650 : Nat := 118140960795 + 1905650 * 2 ^ 59
def prefixEnd_1905650 : Nat := 4983230072969 + 3 ^ 40 * 1905650 * 2
def baseEnd_1905650 : Nat := 48321699221756758978325

theorem tailTrace_1905650 : CollatzResearch.WordTrace tailWord_1905650 prefixEnd_1905650 48321699221756758978325 := by
  unfold tailWord_1905650
  simp only [CollatzResearch.WordTrace]
  refine ⟨17376191386540745988496601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46336510364108655969324269 17376191386540745988496601)
  ·
    refine ⟨13032143539905559491372451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17376191386540745988496601 13032143539905559491372451)
    ·
      refine ⟨19548215309858339237058677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13032143539905559491372451 19548215309858339237058677)
      ·
        refine ⟨1832645185299219303474251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19548215309858339237058677 1832645185299219303474251)
        ·
          refine ⟨2748967777948828955211377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1832645185299219303474251 2748967777948828955211377)
          ·
            refine ⟨2061725833461621716408533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2748967777948828955211377 2061725833461621716408533)
            ·
              refine ⟨48321699221756758978325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2061725833461621716408533 48321699221756758978325)
              ·
                rfl

theorem cell21_1905650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 7].length) (baseStart_1905650 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1905650 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1905650 prefixEnd_1905650 := by exact prefixLift 1905650
  have htrace : WordTrace (prefixWord ++ tailWord_1905650) baseStart_1905650 baseEnd_1905650 := by
    simpa [prefixWord, tailWord_1905650, baseEnd_1905650] using wordTrace_append hprefix tailTrace_1905650
  have hstable : (prefixWord ++ tailWord_1905650).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1905650).length < 2 ^ (prefixWord ++ tailWord_1905650).sum := by decide
  have hdescent : baseEnd_1905650 < baseStart_1905650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1905650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1905726 : List Nat := [4, 2, 1, 3, 1, 3, 1, 6]
def baseStart_1905726 : Nat := 118140960795 + 1905726 * 2 ^ 59
def prefixEnd_1905726 : Nat := 4983230072969 + 3 ^ 40 * 1905726 * 2
def baseEnd_1905726 : Nat := 144970879077083862512701

theorem tailTrace_1905726 : CollatzResearch.WordTrace tailWord_1905726 prefixEnd_1905726 144970879077083862512701 := by
  unfold tailWord_1905726
  simp only [CollatzResearch.WordTrace]
  refine ⟨8688442186735956116719129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46338358329258432622502021 8688442186735956116719129)
  ·
    refine ⟨6516331640051967087539347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8688442186735956116719129 6516331640051967087539347)
    ·
      refine ⟨9774497460077950631309021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6516331640051967087539347 9774497460077950631309021)
      ·
        refine ⟨3665436547529231486740883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9774497460077950631309021 3665436547529231486740883)
        ·
          refine ⟨5498154821293847230111325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3665436547529231486740883 5498154821293847230111325)
          ·
            refine ⟨2061808057985192711291747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5498154821293847230111325 2061808057985192711291747)
            ·
              refine ⟨3092712086977789066937621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2061808057985192711291747 3092712086977789066937621)
              ·
                refine ⟨144970879077083862512701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3092712086977789066937621 144970879077083862512701)
                ·
                  rfl

theorem cell21_1905726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 1, 6].length) (baseStart_1905726 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1905726 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1905726 prefixEnd_1905726 := by exact prefixLift 1905726
  have htrace : WordTrace (prefixWord ++ tailWord_1905726) baseStart_1905726 baseEnd_1905726 := by
    simpa [prefixWord, tailWord_1905726, baseEnd_1905726] using wordTrace_append hprefix tailTrace_1905726
  have hstable : (prefixWord ++ tailWord_1905726).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1905726).length < 2 ^ (prefixWord ++ tailWord_1905726).sum := by decide
  have hdescent : baseEnd_1905726 < baseStart_1905726 := by decide
  rcases family_descends (prefixWord ++ tailWord_1905726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1905878 : List Nat := [5, 2, 1, 2, 3, 8]
def baseStart_1905878 : Nat := 118140960795 + 1905878 * 2 ^ 59
def prefixEnd_1905878 : Nat := 4983230072969 + 3 ^ 40 * 1905878 * 2
def baseEnd_1905878 : Nat := 16109160211190114852017

theorem tailTrace_1905878 : CollatzResearch.WordTrace tailWord_1905878 prefixEnd_1905878 16109160211190114852017 := by
  unfold tailWord_1905878
  simp only [CollatzResearch.WordTrace]
  refine ⟨4344567586833561180830393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46342054259557985928857525 4344567586833561180830393)
  ·
    refine ⟨3258425690125170885622795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4344567586833561180830393 3258425690125170885622795)
    ·
      refine ⟨4887638535187756328434193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3258425690125170885622795 4887638535187756328434193)
      ·
        refine ⟨3665728901390817246325645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4887638535187756328434193 3665728901390817246325645)
        ·
          refine ⟨1374648338021556467372117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3665728901390817246325645 1374648338021556467372117)
          ·
            refine ⟨16109160211190114852017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1374648338021556467372117 16109160211190114852017)
            ·
              rfl

theorem cell21_1905878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 8].length) (baseStart_1905878 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1905878 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1905878 prefixEnd_1905878 := by exact prefixLift 1905878
  have htrace : WordTrace (prefixWord ++ tailWord_1905878) baseStart_1905878 baseEnd_1905878 := by
    simpa [prefixWord, tailWord_1905878, baseEnd_1905878] using wordTrace_append hprefix tailTrace_1905878
  have hstable : (prefixWord ++ tailWord_1905878).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1905878).length < 2 ^ (prefixWord ++ tailWord_1905878).sum := by decide
  have hdescent : baseEnd_1905878 < baseStart_1905878 := by decide
  rcases family_descends (prefixWord ++ tailWord_1905878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1905985 : List Nat := [1, 2, 5, 2, 1, 1, 3, 3, 3]
def baseStart_1905985 : Nat := 118140960795 + 1905985 * 2 ^ 59
def prefixEnd_1905985 : Nat := 4983230072969 + 3 ^ 40 * 1905985 * 2
def baseEnd_1905985 : Nat := 434971744559924692720907

theorem tailTrace_1905985 : CollatzResearch.WordTrace tailWord_1905985 prefixEnd_1905985 434971744559924692720907 := by
  unfold tailWord_1905985
  simp only [CollatzResearch.WordTrace]
  refine ⟨69516983999949336167431409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46344655999966224111620939 69516983999949336167431409)
  ·
    refine ⟨52137737999962002125573557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69516983999949336167431409 52137737999962002125573557)
    ·
      refine ⟨4887912937496437699272521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52137737999962002125573557 4887912937496437699272521)
      ·
        refine ⟨3665934703122328274454391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4887912937496437699272521 3665934703122328274454391)
        ·
          refine ⟨5498902054683492411681587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3665934703122328274454391 5498902054683492411681587)
          ·
            refine ⟨8248353082025238617522381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5498902054683492411681587 8248353082025238617522381)
            ·
              refine ⟨3093132405759464481570893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8248353082025238617522381 3093132405759464481570893)
              ·
                refine ⟨1159924652159799180589085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3093132405759464481570893 1159924652159799180589085)
                ·
                  refine ⟨434971744559924692720907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1159924652159799180589085 434971744559924692720907)
                  ·
                    rfl

theorem cell21_1905985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 3, 3, 3].length) (baseStart_1905985 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1905985 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1905985 prefixEnd_1905985 := by exact prefixLift 1905985
  have htrace : WordTrace (prefixWord ++ tailWord_1905985) baseStart_1905985 baseEnd_1905985 := by
    simpa [prefixWord, tailWord_1905985, baseEnd_1905985] using wordTrace_append hprefix tailTrace_1905985
  have hstable : (prefixWord ++ tailWord_1905985).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1905985).length < 2 ^ (prefixWord ++ tailWord_1905985).sum := by decide
  have hdescent : baseEnd_1905985 < baseStart_1905985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1905985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1905996 : List Nat := [2, 2, 1, 3, 2, 4, 7]
def baseStart_1905996 : Nat := 118140960795 + 1905996 * 2 ^ 59
def prefixEnd_1905996 : Nat := 4983230072969 + 3 ^ 40 * 1905996 * 2
def baseEnd_1905996 : Nat := 48330472767754568670839

theorem tailTrace_1905996 : CollatzResearch.WordTrace tailWord_1905996 prefixEnd_1905996 48330472767754568670839 := by
  unfold tailWord_1905996
  simp only [CollatzResearch.WordTrace]
  refine ⟨34758692601454742523040921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46344923468606323364054561 34758692601454742523040921)
  ·
    refine ⟨26069019451091056892280691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34758692601454742523040921 26069019451091056892280691)
    ·
      refine ⟨39103529176636585338421037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26069019451091056892280691 39103529176636585338421037)
      ·
        refine ⟨14663823441238719501907889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39103529176636585338421037 14663823441238719501907889)
        ·
          refine ⟨10997867580929039626430917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14663823441238719501907889 10997867580929039626430917)
          ·
            refine ⟨2062100171424194929955797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10997867580929039626430917 2062100171424194929955797)
            ·
              refine ⟨48330472767754568670839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2062100171424194929955797 48330472767754568670839)
              ·
                rfl

theorem cell21_1905996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 7].length) (baseStart_1905996 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1905996 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1905996 prefixEnd_1905996 := by exact prefixLift 1905996
  have htrace : WordTrace (prefixWord ++ tailWord_1905996) baseStart_1905996 baseEnd_1905996 := by
    simpa [prefixWord, tailWord_1905996, baseEnd_1905996] using wordTrace_append hprefix tailTrace_1905996
  have hstable : (prefixWord ++ tailWord_1905996).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1905996).length < 2 ^ (prefixWord ++ tailWord_1905996).sum := by decide
  have hdescent : baseEnd_1905996 < baseStart_1905996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1905996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1906055 : List Nat := [1, 1, 4, 2, 2, 11]
def baseStart_1906055 : Nat := 118140960795 + 1906055 * 2 ^ 59
def prefixEnd_1906055 : Nat := 4983230072969 + 3 ^ 40 * 1906055 * 2
def baseEnd_1906055 : Nat := 16110656278282226909411

theorem tailTrace_1906055 : CollatzResearch.WordTrace tailWord_1906055 prefixEnd_1906055 16110656278282226909411 := by
  unfold tailWord_1906055
  simp only [CollatzResearch.WordTrace]
  refine ⟨69519537109695738122479619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46346358073130492081653079 69519537109695738122479619)
  ·
    refine ⟨104279305664543607183719429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69519537109695738122479619 104279305664543607183719429)
    ·
      refine ⟨19552369812101926346947393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104279305664543607183719429 19552369812101926346947393)
      ·
        refine ⟨14664277359076444760210545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19552369812101926346947393 14664277359076444760210545)
        ·
          refine ⟨10998208019307333570157909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14664277359076444760210545 10998208019307333570157909)
          ·
            refine ⟨16110656278282226909411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 10998208019307333570157909 16110656278282226909411)
            ·
              rfl

theorem cell21_1906055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 11].length) (baseStart_1906055 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1906055 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1906055 prefixEnd_1906055 := by exact prefixLift 1906055
  have htrace : WordTrace (prefixWord ++ tailWord_1906055) baseStart_1906055 baseEnd_1906055 := by
    simpa [prefixWord, tailWord_1906055, baseEnd_1906055] using wordTrace_append hprefix tailTrace_1906055
  have hstable : (prefixWord ++ tailWord_1906055).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1906055).length < 2 ^ (prefixWord ++ tailWord_1906055).sum := by decide
  have hdescent : baseEnd_1906055 < baseStart_1906055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1906055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1906154 : List Nat := [3, 1, 3, 1, 5, 1, 1, 3, 3]
def baseStart_1906154 : Nat := 118140960795 + 1906154 * 2 ^ 59
def prefixEnd_1906154 : Nat := 4983230072969 + 3 ^ 40 * 1906154 * 2
def baseEnd_1906154 : Nat := 435010312662417954403895

theorem tailTrace_1906154 : CollatzResearch.WordTrace tailWord_1906154 prefixEnd_1906154 435010312662417954403895 := by
  unfold tailWord_1906154
  simp only [CollatzResearch.WordTrace]
  refine ⟨17380786984084269507583379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46348765290891385353555677 17380786984084269507583379)
  ·
    refine ⟨26071180476126404261375069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17380786984084269507583379 26071180476126404261375069)
    ·
      refine ⟨9776692678547401598015651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26071180476126404261375069 9776692678547401598015651)
      ·
        refine ⟨14665039017821102397023477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9776692678547401598015651 14665039017821102397023477)
        ·
          refine ⟨1374847407920728349720951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14665039017821102397023477 1374847407920728349720951)
          ·
            refine ⟨2062271111881092524581427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1374847407920728349720951 2062271111881092524581427)
            ·
              refine ⟨3093406667821638786872141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2062271111881092524581427 3093406667821638786872141)
              ·
                refine ⟨1160027500433114545077053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3093406667821638786872141 1160027500433114545077053)
                ·
                  refine ⟨435010312662417954403895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1160027500433114545077053 435010312662417954403895)
                  ·
                    rfl

theorem cell21_1906154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 1, 3, 3].length) (baseStart_1906154 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1906154 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1906154 prefixEnd_1906154 := by exact prefixLift 1906154
  have htrace : WordTrace (prefixWord ++ tailWord_1906154) baseStart_1906154 baseEnd_1906154 := by
    simpa [prefixWord, tailWord_1906154, baseEnd_1906154] using wordTrace_append hprefix tailTrace_1906154
  have hstable : (prefixWord ++ tailWord_1906154).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1906154).length < 2 ^ (prefixWord ++ tailWord_1906154).sum := by decide
  have hdescent : baseEnd_1906154 < baseStart_1906154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1906154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1906165 : List Nat := [1, 3, 5, 1, 1, 3, 7]
def baseStart_1906165 : Nat := 118140960795 + 1906165 * 2 ^ 59
def prefixEnd_1906165 : Nat := 4983230072969 + 3 ^ 40 * 1906165 * 2
def baseEnd_1906165 : Nat := 48334758112476042191171

theorem tailTrace_1906165 : CollatzResearch.WordTrace tailWord_1906165 prefixEnd_1906165 48334758112476042191171 := by
  unfold tailWord_1906165
  simp only [CollatzResearch.WordTrace]
  refine ⟨69523549139297226908983949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46349032759531484605989299 69523549139297226908983949)
  ·
    refine ⟨26071330927236460090868981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69523549139297226908983949 26071330927236460090868981)
    ·
      refine ⟨2444187274428418133518967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26071330927236460090868981 2444187274428418133518967)
      ·
        refine ⟨3666280911642627200278451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2444187274428418133518967 3666280911642627200278451)
        ·
          refine ⟨5499421367463940800417677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3666280911642627200278451 5499421367463940800417677)
          ·
            refine ⟨2062283012798977800156629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5499421367463940800417677 2062283012798977800156629)
            ·
              refine ⟨48334758112476042191171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2062283012798977800156629 48334758112476042191171)
              ·
                rfl

theorem cell21_1906165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 7].length) (baseStart_1906165 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1906165 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1906165 prefixEnd_1906165 := by exact prefixLift 1906165
  have htrace : WordTrace (prefixWord ++ tailWord_1906165) baseStart_1906165 baseEnd_1906165 := by
    simpa [prefixWord, tailWord_1906165, baseEnd_1906165] using wordTrace_append hprefix tailTrace_1906165
  have hstable : (prefixWord ++ tailWord_1906165).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1906165).length < 2 ^ (prefixWord ++ tailWord_1906165).sum := by decide
  have hdescent : baseEnd_1906165 < baseStart_1906165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1906165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1906193 : List Nat := [1, 2, 2, 1, 1, 2, 5, 3, 4]
def baseStart_1906193 : Nat := 118140960795 + 1906193 * 2 ^ 59
def prefixEnd_1906193 : Nat := 4983230072969 + 3 ^ 40 * 1906193 * 2
def baseEnd_1906193 : Nat := 435019212993762553253815

theorem tailTrace_1906193 : CollatzResearch.WordTrace tailWord_1906193 prefixEnd_1906193 435019212993762553253815 := by
  unfold tailWord_1906193
  simp only [CollatzResearch.WordTrace]
  refine ⟨69524570383195787691003233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46349713588797191794002155 69524570383195787691003233)
  ·
    refine ⟨52143427787396840768252425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69524570383195787691003233 52143427787396840768252425)
    ·
      refine ⟨39107570840547630576189319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52143427787396840768252425 39107570840547630576189319)
      ·
        refine ⟨58661356260821445864283979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39107570840547630576189319 58661356260821445864283979)
        ·
          refine ⟨87992034391232168796425969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58661356260821445864283979 87992034391232168796425969)
          ·
            refine ⟨65994025793424126597319477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87992034391232168796425969 65994025793424126597319477)
            ·
              refine ⟨6186939918133511868498701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65994025793424126597319477 6186939918133511868498701)
              ·
                refine ⟨2320102469300066950687013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6186939918133511868498701 2320102469300066950687013)
                ·
                  refine ⟨435019212993762553253815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2320102469300066950687013 435019212993762553253815)
                  ·
                    rfl

theorem cell21_1906193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 3, 4].length) (baseStart_1906193 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1906193 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1906193 prefixEnd_1906193 := by exact prefixLift 1906193
  have htrace : WordTrace (prefixWord ++ tailWord_1906193) baseStart_1906193 baseEnd_1906193 := by
    simpa [prefixWord, tailWord_1906193, baseEnd_1906193] using wordTrace_append hprefix tailTrace_1906193
  have hstable : (prefixWord ++ tailWord_1906193).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1906193).length < 2 ^ (prefixWord ++ tailWord_1906193).sum := by decide
  have hdescent : baseEnd_1906193 < baseStart_1906193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1906193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1906207 : List Nat := [1, 1, 2, 4, 1, 1, 4, 7]
def baseStart_1906207 : Nat := 118140960795 + 1906207 * 2 ^ 59
def prefixEnd_1906207 : Nat := 4983230072969 + 3 ^ 40 * 1906207 * 2
def baseEnd_1906207 : Nat := 145007469328167213340151

theorem tailTrace_1906207 : CollatzResearch.WordTrace tailWord_1906207 prefixEnd_1906207 145007469328167213340151 := by
  unfold tailWord_1906207
  simp only [CollatzResearch.WordTrace]
  refine ⟨69525081005145068082012875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46350054003430045388008583 69525081005145068082012875)
  ·
    refine ⟨104287621507717602123019313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69525081005145068082012875 104287621507717602123019313)
    ·
      refine ⟨78215716130788201592264485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104287621507717602123019313 78215716130788201592264485)
      ·
        refine ⟨14665446774522787798549591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78215716130788201592264485 14665446774522787798549591)
        ·
          refine ⟨21998170161784181697824387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14665446774522787798549591 21998170161784181697824387)
          ·
            refine ⟨32997255242676272546736581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21998170161784181697824387 32997255242676272546736581)
            ·
              refine ⟨6186985358001801102513109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32997255242676272546736581 6186985358001801102513109)
              ·
                refine ⟨145007469328167213340151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6186985358001801102513109 145007469328167213340151)
                ·
                  rfl

theorem cell21_1906207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 7].length) (baseStart_1906207 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1906207 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1906207 prefixEnd_1906207 := by exact prefixLift 1906207
  have htrace : WordTrace (prefixWord ++ tailWord_1906207) baseStart_1906207 baseEnd_1906207 := by
    simpa [prefixWord, tailWord_1906207, baseEnd_1906207] using wordTrace_append hprefix tailTrace_1906207
  have hstable : (prefixWord ++ tailWord_1906207).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1906207).length < 2 ^ (prefixWord ++ tailWord_1906207).sum := by decide
  have hdescent : baseEnd_1906207 < baseStart_1906207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1906207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1906286 : List Nat := [4, 1, 2, 2, 3, 1, 1, 1, 6]
def baseStart_1906286 : Nat := 118140960795 + 1906286 * 2 ^ 59
def prefixEnd_1906286 : Nat := 4983230072969 + 3 ^ 40 * 1906286 * 2
def baseEnd_1906286 : Nat := 435040436860815058203625

theorem tailTrace_1906286 : CollatzResearch.WordTrace tailWord_1906286 prefixEnd_1906286 435040436860815058203625 := by
  unfold tailWord_1906286
  simp only [CollatzResearch.WordTrace]
  refine ⟨8690995296482358071767339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46351974914572576382759141 8690995296482358071767339)
  ·
    refine ⟨13036492944723537107651009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8690995296482358071767339 13036492944723537107651009)
    ·
      refine ⟨9777369708542652830738257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13036492944723537107651009 9777369708542652830738257)
      ·
        refine ⟨7333027281406989623053693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9777369708542652830738257 7333027281406989623053693)
        ·
          refine ⟨2749885230527621108645135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7333027281406989623053693 2749885230527621108645135)
          ·
            refine ⟨4124827845791431662967703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2749885230527621108645135 4124827845791431662967703)
            ·
              refine ⟨6187241768687147494451555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4124827845791431662967703 6187241768687147494451555)
              ·
                refine ⟨9280862653030721241677333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6187241768687147494451555 9280862653030721241677333)
                ·
                  refine ⟨435040436860815058203625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9280862653030721241677333 435040436860815058203625)
                  ·
                    rfl

theorem cell21_1906286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 1, 6].length) (baseStart_1906286 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1906286 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1906286 prefixEnd_1906286 := by exact prefixLift 1906286
  have htrace : WordTrace (prefixWord ++ tailWord_1906286) baseStart_1906286 baseEnd_1906286 := by
    simpa [prefixWord, tailWord_1906286, baseEnd_1906286] using wordTrace_append hprefix tailTrace_1906286
  have hstable : (prefixWord ++ tailWord_1906286).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1906286).length < 2 ^ (prefixWord ++ tailWord_1906286).sum := by decide
  have hdescent : baseEnd_1906286 < baseStart_1906286 := by decide
  rcases family_descends (prefixWord ++ tailWord_1906286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1906359 : List Nat := [1, 1, 3, 1, 5, 1, 1, 8]
def baseStart_1906359 : Nat := 118140960795 + 1906359 * 2 ^ 59
def prefixEnd_1906359 : Nat := 4983230072969 + 3 ^ 40 * 1906359 * 2
def baseEnd_1906359 : Nat := 145019032151794384495603

theorem tailTrace_1906359 : CollatzResearch.WordTrace tailWord_1906359 prefixEnd_1906359 145019032151794384495603 := by
  unfold tailWord_1906359
  simp only [CollatzResearch.WordTrace]
  refine ⟨69530624900594398041546131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46353749933729598694364087 69530624900594398041546131)
  ·
    refine ⟨104295937350891597062319197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69530624900594398041546131 104295937350891597062319197)
    ·
      refine ⟨39110976506584348898369699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104295937350891597062319197 39110976506584348898369699)
      ·
        refine ⟨58666464759876523347554549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39110976506584348898369699 58666464759876523347554549)
        ·
          refine ⟨5499981071238424063833239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58666464759876523347554549 5499981071238424063833239)
          ·
            refine ⟨8249971606857636095749859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5499981071238424063833239 8249971606857636095749859)
            ·
              refine ⟨12374957410286454143624789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8249971606857636095749859 12374957410286454143624789)
              ·
                refine ⟨145019032151794384495603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12374957410286454143624789 145019032151794384495603)
                ·
                  rfl

theorem cell21_1906359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 8].length) (baseStart_1906359 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1906359 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1906359 prefixEnd_1906359 := by exact prefixLift 1906359
  have htrace : WordTrace (prefixWord ++ tailWord_1906359) baseStart_1906359 baseEnd_1906359 := by
    simpa [prefixWord, tailWord_1906359, baseEnd_1906359] using wordTrace_append hprefix tailTrace_1906359
  have hstable : (prefixWord ++ tailWord_1906359).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1906359).length < 2 ^ (prefixWord ++ tailWord_1906359).sum := by decide
  have hdescent : baseEnd_1906359 < baseStart_1906359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1906359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1906362 : List Nat := [3, 1, 1, 1, 2, 4, 4, 1, 4]
def baseStart_1906362 : Nat := 118140960795 + 1906362 * 2 ^ 59
def prefixEnd_1906362 : Nat := 4983230072969 + 3 ^ 40 * 1906362 * 2
def baseEnd_1906362 : Nat := 435057781096255814936803

theorem tailTrace_1906362 : CollatzResearch.WordTrace tailWord_1906362 prefixEnd_1906362 435057781096255814936803 := by
  unfold tailWord_1906362
  simp only [CollatzResearch.WordTrace]
  refine ⟨17382683579895882388476335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46353822879722353035936893 17382683579895882388476335)
  ·
    refine ⟨26074025369843823582714503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17382683579895882388476335 26074025369843823582714503)
    ·
      refine ⟨39111038054765735374071755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26074025369843823582714503 39111038054765735374071755)
      ·
        refine ⟨58666557082148603061107633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39111038054765735374071755 58666557082148603061107633)
        ·
          refine ⟨43999917811611452295830725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58666557082148603061107633 43999917811611452295830725)
          ·
            refine ⟨8249984589677147305468261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43999917811611452295830725 8249984589677147305468261)
            ·
              refine ⟨1546872110564465119775299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8249984589677147305468261 1546872110564465119775299)
              ·
                refine ⟨2320308165846697679662949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1546872110564465119775299 2320308165846697679662949)
                ·
                  refine ⟨435057781096255814936803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2320308165846697679662949 435057781096255814936803)
                  ·
                    rfl

theorem cell21_1906362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 4, 1, 4].length) (baseStart_1906362 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1906362 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1906362 prefixEnd_1906362 := by exact prefixLift 1906362
  have htrace : WordTrace (prefixWord ++ tailWord_1906362) baseStart_1906362 baseEnd_1906362 := by
    simpa [prefixWord, tailWord_1906362, baseEnd_1906362] using wordTrace_append hprefix tailTrace_1906362
  have hstable : (prefixWord ++ tailWord_1906362).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1906362).length < 2 ^ (prefixWord ++ tailWord_1906362).sum := by decide
  have hdescent : baseEnd_1906362 < baseStart_1906362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1906362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1906449 : List Nat := [1, 2, 2, 1, 1, 3, 1, 1, 9]
def baseStart_1906449 : Nat := 118140960795 + 1906449 * 2 ^ 59
def prefixEnd_1906449 : Nat := 4983230072969 + 3 ^ 40 * 1906449 * 2
def baseEnd_1906449 : Nat := 435077635681562996986625

theorem tailTrace_1906449 : CollatzResearch.WordTrace tailWord_1906449 prefixEnd_1906449 435077635681562996986625 := by
  unfold tailWord_1906449
  simp only [CollatzResearch.WordTrace]
  refine ⟨69533907470268343412322401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46355938313512228941548267 69533907470268343412322401)
  ·
    refine ⟨52150430602701257559241801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69533907470268343412322401 52150430602701257559241801)
    ·
      refine ⟨39112822952025943169431351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52150430602701257559241801 39112822952025943169431351)
      ·
        refine ⟨58669234428038914754147027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39112822952025943169431351 58669234428038914754147027)
        ·
          refine ⟨88003851642058372131220541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58669234428038914754147027 88003851642058372131220541)
          ·
            refine ⟨33001444365771889549207703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88003851642058372131220541 33001444365771889549207703)
            ·
              refine ⟨49502166548657834323811555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33001444365771889549207703 49502166548657834323811555)
              ·
                refine ⟨74253249822986751485717333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49502166548657834323811555 74253249822986751485717333)
                ·
                  refine ⟨435077635681562996986625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 74253249822986751485717333 435077635681562996986625)
                  ·
                    rfl

theorem cell21_1906449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 9].length) (baseStart_1906449 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1906449 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1906449 prefixEnd_1906449 := by exact prefixLift 1906449
  have htrace : WordTrace (prefixWord ++ tailWord_1906449) baseStart_1906449 baseEnd_1906449 := by
    simpa [prefixWord, tailWord_1906449, baseEnd_1906449] using wordTrace_append hprefix tailTrace_1906449
  have hstable : (prefixWord ++ tailWord_1906449).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1906449).length < 2 ^ (prefixWord ++ tailWord_1906449).sum := by decide
  have hdescent : baseEnd_1906449 < baseStart_1906449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1906449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1906486 : List Nat := [5, 1, 2, 2, 1, 3, 2, 5]
def baseStart_1906486 : Nat := 118140960795 + 1906486 * 2 ^ 59
def prefixEnd_1906486 : Nat := 4983230072969 + 3 ^ 40 * 1906486 * 2
def baseEnd_1906486 : Nat := 145028693195219718289961

theorem tailTrace_1906486 : CollatzResearch.WordTrace tailWord_1906486 prefixEnd_1906486 145028693195219718289961 := by
  unfold tailWord_1906486
  simp only [CollatzResearch.WordTrace]
  refine ⟨4345953560695893670713707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46356837980756199154279541 4345953560695893670713707)
  ·
    refine ⟨6518930341043840506070561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4345953560695893670713707 6518930341043840506070561)
    ·
      refine ⟨4889197755782880379552921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6518930341043840506070561 4889197755782880379552921)
      ·
        refine ⟨3666898316837160284664691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4889197755782880379552921 3666898316837160284664691)
        ·
          refine ⟨5500347475255740426997037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3666898316837160284664691 5500347475255740426997037)
          ·
            refine ⟨2062630303220902660123889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5500347475255740426997037 2062630303220902660123889)
            ·
              refine ⟨1546972727415676995092917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2062630303220902660123889 1546972727415676995092917)
              ·
                refine ⟨145028693195219718289961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1546972727415676995092917 145028693195219718289961)
                ·
                  rfl

theorem cell21_1906486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 2, 5].length) (baseStart_1906486 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1906486 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1906486 prefixEnd_1906486 := by exact prefixLift 1906486
  have htrace : WordTrace (prefixWord ++ tailWord_1906486) baseStart_1906486 baseEnd_1906486 := by
    simpa [prefixWord, tailWord_1906486, baseEnd_1906486] using wordTrace_append hprefix tailTrace_1906486
  have hstable : (prefixWord ++ tailWord_1906486).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1906486).length < 2 ^ (prefixWord ++ tailWord_1906486).sum := by decide
  have hdescent : baseEnd_1906486 < baseStart_1906486 := by decide
  rcases family_descends (prefixWord ++ tailWord_1906486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1906531 : List Nat := [1, 1, 1, 5, 4, 2, 2, 1, 4]
def baseStart_1906531 : Nat := 118140960795 + 1906531 * 2 ^ 59
def prefixEnd_1906531 : Nat := 4983230072969 + 3 ^ 40 * 1906531 * 2
def baseEnd_1906531 : Nat := 435096349198749076619791

theorem tailTrace_1906531 : CollatzResearch.WordTrace tailWord_1906531 prefixEnd_1906531 435096349198749076619791 := by
  unfold tailWord_1906531
  simp only [CollatzResearch.WordTrace]
  refine ⟨69536898255971271416807447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46357932170647514277871631 69536898255971271416807447)
  ·
    refine ⟨104305347383956907125211171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69536898255971271416807447 104305347383956907125211171)
    ·
      refine ⟨156458021075935360687816757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104305347383956907125211171 156458021075935360687816757)
      ·
        refine ⟨14667939475868940064482821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 156458021075935360687816757 14667939475868940064482821)
        ·
          refine ⟨2750238651725426262090529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14667939475868940064482821 2750238651725426262090529)
          ·
            refine ⟨2062678988794069696567897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2750238651725426262090529 2062678988794069696567897)
            ·
              refine ⟨1547009241595552272425923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2062678988794069696567897 1547009241595552272425923)
              ·
                refine ⟨2320513862393328408638885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1547009241595552272425923 2320513862393328408638885)
                ·
                  refine ⟨435096349198749076619791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2320513862393328408638885 435096349198749076619791)
                  ·
                    rfl

theorem cell21_1906531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 2, 1, 4].length) (baseStart_1906531 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1906531 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1906531 prefixEnd_1906531 := by exact prefixLift 1906531
  have htrace : WordTrace (prefixWord ++ tailWord_1906531) baseStart_1906531 baseEnd_1906531 := by
    simpa [prefixWord, tailWord_1906531, baseEnd_1906531] using wordTrace_append hprefix tailTrace_1906531
  have hstable : (prefixWord ++ tailWord_1906531).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1906531).length < 2 ^ (prefixWord ++ tailWord_1906531).sum := by decide
  have hdescent : baseEnd_1906531 < baseStart_1906531 := by decide
  rcases family_descends (prefixWord ++ tailWord_1906531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1906742 : List Nat := [5, 1, 2, 1, 1, 1, 4, 2, 4]
def baseStart_1906742 : Nat := 118140960795 + 1906742 * 2 ^ 59
def prefixEnd_1906742 : Nat := 4983230072969 + 3 ^ 40 * 1906742 * 2
def baseEnd_1906742 : Nat := 435144502273459598602693

theorem tailTrace_1906742 : CollatzResearch.WordTrace tailWord_1906742 prefixEnd_1906742 435144502273459598602693 := by
  unfold tailWord_1906742
  simp only [CollatzResearch.WordTrace]
  refine ⟨4346537128637928403296155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46363062705471236301825653 4346537128637928403296155)
  ·
    refine ⟨6519805692956892604944233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4346537128637928403296155 6519805692956892604944233)
    ·
      refine ⟨4889854269717669453708175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6519805692956892604944233 4889854269717669453708175)
      ·
        refine ⟨7334781404576504180562263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4889854269717669453708175 7334781404576504180562263)
        ·
          refine ⟨11002172106864756270843395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7334781404576504180562263 11002172106864756270843395)
          ·
            refine ⟨16503258160297134406265093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11002172106864756270843395 16503258160297134406265093)
            ·
              refine ⟨3094360905055712701174705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16503258160297134406265093 3094360905055712701174705)
              ·
                refine ⟨2320770678791784525881029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3094360905055712701174705 2320770678791784525881029)
                ·
                  refine ⟨435144502273459598602693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2320770678791784525881029 435144502273459598602693)
                  ·
                    rfl

theorem cell21_1906742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 4, 2, 4].length) (baseStart_1906742 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1906742 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1906742 prefixEnd_1906742 := by exact prefixLift 1906742
  have htrace : WordTrace (prefixWord ++ tailWord_1906742) baseStart_1906742 baseEnd_1906742 := by
    simpa [prefixWord, tailWord_1906742, baseEnd_1906742] using wordTrace_append hprefix tailTrace_1906742
  have hstable : (prefixWord ++ tailWord_1906742).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1906742).length < 2 ^ (prefixWord ++ tailWord_1906742).sum := by decide
  have hdescent : baseEnd_1906742 < baseStart_1906742 := by decide
  rcases family_descends (prefixWord ++ tailWord_1906742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1906745 : List Nat := [1, 2, 1, 5, 3, 2, 2, 2, 3]
def baseStart_1906745 : Nat := 118140960795 + 1906745 * 2 ^ 59
def prefixEnd_1906745 : Nat := 4983230072969 + 3 ^ 40 * 1906745 * 2
def baseEnd_1906745 : Nat := 435145186914332260052687

theorem tailTrace_1906745 : CollatzResearch.WordTrace tailWord_1906745 prefixEnd_1906745 435145186914332260052687 := by
  unfold tailWord_1906745
  simp only [CollatzResearch.WordTrace]
  refine ⟨69544703477195985965097689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46363135651463990643398459 69544703477195985965097689)
  ·
    refine ⟨52158527607896989473823267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69544703477195985965097689 52158527607896989473823267)
    ·
      refine ⟨78237791411845484210734901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52158527607896989473823267 78237791411845484210734901)
      ·
        refine ⟨7334792944860514144756397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 78237791411845484210734901 7334792944860514144756397)
        ·
          refine ⟨2750547354322692804283649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7334792944860514144756397 2750547354322692804283649)
          ·
            refine ⟨2062910515742019603212737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2750547354322692804283649 2062910515742019603212737)
            ·
              refine ⟨1547182886806514702409553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2062910515742019603212737 1547182886806514702409553)
              ·
                refine ⟨1160387165104886026807165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1547182886806514702409553 1160387165104886026807165)
                ·
                  refine ⟨435145186914332260052687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1160387165104886026807165 435145186914332260052687)
                  ·
                    rfl

theorem cell21_1906745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 2, 2, 3].length) (baseStart_1906745 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1906745 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1906745 prefixEnd_1906745 := by exact prefixLift 1906745
  have htrace : WordTrace (prefixWord ++ tailWord_1906745) baseStart_1906745 baseEnd_1906745 := by
    simpa [prefixWord, tailWord_1906745, baseEnd_1906745] using wordTrace_append hprefix tailTrace_1906745
  have hstable : (prefixWord ++ tailWord_1906745).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1906745).length < 2 ^ (prefixWord ++ tailWord_1906745).sum := by decide
  have hdescent : baseEnd_1906745 < baseStart_1906745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1906745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1906843 : List Nat := [1, 1, 1, 1, 1, 1, 2, 5, 8]
def baseStart_1906843 : Nat := 118140960795 + 1906843 * 2 ^ 59
def prefixEnd_1906843 : Nat := 4983230072969 + 3 ^ 40 * 1906843 * 2
def baseEnd_1906843 : Nat := 435167551849505867419153

theorem tailTrace_1906843 : CollatzResearch.WordTrace tailWord_1906843 prefixEnd_1906843 435167551849505867419153 := by
  unfold tailWord_1906843
  simp only [CollatzResearch.WordTrace]
  refine ⟨69548277830840948702165183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46365518553893965801443455 69548277830840948702165183)
  ·
    refine ⟨104322416746261423053247775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69548277830840948702165183 104322416746261423053247775)
    ·
      refine ⟨156483625119392134579871663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104322416746261423053247775 156483625119392134579871663)
      ·
        refine ⟨234725437679088201869807495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156483625119392134579871663 234725437679088201869807495)
        ·
          refine ⟨352088156518632302804711243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234725437679088201869807495 352088156518632302804711243)
          ·
            refine ⟨528132234777948454207066865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 352088156518632302804711243 528132234777948454207066865)
            ·
              refine ⟨396099176083461340655300149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 528132234777948454207066865 396099176083461340655300149)
              ·
                refine ⟨37134297757824500686434389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 396099176083461340655300149 37134297757824500686434389)
                ·
                  refine ⟨435167551849505867419153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37134297757824500686434389 435167551849505867419153)
                  ·
                    rfl

theorem cell21_1906843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 8].length) (baseStart_1906843 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1906843 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1906843 prefixEnd_1906843 := by exact prefixLift 1906843
  have htrace : WordTrace (prefixWord ++ tailWord_1906843) baseStart_1906843 baseEnd_1906843 := by
    simpa [prefixWord, tailWord_1906843, baseEnd_1906843] using wordTrace_append hprefix tailTrace_1906843
  have hstable : (prefixWord ++ tailWord_1906843).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1906843).length < 2 ^ (prefixWord ++ tailWord_1906843).sum := by decide
  have hdescent : baseEnd_1906843 < baseStart_1906843 := by decide
  rcases family_descends (prefixWord ++ tailWord_1906843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1906874 : List Nat := [3, 1, 1, 1, 2, 2, 3, 8]
def baseStart_1906874 : Nat := 118140960795 + 1906874 * 2 ^ 59
def prefixEnd_1906874 : Nat := 4983230072969 + 3 ^ 40 * 1906874 * 2
def baseEnd_1906874 : Nat := 145058208823952234134141

theorem tailTrace_1906874 : CollatzResearch.WordTrace tailWord_1906874 prefixEnd_1906874 145058208823952234134141 := by
  unfold tailWord_1906874
  simp only [CollatzResearch.WordTrace]
  refine ⟨17387352123432160249135919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46366272329152427331029117 17387352123432160249135919)
  ·
    refine ⟨26081028185148240373703879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17387352123432160249135919 26081028185148240373703879)
    ·
      refine ⟨39121542277722360560555819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26081028185148240373703879 39121542277722360560555819)
      ·
        refine ⟨58682313416583540840833729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39121542277722360560555819 58682313416583540840833729)
        ·
          refine ⟨44011735062437655630625297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58682313416583540840833729 44011735062437655630625297)
          ·
            refine ⟨33008801296828241722968973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44011735062437655630625297 33008801296828241722968973)
            ·
              refine ⟨12378300486310590646113365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33008801296828241722968973 12378300486310590646113365)
              ·
                refine ⟨145058208823952234134141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12378300486310590646113365 145058208823952234134141)
                ·
                  rfl

theorem cell21_1906874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 8].length) (baseStart_1906874 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1906874 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1906874 prefixEnd_1906874 := by exact prefixLift 1906874
  have htrace : WordTrace (prefixWord ++ tailWord_1906874) baseStart_1906874 baseEnd_1906874 := by
    simpa [prefixWord, tailWord_1906874, baseEnd_1906874] using wordTrace_append hprefix tailTrace_1906874
  have hstable : (prefixWord ++ tailWord_1906874).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1906874).length < 2 ^ (prefixWord ++ tailWord_1906874).sum := by decide
  have hdescent : baseEnd_1906874 < baseStart_1906874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1906874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1906908 : List Nat := [2, 2, 5, 2, 1, 9]
def baseStart_1906908 : Nat := 118140960795 + 1906908 * 2 ^ 59
def prefixEnd_1906908 : Nat := 4983230072969 + 3 ^ 40 * 1906908 * 2
def baseEnd_1906908 : Nat := 16117866138336303660581

theorem tailTrace_1906908 : CollatzResearch.WordTrace tailWord_1906908 prefixEnd_1906908 16117866138336303660581 := by
  unfold tailWord_1906908
  simp only [CollatzResearch.WordTrace]
  refine ⟨34775324287802732401640689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46367099050403643202187585 34775324287802732401640689)
  ·
    refine ⟨26081493215852049301230517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34775324287802732401640689 26081493215852049301230517)
    ·
      refine ⟨2445139988986129621990361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26081493215852049301230517 2445139988986129621990361)
      ·
        refine ⟨1833854991739597216492771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2445139988986129621990361 1833854991739597216492771)
        ·
          refine ⟨2750782487609395824739157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1833854991739597216492771 2750782487609395824739157)
          ·
            refine ⟨16117866138336303660581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2750782487609395824739157 16117866138336303660581)
            ·
              rfl

theorem cell21_1906908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 9].length) (baseStart_1906908 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1906908 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1906908 prefixEnd_1906908 := by exact prefixLift 1906908
  have htrace : WordTrace (prefixWord ++ tailWord_1906908) baseStart_1906908 baseEnd_1906908 := by
    simpa [prefixWord, tailWord_1906908, baseEnd_1906908] using wordTrace_append hprefix tailTrace_1906908
  have hstable : (prefixWord ++ tailWord_1906908).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1906908).length < 2 ^ (prefixWord ++ tailWord_1906908).sum := by decide
  have hdescent : baseEnd_1906908 < baseStart_1906908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1906908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1906914 : List Nat := [3, 3, 4, 1, 1, 1, 1, 4, 3]
def baseStart_1906914 : Nat := 118140960795 + 1906914 * 2 ^ 59
def prefixEnd_1906914 : Nat := 4983230072969 + 3 ^ 40 * 1906914 * 2
def baseEnd_1906914 : Nat := 435183755016825521735675

theorem tailTrace_1906914 : CollatzResearch.WordTrace tailWord_1906914 prefixEnd_1906914 435183755016825521735675 := by
  unfold tailWord_1906914
  simp only [CollatzResearch.WordTrace]
  refine ⟨17387716853395931956999949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46367244942389151885333197 17387716853395931956999949)
  ·
    refine ⟨6520393820023474483874981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17387716853395931956999949 6520393820023474483874981)
    ·
      refine ⟨1222573841254401465726559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6520393820023474483874981 1222573841254401465726559)
      ·
        refine ⟨1833860761881602198589839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1222573841254401465726559 1833860761881602198589839)
        ·
          refine ⟨2750791142822403297884759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1833860761881602198589839 2750791142822403297884759)
          ·
            refine ⟨4126186714233604946827139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2750791142822403297884759 4126186714233604946827139)
            ·
              refine ⟨6189280071350407420240709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4126186714233604946827139 6189280071350407420240709)
              ·
                refine ⟨1160490013378201391295133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6189280071350407420240709 1160490013378201391295133)
                ·
                  refine ⟨435183755016825521735675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1160490013378201391295133 435183755016825521735675)
                  ·
                    rfl

theorem cell21_1906914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 4, 3].length) (baseStart_1906914 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1906914 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1906914 prefixEnd_1906914 := by exact prefixLift 1906914
  have htrace : WordTrace (prefixWord ++ tailWord_1906914) baseStart_1906914 baseEnd_1906914 := by
    simpa [prefixWord, tailWord_1906914, baseEnd_1906914] using wordTrace_append hprefix tailTrace_1906914
  have hstable : (prefixWord ++ tailWord_1906914).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1906914).length < 2 ^ (prefixWord ++ tailWord_1906914).sum := by decide
  have hdescent : baseEnd_1906914 < baseStart_1906914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1906914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1906925 : List Nat := [1, 5, 1, 2, 4, 1, 1, 6]
def baseStart_1906925 : Nat := 118140960795 + 1906925 * 2 ^ 59
def prefixEnd_1906925 : Nat := 4983230072969 + 3 ^ 40 * 1906925 * 2
def baseEnd_1906925 : Nat := 145062088455563982350773

theorem tailTrace_1906925 : CollatzResearch.WordTrace tailWord_1906925 prefixEnd_1906925 145062088455563982350773 := by
  unfold tailWord_1906925
  simp only [CollatzResearch.WordTrace]
  refine ⟨69551268616543876706650229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46367512411029251137766819 69551268616543876706650229)
  ·
    refine ⟨6520431432800988441248459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 69551268616543876706650229 6520431432800988441248459)
    ·
      refine ⟨9780647149201482661872689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6520431432800988441248459 9780647149201482661872689)
      ·
        refine ⟨7335485361901111996404517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9780647149201482661872689 7335485361901111996404517)
        ·
          refine ⟨1375403505356458499325847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7335485361901111996404517 1375403505356458499325847)
          ·
            refine ⟨2063105258034687748988771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1375403505356458499325847 2063105258034687748988771)
            ·
              refine ⟨3094657887052031623483157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2063105258034687748988771 3094657887052031623483157)
              ·
                refine ⟨145062088455563982350773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3094657887052031623483157 145062088455563982350773)
                ·
                  rfl

theorem cell21_1906925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 1, 6].length) (baseStart_1906925 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1906925 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1906925 prefixEnd_1906925 := by exact prefixLift 1906925
  have htrace : WordTrace (prefixWord ++ tailWord_1906925) baseStart_1906925 baseEnd_1906925 := by
    simpa [prefixWord, tailWord_1906925, baseEnd_1906925] using wordTrace_append hprefix tailTrace_1906925
  have hstable : (prefixWord ++ tailWord_1906925).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1906925).length < 2 ^ (prefixWord ++ tailWord_1906925).sum := by decide
  have hdescent : baseEnd_1906925 < baseStart_1906925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1906925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1906970 : List Nat := [3, 1, 1, 3, 4, 2, 1, 2, 4]
def baseStart_1906970 : Nat := 118140960795 + 1906970 * 2 ^ 59
def prefixEnd_1906970 : Nat := 4983230072969 + 3 ^ 40 * 1906970 * 2
def baseEnd_1906970 : Nat := 435196534979781868802227

theorem tailTrace_1906970 : CollatzResearch.WordTrace tailWord_1906970 prefixEnd_1906970 435196534979781868802227 := by
  unfold tailWord_1906970
  simp only [CollatzResearch.WordTrace]
  refine ⟨17388227475345212348009591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46368606600920566261358909 17388227475345212348009591)
  ·
    refine ⟨26082341213017818522014387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17388227475345212348009591 26082341213017818522014387)
    ·
      refine ⟨39123511819526727783021581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26082341213017818522014387 39123511819526727783021581)
      ·
        refine ⟨14671316932322522918633093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39123511819526727783021581 14671316932322522918633093)
        ·
          refine ⟨2750871924810473047243705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14671316932322522918633093 2750871924810473047243705)
          ·
            refine ⟨2063153943607854785432779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2750871924810473047243705 2063153943607854785432779)
            ·
              refine ⟨3094730915411782178149169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2063153943607854785432779 3094730915411782178149169)
              ·
                refine ⟨2321048186558836633611877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3094730915411782178149169 2321048186558836633611877)
                ·
                  refine ⟨435196534979781868802227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2321048186558836633611877 435196534979781868802227)
                  ·
                    rfl

theorem cell21_1906970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 1, 2, 4].length) (baseStart_1906970 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1906970 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1906970 prefixEnd_1906970 := by exact prefixLift 1906970
  have htrace : WordTrace (prefixWord ++ tailWord_1906970) baseStart_1906970 baseEnd_1906970 := by
    simpa [prefixWord, tailWord_1906970, baseEnd_1906970] using wordTrace_append hprefix tailTrace_1906970
  have hstable : (prefixWord ++ tailWord_1906970).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1906970).length < 2 ^ (prefixWord ++ tailWord_1906970).sum := by decide
  have hdescent : baseEnd_1906970 < baseStart_1906970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1906970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1907026 : List Nat := [3, 2, 2, 1, 1, 1, 11]
def baseStart_1907026 : Nat := 118140960795 + 1907026 * 2 ^ 59
def prefixEnd_1907026 : Nat := 4983230072969 + 3 ^ 40 * 1907026 * 2
def baseEnd_1907026 : Nat := 48356590549193135096531

theorem tailTrace_1907026 : CollatzResearch.WordTrace tailWord_1907026 prefixEnd_1907026 48356590549193135096531 := by
  unfold tailWord_1907026
  simp only [CollatzResearch.WordTrace]
  refine ⟨17388738097294492739019233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46369968259451980637384621 17388738097294492739019233)
  ·
    refine ⟨13041553572970869554264425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17388738097294492739019233 13041553572970869554264425)
    ·
      refine ⟨9781165179728152165698319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13041553572970869554264425 9781165179728152165698319)
      ·
        refine ⟨14671747769592228248547479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9781165179728152165698319 14671747769592228248547479)
        ·
          refine ⟨22007621654388342372821219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14671747769592228248547479 22007621654388342372821219)
          ·
            refine ⟨33011432481582513559231829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22007621654388342372821219 33011432481582513559231829)
            ·
              refine ⟨48356590549193135096531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 33011432481582513559231829 48356590549193135096531)
              ·
                rfl

theorem cell21_1907026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 11].length) (baseStart_1907026 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1907026 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1907026 prefixEnd_1907026 := by exact prefixLift 1907026
  have htrace : WordTrace (prefixWord ++ tailWord_1907026) baseStart_1907026 baseEnd_1907026 := by
    simpa [prefixWord, tailWord_1907026, baseEnd_1907026] using wordTrace_append hprefix tailTrace_1907026
  have hstable : (prefixWord ++ tailWord_1907026).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1907026).length < 2 ^ (prefixWord ++ tailWord_1907026).sum := by decide
  have hdescent : baseEnd_1907026 < baseStart_1907026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1907026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1907038 : List Nat := [4, 4, 2, 1, 1, 2, 2, 1, 4]
def baseStart_1907038 : Nat := 118140960795 + 1907038 * 2 ^ 59
def prefixEnd_1907038 : Nat := 4983230072969 + 3 ^ 40 * 1907038 * 2
def baseEnd_1907038 : Nat := 435212053506228861668755

theorem tailTrace_1907038 : CollatzResearch.WordTrace tailWord_1907038 prefixEnd_1907038 435212053506228861668755 := by
  unfold tailWord_1907038
  simp only [CollatzResearch.WordTrace]
  refine ⟨8694423758141812125689221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46370260043422998003675845 8694423758141812125689221)
  ·
    refine ⟨1630204454651589773566729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8694423758141812125689221 1630204454651589773566729)
    ·
      refine ⟨1222653340988692330175047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1630204454651589773566729 1222653340988692330175047)
      ·
        refine ⟨1833980011483038495262571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1222653340988692330175047 1833980011483038495262571)
        ·
          refine ⟨2750970017224557742893857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1833980011483038495262571 2750970017224557742893857)
          ·
            refine ⟨2063227512918418307170393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2750970017224557742893857 2063227512918418307170393)
            ·
              refine ⟨1547420634688813730377795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2063227512918418307170393 1547420634688813730377795)
              ·
                refine ⟨2321130952033220595566693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1547420634688813730377795 2321130952033220595566693)
                ·
                  refine ⟨435212053506228861668755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2321130952033220595566693 435212053506228861668755)
                  ·
                    rfl

theorem cell21_1907038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_1907038 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1907038 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1907038 prefixEnd_1907038 := by exact prefixLift 1907038
  have htrace : WordTrace (prefixWord ++ tailWord_1907038) baseStart_1907038 baseEnd_1907038 := by
    simpa [prefixWord, tailWord_1907038, baseEnd_1907038] using wordTrace_append hprefix tailTrace_1907038
  have hstable : (prefixWord ++ tailWord_1907038).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1907038).length < 2 ^ (prefixWord ++ tailWord_1907038).sum := by decide
  have hdescent : baseEnd_1907038 < baseStart_1907038 := by decide
  rcases family_descends (prefixWord ++ tailWord_1907038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1907170 : List Nat := [3, 3, 3, 2, 1, 2, 2, 5]
def baseStart_1907170 : Nat := 118140960795 + 1907170 * 2 ^ 59
def prefixEnd_1907170 : Nat := 4983230072969 + 3 ^ 40 * 1907170 * 2
def baseEnd_1907170 : Nat := 145080725901541988489495

theorem tailTrace_1907170 : CollatzResearch.WordTrace tailWord_1907170 prefixEnd_1907170 145080725901541988489495 := by
  unfold tailWord_1907170
  simp only [CollatzResearch.WordTrace]
  refine ⟨17390051125164070887329741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46373469667104189032879309 17390051125164070887329741)
  ·
    refine ⟨6521269171936526582748653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17390051125164070887329741 6521269171936526582748653)
    ·
      refine ⟨2445475939476197468530745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6521269171936526582748653 2445475939476197468530745)
      ·
        refine ⟨1834106954607148101398059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2445475939476197468530745 1834106954607148101398059)
        ·
          refine ⟨2751160431910722152097089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1834106954607148101398059 2751160431910722152097089)
          ·
            refine ⟨2063370323933041614072817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2751160431910722152097089 2063370323933041614072817)
            ·
              refine ⟨1547527742949781210554613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2063370323933041614072817 1547527742949781210554613)
              ·
                refine ⟨145080725901541988489495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1547527742949781210554613 145080725901541988489495)
                ·
                  rfl

theorem cell21_1907170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 2, 5].length) (baseStart_1907170 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1907170 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1907170 prefixEnd_1907170 := by exact prefixLift 1907170
  have htrace : WordTrace (prefixWord ++ tailWord_1907170) baseStart_1907170 baseEnd_1907170 := by
    simpa [prefixWord, tailWord_1907170, baseEnd_1907170] using wordTrace_append hprefix tailTrace_1907170
  have hstable : (prefixWord ++ tailWord_1907170).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1907170).length < 2 ^ (prefixWord ++ tailWord_1907170).sum := by decide
  have hdescent : baseEnd_1907170 < baseStart_1907170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1907170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1907260 : List Nat := [2, 2, 2, 2, 3, 3, 2, 2, 3]
def baseStart_1907260 : Nat := 118140960795 + 1907260 * 2 ^ 59
def prefixEnd_1907260 : Nat := 4983230072969 + 3 ^ 40 * 1907260 * 2
def baseEnd_1907260 : Nat := 435262716930805808968301

theorem tailTrace_1907260 : CollatzResearch.WordTrace tailWord_1907260 prefixEnd_1907260 435262716930805808968301 := by
  unfold tailWord_1907260
  simp only [CollatzResearch.WordTrace]
  refine ⟨34781743535165114460047617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46375658046886819280063489 34781743535165114460047617)
  ·
    refine ⟨26086307651373835845035713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34781743535165114460047617 26086307651373835845035713)
    ·
      refine ⟨19564730738530376883776785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26086307651373835845035713 19564730738530376883776785)
      ·
        refine ⟨14673548053897782662832589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19564730738530376883776785 14673548053897782662832589)
        ·
          refine ⟨5502580520211668498562221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14673548053897782662832589 5502580520211668498562221)
          ·
            refine ⟨2063467695079375686960833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5502580520211668498562221 2063467695079375686960833)
            ·
              refine ⟨1547600771309531765220625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2063467695079375686960833 1547600771309531765220625)
              ·
                refine ⟨1160700578482148823915469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1547600771309531765220625 1160700578482148823915469)
                ·
                  refine ⟨435262716930805808968301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1160700578482148823915469 435262716930805808968301)
                  ·
                    rfl

theorem cell21_1907260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 2, 2, 3].length) (baseStart_1907260 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1907260 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1907260 prefixEnd_1907260 := by exact prefixLift 1907260
  have htrace : WordTrace (prefixWord ++ tailWord_1907260) baseStart_1907260 baseEnd_1907260 := by
    simpa [prefixWord, tailWord_1907260, baseEnd_1907260] using wordTrace_append hprefix tailTrace_1907260
  have hstable : (prefixWord ++ tailWord_1907260).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1907260).length < 2 ^ (prefixWord ++ tailWord_1907260).sum := by decide
  have hdescent : baseEnd_1907260 < baseStart_1907260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1907260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1907271 : List Nat := [1, 1, 4, 1, 4, 3, 1, 6]
def baseStart_1907271 : Nat := 118140960795 + 1907271 * 2 ^ 59
def prefixEnd_1907271 : Nat := 4983230072969 + 3 ^ 40 * 1907271 * 2
def baseEnd_1907271 : Nat := 145088409093557411428315

theorem tailTrace_1907271 : CollatzResearch.WordTrace tailWord_1907271 prefixEnd_1907271 145088409093557411428315 := by
  unfold tailWord_1907271
  simp only [CollatzResearch.WordTrace]
  refine ⟨69563888273290377798745667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46375925515526918532497111 69563888273290377798745667)
  ·
    refine ⟨104345832409935566698118501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69563888273290377798745667 104345832409935566698118501)
    ·
      refine ⟨19564843576862918755897219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104345832409935566698118501 19564843576862918755897219)
      ·
        refine ⟨29347265365294378133845829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19564843576862918755897219 29347265365294378133845829)
        ·
          refine ⟨5502612255992695900096093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29347265365294378133845829 5502612255992695900096093)
          ·
            refine ⟨2063479595997260962536035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5502612255992695900096093 2063479595997260962536035)
            ·
              refine ⟨3095219393995891443804053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2063479595997260962536035 3095219393995891443804053)
              ·
                refine ⟨145088409093557411428315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3095219393995891443804053 145088409093557411428315)
                ·
                  rfl

theorem cell21_1907271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 1, 6].length) (baseStart_1907271 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1907271 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1907271 prefixEnd_1907271 := by exact prefixLift 1907271
  have htrace : WordTrace (prefixWord ++ tailWord_1907271) baseStart_1907271 baseEnd_1907271 := by
    simpa [prefixWord, tailWord_1907271, baseEnd_1907271] using wordTrace_append hprefix tailTrace_1907271
  have hstable : (prefixWord ++ tailWord_1907271).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1907271).length < 2 ^ (prefixWord ++ tailWord_1907271).sum := by decide
  have hdescent : baseEnd_1907271 < baseStart_1907271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1907271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1907294 : List Nat := [4, 4, 1, 2, 1, 1, 2, 3, 3]
def baseStart_1907294 : Nat := 118140960795 + 1907294 * 2 ^ 59
def prefixEnd_1907294 : Nat := 4983230072969 + 3 ^ 40 * 1907294 * 2
def baseEnd_1907294 : Nat := 435270476194029305401565

theorem tailTrace_1907294 : CollatzResearch.WordTrace tailWord_1907294 prefixEnd_1907294 435270476194029305401565 := by
  unfold tailWord_1907294
  simp only [CollatzResearch.WordTrace]
  refine ⟨8695590894025881590854117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46376484768138035151221957 8695590894025881590854117)
  ·
    refine ⟨1630423292629852798285147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8695590894025881590854117 1630423292629852798285147)
    ·
      refine ⟨2445634938944779197427721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1630423292629852798285147 2445634938944779197427721)
      ·
        refine ⟨1834226204208584398070791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2445634938944779197427721 1834226204208584398070791)
        ·
          refine ⟨2751339306312876597106187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1834226204208584398070791 2751339306312876597106187)
          ·
            refine ⟨4127008959469314895659281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2751339306312876597106187 4127008959469314895659281)
            ·
              refine ⟨3095256719601986171744461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4127008959469314895659281 3095256719601986171744461)
              ·
                refine ⟨1160721269850744814404173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3095256719601986171744461 1160721269850744814404173)
                ·
                  refine ⟨435270476194029305401565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1160721269850744814404173 435270476194029305401565)
                  ·
                    rfl

theorem cell21_1907294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_1907294 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1907294 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1907294 prefixEnd_1907294 := by exact prefixLift 1907294
  have htrace : WordTrace (prefixWord ++ tailWord_1907294) baseStart_1907294 baseEnd_1907294 := by
    simpa [prefixWord, tailWord_1907294, baseEnd_1907294] using wordTrace_append hprefix tailTrace_1907294
  have hstable : (prefixWord ++ tailWord_1907294).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1907294).length < 2 ^ (prefixWord ++ tailWord_1907294).sum := by decide
  have hdescent : baseEnd_1907294 < baseStart_1907294 := by decide
  rcases family_descends (prefixWord ++ tailWord_1907294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1907299 : List Nat := [1, 1, 1, 5, 1, 2, 2, 2, 6]
def baseStart_1907299 : Nat := 118140960795 + 1907299 * 2 ^ 59
def prefixEnd_1907299 : Nat := 4983230072969 + 3 ^ 40 * 1907299 * 2
def baseEnd_1907299 : Nat := 435271617262150407818221

theorem tailTrace_1907299 : CollatzResearch.WordTrace tailWord_1907299 prefixEnd_1907299 435271617262150407818221 := by
  unfold tailWord_1907299
  simp only [CollatzResearch.WordTrace]
  refine ⟨69564909517188938580764951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46376606344792625720509967 69564909517188938580764951)
  ·
    refine ⟨104347364275783407871147427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69564909517188938580764951 104347364275783407871147427)
    ·
      refine ⟨156521046413675111806721141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104347364275783407871147427 156521046413675111806721141)
      ·
        refine ⟨14673848101282041731880107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 156521046413675111806721141 14673848101282041731880107)
        ·
          refine ⟨22010772151923062597820161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14673848101282041731880107 22010772151923062597820161)
          ·
            refine ⟨16508079113942296948365121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22010772151923062597820161 16508079113942296948365121)
            ·
              refine ⟨12381059335456722711273841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16508079113942296948365121 12381059335456722711273841)
              ·
                refine ⟨9285794501592542033455381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12381059335456722711273841 9285794501592542033455381)
                ·
                  refine ⟨435271617262150407818221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9285794501592542033455381 435271617262150407818221)
                  ·
                    rfl

theorem cell21_1907299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 2, 6].length) (baseStart_1907299 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1907299 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1907299 prefixEnd_1907299 := by exact prefixLift 1907299
  have htrace : WordTrace (prefixWord ++ tailWord_1907299) baseStart_1907299 baseEnd_1907299 := by
    simpa [prefixWord, tailWord_1907299, baseEnd_1907299] using wordTrace_append hprefix tailTrace_1907299
  have hstable : (prefixWord ++ tailWord_1907299).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1907299).length < 2 ^ (prefixWord ++ tailWord_1907299).sum := by decide
  have hdescent : baseEnd_1907299 < baseStart_1907299 := by decide
  rcases family_descends (prefixWord ++ tailWord_1907299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1907333 : List Nat := [1, 3, 1, 1, 4, 3, 3, 1, 4]
def baseStart_1907333 : Nat := 118140960795 + 1907333 * 2 ^ 59
def prefixEnd_1907333 : Nat := 4983230072969 + 3 ^ 40 * 1907333 * 2
def baseEnd_1907333 : Nat := 435279376525373904251485

theorem tailTrace_1907333 : CollatzResearch.WordTrace tailWord_1907333 prefixEnd_1907333 435279376525373904251485 := by
  unfold tailWord_1907333
  simp only [CollatzResearch.WordTrace]
  refine ⟨69566149599065762387502653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46377433066043841591668435 69566149599065762387502653)
  ·
    refine ⟨26087306099649660895313495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69566149599065762387502653 26087306099649660895313495)
    ·
      refine ⟨39130959149474491342970243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26087306099649660895313495 39130959149474491342970243)
      ·
        refine ⟨58696438724211737014455365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39130959149474491342970243 58696438724211737014455365)
        ·
          refine ⟨11005582260789700690210381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58696438724211737014455365 11005582260789700690210381)
          ·
            refine ⟨4127093347796137758828893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11005582260789700690210381 4127093347796137758828893)
            ·
              refine ⟨1547660005423551659560835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4127093347796137758828893 1547660005423551659560835)
              ·
                refine ⟨2321490008135327489341253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1547660005423551659560835 2321490008135327489341253)
                ·
                  refine ⟨435279376525373904251485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2321490008135327489341253 435279376525373904251485)
                  ·
                    rfl

theorem cell21_1907333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 3, 1, 4].length) (baseStart_1907333 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1907333 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1907333 prefixEnd_1907333 := by exact prefixLift 1907333
  have htrace : WordTrace (prefixWord ++ tailWord_1907333) baseStart_1907333 baseEnd_1907333 := by
    simpa [prefixWord, tailWord_1907333, baseEnd_1907333] using wordTrace_append hprefix tailTrace_1907333
  have hstable : (prefixWord ++ tailWord_1907333).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1907333).length < 2 ^ (prefixWord ++ tailWord_1907333).sum := by decide
  have hdescent : baseEnd_1907333 < baseStart_1907333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1907333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1907375 : List Nat := [1, 1, 2, 1, 2, 5, 2, 1, 6]
def baseStart_1907375 : Nat := 118140960795 + 1907375 * 2 ^ 59
def prefixEnd_1907375 : Nat := 4983230072969 + 3 ^ 40 * 1907375 * 2
def baseEnd_1907375 : Nat := 435288961497591164551399

theorem tailTrace_1907375 : CollatzResearch.WordTrace tailWord_1907375 prefixEnd_1907375 435288961497591164551399 := by
  unfold tailWord_1907375
  simp only [CollatzResearch.WordTrace]
  refine ⟨69567681464913603560531579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46378454309942402373687719 69567681464913603560531579)
  ·
    refine ⟨104351522197370405340797369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69567681464913603560531579 104351522197370405340797369)
    ·
      refine ⟨78263641648027804005598027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104351522197370405340797369 78263641648027804005598027)
      ·
        refine ⟨117395462472041706008397041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78263641648027804005598027 117395462472041706008397041)
        ·
          refine ⟨88046596854031279506297781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117395462472041706008397041 88046596854031279506297781)
          ·
            refine ⟨8254368455065432453715417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 88046596854031279506297781 8254368455065432453715417)
            ·
              refine ⟨6190776341299074340286563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8254368455065432453715417 6190776341299074340286563)
              ·
                refine ⟨9286164511948611510429845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6190776341299074340286563 9286164511948611510429845)
                ·
                  refine ⟨435288961497591164551399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9286164511948611510429845 435288961497591164551399)
                  ·
                    rfl

theorem cell21_1907375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 1, 6].length) (baseStart_1907375 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1907375 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1907375 prefixEnd_1907375 := by exact prefixLift 1907375
  have htrace : WordTrace (prefixWord ++ tailWord_1907375) baseStart_1907375 baseEnd_1907375 := by
    simpa [prefixWord, tailWord_1907375, baseEnd_1907375] using wordTrace_append hprefix tailTrace_1907375
  have hstable : (prefixWord ++ tailWord_1907375).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1907375).length < 2 ^ (prefixWord ++ tailWord_1907375).sum := by decide
  have hdescent : baseEnd_1907375 < baseStart_1907375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1907375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1907392 : List Nat := [2, 1, 1, 2, 4, 3, 1, 3, 4]
def baseStart_1907392 : Nat := 118140960795 + 1907392 * 2 ^ 59
def prefixEnd_1907392 : Nat := 4983230072969 + 3 ^ 40 * 1907392 * 2
def baseEnd_1907392 : Nat := 435292841129202912768031

theorem tailTrace_1907392 : CollatzResearch.WordTrace tailWord_1907392 prefixEnd_1907392 435292841129202912768031 := by
  unfold tailWord_1907392
  simp only [CollatzResearch.WordTrace]
  refine ⟨34784150752926007731950215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46378867670568010309266953 34784150752926007731950215)
  ·
    refine ⟨52176226129389011597925323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34784150752926007731950215 52176226129389011597925323)
    ·
      refine ⟨78264339194083517396887985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52176226129389011597925323 78264339194083517396887985)
      ·
        refine ⟨58698254395562638047665989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78264339194083517396887985 58698254395562638047665989)
        ·
          refine ⟨11005922699167994633937373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58698254395562638047665989 11005922699167994633937373)
          ·
            refine ⟨4127221012187997987726515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11005922699167994633937373 4127221012187997987726515)
            ·
              refine ⟨6190831518281996981589773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4127221012187997987726515 6190831518281996981589773)
              ·
                refine ⟨2321561819355748868096165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6190831518281996981589773 2321561819355748868096165)
                ·
                  refine ⟨435292841129202912768031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2321561819355748868096165 435292841129202912768031)
                  ·
                    rfl

theorem cell21_1907392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 3, 4].length) (baseStart_1907392 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1907392 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1907392 prefixEnd_1907392 := by exact prefixLift 1907392
  have htrace : WordTrace (prefixWord ++ tailWord_1907392) baseStart_1907392 baseEnd_1907392 := by
    simpa [prefixWord, tailWord_1907392, baseEnd_1907392] using wordTrace_append hprefix tailTrace_1907392
  have hstable : (prefixWord ++ tailWord_1907392).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1907392).length < 2 ^ (prefixWord ++ tailWord_1907392).sum := by decide
  have hdescent : baseEnd_1907392 < baseStart_1907392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1907392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1907406 : List Nat := [4, 1, 1, 1, 3, 2, 2, 7]
def baseStart_1907406 : Nat := 118140960795 + 1907406 * 2 ^ 59
def prefixEnd_1907406 : Nat := 4983230072969 + 3 ^ 40 * 1907406 * 2
def baseEnd_1907406 : Nat := 145098678706647333178223

theorem tailTrace_1907406 : CollatzResearch.WordTrace tailWord_1907406 prefixEnd_1907406 145098678706647333178223 := by
  unfold tailWord_1907406
  simp only [CollatzResearch.WordTrace]
  refine ⟨8696101515975161981863759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46379208085200863903273381 8696101515975161981863759)
  ·
    refine ⟨13044152273962742972795639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8696101515975161981863759 13044152273962742972795639)
    ·
      refine ⟨19566228410944114459193459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13044152273962742972795639 19566228410944114459193459)
      ·
        refine ⟨29349342616416171688790189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19566228410944114459193459 29349342616416171688790189)
        ·
          refine ⟨11006003481156064383296321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29349342616416171688790189 11006003481156064383296321)
          ·
            refine ⟨8254502610867048287472241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11006003481156064383296321 8254502610867048287472241)
            ·
              refine ⟨6190876958150286215604181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8254502610867048287472241 6190876958150286215604181)
              ·
                refine ⟨145098678706647333178223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6190876958150286215604181 145098678706647333178223)
                ·
                  rfl

theorem cell21_1907406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 7].length) (baseStart_1907406 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1907406 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1907406 prefixEnd_1907406 := by exact prefixLift 1907406
  have htrace : WordTrace (prefixWord ++ tailWord_1907406) baseStart_1907406 baseEnd_1907406 := by
    simpa [prefixWord, tailWord_1907406, baseEnd_1907406] using wordTrace_append hprefix tailTrace_1907406
  have hstable : (prefixWord ++ tailWord_1907406).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1907406).length < 2 ^ (prefixWord ++ tailWord_1907406).sum := by decide
  have hdescent : baseEnd_1907406 < baseStart_1907406 := by decide
  rcases family_descends (prefixWord ++ tailWord_1907406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1907437 : List Nat := [1, 5, 1, 2, 1, 1, 2, 3, 5]
def baseStart_1907437 : Nat := 118140960795 + 1907437 * 2 ^ 59
def prefixEnd_1907437 : Nat := 4983230072969 + 3 ^ 40 * 1907437 * 2
def baseEnd_1907437 : Nat := 435303110742292834517939

theorem tailTrace_1907437 : CollatzResearch.WordTrace tailWord_1907437 prefixEnd_1907437 435303110742292834517939 := by
  unfold tailWord_1907437
  simp only [CollatzResearch.WordTrace]
  refine ⟨69569942790688988149288565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46379961860459325432859043 69569942790688988149288565)
  ·
    refine ⟨6522182136627092638995803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 69569942790688988149288565 6522182136627092638995803)
    ·
      refine ⟨9783273204940638958493705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6522182136627092638995803 9783273204940638958493705)
      ·
        refine ⟨7337454903705479218870279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9783273204940638958493705 7337454903705479218870279)
        ·
          refine ⟨11006182355558218828305419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7337454903705479218870279 11006182355558218828305419)
          ·
            refine ⟨16509273533337328242458129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11006182355558218828305419 16509273533337328242458129)
            ·
              refine ⟨12381955150002996181843597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16509273533337328242458129 12381955150002996181843597)
              ·
                refine ⟨4643233181251123568191349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12381955150002996181843597 4643233181251123568191349)
                ·
                  refine ⟨435303110742292834517939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4643233181251123568191349 435303110742292834517939)
                  ·
                    rfl

theorem cell21_1907437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 3, 5].length) (baseStart_1907437 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1907437 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1907437 prefixEnd_1907437 := by exact prefixLift 1907437
  have htrace : WordTrace (prefixWord ++ tailWord_1907437) baseStart_1907437 baseEnd_1907437 := by
    simpa [prefixWord, tailWord_1907437, baseEnd_1907437] using wordTrace_append hprefix tailTrace_1907437
  have hstable : (prefixWord ++ tailWord_1907437).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1907437).length < 2 ^ (prefixWord ++ tailWord_1907437).sum := by decide
  have hdescent : baseEnd_1907437 < baseStart_1907437 := by decide
  rcases family_descends (prefixWord ++ tailWord_1907437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1907454 : List Nat := [4, 2, 2, 1, 2, 2, 1, 2, 5]
def baseStart_1907454 : Nat := 118140960795 + 1907454 * 2 ^ 59
def prefixEnd_1907454 : Nat := 4983230072969 + 3 ^ 40 * 1907454 * 2
def baseEnd_1907454 : Nat := 435306990373904582734571

theorem tailTrace_1907454 : CollatzResearch.WordTrace tailWord_1907454 prefixEnd_1907454 435306990373904582734571 := by
  unfold tailWord_1907454
  simp only [CollatzResearch.WordTrace]
  refine ⟨8696320353953425006582177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46380375221084933368438277 8696320353953425006582177)
  ·
    refine ⟨6522240265465068754936633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8696320353953425006582177 6522240265465068754936633)
    ·
      refine ⟨4891680199098801566202475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6522240265465068754936633 4891680199098801566202475)
      ·
        refine ⟨7337520298648202349303713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4891680199098801566202475 7337520298648202349303713)
        ·
          refine ⟨5503140223986151761977785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7337520298648202349303713 5503140223986151761977785)
          ·
            refine ⟨4127355167989613821483339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5503140223986151761977785 4127355167989613821483339)
            ·
              refine ⟨6191032751984420732225009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4127355167989613821483339 6191032751984420732225009)
              ·
                refine ⟨4643274563988315549168757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6191032751984420732225009 4643274563988315549168757)
                ·
                  refine ⟨435306990373904582734571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4643274563988315549168757 435306990373904582734571)
                  ·
                    rfl

theorem cell21_1907454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 2, 5].length) (baseStart_1907454 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1907454 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1907454 prefixEnd_1907454 := by exact prefixLift 1907454
  have htrace : WordTrace (prefixWord ++ tailWord_1907454) baseStart_1907454 baseEnd_1907454 := by
    simpa [prefixWord, tailWord_1907454, baseEnd_1907454] using wordTrace_append hprefix tailTrace_1907454
  have hstable : (prefixWord ++ tailWord_1907454).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1907454).length < 2 ^ (prefixWord ++ tailWord_1907454).sum := by decide
  have hdescent : baseEnd_1907454 < baseStart_1907454 := by decide
  rcases family_descends (prefixWord ++ tailWord_1907454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1907465 : List Nat := [1, 2, 1, 1, 3, 2, 2, 9]
def baseStart_1907465 : Nat := 118140960795 + 1907465 * 2 ^ 59
def prefixEnd_1907465 : Nat := 4983230072969 + 3 ^ 40 * 1907465 * 2
def baseEnd_1907465 : Nat := 145103166907923669350405

theorem tailTrace_1907465 : CollatzResearch.WordTrace tailWord_1907465 prefixEnd_1907465 145103166907923669350405 := by
  unfold tailWord_1907465
  simp only [CollatzResearch.WordTrace]
  refine ⟨69570964034587548931307849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46380642689725032620871899 69570964034587548931307849)
  ·
    refine ⟨52178223025940661698480887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69570964034587548931307849 52178223025940661698480887)
    ·
      refine ⟨78267334538910992547721331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52178223025940661698480887 78267334538910992547721331)
      ·
        refine ⟨117401001808366488821581997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78267334538910992547721331 117401001808366488821581997)
        ·
          refine ⟨44025375678137433308093249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117401001808366488821581997 44025375678137433308093249)
          ·
            refine ⟨33019031758603074981069937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44025375678137433308093249 33019031758603074981069937)
            ·
              refine ⟨24764273818952306235802453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33019031758603074981069937 24764273818952306235802453)
              ·
                refine ⟨145103166907923669350405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24764273818952306235802453 145103166907923669350405)
                ·
                  rfl

theorem cell21_1907465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 9].length) (baseStart_1907465 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1907465 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1907465 prefixEnd_1907465 := by exact prefixLift 1907465
  have htrace : WordTrace (prefixWord ++ tailWord_1907465) baseStart_1907465 baseEnd_1907465 := by
    simpa [prefixWord, tailWord_1907465, baseEnd_1907465] using wordTrace_append hprefix tailTrace_1907465
  have hstable : (prefixWord ++ tailWord_1907465).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1907465).length < 2 ^ (prefixWord ++ tailWord_1907465).sum := by decide
  have hdescent : baseEnd_1907465 < baseStart_1907465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1907465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1907485 : List Nat := [1, 4, 2, 4, 1, 1, 1, 1, 6]
def baseStart_1907485 : Nat := 118140960795 + 1907485 * 2 ^ 59
def prefixEnd_1907485 : Nat := 4983230072969 + 3 ^ 40 * 1907485 * 2
def baseEnd_1907485 : Nat := 435314064996255417717841

theorem tailTrace_1907485 : CollatzResearch.WordTrace tailWord_1907485 prefixEnd_1907485 435314064996255417717841 := by
  unfold tailWord_1907485
  simp only [CollatzResearch.WordTrace]
  refine ⟨69571693494515092347035909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46381128996343394898023939 69571693494515092347035909)
  ·
    refine ⟨13044692530221579815069233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69571693494515092347035909 13044692530221579815069233)
    ·
      refine ⟨9783519397666184861301925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13044692530221579815069233 9783519397666184861301925)
      ·
        refine ⟨1834409887062409661494111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9783519397666184861301925 1834409887062409661494111)
        ·
          refine ⟨2751614830593614492241167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1834409887062409661494111 2751614830593614492241167)
          ·
            refine ⟨4127422245890421738361751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2751614830593614492241167 4127422245890421738361751)
            ·
              refine ⟨6191133368835632607542627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4127422245890421738361751 6191133368835632607542627)
              ·
                refine ⟨9286700053253448911313941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6191133368835632607542627 9286700053253448911313941)
                ·
                  refine ⟨435314064996255417717841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9286700053253448911313941 435314064996255417717841)
                  ·
                    rfl

theorem cell21_1907485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 1, 6].length) (baseStart_1907485 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1907485 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1907485 prefixEnd_1907485 := by exact prefixLift 1907485
  have htrace : WordTrace (prefixWord ++ tailWord_1907485) baseStart_1907485 baseEnd_1907485 := by
    simpa [prefixWord, tailWord_1907485, baseEnd_1907485] using wordTrace_append hprefix tailTrace_1907485
  have hstable : (prefixWord ++ tailWord_1907485).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1907485).length < 2 ^ (prefixWord ++ tailWord_1907485).sum := by decide
  have hdescent : baseEnd_1907485 < baseStart_1907485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1907485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1907502 : List Nat := [4, 1, 3, 2, 1, 2, 3, 1, 4]
def baseStart_1907502 : Nat := 118140960795 + 1907502 * 2 ^ 59
def prefixEnd_1907502 : Nat := 4983230072969 + 3 ^ 40 * 1907502 * 2
def baseEnd_1907502 : Nat := 435317944627867165934473

theorem tailTrace_1907502 : CollatzResearch.WordTrace tailWord_1907502 prefixEnd_1907502 435317944627867165934473 := by
  unfold tailWord_1907502
  simp only [CollatzResearch.WordTrace]
  refine ⟨8696539191931688031300595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46381542356969002833603173 8696539191931688031300595)
  ·
    refine ⟨13044808787897532046950893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8696539191931688031300595 13044808787897532046950893)
    ·
      refine ⟨4891803295461574517606585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13044808787897532046950893 4891803295461574517606585)
      ·
        refine ⟨3668852471596180888204939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4891803295461574517606585 3668852471596180888204939)
        ·
          refine ⟨5503278707394271332307409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3668852471596180888204939 5503278707394271332307409)
          ·
            refine ⟨4127459030545703499230557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5503278707394271332307409 4127459030545703499230557)
            ·
              refine ⟨1547797136454638812211459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4127459030545703499230557 1547797136454638812211459)
              ·
                refine ⟨2321695704681958218317189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1547797136454638812211459 2321695704681958218317189)
                ·
                  refine ⟨435317944627867165934473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2321695704681958218317189 435317944627867165934473)
                  ·
                    rfl

theorem cell21_1907502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 3, 1, 4].length) (baseStart_1907502 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1907502 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1907502 prefixEnd_1907502 := by exact prefixLift 1907502
  have htrace : WordTrace (prefixWord ++ tailWord_1907502) baseStart_1907502 baseEnd_1907502 := by
    simpa [prefixWord, tailWord_1907502, baseEnd_1907502] using wordTrace_append hprefix tailTrace_1907502
  have hstable : (prefixWord ++ tailWord_1907502).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1907502).length < 2 ^ (prefixWord ++ tailWord_1907502).sum := by decide
  have hdescent : baseEnd_1907502 < baseStart_1907502 := by decide
  rcases family_descends (prefixWord ++ tailWord_1907502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1907665 : List Nat := [1, 2, 2, 1, 2, 1, 3, 6, 3]
def baseStart_1907665 : Nat := 118140960795 + 1907665 * 2 ^ 59
def prefixEnd_1907665 : Nat := 4983230072969 + 3 ^ 40 * 1907665 * 2
def baseEnd_1907665 : Nat := 435355143448615104717473

theorem tailTrace_1907665 : CollatzResearch.WordTrace tailWord_1907665 prefixEnd_1907665 435355143448615104717473 := by
  unfold tailWord_1907665
  simp only [CollatzResearch.WordTrace]
  refine ⟨69578258633862983088588449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46385505755908655392392299 69578258633862983088588449)
  ·
    refine ⟨52183693975397237316441337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69578258633862983088588449 52183693975397237316441337)
    ·
      refine ⟨39137770481547927987331003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52183693975397237316441337 39137770481547927987331003)
      ·
        refine ⟨58706655722321891980996505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39137770481547927987331003 58706655722321891980996505)
        ·
          refine ⟨44029991791741418985747379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58706655722321891980996505 44029991791741418985747379)
          ·
            refine ⟨66044987687612128478621069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44029991791741418985747379 66044987687612128478621069)
            ·
              refine ⟨24766870382854548179482901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66044987687612128478621069 24766870382854548179482901)
              ·
                refine ⟨1160947049196306945913261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 24766870382854548179482901 1160947049196306945913261)
                ·
                  refine ⟨435355143448615104717473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1160947049196306945913261 435355143448615104717473)
                  ·
                    rfl

theorem cell21_1907665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 6, 3].length) (baseStart_1907665 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1907665 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1907665 prefixEnd_1907665 := by exact prefixLift 1907665
  have htrace : WordTrace (prefixWord ++ tailWord_1907665) baseStart_1907665 baseEnd_1907665 := by
    simpa [prefixWord, tailWord_1907665, baseEnd_1907665] using wordTrace_append hprefix tailTrace_1907665
  have hstable : (prefixWord ++ tailWord_1907665).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1907665).length < 2 ^ (prefixWord ++ tailWord_1907665).sum := by decide
  have hdescent : baseEnd_1907665 < baseStart_1907665 := by decide
  rcases family_descends (prefixWord ++ tailWord_1907665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1907682 : List Nat := [3, 3, 3, 1, 1, 1, 2, 2, 5]
def baseStart_1907682 : Nat := 118140960795 + 1907682 * 2 ^ 59
def prefixEnd_1907682 : Nat := 4983230072969 + 3 ^ 40 * 1907682 * 2
def baseEnd_1907682 : Nat := 435359023080226852934105

theorem tailTrace_1907682 : CollatzResearch.WordTrace tailWord_1907682 prefixEnd_1907682 435359023080226852934105 := by
  unfold tailWord_1907682
  simp only [CollatzResearch.WordTrace]
  refine ⟨17394719668700348747989325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46385919116534263327971533 17394719668700348747989325)
  ·
    refine ⟨6523019875762630780495997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17394719668700348747989325 6523019875762630780495997)
    ·
      refine ⟨2446132453410986542685999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6523019875762630780495997 2446132453410986542685999)
      ·
        refine ⟨3669198680116479814028999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2446132453410986542685999 3669198680116479814028999)
        ·
          refine ⟨5503798020174719721043499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3669198680116479814028999 5503798020174719721043499)
          ·
            refine ⟨8255697030262079581565249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5503798020174719721043499 8255697030262079581565249)
            ·
              refine ⟨6191772772696559686173937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8255697030262079581565249 6191772772696559686173937)
              ·
                refine ⟨4643829579522419764630453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6191772772696559686173937 4643829579522419764630453)
                ·
                  refine ⟨435359023080226852934105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4643829579522419764630453 435359023080226852934105)
                  ·
                    rfl

theorem cell21_1907682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 2, 5].length) (baseStart_1907682 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1907682 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1907682 prefixEnd_1907682 := by exact prefixLift 1907682
  have htrace : WordTrace (prefixWord ++ tailWord_1907682) baseStart_1907682 baseEnd_1907682 := by
    simpa [prefixWord, tailWord_1907682, baseEnd_1907682] using wordTrace_append hprefix tailTrace_1907682
  have hstable : (prefixWord ++ tailWord_1907682).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1907682).length < 2 ^ (prefixWord ++ tailWord_1907682).sum := by decide
  have hdescent : baseEnd_1907682 < baseStart_1907682 := by decide
  rcases family_descends (prefixWord ++ tailWord_1907682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1907685 : List Nat := [1, 3, 1, 6, 2, 1, 2, 5]
def baseStart_1907685 : Nat := 118140960795 + 1907685 * 2 ^ 59
def prefixEnd_1907685 : Nat := 4983230072969 + 3 ^ 40 * 1907685 * 2
def baseEnd_1907685 : Nat := 145119902573699838128033

theorem tailTrace_1907685 : CollatzResearch.WordTrace tailWord_1907685 prefixEnd_1907685 145119902573699838128033 := by
  unfold tailWord_1907685
  simp only [CollatzResearch.WordTrace]
  refine ⟨69578988093790526504316509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46385992062527017669544339 69578988093790526504316509)
  ·
    refine ⟨26092120535171447439118691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69578988093790526504316509 26092120535171447439118691)
    ·
      refine ⟨39138180802757171158678037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26092120535171447439118691 39138180802757171158678037)
      ·
        refine ⟨1834602225129242398063033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 39138180802757171158678037 1834602225129242398063033)
        ·
          refine ⟨1375951668846931798547275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1834602225129242398063033 1375951668846931798547275)
          ·
            refine ⟨2063927503270397697820913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1375951668846931798547275 2063927503270397697820913)
            ·
              refine ⟨1547945627452798273365685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2063927503270397697820913 1547945627452798273365685)
              ·
                refine ⟨145119902573699838128033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1547945627452798273365685 145119902573699838128033)
                ·
                  rfl

theorem cell21_1907685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 2, 5].length) (baseStart_1907685 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1907685 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1907685 prefixEnd_1907685 := by exact prefixLift 1907685
  have htrace : WordTrace (prefixWord ++ tailWord_1907685) baseStart_1907685 baseEnd_1907685 := by
    simpa [prefixWord, tailWord_1907685, baseEnd_1907685] using wordTrace_append hprefix tailTrace_1907685
  have hstable : (prefixWord ++ tailWord_1907685).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1907685).length < 2 ^ (prefixWord ++ tailWord_1907685).sum := by decide
  have hdescent : baseEnd_1907685 < baseStart_1907685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1907685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1907758 : List Nat := [4, 1, 3, 1, 1, 1, 2, 5, 3]
def baseStart_1907758 : Nat := 118140960795 + 1907758 * 2 ^ 59
def prefixEnd_1907758 : Nat := 4983230072969 + 3 ^ 40 * 1907758 * 2
def baseEnd_1907758 : Nat := 435376367315667609667283

theorem tailTrace_1907758 : CollatzResearch.WordTrace tailWord_1907758 prefixEnd_1907758 435376367315667609667283 := by
  unfold tailWord_1907758
  simp only [CollatzResearch.WordTrace]
  refine ⟨8697706327815757496465491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46387767081684039981149285 8697706327815757496465491)
  ·
    refine ⟨13046559491723636244698237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8697706327815757496465491 13046559491723636244698237)
    ·
      refine ⟨4892459809396363591761839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13046559491723636244698237 4892459809396363591761839)
      ·
        refine ⟨7338689714094545387642759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4892459809396363591761839 7338689714094545387642759)
        ·
          refine ⟨11008034571141818081464139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7338689714094545387642759 11008034571141818081464139)
          ·
            refine ⟨16512051856712727122196209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11008034571141818081464139 16512051856712727122196209)
            ·
              refine ⟨12384038892534545341647157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16512051856712727122196209 12384038892534545341647157)
              ·
                refine ⟨1161003646175113625779421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12384038892534545341647157 1161003646175113625779421)
                ·
                  refine ⟨435376367315667609667283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1161003646175113625779421 435376367315667609667283)
                  ·
                    rfl

theorem cell21_1907758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 5, 3].length) (baseStart_1907758 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1907758 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1907758 prefixEnd_1907758 := by exact prefixLift 1907758
  have htrace : WordTrace (prefixWord ++ tailWord_1907758) baseStart_1907758 baseEnd_1907758 := by
    simpa [prefixWord, tailWord_1907758, baseEnd_1907758] using wordTrace_append hprefix tailTrace_1907758
  have hstable : (prefixWord ++ tailWord_1907758).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1907758).length < 2 ^ (prefixWord ++ tailWord_1907758).sum := by decide
  have hdescent : baseEnd_1907758 < baseStart_1907758 := by decide
  rcases family_descends (prefixWord ++ tailWord_1907758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1907769 : List Nat := [1, 2, 1, 5, 2, 10]
def baseStart_1907769 : Nat := 118140960795 + 1907769 * 2 ^ 59
def prefixEnd_1907769 : Nat := 4983230072969 + 3 ^ 40 * 1907769 * 2
def baseEnd_1907769 : Nat := 16125143617242001295701

theorem tailTrace_1907769 : CollatzResearch.WordTrace tailWord_1907769 prefixEnd_1907769 16125143617242001295701 := by
  unfold tailWord_1907769
  simp only [CollatzResearch.WordTrace]
  refine ⟨69582051825486208850374361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46388034550324139233582907 69582051825486208850374361)
  ·
    refine ⟨52186538869114656637780771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69582051825486208850374361 52186538869114656637780771)
    ·
      refine ⟨78279808303671984956671157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52186538869114656637780771 78279808303671984956671157)
      ·
        refine ⟨7338732028469248589687921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 78279808303671984956671157 7338732028469248589687921)
        ·
          refine ⟨5504049021351936442265941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7338732028469248589687921 5504049021351936442265941)
          ·
            refine ⟨16125143617242001295701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5504049021351936442265941 16125143617242001295701)
            ·
              rfl

theorem cell21_1907769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 10].length) (baseStart_1907769 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1907769 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1907769 prefixEnd_1907769 := by exact prefixLift 1907769
  have htrace : WordTrace (prefixWord ++ tailWord_1907769) baseStart_1907769 baseEnd_1907769 := by
    simpa [prefixWord, tailWord_1907769, baseEnd_1907769] using wordTrace_append hprefix tailTrace_1907769
  have hstable : (prefixWord ++ tailWord_1907769).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1907769).length < 2 ^ (prefixWord ++ tailWord_1907769).sum := by decide
  have hdescent : baseEnd_1907769 < baseStart_1907769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1907769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1907772 : List Nat := [2, 2, 2, 2, 2, 3, 2, 2, 4]
def baseStart_1907772 : Nat := 118140960795 + 1907772 * 2 ^ 59
def prefixEnd_1907772 : Nat := 4983230072969 + 3 ^ 40 * 1907772 * 2
def baseEnd_1907772 : Nat := 435379562306406696433921

theorem tailTrace_1907772 : CollatzResearch.WordTrace tailWord_1907772 prefixEnd_1907772 435379562306406696433921 := by
  unfold tailWord_1907772
  simp only [CollatzResearch.WordTrace]
  refine ⟨34791080622237670181366785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46388107496316893575155713 34791080622237670181366785)
  ·
    refine ⟨26093310466678252636025089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34791080622237670181366785 26093310466678252636025089)
    ·
      refine ⟨19569982850008689477018817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26093310466678252636025089 19569982850008689477018817)
      ·
        refine ⟨14677487137506517107764113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19569982850008689477018817 14677487137506517107764113)
        ·
          refine ⟨11008115353129887830823085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14677487137506517107764113 11008115353129887830823085)
          ·
            refine ⟨4128043257423707936558657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11008115353129887830823085 4128043257423707936558657)
            ·
              refine ⟨3096032443067780952418993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4128043257423707936558657 3096032443067780952418993)
              ·
                refine ⟨2322024332300835714314245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3096032443067780952418993 2322024332300835714314245)
                ·
                  refine ⟨435379562306406696433921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2322024332300835714314245 435379562306406696433921)
                  ·
                    rfl

theorem cell21_1907772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 2, 2, 4].length) (baseStart_1907772 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1907772 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1907772 prefixEnd_1907772 := by exact prefixLift 1907772
  have htrace : WordTrace (prefixWord ++ tailWord_1907772) baseStart_1907772 baseEnd_1907772 := by
    simpa [prefixWord, tailWord_1907772, baseEnd_1907772] using wordTrace_append hprefix tailTrace_1907772
  have hstable : (prefixWord ++ tailWord_1907772).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1907772).length < 2 ^ (prefixWord ++ tailWord_1907772).sum := by decide
  have hdescent : baseEnd_1907772 < baseStart_1907772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1907772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1907800 : List Nat := [2, 1, 2, 2, 1, 3, 3, 2, 5]
def baseStart_1907800 : Nat := 118140960795 + 1907800 * 2 ^ 59
def prefixEnd_1907800 : Nat := 4983230072969 + 3 ^ 40 * 1907800 * 2
def baseEnd_1907800 : Nat := 435385952287884869967197

theorem tailTrace_1907800 : CollatzResearch.WordTrace tailWord_1907800 prefixEnd_1907800 435385952287884869967197 := by
  unfold tailWord_1907800
  simp only [CollatzResearch.WordTrace]
  refine ⟨34791591244186950572376427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46388788325582600763168569 34791591244186950572376427)
  ·
    refine ⟨52187386866280425858564641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34791591244186950572376427 52187386866280425858564641)
    ·
      refine ⟨39140540149710319393923481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52187386866280425858564641 39140540149710319393923481)
      ·
        refine ⟨29355405112282739545442611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39140540149710319393923481 29355405112282739545442611)
        ·
          refine ⟨44033107668424109318163917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29355405112282739545442611 44033107668424109318163917)
          ·
            refine ⟨16512415375659040994311469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44033107668424109318163917 16512415375659040994311469)
            ·
              refine ⟨6192155765872140372866801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16512415375659040994311469 6192155765872140372866801)
              ·
                refine ⟨4644116824404105279650101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6192155765872140372866801 4644116824404105279650101)
                ·
                  refine ⟨435385952287884869967197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4644116824404105279650101 435385952287884869967197)
                  ·
                    rfl

theorem cell21_1907800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 2, 5].length) (baseStart_1907800 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1907800 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1907800 prefixEnd_1907800 := by exact prefixLift 1907800
  have htrace : WordTrace (prefixWord ++ tailWord_1907800) baseStart_1907800 baseEnd_1907800 := by
    simpa [prefixWord, tailWord_1907800, baseEnd_1907800] using wordTrace_append hprefix tailTrace_1907800
  have hstable : (prefixWord ++ tailWord_1907800).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1907800).length < 2 ^ (prefixWord ++ tailWord_1907800).sum := by decide
  have hdescent : baseEnd_1907800 < baseStart_1907800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1907800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1907817 : List Nat := [1, 2, 1, 1, 1, 6, 1, 5, 3]
def baseStart_1907817 : Nat := 118140960795 + 1907817 * 2 ^ 59
def prefixEnd_1907817 : Nat := 4983230072969 + 3 ^ 40 * 1907817 * 2
def baseEnd_1907817 : Nat := 435389831919496618183829

theorem tailTrace_1907817 : CollatzResearch.WordTrace tailWord_1907817 prefixEnd_1907817 435389831919496618183829 := by
  unfold tailWord_1907817
  simp only [CollatzResearch.WordTrace]
  refine ⟨69583802529312313048121705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46389201686208208698747803 69583802529312313048121705)
  ·
    refine ⟨52187851896984234786091279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69583802529312313048121705 52187851896984234786091279)
    ·
      refine ⟨78281777845476352179136919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52187851896984234786091279 78281777845476352179136919)
      ·
        refine ⟨117422666768214528268705379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78281777845476352179136919 117422666768214528268705379)
        ·
          refine ⟨176134000152321792403058069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117422666768214528268705379 176134000152321792403058069)
          ·
            refine ⟨8256281257140084018893347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 176134000152321792403058069 8256281257140084018893347)
            ·
              refine ⟨12384421885710126028340021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8256281257140084018893347 12384421885710126028340021)
              ·
                refine ⟨1161039551785324315156877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12384421885710126028340021 1161039551785324315156877)
                ·
                  refine ⟨435389831919496618183829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1161039551785324315156877 435389831919496618183829)
                  ·
                    rfl

theorem cell21_1907817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 5, 3].length) (baseStart_1907817 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1907817 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1907817 prefixEnd_1907817 := by exact prefixLift 1907817
  have htrace : WordTrace (prefixWord ++ tailWord_1907817) baseStart_1907817 baseEnd_1907817 := by
    simpa [prefixWord, tailWord_1907817, baseEnd_1907817] using wordTrace_append hprefix tailTrace_1907817
  have hstable : (prefixWord ++ tailWord_1907817).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1907817).length < 2 ^ (prefixWord ++ tailWord_1907817).sum := by decide
  have hdescent : baseEnd_1907817 < baseStart_1907817 := by decide
  rcases family_descends (prefixWord ++ tailWord_1907817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1907938 : List Nat := [3, 3, 4, 11]
def baseStart_1907938 : Nat := 118140960795 + 1907938 * 2 ^ 59
def prefixEnd_1907938 : Nat := 4983230072969 + 3 ^ 40 * 1907938 * 2
def baseEnd_1907938 : Nat := 1791841340609165829905

theorem tailTrace_1907938 : CollatzResearch.WordTrace tailWord_1907938 prefixEnd_1907938 1791841340609165829905 := by
  unfold tailWord_1907938
  simp only [CollatzResearch.WordTrace]
  refine ⟨17397053940468487678319117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46392143841249300475517645 17397053940468487678319117)
  ·
    refine ⟨6523895227675682879369669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17397053940468487678319117 6523895227675682879369669)
    ·
      refine ⟨1223230355189190539881813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6523895227675682879369669 1223230355189190539881813)
      ·
        refine ⟨1791841340609165829905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 11 1223230355189190539881813 1791841340609165829905)
        ·
          rfl

theorem cell21_1907938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 11].length) (baseStart_1907938 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1907938 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1907938 prefixEnd_1907938 := by exact prefixLift 1907938
  have htrace : WordTrace (prefixWord ++ tailWord_1907938) baseStart_1907938 baseEnd_1907938 := by
    simpa [prefixWord, tailWord_1907938, baseEnd_1907938] using wordTrace_append hprefix tailTrace_1907938
  have hstable : (prefixWord ++ tailWord_1907938).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1907938).length < 2 ^ (prefixWord ++ tailWord_1907938).sum := by decide
  have hdescent : baseEnd_1907938 < baseStart_1907938 := by decide
  rcases family_descends (prefixWord ++ tailWord_1907938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908028 : List Nat := [2, 2, 2, 2, 1, 3, 2, 2, 5]
def baseStart_1908028 : Nat := 118140960795 + 1908028 * 2 ^ 59
def prefixEnd_1908028 : Nat := 4983230072969 + 3 ^ 40 * 1908028 * 2
def baseEnd_1908028 : Nat := 435437984994207140166731

theorem tailTrace_1908028 : CollatzResearch.WordTrace tailWord_1908028 prefixEnd_1908028 435437984994207140166731 := by
  unfold tailWord_1908028
  simp only [CollatzResearch.WordTrace]
  refine ⟨34795749165773948042026369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46394332221031930722701825 34795749165773948042026369)
  ·
    refine ⟨26096811874330461031519777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34795749165773948042026369 26096811874330461031519777)
    ·
      refine ⟨19572608905747845773639833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26096811874330461031519777 19572608905747845773639833)
      ·
        refine ⟨14679456679310884330229875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19572608905747845773639833 14679456679310884330229875)
        ·
          refine ⟨22019185018966326495344813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14679456679310884330229875 22019185018966326495344813)
          ·
            refine ⟨8257194382112372435754305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22019185018966326495344813 8257194382112372435754305)
            ·
              refine ⟨6192895786584279326815729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8257194382112372435754305 6192895786584279326815729)
              ·
                refine ⟨4644671839938209495111797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6192895786584279326815729 4644671839938209495111797)
                ·
                  refine ⟨435437984994207140166731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4644671839938209495111797 435437984994207140166731)
                  ·
                    rfl

theorem cell21_1908028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 2, 5].length) (baseStart_1908028 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1908028 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1908028 prefixEnd_1908028 := by exact prefixLift 1908028
  have htrace : WordTrace (prefixWord ++ tailWord_1908028) baseStart_1908028 baseEnd_1908028 := by
    simpa [prefixWord, tailWord_1908028, baseEnd_1908028] using wordTrace_append hprefix tailTrace_1908028
  have hstable : (prefixWord ++ tailWord_1908028).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908028).length < 2 ^ (prefixWord ++ tailWord_1908028).sum := by decide
  have hdescent : baseEnd_1908028 < baseStart_1908028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908054 : List Nat := [5, 2, 3, 1, 1, 1, 3, 2, 3]
def baseStart_1908054 : Nat := 118140960795 + 1908054 * 2 ^ 59
def prefixEnd_1908054 : Nat := 4983230072969 + 3 ^ 40 * 1908054 * 2
def baseEnd_1908054 : Nat := 435443918548436872733345

theorem tailTrace_1908054 : CollatzResearch.WordTrace tailWord_1908054 prefixEnd_1908054 435443918548436872733345 := by
  unfold tailWord_1908054
  simp only [CollatzResearch.WordTrace]
  refine ⟨4349527914340856407781201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46394964419635801682999477 4349527914340856407781201)
  ·
    refine ⟨3262145935755642305835901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4349527914340856407781201 3262145935755642305835901)
    ·
      refine ⟨1223304725908365864688463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3262145935755642305835901 1223304725908365864688463)
      ·
        refine ⟨1834957088862548797032695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1223304725908365864688463 1834957088862548797032695)
        ·
          refine ⟨2752435633293823195549043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1834957088862548797032695 2752435633293823195549043)
          ·
            refine ⟨4128653449940734793323565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2752435633293823195549043 4128653449940734793323565)
            ·
              refine ⟨1548245043727775547496337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4128653449940734793323565 1548245043727775547496337)
              ·
                refine ⟨1161183782795831660622253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1548245043727775547496337 1161183782795831660622253)
                ·
                  refine ⟨435443918548436872733345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1161183782795831660622253 435443918548436872733345)
                  ·
                    rfl

theorem cell21_1908054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 3, 2, 3].length) (baseStart_1908054 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1908054 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1908054 prefixEnd_1908054 := by exact prefixLift 1908054
  have htrace : WordTrace (prefixWord ++ tailWord_1908054) baseStart_1908054 baseEnd_1908054 := by
    simpa [prefixWord, tailWord_1908054, baseEnd_1908054] using wordTrace_append hprefix tailTrace_1908054
  have hstable : (prefixWord ++ tailWord_1908054).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908054).length < 2 ^ (prefixWord ++ tailWord_1908054).sum := by decide
  have hdescent : baseEnd_1908054 < baseStart_1908054 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908076 : List Nat := [2, 2, 1, 1, 5, 1, 4, 1, 4]
def baseStart_1908076 : Nat := 118140960795 + 1908076 * 2 ^ 59
def prefixEnd_1908076 : Nat := 4983230072969 + 3 ^ 40 * 1908076 * 2
def baseEnd_1908076 : Nat := 435448939248169723366633

theorem tailTrace_1908076 : CollatzResearch.WordTrace tailWord_1908076 prefixEnd_1908076 435448939248169723366633 := by
  unfold tailWord_1908076
  simp only [CollatzResearch.WordTrace]
  refine ⟨34796624517687000140900041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46395499356916000187866721 34796624517687000140900041)
  ·
    refine ⟨26097468388265250105675031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34796624517687000140900041 26097468388265250105675031)
    ·
      refine ⟨39146202582397875158512547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26097468388265250105675031 39146202582397875158512547)
      ·
        refine ⟨58719303873596812737768821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39146202582397875158512547 58719303873596812737768821)
        ·
          refine ⟨5504934738149701194165827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58719303873596812737768821 5504934738149701194165827)
          ·
            refine ⟨8257402107224551791248741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5504934738149701194165827 8257402107224551791248741)
            ·
              refine ⟨1548262895104603460859139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8257402107224551791248741 1548262895104603460859139)
              ·
                refine ⟨2322394342656905191288709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1548262895104603460859139 2322394342656905191288709)
                ·
                  refine ⟨435448939248169723366633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2322394342656905191288709 435448939248169723366633)
                  ·
                    rfl

theorem cell21_1908076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 4].length) (baseStart_1908076 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1908076 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1908076 prefixEnd_1908076 := by exact prefixLift 1908076
  have htrace : WordTrace (prefixWord ++ tailWord_1908076) baseStart_1908076 baseEnd_1908076 := by
    simpa [prefixWord, tailWord_1908076, baseEnd_1908076] using wordTrace_append hprefix tailTrace_1908076
  have hstable : (prefixWord ++ tailWord_1908076).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908076).length < 2 ^ (prefixWord ++ tailWord_1908076).sum := by decide
  have hdescent : baseEnd_1908076 < baseStart_1908076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908087 : List Nat := [1, 1, 3, 1, 1, 2, 4, 1, 7]
def baseStart_1908087 : Nat := 118140960795 + 1908087 * 2 ^ 59
def prefixEnd_1908087 : Nat := 4983230072969 + 3 ^ 40 * 1908087 * 2
def baseEnd_1908087 : Nat := 435451449598036148683277

theorem tailTrace_1908087 : CollatzResearch.WordTrace tailWord_1908087 prefixEnd_1908087 435451449598036148683277 := by
  unfold tailWord_1908087
  simp only [CollatzResearch.WordTrace]
  refine ⟨69593650238334149160450515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46395766825556099440300343 69593650238334149160450515)
  ·
    refine ⟨104390475357501223740675773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69593650238334149160450515 104390475357501223740675773)
    ·
      refine ⟨39146428259062958902753415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104390475357501223740675773 39146428259062958902753415)
      ·
        refine ⟨58719642388594438354130123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39146428259062958902753415 58719642388594438354130123)
        ·
          refine ⟨88079463582891657531195185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58719642388594438354130123 88079463582891657531195185)
          ·
            refine ⟨66059597687168743148396389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88079463582891657531195185 66059597687168743148396389)
            ·
              refine ⟨12386174566344139340324323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66059597687168743148396389 12386174566344139340324323)
              ·
                refine ⟨18579261849516209010486485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12386174566344139340324323 18579261849516209010486485)
                ·
                  refine ⟨435451449598036148683277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18579261849516209010486485 435451449598036148683277)
                  ·
                    rfl

theorem cell21_1908087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 1, 7].length) (baseStart_1908087 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1908087 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1908087 prefixEnd_1908087 := by exact prefixLift 1908087
  have htrace : WordTrace (prefixWord ++ tailWord_1908087) baseStart_1908087 baseEnd_1908087 := by
    simpa [prefixWord, tailWord_1908087, baseEnd_1908087] using wordTrace_append hprefix tailTrace_1908087
  have hstable : (prefixWord ++ tailWord_1908087).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908087).length < 2 ^ (prefixWord ++ tailWord_1908087).sum := by decide
  have hdescent : baseEnd_1908087 < baseStart_1908087 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908121 : List Nat := [1, 2, 1, 2, 1, 6, 1, 4, 3]
def baseStart_1908121 : Nat := 118140960795 + 1908121 * 2 ^ 59
def prefixEnd_1908121 : Nat := 4983230072969 + 3 ^ 40 * 1908121 * 2
def baseEnd_1908121 : Nat := 435459208861259645116541

theorem tailTrace_1908121 : CollatzResearch.WordTrace tailWord_1908121 prefixEnd_1908121 435459208861259645116541 := by
  unfold tailWord_1908121
  simp only [CollatzResearch.WordTrace]
  refine ⟨69594890320210972967188217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46396593546807315311458811 69594890320210972967188217)
  ·
    refine ⟨52196167740158229725391163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69594890320210972967188217 52196167740158229725391163)
    ·
      refine ⟨78294251610237344588086745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52196167740158229725391163 78294251610237344588086745)
      ·
        refine ⟨58720688707678008441065059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78294251610237344588086745 58720688707678008441065059)
        ·
          refine ⟨88081033061517012661597589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58720688707678008441065059 88081033061517012661597589)
          ·
            refine ⟨4128798424758609968512387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 88081033061517012661597589 4128798424758609968512387)
            ·
              refine ⟨6193197637137914952768581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4128798424758609968512387 6193197637137914952768581)
              ·
                refine ⟨1161224556963359053644109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6193197637137914952768581 1161224556963359053644109)
                ·
                  refine ⟨435459208861259645116541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1161224556963359053644109 435459208861259645116541)
                  ·
                    rfl

theorem cell21_1908121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 4, 3].length) (baseStart_1908121 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1908121 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1908121 prefixEnd_1908121 := by exact prefixLift 1908121
  have htrace : WordTrace (prefixWord ++ tailWord_1908121) baseStart_1908121 baseEnd_1908121 := by
    simpa [prefixWord, tailWord_1908121, baseEnd_1908121] using wordTrace_append hprefix tailTrace_1908121
  have hstable : (prefixWord ++ tailWord_1908121).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908121).length < 2 ^ (prefixWord ++ tailWord_1908121).sum := by decide
  have hdescent : baseEnd_1908121 < baseStart_1908121 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908124 : List Nat := [2, 2, 3, 4, 2, 1, 1, 6]
def baseStart_1908124 : Nat := 118140960795 + 1908124 * 2 ^ 59
def prefixEnd_1908124 : Nat := 4983230072969 + 3 ^ 40 * 1908124 * 2
def baseEnd_1908124 : Nat := 145153297834044102188845

theorem tailTrace_1908124 : CollatzResearch.WordTrace tailWord_1908124 prefixEnd_1908124 145153297834044102188845 := by
  unfold tailWord_1908124
  simp only [CollatzResearch.WordTrace]
  refine ⟨34797499869600052239773713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46396666492800069653031617 34797499869600052239773713)
  ·
    refine ⟨26098124902200039179830285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34797499869600052239773713 26098124902200039179830285)
    ·
      refine ⟨9786796838325014692436357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26098124902200039179830285 9786796838325014692436357)
      ·
        refine ⟨1835024407185940254831817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9786796838325014692436357 1835024407185940254831817)
        ·
          refine ⟨1376268305389455191123863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1835024407185940254831817 1376268305389455191123863)
          ·
            refine ⟨2064402458084182786685795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1376268305389455191123863 2064402458084182786685795)
            ·
              refine ⟨3096603687126274180028693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2064402458084182786685795 3096603687126274180028693)
              ·
                refine ⟨145153297834044102188845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3096603687126274180028693 145153297834044102188845)
                ·
                  rfl

theorem cell21_1908124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 1, 6].length) (baseStart_1908124 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1908124 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1908124 prefixEnd_1908124 := by exact prefixLift 1908124
  have htrace : WordTrace (prefixWord ++ tailWord_1908124) baseStart_1908124 baseEnd_1908124 := by
    simpa [prefixWord, tailWord_1908124, baseEnd_1908124] using wordTrace_append hprefix tailTrace_1908124
  have hstable : (prefixWord ++ tailWord_1908124).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908124).length < 2 ^ (prefixWord ++ tailWord_1908124).sum := by decide
  have hdescent : baseEnd_1908124 < baseStart_1908124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908135 : List Nat := [1, 1, 6, 1, 1, 1, 1, 5, 4]
def baseStart_1908135 : Nat := 118140960795 + 1908135 * 2 ^ 59
def prefixEnd_1908135 : Nat := 4983230072969 + 3 ^ 40 * 1908135 * 2
def baseEnd_1908135 : Nat := 435462403851998731883179

theorem tailTrace_1908135 : CollatzResearch.WordTrace tailWord_1908135 prefixEnd_1908135 435462403851998731883179 := by
  unfold tailWord_1908135
  simp only [CollatzResearch.WordTrace]
  refine ⟨69595400942160253358197859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46396933961440168905465239 69595400942160253358197859)
  ·
    refine ⟨104393101413240380037296789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69595400942160253358197859 104393101413240380037296789)
    ·
      refine ⟨4893426628745642814248287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 104393101413240380037296789 4893426628745642814248287)
      ·
        refine ⟨7340139943118464221372431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4893426628745642814248287 7340139943118464221372431)
        ·
          refine ⟨11010209914677696332058647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7340139943118464221372431 11010209914677696332058647)
          ·
            refine ⟨16515314872016544498087971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11010209914677696332058647 16515314872016544498087971)
            ·
              refine ⟨24772972308024816747131957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16515314872016544498087971 24772972308024816747131957)
              ·
                refine ⟨2322466153877326570043621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24772972308024816747131957 2322466153877326570043621)
                ·
                  refine ⟨435462403851998731883179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2322466153877326570043621 435462403851998731883179)
                  ·
                    rfl

theorem cell21_1908135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 5, 4].length) (baseStart_1908135 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1908135 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1908135 prefixEnd_1908135 := by exact prefixLift 1908135
  have htrace : WordTrace (prefixWord ++ tailWord_1908135) baseStart_1908135 baseEnd_1908135 := by
    simpa [prefixWord, tailWord_1908135, baseEnd_1908135] using wordTrace_append hprefix tailTrace_1908135
  have hstable : (prefixWord ++ tailWord_1908135).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908135).length < 2 ^ (prefixWord ++ tailWord_1908135).sum := by decide
  have hdescent : baseEnd_1908135 < baseStart_1908135 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908214 : List Nat := [5, 1, 1, 1, 2, 2, 3, 3, 3]
def baseStart_1908214 : Nat := 118140960795 + 1908214 * 2 ^ 59
def prefixEnd_1908214 : Nat := 4983230072969 + 3 ^ 40 * 1908214 * 2
def baseEnd_1908214 : Nat := 435480432728312150066351

theorem tailTrace_1908214 : CollatzResearch.WordTrace tailWord_1908214 prefixEnd_1908214 435480432728312150066351 := by
  unfold tailWord_1908214
  simp only [CollatzResearch.WordTrace]
  refine ⟨4349892644304628115645231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46398854872582699900215797 4349892644304628115645231)
  ·
    refine ⟨6524838966456942173467847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4349892644304628115645231 6524838966456942173467847)
    ·
      refine ⟨9787258449685413260201771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6524838966456942173467847 9787258449685413260201771)
      ·
        refine ⟨14680887674528119890302657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9787258449685413260201771 14680887674528119890302657)
        ·
          refine ⟨11010665755896089917726993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14680887674528119890302657 11010665755896089917726993)
          ·
            refine ⟨8257999316922067438295245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11010665755896089917726993 8257999316922067438295245)
            ·
              refine ⟨3096749743845775289360717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8257999316922067438295245 3096749743845775289360717)
              ·
                refine ⟨1161281153942165733510269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3096749743845775289360717 1161281153942165733510269)
                ·
                  refine ⟨435480432728312150066351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1161281153942165733510269 435480432728312150066351)
                  ·
                    rfl

theorem cell21_1908214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 3, 3, 3].length) (baseStart_1908214 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1908214 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1908214 prefixEnd_1908214 := by exact prefixLift 1908214
  have htrace : WordTrace (prefixWord ++ tailWord_1908214) baseStart_1908214 baseEnd_1908214 := by
    simpa [prefixWord, tailWord_1908214, baseEnd_1908214] using wordTrace_append hprefix tailTrace_1908214
  have hstable : (prefixWord ++ tailWord_1908214).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908214).length < 2 ^ (prefixWord ++ tailWord_1908214).sum := by decide
  have hdescent : baseEnd_1908214 < baseStart_1908214 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908284 : List Nat := [2, 2, 2, 2, 13]
def baseStart_1908284 : Nat := 118140960795 + 1908284 * 2 ^ 59
def prefixEnd_1908284 : Nat := 4983230072969 + 3 ^ 40 * 1908284 * 2
def baseEnd_1908284 : Nat := 5376498860271698566661

theorem tailTrace_1908284 : CollatzResearch.WordTrace tailWord_1908284 prefixEnd_1908284 5376498860271698566661 := by
  unfold tailWord_1908284
  simp only [CollatzResearch.WordTrace]
  refine ⟨34800417709310225902685953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46400556945746967870247937 34800417709310225902685953)
  ·
    refine ⟨26100313281982669427014465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34800417709310225902685953 26100313281982669427014465)
    ·
      refine ⟨19575234961487002070260849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26100313281982669427014465 19575234961487002070260849)
      ·
        refine ⟨14681426221115251552695637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19575234961487002070260849 14681426221115251552695637)
        ·
          refine ⟨5376498860271698566661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 14681426221115251552695637 5376498860271698566661)
          ·
            rfl

theorem cell21_1908284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 13].length) (baseStart_1908284 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1908284 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1908284 prefixEnd_1908284 := by exact prefixLift 1908284
  have htrace : WordTrace (prefixWord ++ tailWord_1908284) baseStart_1908284 baseEnd_1908284 := by
    simpa [prefixWord, tailWord_1908284, baseEnd_1908284] using wordTrace_append hprefix tailTrace_1908284
  have hstable : (prefixWord ++ tailWord_1908284).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908284).length < 2 ^ (prefixWord ++ tailWord_1908284).sum := by decide
  have hdescent : baseEnd_1908284 < baseStart_1908284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908287 : List Nat := [1, 1, 2, 2, 3, 4, 2, 2, 4]
def baseStart_1908287 : Nat := 118140960795 + 1908287 * 2 ^ 59
def prefixEnd_1908287 : Nat := 4983230072969 + 3 ^ 40 * 1908287 * 2
def baseEnd_1908287 : Nat := 435497092322880245349535

theorem tailTrace_1908287 : CollatzResearch.WordTrace tailWord_1908287 prefixEnd_1908287 435497092322880245349535 := by
  unfold tailWord_1908287
  simp only [CollatzResearch.WordTrace]
  refine ⟨69600944837609583317731115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46400629891739722211820743 69600944837609583317731115)
  ·
    refine ⟨104401417256414374976596673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69600944837609583317731115 104401417256414374976596673)
    ·
      refine ⟨78301062942310781232447505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104401417256414374976596673 78301062942310781232447505)
      ·
        refine ⟨58725797206733085924335629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78301062942310781232447505 58725797206733085924335629)
        ·
          refine ⟨22022173952524907221625861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58725797206733085924335629 22022173952524907221625861)
          ·
            refine ⟨4129157616098420104054849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22022173952524907221625861 4129157616098420104054849)
            ·
              refine ⟨3096868212073815078041137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4129157616098420104054849 3096868212073815078041137)
              ·
                refine ⟨2322651159055361308530853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3096868212073815078041137 2322651159055361308530853)
                ·
                  refine ⟨435497092322880245349535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2322651159055361308530853 435497092322880245349535)
                  ·
                    rfl

theorem cell21_1908287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 2, 2, 4].length) (baseStart_1908287 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1908287 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1908287 prefixEnd_1908287 := by exact prefixLift 1908287
  have htrace : WordTrace (prefixWord ++ tailWord_1908287) baseStart_1908287 baseEnd_1908287 := by
    simpa [prefixWord, tailWord_1908287, baseEnd_1908287] using wordTrace_append hprefix tailTrace_1908287
  have hstable : (prefixWord ++ tailWord_1908287).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908287).length < 2 ^ (prefixWord ++ tailWord_1908287).sum := by decide
  have hdescent : baseEnd_1908287 < baseStart_1908287 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908346 : List Nat := [3, 1, 1, 1, 1, 1, 1, 8, 4]
def baseStart_1908346 : Nat := 118140960795 + 1908346 * 2 ^ 59
def prefixEnd_1908346 : Nat := 4983230072969 + 3 ^ 40 * 1908346 * 2
def baseEnd_1908346 : Nat := 435510556926709253866081

theorem tailTrace_1908346 : CollatzResearch.WordTrace tailWord_1908346 prefixEnd_1908346 435510556926709253866081 := by
  unfold tailWord_1908346
  simp only [CollatzResearch.WordTrace]
  refine ⟨17400774186098959098532223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46402064496263890929419261 17400774186098959098532223)
  ·
    refine ⟨26101161279148438647798335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17400774186098959098532223 26101161279148438647798335)
    ·
      refine ⟨39151741918722657971697503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26101161279148438647798335 39151741918722657971697503)
      ·
        refine ⟨58727612878083986957546255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39151741918722657971697503 58727612878083986957546255)
        ·
          refine ⟨88091419317125980436319383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58727612878083986957546255 88091419317125980436319383)
          ·
            refine ⟨132137128975688970654479075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88091419317125980436319383 132137128975688970654479075)
            ·
              refine ⟨198205693463533455981718613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132137128975688970654479075 198205693463533455981718613)
              ·
                refine ⟨2322722970275782687285765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 198205693463533455981718613 2322722970275782687285765)
                ·
                  refine ⟨435510556926709253866081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2322722970275782687285765 435510556926709253866081)
                  ·
                    rfl

theorem cell21_1908346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 8, 4].length) (baseStart_1908346 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1908346 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1908346 prefixEnd_1908346 := by exact prefixLift 1908346
  have htrace : WordTrace (prefixWord ++ tailWord_1908346) baseStart_1908346 baseEnd_1908346 := by
    simpa [prefixWord, tailWord_1908346, baseEnd_1908346] using wordTrace_append hprefix tailTrace_1908346
  have hstable : (prefixWord ++ tailWord_1908346).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908346).length < 2 ^ (prefixWord ++ tailWord_1908346).sum := by decide
  have hdescent : baseEnd_1908346 < baseStart_1908346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908349 : List Nat := [1, 4, 1, 1, 4, 1, 2, 4, 3]
def baseStart_1908349 : Nat := 118140960795 + 1908349 * 2 ^ 59
def prefixEnd_1908349 : Nat := 4983230072969 + 3 ^ 40 * 1908349 * 2
def baseEnd_1908349 : Nat := 435511241567581915316075

theorem tailTrace_1908349 : CollatzResearch.WordTrace tailWord_1908349 prefixEnd_1908349 435511241567581915316075 := by
  unfold tailWord_1908349
  simp only [CollatzResearch.WordTrace]
  refine ⟨69603206163384967906488101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46402137442256645270992067 69603206163384967906488101)
  ·
    refine ⟨13050601155634681482466519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69603206163384967906488101 13050601155634681482466519)
    ·
      refine ⟨19575901733452022223699779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13050601155634681482466519 19575901733452022223699779)
      ·
        refine ⟨29363852600178033335549669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19575901733452022223699779 29363852600178033335549669)
        ·
          refine ⟨5505722362533381250415563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29363852600178033335549669 5505722362533381250415563)
          ·
            refine ⟨8258583543800071875623345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5505722362533381250415563 8258583543800071875623345)
            ·
              refine ⟨6193937657850053906717509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8258583543800071875623345 6193937657850053906717509)
              ·
                refine ⟨1161363310846885107509533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6193937657850053906717509 1161363310846885107509533)
                ·
                  refine ⟨435511241567581915316075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1161363310846885107509533 435511241567581915316075)
                  ·
                    rfl

theorem cell21_1908349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 4, 3].length) (baseStart_1908349 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1908349 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1908349 prefixEnd_1908349 := by exact prefixLift 1908349
  have htrace : WordTrace (prefixWord ++ tailWord_1908349) baseStart_1908349 baseEnd_1908349 := by
    simpa [prefixWord, tailWord_1908349, baseEnd_1908349] using wordTrace_append hprefix tailTrace_1908349
  have hstable : (prefixWord ++ tailWord_1908349).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908349).length < 2 ^ (prefixWord ++ tailWord_1908349).sum := by decide
  have hdescent : baseEnd_1908349 < baseStart_1908349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908363 : List Nat := [1, 1, 1, 1, 4, 1, 7, 1, 4]
def baseStart_1908363 : Nat := 118140960795 + 1908363 * 2 ^ 59
def prefixEnd_1908363 : Nat := 4983230072969 + 3 ^ 40 * 1908363 * 2
def baseEnd_1908363 : Nat := 435514436558321002082713

theorem tailTrace_1908363 : CollatzResearch.WordTrace tailWord_1908363 prefixEnd_1908363 435514436558321002082713 := by
  unfold tailWord_1908363
  simp only [CollatzResearch.WordTrace]
  refine ⟨69603716785334248297497743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46402477856889498864998495 69603716785334248297497743)
  ·
    refine ⟨104405575178001372446246615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69603716785334248297497743 104405575178001372446246615)
    ·
      refine ⟨156608362767002058669369923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104405575178001372446246615 156608362767002058669369923)
      ·
        refine ⟨234912544150503088004054885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156608362767002058669369923 234912544150503088004054885)
        ·
          refine ⟨44046102028219329000760291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 234912544150503088004054885 44046102028219329000760291)
          ·
            refine ⟨66069153042328993501140437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44046102028219329000760291 66069153042328993501140437)
            ·
              refine ⟨1548495774429585785182979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 66069153042328993501140437 1548495774429585785182979)
              ·
                refine ⟨2322743661644378677774469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1548495774429585785182979 2322743661644378677774469)
                ·
                  refine ⟨435514436558321002082713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2322743661644378677774469 435514436558321002082713)
                  ·
                    rfl

theorem cell21_1908363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 7, 1, 4].length) (baseStart_1908363 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1908363 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1908363 prefixEnd_1908363 := by exact prefixLift 1908363
  have htrace : WordTrace (prefixWord ++ tailWord_1908363) baseStart_1908363 baseEnd_1908363 := by
    simpa [prefixWord, tailWord_1908363, baseEnd_1908363] using wordTrace_append hprefix tailTrace_1908363
  have hstable : (prefixWord ++ tailWord_1908363).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908363).length < 2 ^ (prefixWord ++ tailWord_1908363).sum := by decide
  have hdescent : baseEnd_1908363 < baseStart_1908363 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908383 : List Nat := [1, 1, 2, 7, 1, 2, 1, 3, 3]
def baseStart_1908383 : Nat := 118140960795 + 1908383 * 2 ^ 59
def prefixEnd_1908383 : Nat := 4983230072969 + 3 ^ 40 * 1908383 * 2
def baseEnd_1908383 : Nat := 435519000830805411749339

theorem tailTrace_1908383 : CollatzResearch.WordTrace tailWord_1908383 prefixEnd_1908383 435519000830805411749339 := by
  unfold tailWord_1908383
  simp only [CollatzResearch.WordTrace]
  refine ⟨69604446245261791713225803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46402964163507861142150535 69604446245261791713225803)
  ·
    refine ⟨104406669367892687569838705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69604446245261791713225803 104406669367892687569838705)
    ·
      refine ⟨78305002025919515677379029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104406669367892687569838705 78305002025919515677379029)
      ·
        refine ⟨1835273484982488648688571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 78305002025919515677379029 1835273484982488648688571)
        ·
          refine ⟨2752910227473732973032857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1835273484982488648688571 2752910227473732973032857)
          ·
            refine ⟨2064682670605299729774643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2752910227473732973032857 2064682670605299729774643)
            ·
              refine ⟨3097024005907949594661965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2064682670605299729774643 3097024005907949594661965)
              ·
                refine ⟨1161384002215481097998237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3097024005907949594661965 1161384002215481097998237)
                ·
                  refine ⟨435519000830805411749339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1161384002215481097998237 435519000830805411749339)
                  ·
                    rfl

theorem cell21_1908383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 1, 3, 3].length) (baseStart_1908383 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1908383 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1908383 prefixEnd_1908383 := by exact prefixLift 1908383
  have htrace : WordTrace (prefixWord ++ tailWord_1908383) baseStart_1908383 baseEnd_1908383 := by
    simpa [prefixWord, tailWord_1908383, baseEnd_1908383] using wordTrace_append hprefix tailTrace_1908383
  have hstable : (prefixWord ++ tailWord_1908383).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908383).length < 2 ^ (prefixWord ++ tailWord_1908383).sum := by decide
  have hdescent : baseEnd_1908383 < baseStart_1908383 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908408 : List Nat := [2, 1, 2, 1, 2, 1, 1, 8, 3]
def baseStart_1908408 : Nat := 118140960795 + 1908408 * 2 ^ 59
def prefixEnd_1908408 : Nat := 4983230072969 + 3 ^ 40 * 1908408 * 2
def baseEnd_1908408 : Nat := 435524706171410923832621

theorem tailTrace_1908408 : CollatzResearch.WordTrace tailWord_1908408 prefixEnd_1908408 435524706171410923832621 := by
  unfold tailWord_1908408
  simp only [CollatzResearch.WordTrace]
  refine ⟨34802679035085610491442939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46403572046780813988590585 34802679035085610491442939)
  ·
    refine ⟨52204018552628415737164409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34802679035085610491442939 52204018552628415737164409)
    ·
      refine ⟨39153013914471311802873307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52204018552628415737164409 39153013914471311802873307)
      ·
        refine ⟨58729520871706967704309961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39153013914471311802873307 58729520871706967704309961)
        ·
          refine ⟨44047140653780225778232471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58729520871706967704309961 44047140653780225778232471)
          ·
            refine ⟨66070710980670338667348707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44047140653780225778232471 66070710980670338667348707)
            ·
              refine ⟨99106066471005508001023061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66070710980670338667348707 99106066471005508001023061)
              ·
                refine ⟨1161399216457095796886989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 99106066471005508001023061 1161399216457095796886989)
                ·
                  refine ⟨435524706171410923832621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1161399216457095796886989 435524706171410923832621)
                  ·
                    rfl

theorem cell21_1908408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 8, 3].length) (baseStart_1908408 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1908408 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1908408 prefixEnd_1908408 := by exact prefixLift 1908408
  have htrace : WordTrace (prefixWord ++ tailWord_1908408) baseStart_1908408 baseEnd_1908408 := by
    simpa [prefixWord, tailWord_1908408, baseEnd_1908408] using wordTrace_append hprefix tailTrace_1908408
  have hstable : (prefixWord ++ tailWord_1908408).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908408).length < 2 ^ (prefixWord ++ tailWord_1908408).sum := by decide
  have hdescent : baseEnd_1908408 < baseStart_1908408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908470 : List Nat := [5, 1, 1, 1, 1, 5, 1, 6]
def baseStart_1908470 : Nat := 118140960795 + 1908470 * 2 ^ 59
def prefixEnd_1908470 : Nat := 4983230072969 + 3 ^ 40 * 1908470 * 2
def baseEnd_1908470 : Nat := 145179618472037531266387

theorem tailTrace_1908470 : CollatzResearch.WordTrace tailWord_1908470 prefixEnd_1908470 145179618472037531266387 := by
  unfold tailWord_1908470
  simp only [CollatzResearch.WordTrace]
  refine ⟨4350476212246662848227679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46405079597297737047761909 4350476212246662848227679)
  ·
    refine ⟨6525714318369994272341519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4350476212246662848227679 6525714318369994272341519)
    ·
      refine ⟨9788571477554991408512279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6525714318369994272341519 9788571477554991408512279)
      ·
        refine ⟨14682857216332487112768419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9788571477554991408512279 14682857216332487112768419)
        ·
          refine ⟨22024285824498730669152629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14682857216332487112768419 22024285824498730669152629)
          ·
            refine ⟨2064776796046756000233059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22024285824498730669152629 2064776796046756000233059)
            ·
              refine ⟨3097165194070134000349589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2064776796046756000233059 3097165194070134000349589)
              ·
                refine ⟨145179618472037531266387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3097165194070134000349589 145179618472037531266387)
                ·
                  rfl

theorem cell21_1908470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 1, 6].length) (baseStart_1908470 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1908470 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1908470 prefixEnd_1908470 := by exact prefixLift 1908470
  have htrace : WordTrace (prefixWord ++ tailWord_1908470) baseStart_1908470 baseEnd_1908470 := by
    simpa [prefixWord, tailWord_1908470, baseEnd_1908470] using wordTrace_append hprefix tailTrace_1908470
  have hstable : (prefixWord ++ tailWord_1908470).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908470).length < 2 ^ (prefixWord ++ tailWord_1908470).sum := by decide
  have hdescent : baseEnd_1908470 < baseStart_1908470 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908484 : List Nat := [2, 3, 2, 2, 1, 3, 1, 2, 5]
def baseStart_1908484 : Nat := 118140960795 + 1908484 * 2 ^ 59
def prefixEnd_1908484 : Nat := 4983230072969 + 3 ^ 40 * 1908484 * 2
def baseEnd_1908484 : Nat := 435542050406851680565799

theorem tailTrace_1908484 : CollatzResearch.WordTrace tailWord_1908484 prefixEnd_1908484 435542050406851680565799 := by
  unfold tailWord_1908484
  simp only [CollatzResearch.WordTrace]
  refine ⟨34804065008947942981326253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46405420011930590641768337 34804065008947942981326253)
  ·
    refine ⟨13051524378355478617997345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34804065008947942981326253 13051524378355478617997345)
    ·
      refine ⟨9788643283766608963498009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13051524378355478617997345 9788643283766608963498009)
      ·
        refine ⟨7341482462824956722623507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9788643283766608963498009 7341482462824956722623507)
        ·
          refine ⟨11012223694237435083935261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7341482462824956722623507 11012223694237435083935261)
          ·
            refine ⟨4129583885339038156475723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11012223694237435083935261 4129583885339038156475723)
            ·
              refine ⟨6194375828008557234713585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4129583885339038156475723 6194375828008557234713585)
              ·
                refine ⟨4645781871006417926035189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6194375828008557234713585 4645781871006417926035189)
                ·
                  refine ⟨435542050406851680565799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4645781871006417926035189 435542050406851680565799)
                  ·
                    rfl

theorem cell21_1908484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 2, 5].length) (baseStart_1908484 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1908484 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1908484 prefixEnd_1908484 := by exact prefixLift 1908484
  have htrace : WordTrace (prefixWord ++ tailWord_1908484) baseStart_1908484 baseEnd_1908484 := by
    simpa [prefixWord, tailWord_1908484, baseEnd_1908484] using wordTrace_append hprefix tailTrace_1908484
  have hstable : (prefixWord ++ tailWord_1908484).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908484).length < 2 ^ (prefixWord ++ tailWord_1908484).sum := by decide
  have hdescent : baseEnd_1908484 < baseStart_1908484 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908493 : List Nat := [1, 7, 2, 1, 1, 1, 2, 3, 3]
def baseStart_1908493 : Nat := 118140960795 + 1908493 * 2 ^ 59
def prefixEnd_1908493 : Nat := 4983230072969 + 3 ^ 40 * 1908493 * 2
def baseEnd_1908493 : Nat := 435544104329469664915781

theorem tailTrace_1908493 : CollatzResearch.WordTrace tailWord_1908493 prefixEnd_1908493 435544104329469664915781 := by
  unfold tailWord_1908493
  simp only [CollatzResearch.WordTrace]
  refine ⟨69608458274863280499730133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46405638849908853666486755 69608458274863280499730133)
  ·
    refine ⟨1631448240817108136712425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 69608458274863280499730133 1631448240817108136712425)
    ·
      refine ⟨1223586180612831102534319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1631448240817108136712425 1223586180612831102534319)
      ·
        refine ⟨1835379270919246653801479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1223586180612831102534319 1835379270919246653801479)
        ·
          refine ⟨2753068906378869980702219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1835379270919246653801479 2753068906378869980702219)
          ·
            refine ⟨4129603359568304971053329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2753068906378869980702219 4129603359568304971053329)
            ·
              refine ⟨3097202519676228728289997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4129603359568304971053329 3097202519676228728289997)
              ·
                refine ⟨1161450944878585773108749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3097202519676228728289997 1161450944878585773108749)
                ·
                  refine ⟨435544104329469664915781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1161450944878585773108749 435544104329469664915781)
                  ·
                    rfl

theorem cell21_1908493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_1908493 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1908493 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1908493 prefixEnd_1908493 := by exact prefixLift 1908493
  have htrace : WordTrace (prefixWord ++ tailWord_1908493) baseStart_1908493 baseEnd_1908493 := by
    simpa [prefixWord, tailWord_1908493, baseEnd_1908493] using wordTrace_append hprefix tailTrace_1908493
  have hstable : (prefixWord ++ tailWord_1908493).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908493).length < 2 ^ (prefixWord ++ tailWord_1908493).sum := by decide
  have hdescent : baseEnd_1908493 < baseStart_1908493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908501 : List Nat := [1, 3, 2, 1, 2, 4, 2, 3, 3]
def baseStart_1908501 : Nat := 118140960795 + 1908501 * 2 ^ 59
def prefixEnd_1908501 : Nat := 4983230072969 + 3 ^ 40 * 1908501 * 2
def baseEnd_1908501 : Nat := 435545930038463428782431

theorem tailTrace_1908501 : CollatzResearch.WordTrace tailWord_1908501 prefixEnd_1908501 435545930038463428782431 := by
  unfold tailWord_1908501
  simp only [CollatzResearch.WordTrace]
  refine ⟨69608750058834297866021357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46405833372556198577347571 69608750058834297866021357)
  ·
    refine ⟨26103281272062861699758009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69608750058834297866021357 26103281272062861699758009)
    ·
      refine ⟨19577460954047146274818507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26103281272062861699758009 19577460954047146274818507)
      ·
        refine ⟨29366191431070719412227761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19577460954047146274818507 29366191431070719412227761)
        ·
          refine ⟨22024643573303039559170821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29366191431070719412227761 22024643573303039559170821)
          ·
            refine ⟨4129620669994319917344529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22024643573303039559170821 4129620669994319917344529)
            ·
              refine ⟨3097215502495739938008397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4129620669994319917344529 3097215502495739938008397)
              ·
                refine ⟨1161455813435902476753149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3097215502495739938008397 1161455813435902476753149)
                ·
                  refine ⟨435545930038463428782431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1161455813435902476753149 435545930038463428782431)
                  ·
                    rfl

theorem cell21_1908501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 2, 3, 3].length) (baseStart_1908501 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1908501 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1908501 prefixEnd_1908501 := by exact prefixLift 1908501
  have htrace : WordTrace (prefixWord ++ tailWord_1908501) baseStart_1908501 baseEnd_1908501 := by
    simpa [prefixWord, tailWord_1908501, baseEnd_1908501] using wordTrace_append hprefix tailTrace_1908501
  have hstable : (prefixWord ++ tailWord_1908501).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908501).length < 2 ^ (prefixWord ++ tailWord_1908501).sum := by decide
  have hdescent : baseEnd_1908501 < baseStart_1908501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908512 : List Nat := [2, 1, 1, 5, 1, 1, 10]
def baseStart_1908512 : Nat := 118140960795 + 1908512 * 2 ^ 59
def prefixEnd_1908512 : Nat := 4983230072969 + 3 ^ 40 * 1908512 * 2
def baseEnd_1908512 : Nat := 48394271154258872677675

theorem tailTrace_1908512 : CollatzResearch.WordTrace tailWord_1908512 prefixEnd_1908512 48394271154258872677675 := by
  unfold tailWord_1908512
  simp only [CollatzResearch.WordTrace]
  refine ⟨34804575630897223372335895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46406100841196297829781193 34804575630897223372335895)
  ·
    refine ⟨52206863446345835058503843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34804575630897223372335895 52206863446345835058503843)
    ·
      refine ⟨78310295169518752587755765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52206863446345835058503843 78310295169518752587755765)
      ·
        refine ⟨7341590172142383055102103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 78310295169518752587755765 7341590172142383055102103)
        ·
          refine ⟨11012385258213574582653155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7341590172142383055102103 11012385258213574582653155)
          ·
            refine ⟨16518577887320361873979733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11012385258213574582653155 16518577887320361873979733)
            ·
              refine ⟨48394271154258872677675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16518577887320361873979733 48394271154258872677675)
              ·
                rfl

theorem cell21_1908512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 10].length) (baseStart_1908512 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1908512 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1908512 prefixEnd_1908512 := by exact prefixLift 1908512
  have htrace : WordTrace (prefixWord ++ tailWord_1908512) baseStart_1908512 baseEnd_1908512 := by
    simpa [prefixWord, tailWord_1908512, baseEnd_1908512] using wordTrace_append hprefix tailTrace_1908512
  have hstable : (prefixWord ++ tailWord_1908512).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908512).length < 2 ^ (prefixWord ++ tailWord_1908512).sum := by decide
  have hdescent : baseEnd_1908512 < baseStart_1908512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908577 : List Nat := [1, 2, 3, 1, 1, 1, 7, 2, 3]
def baseStart_1908577 : Nat := 118140960795 + 1908577 * 2 ^ 59
def prefixEnd_1908577 : Nat := 4983230072969 + 3 ^ 40 * 1908577 * 2
def baseEnd_1908577 : Nat := 435563274273904185515609

theorem tailTrace_1908577 : CollatzResearch.WordTrace tailWord_1908577 prefixEnd_1908577 435563274273904185515609 := by
  unfold tailWord_1908577
  simp only [CollatzResearch.WordTrace]
  refine ⟨69611522006558962845787985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46407681337705975230525323 69611522006558962845787985)
  ·
    refine ⟨52208641504919222134340989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69611522006558962845787985 52208641504919222134340989)
    ·
      refine ⟨19578240564344708300377871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52208641504919222134340989 19578240564344708300377871)
      ·
        refine ⟨29367360846517062450566807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19578240564344708300377871 29367360846517062450566807)
        ·
          refine ⟨44051041269775593675850211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29367360846517062450566807 44051041269775593675850211)
          ·
            refine ⟨66076561904663390513775317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44051041269775593675850211 66076561904663390513775317)
            ·
              refine ⟨1548669419640548215166609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 66076561904663390513775317 1548669419640548215166609)
              ·
                refine ⟨1161502064730411161374957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1548669419640548215166609 1161502064730411161374957)
                ·
                  refine ⟨435563274273904185515609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1161502064730411161374957 435563274273904185515609)
                  ·
                    rfl

theorem cell21_1908577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 7, 2, 3].length) (baseStart_1908577 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1908577 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1908577 prefixEnd_1908577 := by exact prefixLift 1908577
  have htrace : WordTrace (prefixWord ++ tailWord_1908577) baseStart_1908577 baseEnd_1908577 := by
    simpa [prefixWord, tailWord_1908577, baseEnd_1908577] using wordTrace_append hprefix tailTrace_1908577
  have hstable : (prefixWord ++ tailWord_1908577).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908577).length < 2 ^ (prefixWord ++ tailWord_1908577).sum := by decide
  have hdescent : baseEnd_1908577 < baseStart_1908577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908588 : List Nat := [2, 2, 1, 1, 4, 2, 1, 8]
def baseStart_1908588 : Nat := 118140960795 + 1908588 * 2 ^ 59
def prefixEnd_1908588 : Nat := 4983230072969 + 3 ^ 40 * 1908588 * 2
def baseEnd_1908588 : Nat := 145188594874590203610751

theorem tailTrace_1908588 : CollatzResearch.WordTrace tailWord_1908588 prefixEnd_1908588 145188594874590203610751 := by
  unfold tailWord_1908588
  simp only [CollatzResearch.WordTrace]
  refine ⟨34805961604759555862219209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46407948806346074482958945 34805961604759555862219209)
  ·
    refine ⟨26104471203569666896664407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34805961604759555862219209 26104471203569666896664407)
    ·
      refine ⟨39156706805354500344996611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26104471203569666896664407 39156706805354500344996611)
      ·
        refine ⟨58735060208031750517494917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39156706805354500344996611 58735060208031750517494917)
        ·
          refine ⟨11012823789005953222030297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58735060208031750517494917 11012823789005953222030297)
          ·
            refine ⟨8259617841754464916522723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11012823789005953222030297 8259617841754464916522723)
            ·
              refine ⟨12389426762631697374784085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8259617841754464916522723 12389426762631697374784085)
              ·
                refine ⟨145188594874590203610751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12389426762631697374784085 145188594874590203610751)
                ·
                  rfl

theorem cell21_1908588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 8].length) (baseStart_1908588 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1908588 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1908588 prefixEnd_1908588 := by exact prefixLift 1908588
  have htrace : WordTrace (prefixWord ++ tailWord_1908588) baseStart_1908588 baseEnd_1908588 := by
    simpa [prefixWord, tailWord_1908588, baseEnd_1908588] using wordTrace_append hprefix tailTrace_1908588
  have hstable : (prefixWord ++ tailWord_1908588).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908588).length < 2 ^ (prefixWord ++ tailWord_1908588).sum := by decide
  have hdescent : baseEnd_1908588 < baseStart_1908588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908622 : List Nat := [4, 1, 1, 5, 2, 8]
def baseStart_1908622 : Nat := 118140960795 + 1908622 * 2 ^ 59
def prefixEnd_1908622 : Nat := 4983230072969 + 3 ^ 40 * 1908622 * 2
def baseEnd_1908622 : Nat := 16132353477296078046871

theorem tailTrace_1908622 : CollatzResearch.WordTrace tailWord_1908622 prefixEnd_1908622 16132353477296078046871 := by
  unfold tailWord_1908622
  simp only [CollatzResearch.WordTrace]
  refine ⟨8701645411424491941397015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46408775527597290354117413 8701645411424491941397015)
  ·
    refine ⟨13052468117136737912095523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8701645411424491941397015 13052468117136737912095523)
    ·
      refine ⟨19578702175705106868143285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13052468117136737912095523 19578702175705106868143285)
      ·
        refine ⟨1835503328972353768888433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19578702175705106868143285 1835503328972353768888433)
        ·
          refine ⟨1376627496729265326666325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1835503328972353768888433 1376627496729265326666325)
          ·
            refine ⟨16132353477296078046871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1376627496729265326666325 16132353477296078046871)
            ·
              rfl

theorem cell21_1908622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 8].length) (baseStart_1908622 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1908622 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1908622 prefixEnd_1908622 := by exact prefixLift 1908622
  have htrace : WordTrace (prefixWord ++ tailWord_1908622) baseStart_1908622 baseEnd_1908622 := by
    simpa [prefixWord, tailWord_1908622, baseEnd_1908622] using wordTrace_append hprefix tailTrace_1908622
  have hstable : (prefixWord ++ tailWord_1908622).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908622).length < 2 ^ (prefixWord ++ tailWord_1908622).sum := by decide
  have hdescent : baseEnd_1908622 < baseStart_1908622 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908633 : List Nat := [1, 2, 1, 2, 1, 3, 2, 3, 6]
def baseStart_1908633 : Nat := 118140960795 + 1908633 * 2 ^ 59
def prefixEnd_1908633 : Nat := 4983230072969 + 3 ^ 40 * 1908633 * 2
def baseEnd_1908633 : Nat := 435576054236860532582161

theorem tailTrace_1908633 : CollatzResearch.WordTrace tailWord_1908633 prefixEnd_1908633 435576054236860532582161 := by
  unfold tailWord_1908633
  simp only [CollatzResearch.WordTrace]
  refine ⟨69613564494356084409826553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46409042996237389606551035 69613564494356084409826553)
  ·
    refine ⟨52210173370767063307369915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69613564494356084409826553 52210173370767063307369915)
    ·
      refine ⟨78315260056150594961054873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52210173370767063307369915 78315260056150594961054873)
      ·
        refine ⟨58736445042112946220791155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78315260056150594961054873 58736445042112946220791155)
        ·
          refine ⟨88104667563169419331186733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58736445042112946220791155 88104667563169419331186733)
          ·
            refine ⟨33039250336188532249195025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88104667563169419331186733 33039250336188532249195025)
            ·
              refine ⟨24779437752141399186896269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33039250336188532249195025 24779437752141399186896269)
              ·
                refine ⟨9292289157053024695086101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24779437752141399186896269 9292289157053024695086101)
                ·
                  refine ⟨435576054236860532582161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9292289157053024695086101 435576054236860532582161)
                  ·
                    rfl

theorem cell21_1908633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 3, 6].length) (baseStart_1908633 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1908633 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1908633 prefixEnd_1908633 := by exact prefixLift 1908633
  have htrace : WordTrace (prefixWord ++ tailWord_1908633) baseStart_1908633 baseEnd_1908633 := by
    simpa [prefixWord, tailWord_1908633, baseEnd_1908633] using wordTrace_append hprefix tailTrace_1908633
  have hstable : (prefixWord ++ tailWord_1908633).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908633).length < 2 ^ (prefixWord ++ tailWord_1908633).sum := by decide
  have hdescent : baseEnd_1908633 < baseStart_1908633 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908695 : List Nat := [1, 1, 3, 2, 1, 1, 6, 1, 5]
def baseStart_1908695 : Nat := 118140960795 + 1908695 * 2 ^ 59
def prefixEnd_1908695 : Nat := 4983230072969 + 3 ^ 40 * 1908695 * 2
def baseEnd_1908695 : Nat := 435590203481562202548701

theorem tailTrace_1908695 : CollatzResearch.WordTrace tailWord_1908695 prefixEnd_1908695 435590203481562202548701 := by
  unfold tailWord_1908695
  simp only [CollatzResearch.WordTrace]
  refine ⟨69615825820131468998583539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46410550546754312665722359 69615825820131468998583539)
  ·
    refine ⟨104423738730197203497875309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69615825820131468998583539 104423738730197203497875309)
    ·
      refine ⟨39158902023823951311703241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104423738730197203497875309 39158902023823951311703241)
      ·
        refine ⟨29369176517867963483777431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39158902023823951311703241 29369176517867963483777431)
        ·
          refine ⟨44053764776801945225666147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29369176517867963483777431 44053764776801945225666147)
          ·
            refine ⟨66080647165202917838499221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44053764776801945225666147 66080647165202917838499221)
            ·
              refine ⟨3097530335868886773679651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 66080647165202917838499221 3097530335868886773679651)
              ·
                refine ⟨4646295503803330160519477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3097530335868886773679651 4646295503803330160519477)
                ·
                  refine ⟨435590203481562202548701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4646295503803330160519477 435590203481562202548701)
                  ·
                    rfl

theorem cell21_1908695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 6, 1, 5].length) (baseStart_1908695 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1908695 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1908695 prefixEnd_1908695 := by exact prefixLift 1908695
  have htrace : WordTrace (prefixWord ++ tailWord_1908695) baseStart_1908695 baseEnd_1908695 := by
    simpa [prefixWord, tailWord_1908695, baseEnd_1908695] using wordTrace_append hprefix tailTrace_1908695
  have hstable : (prefixWord ++ tailWord_1908695).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908695).length < 2 ^ (prefixWord ++ tailWord_1908695).sum := by decide
  have hdescent : baseEnd_1908695 < baseStart_1908695 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908729 : List Nat := [1, 2, 1, 3, 1, 6, 1, 3, 3]
def baseStart_1908729 : Nat := 118140960795 + 1908729 * 2 ^ 59
def prefixEnd_1908729 : Nat := 4983230072969 + 3 ^ 40 * 1908729 * 2
def baseEnd_1908729 : Nat := 435597962744785698981965

theorem tailTrace_1908729 : CollatzResearch.WordTrace tailWord_1908729 prefixEnd_1908729 435597962744785698981965 := by
  unfold tailWord_1908729
  simp only [CollatzResearch.WordTrace]
  refine ⟨69617065902008292805321241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46411377268005528536880827 69617065902008292805321241)
  ·
    refine ⟨52212799426506219603990931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69617065902008292805321241 52212799426506219603990931)
    ·
      refine ⟨78319199139759329405986397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52212799426506219603990931 78319199139759329405986397)
      ·
        refine ⟨29369699677409748527244899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78319199139759329405986397 29369699677409748527244899)
        ·
          refine ⟨44054549516114622790867349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29369699677409748527244899 44054549516114622790867349)
          ·
            refine ⟨2065057008567872943321907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 44054549516114622790867349 2065057008567872943321907)
            ·
              refine ⟨3097585512851809414982861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2065057008567872943321907 3097585512851809414982861)
              ·
                refine ⟨1161594567319428530618573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3097585512851809414982861 1161594567319428530618573)
                ·
                  refine ⟨435597962744785698981965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1161594567319428530618573 435597962744785698981965)
                  ·
                    rfl

theorem cell21_1908729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 1, 3, 3].length) (baseStart_1908729 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1908729 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1908729 prefixEnd_1908729 := by exact prefixLift 1908729
  have htrace : WordTrace (prefixWord ++ tailWord_1908729) baseStart_1908729 baseEnd_1908729 := by
    simpa [prefixWord, tailWord_1908729, baseEnd_1908729] using wordTrace_append hprefix tailTrace_1908729
  have hstable : (prefixWord ++ tailWord_1908729).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908729).length < 2 ^ (prefixWord ++ tailWord_1908729).sum := by decide
  have hdescent : baseEnd_1908729 < baseStart_1908729 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908746 : List Nat := [3, 1, 2, 2, 4, 1, 3, 2, 3]
def baseStart_1908746 : Nat := 118140960795 + 1908746 * 2 ^ 59
def prefixEnd_1908746 : Nat := 4983230072969 + 3 ^ 40 * 1908746 * 2
def baseEnd_1908746 : Nat := 435601842376397447198597

theorem tailTrace_1908746 : CollatzResearch.WordTrace tailWord_1908746 prefixEnd_1908746 435601842376397447198597 := by
  unfold tailWord_1908746
  simp only [CollatzResearch.WordTrace]
  refine ⟨17404421485736676177172523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46411790628631136472460061 17404421485736676177172523)
  ·
    refine ⟨26106632228605014265758785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17404421485736676177172523 26106632228605014265758785)
    ·
      refine ⟨19579974171453760699319089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26106632228605014265758785 19579974171453760699319089)
      ·
        refine ⟨14684980628590320524489317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19579974171453760699319089 14684980628590320524489317)
        ·
          refine ⟨2753433867860685098341747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14684980628590320524489317 2753433867860685098341747)
          ·
            refine ⟨4130150801791027647512621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2753433867860685098341747 4130150801791027647512621)
            ·
              refine ⟨1548806550671635367817233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4130150801791027647512621 1548806550671635367817233)
              ·
                refine ⟨1161604913003726525862925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1548806550671635367817233 1161604913003726525862925)
                ·
                  refine ⟨435601842376397447198597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1161604913003726525862925 435601842376397447198597)
                  ·
                    rfl

theorem cell21_1908746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 3, 2, 3].length) (baseStart_1908746 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1908746 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1908746 prefixEnd_1908746 := by exact prefixLift 1908746
  have htrace : WordTrace (prefixWord ++ tailWord_1908746) baseStart_1908746 baseEnd_1908746 := by
    simpa [prefixWord, tailWord_1908746, baseEnd_1908746] using wordTrace_append hprefix tailTrace_1908746
  have hstable : (prefixWord ++ tailWord_1908746).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908746).length < 2 ^ (prefixWord ++ tailWord_1908746).sum := by decide
  have hdescent : baseEnd_1908746 < baseStart_1908746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908757 : List Nat := [1, 3, 2, 1, 5, 1, 2, 6]
def baseStart_1908757 : Nat := 118140960795 + 1908757 * 2 ^ 59
def prefixEnd_1908757 : Nat := 4983230072969 + 3 ^ 40 * 1908757 * 2
def baseEnd_1908757 : Nat := 145201450908754624171747

theorem tailTrace_1908757 : CollatzResearch.WordTrace tailWord_1908757 prefixEnd_1908757 145201450908754624171747 := by
  unfold tailWord_1908757
  simp only [CollatzResearch.WordTrace]
  refine ⟨69618087145906853587340525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46412058097271235724893683 69618087145906853587340525)
  ·
    refine ⟨26106782679715070095252697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69618087145906853587340525 26106782679715070095252697)
    ·
      refine ⟨19580087009786302571439523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26106782679715070095252697 19580087009786302571439523)
      ·
        refine ⟨29370130514679453857159285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19580087009786302571439523 29370130514679453857159285)
        ·
          refine ⟨2753449735751198799108683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29370130514679453857159285 2753449735751198799108683)
          ·
            refine ⟨4130174603626798198663025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2753449735751198799108683 4130174603626798198663025)
            ·
              refine ⟨3097630952720098648997269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4130174603626798198663025 3097630952720098648997269)
              ·
                refine ⟨145201450908754624171747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3097630952720098648997269 145201450908754624171747)
                ·
                  rfl

theorem cell21_1908757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 2, 6].length) (baseStart_1908757 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1908757 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1908757 prefixEnd_1908757 := by exact prefixLift 1908757
  have htrace : WordTrace (prefixWord ++ tailWord_1908757) baseStart_1908757 baseEnd_1908757 := by
    simpa [prefixWord, tailWord_1908757, baseEnd_1908757] using wordTrace_append hprefix tailTrace_1908757
  have hstable : (prefixWord ++ tailWord_1908757).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908757).length < 2 ^ (prefixWord ++ tailWord_1908757).sum := by decide
  have hdescent : baseEnd_1908757 < baseStart_1908757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908884 : List Nat := [2, 4, 2, 3, 2, 1, 2, 5]
def baseStart_1908884 : Nat := 118140960795 + 1908884 * 2 ^ 59
def prefixEnd_1908884 : Nat := 4983230072969 + 3 ^ 40 * 1908884 * 2
def baseEnd_1908884 : Nat := 145211111952179957966105

theorem tailTrace_1908884 : CollatzResearch.WordTrace tailWord_1908884 prefixEnd_1908884 145211111952179957966105 := by
  unfold tailWord_1908884
  simp only [CollatzResearch.WordTrace]
  refine ⟨34811359608223377138606853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46415146144297836184809137 34811359608223377138606853)
  ·
    refine ⟨6527129926541883213488785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34811359608223377138606853 6527129926541883213488785)
    ·
      refine ⟨4895347444906412410116589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6527129926541883213488785 4895347444906412410116589)
      ·
        refine ⟨1835755291839904653793721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4895347444906412410116589 1835755291839904653793721)
        ·
          refine ⟨1376816468879928490345291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1835755291839904653793721 1376816468879928490345291)
          ·
            refine ⟨2065224703319892735517937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1376816468879928490345291 2065224703319892735517937)
            ·
              refine ⟨1548918527489919551638453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2065224703319892735517937 1548918527489919551638453)
              ·
                refine ⟨145211111952179957966105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1548918527489919551638453 145211111952179957966105)
                ·
                  rfl

theorem cell21_1908884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 2, 5].length) (baseStart_1908884 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1908884 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1908884 prefixEnd_1908884 := by exact prefixLift 1908884
  have htrace : WordTrace (prefixWord ++ tailWord_1908884) baseStart_1908884 baseEnd_1908884 := by
    simpa [prefixWord, tailWord_1908884, baseEnd_1908884] using wordTrace_append hprefix tailTrace_1908884
  have hstable : (prefixWord ++ tailWord_1908884).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908884).length < 2 ^ (prefixWord ++ tailWord_1908884).sum := by decide
  have hdescent : baseEnd_1908884 < baseStart_1908884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908892 : List Nat := [2, 2, 3, 2, 1, 1, 3, 7]
def baseStart_1908892 : Nat := 118140960795 + 1908892 * 2 ^ 59
def prefixEnd_1908892 : Nat := 4983230072969 + 3 ^ 40 * 1908892 * 2
def baseEnd_1908892 : Nat := 145211720521844545921655

theorem tailTrace_1908892 : CollatzResearch.WordTrace tailWord_1908892 prefixEnd_1908892 145211720521844545921655 := by
  unfold tailWord_1908892
  simp only [CollatzResearch.WordTrace]
  refine ⟨34811505500208885821752465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46415340666945181095669953 34811505500208885821752465)
  ·
    refine ⟨26108629125156664366314349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34811505500208885821752465 26108629125156664366314349)
    ·
      refine ⟨9790735921933749137367881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26108629125156664366314349 9790735921933749137367881)
      ·
        refine ⟨7343051941450311853025911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9790735921933749137367881 7343051941450311853025911)
        ·
          refine ⟨11014577912175467779538867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7343051941450311853025911 11014577912175467779538867)
          ·
            refine ⟨16521866868263201669308301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11014577912175467779538867 16521866868263201669308301)
            ·
              refine ⟨6195700075598700625990613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16521866868263201669308301 6195700075598700625990613)
              ·
                refine ⟨145211720521844545921655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6195700075598700625990613 145211720521844545921655)
                ·
                  rfl

theorem cell21_1908892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 7].length) (baseStart_1908892 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1908892 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1908892 prefixEnd_1908892 := by exact prefixLift 1908892
  have htrace : WordTrace (prefixWord ++ tailWord_1908892) baseStart_1908892 baseEnd_1908892 := by
    simpa [prefixWord, tailWord_1908892, baseEnd_1908892] using wordTrace_append hprefix tailTrace_1908892
  have hstable : (prefixWord ++ tailWord_1908892).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908892).length < 2 ^ (prefixWord ++ tailWord_1908892).sum := by decide
  have hdescent : baseEnd_1908892 < baseStart_1908892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908898 : List Nat := [3, 3, 1, 3, 1, 3, 1, 3, 3]
def baseStart_1908898 : Nat := 118140960795 + 1908898 * 2 ^ 59
def prefixEnd_1908898 : Nat := 4983230072969 + 3 ^ 40 * 1908898 * 2
def baseEnd_1908898 : Nat := 435636530847278960664953

theorem tailTrace_1908898 : CollatzResearch.WordTrace tailWord_1908898 prefixEnd_1908898 435636530847278960664953 := by
  unfold tailWord_1908898
  simp only [CollatzResearch.WordTrace]
  refine ⟨17405807459599008667055837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46415486558930689778815565 17405807459599008667055837)
  ·
    refine ⟨6527177797349628250145939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17405807459599008667055837 6527177797349628250145939)
    ·
      refine ⟨9790766696024442375218909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6527177797349628250145939 9790766696024442375218909)
      ·
        refine ⟨3671537511009165890707091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9790766696024442375218909 3671537511009165890707091)
        ·
          refine ⟨5507306266513748836060637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3671537511009165890707091 5507306266513748836060637)
          ·
            refine ⟨2065239849942655813522739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5507306266513748836060637 2065239849942655813522739)
            ·
              refine ⟨3097859774913983720284109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2065239849942655813522739 3097859774913983720284109)
              ·
                refine ⟨1161697415592743895106541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3097859774913983720284109 1161697415592743895106541)
                ·
                  refine ⟨435636530847278960664953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1161697415592743895106541 435636530847278960664953)
                  ·
                    rfl

theorem cell21_1908898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 1, 3, 3].length) (baseStart_1908898 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1908898 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1908898 prefixEnd_1908898 := by exact prefixLift 1908898
  have htrace : WordTrace (prefixWord ++ tailWord_1908898) baseStart_1908898 baseEnd_1908898 := by
    simpa [prefixWord, tailWord_1908898, baseEnd_1908898] using wordTrace_append hprefix tailTrace_1908898
  have hstable : (prefixWord ++ tailWord_1908898).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908898).length < 2 ^ (prefixWord ++ tailWord_1908898).sum := by decide
  have hdescent : baseEnd_1908898 < baseStart_1908898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908909 : List Nat := [1, 5, 2, 1, 2, 3, 7]
def baseStart_1908909 : Nat := 118140960795 + 1908909 * 2 ^ 59
def prefixEnd_1908909 : Nat := 4983230072969 + 3 ^ 40 * 1908909 * 2
def baseEnd_1908909 : Nat := 48404337910793931775733

theorem tailTrace_1908909 : CollatzResearch.WordTrace tailWord_1908909 prefixEnd_1908909 48404337910793931775733 := by
  unfold tailWord_1908909
  simp only [CollatzResearch.WordTrace]
  refine ⟨69623631041356183546873781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46415754027570789031249187 69623631041356183546873781)
  ·
    refine ⟨6527215410127142207519417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 69623631041356183546873781 6527215410127142207519417)
    ·
      refine ⟨4895411557595356655639563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6527215410127142207519417 4895411557595356655639563)
      ·
        refine ⟨7343117336393034983459345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4895411557595356655639563 7343117336393034983459345)
        ·
          refine ⟨5507338002294776237594509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7343117336393034983459345 5507338002294776237594509)
          ·
            refine ⟨2065251750860541089097941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5507338002294776237594509 2065251750860541089097941)
            ·
              refine ⟨48404337910793931775733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2065251750860541089097941 48404337910793931775733)
              ·
                rfl

theorem cell21_1908909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 7].length) (baseStart_1908909 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1908909 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1908909 prefixEnd_1908909 := by exact prefixLift 1908909
  have htrace : WordTrace (prefixWord ++ tailWord_1908909) baseStart_1908909 baseEnd_1908909 := by
    simpa [prefixWord, tailWord_1908909, baseEnd_1908909] using wordTrace_append hprefix tailTrace_1908909
  have hstable : (prefixWord ++ tailWord_1908909).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908909).length < 2 ^ (prefixWord ++ tailWord_1908909).sum := by decide
  have hdescent : baseEnd_1908909 < baseStart_1908909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908929 : List Nat := [1, 2, 6, 1, 2, 2, 2, 1, 4]
def baseStart_1908929 : Nat := 118140960795 + 1908929 * 2 ^ 59
def prefixEnd_1908929 : Nat := 4983230072969 + 3 ^ 40 * 1908929 * 2
def baseEnd_1908929 : Nat := 435643605469629795648223

theorem tailTrace_1908929 : CollatzResearch.WordTrace tailWord_1908929 prefixEnd_1908929 435643605469629795648223 := by
  unfold tailWord_1908929
  simp only [CollatzResearch.WordTrace]
  refine ⟨69624360501283726962601841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46416240334189151308401227 69624360501283726962601841)
  ·
    refine ⟨52218270375962795221951381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69624360501283726962601841 52218270375962795221951381)
    ·
      refine ⟨2447731423873256026028971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 52218270375962795221951381 2447731423873256026028971)
      ·
        refine ⟨3671597135809884039043457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2447731423873256026028971 3671597135809884039043457)
        ·
          refine ⟨2753697851857413029282593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3671597135809884039043457 2753697851857413029282593)
          ·
            refine ⟨2065273388893059771961945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2753697851857413029282593 2065273388893059771961945)
            ·
              refine ⟨1548955041669794828971459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2065273388893059771961945 1548955041669794828971459)
              ·
                refine ⟨2323432562504692243457189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1548955041669794828971459 2323432562504692243457189)
                ·
                  refine ⟨435643605469629795648223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2323432562504692243457189 435643605469629795648223)
                  ·
                    rfl

theorem cell21_1908929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 2, 1, 4].length) (baseStart_1908929 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1908929 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1908929 prefixEnd_1908929 := by exact prefixLift 1908929
  have htrace : WordTrace (prefixWord ++ tailWord_1908929) baseStart_1908929 baseEnd_1908929 := by
    simpa [prefixWord, tailWord_1908929, baseEnd_1908929] using wordTrace_append hprefix tailTrace_1908929
  have hstable : (prefixWord ++ tailWord_1908929).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908929).length < 2 ^ (prefixWord ++ tailWord_1908929).sum := by decide
  have hdescent : baseEnd_1908929 < baseStart_1908929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909016 : List Nat := [2, 1, 2, 3, 1, 2, 4, 3, 3]
def baseStart_1909016 : Nat := 118140960795 + 1909016 * 2 ^ 59
def prefixEnd_1909016 : Nat := 4983230072969 + 3 ^ 40 * 1909016 * 2
def baseEnd_1909016 : Nat := 435663460054936977698045

theorem tailTrace_1909016 : CollatzResearch.WordTrace tailWord_1909016 prefixEnd_1909016 435663460054936977698045 := by
  unfold tailWord_1909016
  simp only [CollatzResearch.WordTrace]
  refine ⟨34813766825984270410509451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46418355767979027214012601 34813766825984270410509451)
  ·
    refine ⟨52220650238976405615764177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34813766825984270410509451 52220650238976405615764177)
    ·
      refine ⟨39165487679232304211823133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52220650238976405615764177 39165487679232304211823133)
      ·
        refine ⟨14687057879712114079433675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39165487679232304211823133 14687057879712114079433675)
        ·
          refine ⟨22030586819568171119150513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14687057879712114079433675 22030586819568171119150513)
          ·
            refine ⟨16522940114676128339362885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22030586819568171119150513 16522940114676128339362885)
            ·
              refine ⟨3098051271501774063630541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16522940114676128339362885 3098051271501774063630541)
              ·
                refine ⟨1161769226813165273861453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3098051271501774063630541 1161769226813165273861453)
                ·
                  refine ⟨435663460054936977698045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1161769226813165273861453 435663460054936977698045)
                  ·
                    rfl

theorem cell21_1909016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4, 3, 3].length) (baseStart_1909016 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1909016 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1909016 prefixEnd_1909016 := by exact prefixLift 1909016
  have htrace : WordTrace (prefixWord ++ tailWord_1909016) baseStart_1909016 baseEnd_1909016 := by
    simpa [prefixWord, tailWord_1909016, baseEnd_1909016] using wordTrace_append hprefix tailTrace_1909016
  have hstable : (prefixWord ++ tailWord_1909016).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909016).length < 2 ^ (prefixWord ++ tailWord_1909016).sum := by decide
  have hdescent : baseEnd_1909016 < baseStart_1909016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909027 : List Nat := [1, 1, 1, 4, 2, 2, 10]
def baseStart_1909027 : Nat := 118140960795 + 1909027 * 2 ^ 59
def prefixEnd_1909027 : Nat := 4983230072969 + 3 ^ 40 * 1909027 * 2
def baseEnd_1909027 : Nat := 48407330044978155890521

theorem tailTrace_1909027 : CollatzResearch.WordTrace tailWord_1909027 prefixEnd_1909027 48407330044978155890521 := by
  unfold tailWord_1909027
  simp only [CollatzResearch.WordTrace]
  refine ⟨69627934854928689699669335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46418623236619126466446223 69627934854928689699669335)
  ·
    refine ⟨104441902282393034549504003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69627934854928689699669335 104441902282393034549504003)
    ·
      refine ⟨156662853423589551824256005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104441902282393034549504003 156662853423589551824256005)
      ·
        refine ⟨29374285016923040967048001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 156662853423589551824256005 29374285016923040967048001)
        ·
          refine ⟨22030713762692280725286001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29374285016923040967048001 22030713762692280725286001)
          ·
            refine ⟨16523035322019210543964501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22030713762692280725286001 16523035322019210543964501)
            ·
              refine ⟨48407330044978155890521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16523035322019210543964501 48407330044978155890521)
              ·
                rfl

theorem cell21_1909027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 10].length) (baseStart_1909027 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1909027 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1909027 prefixEnd_1909027 := by exact prefixLift 1909027
  have htrace : WordTrace (prefixWord ++ tailWord_1909027) baseStart_1909027 baseEnd_1909027 := by
    simpa [prefixWord, tailWord_1909027, baseEnd_1909027] using wordTrace_append hprefix tailTrace_1909027
  have hstable : (prefixWord ++ tailWord_1909027).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909027).length < 2 ^ (prefixWord ++ tailWord_1909027).sum := by decide
  have hdescent : baseEnd_1909027 < baseStart_1909027 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909075 : List Nat := [1, 1, 1, 2, 1, 1, 4, 7, 3]
def baseStart_1909075 : Nat := 118140960795 + 1909075 * 2 ^ 59
def prefixEnd_1909075 : Nat := 4983230072969 + 3 ^ 40 * 1909075 * 2
def baseEnd_1909075 : Nat := 435676924658765986214591

theorem tailTrace_1909075 : CollatzResearch.WordTrace tailWord_1909075 prefixEnd_1909075 435676924658765986214591 := by
  unfold tailWord_1909075
  simp only [CollatzResearch.WordTrace]
  refine ⟨69629685558754793897416679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46419790372503195931611119 69629685558754793897416679)
  ·
    refine ⟨104444528338132190846125019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69629685558754793897416679 104444528338132190846125019)
    ·
      refine ⟨156666792507198286269187529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104444528338132190846125019 156666792507198286269187529)
      ·
        refine ⟨117500094380398714701890647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156666792507198286269187529 117500094380398714701890647)
        ·
          refine ⟨176250141570598072052835971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117500094380398714701890647 176250141570598072052835971)
          ·
            refine ⟨264375212355897108079253957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176250141570598072052835971 264375212355897108079253957)
            ·
              refine ⟨49570352316730707764860117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 264375212355897108079253957 49570352316730707764860117)
              ·
                refine ⟨1161805132423375963238909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 49570352316730707764860117 1161805132423375963238909)
                ·
                  refine ⟨435676924658765986214591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1161805132423375963238909 435676924658765986214591)
                  ·
                    rfl

theorem cell21_1909075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 7, 3].length) (baseStart_1909075 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1909075 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1909075 prefixEnd_1909075 := by exact prefixLift 1909075
  have htrace : WordTrace (prefixWord ++ tailWord_1909075) baseStart_1909075 baseEnd_1909075 := by
    simpa [prefixWord, tailWord_1909075, baseEnd_1909075] using wordTrace_append hprefix tailTrace_1909075
  have hstable : (prefixWord ++ tailWord_1909075).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909075).length < 2 ^ (prefixWord ++ tailWord_1909075).sum := by decide
  have hdescent : baseEnd_1909075 < baseStart_1909075 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909106 : List Nat := [3, 2, 1, 2, 1, 4, 1, 3, 4]
def baseStart_1909106 : Nat := 118140960795 + 1909106 * 2 ^ 59
def prefixEnd_1909106 : Nat := 4983230072969 + 3 ^ 40 * 1909106 * 2
def baseEnd_1909106 : Nat := 435683999281116821197861

theorem tailTrace_1909106 : CollatzResearch.WordTrace tailWord_1909106 prefixEnd_1909106 435683999281116821197861 := by
  unfold tailWord_1909106
  simp only [CollatzResearch.WordTrace]
  refine ⟨17407704055410621547948793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46420544147761657461196781 17407704055410621547948793)
  ·
    refine ⟨13055778041557966160961595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17407704055410621547948793 13055778041557966160961595)
    ·
      refine ⟨19583667062336949241442393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13055778041557966160961595 19583667062336949241442393)
      ·
        refine ⟨14687750296752711931081795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19583667062336949241442393 14687750296752711931081795)
        ·
          refine ⟨22031625445129067896622693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14687750296752711931081795 22031625445129067896622693)
          ·
            refine ⟨4130929770961700230616755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22031625445129067896622693 4130929770961700230616755)
            ·
              refine ⟨6196394656442550345925133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4130929770961700230616755 6196394656442550345925133)
              ·
                refine ⟨2323647996165956379721925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6196394656442550345925133 2323647996165956379721925)
                ·
                  refine ⟨435683999281116821197861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2323647996165956379721925 435683999281116821197861)
                  ·
                    rfl

theorem cell21_1909106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 3, 4].length) (baseStart_1909106 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1909106 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1909106 prefixEnd_1909106 := by exact prefixLift 1909106
  have htrace : WordTrace (prefixWord ++ tailWord_1909106) baseStart_1909106 baseEnd_1909106 := by
    simpa [prefixWord, tailWord_1909106, baseEnd_1909106] using wordTrace_append hprefix tailTrace_1909106
  have hstable : (prefixWord ++ tailWord_1909106).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909106).length < 2 ^ (prefixWord ++ tailWord_1909106).sum := by decide
  have hdescent : baseEnd_1909106 < baseStart_1909106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909196 : List Nat := [2, 2, 1, 4, 3, 1, 8]
def baseStart_1909196 : Nat := 118140960795 + 1909196 * 2 ^ 59
def prefixEnd_1909196 : Nat := 4983230072969 + 3 ^ 40 * 1909196 * 2
def baseEnd_1909196 : Nat := 48411615389699629410853

theorem tailTrace_1909196 : CollatzResearch.WordTrace tailWord_1909196 prefixEnd_1909196 48411615389699629410853 := by
  unfold tailWord_1909196
  simp only [CollatzResearch.WordTrace]
  refine ⟨34817049395658215781285721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46422732527544287708380961 34817049395658215781285721)
  ·
    refine ⟨26112787046743661835964291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34817049395658215781285721 26112787046743661835964291)
    ·
      refine ⟨39169180570115492753946437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26112787046743661835964291 39169180570115492753946437)
      ·
        refine ⟨7344221356896654891364957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39169180570115492753946437 7344221356896654891364957)
        ·
          refine ⟨2754083008836245584261859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7344221356896654891364957 2754083008836245584261859)
          ·
            refine ⟨4131124513254368376392789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2754083008836245584261859 4131124513254368376392789)
            ·
              refine ⟨48411615389699629410853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4131124513254368376392789 48411615389699629410853)
              ·
                rfl

theorem cell21_1909196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 8].length) (baseStart_1909196 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1909196 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1909196 prefixEnd_1909196 := by exact prefixLift 1909196
  have htrace : WordTrace (prefixWord ++ tailWord_1909196) baseStart_1909196 baseEnd_1909196 := by
    simpa [prefixWord, tailWord_1909196, baseEnd_1909196] using wordTrace_append hprefix tailTrace_1909196
  have hstable : (prefixWord ++ tailWord_1909196).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909196).length < 2 ^ (prefixWord ++ tailWord_1909196).sum := by decide
  have hdescent : baseEnd_1909196 < baseStart_1909196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909261 : List Nat := [1, 7, 1, 1, 1, 1, 3, 1, 5]
def baseStart_1909261 : Nat := 118140960795 + 1909261 * 2 ^ 59
def prefixEnd_1909261 : Nat := 4983230072969 + 3 ^ 40 * 1909261 * 2
def baseEnd_1909261 : Nat := 435719372392870996114211

theorem tailTrace_1909261 : CollatzResearch.WordTrace tailWord_1909261 prefixEnd_1909261 435719372392870996114211 := by
  unfold tailWord_1909261
  simp only [CollatzResearch.WordTrace]
  refine ⟨69636469536080947663687637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46424313024053965109125091 69636469536080947663687637)
  ·
    refine ⟨1632104754751897210867679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 69636469536080947663687637 1632104754751897210867679)
    ·
      refine ⟨2448157132127845816301519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1632104754751897210867679 2448157132127845816301519)
      ·
        refine ⟨3672235698191768724452279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2448157132127845816301519 3672235698191768724452279)
        ·
          refine ⟨5508353547287653086678419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3672235698191768724452279 5508353547287653086678419)
          ·
            refine ⟨8262530320931479630017629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5508353547287653086678419 8262530320931479630017629)
            ·
              refine ⟨3098448870349304861256611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8262530320931479630017629 3098448870349304861256611)
              ·
                refine ⟨4647673305523957291884917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3098448870349304861256611 4647673305523957291884917)
                ·
                  refine ⟨435719372392870996114211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4647673305523957291884917 435719372392870996114211)
                  ·
                    rfl

theorem cell21_1909261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_1909261 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1909261 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1909261 prefixEnd_1909261 := by exact prefixLift 1909261
  have htrace : WordTrace (prefixWord ++ tailWord_1909261) baseStart_1909261 baseEnd_1909261 := by
    simpa [prefixWord, tailWord_1909261, baseEnd_1909261] using wordTrace_append hprefix tailTrace_1909261
  have hstable : (prefixWord ++ tailWord_1909261).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909261).length < 2 ^ (prefixWord ++ tailWord_1909261).sum := by decide
  have hdescent : baseEnd_1909261 < baseStart_1909261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909272 : List Nat := [2, 1, 2, 3, 3, 2, 2, 6]
def baseStart_1909272 : Nat := 118140960795 + 1909272 * 2 ^ 59
def prefixEnd_1909272 : Nat := 4983230072969 + 3 ^ 40 * 1909272 * 2
def baseEnd_1909272 : Nat := 145240627580912473810285

theorem tailTrace_1909272 : CollatzResearch.WordTrace tailWord_1909272 prefixEnd_1909272 145240627580912473810285 := by
  unfold tailWord_1909272
  simp only [CollatzResearch.WordTrace]
  refine ⟨34818435369520548271169035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46424580492694064361558713 34818435369520548271169035)
  ·
    refine ⟨52227653054280822406753553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34818435369520548271169035 52227653054280822406753553)
    ·
      refine ⟨39170739790710616805065165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52227653054280822406753553 39170739790710616805065165)
      ·
        refine ⟨14689027421516481301899437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39170739790710616805065165 14689027421516481301899437)
        ·
          refine ⟨5508385283068680488212289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14689027421516481301899437 5508385283068680488212289)
          ·
            refine ⟨4131288962301510366159217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5508385283068680488212289 4131288962301510366159217)
            ·
              refine ⟨3098466721726132774619413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4131288962301510366159217 3098466721726132774619413)
              ·
                refine ⟨145240627580912473810285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3098466721726132774619413 145240627580912473810285)
                ·
                  rfl

theorem cell21_1909272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 2, 6].length) (baseStart_1909272 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1909272 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1909272 prefixEnd_1909272 := by exact prefixLift 1909272
  have htrace : WordTrace (prefixWord ++ tailWord_1909272) baseStart_1909272 baseEnd_1909272 := by
    simpa [prefixWord, tailWord_1909272, baseEnd_1909272] using wordTrace_append hprefix tailTrace_1909272
  have hstable : (prefixWord ++ tailWord_1909272).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909272).length < 2 ^ (prefixWord ++ tailWord_1909272).sum := by decide
  have hdescent : baseEnd_1909272 < baseStart_1909272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909303 : List Nat := [1, 1, 3, 1, 2, 3, 2, 5, 3]
def baseStart_1909303 : Nat := 118140960795 + 1909303 * 2 ^ 59
def prefixEnd_1909303 : Nat := 4983230072969 + 3 ^ 40 * 1909303 * 2
def baseEnd_1909303 : Nat := 435728957365088256414125

theorem tailTrace_1909303 : CollatzResearch.WordTrace tailWord_1909303 prefixEnd_1909303 435728957365088256414125 := by
  unfold tailWord_1909303
  simp only [CollatzResearch.WordTrace]
  refine ⟨69638001401928788836716563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46425334267952525891144375 69638001401928788836716563)
  ·
    refine ⟨104457002102893183255074845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69638001401928788836716563 104457002102893183255074845)
    ·
      refine ⟨39171375788584943720653067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104457002102893183255074845 39171375788584943720653067)
      ·
        refine ⟨58757063682877415580979601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39171375788584943720653067 58757063682877415580979601)
        ·
          refine ⟨44067797762158061685734701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58757063682877415580979601 44067797762158061685734701)
          ·
            refine ⟨16525424160809273132150513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44067797762158061685734701 16525424160809273132150513)
            ·
              refine ⟨12394068120606954849112885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16525424160809273132150513 12394068120606954849112885)
              ·
                refine ⟨1161943886306902017104333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12394068120606954849112885 1161943886306902017104333)
                ·
                  refine ⟨435728957365088256414125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1161943886306902017104333 435728957365088256414125)
                  ·
                    rfl

theorem cell21_1909303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 5, 3].length) (baseStart_1909303 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1909303 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1909303 prefixEnd_1909303 := by exact prefixLift 1909303
  have htrace : WordTrace (prefixWord ++ tailWord_1909303) baseStart_1909303 baseEnd_1909303 := by
    simpa [prefixWord, tailWord_1909303, baseEnd_1909303] using wordTrace_append hprefix tailTrace_1909303
  have hstable : (prefixWord ++ tailWord_1909303).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909303).length < 2 ^ (prefixWord ++ tailWord_1909303).sum := by decide
  have hdescent : baseEnd_1909303 < baseStart_1909303 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909317 : List Nat := [1, 3, 1, 1, 1, 5, 1, 4, 4]
def baseStart_1909317 : Nat := 118140960795 + 1909317 * 2 ^ 59
def prefixEnd_1909317 : Nat := 4983230072969 + 3 ^ 40 * 1909317 * 2
def baseEnd_1909317 : Nat := 435732152355827343180763

theorem tailTrace_1909317 : CollatzResearch.WordTrace tailWord_1909317 prefixEnd_1909317 435732152355827343180763 := by
  unfold tailWord_1909317
  simp only [CollatzResearch.WordTrace]
  refine ⟨69638512023878069227726205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46425674682585379485150803 69638512023878069227726205)
  ·
    refine ⟨26114442008954275960397327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69638512023878069227726205 26114442008954275960397327)
    ·
      refine ⟨39171663013431413940595991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26114442008954275960397327 39171663013431413940595991)
      ·
        refine ⟨58757494520147120910893987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39171663013431413940595991 58757494520147120910893987)
        ·
          refine ⟨88136241780220681366340981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58757494520147120910893987 88136241780220681366340981)
          ·
            refine ⟨8262772666895688878094467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 88136241780220681366340981 8262772666895688878094467)
            ·
              refine ⟨12394159000343533317141701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8262772666895688878094467 12394159000343533317141701)
              ·
                refine ⟨2323904812564412496964069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12394159000343533317141701 2323904812564412496964069)
                ·
                  refine ⟨435732152355827343180763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2323904812564412496964069 435732152355827343180763)
                  ·
                    rfl

theorem cell21_1909317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 4, 4].length) (baseStart_1909317 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1909317 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1909317 prefixEnd_1909317 := by exact prefixLift 1909317
  have htrace : WordTrace (prefixWord ++ tailWord_1909317) baseStart_1909317 baseEnd_1909317 := by
    simpa [prefixWord, tailWord_1909317, baseEnd_1909317] using wordTrace_append hprefix tailTrace_1909317
  have hstable : (prefixWord ++ tailWord_1909317).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909317).length < 2 ^ (prefixWord ++ tailWord_1909317).sum := by decide
  have hdescent : baseEnd_1909317 < baseStart_1909317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909348 : List Nat := [2, 3, 1, 1, 2, 2, 5, 5]
def baseStart_1909348 : Nat := 118140960795 + 1909348 * 2 ^ 59
def prefixEnd_1909348 : Nat := 4983230072969 + 3 ^ 40 * 1909348 * 2
def baseEnd_1909348 : Nat := 145246408992726059388011

theorem tailTrace_1909348 : CollatzResearch.WordTrace tailWord_1909348 prefixEnd_1909348 145246408992726059388011 := by
  unfold tailWord_1909348
  simp only [CollatzResearch.WordTrace]
  refine ⟨34819821343382880761052349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46426428457843841014736465 34819821343382880761052349)
  ·
    refine ⟨13057433003768580285394631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34819821343382880761052349 13057433003768580285394631)
    ·
      refine ⟨19586149505652870428091947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13057433003768580285394631 19586149505652870428091947)
      ·
        refine ⟨29379224258479305642137921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19586149505652870428091947 29379224258479305642137921)
        ·
          refine ⟨22034418193859479231603441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29379224258479305642137921 22034418193859479231603441)
          ·
            refine ⟨16525813645394609423702581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22034418193859479231603441 16525813645394609423702581)
            ·
              refine ⟨1549295029255744633472117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16525813645394609423702581 1549295029255744633472117)
              ·
                refine ⟨145246408992726059388011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1549295029255744633472117 145246408992726059388011)
                ·
                  rfl

theorem cell21_1909348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 5, 5].length) (baseStart_1909348 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1909348 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1909348 prefixEnd_1909348 := by exact prefixLift 1909348
  have htrace : WordTrace (prefixWord ++ tailWord_1909348) baseStart_1909348 baseEnd_1909348 := by
    simpa [prefixWord, tailWord_1909348, baseEnd_1909348] using wordTrace_append hprefix tailTrace_1909348
  have hstable : (prefixWord ++ tailWord_1909348).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909348).length < 2 ^ (prefixWord ++ tailWord_1909348).sum := by decide
  have hdescent : baseEnd_1909348 < baseStart_1909348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909379 : List Nat := [1, 1, 1, 3, 3, 1, 4, 4, 3]
def baseStart_1909379 : Nat := 118140960795 + 1909379 * 2 ^ 59
def prefixEnd_1909379 : Nat := 4983230072969 + 3 ^ 40 * 1909379 * 2
def baseEnd_1909379 : Nat := 435746301600529013147303

theorem tailTrace_1909379 : CollatzResearch.WordTrace tailWord_1909379 prefixEnd_1909379 435746301600529013147303 := by
  unfold tailWord_1909379
  simp only [CollatzResearch.WordTrace]
  refine ⟨69640773349653453816483191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46427182233102302544322127 69640773349653453816483191)
  ·
    refine ⟨104461160024480180724724787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69640773349653453816483191 104461160024480180724724787)
    ·
      refine ⟨156691740036720271087087181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104461160024480180724724787 156691740036720271087087181)
      ·
        refine ⟨58759402513770101657657693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156691740036720271087087181 58759402513770101657657693)
        ·
          refine ⟨22034775942663788121621635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58759402513770101657657693 22034775942663788121621635)
          ·
            refine ⟨33052163913995682182432453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22034775942663788121621635 33052163913995682182432453)
            ·
              refine ⟨6197280733874190409206085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33052163913995682182432453 6197280733874190409206085)
              ·
                refine ⟨1161990137601410701726141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6197280733874190409206085 1161990137601410701726141)
                ·
                  refine ⟨435746301600529013147303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1161990137601410701726141 435746301600529013147303)
                  ·
                    rfl

theorem cell21_1909379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 4, 3].length) (baseStart_1909379 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1909379 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1909379 prefixEnd_1909379 := by exact prefixLift 1909379
  have htrace : WordTrace (prefixWord ++ tailWord_1909379) baseStart_1909379 baseEnd_1909379 := by
    simpa [prefixWord, tailWord_1909379, baseEnd_1909379] using wordTrace_append hprefix tailTrace_1909379
  have hstable : (prefixWord ++ tailWord_1909379).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909379).length < 2 ^ (prefixWord ++ tailWord_1909379).sum := by decide
  have hdescent : baseEnd_1909379 < baseStart_1909379 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909430 : List Nat := [5, 1, 3, 1, 3, 1, 1, 1, 5]
def baseStart_1909430 : Nat := 118140960795 + 1909430 * 2 ^ 59
def prefixEnd_1909430 : Nat := 4983230072969 + 3 ^ 40 * 1909430 * 2
def baseEnd_1909430 : Nat := 435757940495364257797199

theorem tailTrace_1909430 : CollatzResearch.WordTrace tailWord_1909430 prefixEnd_1909430 435757940495364257797199 := by
  unfold tailWord_1909430
  simp only [CollatzResearch.WordTrace]
  refine ⟨4352664592029293095411859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46428422314979126351059829 4352664592029293095411859)
  ·
    refine ⟨6528996888043939643117789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4352664592029293095411859 6528996888043939643117789)
    ·
      refine ⟨2448373833016477366169171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6528996888043939643117789 2448373833016477366169171)
      ·
        refine ⟨3672560749524716049253757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2448373833016477366169171 3672560749524716049253757)
        ·
          refine ⟨1377210281071768518470159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3672560749524716049253757 1377210281071768518470159)
          ·
            refine ⟨2065815421607652777705239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1377210281071768518470159 2065815421607652777705239)
            ·
              refine ⟨3098723132411479166557859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2065815421607652777705239 3098723132411479166557859)
              ·
                refine ⟨4648084698617218749836789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3098723132411479166557859 4648084698617218749836789)
                ·
                  refine ⟨435757940495364257797199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4648084698617218749836789 435757940495364257797199)
                  ·
                    rfl

theorem cell21_1909430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 1, 1, 5].length) (baseStart_1909430 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1909430 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1909430 prefixEnd_1909430 := by exact prefixLift 1909430
  have htrace : WordTrace (prefixWord ++ tailWord_1909430) baseStart_1909430 baseEnd_1909430 := by
    simpa [prefixWord, tailWord_1909430, baseEnd_1909430] using wordTrace_append hprefix tailTrace_1909430
  have hstable : (prefixWord ++ tailWord_1909430).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909430).length < 2 ^ (prefixWord ++ tailWord_1909430).sum := by decide
  have hdescent : baseEnd_1909430 < baseStart_1909430 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909486 : List Nat := [4, 1, 2, 1, 1, 4, 2, 2, 4]
def baseStart_1909486 : Nat := 118140960795 + 1909486 * 2 ^ 59
def prefixEnd_1909486 : Nat := 4983230072969 + 3 ^ 40 * 1909486 * 2
def baseEnd_1909486 : Nat := 435770720458320604863751

theorem tailTrace_1909486 : CollatzResearch.WordTrace tailWord_1909486 prefixEnd_1909486 435770720458320604863751 := by
  unfold tailWord_1909486
  simp only [CollatzResearch.WordTrace]
  refine ⟨8705584495033226386328539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46429783973510540727085541 8705584495033226386328539)
  ·
    refine ⟨13058376742549839579492809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8705584495033226386328539 13058376742549839579492809)
    ·
      refine ⟨9793782556912379684619607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13058376742549839579492809 9793782556912379684619607)
      ·
        refine ⟨14690673835368569526929411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9793782556912379684619607 14690673835368569526929411)
        ·
          refine ⟨22036010753052854290394117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14690673835368569526929411 22036010753052854290394117)
          ·
            refine ⟨4131752016197410179448897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22036010753052854290394117 4131752016197410179448897)
            ·
              refine ⟨3098814012148057634586673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4131752016197410179448897 3098814012148057634586673)
              ·
                refine ⟨2324110509111043225940005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3098814012148057634586673 2324110509111043225940005)
                ·
                  refine ⟨435770720458320604863751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2324110509111043225940005 435770720458320604863751)
                  ·
                    rfl

theorem cell21_1909486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 2, 2, 4].length) (baseStart_1909486 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1909486 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1909486 prefixEnd_1909486 := by exact prefixLift 1909486
  have htrace : WordTrace (prefixWord ++ tailWord_1909486) baseStart_1909486 baseEnd_1909486 := by
    simpa [prefixWord, tailWord_1909486, baseEnd_1909486] using wordTrace_append hprefix tailTrace_1909486
  have hstable : (prefixWord ++ tailWord_1909486).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909486).length < 2 ^ (prefixWord ++ tailWord_1909486).sum := by decide
  have hdescent : baseEnd_1909486 < baseStart_1909486 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909497 : List Nat := [1, 2, 1, 3, 1, 1, 1, 2, 9]
def baseStart_1909497 : Nat := 118140960795 + 1909497 * 2 ^ 59
def prefixEnd_1909497 : Nat := 4983230072969 + 3 ^ 40 * 1909497 * 2
def baseEnd_1909497 : Nat := 435773230808187030180395

theorem tailTrace_1909497 : CollatzResearch.WordTrace tailWord_1909497 prefixEnd_1909497 435773230808187030180395 := by
  unfold tailWord_1909497
  simp only [CollatzResearch.WordTrace]
  refine ⟨69645077163225959969278745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46430051442150639979519163 69645077163225959969278745)
  ·
    refine ⟨52233807872419469976959059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69645077163225959969278745 52233807872419469976959059)
    ·
      refine ⟨78350711808629204965438589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52233807872419469976959059 78350711808629204965438589)
      ·
        refine ⟨29381516928235951862039471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78350711808629204965438589 29381516928235951862039471)
        ·
          refine ⟨44072275392353927793059207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29381516928235951862039471 44072275392353927793059207)
          ·
            refine ⟨66108413088530891689588811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44072275392353927793059207 66108413088530891689588811)
            ·
              refine ⟨99162619632796337534383217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66108413088530891689588811 99162619632796337534383217)
              ·
                refine ⟨74371964724597253150787413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99162619632796337534383217 74371964724597253150787413)
                ·
                  refine ⟨435773230808187030180395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 74371964724597253150787413 435773230808187030180395)
                  ·
                    rfl

theorem cell21_1909497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 9].length) (baseStart_1909497 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1909497 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1909497 prefixEnd_1909497 := by exact prefixLift 1909497
  have htrace : WordTrace (prefixWord ++ tailWord_1909497) baseStart_1909497 baseEnd_1909497 := by
    simpa [prefixWord, tailWord_1909497, baseEnd_1909497] using wordTrace_append hprefix tailTrace_1909497
  have hstable : (prefixWord ++ tailWord_1909497).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909497).length < 2 ^ (prefixWord ++ tailWord_1909497).sum := by decide
  have hdescent : baseEnd_1909497 < baseStart_1909497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909500 : List Nat := [2, 2, 2, 1, 3, 4, 1, 6]
def baseStart_1909500 : Nat := 118140960795 + 1909500 * 2 ^ 59
def prefixEnd_1909500 : Nat := 4983230072969 + 3 ^ 40 * 1909500 * 2
def baseEnd_1909500 : Nat := 145257971816353230543463

theorem tailTrace_1909500 : CollatzResearch.WordTrace tailWord_1909500 prefixEnd_1909500 145257971816353230543463 := by
  unfold tailWord_1909500
  simp only [CollatzResearch.WordTrace]
  refine ⟨34822593291107545740818977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46430124388143394321091969 34822593291107545740818977)
  ·
    refine ⟨26116944968330659305614233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34822593291107545740818977 26116944968330659305614233)
    ·
      refine ⟨19587708726247994479210675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26116944968330659305614233 19587708726247994479210675)
      ·
        refine ⟨29381563089371991718816013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19587708726247994479210675 29381563089371991718816013)
        ·
          refine ⟨11018086158514496894556005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29381563089371991718816013 11018086158514496894556005)
          ·
            refine ⟨2065891154721468167729251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11018086158514496894556005 2065891154721468167729251)
            ·
              refine ⟨3098836732082202251593877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2065891154721468167729251 3098836732082202251593877)
              ·
                refine ⟨145257971816353230543463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3098836732082202251593877 145257971816353230543463)
                ·
                  rfl

theorem cell21_1909500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 1, 6].length) (baseStart_1909500 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1909500 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1909500 prefixEnd_1909500 := by exact prefixLift 1909500
  have htrace : WordTrace (prefixWord ++ tailWord_1909500) baseStart_1909500 baseEnd_1909500 := by
    simpa [prefixWord, tailWord_1909500, baseEnd_1909500] using wordTrace_append hprefix tailTrace_1909500
  have hstable : (prefixWord ++ tailWord_1909500).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909500).length < 2 ^ (prefixWord ++ tailWord_1909500).sum := by decide
  have hdescent : baseEnd_1909500 < baseStart_1909500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909514 : List Nat := [3, 1, 2, 2, 1, 2, 3, 2, 5]
def baseStart_1909514 : Nat := 118140960795 + 1909514 * 2 ^ 59
def prefixEnd_1909514 : Nat := 4983230072969 + 3 ^ 40 * 1909514 * 2
def baseEnd_1909514 : Nat := 435777110439798778397027

theorem tailTrace_1909514 : CollatzResearch.WordTrace tailWord_1909514 prefixEnd_1909514 435777110439798778397027 := by
  unfold tailWord_1909514
  simp only [CollatzResearch.WordTrace]
  refine ⟨17411424301041092968161899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46430464802776247915098397 17411424301041092968161899)
  ·
    refine ⟨26117136451561639452242849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17411424301041092968161899 26117136451561639452242849)
    ·
      refine ⟨19587852338671229589182137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26117136451561639452242849 19587852338671229589182137)
      ·
        refine ⟨14690889254003422191886603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19587852338671229589182137 14690889254003422191886603)
        ·
          refine ⟨22036333881005133287829905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14690889254003422191886603 22036333881005133287829905)
          ·
            refine ⟨16527250410753849965872429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22036333881005133287829905 16527250410753849965872429)
            ·
              refine ⟨6197718904032693737202161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16527250410753849965872429 6197718904032693737202161)
              ·
                refine ⟨4648289178024520302901621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6197718904032693737202161 4648289178024520302901621)
                ·
                  refine ⟨435777110439798778397027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4648289178024520302901621 435777110439798778397027)
                  ·
                    rfl

theorem cell21_1909514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 2, 5].length) (baseStart_1909514 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1909514 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1909514 prefixEnd_1909514 := by exact prefixLift 1909514
  have htrace : WordTrace (prefixWord ++ tailWord_1909514) baseStart_1909514 baseEnd_1909514 := by
    simpa [prefixWord, tailWord_1909514, baseEnd_1909514] using wordTrace_append hprefix tailTrace_1909514
  have hstable : (prefixWord ++ tailWord_1909514).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909514).length < 2 ^ (prefixWord ++ tailWord_1909514).sum := by decide
  have hdescent : baseEnd_1909514 < baseStart_1909514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909528 : List Nat := [2, 1, 2, 3, 1, 1, 1, 4, 6]
def baseStart_1909528 : Nat := 118140960795 + 1909528 * 2 ^ 59
def prefixEnd_1909528 : Nat := 4983230072969 + 3 ^ 40 * 1909528 * 2
def baseEnd_1909528 : Nat := 435780305430537865163665

theorem tailTrace_1909528 : CollatzResearch.WordTrace tailWord_1909528 prefixEnd_1909528 435780305430537865163665 := by
  unfold tailWord_1909528
  simp only [CollatzResearch.WordTrace]
  refine ⟨34823103913056826131828619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46430805217409101509104825 34823103913056826131828619)
  ·
    refine ⟨52234655869585239197742929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34823103913056826131828619 52234655869585239197742929)
    ·
      refine ⟨39175991902188929398307197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52234655869585239197742929 39175991902188929398307197)
      ·
        refine ⟨14690996963320848524365199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39175991902188929398307197 14690996963320848524365199)
        ·
          refine ⟨22036495444981272786547799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14690996963320848524365199 22036495444981272786547799)
          ·
            refine ⟨33054743167471909179821699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22036495444981272786547799 33054743167471909179821699)
            ·
              refine ⟨49582114751207863769732549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33054743167471909179821699 49582114751207863769732549)
              ·
                refine ⟨9296646515851474456824853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49582114751207863769732549 9296646515851474456824853)
                ·
                  refine ⟨435780305430537865163665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9296646515851474456824853 435780305430537865163665)
                  ·
                    rfl

theorem cell21_1909528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 4, 6].length) (baseStart_1909528 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1909528 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1909528 prefixEnd_1909528 := by exact prefixLift 1909528
  have htrace : WordTrace (prefixWord ++ tailWord_1909528) baseStart_1909528 baseEnd_1909528 := by
    simpa [prefixWord, tailWord_1909528, baseEnd_1909528] using wordTrace_append hprefix tailTrace_1909528
  have hstable : (prefixWord ++ tailWord_1909528).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909528).length < 2 ^ (prefixWord ++ tailWord_1909528).sum := by decide
  have hdescent : baseEnd_1909528 < baseStart_1909528 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909573 : List Nat := [1, 3, 1, 1, 1, 2, 2, 3, 7]
def baseStart_1909573 : Nat := 118140960795 + 1909573 * 2 ^ 59
def prefixEnd_1909573 : Nat := 4983230072969 + 3 ^ 40 * 1909573 * 2
def baseEnd_1909573 : Nat := 435790575043627786913573

theorem tailTrace_1909573 : CollatzResearch.WordTrace tailWord_1909573 prefixEnd_1909573 435790575043627786913573 := by
  unfold tailWord_1909573
  simp only [CollatzResearch.WordTrace]
  refine ⟨69647849110950624949045373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46431899407300416632696915 69647849110950624949045373)
  ·
    refine ⟨26117943416606484355892015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69647849110950624949045373 26117943416606484355892015)
    ·
      refine ⟨39176915124909726533838023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26117943416606484355892015 39176915124909726533838023)
      ·
        refine ⟨58765372687364589800757035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39176915124909726533838023 58765372687364589800757035)
        ·
          refine ⟨88148059031046884701135553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58765372687364589800757035 88148059031046884701135553)
          ·
            refine ⟨66111044273285163525851665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88148059031046884701135553 66111044273285163525851665)
            ·
              refine ⟨49583283204963872644388749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66111044273285163525851665 49583283204963872644388749)
              ·
                refine ⟨18593731201861452241645781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49583283204963872644388749 18593731201861452241645781)
                ·
                  refine ⟨435790575043627786913573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18593731201861452241645781 435790575043627786913573)
                  ·
                    rfl

theorem cell21_1909573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 3, 7].length) (baseStart_1909573 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1909573 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1909573 prefixEnd_1909573 := by exact prefixLift 1909573
  have htrace : WordTrace (prefixWord ++ tailWord_1909573) baseStart_1909573 baseEnd_1909573 := by
    simpa [prefixWord, tailWord_1909573, baseEnd_1909573] using wordTrace_append hprefix tailTrace_1909573
  have hstable : (prefixWord ++ tailWord_1909573).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909573).length < 2 ^ (prefixWord ++ tailWord_1909573).sum := by decide
  have hdescent : baseEnd_1909573 < baseStart_1909573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909607 : List Nat := [1, 1, 5, 1, 2, 4, 1, 1, 5]
def baseStart_1909607 : Nat := 118140960795 + 1909607 * 2 ^ 59
def prefixEnd_1909607 : Nat := 4983230072969 + 3 ^ 40 * 1909607 * 2
def baseEnd_1909607 : Nat := 435798334306851283346837

theorem tailTrace_1909607 : CollatzResearch.WordTrace tailWord_1909607 prefixEnd_1909607 435798334306851283346837 := by
  unfold tailWord_1909607
  simp only [CollatzResearch.WordTrace]
  refine ⟨69649089192827448755783075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46432726128551632503855383 69649089192827448755783075)
  ·
    refine ⟨104473633789241173133674613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69649089192827448755783075 104473633789241173133674613)
    ·
      refine ⟨9794403167741359981281995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 104473633789241173133674613 9794403167741359981281995)
      ·
        refine ⟨14691604751612039971922993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9794403167741359981281995 14691604751612039971922993)
        ·
          refine ⟨11018703563709029978942245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14691604751612039971922993 11018703563709029978942245)
          ·
            refine ⟨2066006918195443121051671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11018703563709029978942245 2066006918195443121051671)
            ·
              refine ⟨3099010377293164681577507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2066006918195443121051671 3099010377293164681577507)
              ·
                refine ⟨4648515565939747022366261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3099010377293164681577507 4648515565939747022366261)
                ·
                  refine ⟨435798334306851283346837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4648515565939747022366261 435798334306851283346837)
                  ·
                    rfl

theorem cell21_1909607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 1, 1, 5].length) (baseStart_1909607 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1909607 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1909607 prefixEnd_1909607 := by exact prefixLift 1909607
  have htrace : WordTrace (prefixWord ++ tailWord_1909607) baseStart_1909607 baseEnd_1909607 := by
    simpa [prefixWord, tailWord_1909607, baseEnd_1909607] using wordTrace_append hprefix tailTrace_1909607
  have hstable : (prefixWord ++ tailWord_1909607).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909607).length < 2 ^ (prefixWord ++ tailWord_1909607).sum := by decide
  have hdescent : baseEnd_1909607 < baseStart_1909607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909658 : List Nat := [3, 1, 1, 4, 4, 1, 2, 2, 3]
def baseStart_1909658 : Nat := 118140960795 + 1909658 * 2 ^ 59
def prefixEnd_1909658 : Nat := 4983230072969 + 3 ^ 40 * 1909658 * 2
def baseEnd_1909658 : Nat := 435809973201686527996733

theorem tailTrace_1909658 : CollatzResearch.WordTrace tailWord_1909658 prefixEnd_1909658 435809973201686527996733 := by
  unfold tailWord_1909658
  simp only [CollatzResearch.WordTrace]
  refine ⟨17412737328910671116472407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46433966210428456310593085 17412737328910671116472407)
  ·
    refine ⟨26119105993366006674708611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17412737328910671116472407 26119105993366006674708611)
    ·
      refine ⟨39178658990049010012062917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26119105993366006674708611 39178658990049010012062917)
      ·
        refine ⟨7345998560634189377261797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39178658990049010012062917 7345998560634189377261797)
        ·
          refine ⟨1377374730118910508236587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7345998560634189377261797 1377374730118910508236587)
          ·
            refine ⟨2066062095178365762354881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1377374730118910508236587 2066062095178365762354881)
            ·
              refine ⟨1549546571383774321766161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2066062095178365762354881 1549546571383774321766161)
              ·
                refine ⟨1162159928537830741324621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1549546571383774321766161 1162159928537830741324621)
                ·
                  refine ⟨435809973201686527996733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1162159928537830741324621 435809973201686527996733)
                  ·
                    rfl

theorem cell21_1909658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 2, 2, 3].length) (baseStart_1909658 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1909658 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1909658 prefixEnd_1909658 := by exact prefixLift 1909658
  have htrace : WordTrace (prefixWord ++ tailWord_1909658) baseStart_1909658 baseEnd_1909658 := by
    simpa [prefixWord, tailWord_1909658, baseEnd_1909658] using wordTrace_append hprefix tailTrace_1909658
  have hstable : (prefixWord ++ tailWord_1909658).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909658).length < 2 ^ (prefixWord ++ tailWord_1909658).sum := by decide
  have hdescent : baseEnd_1909658 < baseStart_1909658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909714 : List Nat := [3, 2, 2, 3, 1, 1, 3, 2, 4]
def baseStart_1909714 : Nat := 118140960795 + 1909714 * 2 ^ 59
def prefixEnd_1909714 : Nat := 4983230072969 + 3 ^ 40 * 1909714 * 2
def baseEnd_1909714 : Nat := 435822753164642875063285

theorem tailTrace_1909714 : CollatzResearch.WordTrace tailWord_1909714 prefixEnd_1909714 435822753164642875063285 := by
  unfold tailWord_1909714
  simp only [CollatzResearch.WordTrace]
  refine ⟨17413247950859951507482049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46435327868959870686618797 17413247950859951507482049)
  ·
    refine ⟨13059935963144963630611537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17413247950859951507482049 13059935963144963630611537)
    ·
      refine ⟨9794951972358722722958653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13059935963144963630611537 9794951972358722722958653)
      ·
        refine ⟨3673106989634521021109495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9794951972358722722958653 3673106989634521021109495)
        ·
          refine ⟨5509660484451781531664243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3673106989634521021109495 5509660484451781531664243)
          ·
            refine ⟨8264490726677672297496365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5509660484451781531664243 8264490726677672297496365)
            ·
              refine ⟨3099184022504127111561137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8264490726677672297496365 3099184022504127111561137)
              ·
                refine ⟨2324388016878095333670853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3099184022504127111561137 2324388016878095333670853)
                ·
                  refine ⟨435822753164642875063285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2324388016878095333670853 435822753164642875063285)
                  ·
                    rfl

theorem cell21_1909714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 3, 2, 4].length) (baseStart_1909714 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1909714 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1909714 prefixEnd_1909714 := by exact prefixLift 1909714
  have htrace : WordTrace (prefixWord ++ tailWord_1909714) baseStart_1909714 baseEnd_1909714 := by
    simpa [prefixWord, tailWord_1909714, baseEnd_1909714] using wordTrace_append hprefix tailTrace_1909714
  have hstable : (prefixWord ++ tailWord_1909714).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909714).length < 2 ^ (prefixWord ++ tailWord_1909714).sum := by decide
  have hdescent : baseEnd_1909714 < baseStart_1909714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909756 : List Nat := [2, 2, 2, 1, 2, 3, 1, 2, 6]
def baseStart_1909756 : Nat := 118140960795 + 1909756 * 2 ^ 59
def prefixEnd_1909756 : Nat := 4983230072969 + 3 ^ 40 * 1909756 * 2
def baseEnd_1909756 : Nat := 435832338136860135363199

theorem tailTrace_1909756 : CollatzResearch.WordTrace tailWord_1909756 prefixEnd_1909756 435832338136860135363199 := by
  unfold tailWord_1909756
  simp only [CollatzResearch.WordTrace]
  refine ⟨34827261834643823601478561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46436349112858431468638081 34827261834643823601478561)
  ·
    refine ⟨26120446375982867701108921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34827261834643823601478561 26120446375982867701108921)
    ·
      refine ⟨19590334781987150775831691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26120446375982867701108921 19590334781987150775831691)
      ·
        refine ⟨29385502172980726163747537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19590334781987150775831691 29385502172980726163747537)
        ·
          refine ⟨22039126629735544622810653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29385502172980726163747537 22039126629735544622810653)
          ·
            refine ⟨8264672486150829233553995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22039126629735544622810653 8264672486150829233553995)
            ·
              refine ⟨12397008729226243850330993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8264672486150829233553995 12397008729226243850330993)
              ·
                refine ⟨9297756546919682887748245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12397008729226243850330993 9297756546919682887748245)
                ·
                  refine ⟨435832338136860135363199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9297756546919682887748245 435832338136860135363199)
                  ·
                    rfl

theorem cell21_1909756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 2, 6].length) (baseStart_1909756 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1909756 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1909756 prefixEnd_1909756 := by exact prefixLift 1909756
  have htrace : WordTrace (prefixWord ++ tailWord_1909756) baseStart_1909756 baseEnd_1909756 := by
    simpa [prefixWord, tailWord_1909756, baseEnd_1909756] using wordTrace_append hprefix tailTrace_1909756
  have hstable : (prefixWord ++ tailWord_1909756).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909756).length < 2 ^ (prefixWord ++ tailWord_1909756).sum := by decide
  have hdescent : baseEnd_1909756 < baseStart_1909756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909762 : List Nat := [3, 4, 1, 3, 2, 1, 7]
def baseStart_1909762 : Nat := 118140960795 + 1909762 * 2 ^ 59
def prefixEnd_1909762 : Nat := 4983230072969 + 3 ^ 40 * 1909762 * 2
def baseEnd_1909762 : Nat := 48425967490956162029243

theorem tailTrace_1909762 : CollatzResearch.WordTrace tailWord_1909762 prefixEnd_1909762 48425967490956162029243 := by
  unfold tailWord_1909762
  simp only [CollatzResearch.WordTrace]
  refine ⟨17413685626816477556918885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46436495004843940151783693 17413685626816477556918885)
  ·
    refine ⟨3265066055028089541922291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17413685626816477556918885 3265066055028089541922291)
    ·
      refine ⟨4897599082542134312883437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3265066055028089541922291 4897599082542134312883437)
      ·
        refine ⟨1836599655953300367331289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4897599082542134312883437 1836599655953300367331289)
        ·
          refine ⟨1377449741964975275498467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1836599655953300367331289 1377449741964975275498467)
          ·
            refine ⟨2066174612947462913247701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1377449741964975275498467 2066174612947462913247701)
            ·
              refine ⟨48425967490956162029243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2066174612947462913247701 48425967490956162029243)
              ·
                rfl

theorem cell21_1909762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 7].length) (baseStart_1909762 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1909762 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1909762 prefixEnd_1909762 := by exact prefixLift 1909762
  have htrace : WordTrace (prefixWord ++ tailWord_1909762) baseStart_1909762 baseEnd_1909762 := by
    simpa [prefixWord, tailWord_1909762, baseEnd_1909762] using wordTrace_append hprefix tailTrace_1909762
  have hstable : (prefixWord ++ tailWord_1909762).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909762).length < 2 ^ (prefixWord ++ tailWord_1909762).sum := by decide
  have hdescent : baseEnd_1909762 < baseStart_1909762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909956 : List Nat := [2, 3, 3, 1, 3, 1, 2, 6]
def baseStart_1909956 : Nat := 118140960795 + 1909956 * 2 ^ 59
def prefixEnd_1909956 : Nat := 4983230072969 + 3 ^ 40 * 1909956 * 2
def baseEnd_1909956 : Nat := 145292660287234744009819

theorem tailTrace_1909956 : CollatzResearch.WordTrace tailWord_1909956 prefixEnd_1909956 145292660287234744009819 := by
  unfold tailWord_1909956
  simp only [CollatzResearch.WordTrace]
  refine ⟨34830909134281540680118861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46441212179042054240158481 34830909134281540680118861)
  ·
    refine ⟨13061590925355577755044573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34830909134281540680118861 13061590925355577755044573)
    ·
      refine ⟨4898096597008341658141715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13061590925355577755044573 4898096597008341658141715)
      ·
        refine ⟨7347144895512512487212573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4898096597008341658141715 7347144895512512487212573)
        ·
          refine ⟨2755179335817192182704715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7347144895512512487212573 2755179335817192182704715)
          ·
            refine ⟨4132769003725788274057073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2755179335817192182704715 4132769003725788274057073)
            ·
              refine ⟨3099576752794341205542805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4132769003725788274057073 3099576752794341205542805)
              ·
                refine ⟨145292660287234744009819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3099576752794341205542805 145292660287234744009819)
                ·
                  rfl

theorem cell21_1909956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 2, 6].length) (baseStart_1909956 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1909956 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1909956 prefixEnd_1909956 := by exact prefixLift 1909956
  have htrace : WordTrace (prefixWord ++ tailWord_1909956) baseStart_1909956 baseEnd_1909956 := by
    simpa [prefixWord, tailWord_1909956, baseEnd_1909956] using wordTrace_append hprefix tailTrace_1909956
  have hstable : (prefixWord ++ tailWord_1909956).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909956).length < 2 ^ (prefixWord ++ tailWord_1909956).sum := by decide
  have hdescent : baseEnd_1909956 < baseStart_1909956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909967 : List Nat := [1, 1, 2, 1, 1, 3, 2, 2, 8]
def baseStart_1909967 : Nat := 118140960795 + 1909967 * 2 ^ 59
def prefixEnd_1909967 : Nat := 4983230072969 + 3 ^ 40 * 1909967 * 2
def baseEnd_1909967 : Nat := 435880491211570657346101

theorem tailTrace_1909967 : CollatzResearch.WordTrace tailWord_1909967 prefixEnd_1909967 435880491211570657346101 := by
  unfold tailWord_1909967
  simp only [CollatzResearch.WordTrace]
  refine ⟨69662219471523230238888155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46441479647682153492592103 69662219471523230238888155)
  ·
    refine ⟨104493329207284845358332233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69662219471523230238888155 104493329207284845358332233)
    ·
      refine ⟨78369996905463634018749175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104493329207284845358332233 78369996905463634018749175)
      ·
        refine ⟨117554995358195451028123763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78369996905463634018749175 117554995358195451028123763)
        ·
          refine ⟨176332493037293176542185645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117554995358195451028123763 176332493037293176542185645)
          ·
            refine ⟨66124684888984941203319617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 176332493037293176542185645 66124684888984941203319617)
            ·
              refine ⟨49593513666738705902489713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66124684888984941203319617 49593513666738705902489713)
              ·
                refine ⟨37195135250054029426867285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49593513666738705902489713 37195135250054029426867285)
                ·
                  refine ⟨435880491211570657346101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37195135250054029426867285 435880491211570657346101)
                  ·
                    rfl

theorem cell21_1909967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 8].length) (baseStart_1909967 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1909967 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1909967 prefixEnd_1909967 := by exact prefixLift 1909967
  have htrace : WordTrace (prefixWord ++ tailWord_1909967) baseStart_1909967 baseEnd_1909967 := by
    simpa [prefixWord, tailWord_1909967, baseEnd_1909967] using wordTrace_append hprefix tailTrace_1909967
  have hstable : (prefixWord ++ tailWord_1909967).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909967).length < 2 ^ (prefixWord ++ tailWord_1909967).sum := by decide
  have hdescent : baseEnd_1909967 < baseStart_1909967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1910015 : List Nat := [1, 1, 2, 2, 1, 7, 1, 6]
def baseStart_1910015 : Nat := 118140960795 + 1910015 * 2 ^ 59
def prefixEnd_1910015 : Nat := 4983230072969 + 3 ^ 40 * 1910015 * 2
def baseEnd_1910015 : Nat := 145297148488511080182001

theorem tailTrace_1910015 : CollatzResearch.WordTrace tailWord_1910015 prefixEnd_1910015 145297148488511080182001 := by
  unfold tailWord_1910015
  simp only [CollatzResearch.WordTrace]
  refine ⟨69663970175349334436635499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46442646783566222957756999 69663970175349334436635499)
  ·
    refine ⟨104495955263024001654953249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69663970175349334436635499 104495955263024001654953249)
    ·
      refine ⟨78371966447268001241214937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104495955263024001654953249 78371966447268001241214937)
      ·
        refine ⟨58778974835451000930911203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78371966447268001241214937 58778974835451000930911203)
        ·
          refine ⟨88168462253176501396366805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58778974835451000930911203 88168462253176501396366805)
          ·
            refine ⟨2066448334058824251477347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 88168462253176501396366805 2066448334058824251477347)
            ·
              refine ⟨3099672501088236377216021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2066448334058824251477347 3099672501088236377216021)
              ·
                refine ⟨145297148488511080182001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3099672501088236377216021 145297148488511080182001)
                ·
                  rfl

theorem cell21_1910015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 1, 6].length) (baseStart_1910015 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1910015 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1910015 prefixEnd_1910015 := by exact prefixLift 1910015
  have htrace : WordTrace (prefixWord ++ tailWord_1910015) baseStart_1910015 baseEnd_1910015 := by
    simpa [prefixWord, tailWord_1910015, baseEnd_1910015] using wordTrace_append hprefix tailTrace_1910015
  have hstable : (prefixWord ++ tailWord_1910015).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1910015).length < 2 ^ (prefixWord ++ tailWord_1910015).sum := by decide
  have hdescent : baseEnd_1910015 < baseStart_1910015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1910015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1910043 : List Nat := [1, 1, 1, 1, 1, 1, 5, 4, 6]
def baseStart_1910043 : Nat := 118140960795 + 1910043 * 2 ^ 59
def prefixEnd_1910043 : Nat := 4983230072969 + 3 ^ 40 * 1910043 * 2
def baseEnd_1910043 : Nat := 435897835447011414079279

theorem tailTrace_1910043 : CollatzResearch.WordTrace tailWord_1910043 prefixEnd_1910043 435897835447011414079279 := by
  unfold tailWord_1910043
  simp only [CollatzResearch.WordTrace]
  refine ⟨69664991419247895218654783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46443327612831930145769855 69664991419247895218654783)
  ·
    refine ⟨104497487128871842827982175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69664991419247895218654783 104497487128871842827982175)
    ·
      refine ⟨156746230693307764241973263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104497487128871842827982175 156746230693307764241973263)
      ·
        refine ⟨235119346039961646362959895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156746230693307764241973263 235119346039961646362959895)
        ·
          refine ⟨352679019059942469544439843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235119346039961646362959895 352679019059942469544439843)
          ·
            refine ⟨529018528589913704316659765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 352679019059942469544439843 529018528589913704316659765)
            ·
              refine ⟨49595487055304409779686853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 529018528589913704316659765 49595487055304409779686853)
              ·
                refine ⟨9299153822869576833691285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49595487055304409779686853 9299153822869576833691285)
                ·
                  refine ⟨435897835447011414079279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9299153822869576833691285 435897835447011414079279)
                  ·
                    rfl

theorem cell21_1910043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 4, 6].length) (baseStart_1910043 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1910043 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1910043 prefixEnd_1910043 := by exact prefixLift 1910043
  have htrace : WordTrace (prefixWord ++ tailWord_1910043) baseStart_1910043 baseEnd_1910043 := by
    simpa [prefixWord, tailWord_1910043, baseEnd_1910043] using wordTrace_append hprefix tailTrace_1910043
  have hstable : (prefixWord ++ tailWord_1910043).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1910043).length < 2 ^ (prefixWord ++ tailWord_1910043).sum := by decide
  have hdescent : baseEnd_1910043 < baseStart_1910043 := by decide
  rcases family_descends (prefixWord ++ tailWord_1910043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1910074 : List Nat := [3, 1, 1, 1, 4, 1, 2, 8]
def baseStart_1910074 : Nat := 118140960795 + 1910074 * 2 ^ 59
def prefixEnd_1910074 : Nat := 4983230072969 + 3 ^ 40 * 1910074 * 2
def baseEnd_1910074 : Nat := 145301636689787416354183

theorem tailTrace_1910074 : CollatzResearch.WordTrace tailWord_1910074 prefixEnd_1910074 145301636689787416354183 := by
  unfold tailWord_1910074
  simp only [CollatzResearch.WordTrace]
  refine ⟨17416530520533896878258319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46444081388090391675355517 17416530520533896878258319)
  ·
    refine ⟨26124795780800845317387479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17416530520533896878258319 26124795780800845317387479)
    ·
      refine ⟨39187193671201267976081219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26124795780800845317387479 39187193671201267976081219)
      ·
        refine ⟨58780790506801901964121829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39187193671201267976081219 58780790506801901964121829)
        ·
          refine ⟨11021398220025356618272843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58780790506801901964121829 11021398220025356618272843)
          ·
            refine ⟨16532097330038034927409265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11021398220025356618272843 16532097330038034927409265)
            ·
              refine ⟨12399072997528526195556949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16532097330038034927409265 12399072997528526195556949)
              ·
                refine ⟨145301636689787416354183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12399072997528526195556949 145301636689787416354183)
                ·
                  rfl

theorem cell21_1910074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 8].length) (baseStart_1910074 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1910074 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1910074 prefixEnd_1910074 := by exact prefixLift 1910074
  have htrace : WordTrace (prefixWord ++ tailWord_1910074) baseStart_1910074 baseEnd_1910074 := by
    simpa [prefixWord, tailWord_1910074, baseEnd_1910074] using wordTrace_append hprefix tailTrace_1910074
  have hstable : (prefixWord ++ tailWord_1910074).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1910074).length < 2 ^ (prefixWord ++ tailWord_1910074).sum := by decide
  have hdescent : baseEnd_1910074 < baseStart_1910074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1910074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1910257 : List Nat := [1, 2, 2, 2, 3, 2, 2, 2, 5]
def baseStart_1910257 : Nat := 118140960795 + 1910257 * 2 ^ 59
def prefixEnd_1910257 : Nat := 4983230072969 + 3 ^ 40 * 1910257 * 2
def baseEnd_1910257 : Nat := 435946673162594597512175

theorem tailTrace_1910257 : CollatzResearch.WordTrace tailWord_1910257 prefixEnd_1910257 435946673162594597512175 := by
  unfold tailWord_1910257
  simp only [CollatzResearch.WordTrace]
  refine ⟨69672796640472609766945025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46448531093648406511296683 69672796640472609766945025)
  ·
    refine ⟨52254597480354457325208769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69672796640472609766945025 52254597480354457325208769)
    ·
      refine ⟨39190948110265842993906577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52254597480354457325208769 39190948110265842993906577)
      ·
        refine ⟨29393211082699382245429933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39190948110265842993906577 29393211082699382245429933)
        ·
          refine ⟨11022454156012268342036225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29393211082699382245429933 11022454156012268342036225)
          ·
            refine ⟨8266840617009201256527169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11022454156012268342036225 8266840617009201256527169)
            ·
              refine ⟨6200130462756900942395377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8266840617009201256527169 6200130462756900942395377)
              ·
                refine ⟨4650097847067675706796533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6200130462756900942395377 4650097847067675706796533)
                ·
                  refine ⟨435946673162594597512175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4650097847067675706796533 435946673162594597512175)
                  ·
                    rfl

theorem cell21_1910257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 2, 5].length) (baseStart_1910257 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1910257 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1910257 prefixEnd_1910257 := by exact prefixLift 1910257
  have htrace : WordTrace (prefixWord ++ tailWord_1910257) baseStart_1910257 baseEnd_1910257 := by
    simpa [prefixWord, tailWord_1910257, baseEnd_1910257] using wordTrace_append hprefix tailTrace_1910257
  have hstable : (prefixWord ++ tailWord_1910257).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1910257).length < 2 ^ (prefixWord ++ tailWord_1910257).sum := by decide
  have hdescent : baseEnd_1910257 < baseStart_1910257 := by decide
  rcases family_descends (prefixWord ++ tailWord_1910257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1910291 : List Nat := [1, 1, 1, 2, 1, 7, 3, 2, 3]
def baseStart_1910291 : Nat := 118140960795 + 1910291 * 2 ^ 59
def prefixEnd_1910291 : Nat := 4983230072969 + 3 ^ 40 * 1910291 * 2
def baseEnd_1910291 : Nat := 435954432425818093945439

theorem tailTrace_1910291 : CollatzResearch.WordTrace tailWord_1910291 prefixEnd_1910291 435954432425818093945439 := by
  unfold tailWord_1910291
  simp only [CollatzResearch.WordTrace]
  refine ⟨69674036722349433573682727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46449357814899622382455151 69674036722349433573682727)
  ·
    refine ⟨104511055083524150360524091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69674036722349433573682727 104511055083524150360524091)
    ·
      refine ⟨156766582625286225540786137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104511055083524150360524091 156766582625286225540786137)
      ·
        refine ⟨117574936968964669155589603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156766582625286225540786137 117574936968964669155589603)
        ·
          refine ⟨176362405453447003733384405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117574936968964669155589603 176362405453447003733384405)
          ·
            refine ⟨4133493877815164150001197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 176362405453447003733384405 4133493877815164150001197)
            ·
              refine ⟨1550060204180686556250449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4133493877815164150001197 1550060204180686556250449)
              ·
                refine ⟨1162545153135514917187837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1550060204180686556250449 1162545153135514917187837)
                ·
                  refine ⟨435954432425818093945439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1162545153135514917187837 435954432425818093945439)
                  ·
                    rfl

theorem cell21_1910291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 3, 2, 3].length) (baseStart_1910291 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1910291 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1910291 prefixEnd_1910291 := by exact prefixLift 1910291
  have htrace : WordTrace (prefixWord ++ tailWord_1910291) baseStart_1910291 baseEnd_1910291 := by
    simpa [prefixWord, tailWord_1910291, baseEnd_1910291] using wordTrace_append hprefix tailTrace_1910291
  have hstable : (prefixWord ++ tailWord_1910291).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1910291).length < 2 ^ (prefixWord ++ tailWord_1910291).sum := by decide
  have hdescent : baseEnd_1910291 < baseStart_1910291 := by decide
  rcases family_descends (prefixWord ++ tailWord_1910291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1910305 : List Nat := [1, 2, 3, 2, 2, 2, 4, 1, 4]
def baseStart_1910305 : Nat := 118140960795 + 1910305 * 2 ^ 59
def prefixEnd_1910305 : Nat := 4983230072969 + 3 ^ 40 * 1910305 * 2
def baseEnd_1910305 : Nat := 435957627416557180712077

theorem tailTrace_1910305 : CollatzResearch.WordTrace tailWord_1910305 prefixEnd_1910305 435957627416557180712077 := by
  unfold tailWord_1910305
  simp only [CollatzResearch.WordTrace]
  refine ⟨69674547344298713964692369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46449698229532475976461579 69674547344298713964692369)
  ·
    refine ⟨52255910508224035473519277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69674547344298713964692369 52255910508224035473519277)
    ·
      refine ⟨19595966440584013302569729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52255910508224035473519277 19595966440584013302569729)
      ·
        refine ⟨14696974830438009976927297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19595966440584013302569729 14696974830438009976927297)
        ·
          refine ⟨11022731122828507482695473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14696974830438009976927297 11022731122828507482695473)
          ·
            refine ⟨8267048342121380612021605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11022731122828507482695473 8267048342121380612021605)
            ·
              refine ⟨1550071564147758864754051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8267048342121380612021605 1550071564147758864754051)
              ·
                refine ⟨2325107346221638297131077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1550071564147758864754051 2325107346221638297131077)
                ·
                  refine ⟨435957627416557180712077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2325107346221638297131077 435957627416557180712077)
                  ·
                    rfl

theorem cell21_1910305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 4, 1, 4].length) (baseStart_1910305 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1910305 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1910305 prefixEnd_1910305 := by exact prefixLift 1910305
  have htrace : WordTrace (prefixWord ++ tailWord_1910305) baseStart_1910305 baseEnd_1910305 := by
    simpa [prefixWord, tailWord_1910305, baseEnd_1910305] using wordTrace_append hprefix tailTrace_1910305
  have hstable : (prefixWord ++ tailWord_1910305).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1910305).length < 2 ^ (prefixWord ++ tailWord_1910305).sum := by decide
  have hdescent : baseEnd_1910305 < baseStart_1910305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1910305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1910342 : List Nat := [6, 1, 1, 1, 3, 2, 2, 2, 3]
def baseStart_1910342 : Nat := 118140960795 + 1910342 * 2 ^ 59
def prefixEnd_1910342 : Nat := 4983230072969 + 3 ^ 40 * 1910342 * 2
def baseEnd_1910342 : Nat := 435966071320653338595335

theorem tailTrace_1910342 : CollatzResearch.WordTrace tailWord_1910342 prefixEnd_1910342 435966071320653338595335 := by
  unfold tailWord_1910342
  simp only [CollatzResearch.WordTrace]
  refine ⟨2177371776411395915118415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 46450597896776446189192853 2177371776411395915118415)
  ·
    refine ⟨3266057664617093872677623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2177371776411395915118415 3266057664617093872677623)
    ·
      refine ⟨4899086496925640809016435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3266057664617093872677623 4899086496925640809016435)
      ·
        refine ⟨7348629745388461213524653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4899086496925640809016435 7348629745388461213524653)
        ·
          refine ⟨2755736154520672955071745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7348629745388461213524653 2755736154520672955071745)
          ·
            refine ⟨2066802115890504716303809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2755736154520672955071745 2066802115890504716303809)
            ·
              refine ⟨1550101586917878537227857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2066802115890504716303809 1550101586917878537227857)
              ·
                refine ⟨1162576190188408902920893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1550101586917878537227857 1162576190188408902920893)
                ·
                  refine ⟨435966071320653338595335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1162576190188408902920893 435966071320653338595335)
                  ·
                    rfl

theorem cell21_1910342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 2, 2, 3].length) (baseStart_1910342 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1910342 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1910342 prefixEnd_1910342 := by exact prefixLift 1910342
  have htrace : WordTrace (prefixWord ++ tailWord_1910342) baseStart_1910342 baseEnd_1910342 := by
    simpa [prefixWord, tailWord_1910342, baseEnd_1910342] using wordTrace_append hprefix tailTrace_1910342
  have hstable : (prefixWord ++ tailWord_1910342).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1910342).length < 2 ^ (prefixWord ++ tailWord_1910342).sum := by decide
  have hdescent : baseEnd_1910342 < baseStart_1910342 := by decide
  rcases family_descends (prefixWord ++ tailWord_1910342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1910474 : List Nat := [3, 1, 2, 1, 5, 2, 2, 1, 4]
def baseStart_1910474 : Nat := 118140960795 + 1910474 * 2 ^ 59
def prefixEnd_1910474 : Nat := 4983230072969 + 3 ^ 40 * 1910474 * 2
def baseEnd_1910474 : Nat := 435996195519050442395065

theorem tailTrace_1910474 : CollatzResearch.WordTrace tailWord_1910474 prefixEnd_1910474 435996195519050442395065 := by
  unfold tailWord_1910474
  simp only [CollatzResearch.WordTrace]
  refine ⟨17420177820171613956898619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46453807520457637218396317 17420177820171613956898619)
  ·
    refine ⟨26130266730257420935347929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17420177820171613956898619 26130266730257420935347929)
    ·
      refine ⟨19597700047693065701510947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26130266730257420935347929 19597700047693065701510947)
      ·
        refine ⟨29396550071539598552266421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19597700047693065701510947 29396550071539598552266421)
        ·
          refine ⟨2755926569206837364274977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29396550071539598552266421 2755926569206837364274977)
          ·
            refine ⟨2066944926905128023206233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2755926569206837364274977 2066944926905128023206233)
            ·
              refine ⟨1550208695178846017404675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2066944926905128023206233 1550208695178846017404675)
              ·
                refine ⟨2325313042768269026107013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1550208695178846017404675 2325313042768269026107013)
                ·
                  refine ⟨435996195519050442395065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2325313042768269026107013 435996195519050442395065)
                  ·
                    rfl

theorem cell21_1910474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 2, 1, 4].length) (baseStart_1910474 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1910474 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1910474 prefixEnd_1910474 := by exact prefixLift 1910474
  have htrace : WordTrace (prefixWord ++ tailWord_1910474) baseStart_1910474 baseEnd_1910474 := by
    simpa [prefixWord, tailWord_1910474, baseEnd_1910474] using wordTrace_append hprefix tailTrace_1910474
  have hstable : (prefixWord ++ tailWord_1910474).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1910474).length < 2 ^ (prefixWord ++ tailWord_1910474).sum := by decide
  have hdescent : baseEnd_1910474 < baseStart_1910474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1910474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1910513 : List Nat := [1, 2, 2, 2, 2, 12]
def baseStart_1910513 : Nat := 118140960795 + 1910513 * 2 ^ 59
def prefixEnd_1910513 : Nat := 4983230072969 + 3 ^ 40 * 1910513 * 2
def baseEnd_1910513 : Nat := 16148336883347964490555

theorem tailTrace_1910513 : CollatzResearch.WordTrace tailWord_1910513 prefixEnd_1910513 16148336883347964490555 := by
  unfold tailWord_1910513
  simp only [CollatzResearch.WordTrace]
  refine ⟨69682133727545165488264193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46454755818363443658842795 69682133727545165488264193)
  ·
    refine ⟨52261600295658874116198145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69682133727545165488264193 52261600295658874116198145)
    ·
      refine ⟨39196200221744155587148609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52261600295658874116198145 39196200221744155587148609)
      ·
        refine ⟨29397150166308116690361457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39196200221744155587148609 29397150166308116690361457)
        ·
          refine ⟨22047862624731087517771093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29397150166308116690361457 22047862624731087517771093)
          ·
            refine ⟨16148336883347964490555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 22047862624731087517771093 16148336883347964490555)
            ·
              rfl

theorem cell21_1910513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 12].length) (baseStart_1910513 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1910513 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1910513 prefixEnd_1910513 := by exact prefixLift 1910513
  have htrace : WordTrace (prefixWord ++ tailWord_1910513) baseStart_1910513 baseEnd_1910513 := by
    simpa [prefixWord, tailWord_1910513, baseEnd_1910513] using wordTrace_append hprefix tailTrace_1910513
  have hstable : (prefixWord ++ tailWord_1910513).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1910513).length < 2 ^ (prefixWord ++ tailWord_1910513).sum := by decide
  have hdescent : baseEnd_1910513 < baseStart_1910513 := by decide
  rcases family_descends (prefixWord ++ tailWord_1910513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1910578 : List Nat := [3, 2, 1, 1, 3, 2, 2, 4, 3]
def baseStart_1910578 : Nat := 118140960795 + 1910578 * 2 ^ 59
def prefixEnd_1910578 : Nat := 4983230072969 + 3 ^ 40 * 1910578 * 2
def baseEnd_1910578 : Nat := 436019929735969372661519

theorem tailTrace_1910578 : CollatzResearch.WordTrace tailWord_1910578 prefixEnd_1910578 436019929735969372661519 := by
  unfold tailWord_1910578
  simp only [CollatzResearch.WordTrace]
  refine ⟨17421126118077420397345097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46456336314873121059586925 17421126118077420397345097)
  ·
    refine ⟨13065844588558065298008823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17421126118077420397345097 13065844588558065298008823)
    ·
      refine ⟨19598766882837097947013235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13065844588558065298008823 19598766882837097947013235)
      ·
        refine ⟨29398150324255646920519853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19598766882837097947013235 29398150324255646920519853)
        ·
          refine ⟨11024306371595867595194945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29398150324255646920519853 11024306371595867595194945)
          ·
            refine ⟨8268229778696900696396209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11024306371595867595194945 8268229778696900696396209)
            ·
              refine ⟨6201172334022675522297157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8268229778696900696396209 6201172334022675522297157)
              ·
                refine ⟨1162719812629251660430717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6201172334022675522297157 1162719812629251660430717)
                ·
                  refine ⟨436019929735969372661519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1162719812629251660430717 436019929735969372661519)
                  ·
                    rfl

theorem cell21_1910578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 4, 3].length) (baseStart_1910578 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1910578 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1910578 prefixEnd_1910578 := by exact prefixLift 1910578
  have htrace : WordTrace (prefixWord ++ tailWord_1910578) baseStart_1910578 baseEnd_1910578 := by
    simpa [prefixWord, tailWord_1910578, baseEnd_1910578] using wordTrace_append hprefix tailTrace_1910578
  have hstable : (prefixWord ++ tailWord_1910578).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1910578).length < 2 ^ (prefixWord ++ tailWord_1910578).sum := by decide
  have hdescent : baseEnd_1910578 < baseStart_1910578 := by decide
  rcases family_descends (prefixWord ++ tailWord_1910578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1910637 : List Nat := [1, 5, 1, 1, 1, 1, 5, 1, 5]
def baseStart_1910637 : Nat := 118140960795 + 1910637 * 2 ^ 59
def prefixEnd_1910637 : Nat := 4983230072969 + 3 ^ 40 * 1910637 * 2
def baseEnd_1910637 : Nat := 436033394339798381178065

theorem tailTrace_1910637 : CollatzResearch.WordTrace tailWord_1910637 prefixEnd_1910637 436033394339798381178065 := by
  unfold tailWord_1910637
  simp only [CollatzResearch.WordTrace]
  refine ⟨69686656379095934665778165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46457770919397289777185443 69686656379095934665778165)
  ·
    refine ⟨6533124035540243874916703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 69686656379095934665778165 6533124035540243874916703)
    ·
      refine ⟨9799686053310365812375055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6533124035540243874916703 9799686053310365812375055)
      ·
        refine ⟨14699529079965548718562583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9799686053310365812375055 14699529079965548718562583)
        ·
          refine ⟨22049293619948323077843875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14699529079965548718562583 22049293619948323077843875)
          ·
            refine ⟨33073940429922484616765813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22049293619948323077843875 33073940429922484616765813)
            ·
              refine ⟨3100681915305232932821795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33073940429922484616765813 3100681915305232932821795)
              ·
                refine ⟨4651022872957849399232693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3100681915305232932821795 4651022872957849399232693)
                ·
                  refine ⟨436033394339798381178065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4651022872957849399232693 436033394339798381178065)
                  ·
                    rfl

theorem cell21_1910637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 5, 1, 5].length) (baseStart_1910637 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1910637 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1910637 prefixEnd_1910637 := by exact prefixLift 1910637
  have htrace : WordTrace (prefixWord ++ tailWord_1910637) baseStart_1910637 baseEnd_1910637 := by
    simpa [prefixWord, tailWord_1910637, baseEnd_1910637] using wordTrace_append hprefix tailTrace_1910637
  have hstable : (prefixWord ++ tailWord_1910637).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1910637).length < 2 ^ (prefixWord ++ tailWord_1910637).sum := by decide
  have hdescent : baseEnd_1910637 < baseStart_1910637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1910637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1910665 : List Nat := [1, 2, 1, 1, 5, 1, 1, 9]
def baseStart_1910665 : Nat := 118140960795 + 1910665 * 2 ^ 59
def prefixEnd_1910665 : Nat := 4983230072969 + 3 ^ 40 * 1910665 * 2
def baseEnd_1910665 : Nat := 145346594773758851570447

theorem tailTrace_1910665 : CollatzResearch.WordTrace tailWord_1910665 prefixEnd_1910665 145346594773758851570447 := by
  unfold tailWord_1910665
  simp only [CollatzResearch.WordTrace]
  refine ⟨69687677622994495447797449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46458451748662996965198299 69687677622994495447797449)
  ·
    refine ⟨52265758217245871585848087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69687677622994495447797449 52265758217245871585848087)
    ·
      refine ⟨78398637325868807378772131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52265758217245871585848087 78398637325868807378772131)
      ·
        refine ⟨117597955988803211068158197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78398637325868807378772131 117597955988803211068158197)
        ·
          refine ⟨11024808373950301037639831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 117597955988803211068158197 11024808373950301037639831)
          ·
            refine ⟨16537212560925451556459747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11024808373950301037639831 16537212560925451556459747)
            ·
              refine ⟨24805818841388177334689621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16537212560925451556459747 24805818841388177334689621)
              ·
                refine ⟨145346594773758851570447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24805818841388177334689621 145346594773758851570447)
                ·
                  rfl

theorem cell21_1910665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 9].length) (baseStart_1910665 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1910665 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1910665 prefixEnd_1910665 := by exact prefixLift 1910665
  have htrace : WordTrace (prefixWord ++ tailWord_1910665) baseStart_1910665 baseEnd_1910665 := by
    simpa [prefixWord, tailWord_1910665, baseEnd_1910665] using wordTrace_append hprefix tailTrace_1910665
  have hstable : (prefixWord ++ tailWord_1910665).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1910665).length < 2 ^ (prefixWord ++ tailWord_1910665).sum := by decide
  have hdescent : baseEnd_1910665 < baseStart_1910665 := by decide
  rcases family_descends (prefixWord ++ tailWord_1910665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1910716 : List Nat := [2, 2, 2, 5, 1, 1, 3, 5]
def baseStart_1910716 : Nat := 118140960795 + 1910716 * 2 ^ 59
def prefixEnd_1910716 : Nat := 4983230072969 + 3 ^ 40 * 1910716 * 2
def baseEnd_1910716 : Nat := 145350474405370599787079

theorem tailTrace_1910716 : CollatzResearch.WordTrace tailWord_1910716 prefixEnd_1910716 145350474405370599787079 := by
  unfold tailWord_1910716
  simp only [CollatzResearch.WordTrace]
  refine ⟨34844768872904865578952001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46459691830539820771936001 34844768872904865578952001)
  ·
    refine ⟨26133576654678649184214001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34844768872904865578952001 26133576654678649184214001)
    ·
      refine ⟨19600182491008986888160501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26133576654678649184214001 19600182491008986888160501)
      ·
        refine ⟨1837517108532092520765047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19600182491008986888160501 1837517108532092520765047)
        ·
          refine ⟨2756275662798138781147571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1837517108532092520765047 2756275662798138781147571)
          ·
            refine ⟨4134413494197208171721357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2756275662798138781147571 4134413494197208171721357)
            ·
              refine ⟨1550405060323953064395509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4134413494197208171721357 1550405060323953064395509)
              ·
                refine ⟨145350474405370599787079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1550405060323953064395509 145350474405370599787079)
                ·
                  rfl

theorem cell21_1910716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 3, 5].length) (baseStart_1910716 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1910716 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1910716 prefixEnd_1910716 := by exact prefixLift 1910716
  have htrace : WordTrace (prefixWord ++ tailWord_1910716) baseStart_1910716 baseEnd_1910716 := by
    simpa [prefixWord, tailWord_1910716, baseEnd_1910716] using wordTrace_append hprefix tailTrace_1910716
  have hstable : (prefixWord ++ tailWord_1910716).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1910716).length < 2 ^ (prefixWord ++ tailWord_1910716).sum := by decide
  have hdescent : baseEnd_1910716 < baseStart_1910716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1910716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1910882 : List Nat := [3, 3, 2, 2, 2, 1, 1, 2, 5]
def baseStart_1910882 : Nat := 118140960795 + 1910882 * 2 ^ 59
def prefixEnd_1910882 : Nat := 4983230072969 + 3 ^ 40 * 1910882 * 2
def baseEnd_1910882 : Nat := 436089306677732399594231

theorem tailTrace_1910882 : CollatzResearch.WordTrace tailWord_1910882 prefixEnd_1910882 436089306677732399594231 := by
  unfold tailWord_1910882
  simp only [CollatzResearch.WordTrace]
  refine ⟨17423898065802085377111725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46463728175472227672297933 17423898065802085377111725)
  ·
    refine ⟨6533961774675782016416897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17423898065802085377111725 6533961774675782016416897)
    ·
      refine ⟨4900471331006836512312673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6533961774675782016416897 4900471331006836512312673)
      ·
        refine ⟨3675353498255127384234505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4900471331006836512312673 3675353498255127384234505)
        ·
          refine ⟨2756515123691345538175879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3675353498255127384234505 2756515123691345538175879)
          ·
            refine ⟨4134772685537018307263819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2756515123691345538175879 4134772685537018307263819)
            ·
              refine ⟨6202159028305527460895729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4134772685537018307263819 6202159028305527460895729)
              ·
                refine ⟨4651619271229145595671797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6202159028305527460895729 4651619271229145595671797)
                ·
                  refine ⟨436089306677732399594231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4651619271229145595671797 436089306677732399594231)
                  ·
                    rfl

theorem cell21_1910882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 2, 5].length) (baseStart_1910882 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1910882 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1910882 prefixEnd_1910882 := by exact prefixLift 1910882
  have htrace : WordTrace (prefixWord ++ tailWord_1910882) baseStart_1910882 baseEnd_1910882 := by
    simpa [prefixWord, tailWord_1910882, baseEnd_1910882] using wordTrace_append hprefix tailTrace_1910882
  have hstable : (prefixWord ++ tailWord_1910882).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1910882).length < 2 ^ (prefixWord ++ tailWord_1910882).sum := by decide
  have hdescent : baseEnd_1910882 < baseStart_1910882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1910882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1910913 : List Nat := [1, 2, 4, 2, 3, 2, 1, 2, 4]
def baseStart_1910913 : Nat := 118140960795 + 1910913 * 2 ^ 59
def prefixEnd_1910913 : Nat := 4983230072969 + 3 ^ 40 * 1910913 * 2
def baseEnd_1910913 : Nat := 436096381300083234577501

theorem tailTrace_1910913 : CollatzResearch.WordTrace tailWord_1910913 prefixEnd_1910913 436096381300083234577501 := by
  unfold tailWord_1910913
  simp only [CollatzResearch.WordTrace]
  refine ⟨69696722926096033802825393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46464481950730689201883595 69696722926096033802825393)
  ·
    refine ⟨52272542194572025352119045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69696722926096033802825393 52272542194572025352119045)
    ·
      refine ⟨9801101661482254753522321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52272542194572025352119045 9801101661482254753522321)
      ·
        refine ⟨7350826246111691065141741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9801101661482254753522321 7350826246111691065141741)
        ·
          refine ⟨2756559842291884149428153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7350826246111691065141741 2756559842291884149428153)
          ·
            refine ⟨2067419881718913112071115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2756559842291884149428153 2067419881718913112071115)
            ·
              refine ⟨3101129822578369668106673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2067419881718913112071115 3101129822578369668106673)
              ·
                refine ⟨2325847366933777251080005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3101129822578369668106673 2325847366933777251080005)
                ·
                  refine ⟨436096381300083234577501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2325847366933777251080005 436096381300083234577501)
                  ·
                    rfl

theorem cell21_1910913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 1, 2, 4].length) (baseStart_1910913 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1910913 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1910913 prefixEnd_1910913 := by exact prefixLift 1910913
  have htrace : WordTrace (prefixWord ++ tailWord_1910913) baseStart_1910913 baseEnd_1910913 := by
    simpa [prefixWord, tailWord_1910913, baseEnd_1910913] using wordTrace_append hprefix tailTrace_1910913
  have hstable : (prefixWord ++ tailWord_1910913).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1910913).length < 2 ^ (prefixWord ++ tailWord_1910913).sum := by decide
  have hdescent : baseEnd_1910913 < baseStart_1910913 := by decide
  rcases family_descends (prefixWord ++ tailWord_1910913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911034 : List Nat := [3, 1, 1, 1, 1, 5, 4, 2, 3]
def baseStart_1911034 : Nat := 118140960795 + 1911034 * 2 ^ 59
def prefixEnd_1911034 : Nat := 4983230072969 + 3 ^ 40 * 1911034 * 2
def baseEnd_1911034 : Nat := 436123995148613913060587

theorem tailTrace_1911034 : CollatzResearch.WordTrace tailWord_1911034 prefixEnd_1911034 436123995148613913060587 := by
  unfold tailWord_1911034
  simp only [CollatzResearch.WordTrace]
  refine ⟨17425284039664417866995039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46467424105771780978653437 17425284039664417866995039)
  ·
    refine ⟨26137926059496626800492559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17425284039664417866995039 26137926059496626800492559)
    ·
      refine ⟨39206889089244940200738839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26137926059496626800492559 39206889089244940200738839)
      ·
        refine ⟨58810333633867410301108259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39206889089244940200738839 58810333633867410301108259)
        ·
          refine ⟨88215500450801115451662389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58810333633867410301108259 88215500450801115451662389)
          ·
            refine ⟨8270203167262604573593349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 88215500450801115451662389 8270203167262604573593349)
            ·
              refine ⟨1550663093861738357548753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8270203167262604573593349 1550663093861738357548753)
              ·
                refine ⟨1162997320396303768161565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1550663093861738357548753 1162997320396303768161565)
                ·
                  refine ⟨436123995148613913060587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1162997320396303768161565 436123995148613913060587)
                  ·
                    rfl

theorem cell21_1911034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 4, 2, 3].length) (baseStart_1911034 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1911034 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1911034 prefixEnd_1911034 := by exact prefixLift 1911034
  have htrace : WordTrace (prefixWord ++ tailWord_1911034) baseStart_1911034 baseEnd_1911034 := by
    simpa [prefixWord, tailWord_1911034, baseEnd_1911034] using wordTrace_append hprefix tailTrace_1911034
  have hstable : (prefixWord ++ tailWord_1911034).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911034).length < 2 ^ (prefixWord ++ tailWord_1911034).sum := by decide
  have hdescent : baseEnd_1911034 < baseStart_1911034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911082 : List Nat := [3, 1, 4, 2, 3, 1, 1, 2, 4]
def baseStart_1911082 : Nat := 118140960795 + 1911082 * 2 ^ 59
def prefixEnd_1911082 : Nat := 4983230072969 + 3 ^ 40 * 1911082 * 2
def baseEnd_1911082 : Nat := 436134949402576496260489

theorem tailTrace_1911082 : CollatzResearch.WordTrace tailWord_1911082 prefixEnd_1911082 436134949402576496260489 := by
  unfold tailWord_1911082
  simp only [CollatzResearch.WordTrace]
  refine ⟨17425721715620943916431875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46468591241655850443818333 17425721715620943916431875)
  ·
    refine ⟨26138582573431415874647813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17425721715620943916431875 26138582573431415874647813)
    ·
      refine ⟨4900984232518390476496465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26138582573431415874647813 4900984232518390476496465)
      ·
        refine ⟨3675738174388792857372349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4900984232518390476496465 3675738174388792857372349)
        ·
          refine ⟨1378401815395797321514631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3675738174388792857372349 1378401815395797321514631)
          ·
            refine ⟨2067602723093695982271947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1378401815395797321514631 2067602723093695982271947)
            ·
              refine ⟨3101404084640543973407921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2067602723093695982271947 3101404084640543973407921)
              ·
                refine ⟨2326053063480407980055941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3101404084640543973407921 2326053063480407980055941)
                ·
                  refine ⟨436134949402576496260489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2326053063480407980055941 436134949402576496260489)
                  ·
                    rfl

theorem cell21_1911082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 1, 2, 4].length) (baseStart_1911082 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1911082 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1911082 prefixEnd_1911082 := by exact prefixLift 1911082
  have htrace : WordTrace (prefixWord ++ tailWord_1911082) baseStart_1911082 baseEnd_1911082 := by
    simpa [prefixWord, tailWord_1911082, baseEnd_1911082] using wordTrace_append hprefix tailTrace_1911082
  have hstable : (prefixWord ++ tailWord_1911082).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911082).length < 2 ^ (prefixWord ++ tailWord_1911082).sum := by decide
  have hdescent : baseEnd_1911082 < baseStart_1911082 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911093 : List Nat := [1, 3, 3, 1, 2, 1, 1, 6, 3]
def baseStart_1911093 : Nat := 118140960795 + 1911093 * 2 ^ 59
def prefixEnd_1911093 : Nat := 4983230072969 + 3 ^ 40 * 1911093 * 2
def baseEnd_1911093 : Nat := 436137459752442921577133

theorem tailTrace_1911093 : CollatzResearch.WordTrace tailWord_1911093 prefixEnd_1911093 436137459752442921577133 := by
  unfold tailWord_1911093
  simp only [CollatzResearch.WordTrace]
  refine ⟨69703288065443924544377933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46468858710295949696251955 69703288065443924544377933)
  ·
    refine ⟨26138733024541471704141725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69703288065443924544377933 26138733024541471704141725)
    ·
      refine ⟨9802024884203051889053147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26138733024541471704141725 9802024884203051889053147)
      ·
        refine ⟨14703037326304577833579721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9802024884203051889053147 14703037326304577833579721)
        ·
          refine ⟨11027277994728433375184791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14703037326304577833579721 11027277994728433375184791)
          ·
            refine ⟨16540916992092650062777187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11027277994728433375184791 16540916992092650062777187)
            ·
              refine ⟨24811375488138975094165781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16540916992092650062777187 24811375488138975094165781)
              ·
                refine ⟨1163033226006514457539021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 24811375488138975094165781 1163033226006514457539021)
                ·
                  refine ⟨436137459752442921577133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1163033226006514457539021 436137459752442921577133)
                  ·
                    rfl

theorem cell21_1911093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 6, 3].length) (baseStart_1911093 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1911093 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1911093 prefixEnd_1911093 := by exact prefixLift 1911093
  have htrace : WordTrace (prefixWord ++ tailWord_1911093) baseStart_1911093 baseEnd_1911093 := by
    simpa [prefixWord, tailWord_1911093, baseEnd_1911093] using wordTrace_append hprefix tailTrace_1911093
  have hstable : (prefixWord ++ tailWord_1911093).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911093).length < 2 ^ (prefixWord ++ tailWord_1911093).sum := by decide
  have hdescent : baseEnd_1911093 < baseStart_1911093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911121 : List Nat := [1, 2, 2, 1, 4, 3, 1, 7]
def baseStart_1911121 : Nat := 118140960795 + 1911121 * 2 ^ 59
def prefixEnd_1911121 : Nat := 4983230072969 + 3 ^ 40 * 1911121 * 2
def baseEnd_1911121 : Nat := 145381283244640365036803

theorem tailTrace_1911121 : CollatzResearch.WordTrace tailWord_1911121 prefixEnd_1911121 145381283244640365036803 := by
  unfold tailWord_1911121
  simp only [CollatzResearch.WordTrace]
  refine ⟨69704309309342485326397217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46469539539561656884264811 69704309309342485326397217)
  ·
    refine ⟨52278231982006863994797913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69704309309342485326397217 52278231982006863994797913)
    ·
      refine ⟨39208673986505147996098435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52278231982006863994797913 39208673986505147996098435)
      ·
        refine ⟨58813010979757721994147653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39208673986505147996098435 58813010979757721994147653)
        ·
          refine ⟨11027439558704572873902685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58813010979757721994147653 11027439558704572873902685)
          ·
            refine ⟨4135289834514214827713507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11027439558704572873902685 4135289834514214827713507)
            ·
              refine ⟨6202934751771322241570261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4135289834514214827713507 6202934751771322241570261)
              ·
                refine ⟨145381283244640365036803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6202934751771322241570261 145381283244640365036803)
                ·
                  rfl

theorem cell21_1911121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 7].length) (baseStart_1911121 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1911121 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1911121 prefixEnd_1911121 := by exact prefixLift 1911121
  have htrace : WordTrace (prefixWord ++ tailWord_1911121) baseStart_1911121 baseEnd_1911121 := by
    simpa [prefixWord, tailWord_1911121, baseEnd_1911121] using wordTrace_append hprefix tailTrace_1911121
  have hstable : (prefixWord ++ tailWord_1911121).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911121).length < 2 ^ (prefixWord ++ tailWord_1911121).sum := by decide
  have hdescent : baseEnd_1911121 < baseStart_1911121 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911135 : List Nat := [1, 1, 2, 3, 1, 2, 2, 2, 7]
def baseStart_1911135 : Nat := 118140960795 + 1911135 * 2 ^ 59
def prefixEnd_1911135 : Nat := 4983230072969 + 3 ^ 40 * 1911135 * 2
def baseEnd_1911135 : Nat := 436147044724660181877047

theorem tailTrace_1911135 : CollatzResearch.WordTrace tailWord_1911135 prefixEnd_1911135 436147044724660181877047 := by
  unfold tailWord_1911135
  simp only [CollatzResearch.WordTrace]
  refine ⟨69704819931291765717406859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46469879954194510478271239 69704819931291765717406859)
  ·
    refine ⟨104557229896937648576110289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69704819931291765717406859 104557229896937648576110289)
    ·
      refine ⟨78417922422703236432082717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104557229896937648576110289 78417922422703236432082717)
      ·
        refine ⟨29406720908513713662031019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78417922422703236432082717 29406720908513713662031019)
        ·
          refine ⟨44110081362770570493046529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29406720908513713662031019 44110081362770570493046529)
          ·
            refine ⟨33082561022077927869784897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44110081362770570493046529 33082561022077927869784897)
            ·
              refine ⟨24811920766558445902338673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33082561022077927869784897 24811920766558445902338673)
              ·
                refine ⟨18608940574918834426754005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24811920766558445902338673 18608940574918834426754005)
                ·
                  refine ⟨436147044724660181877047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18608940574918834426754005 436147044724660181877047)
                  ·
                    rfl

theorem cell21_1911135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 2, 7].length) (baseStart_1911135 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1911135 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1911135 prefixEnd_1911135 := by exact prefixLift 1911135
  have htrace : WordTrace (prefixWord ++ tailWord_1911135) baseStart_1911135 baseEnd_1911135 := by
    simpa [prefixWord, tailWord_1911135, baseEnd_1911135] using wordTrace_append hprefix tailTrace_1911135
  have hstable : (prefixWord ++ tailWord_1911135).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911135).length < 2 ^ (prefixWord ++ tailWord_1911135).sum := by decide
  have hdescent : baseEnd_1911135 < baseStart_1911135 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911138 : List Nat := [3, 3, 2, 1, 1, 4, 7]
def baseStart_1911138 : Nat := 118140960795 + 1911138 * 2 ^ 59
def prefixEnd_1911138 : Nat := 4983230072969 + 3 ^ 40 * 1911138 * 2
def baseEnd_1911138 : Nat := 48460858818392538147449

theorem tailTrace_1911138 : CollatzResearch.WordTrace tailWord_1911138 prefixEnd_1911138 48460858818392538147449 := by
  unfold tailWord_1911138
  simp only [CollatzResearch.WordTrace]
  refine ⟨17426232337570224307441517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46469952900187264819844045 17426232337570224307441517)
  ·
    refine ⟨6534837126588834115290569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17426232337570224307441517 6534837126588834115290569)
    ·
      refine ⟨4901127844941625586467927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6534837126588834115290569 4901127844941625586467927)
      ·
        refine ⟨7351691767412438379701891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4901127844941625586467927 7351691767412438379701891)
        ·
          refine ⟨11027537651118657569552837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7351691767412438379701891 11027537651118657569552837)
          ·
            refine ⟨2067663309584748294291157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11027537651118657569552837 2067663309584748294291157)
            ·
              refine ⟨48460858818392538147449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2067663309584748294291157 48460858818392538147449)
              ·
                rfl

theorem cell21_1911138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 7].length) (baseStart_1911138 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1911138 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1911138 prefixEnd_1911138 := by exact prefixLift 1911138
  have htrace : WordTrace (prefixWord ++ tailWord_1911138) baseStart_1911138 baseEnd_1911138 := by
    simpa [prefixWord, tailWord_1911138, baseEnd_1911138] using wordTrace_append hprefix tailTrace_1911138
  have hstable : (prefixWord ++ tailWord_1911138).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911138).length < 2 ^ (prefixWord ++ tailWord_1911138).sum := by decide
  have hdescent : baseEnd_1911138 < baseStart_1911138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911152 : List Nat := [2, 1, 1, 1, 4, 3, 3, 1, 5]
def baseStart_1911152 : Nat := 118140960795 + 1911152 * 2 ^ 59
def prefixEnd_1911152 : Nat := 4983230072969 + 3 ^ 40 * 1911152 * 2
def baseEnd_1911152 : Nat := 436150924356271930093679

theorem tailTrace_1911152 : CollatzResearch.WordTrace tailWord_1911152 prefixEnd_1911152 436150924356271930093679 := by
  unfold tailWord_1911152
  simp only [CollatzResearch.WordTrace]
  refine ⟨34852719986115088810387855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46470293314820118413850473 34852719986115088810387855)
  ·
    refine ⟨52279079979172633215581783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34852719986115088810387855 52279079979172633215581783)
    ·
      refine ⟨78418619968758949823372675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52279079979172633215581783 78418619968758949823372675)
      ·
        refine ⟨117627929953138424735059013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78418619968758949823372675 117627929953138424735059013)
        ·
          refine ⟨22055236866213454637823565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117627929953138424735059013 22055236866213454637823565)
          ·
            refine ⟨8270713824830045489183837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22055236866213454637823565 8270713824830045489183837)
            ·
              refine ⟨3101517684311267058443939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8270713824830045489183837 3101517684311267058443939)
              ·
                refine ⟨4652276526466900587665909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3101517684311267058443939 4652276526466900587665909)
                ·
                  refine ⟨436150924356271930093679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4652276526466900587665909 436150924356271930093679)
                  ·
                    rfl

theorem cell21_1911152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 3, 1, 5].length) (baseStart_1911152 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1911152 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1911152 prefixEnd_1911152 := by exact prefixLift 1911152
  have htrace : WordTrace (prefixWord ++ tailWord_1911152) baseStart_1911152 baseEnd_1911152 := by
    simpa [prefixWord, tailWord_1911152, baseEnd_1911152] using wordTrace_append hprefix tailTrace_1911152
  have hstable : (prefixWord ++ tailWord_1911152).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911152).length < 2 ^ (prefixWord ++ tailWord_1911152).sum := by decide
  have hdescent : baseEnd_1911152 < baseStart_1911152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911197 : List Nat := [1, 4, 2, 1, 4, 9]
def baseStart_1911197 : Nat := 118140960795 + 1911197 * 2 ^ 59
def prefixEnd_1911197 : Nat := 4983230072969 + 3 ^ 40 * 1911197 * 2
def baseEnd_1911197 : Nat := 16154118295161550068281

theorem tailTrace_1911197 : CollatzResearch.WordTrace tailWord_1911197 prefixEnd_1911197 16154118295161550068281 := by
  unfold tailWord_1911197
  simp only [CollatzResearch.WordTrace]
  refine ⟨69707081257067150306163845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46471387504711433537442563 69707081257067150306163845)
  ·
    refine ⟨13070077735700090682405721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69707081257067150306163845 13070077735700090682405721)
    ·
      refine ⟨9802558301775068011804291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13070077735700090682405721 9802558301775068011804291)
      ·
        refine ⟨14703837452662602017706437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9802558301775068011804291 14703837452662602017706437)
        ·
          refine ⟨2756969522374237878319957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14703837452662602017706437 2756969522374237878319957)
          ·
            refine ⟨16154118295161550068281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2756969522374237878319957 16154118295161550068281)
            ·
              rfl

theorem cell21_1911197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 9].length) (baseStart_1911197 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1911197 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1911197 prefixEnd_1911197 := by exact prefixLift 1911197
  have htrace : WordTrace (prefixWord ++ tailWord_1911197) baseStart_1911197 baseEnd_1911197 := by
    simpa [prefixWord, tailWord_1911197, baseEnd_1911197] using wordTrace_append hprefix tailTrace_1911197
  have hstable : (prefixWord ++ tailWord_1911197).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911197).length < 2 ^ (prefixWord ++ tailWord_1911197).sum := by decide
  have hdescent : baseEnd_1911197 < baseStart_1911197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911228 : List Nat := [2, 2, 2, 4, 1, 1, 1, 1, 7]
def baseStart_1911228 : Nat := 118140960795 + 1911228 * 2 ^ 59
def prefixEnd_1911228 : Nat := 4983230072969 + 3 ^ 40 * 1911228 * 2
def baseEnd_1911228 : Nat := 436168268591712686826857

theorem tailTrace_1911228 : CollatzResearch.WordTrace tailWord_1911228 prefixEnd_1911228 436168268591712686826857 := by
  unfold tailWord_1911228
  simp only [CollatzResearch.WordTrace]
  refine ⟨34854105959977421300271169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46472141279969895067028225 34854105959977421300271169)
  ·
    refine ⟨26140579469983065975203377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34854105959977421300271169 26140579469983065975203377)
    ·
      refine ⟨19605434602487299481402533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26140579469983065975203377 19605434602487299481402533)
      ·
        refine ⟨3676018987966368652762975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19605434602487299481402533 3676018987966368652762975)
        ·
          refine ⟨5514028481949552979144463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3676018987966368652762975 5514028481949552979144463)
          ·
            refine ⟨8271042722924329468716695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5514028481949552979144463 8271042722924329468716695)
            ·
              refine ⟨12406564084386494203075043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8271042722924329468716695 12406564084386494203075043)
              ·
                refine ⟨18609846126579741304612565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12406564084386494203075043 18609846126579741304612565)
                ·
                  refine ⟨436168268591712686826857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18609846126579741304612565 436168268591712686826857)
                  ·
                    rfl

theorem cell21_1911228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 1, 7].length) (baseStart_1911228 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1911228 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1911228 prefixEnd_1911228 := by exact prefixLift 1911228
  have htrace : WordTrace (prefixWord ++ tailWord_1911228) baseStart_1911228 baseEnd_1911228 := by
    simpa [prefixWord, tailWord_1911228, baseEnd_1911228] using wordTrace_append hprefix tailTrace_1911228
  have hstable : (prefixWord ++ tailWord_1911228).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911228).length < 2 ^ (prefixWord ++ tailWord_1911228).sum := by decide
  have hdescent : baseEnd_1911228 < baseStart_1911228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911242 : List Nat := [3, 1, 2, 1, 2, 2, 2, 2, 6]
def baseStart_1911242 : Nat := 118140960795 + 1911242 * 2 ^ 59
def prefixEnd_1911242 : Nat := 4983230072969 + 3 ^ 40 * 1911242 * 2
def baseEnd_1911242 : Nat := 436171463582451773593495

theorem tailTrace_1911242 : CollatzResearch.WordTrace tailWord_1911242 prefixEnd_1911242 436171463582451773593495 := by
  unfold tailWord_1911242
  simp only [CollatzResearch.WordTrace]
  refine ⟨17427180635476030747887995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46472481694602748661034653 17427180635476030747887995)
  ·
    refine ⟨26140770953214046121831993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17427180635476030747887995 26140770953214046121831993)
    ·
      refine ⟨19605578214910534591373995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26140770953214046121831993 19605578214910534591373995)
      ·
        refine ⟨29408367322365801887060993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19605578214910534591373995 29408367322365801887060993)
        ·
          refine ⟨22056275491774351415295745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29408367322365801887060993 22056275491774351415295745)
          ·
            refine ⟨16542206618830763561471809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22056275491774351415295745 16542206618830763561471809)
            ·
              refine ⟨12406654964123072671103857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16542206618830763561471809 12406654964123072671103857)
              ·
                refine ⟨9304991223092304503327893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12406654964123072671103857 9304991223092304503327893)
                ·
                  refine ⟨436171463582451773593495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9304991223092304503327893 436171463582451773593495)
                  ·
                    rfl

theorem cell21_1911242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 2, 6].length) (baseStart_1911242 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1911242 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1911242 prefixEnd_1911242 := by exact prefixLift 1911242
  have htrace : WordTrace (prefixWord ++ tailWord_1911242) baseStart_1911242 baseEnd_1911242 := by
    simpa [prefixWord, tailWord_1911242, baseEnd_1911242] using wordTrace_append hprefix tailTrace_1911242
  have hstable : (prefixWord ++ tailWord_1911242).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911242).length < 2 ^ (prefixWord ++ tailWord_1911242).sum := by decide
  have hdescent : baseEnd_1911242 < baseStart_1911242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911366 : List Nat := [6, 1, 1, 1, 2, 10]
def baseStart_1911366 : Nat := 118140960795 + 1911366 * 2 ^ 59
def prefixEnd_1911366 : Nat := 4983230072969 + 3 ^ 40 * 1911366 * 2
def baseEnd_1911366 : Nat := 16155546743402041241725

theorem tailTrace_1911366 : CollatzResearch.WordTrace tailWord_1911366 prefixEnd_1911366 16155546743402041241725 := by
  unfold tailWord_1911366
  simp only [CollatzResearch.WordTrace]
  refine ⟨2178538912295465380283311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 46475496795636594779377301 2178538912295465380283311)
  ·
    refine ⟨3267808368443198070424967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2178538912295465380283311 3267808368443198070424967)
    ·
      refine ⟨4901712552664797105637451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3267808368443198070424967 4901712552664797105637451)
      ·
        refine ⟨7352568828997195658456177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4901712552664797105637451 7352568828997195658456177)
        ·
          refine ⟨5514426621747896743842133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7352568828997195658456177 5514426621747896743842133)
          ·
            refine ⟨16155546743402041241725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5514426621747896743842133 16155546743402041241725)
            ·
              rfl

theorem cell21_1911366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 10].length) (baseStart_1911366 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1911366 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1911366 prefixEnd_1911366 := by exact prefixLift 1911366
  have htrace : WordTrace (prefixWord ++ tailWord_1911366) baseStart_1911366 baseEnd_1911366 := by
    simpa [prefixWord, tailWord_1911366, baseEnd_1911366] using wordTrace_append hprefix tailTrace_1911366
  have hstable : (prefixWord ++ tailWord_1911366).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911366).length < 2 ^ (prefixWord ++ tailWord_1911366).sum := by decide
  have hdescent : baseEnd_1911366 < baseStart_1911366 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911428 : List Nat := [2, 3, 2, 1, 3, 3, 1, 2, 4]
def baseStart_1911428 : Nat := 118140960795 + 1911428 * 2 ^ 59
def prefixEnd_1911428 : Nat := 4983230072969 + 3 ^ 40 * 1911428 * 2
def baseEnd_1911428 : Nat := 436213911316556783493115

theorem tailTrace_1911428 : CollatzResearch.WordTrace tailWord_1911428 prefixEnd_1911428 436213911316556783493115 := by
  unfold tailWord_1911428
  simp only [CollatzResearch.WordTrace]
  refine ⟨34857753259615138378911469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46477004346153517838548625 34857753259615138378911469)
  ·
    refine ⟨13071657472355676892091801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34857753259615138378911469 13071657472355676892091801)
    ·
      refine ⟨9803743104266757669068851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13071657472355676892091801 9803743104266757669068851)
      ·
        refine ⟨14705614656400136503603277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9803743104266757669068851 14705614656400136503603277)
        ·
          refine ⟨5514605496150051188851229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14705614656400136503603277 5514605496150051188851229)
          ·
            refine ⟨2067977061056269195819211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5514605496150051188851229 2067977061056269195819211)
            ·
              refine ⟨3101965591584403793728817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2067977061056269195819211 3101965591584403793728817)
              ·
                refine ⟨2326474193688302845296613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3101965591584403793728817 2326474193688302845296613)
                ·
                  refine ⟨436213911316556783493115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2326474193688302845296613 436213911316556783493115)
                  ·
                    rfl

theorem cell21_1911428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 1, 2, 4].length) (baseStart_1911428 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1911428 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1911428 prefixEnd_1911428 := by exact prefixLift 1911428
  have htrace : WordTrace (prefixWord ++ tailWord_1911428) baseStart_1911428 baseEnd_1911428 := by
    simpa [prefixWord, tailWord_1911428, baseEnd_1911428] using wordTrace_append hprefix tailTrace_1911428
  have hstable : (prefixWord ++ tailWord_1911428).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911428).length < 2 ^ (prefixWord ++ tailWord_1911428).sum := by decide
  have hdescent : baseEnd_1911428 < baseStart_1911428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911529 : List Nat := [1, 2, 1, 1, 1, 2, 4, 1, 8]
def baseStart_1911529 : Nat := 118140960795 + 1911529 * 2 ^ 59
def prefixEnd_1911529 : Nat := 4983230072969 + 3 ^ 40 * 1911529 * 2
def baseEnd_1911529 : Nat := 436236960892603052309575

theorem tailTrace_1911529 : CollatzResearch.WordTrace tailWord_1911529 prefixEnd_1911529 436236960892603052309575 := by
  unfold tailWord_1911529
  simp only [CollatzResearch.WordTrace]
  refine ⟨69719190291864371007249641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46479460194576247338166427 69719190291864371007249641)
  ·
    refine ⟨52289392718898278255437231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69719190291864371007249641 52289392718898278255437231)
    ·
      refine ⟨78434089078347417383155847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52289392718898278255437231 78434089078347417383155847)
      ·
        refine ⟨117651133617521126074733771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78434089078347417383155847 117651133617521126074733771)
        ·
          refine ⟨176476700426281689112100657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117651133617521126074733771 176476700426281689112100657)
          ·
            refine ⟨132357525319711266834075493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176476700426281689112100657 132357525319711266834075493)
            ·
              refine ⟨24817035997445862531389155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 132357525319711266834075493 24817035997445862531389155)
              ·
                refine ⟨37225553996168793797083733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24817035997445862531389155 37225553996168793797083733)
                ·
                  refine ⟨436236960892603052309575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37225553996168793797083733 436236960892603052309575)
                  ·
                    rfl

theorem cell21_1911529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 8].length) (baseStart_1911529 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1911529 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1911529 prefixEnd_1911529 := by exact prefixLift 1911529
  have htrace : WordTrace (prefixWord ++ tailWord_1911529) baseStart_1911529 baseEnd_1911529 := by
    simpa [prefixWord, tailWord_1911529, baseEnd_1911529] using wordTrace_append hprefix tailTrace_1911529
  have hstable : (prefixWord ++ tailWord_1911529).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911529).length < 2 ^ (prefixWord ++ tailWord_1911529).sum := by decide
  have hdescent : baseEnd_1911529 < baseStart_1911529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911532 : List Nat := [2, 2, 1, 1, 2, 2, 1, 7, 3]
def baseStart_1911532 : Nat := 118140960795 + 1911532 * 2 ^ 59
def prefixEnd_1911532 : Nat := 4983230072969 + 3 ^ 40 * 1911532 * 2
def baseEnd_1911532 : Nat := 436237645533475713759569

theorem tailTrace_1911532 : CollatzResearch.WordTrace tailWord_1911532 prefixEnd_1911532 436237645533475713759569 := by
  unfold tailWord_1911532
  simp only [CollatzResearch.WordTrace]
  refine ⟨34859649855426751259804425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46479533140569001679739233 34859649855426751259804425)
  ·
    refine ⟨26144737391570063444853319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34859649855426751259804425 26144737391570063444853319)
    ·
      refine ⟨39217106087355095167279979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26144737391570063444853319 39217106087355095167279979)
      ·
        refine ⟨58825659131032642750919969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39217106087355095167279979 58825659131032642750919969)
        ·
          refine ⟨44119244348274482063189977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58825659131032642750919969 44119244348274482063189977)
          ·
            refine ⟨33089433261205861547392483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44119244348274482063189977 33089433261205861547392483)
            ·
              refine ⟨49634149891808792321088725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33089433261205861547392483 49634149891808792321088725)
              ·
                refine ⟨1163300388089268570025517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 49634149891808792321088725 1163300388089268570025517)
                ·
                  refine ⟨436237645533475713759569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1163300388089268570025517 436237645533475713759569)
                  ·
                    rfl

theorem cell21_1911532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 7, 3].length) (baseStart_1911532 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1911532 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1911532 prefixEnd_1911532 := by exact prefixLift 1911532
  have htrace : WordTrace (prefixWord ++ tailWord_1911532) baseStart_1911532 baseEnd_1911532 := by
    simpa [prefixWord, tailWord_1911532, baseEnd_1911532] using wordTrace_append hprefix tailTrace_1911532
  have hstable : (prefixWord ++ tailWord_1911532).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911532).length < 2 ^ (prefixWord ++ tailWord_1911532).sum := by decide
  have hdescent : baseEnd_1911532 < baseStart_1911532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911541 : List Nat := [1, 3, 6, 1, 1, 2, 2, 2, 3]
def baseStart_1911541 : Nat := 118140960795 + 1911541 * 2 ^ 59
def prefixEnd_1911541 : Nat := 4983230072969 + 3 ^ 40 * 1911541 * 2
def baseEnd_1911541 : Nat := 436239699456093698109551

theorem tailTrace_1911541 : CollatzResearch.WordTrace tailWord_1911541 prefixEnd_1911541 436239699456093698109551 := by
  unfold tailWord_1911541
  simp only [CollatzResearch.WordTrace]
  refine ⟨69719627967820897056686477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46479751978547264704457651 69719627967820897056686477)
  ·
    refine ⟨26144860487932836396257429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69719627967820897056686477 26144860487932836396257429)
    ·
      refine ⟨1225540335371851706074567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 26144860487932836396257429 1225540335371851706074567)
      ·
        refine ⟨1838310503057777559111851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1225540335371851706074567 1838310503057777559111851)
        ·
          refine ⟨2757465754586666338667777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1838310503057777559111851 2757465754586666338667777)
          ·
            refine ⟨2068099315939999754000833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2757465754586666338667777 2068099315939999754000833)
            ·
              refine ⟨1551074486954999815500625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2068099315939999754000833 1551074486954999815500625)
              ·
                refine ⟨1163305865216249861625469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1551074486954999815500625 1163305865216249861625469)
                ·
                  refine ⟨436239699456093698109551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1163305865216249861625469 436239699456093698109551)
                  ·
                    rfl

theorem cell21_1911541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 2, 2, 3].length) (baseStart_1911541 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1911541 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1911541 prefixEnd_1911541 := by exact prefixLift 1911541
  have htrace : WordTrace (prefixWord ++ tailWord_1911541) baseStart_1911541 baseEnd_1911541 := by
    simpa [prefixWord, tailWord_1911541, baseEnd_1911541] using wordTrace_append hprefix tailTrace_1911541
  have hstable : (prefixWord ++ tailWord_1911541).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911541).length < 2 ^ (prefixWord ++ tailWord_1911541).sum := by decide
  have hdescent : baseEnd_1911541 < baseStart_1911541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911546 : List Nat := [3, 1, 1, 1, 1, 3, 3, 4, 4]
def baseStart_1911546 : Nat := 118140960795 + 1911546 * 2 ^ 59
def prefixEnd_1911546 : Nat := 4983230072969 + 3 ^ 40 * 1911546 * 2
def baseEnd_1911546 : Nat := 436240840524214800526207

theorem tailTrace_1911546 : CollatzResearch.WordTrace tailWord_1911546 prefixEnd_1911546 436240840524214800526207 := by
  unfold tailWord_1911546
  simp only [CollatzResearch.WordTrace]
  refine ⟨17429952583200695727654623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46479873555201855273745661 17429952583200695727654623)
  ·
    refine ⟨26144928874801043591481935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17429952583200695727654623 26144928874801043591481935)
    ·
      refine ⟨39217393312201565387222903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26144928874801043591481935 39217393312201565387222903)
      ·
        refine ⟨58826089968302348080834355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39217393312201565387222903 58826089968302348080834355)
        ·
          refine ⟨88239134952453522121251533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58826089968302348080834355 88239134952453522121251533)
          ·
            refine ⟨33089675607170070795469325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88239134952453522121251533 33089675607170070795469325)
            ·
              refine ⟨12408628352688776548300997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33089675607170070795469325 12408628352688776548300997)
              ·
                refine ⟨2326617816129145602806437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12408628352688776548300997 2326617816129145602806437)
                ·
                  refine ⟨436240840524214800526207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2326617816129145602806437 436240840524214800526207)
                  ·
                    rfl

theorem cell21_1911546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 4, 4].length) (baseStart_1911546 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1911546 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1911546 prefixEnd_1911546 := by exact prefixLift 1911546
  have htrace : WordTrace (prefixWord ++ tailWord_1911546) baseStart_1911546 baseEnd_1911546 := by
    simpa [prefixWord, tailWord_1911546, baseEnd_1911546] using wordTrace_append hprefix tailTrace_1911546
  have hstable : (prefixWord ++ tailWord_1911546).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911546).length < 2 ^ (prefixWord ++ tailWord_1911546).sum := by decide
  have hdescent : baseEnd_1911546 < baseStart_1911546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911594 : List Nat := [3, 1, 4, 3, 1, 1, 8]
def baseStart_1911594 : Nat := 118140960795 + 1911594 * 2 ^ 59
def prefixEnd_1911594 : Nat := 4983230072969 + 3 ^ 40 * 1911594 * 2
def baseEnd_1911594 : Nat := 48472421642019709302901

theorem tailTrace_1911594 : CollatzResearch.WordTrace tailWord_1911594 prefixEnd_1911594 48472421642019709302901 := by
  unfold tailWord_1911594
  simp only [CollatzResearch.WordTrace]
  refine ⟨17430390259157221777091459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46481040691085924738910557 17430390259157221777091459)
  ·
    refine ⟨26145585388735832665637189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17430390259157221777091459 26145585388735832665637189)
    ·
      refine ⟨4902297260387968624806973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26145585388735832665637189 4902297260387968624806973)
      ·
        refine ⟨1838361472645488234302615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4902297260387968624806973 1838361472645488234302615)
        ·
          refine ⟨2757542208968232351453923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1838361472645488234302615 2757542208968232351453923)
          ·
            refine ⟨4136313313452348527180885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2757542208968232351453923 4136313313452348527180885)
            ·
              refine ⟨48472421642019709302901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4136313313452348527180885 48472421642019709302901)
              ·
                rfl

theorem cell21_1911594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 8].length) (baseStart_1911594 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1911594 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1911594 prefixEnd_1911594 := by exact prefixLift 1911594
  have htrace : WordTrace (prefixWord ++ tailWord_1911594) baseStart_1911594 baseEnd_1911594 := by
    simpa [prefixWord, tailWord_1911594, baseEnd_1911594] using wordTrace_append hprefix tailTrace_1911594
  have hstable : (prefixWord ++ tailWord_1911594).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911594).length < 2 ^ (prefixWord ++ tailWord_1911594).sum := by decide
  have hdescent : baseEnd_1911594 < baseStart_1911594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911608 : List Nat := [2, 1, 2, 1, 3, 2, 1, 6, 3]
def baseStart_1911608 : Nat := 118140960795 + 1911608 * 2 ^ 59
def prefixEnd_1911608 : Nat := 4983230072969 + 3 ^ 40 * 1911608 * 2
def baseEnd_1911608 : Nat := 436254989768916470492747

theorem tailTrace_1911608 : CollatzResearch.WordTrace tailWord_1911608 prefixEnd_1911608 436254989768916470492747 := by
  unfold tailWord_1911608
  simp only [CollatzResearch.WordTrace]
  refine ⟨34861035829289083749687739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46481381105718778332916985 34861035829289083749687739)
  ·
    refine ⟨52291553743933625624531609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34861035829289083749687739 52291553743933625624531609)
    ·
      refine ⟨39218665307950219218398707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52291553743933625624531609 39218665307950219218398707)
      ·
        refine ⟨58827997961925328827598061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39218665307950219218398707 58827997961925328827598061)
        ·
          refine ⟨22060499235721998310349273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58827997961925328827598061 22060499235721998310349273)
          ·
            refine ⟨16545374426791498732761955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22060499235721998310349273 16545374426791498732761955)
            ·
              refine ⟨24818061640187248099142933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16545374426791498732761955 24818061640187248099142933)
              ·
                refine ⟨1163346639383777254647325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 24818061640187248099142933 1163346639383777254647325)
                ·
                  refine ⟨436254989768916470492747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1163346639383777254647325 436254989768916470492747)
                  ·
                    rfl

theorem cell21_1911608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 6, 3].length) (baseStart_1911608 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1911608 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1911608 prefixEnd_1911608 := by exact prefixLift 1911608
  have htrace : WordTrace (prefixWord ++ tailWord_1911608) baseStart_1911608 baseEnd_1911608 := by
    simpa [prefixWord, tailWord_1911608, baseEnd_1911608] using wordTrace_append hprefix tailTrace_1911608
  have hstable : (prefixWord ++ tailWord_1911608).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911608).length < 2 ^ (prefixWord ++ tailWord_1911608).sum := by decide
  have hdescent : baseEnd_1911608 < baseStart_1911608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911667 : List Nat := [1, 1, 1, 2, 2, 1, 7, 1, 5]
def baseStart_1911667 : Nat := 118140960795 + 1911667 * 2 ^ 59
def prefixEnd_1911667 : Nat := 4983230072969 + 3 ^ 40 * 1911667 * 2
def baseEnd_1911667 : Nat := 436268454372745479009293

theorem tailTrace_1911667 : CollatzResearch.WordTrace tailWord_1911667 prefixEnd_1911667 436268454372745479009293 := by
  unfold tailWord_1911667
  simp only [CollatzResearch.WordTrace]
  refine ⟨69724223565364420575773255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46482815710242947050515503 69724223565364420575773255)
  ·
    refine ⟨104586335348046630863659883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69724223565364420575773255 104586335348046630863659883)
    ·
      refine ⟨156879503022069946295489825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104586335348046630863659883 156879503022069946295489825)
      ·
        refine ⟨117659627266552459721617369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156879503022069946295489825 117659627266552459721617369)
        ·
          refine ⟨88244720449914344791213027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117659627266552459721617369 88244720449914344791213027)
          ·
            refine ⟨132367080674871517186819541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88244720449914344791213027 132367080674871517186819541)
            ·
              refine ⟨3102353453317301184066083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 132367080674871517186819541 3102353453317301184066083)
              ·
                refine ⟨4653530179975951776099125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3102353453317301184066083 4653530179975951776099125)
                ·
                  refine ⟨436268454372745479009293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4653530179975951776099125 436268454372745479009293)
                  ·
                    rfl

theorem cell21_1911667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 7, 1, 5].length) (baseStart_1911667 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1911667 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1911667 prefixEnd_1911667 := by exact prefixLift 1911667
  have htrace : WordTrace (prefixWord ++ tailWord_1911667) baseStart_1911667 baseEnd_1911667 := by
    simpa [prefixWord, tailWord_1911667, baseEnd_1911667] using wordTrace_append hprefix tailTrace_1911667
  have hstable : (prefixWord ++ tailWord_1911667).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911667).length < 2 ^ (prefixWord ++ tailWord_1911667).sum := by decide
  have hdescent : baseEnd_1911667 < baseStart_1911667 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911670 : List Nat := [5, 1, 1, 3, 1, 2, 2, 6]
def baseStart_1911670 : Nat := 118140960795 + 1911670 * 2 ^ 59
def prefixEnd_1911670 : Nat := 4983230072969 + 3 ^ 40 * 1911670 * 2
def baseEnd_1911670 : Nat := 145423046337872713486429

theorem tailTrace_1911670 : CollatzResearch.WordTrace tailWord_1911670 prefixEnd_1911670 145423046337872713486429 := by
  unfold tailWord_1911670
  simp only [CollatzResearch.WordTrace]
  refine ⟨4357770811522097005508279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46482888656235701392088309 4357770811522097005508279)
  ·
    refine ⟨6536656217283145508262419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4357770811522097005508279 6536656217283145508262419)
    ·
      refine ⟨9804984325924718262393629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6536656217283145508262419 9804984325924718262393629)
      ·
        refine ⟨3676869122221769348397611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9804984325924718262393629 3676869122221769348397611)
        ·
          refine ⟨5515303683332654022596417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3676869122221769348397611 5515303683332654022596417)
          ·
            refine ⟨4136477762499490516947313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5515303683332654022596417 4136477762499490516947313)
            ·
              refine ⟨3102358321874617887710485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4136477762499490516947313 3102358321874617887710485)
              ·
                refine ⟨145423046337872713486429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3102358321874617887710485 145423046337872713486429)
                ·
                  rfl

theorem cell21_1911670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 2, 6].length) (baseStart_1911670 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1911670 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1911670 prefixEnd_1911670 := by exact prefixLift 1911670
  have htrace : WordTrace (prefixWord ++ tailWord_1911670) baseStart_1911670 baseEnd_1911670 := by
    simpa [prefixWord, tailWord_1911670, baseEnd_1911670] using wordTrace_append hprefix tailTrace_1911670
  have hstable : (prefixWord ++ tailWord_1911670).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911670).length < 2 ^ (prefixWord ++ tailWord_1911670).sum := by decide
  have hdescent : baseEnd_1911670 < baseStart_1911670 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911732 : List Nat := [2, 5, 2, 1, 1, 1, 2, 3, 4]
def baseStart_1911732 : Nat := 118140960795 + 1911732 * 2 ^ 59
def prefixEnd_1911732 : Nat := 4983230072969 + 3 ^ 40 * 1911732 * 2
def baseEnd_1911732 : Nat := 436283288258319810425827

theorem tailTrace_1911732 : CollatzResearch.WordTrace tailWord_1911732 prefixEnd_1911732 436283288258319810425827 := by
  unfold tailWord_1911732
  simp only [CollatzResearch.WordTrace]
  refine ⟨34863297155064468338444725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46484396206752624451259633 34863297155064468338444725)
  ·
    refine ⟨3268434108287293906729193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34863297155064468338444725 3268434108287293906729193)
    ·
      refine ⟨2451325581215470430046895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3268434108287293906729193 2451325581215470430046895)
      ·
        refine ⟨3676988371823205645070343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2451325581215470430046895 3676988371823205645070343)
        ·
          refine ⟨5515482557734808467605515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3676988371823205645070343 5515482557734808467605515)
          ·
            refine ⟨8273223836602212701408273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5515482557734808467605515 8273223836602212701408273)
            ·
              refine ⟨6204917877451659526056205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8273223836602212701408273 6204917877451659526056205)
              ·
                refine ⟨2326844204044372322271077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6204917877451659526056205 2326844204044372322271077)
                ·
                  refine ⟨436283288258319810425827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2326844204044372322271077 436283288258319810425827)
                  ·
                    rfl

theorem cell21_1911732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_1911732 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1911732 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1911732 prefixEnd_1911732 := by exact prefixLift 1911732
  have htrace : WordTrace (prefixWord ++ tailWord_1911732) baseStart_1911732 baseEnd_1911732 := by
    simpa [prefixWord, tailWord_1911732, baseEnd_1911732] using wordTrace_append hprefix tailTrace_1911732
  have hstable : (prefixWord ++ tailWord_1911732).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911732).length < 2 ^ (prefixWord ++ tailWord_1911732).sum := by decide
  have hdescent : baseEnd_1911732 < baseStart_1911732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911791 : List Nat := [1, 1, 2, 1, 4, 4, 3, 1, 4]
def baseStart_1911791 : Nat := 118140960795 + 1911791 * 2 ^ 59
def prefixEnd_1911791 : Nat := 4983230072969 + 3 ^ 40 * 1911791 * 2
def baseEnd_1911791 : Nat := 436296752862148818942373

theorem tailTrace_1911791 : CollatzResearch.WordTrace tailWord_1911791 prefixEnd_1911791 436296752862148818942373 := by
  unfold tailWord_1911791
  simp only [CollatzResearch.WordTrace]
  refine ⟨69728746216915189753287227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46485830811276793168858151 69728746216915189753287227)
  ·
    refine ⟨104593119325372784629930841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69728746216915189753287227 104593119325372784629930841)
    ·
      refine ⟨78444839494029588472448131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104593119325372784629930841 78444839494029588472448131)
      ·
        refine ⟨117667259241044382708672197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78444839494029588472448131 117667259241044382708672197)
        ·
          refine ⟨22062611107695821757876037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117667259241044382708672197 22062611107695821757876037)
          ·
            refine ⟨4136739582692966579601757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22062611107695821757876037 4136739582692966579601757)
            ·
              refine ⟨1551277343509862467350659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4136739582692966579601757 1551277343509862467350659)
              ·
                refine ⟨2326916015264793701025989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1551277343509862467350659 2326916015264793701025989)
                ·
                  refine ⟨436296752862148818942373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2326916015264793701025989 436296752862148818942373)
                  ·
                    rfl

theorem cell21_1911791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 3, 1, 4].length) (baseStart_1911791 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1911791 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1911791 prefixEnd_1911791 := by exact prefixLift 1911791
  have htrace : WordTrace (prefixWord ++ tailWord_1911791) baseStart_1911791 baseEnd_1911791 := by
    simpa [prefixWord, tailWord_1911791, baseEnd_1911791] using wordTrace_append hprefix tailTrace_1911791
  have hstable : (prefixWord ++ tailWord_1911791).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911791).length < 2 ^ (prefixWord ++ tailWord_1911791).sum := by decide
  have hdescent : baseEnd_1911791 < baseStart_1911791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911833 : List Nat := [1, 2, 1, 2, 1, 1, 6, 1, 6]
def baseStart_1911833 : Nat := 118140960795 + 1911833 * 2 ^ 59
def prefixEnd_1911833 : Nat := 4983230072969 + 3 ^ 40 * 1911833 * 2
def baseEnd_1911833 : Nat := 436306337834366079242287

theorem tailTrace_1911833 : CollatzResearch.WordTrace tailWord_1911833 prefixEnd_1911833 436306337834366079242287 := by
  unfold tailWord_1911833
  simp only [CollatzResearch.WordTrace]
  refine ⟨69730278082763030926316153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46486852055175353950877435 69730278082763030926316153)
  ·
    refine ⟨52297708562072273194737115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69730278082763030926316153 52297708562072273194737115)
    ·
      refine ⟨78446562843108409792105673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52297708562072273194737115 78446562843108409792105673)
      ·
        refine ⟨58834922132331307344079255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78446562843108409792105673 58834922132331307344079255)
        ·
          refine ⟨88252383198496961016118883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58834922132331307344079255 88252383198496961016118883)
          ·
            refine ⟨132378574797745441524178325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88252383198496961016118883 132378574797745441524178325)
            ·
              refine ⟨6205245693644317571445859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 132378574797745441524178325 6205245693644317571445859)
              ·
                refine ⟨9307868540466476357168789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6205245693644317571445859 9307868540466476357168789)
                ·
                  refine ⟨436306337834366079242287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9307868540466476357168789 436306337834366079242287)
                  ·
                    rfl

theorem cell21_1911833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 1, 6].length) (baseStart_1911833 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1911833 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1911833 prefixEnd_1911833 := by exact prefixLift 1911833
  have htrace : WordTrace (prefixWord ++ tailWord_1911833) baseStart_1911833 baseEnd_1911833 := by
    simpa [prefixWord, tailWord_1911833, baseEnd_1911833] using wordTrace_append hprefix tailTrace_1911833
  have hstable : (prefixWord ++ tailWord_1911833).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911833).length < 2 ^ (prefixWord ++ tailWord_1911833).sum := by decide
  have hdescent : baseEnd_1911833 < baseStart_1911833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911864 : List Nat := [2, 1, 2, 1, 5, 1, 2, 7]
def baseStart_1911864 : Nat := 118140960795 + 1911864 * 2 ^ 59
def prefixEnd_1911864 : Nat := 4983230072969 + 3 ^ 40 * 1911864 * 2
def baseEnd_1911864 : Nat := 145437804152238971408519

theorem tailTrace_1911864 : CollatzResearch.WordTrace tailWord_1911864 prefixEnd_1911864 145437804152238971408519 := by
  unfold tailWord_1911864
  simp only [CollatzResearch.WordTrace]
  refine ⟨34865704372825361610347323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46487605830433815480463097 34865704372825361610347323)
  ·
    refine ⟨52298556559238042415520985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34865704372825361610347323 52298556559238042415520985)
    ·
      refine ⟨39223917419428531811640739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52298556559238042415520985 39223917419428531811640739)
      ·
        refine ⟨58835876129142797717461109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39223917419428531811640739 58835876129142797717461109)
        ·
          refine ⟨5515863387107137286011979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58835876129142797717461109 5515863387107137286011979)
          ·
            refine ⟨8273795080660705929017969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5515863387107137286011979 8273795080660705929017969)
            ·
              refine ⟨6205346310495529446763477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8273795080660705929017969 6205346310495529446763477)
              ·
                refine ⟨145437804152238971408519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6205346310495529446763477 145437804152238971408519)
                ·
                  rfl

theorem cell21_1911864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 7].length) (baseStart_1911864 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1911864 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1911864 prefixEnd_1911864 := by exact prefixLift 1911864
  have htrace : WordTrace (prefixWord ++ tailWord_1911864) baseStart_1911864 baseEnd_1911864 := by
    simpa [prefixWord, tailWord_1911864, baseEnd_1911864] using wordTrace_append hprefix tailTrace_1911864
  have hstable : (prefixWord ++ tailWord_1911864).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911864).length < 2 ^ (prefixWord ++ tailWord_1911864).sum := by decide
  have hdescent : baseEnd_1911864 < baseStart_1911864 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911926 : List Nat := [5, 1, 1, 2, 1, 1, 2, 2, 6]
def baseStart_1911926 : Nat := 118140960795 + 1911926 * 2 ^ 59
def prefixEnd_1911926 : Nat := 4983230072969 + 3 ^ 40 * 1911926 * 2
def baseEnd_1911926 : Nat := 436327561701418584192097

theorem tailTrace_1911926 : CollatzResearch.WordTrace tailWord_1911926 prefixEnd_1911926 436327561701418584192097 := by
  unfold tailWord_1911926
  simp only [CollatzResearch.WordTrace]
  refine ⟨4358354379464131738090727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46489113380950738539634421 4358354379464131738090727)
  ·
    refine ⟨6537531569196197607136091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4358354379464131738090727 6537531569196197607136091)
    ·
      refine ⟨9806297353794296410704137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6537531569196197607136091 9806297353794296410704137)
      ·
        refine ⟨7354723015345722308028103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9806297353794296410704137 7354723015345722308028103)
        ·
          refine ⟨11032084523018583462042155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7354723015345722308028103 11032084523018583462042155)
          ·
            refine ⟨16548126784527875193063233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11032084523018583462042155 16548126784527875193063233)
            ·
              refine ⟨12411095088395906394797425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16548126784527875193063233 12411095088395906394797425)
              ·
                refine ⟨9308321316296929796098069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12411095088395906394797425 9308321316296929796098069)
                ·
                  refine ⟨436327561701418584192097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9308321316296929796098069 436327561701418584192097)
                  ·
                    rfl

theorem cell21_1911926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 2, 6].length) (baseStart_1911926 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1911926 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1911926 prefixEnd_1911926 := by exact prefixLift 1911926
  have htrace : WordTrace (prefixWord ++ tailWord_1911926) baseStart_1911926 baseEnd_1911926 := by
    simpa [prefixWord, tailWord_1911926, baseEnd_1911926] using wordTrace_append hprefix tailTrace_1911926
  have hstable : (prefixWord ++ tailWord_1911926).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911926).length < 2 ^ (prefixWord ++ tailWord_1911926).sum := by decide
  have hdescent : baseEnd_1911926 < baseStart_1911926 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911929 : List Nat := [1, 2, 1, 3, 5, 1, 2, 3, 3]
def baseStart_1911929 : Nat := 118140960795 + 1911929 * 2 ^ 59
def prefixEnd_1911929 : Nat := 4983230072969 + 3 ^ 40 * 1911929 * 2
def baseEnd_1911929 : Nat := 436328246342291245642091

theorem tailTrace_1911929 : CollatzResearch.WordTrace tailWord_1911929 prefixEnd_1911929 436328246342291245642091 := by
  unfold tailWord_1911929
  simp only [CollatzResearch.WordTrace]
  refine ⟨69733779490415239321810841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46489186326943492881207227 69733779490415239321810841)
  ·
    refine ⟨52300334617811429491358131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69733779490415239321810841 52300334617811429491358131)
    ·
      refine ⟨78450501926717144237037197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52300334617811429491358131 78450501926717144237037197)
      ·
        refine ⟨29418938222518929088888949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78450501926717144237037197 29418938222518929088888949)
        ·
          refine ⟨2758025458361149602083339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29418938222518929088888949 2758025458361149602083339)
          ·
            refine ⟨4137038187541724403125009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2758025458361149602083339 4137038187541724403125009)
            ·
              refine ⟨3102778640656293302343757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4137038187541724403125009 3102778640656293302343757)
              ·
                refine ⟨1163541990246109988378909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3102778640656293302343757 1163541990246109988378909)
                ·
                  refine ⟨436328246342291245642091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1163541990246109988378909 436328246342291245642091)
                  ·
                    rfl

theorem cell21_1911929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 2, 3, 3].length) (baseStart_1911929 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1911929 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1911929 prefixEnd_1911929 := by exact prefixLift 1911929
  have htrace : WordTrace (prefixWord ++ tailWord_1911929) baseStart_1911929 baseEnd_1911929 := by
    simpa [prefixWord, tailWord_1911929, baseEnd_1911929] using wordTrace_append hprefix tailTrace_1911929
  have hstable : (prefixWord ++ tailWord_1911929).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911929).length < 2 ^ (prefixWord ++ tailWord_1911929).sum := by decide
  have hdescent : baseEnd_1911929 < baseStart_1911929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911940 : List Nat := [2, 3, 2, 1, 2, 3, 8]
def baseStart_1911940 : Nat := 118140960795 + 1911940 * 2 ^ 59
def prefixEnd_1911940 : Nat := 4983230072969 + 3 ^ 40 * 1911940 * 2
def baseEnd_1911940 : Nat := 48481195188017518995415

theorem tailTrace_1911940 : CollatzResearch.WordTrace tailWord_1911940 prefixEnd_1911940 48481195188017518995415 := by
  unfold tailWord_1911940
  simp only [CollatzResearch.WordTrace]
  refine ⟨34867090346687694100230637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46489453795583592133640849 34867090346687694100230637)
  ·
    refine ⟨13075158880007885287586489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34867090346687694100230637 13075158880007885287586489)
    ·
      refine ⟨9806369160005913965689867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13075158880007885287586489 9806369160005913965689867)
      ·
        refine ⟨14709553740008870948534801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9806369160005913965689867 14709553740008870948534801)
        ·
          refine ⟨11032165305006653211401101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14709553740008870948534801 11032165305006653211401101)
          ·
            refine ⟨4137061989377494954275413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11032165305006653211401101 4137061989377494954275413)
            ·
              refine ⟨48481195188017518995415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4137061989377494954275413 48481195188017518995415)
              ·
                rfl

theorem cell21_1911940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 8].length) (baseStart_1911940 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1911940 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1911940 prefixEnd_1911940 := by exact prefixLift 1911940
  have htrace : WordTrace (prefixWord ++ tailWord_1911940) baseStart_1911940 baseEnd_1911940 := by
    simpa [prefixWord, tailWord_1911940, baseEnd_1911940] using wordTrace_append hprefix tailTrace_1911940
  have hstable : (prefixWord ++ tailWord_1911940).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911940).length < 2 ^ (prefixWord ++ tailWord_1911940).sum := by decide
  have hdescent : baseEnd_1911940 < baseStart_1911940 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911999 : List Nat := [1, 1, 2, 2, 2, 2, 11]
def baseStart_1911999 : Nat := 118140960795 + 1911999 * 2 ^ 59
def prefixEnd_1911999 : Nat := 4983230072969 + 3 ^ 40 * 1911999 * 2
def baseEnd_1911999 : Nat := 48482691255109631052809

theorem tailTrace_1911999 : CollatzResearch.WordTrace tailWord_1911999 prefixEnd_1911999 48482691255109631052809 := by
  unfold tailWord_1911999
  simp only [CollatzResearch.WordTrace]
  refine ⟨69736332600161641276859051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46490888400107760851239367 69736332600161641276859051)
  ·
    refine ⟨104604498900242461915288577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69736332600161641276859051 104604498900242461915288577)
    ·
      refine ⟨78453374175181846436466433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104604498900242461915288577 78453374175181846436466433)
      ·
        refine ⟨58840030631386384827349825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78453374175181846436466433 58840030631386384827349825)
        ·
          refine ⟨44130022973539788620512369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58840030631386384827349825 44130022973539788620512369)
          ·
            refine ⟨33097517230154841465384277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44130022973539788620512369 33097517230154841465384277)
            ·
              refine ⟨48482691255109631052809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 33097517230154841465384277 48482691255109631052809)
              ·
                rfl

theorem cell21_1911999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 11].length) (baseStart_1911999 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1911999 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1911999 prefixEnd_1911999 := by exact prefixLift 1911999
  have htrace : WordTrace (prefixWord ++ tailWord_1911999) baseStart_1911999 baseEnd_1911999 := by
    simpa [prefixWord, tailWord_1911999, baseEnd_1911999] using wordTrace_append hprefix tailTrace_1911999
  have hstable : (prefixWord ++ tailWord_1911999).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911999).length < 2 ^ (prefixWord ++ tailWord_1911999).sum := by decide
  have hdescent : baseEnd_1911999 < baseStart_1911999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1912078 : List Nat := [4, 1, 1, 2, 1, 3, 2, 3, 4]
def baseStart_1912078 : Nat := 118140960795 + 1912078 * 2 ^ 59
def prefixEnd_1912078 : Nat := 4983230072969 + 3 ^ 40 * 1912078 * 2
def baseEnd_1912078 : Nat := 436362250172300097658453

theorem tailTrace_1912078 : CollatzResearch.WordTrace tailWord_1912078 prefixEnd_1912078 436362250172300097658453 := by
  unfold tailWord_1912078
  simp only [CollatzResearch.WordTrace]
  refine ⟨8717401745859429721123111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46492809311250291845989925 8717401745859429721123111)
  ·
    refine ⟨13076102618789144581684667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8717401745859429721123111 13076102618789144581684667)
    ·
      refine ⟨19614153928183716872527001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13076102618789144581684667 19614153928183716872527001)
      ·
        refine ⟨14710615446137787654395251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19614153928183716872527001 14710615446137787654395251)
        ·
          refine ⟨22065923169206681481592877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14710615446137787654395251 22065923169206681481592877)
          ·
            refine ⟨8274721188452505555597329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22065923169206681481592877 8274721188452505555597329)
            ·
              refine ⟨6206040891339379166697997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8274721188452505555597329 6206040891339379166697997)
              ·
                refine ⟨2327265334252267187511749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6206040891339379166697997 2327265334252267187511749)
                ·
                  refine ⟨436362250172300097658453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2327265334252267187511749 436362250172300097658453)
                  ·
                    rfl

theorem cell21_1912078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 3, 4].length) (baseStart_1912078 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1912078 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1912078 prefixEnd_1912078 := by exact prefixLift 1912078
  have htrace : WordTrace (prefixWord ++ tailWord_1912078) baseStart_1912078 baseEnd_1912078 := by
    simpa [prefixWord, tailWord_1912078, baseEnd_1912078] using wordTrace_append hprefix tailTrace_1912078
  have hstable : (prefixWord ++ tailWord_1912078).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1912078).length < 2 ^ (prefixWord ++ tailWord_1912078).sum := by decide
  have hdescent : baseEnd_1912078 < baseStart_1912078 := by decide
  rcases family_descends (prefixWord ++ tailWord_1912078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1912109 : List Nat := [1, 5, 3, 1, 1, 2, 8]
def baseStart_1912109 : Nat := 118140960795 + 1912109 * 2 ^ 59
def prefixEnd_1912109 : Nat := 4983230072969 + 3 ^ 40 * 1912109 * 2
def baseEnd_1912109 : Nat := 48485480532738992515747

theorem tailTrace_1912109 : CollatzResearch.WordTrace tailWord_1912109 prefixEnd_1912109 48485480532738992515747 := by
  unfold tailWord_1912109
  simp only [CollatzResearch.WordTrace]
  refine ⟨69740344629763130063363381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46493563086508753375575587 69740344629763130063363381)
  ·
    refine ⟨6538157309040293443440317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 69740344629763130063363381 6538157309040293443440317)
    ·
      refine ⟨2451808990890110041290119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6538157309040293443440317 2451808990890110041290119)
      ·
        refine ⟨3677713486335165061935179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2451808990890110041290119 3677713486335165061935179)
        ·
          refine ⟨5516570229502747592902769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3677713486335165061935179 5516570229502747592902769)
          ·
            refine ⟨4137427672127060694677077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5516570229502747592902769 4137427672127060694677077)
            ·
              refine ⟨48485480532738992515747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4137427672127060694677077 48485480532738992515747)
              ·
                rfl

theorem cell21_1912109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 8].length) (baseStart_1912109 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1912109 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1912109 prefixEnd_1912109 := by exact prefixLift 1912109
  have htrace : WordTrace (prefixWord ++ tailWord_1912109) baseStart_1912109 baseEnd_1912109 := by
    simpa [prefixWord, tailWord_1912109, baseEnd_1912109] using wordTrace_append hprefix tailTrace_1912109
  have hstable : (prefixWord ++ tailWord_1912109).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1912109).length < 2 ^ (prefixWord ++ tailWord_1912109).sum := by decide
  have hdescent : baseEnd_1912109 < baseStart_1912109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1912109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1912137 : List Nat := [1, 2, 1, 1, 2, 3, 2, 5, 4]
def baseStart_1912137 : Nat := 118140960795 + 1912137 * 2 ^ 59
def prefixEnd_1912137 : Nat := 4983230072969 + 3 ^ 40 * 1912137 * 2
def baseEnd_1912137 : Nat := 436375714776129106174999

theorem tailTrace_1912137 : CollatzResearch.WordTrace tailWord_1912137 prefixEnd_1912137 436375714776129106174999 := by
  unfold tailWord_1912137
  simp only [CollatzResearch.WordTrace]
  refine ⟨69741365873661690845382665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46494243915774460563588443 69741365873661690845382665)
  ·
    refine ⟨52306024405246268134036999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69741365873661690845382665 52306024405246268134036999)
    ·
      refine ⟨78459036607869402201055499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52306024405246268134036999 78459036607869402201055499)
      ·
        refine ⟨117688554911804103301583249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78459036607869402201055499 117688554911804103301583249)
        ·
          refine ⟨88266416183853077476187437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117688554911804103301583249 88266416183853077476187437)
          ·
            refine ⟨33099906068944904053570289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88266416183853077476187437 33099906068944904053570289)
            ·
              refine ⟨24824929551708678040177717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33099906068944904053570289 24824929551708678040177717)
              ·
                refine ⟨2327337145472688566266661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24824929551708678040177717 2327337145472688566266661)
                ·
                  refine ⟨436375714776129106174999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2327337145472688566266661 436375714776129106174999)
                  ·
                    rfl

theorem cell21_1912137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 5, 4].length) (baseStart_1912137 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1912137 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1912137 prefixEnd_1912137 := by exact prefixLift 1912137
  have htrace : WordTrace (prefixWord ++ tailWord_1912137) baseStart_1912137 baseEnd_1912137 := by
    simpa [prefixWord, tailWord_1912137, baseEnd_1912137] using wordTrace_append hprefix tailTrace_1912137
  have hstable : (prefixWord ++ tailWord_1912137).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1912137).length < 2 ^ (prefixWord ++ tailWord_1912137).sum := by decide
  have hdescent : baseEnd_1912137 < baseStart_1912137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1912137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1912174 : List Nat := [4, 1, 2, 4, 2, 1, 1, 1, 5]
def baseStart_1912174 : Nat := 118140960795 + 1912174 * 2 ^ 59
def prefixEnd_1912174 : Nat := 4983230072969 + 3 ^ 40 * 1912174 * 2
def baseEnd_1912174 : Nat := 436384158680225264058257

theorem tailTrace_1912174 : CollatzResearch.WordTrace tailWord_1912174 prefixEnd_1912174 436384158680225264058257 := by
  unfold tailWord_1912174
  simp only [CollatzResearch.WordTrace]
  refine ⟨8717839421815955770559947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46495143583018430776319717 8717839421815955770559947)
  ·
    refine ⟨13076759132723933655839921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8717839421815955770559947 13076759132723933655839921)
    ·
      refine ⟨9807569349542950241879941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13076759132723933655839921 9807569349542950241879941)
      ·
        refine ⟨1838919253039303170352489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9807569349542950241879941 1838919253039303170352489)
        ·
          refine ⟨1379189439779477377764367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1838919253039303170352489 1379189439779477377764367)
          ·
            refine ⟨2068784159669216066646551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1379189439779477377764367 2068784159669216066646551)
            ·
              refine ⟨3103176239503824099969827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2068784159669216066646551 3103176239503824099969827)
              ·
                refine ⟨4654764359255736149954741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3103176239503824099969827 4654764359255736149954741)
                ·
                  refine ⟨436384158680225264058257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4654764359255736149954741 436384158680225264058257)
                  ·
                    rfl

theorem cell21_1912174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 1, 1, 5].length) (baseStart_1912174 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1912174 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1912174 prefixEnd_1912174 := by exact prefixLift 1912174
  have htrace : WordTrace (prefixWord ++ tailWord_1912174) baseStart_1912174 baseEnd_1912174 := by
    simpa [prefixWord, tailWord_1912174, baseEnd_1912174] using wordTrace_append hprefix tailTrace_1912174
  have hstable : (prefixWord ++ tailWord_1912174).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1912174).length < 2 ^ (prefixWord ++ tailWord_1912174).sum := by decide
  have hdescent : baseEnd_1912174 < baseStart_1912174 := by decide
  rcases family_descends (prefixWord ++ tailWord_1912174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1912272 : List Nat := [2, 1, 1, 1, 1, 2, 2, 3, 8]
def baseStart_1912272 : Nat := 118140960795 + 1912272 * 2 ^ 59
def prefixEnd_1912272 : Nat := 4983230072969 + 3 ^ 40 * 1912272 * 2
def baseEnd_1912272 : Nat := 436406523615398871424723

theorem tailTrace_1912272 : CollatzResearch.WordTrace tailWord_1912272 prefixEnd_1912272 436406523615398871424723 := by
  unfold tailWord_1912272
  simp only [CollatzResearch.WordTrace]
  refine ⟨34873144864086304450773535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46497526485448405934364713 34873144864086304450773535)
  ·
    refine ⟨52309717296129456676160303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34873144864086304450773535 52309717296129456676160303)
    ·
      refine ⟨78464575944194185014240455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52309717296129456676160303 78464575944194185014240455)
      ·
        refine ⟨117696863916291277521360683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78464575944194185014240455 117696863916291277521360683)
        ·
          refine ⟨176545295874436916282041025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117696863916291277521360683 176545295874436916282041025)
          ·
            refine ⟨132408971905827687211530769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176545295874436916282041025 132408971905827687211530769)
            ·
              refine ⟨99306728929370765408648077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132408971905827687211530769 99306728929370765408648077)
              ·
                refine ⟨37240023348514037028243029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99306728929370765408648077 37240023348514037028243029)
                ·
                  refine ⟨436406523615398871424723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37240023348514037028243029 436406523615398871424723)
                  ·
                    rfl

theorem cell21_1912272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 8].length) (baseStart_1912272 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1912272 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1912272 prefixEnd_1912272 := by exact prefixLift 1912272
  have htrace : WordTrace (prefixWord ++ tailWord_1912272) baseStart_1912272 baseEnd_1912272 := by
    simpa [prefixWord, tailWord_1912272, baseEnd_1912272] using wordTrace_append hprefix tailTrace_1912272
  have hstable : (prefixWord ++ tailWord_1912272).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1912272).length < 2 ^ (prefixWord ++ tailWord_1912272).sum := by decide
  have hdescent : baseEnd_1912272 < baseStart_1912272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1912272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1912289 : List Nat := [1, 2, 3, 1, 2, 4, 1, 1, 6]
def baseStart_1912289 : Nat := 118140960795 + 1912289 * 2 ^ 59
def prefixEnd_1912289 : Nat := 4983230072969 + 3 ^ 40 * 1912289 * 2
def baseEnd_1912289 : Nat := 436410403247010619641355

theorem tailTrace_1912289 : CollatzResearch.WordTrace tailWord_1912289 prefixEnd_1912289 436410403247010619641355 := by
  unfold tailWord_1912289
  simp only [CollatzResearch.WordTrace]
  refine ⟨69746909769111020804915921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46497939846074013869943947 69746909769111020804915921)
  ·
    refine ⟨52310182326833265603686941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69746909769111020804915921 52310182326833265603686941)
    ·
      refine ⟨19616318372562474601382603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52310182326833265603686941 19616318372562474601382603)
      ·
        refine ⟨29424477558843711902073905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19616318372562474601382603 29424477558843711902073905)
        ·
          refine ⟨22068358169132783926555429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29424477558843711902073905 22068358169132783926555429)
          ·
            refine ⟨4137817156712396986229143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22068358169132783926555429 4137817156712396986229143)
            ·
              refine ⟨6206725735068595479343715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4137817156712396986229143 6206725735068595479343715)
              ·
                refine ⟨9310088602602893219015573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6206725735068595479343715 9310088602602893219015573)
                ·
                  refine ⟨436410403247010619641355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9310088602602893219015573 436410403247010619641355)
                  ·
                    rfl

theorem cell21_1912289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 1, 6].length) (baseStart_1912289 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1912289 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1912289 prefixEnd_1912289 := by exact prefixLift 1912289
  have htrace : WordTrace (prefixWord ++ tailWord_1912289) baseStart_1912289 baseEnd_1912289 := by
    simpa [prefixWord, tailWord_1912289, baseEnd_1912289] using wordTrace_append hprefix tailTrace_1912289
  have hstable : (prefixWord ++ tailWord_1912289).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1912289).length < 2 ^ (prefixWord ++ tailWord_1912289).sum := by decide
  have hdescent : baseEnd_1912289 < baseStart_1912289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1912289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1912351 : List Nat := [1, 1, 2, 4, 1, 1, 2, 6, 3]
def baseStart_1912351 : Nat := 118140960795 + 1912351 * 2 ^ 59
def prefixEnd_1912351 : Nat := 4983230072969 + 3 ^ 40 * 1912351 * 2
def baseEnd_1912351 : Nat := 436424552491712289607895

theorem tailTrace_1912351 : CollatzResearch.WordTrace tailWord_1912351 prefixEnd_1912351 436424552491712289607895 := by
  unfold tailWord_1912351
  simp only [CollatzResearch.WordTrace]
  refine ⟨69749171094886405393672907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46499447396590936929115271 69749171094886405393672907)
  ·
    refine ⟨104623756642329608090509361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69749171094886405393672907 104623756642329608090509361)
    ·
      refine ⟨78467817481747206067882021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104623756642329608090509361 78467817481747206067882021)
      ·
        refine ⟨14712715777827601137727879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78467817481747206067882021 14712715777827601137727879)
        ·
          refine ⟨22069073666741401706591819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14712715777827601137727879 22069073666741401706591819)
          ·
            refine ⟨33103610500112102559887729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22069073666741401706591819 33103610500112102559887729)
            ·
              refine ⟨24827707875084076919915797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33103610500112102559887729 24827707875084076919915797)
              ·
                refine ⟨1163798806644566105621053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 24827707875084076919915797 1163798806644566105621053)
                ·
                  refine ⟨436424552491712289607895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1163798806644566105621053 436424552491712289607895)
                  ·
                    rfl

theorem cell21_1912351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 6, 3].length) (baseStart_1912351 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1912351 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1912351 prefixEnd_1912351 := by exact prefixLift 1912351
  have htrace : WordTrace (prefixWord ++ tailWord_1912351) baseStart_1912351 baseEnd_1912351 := by
    simpa [prefixWord, tailWord_1912351, baseEnd_1912351] using wordTrace_append hprefix tailTrace_1912351
  have hstable : (prefixWord ++ tailWord_1912351).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1912351).length < 2 ^ (prefixWord ++ tailWord_1912351).sum := by decide
  have hdescent : baseEnd_1912351 < baseStart_1912351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1912351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1912455 : List Nat := [1, 1, 4, 2, 1, 4, 8]
def baseStart_1912455 : Nat := 118140960795 + 1912455 * 2 ^ 59
def prefixEnd_1912455 : Nat := 4983230072969 + 3 ^ 40 * 1912455 * 2
def baseEnd_1912455 : Nat := 48494254078736802208261

theorem tailTrace_1912455 : CollatzResearch.WordTrace tailWord_1912455 prefixEnd_1912455 48494254078736802208261 := by
  unfold tailWord_1912455
  simp only [CollatzResearch.WordTrace]
  refine ⟨69752964286509631155458819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46501976191006420770305879 69752964286509631155458819)
  ·
    refine ⟨104629446429764446733188229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69752964286509631155458819 104629446429764446733188229)
    ·
      refine ⟨19618021205580833762472793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104629446429764446733188229 19618021205580833762472793)
      ·
        refine ⟨14713515904185625321854595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19618021205580833762472793 14713515904185625321854595)
        ·
          refine ⟨22070273856278437982781893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14713515904185625321854595 22070273856278437982781893)
          ·
            refine ⟨4138176348052207121771605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22070273856278437982781893 4138176348052207121771605)
            ·
              refine ⟨48494254078736802208261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4138176348052207121771605 48494254078736802208261)
              ·
                rfl

theorem cell21_1912455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 8].length) (baseStart_1912455 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1912455 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1912455 prefixEnd_1912455 := by exact prefixLift 1912455
  have htrace : WordTrace (prefixWord ++ tailWord_1912455) baseStart_1912455 baseEnd_1912455 := by
    simpa [prefixWord, tailWord_1912455, baseEnd_1912455] using wordTrace_append hprefix tailTrace_1912455
  have hstable : (prefixWord ++ tailWord_1912455).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1912455).length < 2 ^ (prefixWord ++ tailWord_1912455).sum := by decide
  have hdescent : baseEnd_1912455 < baseStart_1912455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1912455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1912458 : List Nat := [3, 1, 2, 3, 2, 1, 3, 2, 4]
def baseStart_1912458 : Nat := 118140960795 + 1912458 * 2 ^ 59
def prefixEnd_1912458 : Nat := 4983230072969 + 3 ^ 40 * 1912458 * 2
def baseEnd_1912458 : Nat := 436448971349503881324343

theorem tailTrace_1912458 : CollatzResearch.WordTrace tailWord_1912458 prefixEnd_1912458 436448971349503881324343 := by
  unfold tailWord_1912458
  simp only [CollatzResearch.WordTrace]
  refine ⟨17438268426374690666954507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46502049136999175111878685 17438268426374690666954507)
  ·
    refine ⟨26157402639562036000431761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17438268426374690666954507 26157402639562036000431761)
    ·
      refine ⟨19618051979671527000323821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26157402639562036000431761 19618051979671527000323821)
      ·
        refine ⟨7356769492376822625121433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19618051979671527000323821 7356769492376822625121433)
        ·
          refine ⟨5517577119282616968841075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7356769492376822625121433 5517577119282616968841075)
          ·
            refine ⟨8276365678923925453261613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5517577119282616968841075 8276365678923925453261613)
            ·
              refine ⟨3103637129596472044973105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8276365678923925453261613 3103637129596472044973105)
              ·
                refine ⟨2327727847197354033729829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3103637129596472044973105 2327727847197354033729829)
                ·
                  refine ⟨436448971349503881324343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2327727847197354033729829 436448971349503881324343)
                  ·
                    rfl

theorem cell21_1912458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 3, 2, 4].length) (baseStart_1912458 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1912458 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1912458 prefixEnd_1912458 := by exact prefixLift 1912458
  have htrace : WordTrace (prefixWord ++ tailWord_1912458) baseStart_1912458 baseEnd_1912458 := by
    simpa [prefixWord, tailWord_1912458, baseEnd_1912458] using wordTrace_append hprefix tailTrace_1912458
  have hstable : (prefixWord ++ tailWord_1912458).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1912458).length < 2 ^ (prefixWord ++ tailWord_1912458).sum := by decide
  have hdescent : baseEnd_1912458 < baseStart_1912458 := by decide
  rcases family_descends (prefixWord ++ tailWord_1912458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1912520 : List Nat := [2, 1, 3, 1, 2, 2, 5, 2, 3]
def baseStart_1912520 : Nat := 118140960795 + 1912520 * 2 ^ 59
def prefixEnd_1912520 : Nat := 4983230072969 + 3 ^ 40 * 1912520 * 2
def baseEnd_1912520 : Nat := 436463120594205551290883

theorem tailTrace_1912520 : CollatzResearch.WordTrace tailWord_1912520 prefixEnd_1912520 436463120594205551290883 := by
  unfold tailWord_1912520
  simp only [CollatzResearch.WordTrace]
  refine ⟨34877667515637073628287507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46503556687516098171050009 34877667515637073628287507)
  ·
    refine ⟨52316501273455610442431261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34877667515637073628287507 52316501273455610442431261)
    ·
      refine ⟨19618687977545853915911723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52316501273455610442431261 19618687977545853915911723)
      ·
        refine ⟨29428031966318780873867585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19618687977545853915911723 29428031966318780873867585)
        ·
          refine ⟨22071023974739085655400689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29428031966318780873867585 22071023974739085655400689)
          ·
            refine ⟨16553267981054314241550517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22071023974739085655400689 16553267981054314241550517)
            ·
              refine ⟨1551868873223841960145361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16553267981054314241550517 1551868873223841960145361)
              ·
                refine ⟨1163901654917881470109021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1551868873223841960145361 1163901654917881470109021)
                ·
                  refine ⟨436463120594205551290883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1163901654917881470109021 436463120594205551290883)
                  ·
                    rfl

theorem cell21_1912520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 5, 2, 3].length) (baseStart_1912520 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1912520 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1912520 prefixEnd_1912520 := by exact prefixLift 1912520
  have htrace : WordTrace (prefixWord ++ tailWord_1912520) baseStart_1912520 baseEnd_1912520 := by
    simpa [prefixWord, tailWord_1912520, baseEnd_1912520] using wordTrace_append hprefix tailTrace_1912520
  have hstable : (prefixWord ++ tailWord_1912520).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1912520).length < 2 ^ (prefixWord ++ tailWord_1912520).sum := by decide
  have hdescent : baseEnd_1912520 < baseStart_1912520 := by decide
  rcases family_descends (prefixWord ++ tailWord_1912520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1912627 : List Nat := [1, 1, 1, 2, 8, 1, 1, 2, 4]
def baseStart_1912627 : Nat := 118140960795 + 1912627 * 2 ^ 59
def prefixEnd_1912627 : Nat := 4983230072969 + 3 ^ 40 * 1912627 * 2
def baseEnd_1912627 : Nat := 436487539451997143007331

theorem tailTrace_1912627 : CollatzResearch.WordTrace tailWord_1912627 prefixEnd_1912627 436487539451997143007331 := by
  unfold tailWord_1912627
  simp only [CollatzResearch.WordTrace]
  refine ⟨69759237641886504530720135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46506158427924336353813423 69759237641886504530720135)
  ·
    refine ⟨104638856462829756796080203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69759237641886504530720135 104638856462829756796080203)
    ·
      refine ⟨156958284694244635194120305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104638856462829756796080203 156958284694244635194120305)
      ·
        refine ⟨117718713520683476395590229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156958284694244635194120305 117718713520683476395590229)
        ·
          refine ⟨1379516174070509489010823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 117718713520683476395590229 1379516174070509489010823)
          ·
            refine ⟨2069274261105764233516235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1379516174070509489010823 2069274261105764233516235)
            ·
              refine ⟨3103911391658646350274353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2069274261105764233516235 3103911391658646350274353)
              ·
                refine ⟨2327933543743984762705765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3103911391658646350274353 2327933543743984762705765)
                ·
                  refine ⟨436487539451997143007331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2327933543743984762705765 436487539451997143007331)
                  ·
                    rfl

theorem cell21_1912627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 1, 2, 4].length) (baseStart_1912627 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1912627 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1912627 prefixEnd_1912627 := by exact prefixLift 1912627
  have htrace : WordTrace (prefixWord ++ tailWord_1912627) baseStart_1912627 baseEnd_1912627 := by
    simpa [prefixWord, tailWord_1912627, baseEnd_1912627] using wordTrace_append hprefix tailTrace_1912627
  have hstable : (prefixWord ++ tailWord_1912627).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1912627).length < 2 ^ (prefixWord ++ tailWord_1912627).sum := by decide
  have hdescent : baseEnd_1912627 < baseStart_1912627 := by decide
  rcases family_descends (prefixWord ++ tailWord_1912627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1912672 : List Nat := [2, 1, 1, 3, 3, 4, 1, 3, 3]
def baseStart_1912672 : Nat := 118140960795 + 1912672 * 2 ^ 59
def prefixEnd_1912672 : Nat := 4983230072969 + 3 ^ 40 * 1912672 * 2
def baseEnd_1912672 : Nat := 436497809065087064757239

theorem tailTrace_1912672 : CollatzResearch.WordTrace tailWord_1912672 prefixEnd_1912672 436497809065087064757239 := by
  unfold tailWord_1912672
  simp only [CollatzResearch.WordTrace]
  refine ⟨34880439463361738608054135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46507252617815651477405513 34880439463361738608054135)
  ·
    refine ⟨52320659195042607912081203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34880439463361738608054135 52320659195042607912081203)
    ·
      refine ⟨78480988792563911868121805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52320659195042607912081203 78480988792563911868121805)
      ·
        refine ⟨29430370797211466950545677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78480988792563911868121805 29430370797211466950545677)
        ·
          refine ⟨11036389048954300106454629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29430370797211466950545677 11036389048954300106454629)
          ·
            refine ⟨2069322946678931269960243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11036389048954300106454629 2069322946678931269960243)
            ·
              refine ⟨3103984420018396904940365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2069322946678931269960243 3103984420018396904940365)
              ·
                refine ⟨1163994157506898839352637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3103984420018396904940365 1163994157506898839352637)
                ·
                  refine ⟨436497809065087064757239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1163994157506898839352637 436497809065087064757239)
                  ·
                    rfl

theorem cell21_1912672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 1, 3, 3].length) (baseStart_1912672 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1912672 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1912672 prefixEnd_1912672 := by exact prefixLift 1912672
  have htrace : WordTrace (prefixWord ++ tailWord_1912672) baseStart_1912672 baseEnd_1912672 := by
    simpa [prefixWord, tailWord_1912672, baseEnd_1912672] using wordTrace_append hprefix tailTrace_1912672
  have hstable : (prefixWord ++ tailWord_1912672).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1912672).length < 2 ^ (prefixWord ++ tailWord_1912672).sum := by decide
  have hdescent : baseEnd_1912672 < baseStart_1912672 := by decide
  rcases family_descends (prefixWord ++ tailWord_1912672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1912776 : List Nat := [2, 1, 3, 1, 4, 2, 3, 5]
def baseStart_1912776 : Nat := 118140960795 + 1912776 * 2 ^ 59
def prefixEnd_1912776 : Nat := 4983230072969 + 3 ^ 40 * 1912776 * 2
def baseEnd_1912776 : Nat := 145507181094001998341231

theorem tailTrace_1912776 : CollatzResearch.WordTrace tailWord_1912776 prefixEnd_1912776 145507181094001998341231 := by
  unfold tailWord_1912776
  simp only [CollatzResearch.WordTrace]
  refine ⟨34882336059173351488947091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46509781412231135318596121 34882336059173351488947091)
  ·
    refine ⟨52323504088760027233420637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34882336059173351488947091 52323504088760027233420637)
    ·
      refine ⟨19621314033285010212532739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52323504088760027233420637 19621314033285010212532739)
      ·
        refine ⟨29431971049927515318799109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19621314033285010212532739 29431971049927515318799109)
        ·
          refine ⟨5518494571861409122274833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29431971049927515318799109 5518494571861409122274833)
          ·
            refine ⟨4138870928896056841706125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5518494571861409122274833 4138870928896056841706125)
            ·
              refine ⟨1552076598336021315639797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4138870928896056841706125 1552076598336021315639797)
              ·
                refine ⟨145507181094001998341231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1552076598336021315639797 145507181094001998341231)
                ·
                  rfl

theorem cell21_1912776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 3, 5].length) (baseStart_1912776 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1912776 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1912776 prefixEnd_1912776 := by exact prefixLift 1912776
  have htrace : WordTrace (prefixWord ++ tailWord_1912776) baseStart_1912776 baseEnd_1912776 := by
    simpa [prefixWord, tailWord_1912776, baseEnd_1912776] using wordTrace_append hprefix tailTrace_1912776
  have hstable : (prefixWord ++ tailWord_1912776).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1912776).length < 2 ^ (prefixWord ++ tailWord_1912776).sum := by decide
  have hdescent : baseEnd_1912776 < baseStart_1912776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1912776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1912804 : List Nat := [2, 3, 1, 1, 1, 1, 5, 1, 6]
def baseStart_1912804 : Nat := 118140960795 + 1912804 * 2 ^ 59
def prefixEnd_1912804 : Nat := 4983230072969 + 3 ^ 40 * 1912804 * 2
def baseEnd_1912804 : Nat := 436527933263484168556969

theorem tailTrace_1912804 : CollatzResearch.WordTrace tailWord_1912804 prefixEnd_1912804 436527933263484168556969 := by
  unfold tailWord_1912804
  simp only [CollatzResearch.WordTrace]
  refine ⟨34882846681122631879956733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46510462241496842506608977 34882846681122631879956733)
  ·
    refine ⟨13081067505420986954983775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34882846681122631879956733 13081067505420986954983775)
    ·
      refine ⟨19621601258131480432475663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13081067505420986954983775 19621601258131480432475663)
      ·
        refine ⟨29432401887197220648713495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19621601258131480432475663 29432401887197220648713495)
        ·
          refine ⟨44148602830795830973070243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29432401887197220648713495 44148602830795830973070243)
          ·
            refine ⟨66222904246193746459605365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44148602830795830973070243 66222904246193746459605365)
            ·
              refine ⟨6208397273080663730588003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66222904246193746459605365 6208397273080663730588003)
              ·
                refine ⟨9312595909620995595882005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6208397273080663730588003 9312595909620995595882005)
                ·
                  refine ⟨436527933263484168556969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9312595909620995595882005 436527933263484168556969)
                  ·
                    rfl

theorem cell21_1912804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 1, 6].length) (baseStart_1912804 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1912804 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1912804 prefixEnd_1912804 := by exact prefixLift 1912804
  have htrace : WordTrace (prefixWord ++ tailWord_1912804) baseStart_1912804 baseEnd_1912804 := by
    simpa [prefixWord, tailWord_1912804, baseEnd_1912804] using wordTrace_append hprefix tailTrace_1912804
  have hstable : (prefixWord ++ tailWord_1912804).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1912804).length < 2 ^ (prefixWord ++ tailWord_1912804).sum := by decide
  have hdescent : baseEnd_1912804 < baseStart_1912804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1912804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1912807 : List Nat := [1, 1, 5, 2, 3, 1, 2, 1, 5]
def baseStart_1912807 : Nat := 118140960795 + 1912807 * 2 ^ 59
def prefixEnd_1912807 : Nat := 4983230072969 + 3 ^ 40 * 1912807 * 2
def baseEnd_1912807 : Nat := 436528617904356830006963

theorem tailTrace_1912807 : CollatzResearch.WordTrace tailWord_1912807 prefixEnd_1912807 436528617904356830006963 := by
  unfold tailWord_1912807
  simp only [CollatzResearch.WordTrace]
  refine ⟨69765802781234395272272675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46510535187489596848181783 69765802781234395272272675)
  ·
    refine ⟨104648704171851592908409013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69765802781234395272272675 104648704171851592908409013)
    ·
      refine ⟨9810816016111086835163345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 104648704171851592908409013 9810816016111086835163345)
      ·
        refine ⟨7358112012083315126372509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9810816016111086835163345 7358112012083315126372509)
        ·
          refine ⟨2759292004531243172389691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7358112012083315126372509 2759292004531243172389691)
          ·
            refine ⟨4138938006796864758584537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2759292004531243172389691 4138938006796864758584537)
            ·
              refine ⟨3104203505097648568938403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4138938006796864758584537 3104203505097648568938403)
              ·
                refine ⟨4656305257646472853407605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3104203505097648568938403 4656305257646472853407605)
                ·
                  refine ⟨436528617904356830006963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4656305257646472853407605 436528617904356830006963)
                  ·
                    rfl

theorem cell21_1912807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 2, 1, 5].length) (baseStart_1912807 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1912807 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1912807 prefixEnd_1912807 := by exact prefixLift 1912807
  have htrace : WordTrace (prefixWord ++ tailWord_1912807) baseStart_1912807 baseEnd_1912807 := by
    simpa [prefixWord, tailWord_1912807, baseEnd_1912807] using wordTrace_append hprefix tailTrace_1912807
  have hstable : (prefixWord ++ tailWord_1912807).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1912807).length < 2 ^ (prefixWord ++ tailWord_1912807).sum := by decide
  have hdescent : baseEnd_1912807 < baseStart_1912807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1912807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1912872 : List Nat := [2, 1, 5, 3, 1, 2, 2, 1, 4]
def baseStart_1912872 : Nat := 118140960795 + 1912872 * 2 ^ 59
def prefixEnd_1912872 : Nat := 4983230072969 + 3 ^ 40 * 1912872 * 2
def baseEnd_1912872 : Nat := 436543451789931161423497

theorem tailTrace_1912872 : CollatzResearch.WordTrace tailWord_1912872 prefixEnd_1912872 436543451789931161423497 := by
  unfold tailWord_1912872
  simp only [CollatzResearch.WordTrace]
  refine ⟨34884086762999455686694435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46512115683999274248925913 34884086762999455686694435)
  ·
    refine ⟨52326130144499183530041653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34884086762999455686694435 52326130144499183530041653)
    ·
      refine ⟨4905574701046798455941405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52326130144499183530041653 4905574701046798455941405)
      ·
        refine ⟨1839590512892549420978027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4905574701046798455941405 1839590512892549420978027)
        ·
          refine ⟨2759385769338824131467041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1839590512892549420978027 2759385769338824131467041)
          ·
            refine ⟨2069539327004118098600281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2759385769338824131467041 2069539327004118098600281)
            ·
              refine ⟨1552154495253088573950211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2069539327004118098600281 1552154495253088573950211)
              ·
                refine ⟨2328231742879632860925317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1552154495253088573950211 2328231742879632860925317)
                ·
                  refine ⟨436543451789931161423497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2328231742879632860925317 436543451789931161423497)
                  ·
                    rfl

theorem cell21_1912872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 2, 1, 4].length) (baseStart_1912872 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1912872 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1912872 prefixEnd_1912872 := by exact prefixLift 1912872
  have htrace : WordTrace (prefixWord ++ tailWord_1912872) baseStart_1912872 baseEnd_1912872 := by
    simpa [prefixWord, tailWord_1912872, baseEnd_1912872] using wordTrace_append hprefix tailTrace_1912872
  have hstable : (prefixWord ++ tailWord_1912872).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1912872).length < 2 ^ (prefixWord ++ tailWord_1912872).sum := by decide
  have hdescent : baseEnd_1912872 < baseStart_1912872 := by decide
  rcases family_descends (prefixWord ++ tailWord_1912872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1912914 : List Nat := [3, 2, 2, 1, 4, 1, 2, 2, 4]
def baseStart_1912914 : Nat := 118140960795 + 1912914 * 2 ^ 59
def prefixEnd_1912914 : Nat := 4983230072969 + 3 ^ 40 * 1912914 * 2
def baseEnd_1912914 : Nat := 436553036762148421723411

theorem tailTrace_1912914 : CollatzResearch.WordTrace tailWord_1912914 prefixEnd_1912914 436553036762148421723411 := by
  unfold tailWord_1912914
  simp only [CollatzResearch.WordTrace]
  refine ⟨17442426347961688136604449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46513136927897835030945197 17442426347961688136604449)
  ·
    refine ⟨13081819760971266102453337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17442426347961688136604449 13081819760971266102453337)
    ·
      refine ⟨9811364820728449576840003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13081819760971266102453337 9811364820728449576840003)
      ·
        refine ⟨14717047231092674365260005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9811364820728449576840003 14717047231092674365260005)
        ·
          refine ⟨2759446355829876443486251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14717047231092674365260005 2759446355829876443486251)
          ·
            refine ⟨4139169533744814665229377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2759446355829876443486251 4139169533744814665229377)
            ·
              refine ⟨3104377150308610998922033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4139169533744814665229377 3104377150308610998922033)
              ·
                refine ⟨2328282862731458249191525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3104377150308610998922033 2328282862731458249191525)
                ·
                  refine ⟨436553036762148421723411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2328282862731458249191525 436553036762148421723411)
                  ·
                    rfl

theorem cell21_1912914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 2, 2, 4].length) (baseStart_1912914 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1912914 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1912914 prefixEnd_1912914 := by exact prefixLift 1912914
  have htrace : WordTrace (prefixWord ++ tailWord_1912914) baseStart_1912914 baseEnd_1912914 := by
    simpa [prefixWord, tailWord_1912914, baseEnd_1912914] using wordTrace_append hprefix tailTrace_1912914
  have hstable : (prefixWord ++ tailWord_1912914).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1912914).length < 2 ^ (prefixWord ++ tailWord_1912914).sum := by decide
  have hdescent : baseEnd_1912914 < baseStart_1912914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1912914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1912942 : List Nat := [4, 1, 2, 2, 1, 1, 3, 2, 5]
def baseStart_1912942 : Nat := 118140960795 + 1912942 * 2 ^ 59
def prefixEnd_1912942 : Nat := 4983230072969 + 3 ^ 40 * 1912942 * 2
def baseEnd_1912942 : Nat := 436559426743626595256687

theorem tailTrace_1912942 : CollatzResearch.WordTrace tailWord_1912942 prefixEnd_1912942 436559426743626595256687 := by
  unfold tailWord_1912942
  simp only [CollatzResearch.WordTrace]
  refine ⟨8721340829468164166054635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46513817757163542218958053 8721340829468164166054635)
  ·
    refine ⟨13082011244202246249081953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8721340829468164166054635 13082011244202246249081953)
    ·
      refine ⟨9811508433151684686811465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13082011244202246249081953 9811508433151684686811465)
      ·
        refine ⟨7358631324863763515108599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9811508433151684686811465 7358631324863763515108599)
        ·
          refine ⟨11037946987295645272662899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7358631324863763515108599 11037946987295645272662899)
          ·
            refine ⟨16556920480943467908994349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11037946987295645272662899 16556920480943467908994349)
            ·
              refine ⟨6208845180353800465872881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16556920480943467908994349 6208845180353800465872881)
              ·
                refine ⟨4656633885265350349404661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6208845180353800465872881 4656633885265350349404661)
                ·
                  refine ⟨436559426743626595256687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4656633885265350349404661 436559426743626595256687)
                  ·
                    rfl

theorem cell21_1912942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 2, 5].length) (baseStart_1912942 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1912942 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1912942 prefixEnd_1912942 := by exact prefixLift 1912942
  have htrace : WordTrace (prefixWord ++ tailWord_1912942) baseStart_1912942 baseEnd_1912942 := by
    simpa [prefixWord, tailWord_1912942, baseEnd_1912942] using wordTrace_append hprefix tailTrace_1912942
  have hstable : (prefixWord ++ tailWord_1912942).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1912942).length < 2 ^ (prefixWord ++ tailWord_1912942).sum := by decide
  have hdescent : baseEnd_1912942 < baseStart_1912942 := by decide
  rcases family_descends (prefixWord ++ tailWord_1912942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1912982 : List Nat := [5, 3, 2, 1, 1, 1, 3, 1, 4]
def baseStart_1912982 : Nat := 118140960795 + 1912982 * 2 ^ 59
def prefixEnd_1912982 : Nat := 4983230072969 + 3 ^ 40 * 1912982 * 2
def baseEnd_1912982 : Nat := 436568555288595414589939

theorem tailTrace_1912982 : CollatzResearch.WordTrace tailWord_1912982 prefixEnd_1912982 436568555288595414589939 := by
  unfold tailWord_1912982
  simp only [CollatzResearch.WordTrace]
  refine ⟨4360761597225025009993325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46514790370400266773262133 4360761597225025009993325)
  ·
    refine ⟨1635285598959384378747497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4360761597225025009993325 1635285598959384378747497)
    ·
      refine ⟨1226464199219538284060623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1635285598959384378747497 1226464199219538284060623)
      ·
        refine ⟨1839696298829307426090935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1226464199219538284060623 1839696298829307426090935)
        ·
          refine ⟨2759544448243961139136403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1839696298829307426090935 2759544448243961139136403)
          ·
            refine ⟨4139316672365941708704605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2759544448243961139136403 4139316672365941708704605)
            ·
              refine ⟨1552243752137228140764227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4139316672365941708704605 1552243752137228140764227)
              ·
                refine ⟨2328365628205842211146341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1552243752137228140764227 2328365628205842211146341)
                ·
                  refine ⟨436568555288595414589939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2328365628205842211146341 436568555288595414589939)
                  ·
                    rfl

theorem cell21_1912982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_1912982 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1912982 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1912982 prefixEnd_1912982 := by exact prefixLift 1912982
  have htrace : WordTrace (prefixWord ++ tailWord_1912982) baseStart_1912982 baseEnd_1912982 := by
    simpa [prefixWord, tailWord_1912982, baseEnd_1912982] using wordTrace_append hprefix tailTrace_1912982
  have hstable : (prefixWord ++ tailWord_1912982).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1912982).length < 2 ^ (prefixWord ++ tailWord_1912982).sum := by decide
  have hdescent : baseEnd_1912982 < baseStart_1912982 := by decide
  rcases family_descends (prefixWord ++ tailWord_1912982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
