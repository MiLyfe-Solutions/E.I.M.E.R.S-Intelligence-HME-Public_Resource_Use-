import V185TrunkScan19Chunk002

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental

namespace V185TrunkScan19Incremental

def tailWord_30032 : List Nat := [2, 1, 1, 1, 1, 5, 4, 4]
def baseStart_30032 : Nat := 118140960795 + 30032 * 2 ^ 59
def prefixEnd_30032 : Nat := 4983230072969 + 3 ^ 40 * 30032 * 2
def baseEnd_30032 : Nat := 9138282083515101251491

theorem tailTrace_30032 : CollatzResearch.WordTrace tailWord_30032 prefixEnd_30032 9138282083515101251491 := by
  unfold tailWord_30032
  simp only [CollatzResearch.WordTrace]
  refine ⟨547678513603333951182175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 730238018137778601576233 547678513603333951182175)
  ·
    refine ⟨821517770405000926773263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 547678513603333951182175 821517770405000926773263)
    ·
      refine ⟨1232276655607501390159895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 821517770405000926773263 1232276655607501390159895)
      ·
        refine ⟨1848414983411252085239843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1232276655607501390159895 1848414983411252085239843)
        ·
          refine ⟨2772622475116878127859765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1848414983411252085239843 2772622475116878127859765)
          ·
            refine ⟨259933357042207324486853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2772622475116878127859765 259933357042207324486853)
            ·
              refine ⟨48737504445413873341285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 259933357042207324486853 48737504445413873341285)
              ·
                refine ⟨9138282083515101251491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48737504445413873341285 9138282083515101251491)
                ·
                  rfl

theorem cell19_30032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 4, 4].length) (baseStart_30032 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_30032 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_30032 prefixEnd_30032 := by exact prefixLift 30032
  have htrace : WordTrace (prefixWord ++ tailWord_30032) baseStart_30032 baseEnd_30032 := by
    simpa [prefixWord, tailWord_30032, baseEnd_30032] using wordTrace_append hprefix tailTrace_30032
  have hstable : (prefixWord ++ tailWord_30032).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30032).length < 2 ^ (prefixWord ++ tailWord_30032).sum := by decide
  have hdescent : baseEnd_30032 < baseStart_30032 := by decide
  rcases family_descends (prefixWord ++ tailWord_30032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30051 : List Nat := [1, 1, 1, 5, 2, 2, 2, 5]
def baseStart_30051 : Nat := 118140960795 + 30051 * 2 ^ 59
def prefixEnd_30051 : Nat := 4983230072969 + 3 ^ 40 * 30051 * 2
def baseEnd_30051 : Nat := 9144063495328686829217

theorem tailTrace_30051 : CollatzResearch.WordTrace tailWord_30051 prefixEnd_30051 9144063495328686829217 := by
  unfold tailWord_30051
  simp only [CollatzResearch.WordTrace]
  refine ⟨1096050014137834147306007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 730700009425222764870671 1096050014137834147306007)
  ·
    refine ⟨1644075021206751220959011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1096050014137834147306007 1644075021206751220959011)
    ·
      refine ⟨2466112531810126831438517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1644075021206751220959011 2466112531810126831438517)
      ·
        refine ⟨231198049857199390447361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2466112531810126831438517 231198049857199390447361)
        ·
          refine ⟨173398537392899542835521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231198049857199390447361 173398537392899542835521)
          ·
            refine ⟨130048903044674657126641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173398537392899542835521 130048903044674657126641)
            ·
              refine ⟨97536677283505992844981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130048903044674657126641 97536677283505992844981)
              ·
                refine ⟨9144063495328686829217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 97536677283505992844981 9144063495328686829217)
                ·
                  rfl

theorem cell19_30051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 5].length) (baseStart_30051 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_30051 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_30051 prefixEnd_30051 := by exact prefixLift 30051
  have htrace : WordTrace (prefixWord ++ tailWord_30051) baseStart_30051 baseEnd_30051 := by
    simpa [prefixWord, tailWord_30051, baseEnd_30051] using wordTrace_append hprefix tailTrace_30051
  have hstable : (prefixWord ++ tailWord_30051).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30051).length < 2 ^ (prefixWord ++ tailWord_30051).sum := by decide
  have hdescent : baseEnd_30051 < baseStart_30051 := by decide
  rcases family_descends (prefixWord ++ tailWord_30051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30070 : List Nat := [5, 1, 1, 12]
def baseStart_30070 : Nat := 118140960795 + 30070 * 2 ^ 59
def prefixEnd_30070 : Nat := 4983230072969 + 3 ^ 40 * 30070 * 2
def baseEnd_30070 : Nat := 112961048236324350703

theorem tailTrace_30070 : CollatzResearch.WordTrace tailWord_30070 prefixEnd_30070 112961048236324350703 := by
  unfold tailWord_30070
  simp only [CollatzResearch.WordTrace]
  refine ⟨68546437566812524515479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 731162000712666928165109 68546437566812524515479)
  ·
    refine ⟨102819656350218786773219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68546437566812524515479 102819656350218786773219)
    ·
      refine ⟨154229484525328180159829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102819656350218786773219 154229484525328180159829)
      ·
        refine ⟨112961048236324350703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 12 154229484525328180159829 112961048236324350703)
        ·
          rfl

theorem cell19_30070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 12].length) (baseStart_30070 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_30070 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_30070 prefixEnd_30070 := by exact prefixLift 30070
  have htrace : WordTrace (prefixWord ++ tailWord_30070) baseStart_30070 baseEnd_30070 := by
    simpa [prefixWord, tailWord_30070, baseEnd_30070] using wordTrace_append hprefix tailTrace_30070
  have hstable : (prefixWord ++ tailWord_30070).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30070).length < 2 ^ (prefixWord ++ tailWord_30070).sum := by decide
  have hdescent : baseEnd_30070 < baseStart_30070 := by decide
  rcases family_descends (prefixWord ++ tailWord_30070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30087 : List Nat := [1, 1, 4, 2, 2, 4, 1, 4]
def baseStart_30087 : Nat := 118140960795 + 30087 * 2 ^ 59
def prefixEnd_30087 : Nat := 4983230072969 + 3 ^ 40 * 30087 * 2
def baseEnd_30087 : Nat := 9155017749291270029119

theorem tailTrace_30087 : CollatzResearch.WordTrace tailWord_30087 prefixEnd_30087 9155017749291270029119 := by
  unfold tailWord_30087
  simp only [CollatzResearch.WordTrace]
  refine ⟨1097363042007412295616515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 731575361338274863744343 1097363042007412295616515)
  ·
    refine ⟨1646044563011118443424773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1097363042007412295616515 1646044563011118443424773)
    ·
      refine ⟨308633355564584708142145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1646044563011118443424773 308633355564584708142145)
      ·
        refine ⟨231475016673438531106609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 308633355564584708142145 231475016673438531106609)
        ·
          refine ⟨173606262505078898329957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231475016673438531106609 173606262505078898329957)
          ·
            refine ⟨32551174219702293436867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 173606262505078898329957 32551174219702293436867)
            ·
              refine ⟨48826761329553440155301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32551174219702293436867 48826761329553440155301)
              ·
                refine ⟨9155017749291270029119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48826761329553440155301 9155017749291270029119)
                ·
                  rfl

theorem cell19_30087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 1, 4].length) (baseStart_30087 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_30087 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_30087 prefixEnd_30087 := by exact prefixLift 30087
  have htrace : WordTrace (prefixWord ++ tailWord_30087) baseStart_30087 baseEnd_30087 := by
    simpa [prefixWord, tailWord_30087, baseEnd_30087] using wordTrace_append hprefix tailTrace_30087
  have hstable : (prefixWord ++ tailWord_30087).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30087).length < 2 ^ (prefixWord ++ tailWord_30087).sum := by decide
  have hdescent : baseEnd_30087 < baseStart_30087 := by decide
  rcases family_descends (prefixWord ++ tailWord_30087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30104 : List Nat := [2, 1, 2, 5, 2, 1, 3, 3]
def baseStart_30104 : Nat := 118140960795 + 30104 * 2 ^ 59
def prefixEnd_30104 : Nat := 4983230072969 + 3 ^ 40 * 30104 * 2
def baseEnd_30104 : Nat := 9160190591440267651295

theorem tailTrace_30104 : CollatzResearch.WordTrace tailWord_30104 prefixEnd_30104 9160190591440267651295 := by
  unfold tailWord_30104
  simp only [CollatzResearch.WordTrace]
  refine ⟨548991541472912099492683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 731988721963882799323577 548991541472912099492683)
  ·
    refine ⟨823487312209368149239025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 548991541472912099492683 823487312209368149239025)
    ·
      refine ⟨617615484157026111929269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 823487312209368149239025 617615484157026111929269)
      ·
        refine ⟨57901451639721197993369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 617615484157026111929269 57901451639721197993369)
        ·
          refine ⟨43426088729790898495027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57901451639721197993369 43426088729790898495027)
          ·
            refine ⟨65139133094686347742541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43426088729790898495027 65139133094686347742541)
            ·
              refine ⟨24427174910507380403453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65139133094686347742541 24427174910507380403453)
              ·
                refine ⟨9160190591440267651295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24427174910507380403453 9160190591440267651295)
                ·
                  rfl

theorem cell19_30104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 3, 3].length) (baseStart_30104 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_30104 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_30104 prefixEnd_30104 := by exact prefixLift 30104
  have htrace : WordTrace (prefixWord ++ tailWord_30104) baseStart_30104 baseEnd_30104 := by
    simpa [prefixWord, tailWord_30104, baseEnd_30104] using wordTrace_append hprefix tailTrace_30104
  have hstable : (prefixWord ++ tailWord_30104).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30104).length < 2 ^ (prefixWord ++ tailWord_30104).sum := by decide
  have hdescent : baseEnd_30104 < baseStart_30104 := by decide
  rcases family_descends (prefixWord ++ tailWord_30104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30106 : List Nat := [3, 1, 1, 4, 1, 1, 5, 3]
def baseStart_30106 : Nat := 118140960795 + 30106 * 2 ^ 59
def prefixEnd_30106 : Nat := 4983230072969 + 3 ^ 40 * 30106 * 2
def baseEnd_30106 : Nat := 9160799161104855606845

theorem tailTrace_30106 : CollatzResearch.WordTrace tailWord_30106 prefixEnd_30106 9160799161104855606845 := by
  unfold tailWord_30106
  simp only [CollatzResearch.WordTrace]
  refine ⟨274514007234644635139543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 732037352625719027038781 274514007234644635139543)
  ·
    refine ⟨411771010851966952709315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274514007234644635139543 411771010851966952709315)
    ·
      refine ⟨617656516277950429063973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 411771010851966952709315 617656516277950429063973)
      ·
        refine ⟨115810596802115705449495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 617656516277950429063973 115810596802115705449495)
        ·
          refine ⟨173715895203173558174243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115810596802115705449495 173715895203173558174243)
          ·
            refine ⟨260573842804760337261365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173715895203173558174243 260573842804760337261365)
            ·
              refine ⟨24428797762946281618253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 260573842804760337261365 24428797762946281618253)
              ·
                refine ⟨9160799161104855606845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24428797762946281618253 9160799161104855606845)
                ·
                  rfl

theorem cell19_30106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 5, 3].length) (baseStart_30106 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_30106 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_30106 prefixEnd_30106 := by exact prefixLift 30106
  have htrace : WordTrace (prefixWord ++ tailWord_30106) baseStart_30106 baseEnd_30106 := by
    simpa [prefixWord, tailWord_30106, baseEnd_30106] using wordTrace_append hprefix tailTrace_30106
  have hstable : (prefixWord ++ tailWord_30106).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30106).length < 2 ^ (prefixWord ++ tailWord_30106).sum := by decide
  have hdescent : baseEnd_30106 < baseStart_30106 := by decide
  rcases family_descends (prefixWord ++ tailWord_30106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30125 : List Nat := [1, 5, 2, 2, 1, 2, 6]
def baseStart_30125 : Nat := 118140960795 + 30125 * 2 ^ 59
def prefixEnd_30125 : Nat := 4983230072969 + 3 ^ 40 * 30125 * 2
def baseEnd_30125 : Nat := 3055526857639480394857

theorem tailTrace_30125 : CollatzResearch.WordTrace tailWord_30125 prefixEnd_30125 3055526857639480394857 := by
  unfold tailWord_30125
  simp only [CollatzResearch.WordTrace]
  refine ⟨1098749015869744785499829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 732499343913163190333219 1098749015869744785499829)
  ·
    refine ⟨103007720237788573640609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1098749015869744785499829 103007720237788573640609)
    ·
      refine ⟨77255790178341430230457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103007720237788573640609 77255790178341430230457)
      ·
        refine ⟨57941842633756072672843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77255790178341430230457 57941842633756072672843)
        ·
          refine ⟨86912763950634109009265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57941842633756072672843 86912763950634109009265)
          ·
            refine ⟨65184572962975581756949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86912763950634109009265 65184572962975581756949)
            ·
              refine ⟨3055526857639480394857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 65184572962975581756949 3055526857639480394857)
              ·
                rfl

theorem cell19_30125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 6].length) (baseStart_30125 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_30125 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_30125 prefixEnd_30125 := by exact prefixLift 30125
  have htrace : WordTrace (prefixWord ++ tailWord_30125) baseStart_30125 baseEnd_30125 := by
    simpa [prefixWord, tailWord_30125, baseEnd_30125] using wordTrace_append hprefix tailTrace_30125
  have hstable : (prefixWord ++ tailWord_30125).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30125).length < 2 ^ (prefixWord ++ tailWord_30125).sum := by decide
  have hdescent : baseEnd_30125 < baseStart_30125 := by decide
  rcases family_descends (prefixWord ++ tailWord_30125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30165 : List Nat := [1, 3, 2, 3, 1, 1, 3, 5]
def baseStart_30165 : Nat := 118140960795 + 30165 * 2 ^ 59
def prefixEnd_30165 : Nat := 4983230072969 + 3 ^ 40 * 30165 * 2
def baseEnd_30165 : Nat := 9178751966210200295573

theorem tailTrace_30165 : CollatzResearch.WordTrace tailWord_30165 prefixEnd_30165 9178751966210200295573 := by
  unfold tailWord_30165
  simp only [CollatzResearch.WordTrace]
  refine ⟨1100207935724831616955949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 733471957149887744637299 1100207935724831616955949)
  ·
    refine ⟨412577975896811856358481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1100207935724831616955949 412577975896811856358481)
    ·
      refine ⟨309433481922608892268861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 412577975896811856358481 309433481922608892268861)
      ·
        refine ⟨116037555720978334600823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 309433481922608892268861 116037555720978334600823)
        ·
          refine ⟨174056333581467501901235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116037555720978334600823 174056333581467501901235)
          ·
            refine ⟨261084500372201252851853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174056333581467501901235 261084500372201252851853)
            ·
              refine ⟨97906687639575469819445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 261084500372201252851853 97906687639575469819445)
              ·
                refine ⟨9178751966210200295573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 97906687639575469819445 9178751966210200295573)
                ·
                  rfl

theorem cell19_30165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 5].length) (baseStart_30165 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_30165 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_30165 prefixEnd_30165 := by exact prefixLift 30165
  have htrace : WordTrace (prefixWord ++ tailWord_30165) baseStart_30165 baseEnd_30165 := by
    simpa [prefixWord, tailWord_30165, baseEnd_30165] using wordTrace_append hprefix tailTrace_30165
  have hstable : (prefixWord ++ tailWord_30165).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30165).length < 2 ^ (prefixWord ++ tailWord_30165).sum := by decide
  have hdescent : baseEnd_30165 < baseStart_30165 := by decide
  rcases family_descends (prefixWord ++ tailWord_30165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30243 : List Nat := [1, 1, 1, 4, 12]
def baseStart_30243 : Nat := 118140960795 + 30243 * 2 ^ 59
def prefixEnd_30243 : Nat := 4983230072969 + 3 ^ 40 * 30243 * 2
def baseEnd_30243 : Nat := 340832821597375206001

theorem tailTrace_30243 : CollatzResearch.WordTrace tailWord_30243 prefixEnd_30243 340832821597375206001 := by
  unfold tailWord_30243
  simp only [CollatzResearch.WordTrace]
  refine ⟨1103052829442250938295383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 735368552961500625530255 1103052829442250938295383)
  ·
    refine ⟨1654579244163376407443075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1103052829442250938295383 1654579244163376407443075)
    ·
      refine ⟨2481868866245064611164613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1654579244163376407443075 2481868866245064611164613)
      ·
        refine ⟨465350412420949614593365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2481868866245064611164613 465350412420949614593365)
        ·
          refine ⟨340832821597375206001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 465350412420949614593365 340832821597375206001)
          ·
            rfl

theorem cell19_30243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 12].length) (baseStart_30243 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_30243 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_30243 prefixEnd_30243 := by exact prefixLift 30243
  have htrace : WordTrace (prefixWord ++ tailWord_30243) baseStart_30243 baseEnd_30243 := by
    simpa [prefixWord, tailWord_30243, baseEnd_30243] using wordTrace_append hprefix tailTrace_30243
  have hstable : (prefixWord ++ tailWord_30243).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30243).length < 2 ^ (prefixWord ++ tailWord_30243).sum := by decide
  have hdescent : baseEnd_30243 < baseStart_30243 := by decide
  rcases family_descends (prefixWord ++ tailWord_30243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30281 : List Nat := [1, 2, 1, 1, 2, 2, 1, 9]
def baseStart_30281 : Nat := 118140960795 + 30281 * 2 ^ 59
def prefixEnd_30281 : Nat := 4983230072969 + 3 ^ 40 * 30281 * 2
def baseEnd_30281 : Nat := 9214049006756301717479

theorem tailTrace_30281 : CollatzResearch.WordTrace tailWord_30281 prefixEnd_30281 9214049006756301717479 := by
  unfold tailWord_30281
  simp only [CollatzResearch.WordTrace]
  refine ⟨1104438803304583428178697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 736292535536388952119131 1104438803304583428178697)
  ·
    refine ⟨828329102478437571134023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1104438803304583428178697 828329102478437571134023)
    ·
      refine ⟨1242493653717656356701035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 828329102478437571134023 1242493653717656356701035)
      ·
        refine ⟨1863740480576484535051553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1242493653717656356701035 1863740480576484535051553)
        ·
          refine ⟨1397805360432363401288665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1863740480576484535051553 1397805360432363401288665)
          ·
            refine ⟨1048354020324272550966499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1397805360432363401288665 1048354020324272550966499)
            ·
              refine ⟨1572531030486408826449749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1048354020324272550966499 1572531030486408826449749)
              ·
                refine ⟨9214049006756301717479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1572531030486408826449749 9214049006756301717479)
                ·
                  rfl

theorem cell19_30281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 9].length) (baseStart_30281 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_30281 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_30281 prefixEnd_30281 := by exact prefixLift 30281
  have htrace : WordTrace (prefixWord ++ tailWord_30281) baseStart_30281 baseEnd_30281 := by
    simpa [prefixWord, tailWord_30281, baseEnd_30281] using wordTrace_append hprefix tailTrace_30281
  have hstable : (prefixWord ++ tailWord_30281).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30281).length < 2 ^ (prefixWord ++ tailWord_30281).sum := by decide
  have hdescent : baseEnd_30281 < baseStart_30281 := by decide
  rcases family_descends (prefixWord ++ tailWord_30281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30319 : List Nat := [1, 1, 2, 1, 3, 2, 1, 8]
def baseStart_30319 : Nat := 118140960795 + 30319 * 2 ^ 59
def prefixEnd_30319 : Nat := 4983230072969 + 3 ^ 40 * 30319 * 2
def baseEnd_30319 : Nat := 9225611830383472872931

theorem tailTrace_30319 : CollatzResearch.WordTrace tailWord_30319 prefixEnd_30319 9225611830383472872931 := by
  unfold tailWord_30319
  simp only [CollatzResearch.WordTrace]
  refine ⟨1105824777166915918062011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 737216518111277278708007 1105824777166915918062011)
  ·
    refine ⟨1658737165750373877093017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1105824777166915918062011 1658737165750373877093017)
    ·
      refine ⟨1244052874312780407819763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1658737165750373877093017 1244052874312780407819763)
      ·
        refine ⟨1866079311469170611729645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1244052874312780407819763 1866079311469170611729645)
        ·
          refine ⟨699779741800938979398617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1866079311469170611729645 699779741800938979398617)
          ·
            refine ⟨524834806350704234548963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 699779741800938979398617 524834806350704234548963)
            ·
              refine ⟨787252209526056351823445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 524834806350704234548963 787252209526056351823445)
              ·
                refine ⟨9225611830383472872931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 787252209526056351823445 9225611830383472872931)
                ·
                  rfl

theorem cell19_30319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 8].length) (baseStart_30319 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_30319 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_30319 prefixEnd_30319 := by exact prefixLift 30319
  have htrace : WordTrace (prefixWord ++ tailWord_30319) baseStart_30319 baseEnd_30319 := by
    simpa [prefixWord, tailWord_30319, baseEnd_30319] using wordTrace_append hprefix tailTrace_30319
  have hstable : (prefixWord ++ tailWord_30319).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30319).length < 2 ^ (prefixWord ++ tailWord_30319).sum := by decide
  have hdescent : baseEnd_30319 < baseStart_30319 := by decide
  rcases family_descends (prefixWord ++ tailWord_30319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30370 : List Nat := [3, 3, 1, 4, 1, 1, 2, 4]
def baseStart_30370 : Nat := 118140960795 + 30370 * 2 ^ 59
def prefixEnd_30370 : Nat := 4983230072969 + 3 ^ 40 * 30370 * 2
def baseEnd_30370 : Nat := 9241130356830465739459

theorem tailTrace_30370 : CollatzResearch.WordTrace tailWord_30370 prefixEnd_30370 9241130356830465739459 := by
  unfold tailWord_30370
  simp only [CollatzResearch.WordTrace]
  refine ⟨276921224995537907042141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 738456599988101085445709 276921224995537907042141)
  ·
    refine ⟨103845459373326715140803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 276921224995537907042141 103845459373326715140803)
    ·
      refine ⟨155768189059990072711205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103845459373326715140803 155768189059990072711205)
      ·
        refine ⟨29206535448748138633351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 155768189059990072711205 29206535448748138633351)
        ·
          refine ⟨43809803173122207950027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29206535448748138633351 43809803173122207950027)
          ·
            refine ⟨65714704759683311925041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43809803173122207950027 65714704759683311925041)
            ·
              refine ⟨49286028569762483943781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65714704759683311925041 49286028569762483943781)
              ·
                refine ⟨9241130356830465739459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49286028569762483943781 9241130356830465739459)
                ·
                  rfl

theorem cell19_30370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 2, 4].length) (baseStart_30370 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_30370 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_30370 prefixEnd_30370 := by exact prefixLift 30370
  have htrace : WordTrace (prefixWord ++ tailWord_30370) baseStart_30370 baseEnd_30370 := by
    simpa [prefixWord, tailWord_30370, baseEnd_30370] using wordTrace_append hprefix tailTrace_30370
  have hstable : (prefixWord ++ tailWord_30370).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30370).length < 2 ^ (prefixWord ++ tailWord_30370).sum := by decide
  have hdescent : baseEnd_30370 < baseStart_30370 := by decide
  rcases family_descends (prefixWord ++ tailWord_30370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30412 : List Nat := [2, 2, 1, 5, 2, 7]
def baseStart_30412 : Nat := 118140960795 + 30412 * 2 ^ 59
def prefixEnd_30412 : Nat := 4983230072969 + 3 ^ 40 * 30412 * 2
def baseEnd_30412 : Nat := 1028212257754090311779

theorem tailTrace_30412 : CollatzResearch.WordTrace tailWord_30412 prefixEnd_30412 1028212257754090311779 := by
  unfold tailWord_30412
  simp only [CollatzResearch.WordTrace]
  refine ⟨554608382914996400598745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 739477843886661867464993 554608382914996400598745)
  ·
    refine ⟨415956287186247300449059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 554608382914996400598745 415956287186247300449059)
    ·
      refine ⟨623934430779370950673589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415956287186247300449059 623934430779370950673589)
      ·
        refine ⟨58493852885566026625649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 623934430779370950673589 58493852885566026625649)
        ·
          refine ⟨43870389664174519969237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58493852885566026625649 43870389664174519969237)
          ·
            refine ⟨1028212257754090311779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 43870389664174519969237 1028212257754090311779)
            ·
              rfl

theorem cell19_30412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 7].length) (baseStart_30412 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_30412 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_30412 prefixEnd_30412 := by exact prefixLift 30412
  have htrace : WordTrace (prefixWord ++ tailWord_30412) baseStart_30412 baseEnd_30412 := by
    simpa [prefixWord, tailWord_30412, baseEnd_30412] using wordTrace_append hprefix tailTrace_30412
  have hstable : (prefixWord ++ tailWord_30412).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30412).length < 2 ^ (prefixWord ++ tailWord_30412).sum := by decide
  have hdescent : baseEnd_30412 < baseStart_30412 := by decide
  rcases family_descends (prefixWord ++ tailWord_30412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30526 : List Nat := [4, 2, 1, 2, 2, 1, 7]
def baseStart_30526 : Nat := 118140960795 + 30526 * 2 ^ 59
def prefixEnd_30526 : Nat := 4983230072969 + 3 ^ 40 * 30526 * 2
def baseEnd_30526 : Nat := 3096199596889442090789

theorem tailTrace_30526 : CollatzResearch.WordTrace tailWord_30526 prefixEnd_30526 3096199596889442090789 := by
  unfold tailWord_30526
  simp only [CollatzResearch.WordTrace]
  refine ⟨139171835927123783855929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 742249791611326847231621 139171835927123783855929)
  ·
    refine ⟨104378876945342837891947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139171835927123783855929 104378876945342837891947)
    ·
      refine ⟨156568315418014256837921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104378876945342837891947 156568315418014256837921)
      ·
        refine ⟨117426236563510692628441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156568315418014256837921 117426236563510692628441)
        ·
          refine ⟨88069677422633019471331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117426236563510692628441 88069677422633019471331)
          ·
            refine ⟨132104516133949529206997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88069677422633019471331 132104516133949529206997)
            ·
              refine ⟨3096199596889442090789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 132104516133949529206997 3096199596889442090789)
              ·
                rfl

theorem cell19_30526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 7].length) (baseStart_30526 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_30526 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_30526 prefixEnd_30526 := by exact prefixLift 30526
  have htrace : WordTrace (prefixWord ++ tailWord_30526) baseStart_30526 baseEnd_30526 := by
    simpa [prefixWord, tailWord_30526, baseEnd_30526] using wordTrace_append hprefix tailTrace_30526
  have hstable : (prefixWord ++ tailWord_30526).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30526).length < 2 ^ (prefixWord ++ tailWord_30526).sum := by decide
  have hdescent : baseEnd_30526 < baseStart_30526 := by decide
  rcases family_descends (prefixWord ++ tailWord_30526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30545 : List Nat := [1, 2, 2, 1, 5, 2, 2, 4]
def baseStart_30545 : Nat := 118140960795 + 30545 * 2 ^ 59
def prefixEnd_30545 : Nat := 4983230072969 + 3 ^ 40 * 30545 * 2
def baseEnd_30545 : Nat := 9294380202481911850093

theorem tailTrace_30545 : CollatzResearch.WordTrace tailWord_30545 prefixEnd_30545 9294380202481911850093 := by
  unfold tailWord_30545
  simp only [CollatzResearch.WordTrace]
  refine ⟨1114067674348156515789089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 742711782898771010526059 1114067674348156515789089)
  ·
    refine ⟨835550755761117386841817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1114067674348156515789089 835550755761117386841817)
    ·
      refine ⟨626663066820838040131363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 835550755761117386841817 626663066820838040131363)
      ·
        refine ⟨939994600231257060197045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 626663066820838040131363 939994600231257060197045)
        ·
          refine ⟨88124493771680349393473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 939994600231257060197045 88124493771680349393473)
          ·
            refine ⟨66093370328760262045105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88124493771680349393473 66093370328760262045105)
            ·
              refine ⟨49570027746570196533829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66093370328760262045105 49570027746570196533829)
              ·
                refine ⟨9294380202481911850093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49570027746570196533829 9294380202481911850093)
                ·
                  rfl

theorem cell19_30545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 2, 4].length) (baseStart_30545 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_30545 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_30545 prefixEnd_30545 := by exact prefixLift 30545
  have htrace : WordTrace (prefixWord ++ tailWord_30545) baseStart_30545 baseEnd_30545 := by
    simpa [prefixWord, tailWord_30545, baseEnd_30545] using wordTrace_append hprefix tailTrace_30545
  have hstable : (prefixWord ++ tailWord_30545).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30545).length < 2 ^ (prefixWord ++ tailWord_30545).sum := by decide
  have hdescent : baseEnd_30545 < baseStart_30545 := by decide
  rcases family_descends (prefixWord ++ tailWord_30545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30600 : List Nat := [2, 1, 3, 3, 3, 2, 1, 4]
def baseStart_30600 : Nat := 118140960795 + 30600 * 2 ^ 59
def prefixEnd_30600 : Nat := 4983230072969 + 3 ^ 40 * 30600 * 2
def baseEnd_30600 : Nat := 9311115868258080627721

theorem tailTrace_30600 : CollatzResearch.WordTrace tailWord_30600 prefixEnd_30600 9311115868258080627721 := by
  unfold tailWord_30600
  simp only [CollatzResearch.WordTrace]
  refine ⟨558036844574450454520627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 744049126099267272694169 558036844574450454520627)
  ·
    refine ⟨837055266861675681780941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 558036844574450454520627 837055266861675681780941)
    ·
      refine ⟨313895725073128380667853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 837055266861675681780941 313895725073128380667853)
      ·
        refine ⟨117710896902423142750445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 313895725073128380667853 117710896902423142750445)
        ·
          refine ⟨44141586338408678531417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117710896902423142750445 44141586338408678531417)
          ·
            refine ⟨33106189753806508898563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44141586338408678531417 33106189753806508898563)
            ·
              refine ⟨49659284630709763347845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33106189753806508898563 49659284630709763347845)
              ·
                refine ⟨9311115868258080627721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49659284630709763347845 9311115868258080627721)
                ·
                  rfl

theorem cell19_30600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 1, 4].length) (baseStart_30600 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_30600 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_30600 prefixEnd_30600 := by exact prefixLift 30600
  have htrace : WordTrace (prefixWord ++ tailWord_30600) baseStart_30600 baseEnd_30600 := by
    simpa [prefixWord, tailWord_30600, baseEnd_30600] using wordTrace_append hprefix tailTrace_30600
  have hstable : (prefixWord ++ tailWord_30600).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30600).length < 2 ^ (prefixWord ++ tailWord_30600).sum := by decide
  have hdescent : baseEnd_30600 < baseStart_30600 := by decide
  rcases family_descends (prefixWord ++ tailWord_30600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30674 : List Nat := [3, 2, 2, 3, 2, 2, 2, 3]
def baseStart_30674 : Nat := 118140960795 + 30674 * 2 ^ 59
def prefixEnd_30674 : Nat := 4983230072969 + 3 ^ 40 * 30674 * 2
def baseEnd_30674 : Nat := 9333632945847834983075

theorem tailTrace_30674 : CollatzResearch.WordTrace tailWord_30674 prefixEnd_30674 9333632945847834983075 := by
  unfold tailWord_30674
  simp only [CollatzResearch.WordTrace]
  refine ⟨279693172720202886808769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 745848460587207698156717 279693172720202886808769)
  ·
    refine ⟨209769879540152165106577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279693172720202886808769 209769879540152165106577)
    ·
      refine ⟨157327409655114123829933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209769879540152165106577 157327409655114123829933)
      ·
        refine ⟨58997778620667796436225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157327409655114123829933 58997778620667796436225)
        ·
          refine ⟨44248333965500847327169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58997778620667796436225 44248333965500847327169)
          ·
            refine ⟨33186250474125635495377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44248333965500847327169 33186250474125635495377)
            ·
              refine ⟨24889687855594226621533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33186250474125635495377 24889687855594226621533)
              ·
                refine ⟨9333632945847834983075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24889687855594226621533 9333632945847834983075)
                ·
                  rfl

theorem cell19_30674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 2, 3].length) (baseStart_30674 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_30674 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_30674 prefixEnd_30674 := by exact prefixLift 30674
  have htrace : WordTrace (prefixWord ++ tailWord_30674) baseStart_30674 baseEnd_30674 := by
    simpa [prefixWord, tailWord_30674, baseEnd_30674] using wordTrace_append hprefix tailTrace_30674
  have hstable : (prefixWord ++ tailWord_30674).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30674).length < 2 ^ (prefixWord ++ tailWord_30674).sum := by decide
  have hdescent : baseEnd_30674 < baseStart_30674 := by decide
  rcases family_descends (prefixWord ++ tailWord_30674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30680 : List Nat := [2, 1, 2, 2, 2, 2, 3, 5]
def baseStart_30680 : Nat := 118140960795 + 30680 * 2 ^ 59
def prefixEnd_30680 : Nat := 4983230072969 + 3 ^ 40 * 30680 * 2
def baseEnd_30680 : Nat := 9335458654841598849725

theorem tailTrace_30680 : CollatzResearch.WordTrace tailWord_30680 prefixEnd_30680 9335458654841598849725 := by
  unfold tailWord_30680
  simp only [CollatzResearch.WordTrace]
  refine ⟨559495764429537285976747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 745994352572716381302329 559495764429537285976747)
  ·
    refine ⟨839243646644305928965121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 559495764429537285976747 839243646644305928965121)
    ·
      refine ⟨629432734983229446723841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 839243646644305928965121 629432734983229446723841)
      ·
        refine ⟨472074551237422085042881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 629432734983229446723841 472074551237422085042881)
        ·
          refine ⟨354055913428066563782161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 472074551237422085042881 354055913428066563782161)
          ·
            refine ⟨265541935071049922836621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 354055913428066563782161 265541935071049922836621)
            ·
              refine ⟨99578225651643721063733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 265541935071049922836621 99578225651643721063733)
              ·
                refine ⟨9335458654841598849725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 99578225651643721063733 9335458654841598849725)
                ·
                  rfl

theorem cell19_30680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 5].length) (baseStart_30680 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_30680 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_30680 prefixEnd_30680 := by exact prefixLift 30680
  have htrace : WordTrace (prefixWord ++ tailWord_30680) baseStart_30680 baseEnd_30680 := by
    simpa [prefixWord, tailWord_30680, baseEnd_30680] using wordTrace_append hprefix tailTrace_30680
  have hstable : (prefixWord ++ tailWord_30680).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30680).length < 2 ^ (prefixWord ++ tailWord_30680).sum := by decide
  have hdescent : baseEnd_30680 < baseStart_30680 := by decide
  rcases family_descends (prefixWord ++ tailWord_30680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30695 : List Nat := [1, 1, 5, 2, 4, 1, 5]
def baseStart_30695 : Nat := 118140960795 + 30695 * 2 ^ 59
def prefixEnd_30695 : Nat := 4983230072969 + 3 ^ 40 * 30695 * 2
def baseEnd_30695 : Nat := 3113340975775336172117

theorem tailTrace_30695 : CollatzResearch.WordTrace tailWord_30695 prefixEnd_30695 3113340975775336172117 := by
  unfold tailWord_30695
  simp only [CollatzResearch.WordTrace]
  refine ⟨1119538623804732133749539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 746359082536488089166359 1119538623804732133749539)
  ·
    refine ⟨1679307935707098200624309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1119538623804732133749539 1679307935707098200624309)
    ·
      refine ⟨157435118972540456308529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1679307935707098200624309 157435118972540456308529)
      ·
        refine ⟨118076339229405342231397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157435118972540456308529 118076339229405342231397)
        ·
          refine ⟨22139313605513501668387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118076339229405342231397 22139313605513501668387)
          ·
            refine ⟨33208970408270252502581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22139313605513501668387 33208970408270252502581)
            ·
              refine ⟨3113340975775336172117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33208970408270252502581 3113340975775336172117)
              ·
                rfl

theorem cell19_30695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 5].length) (baseStart_30695 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_30695 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_30695 prefixEnd_30695 := by exact prefixLift 30695
  have htrace : WordTrace (prefixWord ++ tailWord_30695) baseStart_30695 baseEnd_30695 := by
    simpa [prefixWord, tailWord_30695, baseEnd_30695] using wordTrace_append hprefix tailTrace_30695
  have hstable : (prefixWord ++ tailWord_30695).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30695).length < 2 ^ (prefixWord ++ tailWord_30695).sum := by decide
  have hdescent : baseEnd_30695 < baseStart_30695 := by decide
  rcases family_descends (prefixWord ++ tailWord_30695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30756 : List Nat := [2, 3, 1, 4, 9]
def baseStart_30756 : Nat := 118140960795 + 30756 * 2 ^ 59
def prefixEnd_30756 : Nat := 4983230072969 + 3 ^ 40 * 30756 * 2
def baseEnd_30756 : Nat := 346614233410960783727

theorem tailTrace_30756 : CollatzResearch.WordTrace tailWord_30756 prefixEnd_30756 346614233410960783727 := by
  unfold tailWord_30756
  simp only [CollatzResearch.WordTrace]
  refine ⟨560881738291869775860061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 747842317722493034480081 560881738291869775860061)
  ·
    refine ⟨210330651859451165947523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 560881738291869775860061 210330651859451165947523)
    ·
      refine ⟨315495977789176748921285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210330651859451165947523 315495977789176748921285)
      ·
        refine ⟨59155495835470640422741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 315495977789176748921285 59155495835470640422741)
        ·
          refine ⟨346614233410960783727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 59155495835470640422741 346614233410960783727)
          ·
            rfl

theorem cell19_30756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 9].length) (baseStart_30756 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_30756 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_30756 prefixEnd_30756 := by exact prefixLift 30756
  have htrace : WordTrace (prefixWord ++ tailWord_30756) baseStart_30756 baseEnd_30756 := by
    simpa [prefixWord, tailWord_30756, baseEnd_30756] using wordTrace_append hprefix tailTrace_30756
  have hstable : (prefixWord ++ tailWord_30756).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30756).length < 2 ^ (prefixWord ++ tailWord_30756).sum := by decide
  have hdescent : baseEnd_30756 < baseStart_30756 := by decide
  rcases family_descends (prefixWord ++ tailWord_30756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30775 : List Nat := [1, 1, 3, 1, 2, 2, 5, 4]
def baseStart_30775 : Nat := 118140960795 + 30775 * 2 ^ 59
def prefixEnd_30775 : Nat := 4983230072969 + 3 ^ 40 * 30775 * 2
def baseEnd_30775 : Nat := 9364365713909526738355

theorem tailTrace_30775 : CollatzResearch.WordTrace tailWord_30775 prefixEnd_30775 9364365713909526738355 := by
  unfold tailWord_30775
  simp only [CollatzResearch.WordTrace]
  refine ⟨1122456463514905796661779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 748304309009937197774519 1122456463514905796661779)
  ·
    refine ⟨1683684695272358694992669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1122456463514905796661779 1683684695272358694992669)
    ·
      refine ⟨631381760727134510622251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1683684695272358694992669 631381760727134510622251)
      ·
        refine ⟨947072641090701765933377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 631381760727134510622251 947072641090701765933377)
        ·
          refine ⟨710304480818026324450033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 947072641090701765933377 710304480818026324450033)
          ·
            refine ⟨532728360613519743337525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 710304480818026324450033 532728360613519743337525)
            ·
              refine ⟨49943283807517475937893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 532728360613519743337525 49943283807517475937893)
              ·
                refine ⟨9364365713909526738355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49943283807517475937893 9364365713909526738355)
                ·
                  rfl

theorem cell19_30775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 5, 4].length) (baseStart_30775 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_30775 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_30775 prefixEnd_30775 := by exact prefixLift 30775
  have htrace : WordTrace (prefixWord ++ tailWord_30775) baseStart_30775 baseEnd_30775 := by
    simpa [prefixWord, tailWord_30775, baseEnd_30775] using wordTrace_append hprefix tailTrace_30775
  have hstable : (prefixWord ++ tailWord_30775).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30775).length < 2 ^ (prefixWord ++ tailWord_30775).sum := by decide
  have hdescent : baseEnd_30775 < baseStart_30775 := by decide
  rcases family_descends (prefixWord ++ tailWord_30775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30849 : List Nat := [1, 2, 4, 2, 3, 1, 1, 5]
def baseStart_30849 : Nat := 118140960795 + 30849 * 2 ^ 59
def prefixEnd_30849 : Nat := 4983230072969 + 3 ^ 40 * 30849 * 2
def baseEnd_30849 : Nat := 9386882791499281093709

theorem tailTrace_30849 : CollatzResearch.WordTrace tailWord_30849 prefixEnd_30849 9386882791499281093709 := by
  unfold tailWord_30849
  simp only [CollatzResearch.WordTrace]
  refine ⟨1125155465246816434855601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 750103643497877623237067 1125155465246816434855601)
  ·
    refine ⟨843866598935112326141701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1125155465246816434855601 843866598935112326141701)
    ·
      refine ⟨158224987300333561151569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 843866598935112326141701 158224987300333561151569)
      ·
        refine ⟨118668740475250170863677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158224987300333561151569 118668740475250170863677)
        ·
          refine ⟨44500777678218814073879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118668740475250170863677 44500777678218814073879)
          ·
            refine ⟨66751166517328221110819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44500777678218814073879 66751166517328221110819)
            ·
              refine ⟨100126749775992331666229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66751166517328221110819 100126749775992331666229)
              ·
                refine ⟨9386882791499281093709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 100126749775992331666229 9386882791499281093709)
                ·
                  rfl

theorem cell19_30849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 5].length) (baseStart_30849 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_30849 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_30849 prefixEnd_30849 := by exact prefixLift 30849
  have htrace : WordTrace (prefixWord ++ tailWord_30849) baseStart_30849 baseEnd_30849 := by
    simpa [prefixWord, tailWord_30849, baseEnd_30849] using wordTrace_append hprefix tailTrace_30849
  have hstable : (prefixWord ++ tailWord_30849).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30849).length < 2 ^ (prefixWord ++ tailWord_30849).sum := by decide
  have hdescent : baseEnd_30849 < baseStart_30849 := by decide
  rcases family_descends (prefixWord ++ tailWord_30849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30851 : List Nat := [1, 1, 1, 3, 3, 4, 1, 5]
def baseStart_30851 : Nat := 118140960795 + 30851 * 2 ^ 59
def prefixEnd_30851 : Nat := 4983230072969 + 3 ^ 40 * 30851 * 2
def baseEnd_30851 : Nat := 9387491361163869049259

theorem tailTrace_30851 : CollatzResearch.WordTrace tailWord_30851 prefixEnd_30851 9387491361163869049259 := by
  unfold tailWord_30851
  simp only [CollatzResearch.WordTrace]
  refine ⟨1125228411239570776428407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 750152274159713850952271 1125228411239570776428407)
  ·
    refine ⟨1687842616859356164642611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1125228411239570776428407 1687842616859356164642611)
    ·
      refine ⟨2531763925289034246963917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1687842616859356164642611 2531763925289034246963917)
      ·
        refine ⟨949411471983387842611469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2531763925289034246963917 949411471983387842611469)
        ·
          refine ⟨356029301993770440979301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 949411471983387842611469 356029301993770440979301)
          ·
            refine ⟨66755494123831957683619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 356029301993770440979301 66755494123831957683619)
            ·
              refine ⟨100133241185747936525429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66755494123831957683619 100133241185747936525429)
              ·
                refine ⟨9387491361163869049259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 100133241185747936525429 9387491361163869049259)
                ·
                  rfl

theorem cell19_30851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 5].length) (baseStart_30851 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_30851 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_30851 prefixEnd_30851 := by exact prefixLift 30851
  have htrace : WordTrace (prefixWord ++ tailWord_30851) baseStart_30851 baseEnd_30851 := by
    simpa [prefixWord, tailWord_30851, baseEnd_30851] using wordTrace_append hprefix tailTrace_30851
  have hstable : (prefixWord ++ tailWord_30851).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30851).length < 2 ^ (prefixWord ++ tailWord_30851).sum := by decide
  have hdescent : baseEnd_30851 < baseStart_30851 := by decide
  rcases family_descends (prefixWord ++ tailWord_30851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30940 : List Nat := [2, 2, 5, 2, 1, 2, 1, 4]
def baseStart_30940 : Nat := 118140960795 + 30940 * 2 ^ 59
def prefixEnd_30940 : Nat := 4983230072969 + 3 ^ 40 * 30940 * 2
def baseEnd_30940 : Nat := 9414572711238033071239

theorem tailTrace_30940 : CollatzResearch.WordTrace tailWord_30940 prefixEnd_30940 9414572711238033071239 := by
  unfold tailWord_30940
  simp only [CollatzResearch.WordTrace]
  refine ⟨564237253958569488209137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 752316338611425984278849 564237253958569488209137)
  ·
    refine ⟨423177940468927116156853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 564237253958569488209137 423177940468927116156853)
    ·
      refine ⟨39672931918961917139705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 423177940468927116156853 39672931918961917139705)
      ·
        refine ⟨29754698939221437854779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39672931918961917139705 29754698939221437854779)
        ·
          refine ⟨44632048408832156782169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29754698939221437854779 44632048408832156782169)
          ·
            refine ⟨33474036306624117586627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44632048408832156782169 33474036306624117586627)
            ·
              refine ⟨50211054459936176379941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33474036306624117586627 50211054459936176379941)
              ·
                refine ⟨9414572711238033071239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50211054459936176379941 9414572711238033071239)
                ·
                  rfl

theorem cell19_30940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 1, 4].length) (baseStart_30940 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_30940 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_30940 prefixEnd_30940 := by exact prefixLift 30940
  have htrace : WordTrace (prefixWord ++ tailWord_30940) baseStart_30940 baseEnd_30940 := by
    simpa [prefixWord, tailWord_30940, baseEnd_30940] using wordTrace_append hprefix tailTrace_30940
  have hstable : (prefixWord ++ tailWord_30940).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30940).length < 2 ^ (prefixWord ++ tailWord_30940).sum := by decide
  have hdescent : baseEnd_30940 < baseStart_30940 := by decide
  rcases family_descends (prefixWord ++ tailWord_30940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30984 : List Nat := [2, 1, 3, 2, 3, 2, 6]
def baseStart_30984 : Nat := 118140960795 + 30984 * 2 ^ 59
def prefixEnd_30984 : Nat := 4983230072969 + 3 ^ 40 * 30984 * 2
def baseEnd_30984 : Nat := 3142653747952989364447

theorem tailTrace_30984 : CollatzResearch.WordTrace tailWord_30984 prefixEnd_30984 3142653747952989364447 := by
  unfold tailWord_30984
  simp only [CollatzResearch.WordTrace]
  refine ⟨565039659878867245510003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 753386213171822994013337 565039659878867245510003)
  ·
    refine ⟨847559489818300868265005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 565039659878867245510003 847559489818300868265005)
    ·
      refine ⟨317834808681862825599377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 847559489818300868265005 317834808681862825599377)
      ·
        refine ⟨238376106511397119199533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 317834808681862825599377 238376106511397119199533)
        ·
          refine ⟨89391039941773919699825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 238376106511397119199533 89391039941773919699825)
          ·
            refine ⟨67043279956330439774869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89391039941773919699825 67043279956330439774869)
            ·
              refine ⟨3142653747952989364447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 67043279956330439774869 3142653747952989364447)
              ·
                rfl

theorem cell19_30984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 6].length) (baseStart_30984 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_30984 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_30984 prefixEnd_30984 := by exact prefixLift 30984
  have htrace : WordTrace (prefixWord ++ tailWord_30984) baseStart_30984 baseEnd_30984 := by
    simpa [prefixWord, tailWord_30984, baseEnd_30984] using wordTrace_append hprefix tailTrace_30984
  have hstable : (prefixWord ++ tailWord_30984).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30984).length < 2 ^ (prefixWord ++ tailWord_30984).sum := by decide
  have hdescent : baseEnd_30984 < baseStart_30984 := by decide
  rcases family_descends (prefixWord ++ tailWord_30984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31016 : List Nat := [2, 1, 5, 1, 4, 1, 2, 3]
def baseStart_31016 : Nat := 118140960795 + 31016 * 2 ^ 59
def prefixEnd_31016 : Nat := 4983230072969 + 3 ^ 40 * 31016 * 2
def baseEnd_31016 : Nat := 9437698358492375382143

theorem tailTrace_31016 : CollatzResearch.WordTrace tailWord_31016 prefixEnd_31016 9437698358492375382143 := by
  unfold tailWord_31016
  simp only [CollatzResearch.WordTrace]
  refine ⟨565623227820901978092451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 754164303761202637456601 565623227820901978092451)
  ·
    refine ⟨848434841731352967138677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 565623227820901978092451 848434841731352967138677)
    ·
      refine ⟨79540766412314340669251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 848434841731352967138677 79540766412314340669251)
      ·
        refine ⟨119311149618471511003877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79540766412314340669251 119311149618471511003877)
        ·
          refine ⟨22370840553463408313227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 119311149618471511003877 22370840553463408313227)
          ·
            refine ⟨33556260830195112469841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22370840553463408313227 33556260830195112469841)
            ·
              refine ⟨25167195622646334352381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33556260830195112469841 25167195622646334352381)
              ·
                refine ⟨9437698358492375382143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25167195622646334352381 9437698358492375382143)
                ·
                  rfl

theorem cell19_31016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 2, 3].length) (baseStart_31016 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_31016 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_31016 prefixEnd_31016 := by exact prefixLift 31016
  have htrace : WordTrace (prefixWord ++ tailWord_31016) baseStart_31016 baseEnd_31016 := by
    simpa [prefixWord, tailWord_31016, baseEnd_31016] using wordTrace_append hprefix tailTrace_31016
  have hstable : (prefixWord ++ tailWord_31016).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31016).length < 2 ^ (prefixWord ++ tailWord_31016).sum := by decide
  have hdescent : baseEnd_31016 < baseStart_31016 := by decide
  rcases family_descends (prefixWord ++ tailWord_31016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31043 : List Nat := [1, 1, 1, 3, 1, 3, 9]
def baseStart_31043 : Nat := 118140960795 + 31043 * 2 ^ 59
def prefixEnd_31043 : Nat := 4983230072969 + 3 ^ 40 * 31043 * 2
def baseEnd_31043 : Nat := 3148638016321437594023

theorem tailTrace_31043 : CollatzResearch.WordTrace tailWord_31043 prefixEnd_31043 3148638016321437594023 := by
  unfold tailWord_31043
  simp only [CollatzResearch.WordTrace]
  refine ⟨1132231226543987567417783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 754820817695991711611855 1132231226543987567417783)
  ·
    refine ⟨1698346839815981351126675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1132231226543987567417783 1698346839815981351126675)
    ·
      refine ⟨2547520259723972026690013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1698346839815981351126675 2547520259723972026690013)
      ·
        refine ⟨955320097396489510008755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2547520259723972026690013 955320097396489510008755)
        ·
          refine ⟨1432980146094734265013133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 955320097396489510008755 1432980146094734265013133)
          ·
            refine ⟨537367554785525349379925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1432980146094734265013133 537367554785525349379925)
            ·
              refine ⟨3148638016321437594023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 537367554785525349379925 3148638016321437594023)
              ·
                rfl

theorem cell19_31043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 9].length) (baseStart_31043 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_31043 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_31043 prefixEnd_31043 := by exact prefixLift 31043
  have htrace : WordTrace (prefixWord ++ tailWord_31043) baseStart_31043 baseEnd_31043 := by
    simpa [prefixWord, tailWord_31043, baseEnd_31043] using wordTrace_append hprefix tailTrace_31043
  have hstable : (prefixWord ++ tailWord_31043).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31043).length < 2 ^ (prefixWord ++ tailWord_31043).sum := by decide
  have hdescent : baseEnd_31043 < baseStart_31043 := by decide
  rcases family_descends (prefixWord ++ tailWord_31043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31060 : List Nat := [2, 4, 1, 1, 2, 2, 1, 6]
def baseStart_31060 : Nat := 118140960795 + 31060 * 2 ^ 59
def prefixEnd_31060 : Nat := 4983230072969 + 3 ^ 40 * 31060 * 2
def baseEnd_31060 : Nat := 9451086891113310404245

theorem tailTrace_31060 : CollatzResearch.WordTrace tailWord_31060 prefixEnd_31060 9451086891113310404245 := by
  unfold tailWord_31060
  simp only [CollatzResearch.WordTrace]
  refine ⟨566425633741199735393317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 755234178321599647191089 566425633741199735393317)
  ·
    refine ⟨106204806326474950386247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 566425633741199735393317 106204806326474950386247)
    ·
      refine ⟨159307209489712425579371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106204806326474950386247 159307209489712425579371)
      ·
        refine ⟨238960814234568638369057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159307209489712425579371 238960814234568638369057)
        ·
          refine ⟨179220610675926478776793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238960814234568638369057 179220610675926478776793)
          ·
            refine ⟨134415458006944859082595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179220610675926478776793 134415458006944859082595)
            ·
              refine ⟨201623187010417288623893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134415458006944859082595 201623187010417288623893)
              ·
                refine ⟨9451086891113310404245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 201623187010417288623893 9451086891113310404245)
                ·
                  rfl

theorem cell19_31060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 6].length) (baseStart_31060 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_31060 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_31060 prefixEnd_31060 := by exact prefixLift 31060
  have htrace : WordTrace (prefixWord ++ tailWord_31060) baseStart_31060 baseEnd_31060 := by
    simpa [prefixWord, tailWord_31060, baseEnd_31060] using wordTrace_append hprefix tailTrace_31060
  have hstable : (prefixWord ++ tailWord_31060).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31060).length < 2 ^ (prefixWord ++ tailWord_31060).sum := by decide
  have hdescent : baseEnd_31060 < baseStart_31060 := by decide
  rcases family_descends (prefixWord ++ tailWord_31060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31079 : List Nat := [1, 1, 5, 1, 3, 1, 2, 5]
def baseStart_31079 : Nat := 118140960795 + 31079 * 2 ^ 59
def prefixEnd_31079 : Nat := 4983230072969 + 3 ^ 40 * 31079 * 2
def baseEnd_31079 : Nat := 9456868302926895981971

theorem tailTrace_31079 : CollatzResearch.WordTrace tailWord_31079 prefixEnd_31079 9456868302926895981971 := by
  unfold tailWord_31079
  simp only [CollatzResearch.WordTrace]
  refine ⟨1133544254413565715728291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 755696169609043810485527 1133544254413565715728291)
  ·
    refine ⟨1700316381620348573592437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1133544254413565715728291 1700316381620348573592437)
    ·
      refine ⟨159404660776907678774291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1700316381620348573592437 159404660776907678774291)
      ·
        refine ⟨239106991165361518161437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159404660776907678774291 239106991165361518161437)
        ·
          refine ⟨89665121687010569310539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 239106991165361518161437 89665121687010569310539)
          ·
            refine ⟨134497682530515853965809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89665121687010569310539 134497682530515853965809)
            ·
              refine ⟨100873261897886890474357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134497682530515853965809 100873261897886890474357)
              ·
                refine ⟨9456868302926895981971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 100873261897886890474357 9456868302926895981971)
                ·
                  rfl

theorem cell19_31079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 5].length) (baseStart_31079 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_31079 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_31079 prefixEnd_31079 := by exact prefixLift 31079
  have htrace : WordTrace (prefixWord ++ tailWord_31079) baseStart_31079 baseEnd_31079 := by
    simpa [prefixWord, tailWord_31079, baseEnd_31079] using wordTrace_append hprefix tailTrace_31079
  have hstable : (prefixWord ++ tailWord_31079).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31079).length < 2 ^ (prefixWord ++ tailWord_31079).sum := by decide
  have hdescent : baseEnd_31079 < baseStart_31079 := by decide
  rcases family_descends (prefixWord ++ tailWord_31079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31081 : List Nat := [1, 2, 1, 1, 1, 3, 3, 7]
def baseStart_31081 : Nat := 118140960795 + 31081 * 2 ^ 59
def prefixEnd_31081 : Nat := 4983230072969 + 3 ^ 40 * 31081 * 2
def baseEnd_31081 : Nat := 9457476872591483937521

theorem tailTrace_31081 : CollatzResearch.WordTrace tailWord_31081 prefixEnd_31081 9457476872591483937521 := by
  unfold tailWord_31081
  simp only [CollatzResearch.WordTrace]
  refine ⟨1133617200406320057301097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 755744800270880038200731 1133617200406320057301097)
  ·
    refine ⟨850212900304740042975823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1133617200406320057301097 850212900304740042975823)
    ·
      refine ⟨1275319350457110064463735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 850212900304740042975823 1275319350457110064463735)
      ·
        refine ⟨1912979025685665096695603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1275319350457110064463735 1912979025685665096695603)
        ·
          refine ⟨2869468538528497645043405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1912979025685665096695603 2869468538528497645043405)
          ·
            refine ⟨1076050701948186616891277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2869468538528497645043405 1076050701948186616891277)
            ·
              refine ⟨403519013230569981334229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1076050701948186616891277 403519013230569981334229)
              ·
                refine ⟨9457476872591483937521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 403519013230569981334229 9457476872591483937521)
                ·
                  rfl

theorem cell19_31081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 7].length) (baseStart_31081 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_31081 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_31081 prefixEnd_31081 := by exact prefixLift 31081
  have htrace : WordTrace (prefixWord ++ tailWord_31081) baseStart_31081 baseEnd_31081 := by
    simpa [prefixWord, tailWord_31081, baseEnd_31081] using wordTrace_append hprefix tailTrace_31081
  have hstable : (prefixWord ++ tailWord_31081).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31081).length < 2 ^ (prefixWord ++ tailWord_31081).sum := by decide
  have hdescent : baseEnd_31081 < baseStart_31081 := by decide
  rcases family_descends (prefixWord ++ tailWord_31081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31094 : List Nat := [5, 1, 1, 4, 2, 6]
def baseStart_31094 : Nat := 118140960795 + 31094 * 2 ^ 59
def prefixEnd_31094 : Nat := 4983230072969 + 3 ^ 40 * 31094 * 2
def baseEnd_31094 : Nat := 1051270286156811738733

theorem tailTrace_31094 : CollatzResearch.WordTrace tailWord_31094 prefixEnd_31094 1051270286156811738733 := by
  unfold tailWord_31094
  simp only [CollatzResearch.WordTrace]
  refine ⟨70880709334951454845271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 756060899572815518349557 70880709334951454845271)
  ·
    refine ⟨106321064002427182267907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70880709334951454845271 106321064002427182267907)
    ·
      refine ⟨159481596003640773401861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106321064002427182267907 159481596003640773401861)
      ·
        refine ⟨29902799250682645012849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 159481596003640773401861 29902799250682645012849)
        ·
          refine ⟨22427099438011983759637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29902799250682645012849 22427099438011983759637)
          ·
            refine ⟨1051270286156811738733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 22427099438011983759637 1051270286156811738733)
            ·
              rfl

theorem cell19_31094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 6].length) (baseStart_31094 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_31094 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_31094 prefixEnd_31094 := by exact prefixLift 31094
  have htrace : WordTrace (prefixWord ++ tailWord_31094) baseStart_31094 baseEnd_31094 := by
    simpa [prefixWord, tailWord_31094, baseEnd_31094] using wordTrace_append hprefix tailTrace_31094
  have hstable : (prefixWord ++ tailWord_31094).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31094).length < 2 ^ (prefixWord ++ tailWord_31094).sum := by decide
  have hdescent : baseEnd_31094 < baseStart_31094 := by decide
  rcases family_descends (prefixWord ++ tailWord_31094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31286 : List Nat := [5, 1, 2, 1, 2, 1, 3, 4]
def baseStart_31286 : Nat := 118140960795 + 31286 * 2 ^ 59
def prefixEnd_31286 : Nat := 4983230072969 + 3 ^ 40 * 31286 * 2
def baseEnd_31286 : Nat := 9519855263211749381407

theorem tailTrace_31286 : CollatzResearch.WordTrace tailWord_31286 prefixEnd_31286 9519855263211749381407 := by
  unfold tailWord_31286
  simp only [CollatzResearch.WordTrace]
  refine ⟨71318385291477504282107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 760729443109093379009141 71318385291477504282107)
  ·
    refine ⟨106977577937216256423161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71318385291477504282107 106977577937216256423161)
    ·
      refine ⟨80233183452912192317371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106977577937216256423161 80233183452912192317371)
      ·
        refine ⟨120349775179368288476057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80233183452912192317371 120349775179368288476057)
        ·
          refine ⟨90262331384526216357043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120349775179368288476057 90262331384526216357043)
          ·
            refine ⟨135393497076789324535565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90262331384526216357043 135393497076789324535565)
            ·
              refine ⟨50772561403795996700837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135393497076789324535565 50772561403795996700837)
              ·
                refine ⟨9519855263211749381407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50772561403795996700837 9519855263211749381407)
                ·
                  rfl

theorem cell19_31286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_31286 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_31286 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_31286 prefixEnd_31286 := by exact prefixLift 31286
  have htrace : WordTrace (prefixWord ++ tailWord_31286) baseStart_31286 baseEnd_31286 := by
    simpa [prefixWord, tailWord_31286, baseEnd_31286] using wordTrace_append hprefix tailTrace_31286
  have hstable : (prefixWord ++ tailWord_31286).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31286).length < 2 ^ (prefixWord ++ tailWord_31286).sum := by decide
  have hdescent : baseEnd_31286 < baseStart_31286 := by decide
  rcases family_descends (prefixWord ++ tailWord_31286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31364 : List Nat := [2, 3, 2, 1, 3, 2, 1, 5]
def baseStart_31364 : Nat := 118140960795 + 31364 * 2 ^ 59
def prefixEnd_31364 : Nat := 4983230072969 + 3 ^ 40 * 31364 * 2
def baseEnd_31364 : Nat := 9543589480130679647861

theorem tailTrace_31364 : CollatzResearch.WordTrace tailWord_31364 prefixEnd_31364 9543589480130679647861 := by
  unfold tailWord_31364
  simp only [CollatzResearch.WordTrace]
  refine ⟨571969529190529694926573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 762626038920706259902097 571969529190529694926573)
  ·
    refine ⟨214488573446448635597465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 571969529190529694926573 214488573446448635597465)
    ·
      refine ⟨160866430084836476698099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214488573446448635597465 160866430084836476698099)
      ·
        refine ⟨241299645127254715047149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160866430084836476698099 241299645127254715047149)
        ·
          refine ⟨90487366922720518142681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 241299645127254715047149 90487366922720518142681)
          ·
            refine ⟨67865525192040388607011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90487366922720518142681 67865525192040388607011)
            ·
              refine ⟨101798287788060582910517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67865525192040388607011 101798287788060582910517)
              ·
                refine ⟨9543589480130679647861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 101798287788060582910517 9543589480130679647861)
                ·
                  rfl

theorem cell19_31364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 5].length) (baseStart_31364 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_31364 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_31364 prefixEnd_31364 := by exact prefixLift 31364
  have htrace : WordTrace (prefixWord ++ tailWord_31364) baseStart_31364 baseEnd_31364 := by
    simpa [prefixWord, tailWord_31364, baseEnd_31364] using wordTrace_append hprefix tailTrace_31364
  have hstable : (prefixWord ++ tailWord_31364).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31364).length < 2 ^ (prefixWord ++ tailWord_31364).sum := by decide
  have hdescent : baseEnd_31364 < baseStart_31364 := by decide
  rcases family_descends (prefixWord ++ tailWord_31364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31423 : List Nat := [1, 1, 2, 2, 2, 4, 2, 5]
def baseStart_31423 : Nat := 118140960795 + 31423 * 2 ^ 59
def prefixEnd_31423 : Nat := 4983230072969 + 3 ^ 40 * 31423 * 2
def baseEnd_31423 : Nat := 9561542285236024336589

theorem tailTrace_31423 : CollatzResearch.WordTrace tailWord_31423 prefixEnd_31423 9561542285236024336589 := by
  unfold tailWord_31423
  simp only [CollatzResearch.WordTrace]
  refine ⟨1146090965167312466250923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 764060643444874977500615 1146090965167312466250923)
  ·
    refine ⟨1719136447750968699376385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1146090965167312466250923 1719136447750968699376385)
    ·
      refine ⟨1289352335813226524532289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1719136447750968699376385 1289352335813226524532289)
      ·
        refine ⟨967014251859919893399217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1289352335813226524532289 967014251859919893399217)
        ·
          refine ⟨725260688894939920049413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 967014251859919893399217 725260688894939920049413)
          ·
            refine ⟨135986379167801235009265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 725260688894939920049413 135986379167801235009265)
            ·
              refine ⟨101989784375850926256949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135986379167801235009265 101989784375850926256949)
              ·
                refine ⟨9561542285236024336589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 101989784375850926256949 9561542285236024336589)
                ·
                  rfl

theorem cell19_31423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 5].length) (baseStart_31423 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_31423 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_31423 prefixEnd_31423 := by exact prefixLift 31423
  have htrace : WordTrace (prefixWord ++ tailWord_31423) baseStart_31423 baseEnd_31423 := by
    simpa [prefixWord, tailWord_31423, baseEnd_31423] using wordTrace_append hprefix tailTrace_31423
  have hstable : (prefixWord ++ tailWord_31423).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31423).length < 2 ^ (prefixWord ++ tailWord_31423).sum := by decide
  have hdescent : baseEnd_31423 < baseStart_31423 := by decide
  rcases family_descends (prefixWord ++ tailWord_31423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31442 : List Nat := [3, 2, 2, 2, 10]
def baseStart_31442 : Nat := 118140960795 + 31442 * 2 ^ 59
def prefixEnd_31442 : Nat := 4983230072969 + 3 ^ 40 * 31442 * 2
def baseEnd_31442 : Nat := 354345322112948515345

theorem tailTrace_31442 : CollatzResearch.WordTrace tailWord_31442 prefixEnd_31442 354345322112948515345 := by
  unfold tailWord_31442
  simp only [CollatzResearch.WordTrace]
  refine ⟨286695988024619677798145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 764522634732319140795053 286695988024619677798145)
  ·
    refine ⟨215021991018464758348609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286695988024619677798145 215021991018464758348609)
    ·
      refine ⟨161266493263848568761457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215021991018464758348609 161266493263848568761457)
      ·
        refine ⟨120949869947886426571093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161266493263848568761457 120949869947886426571093)
        ·
          refine ⟨354345322112948515345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 120949869947886426571093 354345322112948515345)
          ·
            rfl

theorem cell19_31442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 10].length) (baseStart_31442 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_31442 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_31442 prefixEnd_31442 := by exact prefixLift 31442
  have htrace : WordTrace (prefixWord ++ tailWord_31442) baseStart_31442 baseEnd_31442 := by
    simpa [prefixWord, tailWord_31442, baseEnd_31442] using wordTrace_append hprefix tailTrace_31442
  have hstable : (prefixWord ++ tailWord_31442).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31442).length < 2 ^ (prefixWord ++ tailWord_31442).sum := by decide
  have hdescent : baseEnd_31442 < baseStart_31442 := by decide
  rcases family_descends (prefixWord ++ tailWord_31442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31459 : List Nat := [1, 1, 1, 7, 1, 1, 3, 4]
def baseStart_31459 : Nat := 118140960795 + 31459 * 2 ^ 59
def prefixEnd_31459 : Nat := 4983230072969 + 3 ^ 40 * 31459 * 2
def baseEnd_31459 : Nat := 9572496539198607536491

theorem tailTrace_31459 : CollatzResearch.WordTrace tailWord_31459 prefixEnd_31459 9572496539198607536491 := by
  unfold tailWord_31459
  simp only [CollatzResearch.WordTrace]
  refine ⟨1147403993036890614561431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 764935995357927076374287 1147403993036890614561431)
  ·
    refine ⟨1721105989555335921842147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1147403993036890614561431 1721105989555335921842147)
    ·
      refine ⟨2581658984333003882763221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1721105989555335921842147 2581658984333003882763221)
      ·
        refine ⟨60507632445304778502263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 2581658984333003882763221 60507632445304778502263)
        ·
          refine ⟨90761448667957167753395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60507632445304778502263 90761448667957167753395)
          ·
            refine ⟨136142173001935751630093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90761448667957167753395 136142173001935751630093)
            ·
              refine ⟨51053314875725906861285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136142173001935751630093 51053314875725906861285)
              ·
                refine ⟨9572496539198607536491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51053314875725906861285 9572496539198607536491)
                ·
                  rfl

theorem cell19_31459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 3, 4].length) (baseStart_31459 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_31459 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_31459 prefixEnd_31459 := by exact prefixLift 31459
  have htrace : WordTrace (prefixWord ++ tailWord_31459) baseStart_31459 baseEnd_31459 := by
    simpa [prefixWord, tailWord_31459, baseEnd_31459] using wordTrace_append hprefix tailTrace_31459
  have hstable : (prefixWord ++ tailWord_31459).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31459).length < 2 ^ (prefixWord ++ tailWord_31459).sum := by decide
  have hdescent : baseEnd_31459 < baseStart_31459 := by decide
  rcases family_descends (prefixWord ++ tailWord_31459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31537 : List Nat := [1, 2, 2, 3, 2, 1, 3, 5]
def baseStart_31537 : Nat := 118140960795 + 31537 * 2 ^ 59
def prefixEnd_31537 : Nat := 4983230072969 + 3 ^ 40 * 31537 * 2
def baseEnd_31537 : Nat := 9596230756117537802945

theorem tailTrace_31537 : CollatzResearch.WordTrace tailWord_31537 prefixEnd_31537 9596230756117537802945 := by
  unfold tailWord_31537
  simp only [CollatzResearch.WordTrace]
  refine ⟨1150248886754309935900865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 766832591169539957267243 1150248886754309935900865)
  ·
    refine ⟨862686665065732451925649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1150248886754309935900865 862686665065732451925649)
    ·
      refine ⟨647014998799299338944237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 862686665065732451925649 647014998799299338944237)
      ·
        refine ⟨242630624549737252104089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 647014998799299338944237 242630624549737252104089)
        ·
          refine ⟨181972968412302939078067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242630624549737252104089 181972968412302939078067)
          ·
            refine ⟨272959452618454408617101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181972968412302939078067 272959452618454408617101)
            ·
              refine ⟨102359794731920403231413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 272959452618454408617101 102359794731920403231413)
              ·
                refine ⟨9596230756117537802945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 102359794731920403231413 9596230756117537802945)
                ·
                  rfl

theorem cell19_31537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 5].length) (baseStart_31537 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_31537 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_31537 prefixEnd_31537 := by exact prefixLift 31537
  have htrace : WordTrace (prefixWord ++ tailWord_31537) baseStart_31537 baseEnd_31537 := by
    simpa [prefixWord, tailWord_31537, baseEnd_31537] using wordTrace_append hprefix tailTrace_31537
  have hstable : (prefixWord ++ tailWord_31537).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31537).length < 2 ^ (prefixWord ++ tailWord_31537).sum := by decide
  have hdescent : baseEnd_31537 < baseStart_31537 := by decide
  rcases family_descends (prefixWord ++ tailWord_31537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31575 : List Nat := [1, 1, 3, 2, 4, 1, 1, 6]
def baseStart_31575 : Nat := 118140960795 + 31575 * 2 ^ 59
def prefixEnd_31575 : Nat := 4983230072969 + 3 ^ 40 * 31575 * 2
def baseEnd_31575 : Nat := 9607793579744708958397

theorem tailTrace_31575 : CollatzResearch.WordTrace tailWord_31575 prefixEnd_31575 9607793579744708958397 := by
  unfold tailWord_31575
  simp only [CollatzResearch.WordTrace]
  refine ⟨1151634860616642425784179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 767756573744428283856119 1151634860616642425784179)
  ·
    refine ⟨1727452290924963638676269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1151634860616642425784179 1727452290924963638676269)
    ·
      refine ⟨647794609096861364503601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1727452290924963638676269 647794609096861364503601)
      ·
        refine ⟨485845956822646023377701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 647794609096861364503601 485845956822646023377701)
        ·
          refine ⟨91096116904246129383319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 485845956822646023377701 91096116904246129383319)
          ·
            refine ⟨136644175356369194074979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91096116904246129383319 136644175356369194074979)
            ·
              refine ⟨204966263034553791112469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136644175356369194074979 204966263034553791112469)
              ·
                refine ⟨9607793579744708958397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 204966263034553791112469 9607793579744708958397)
                ·
                  rfl

theorem cell19_31575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 6].length) (baseStart_31575 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_31575 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_31575 prefixEnd_31575 := by exact prefixLift 31575
  have htrace : WordTrace (prefixWord ++ tailWord_31575) baseStart_31575 baseEnd_31575 := by
    simpa [prefixWord, tailWord_31575, baseEnd_31575] using wordTrace_append hprefix tailTrace_31575
  have hstable : (prefixWord ++ tailWord_31575).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31575).length < 2 ^ (prefixWord ++ tailWord_31575).sum := by decide
  have hdescent : baseEnd_31575 < baseStart_31575 := by decide
  rcases family_descends (prefixWord ++ tailWord_31575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31702 : List Nat := [5, 2, 1, 1, 2, 3, 2, 3]
def baseStart_31702 : Nat := 118140960795 + 31702 * 2 ^ 59
def prefixEnd_31702 : Nat := 4983230072969 + 3 ^ 40 * 31702 * 2
def baseEnd_31702 : Nat := 9646437753446044135829

theorem tailTrace_31702 : CollatzResearch.WordTrace tailWord_31702 prefixEnd_31702 9646437753446044135829 := by
  unfold tailWord_31702
  simp only [CollatzResearch.WordTrace]
  refine ⟨72266683197283944728585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 770844620771028743771573 72266683197283944728585)
  ·
    refine ⟨54200012397962958546439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72266683197283944728585 54200012397962958546439)
    ·
      refine ⟨81300018596944437819659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54200012397962958546439 81300018596944437819659)
      ·
        refine ⟨121950027895416656729489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81300018596944437819659 121950027895416656729489)
        ·
          refine ⟨91462520921562492547117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121950027895416656729489 91462520921562492547117)
          ·
            refine ⟨34298445345585934705169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91462520921562492547117 34298445345585934705169)
            ·
              refine ⟨25723834009189451028877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34298445345585934705169 25723834009189451028877)
              ·
                refine ⟨9646437753446044135829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25723834009189451028877 9646437753446044135829)
                ·
                  rfl

theorem cell19_31702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 2, 3].length) (baseStart_31702 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_31702 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_31702 prefixEnd_31702 := by exact prefixLift 31702
  have htrace : WordTrace (prefixWord ++ tailWord_31702) baseStart_31702 baseEnd_31702 := by
    simpa [prefixWord, tailWord_31702, baseEnd_31702] using wordTrace_append hprefix tailTrace_31702
  have hstable : (prefixWord ++ tailWord_31702).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31702).length < 2 ^ (prefixWord ++ tailWord_31702).sum := by decide
  have hdescent : baseEnd_31702 < baseStart_31702 := by decide
  rcases family_descends (prefixWord ++ tailWord_31702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31706 : List Nat := [3, 1, 1, 2, 4, 1, 4, 3]
def baseStart_31706 : Nat := 118140960795 + 31706 * 2 ^ 59
def prefixEnd_31706 : Nat := 4983230072969 + 3 ^ 40 * 31706 * 2
def baseEnd_31706 : Nat := 9647654892775220046929

theorem tailTrace_31706 : CollatzResearch.WordTrace tailWord_31706 prefixEnd_31706 9647654892775220046929 := by
  unfold tailWord_31706
  simp only [CollatzResearch.WordTrace]
  refine ⟨289103205785512949700743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 770941882094701199201981 289103205785512949700743)
  ·
    refine ⟨433654808678269424551115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289103205785512949700743 433654808678269424551115)
    ·
      refine ⟨650482213017404136826673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433654808678269424551115 650482213017404136826673)
      ·
        refine ⟨487861659763053102620005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 650482213017404136826673 487861659763053102620005)
        ·
          refine ⟨91474061205572456741251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 487861659763053102620005 91474061205572456741251)
          ·
            refine ⟨137211091808358685111877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91474061205572456741251 137211091808358685111877)
            ·
              refine ⟨25727079714067253458477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 137211091808358685111877 25727079714067253458477)
              ·
                refine ⟨9647654892775220046929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25727079714067253458477 9647654892775220046929)
                ·
                  rfl

theorem cell19_31706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 4, 3].length) (baseStart_31706 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_31706 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_31706 prefixEnd_31706 := by exact prefixLift 31706
  have htrace : WordTrace (prefixWord ++ tailWord_31706) baseStart_31706 baseEnd_31706 := by
    simpa [prefixWord, tailWord_31706, baseEnd_31706] using wordTrace_append hprefix tailTrace_31706
  have hstable : (prefixWord ++ tailWord_31706).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31706).length < 2 ^ (prefixWord ++ tailWord_31706).sum := by decide
  have hdescent : baseEnd_31706 < baseStart_31706 := by decide
  rcases family_descends (prefixWord ++ tailWord_31706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31727 : List Nat := [1, 1, 2, 1, 4, 5, 5]
def baseStart_31727 : Nat := 118140960795 + 31727 * 2 ^ 59
def prefixEnd_31727 : Nat := 4983230072969 + 3 ^ 40 * 31727 * 2
def baseEnd_31727 : Nat := 3218014958084464526735

theorem tailTrace_31727 : CollatzResearch.WordTrace tailWord_31727 prefixEnd_31727 3218014958084464526735 := by
  unfold tailWord_31727
  simp only [CollatzResearch.WordTrace]
  refine ⟨1157178756065972385317435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 771452504043981590211623 1157178756065972385317435)
  ·
    refine ⟨1735768134098958577976153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1157178756065972385317435 1735768134098958577976153)
    ·
      refine ⟨1301826100574218933482115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1735768134098958577976153 1301826100574218933482115)
      ·
        refine ⟨1952739150861328400223173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1301826100574218933482115 1952739150861328400223173)
        ·
          refine ⟨366138590786499075041845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1952739150861328400223173 366138590786499075041845)
          ·
            refine ⟨34325492886234288285173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 366138590786499075041845 34325492886234288285173)
            ·
              refine ⟨3218014958084464526735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34325492886234288285173 3218014958084464526735)
              ·
                rfl

theorem cell19_31727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 5].length) (baseStart_31727 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_31727 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_31727 prefixEnd_31727 := by exact prefixLift 31727
  have htrace : WordTrace (prefixWord ++ tailWord_31727) baseStart_31727 baseEnd_31727 := by
    simpa [prefixWord, tailWord_31727, baseEnd_31727] using wordTrace_append hprefix tailTrace_31727
  have hstable : (prefixWord ++ tailWord_31727).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31727).length < 2 ^ (prefixWord ++ tailWord_31727).sum := by decide
  have hdescent : baseEnd_31727 < baseStart_31727 := by decide
  rcases family_descends (prefixWord ++ tailWord_31727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31742 : List Nat := [4, 2, 2, 2, 2, 1, 2, 4]
def baseStart_31742 : Nat := 118140960795 + 31742 * 2 ^ 59
def prefixEnd_31742 : Nat := 4983230072969 + 3 ^ 40 * 31742 * 2
def baseEnd_31742 : Nat := 9658609146737803246831

theorem tailTrace_31742 : CollatzResearch.WordTrace tailWord_31742 prefixEnd_31742 9658609146737803246831 := by
  unfold tailWord_31742
  simp only [CollatzResearch.WordTrace]
  refine ⟨144715731376453743389185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 771817234007753298075653 144715731376453743389185)
  ·
    refine ⟨108536798532340307541889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144715731376453743389185 108536798532340307541889)
    ·
      refine ⟨81402598899255230656417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108536798532340307541889 81402598899255230656417)
      ·
        refine ⟨61051949174441422992313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81402598899255230656417 61051949174441422992313)
        ·
          refine ⟨45788961880831067244235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61051949174441422992313 45788961880831067244235)
          ·
            refine ⟨68683442821246600866353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45788961880831067244235 68683442821246600866353)
            ·
              refine ⟨51512582115934950649765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68683442821246600866353 51512582115934950649765)
              ·
                refine ⟨9658609146737803246831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51512582115934950649765 9658609146737803246831)
                ·
                  rfl

theorem cell19_31742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 2, 4].length) (baseStart_31742 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_31742 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_31742 prefixEnd_31742 := by exact prefixLift 31742
  have htrace : WordTrace (prefixWord ++ tailWord_31742) baseStart_31742 baseEnd_31742 := by
    simpa [prefixWord, tailWord_31742, baseEnd_31742] using wordTrace_append hprefix tailTrace_31742
  have hstable : (prefixWord ++ tailWord_31742).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31742).length < 2 ^ (prefixWord ++ tailWord_31742).sum := by decide
  have hdescent : baseEnd_31742 < baseStart_31742 := by decide
  rcases family_descends (prefixWord ++ tailWord_31742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31765 : List Nat := [1, 3, 2, 1, 4, 1, 2, 5]
def baseStart_31765 : Nat := 118140960795 + 31765 * 2 ^ 59
def prefixEnd_31765 : Nat := 4983230072969 + 3 ^ 40 * 31765 * 2
def baseEnd_31765 : Nat := 9665607697880564735657

theorem tailTrace_31765 : CollatzResearch.WordTrace tailWord_31765 prefixEnd_31765 9665607697880564735657 := by
  unfold tailWord_31765
  simp only [CollatzResearch.WordTrace]
  refine ⟨1158564729928304875200749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 772376486618869916800499 1158564729928304875200749)
  ·
    refine ⟨434461773723114328200281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1158564729928304875200749 434461773723114328200281)
    ·
      refine ⟨325846330292335746150211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 434461773723114328200281 325846330292335746150211)
      ·
        refine ⟨488769495438503619225317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325846330292335746150211 488769495438503619225317)
        ·
          refine ⟨91644280394719428604747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 488769495438503619225317 91644280394719428604747)
          ·
            refine ⟨137466420592079142907121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91644280394719428604747 137466420592079142907121)
            ·
              refine ⟨103099815444059357180341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137466420592079142907121 103099815444059357180341)
              ·
                refine ⟨9665607697880564735657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 103099815444059357180341 9665607697880564735657)
                ·
                  rfl

theorem cell19_31765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 5].length) (baseStart_31765 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_31765 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_31765 prefixEnd_31765 := by exact prefixLift 31765
  have htrace : WordTrace (prefixWord ++ tailWord_31765) baseStart_31765 baseEnd_31765 := by
    simpa [prefixWord, tailWord_31765, baseEnd_31765] using wordTrace_append hprefix tailTrace_31765
  have hstable : (prefixWord ++ tailWord_31765).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31765).length < 2 ^ (prefixWord ++ tailWord_31765).sum := by decide
  have hdescent : baseEnd_31765 < baseStart_31765 := by decide
  rcases family_descends (prefixWord ++ tailWord_31765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31801 : List Nat := [1, 2, 1, 5, 2, 3, 1, 4]
def baseStart_31801 : Nat := 118140960795 + 31801 * 2 ^ 59
def prefixEnd_31801 : Nat := 4983230072969 + 3 ^ 40 * 31801 * 2
def baseEnd_31801 : Nat := 9676561951843147935559

theorem tailTrace_31801 : CollatzResearch.WordTrace tailWord_31801 prefixEnd_31801 9676561951843147935559 := by
  unfold tailWord_31801
  simp only [CollatzResearch.WordTrace]
  refine ⟨1159877757797883023511257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 773251838531922015674171 1159877757797883023511257)
  ·
    refine ⟨869908318348412267633443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1159877757797883023511257 869908318348412267633443)
    ·
      refine ⟨1304862477522618401450165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 869908318348412267633443 1304862477522618401450165)
      ·
        refine ⟨122330857267745475135953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1304862477522618401450165 122330857267745475135953)
        ·
          refine ⟨91748142950809106351965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122330857267745475135953 91748142950809106351965)
          ·
            refine ⟨34405553606553414881987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91748142950809106351965 34405553606553414881987)
            ·
              refine ⟨51608330409830122322981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34405553606553414881987 51608330409830122322981)
              ·
                refine ⟨9676561951843147935559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51608330409830122322981 9676561951843147935559)
                ·
                  rfl

theorem cell19_31801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 1, 4].length) (baseStart_31801 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_31801 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_31801 prefixEnd_31801 := by exact prefixLift 31801
  have htrace : WordTrace (prefixWord ++ tailWord_31801) baseStart_31801 baseEnd_31801 := by
    simpa [prefixWord, tailWord_31801, baseEnd_31801] using wordTrace_append hprefix tailTrace_31801
  have hstable : (prefixWord ++ tailWord_31801).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31801).length < 2 ^ (prefixWord ++ tailWord_31801).sum := by decide
  have hdescent : baseEnd_31801 < baseStart_31801 := by decide
  rcases family_descends (prefixWord ++ tailWord_31801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31824 : List Nat := [2, 1, 1, 1, 1, 3, 1, 9]
def baseStart_31824 : Nat := 118140960795 + 31824 * 2 ^ 59
def prefixEnd_31824 : Nat := 4983230072969 + 3 ^ 40 * 31824 * 2
def baseEnd_31824 : Nat := 9683560502985909424385

theorem tailTrace_31824 : CollatzResearch.WordTrace tailWord_31824 prefixEnd_31824 9683560502985909424385 := by
  unfold tailWord_31824
  simp only [CollatzResearch.WordTrace]
  refine ⟨580358318357278975799263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 773811091143038634399017 580358318357278975799263)
  ·
    refine ⟨870537477535918463698895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 580358318357278975799263 870537477535918463698895)
    ·
      refine ⟨1305806216303877695548343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 870537477535918463698895 1305806216303877695548343)
      ·
        refine ⟨1958709324455816543322515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1305806216303877695548343 1958709324455816543322515)
        ·
          refine ⟨2938063986683724814983773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1958709324455816543322515 2938063986683724814983773)
          ·
            refine ⟨1101773995006396805618915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2938063986683724814983773 1101773995006396805618915)
            ·
              refine ⟨1652660992509595208428373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1101773995006396805618915 1652660992509595208428373)
              ·
                refine ⟨9683560502985909424385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1652660992509595208428373 9683560502985909424385)
                ·
                  rfl

theorem cell19_31824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 9].length) (baseStart_31824 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_31824 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_31824 prefixEnd_31824 := by exact prefixLift 31824
  have htrace : WordTrace (prefixWord ++ tailWord_31824) baseStart_31824 baseEnd_31824 := by
    simpa [prefixWord, tailWord_31824, baseEnd_31824] using wordTrace_append hprefix tailTrace_31824
  have hstable : (prefixWord ++ tailWord_31824).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31824).length < 2 ^ (prefixWord ++ tailWord_31824).sum := by decide
  have hdescent : baseEnd_31824 < baseStart_31824 := by decide
  rcases family_descends (prefixWord ++ tailWord_31824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31898 : List Nat := [3, 1, 1, 5, 1, 1, 7]
def baseStart_31898 : Nat := 118140960795 + 31898 * 2 ^ 59
def prefixEnd_31898 : Nat := 4983230072969 + 3 ^ 40 * 31898 * 2
def baseEnd_31898 : Nat := 3235359193525221259913

theorem tailTrace_31898 : CollatzResearch.WordTrace tailWord_31898 prefixEnd_31898 3235359193525221259913 := by
  unfold tailWord_31898
  simp only [CollatzResearch.WordTrace]
  refine ⟨290853909611617147448087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 775610425630979059861565 290853909611617147448087)
  ·
    refine ⟨436280864417425721172131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290853909611617147448087 436280864417425721172131)
    ·
      refine ⟨654421296626138581758197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 436280864417425721172131 654421296626138581758197)
      ·
        refine ⟨61351996558700492039831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 654421296626138581758197 61351996558700492039831)
        ·
          refine ⟨92027994838050738059747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61351996558700492039831 92027994838050738059747)
          ·
            refine ⟨138041992257076107089621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92027994838050738059747 138041992257076107089621)
            ·
              refine ⟨3235359193525221259913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 138041992257076107089621 3235359193525221259913)
              ·
                rfl

theorem cell19_31898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 7].length) (baseStart_31898 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_31898 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_31898 prefixEnd_31898 := by exact prefixLift 31898
  have htrace : WordTrace (prefixWord ++ tailWord_31898) baseStart_31898 baseEnd_31898 := by
    simpa [prefixWord, tailWord_31898, baseEnd_31898] using wordTrace_append hprefix tailTrace_31898
  have hstable : (prefixWord ++ tailWord_31898).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31898).length < 2 ^ (prefixWord ++ tailWord_31898).sum := by decide
  have hdescent : baseEnd_31898 < baseStart_31898 := by decide
  rcases family_descends (prefixWord ++ tailWord_31898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31919 : List Nat := [1, 1, 2, 1, 2, 3, 3, 6]
def baseStart_31919 : Nat := 118140960795 + 31919 * 2 ^ 59
def prefixEnd_31919 : Nat := 4983230072969 + 3 ^ 40 * 31919 * 2
def baseEnd_31919 : Nat := 9712467562053837313015

theorem tailTrace_31919 : CollatzResearch.WordTrace tailWord_31919 prefixEnd_31919 9712467562053837313015 := by
  unfold tailWord_31919
  simp only [CollatzResearch.WordTrace]
  refine ⟨1164181571370389176306811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 776121047580259450871207 1164181571370389176306811)
  ·
    refine ⟨1746272357055583764460217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1164181571370389176306811 1746272357055583764460217)
    ·
      refine ⟨1309704267791687823345163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1746272357055583764460217 1309704267791687823345163)
      ·
        refine ⟨1964556401687531735017745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1309704267791687823345163 1964556401687531735017745)
        ·
          refine ⟨1473417301265648801263309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1964556401687531735017745 1473417301265648801263309)
          ·
            refine ⟨552531487974618300473741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1473417301265648801263309 552531487974618300473741)
            ·
              refine ⟨207199307990481862677653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 552531487974618300473741 207199307990481862677653)
              ·
                refine ⟨9712467562053837313015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 207199307990481862677653 9712467562053837313015)
                ·
                  rfl

theorem cell19_31919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 6].length) (baseStart_31919 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_31919 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_31919 prefixEnd_31919 := by exact prefixLift 31919
  have htrace : WordTrace (prefixWord ++ tailWord_31919) baseStart_31919 baseEnd_31919 := by
    simpa [prefixWord, tailWord_31919, baseEnd_31919] using wordTrace_append hprefix tailTrace_31919
  have hstable : (prefixWord ++ tailWord_31919).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31919).length < 2 ^ (prefixWord ++ tailWord_31919).sum := by decide
  have hdescent : baseEnd_31919 < baseStart_31919 := by decide
  rcases family_descends (prefixWord ++ tailWord_31919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31993 : List Nat := [1, 2, 1, 3, 1, 1, 7, 3]
def baseStart_31993 : Nat := 118140960795 + 31993 * 2 ^ 59
def prefixEnd_31993 : Nat := 4983230072969 + 3 ^ 40 * 31993 * 2
def baseEnd_31993 : Nat := 9734984639643591668369

theorem tailTrace_31993 : CollatzResearch.WordTrace tailWord_31993 prefixEnd_31993 9734984639643591668369 := by
  unfold tailWord_31993
  simp only [CollatzResearch.WordTrace]
  refine ⟨1166880573102299814500633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 777920382068199876333755 1166880573102299814500633)
  ·
    refine ⟨875160429826724860875475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1166880573102299814500633 875160429826724860875475)
    ·
      refine ⟨1312740644740087291313213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 875160429826724860875475 1312740644740087291313213)
      ·
        refine ⟨492277741777532734242455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1312740644740087291313213 492277741777532734242455)
        ·
          refine ⟨738416612666299101363683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 492277741777532734242455 738416612666299101363683)
          ·
            refine ⟨1107624918999448652045525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 738416612666299101363683 1107624918999448652045525)
            ·
              refine ⟨25959959039049577782317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1107624918999448652045525 25959959039049577782317)
              ·
                refine ⟨9734984639643591668369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25959959039049577782317 9734984639643591668369)
                ·
                  rfl

theorem cell19_31993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 7, 3].length) (baseStart_31993 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_31993 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_31993 prefixEnd_31993 := by exact prefixLift 31993
  have htrace : WordTrace (prefixWord ++ tailWord_31993) baseStart_31993 baseEnd_31993 := by
    simpa [prefixWord, tailWord_31993, baseEnd_31993] using wordTrace_append hprefix tailTrace_31993
  have hstable : (prefixWord ++ tailWord_31993).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31993).length < 2 ^ (prefixWord ++ tailWord_31993).sum := by decide
  have hdescent : baseEnd_31993 < baseStart_31993 := by decide
  rcases family_descends (prefixWord ++ tailWord_31993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32033 : List Nat := [1, 2, 3, 2, 1, 1, 1, 8]
def baseStart_32033 : Nat := 118140960795 + 32033 * 2 ^ 59
def prefixEnd_32033 : Nat := 4983230072969 + 3 ^ 40 * 32033 * 2
def baseEnd_32033 : Nat := 9747156032935350779371

theorem tailTrace_32033 : CollatzResearch.WordTrace tailWord_32033 prefixEnd_32033 9747156032935350779371 := by
  unfold tailWord_32033
  simp only [CollatzResearch.WordTrace]
  refine ⟨1168339492957386645956753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 778892995304924430637835 1168339492957386645956753)
  ·
    refine ⟨876254619718039984467565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1168339492957386645956753 876254619718039984467565)
    ·
      refine ⟨328595482394264994175337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 876254619718039984467565 328595482394264994175337)
      ·
        refine ⟨246446611795698745631503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 328595482394264994175337 246446611795698745631503)
        ·
          refine ⟨369669917693548118447255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246446611795698745631503 369669917693548118447255)
          ·
            refine ⟨554504876540322177670883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 369669917693548118447255 554504876540322177670883)
            ·
              refine ⟨831757314810483266506325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 554504876540322177670883 831757314810483266506325)
              ·
                refine ⟨9747156032935350779371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 831757314810483266506325 9747156032935350779371)
                ·
                  rfl

theorem cell19_32033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 8].length) (baseStart_32033 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_32033 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_32033 prefixEnd_32033 := by exact prefixLift 32033
  have htrace : WordTrace (prefixWord ++ tailWord_32033) baseStart_32033 baseEnd_32033 := by
    simpa [prefixWord, tailWord_32033, baseEnd_32033] using wordTrace_append hprefix tailTrace_32033
  have hstable : (prefixWord ++ tailWord_32033).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32033).length < 2 ^ (prefixWord ++ tailWord_32033).sum := by decide
  have hdescent : baseEnd_32033 < baseStart_32033 := by decide
  rcases family_descends (prefixWord ++ tailWord_32033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32050 : List Nat := [3, 2, 1, 1, 4, 2, 1, 5]
def baseStart_32050 : Nat := 118140960795 + 32050 * 2 ^ 59
def prefixEnd_32050 : Nat := 4983230072969 + 3 ^ 40 * 32050 * 2
def baseEnd_32050 : Nat := 9752328875084348401547

theorem tailTrace_32050 : CollatzResearch.WordTrace tailWord_32050 prefixEnd_32050 9752328875084348401547 := by
  unfold tailWord_32050
  simp only [CollatzResearch.WordTrace]
  refine ⟨292239883473949637331401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 779306355930532366217069 292239883473949637331401)
  ·
    refine ⟨219179912605462227998551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292239883473949637331401 219179912605462227998551)
    ·
      refine ⟨328769868908193341997827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219179912605462227998551 328769868908193341997827)
      ·
        refine ⟨493154803362290012996741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328769868908193341997827 493154803362290012996741)
        ·
          refine ⟨92466525630429377436889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 493154803362290012996741 92466525630429377436889)
          ·
            refine ⟨69349894222822033077667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92466525630429377436889 69349894222822033077667)
            ·
              refine ⟨104024841334233049616501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69349894222822033077667 104024841334233049616501)
              ·
                refine ⟨9752328875084348401547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 104024841334233049616501 9752328875084348401547)
                ·
                  rfl

theorem cell19_32050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 5].length) (baseStart_32050 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_32050 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_32050 prefixEnd_32050 := by exact prefixLift 32050
  have htrace : WordTrace (prefixWord ++ tailWord_32050) baseStart_32050 baseEnd_32050 := by
    simpa [prefixWord, tailWord_32050, baseEnd_32050] using wordTrace_append hprefix tailTrace_32050
  have hstable : (prefixWord ++ tailWord_32050).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32050).length < 2 ^ (prefixWord ++ tailWord_32050).sum := by decide
  have hdescent : baseEnd_32050 < baseStart_32050 := by decide
  rcases family_descends (prefixWord ++ tailWord_32050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32071 : List Nat := [1, 1, 4, 1, 2, 3, 7]
def baseStart_32071 : Nat := 118140960795 + 32071 * 2 ^ 59
def prefixEnd_32071 : Nat := 4983230072969 + 3 ^ 40 * 32071 * 2
def baseEnd_32071 : Nat := 3252906285520840644941

theorem tailTrace_32071 : CollatzResearch.WordTrace tailWord_32071 prefixEnd_32071 3252906285520840644941 := by
  unfold tailWord_32071
  simp only [CollatzResearch.WordTrace]
  refine ⟨1169725466819719135840067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 779816977879812757226711 1169725466819719135840067)
  ·
    refine ⟨1754588200229578703760101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1169725466819719135840067 1754588200229578703760101)
    ·
      refine ⟨328985287543046006955019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1754588200229578703760101 328985287543046006955019)
      ·
        refine ⟨493477931314569010432529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328985287543046006955019 493477931314569010432529)
        ·
          refine ⟨370108448485926757824397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 493477931314569010432529 370108448485926757824397)
          ·
            refine ⟨138790668182222534184149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 370108448485926757824397 138790668182222534184149)
            ·
              refine ⟨3252906285520840644941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 138790668182222534184149 3252906285520840644941)
              ·
                rfl

theorem cell19_32071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 7].length) (baseStart_32071 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_32071 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_32071 prefixEnd_32071 := by exact prefixLift 32071
  have htrace : WordTrace (prefixWord ++ tailWord_32071) baseStart_32071 baseEnd_32071 := by
    simpa [prefixWord, tailWord_32071, baseEnd_32071] using wordTrace_append hprefix tailTrace_32071
  have hstable : (prefixWord ++ tailWord_32071).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32071).length < 2 ^ (prefixWord ++ tailWord_32071).sum := by decide
  have hdescent : baseEnd_32071 < baseStart_32071 := by decide
  rcases family_descends (prefixWord ++ tailWord_32071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32090 : List Nat := [3, 1, 1, 2, 1, 2, 3, 6]
def baseStart_32090 : Nat := 118140960795 + 32090 * 2 ^ 59
def prefixEnd_32090 : Nat := 4983230072969 + 3 ^ 40 * 32090 * 2
def baseEnd_32090 : Nat := 9764500268376107512549

theorem tailTrace_32090 : CollatzResearch.WordTrace tailWord_32090 prefixEnd_32090 9764500268376107512549 := by
  unfold tailWord_32090
  simp only [CollatzResearch.WordTrace]
  refine ⟨292604613437721345195431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 780278969167256920521149 292604613437721345195431)
  ·
    refine ⟨438906920156582017793147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292604613437721345195431 438906920156582017793147)
    ·
      refine ⟨658360380234873026689721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 438906920156582017793147 658360380234873026689721)
      ·
        refine ⟨493770285176154770017291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 658360380234873026689721 493770285176154770017291)
        ·
          refine ⟨740655427764232155025937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 493770285176154770017291 740655427764232155025937)
          ·
            refine ⟨555491570823174116269453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 740655427764232155025937 555491570823174116269453)
            ·
              refine ⟨208309339058690293601045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 555491570823174116269453 208309339058690293601045)
              ·
                refine ⟨9764500268376107512549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 208309339058690293601045 9764500268376107512549)
                ·
                  rfl

theorem cell19_32090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 6].length) (baseStart_32090 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_32090 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_32090 prefixEnd_32090 := by exact prefixLift 32090
  have htrace : WordTrace (prefixWord ++ tailWord_32090) baseStart_32090 baseEnd_32090 := by
    simpa [prefixWord, tailWord_32090, baseEnd_32090] using wordTrace_append hprefix tailTrace_32090
  have hstable : (prefixWord ++ tailWord_32090).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32090).length < 2 ^ (prefixWord ++ tailWord_32090).sum := by decide
  have hdescent : baseEnd_32090 < baseStart_32090 := by decide
  rcases family_descends (prefixWord ++ tailWord_32090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32162 : List Nat := [3, 3, 1, 2, 1, 3, 3, 3]
def baseStart_32162 : Nat := 118140960795 + 32162 * 2 ^ 59
def prefixEnd_32162 : Nat := 4983230072969 + 3 ^ 40 * 32162 * 2
def baseEnd_32162 : Nat := 9786408776301273912353

theorem tailTrace_32162 : CollatzResearch.WordTrace tailWord_32162 prefixEnd_32162 9786408776301273912353 := by
  unfold tailWord_32162
  simp only [CollatzResearch.WordTrace]
  refine ⟨293261127372510419350685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 782029672993361118268493 293261127372510419350685)
  ·
    refine ⟨109972922764691407256507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 293261127372510419350685 109972922764691407256507)
    ·
      refine ⟨164959384147037110884761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109972922764691407256507 164959384147037110884761)
      ·
        refine ⟨123719538110277833163571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164959384147037110884761 123719538110277833163571)
        ·
          refine ⟨185579307165416749745357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123719538110277833163571 185579307165416749745357)
          ·
            refine ⟨69592240187031281154509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 185579307165416749745357 69592240187031281154509)
            ·
              refine ⟨26097090070136730432941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69592240187031281154509 26097090070136730432941)
              ·
                refine ⟨9786408776301273912353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26097090070136730432941 9786408776301273912353)
                ·
                  rfl

theorem cell19_32162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 3, 3].length) (baseStart_32162 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_32162 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_32162 prefixEnd_32162 := by exact prefixLift 32162
  have htrace : WordTrace (prefixWord ++ tailWord_32162) baseStart_32162 baseEnd_32162 := by
    simpa [prefixWord, tailWord_32162, baseEnd_32162] using wordTrace_append hprefix tailTrace_32162
  have hstable : (prefixWord ++ tailWord_32162).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32162).length < 2 ^ (prefixWord ++ tailWord_32162).sum := by decide
  have hdescent : baseEnd_32162 < baseStart_32162 := by decide
  rcases family_descends (prefixWord ++ tailWord_32162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32221 : List Nat := [1, 4, 3, 1, 1, 3, 1, 5]
def baseStart_32221 : Nat := 118140960795 + 32221 * 2 ^ 59
def prefixEnd_32221 : Nat := 4983230072969 + 3 ^ 40 * 32221 * 2
def baseEnd_32221 : Nat := 9804361581406618601081

theorem tailTrace_32221 : CollatzResearch.WordTrace tailWord_32221 prefixEnd_32221 9804361581406618601081 := by
  unfold tailWord_32221
  simp only [CollatzResearch.WordTrace]
  refine ⟨1175196416276294753800517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 783464277517529835867011 1175196416276294753800517)
  ·
    refine ⟨220349328051805266337597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1175196416276294753800517 220349328051805266337597)
    ·
      refine ⟨82630998019426974876599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220349328051805266337597 82630998019426974876599)
      ·
        refine ⟨123946497029140462314899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82630998019426974876599 123946497029140462314899)
        ·
          refine ⟨185919745543710693472349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123946497029140462314899 185919745543710693472349)
          ·
            refine ⟨69719904578891510052131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 185919745543710693472349 69719904578891510052131)
            ·
              refine ⟨104579856868337265078197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69719904578891510052131 104579856868337265078197)
              ·
                refine ⟨9804361581406618601081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 104579856868337265078197 9804361581406618601081)
                ·
                  rfl

theorem cell19_32221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 5].length) (baseStart_32221 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_32221 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_32221 prefixEnd_32221 := by exact prefixLift 32221
  have htrace : WordTrace (prefixWord ++ tailWord_32221) baseStart_32221 baseEnd_32221 := by
    simpa [prefixWord, tailWord_32221, baseEnd_32221] using wordTrace_append hprefix tailTrace_32221
  have hstable : (prefixWord ++ tailWord_32221).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32221).length < 2 ^ (prefixWord ++ tailWord_32221).sum := by decide
  have hdescent : baseEnd_32221 < baseStart_32221 := by decide
  rcases family_descends (prefixWord ++ tailWord_32221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32223 : List Nat := [1, 1, 2, 3, 3, 1, 3, 5]
def baseStart_32223 : Nat := 118140960795 + 32223 * 2 ^ 59
def prefixEnd_32223 : Nat := 4983230072969 + 3 ^ 40 * 32223 * 2
def baseEnd_32223 : Nat := 9804970151071206556631

theorem tailTrace_32223 : CollatzResearch.WordTrace tailWord_32223 prefixEnd_32223 9804970151071206556631 := by
  unfold tailWord_32223
  simp only [CollatzResearch.WordTrace]
  refine ⟨1175269362269049095373323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 783512908179366063582215 1175269362269049095373323)
  ·
    refine ⟨1762904043403573643059985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1175269362269049095373323 1762904043403573643059985)
    ·
      refine ⟨1322178032552680232294989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1762904043403573643059985 1322178032552680232294989)
      ·
        refine ⟨495816762207255087110621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1322178032552680232294989 495816762207255087110621)
        ·
          refine ⟨185931285827720657666483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 495816762207255087110621 185931285827720657666483)
          ·
            refine ⟨278896928741580986499725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185931285827720657666483 278896928741580986499725)
            ·
              refine ⟨104586348278092869937397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 278896928741580986499725 104586348278092869937397)
              ·
                refine ⟨9804970151071206556631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 104586348278092869937397 9804970151071206556631)
                ·
                  rfl

theorem cell19_32223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 5].length) (baseStart_32223 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_32223 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_32223 prefixEnd_32223 := by exact prefixLift 32223
  have htrace : WordTrace (prefixWord ++ tailWord_32223) baseStart_32223 baseEnd_32223 := by
    simpa [prefixWord, tailWord_32223, baseEnd_32223] using wordTrace_append hprefix tailTrace_32223
  have hstable : (prefixWord ++ tailWord_32223).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32223).length < 2 ^ (prefixWord ++ tailWord_32223).sum := by decide
  have hdescent : baseEnd_32223 < baseStart_32223 := by decide
  rcases family_descends (prefixWord ++ tailWord_32223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32356 : List Nat := [2, 3, 1, 1, 2, 4, 6]
def baseStart_32356 : Nat := 118140960795 + 32356 * 2 ^ 59
def prefixEnd_32356 : Nat := 4983230072969 + 3 ^ 40 * 32356 * 2
def baseEnd_32356 : Nat := 3281813344588768533571

theorem tailTrace_32356 : CollatzResearch.WordTrace tailWord_32356 prefixEnd_32356 3281813344588768533571 := by
  unfold tailWord_32356
  simp only [CollatzResearch.WordTrace]
  refine ⟨590060135393606404982461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 786746847191475206643281 590060135393606404982461)
  ·
    refine ⟨221272550772602401868423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 590060135393606404982461 221272550772602401868423)
    ·
      refine ⟨331908826158903602802635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221272550772602401868423 331908826158903602802635)
      ·
        refine ⟨497863239238355404203953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331908826158903602802635 497863239238355404203953)
        ·
          refine ⟨373397429428766553152965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 497863239238355404203953 373397429428766553152965)
          ·
            refine ⟨70012018017893728716181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 373397429428766553152965 70012018017893728716181)
            ·
              refine ⟨3281813344588768533571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 70012018017893728716181 3281813344588768533571)
              ·
                rfl

theorem cell19_32356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 6].length) (baseStart_32356 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_32356 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_32356 prefixEnd_32356 := by exact prefixLift 32356
  have htrace : WordTrace (prefixWord ++ tailWord_32356) baseStart_32356 baseEnd_32356 := by
    simpa [prefixWord, tailWord_32356, baseEnd_32356] using wordTrace_append hprefix tailTrace_32356
  have hstable : (prefixWord ++ tailWord_32356).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32356).length < 2 ^ (prefixWord ++ tailWord_32356).sum := by decide
  have hdescent : baseEnd_32356 < baseStart_32356 := by decide
  rcases family_descends (prefixWord ++ tailWord_32356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32388 : List Nat := [2, 3, 2, 1, 5, 1, 2, 3]
def baseStart_32388 : Nat := 118140960795 + 32388 * 2 ^ 59
def prefixEnd_32388 : Nat := 4983230072969 + 3 ^ 40 * 32388 * 2
def baseEnd_32388 : Nat := 9855177148399712889515

theorem tailTrace_32388 : CollatzResearch.WordTrace tailWord_32388 prefixEnd_32388 9855177148399712889515 := by
  unfold tailWord_32388
  simp only [CollatzResearch.WordTrace]
  refine ⟨590643703335641137564909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 787524937780854850086545 590643703335641137564909)
  ·
    refine ⟨221491388750865426586841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 590643703335641137564909 221491388750865426586841)
    ·
      refine ⟨166118541563149069940131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221491388750865426586841 166118541563149069940131)
      ·
        refine ⟨249177812344723604910197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166118541563149069940131 249177812344723604910197)
        ·
          refine ⟨23360419907317837960331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 249177812344723604910197 23360419907317837960331)
          ·
            refine ⟨35040629860976756940497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23360419907317837960331 35040629860976756940497)
            ·
              refine ⟨26280472395732567705373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35040629860976756940497 26280472395732567705373)
              ·
                refine ⟨9855177148399712889515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26280472395732567705373 9855177148399712889515)
                ·
                  rfl

theorem cell19_32388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 2, 3].length) (baseStart_32388 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_32388 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_32388 prefixEnd_32388 := by exact prefixLift 32388
  have htrace : WordTrace (prefixWord ++ tailWord_32388) baseStart_32388 baseEnd_32388 := by
    simpa [prefixWord, tailWord_32388, baseEnd_32388] using wordTrace_append hprefix tailTrace_32388
  have hstable : (prefixWord ++ tailWord_32388).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32388).length < 2 ^ (prefixWord ++ tailWord_32388).sum := by decide
  have hdescent : baseEnd_32388 < baseStart_32388 := by decide
  rcases family_descends (prefixWord ++ tailWord_32388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32546 : List Nat := [3, 3, 1, 1, 2, 1, 2, 6]
def baseStart_32546 : Nat := 118140960795 + 32546 * 2 ^ 59
def prefixEnd_32546 : Nat := 4983230072969 + 3 ^ 40 * 32546 * 2
def baseEnd_32546 : Nat := 9903254151902161377973

theorem tailTrace_32546 : CollatzResearch.WordTrace tailWord_32546 prefixEnd_32546 9903254151902161377973 := by
  unfold tailWord_32546
  simp only [CollatzResearch.WordTrace]
  refine ⟨296762535024718814845373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 791366760065916839587661 296762535024718814845373)
  ·
    refine ⟨111285950634269555567015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 296762535024718814845373 111285950634269555567015)
    ·
      refine ⟨166928925951404333350523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111285950634269555567015 166928925951404333350523)
      ·
        refine ⟨250393388927106500025785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166928925951404333350523 250393388927106500025785)
        ·
          refine ⟨187795041695329875019339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250393388927106500025785 187795041695329875019339)
          ·
            refine ⟨281692562542994812529009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187795041695329875019339 281692562542994812529009)
            ·
              refine ⟨211269421907246109396757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 281692562542994812529009 211269421907246109396757)
              ·
                refine ⟨9903254151902161377973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 211269421907246109396757 9903254151902161377973)
                ·
                  rfl

theorem cell19_32546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 6].length) (baseStart_32546 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_32546 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_32546 prefixEnd_32546 := by exact prefixLift 32546
  have htrace : WordTrace (prefixWord ++ tailWord_32546) baseStart_32546 baseEnd_32546 := by
    simpa [prefixWord, tailWord_32546, baseEnd_32546] using wordTrace_append hprefix tailTrace_32546
  have hstable : (prefixWord ++ tailWord_32546).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32546).length < 2 ^ (prefixWord ++ tailWord_32546).sum := by decide
  have hdescent : baseEnd_32546 < baseStart_32546 := by decide
  rcases family_descends (prefixWord ++ tailWord_32546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32584 : List Nat := [2, 1, 3, 1, 1, 6, 5]
def baseStart_32584 : Nat := 118140960795 + 32584 * 2 ^ 59
def prefixEnd_32584 : Nat := 4983230072969 + 3 ^ 40 * 32584 * 2
def baseEnd_32584 : Nat := 3304938991843110844475

theorem tailTrace_32584 : CollatzResearch.WordTrace tailWord_32584 prefixEnd_32584 3304938991843110844475 := by
  unfold tailWord_32584
  simp only [CollatzResearch.WordTrace]
  refine ⟨594218056980603874632403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 792290742640805166176537 594218056980603874632403)
  ·
    refine ⟨891327085470905811948605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 594218056980603874632403 891327085470905811948605)
    ·
      refine ⟨334247657051589679480727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 891327085470905811948605 334247657051589679480727)
      ·
        refine ⟨501371485577384519221091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334247657051589679480727 501371485577384519221091)
        ·
          refine ⟨752057228366076778831637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 501371485577384519221091 752057228366076778831637)
          ·
            refine ⟨35252682579659849007733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 752057228366076778831637 35252682579659849007733)
            ·
              refine ⟨3304938991843110844475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35252682579659849007733 3304938991843110844475)
              ·
                rfl

theorem cell19_32584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 5].length) (baseStart_32584 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_32584 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_32584 prefixEnd_32584 := by exact prefixLift 32584
  have htrace : WordTrace (prefixWord ++ tailWord_32584) baseStart_32584 baseEnd_32584 := by
    simpa [prefixWord, tailWord_32584, baseEnd_32584] using wordTrace_append hprefix tailTrace_32584
  have hstable : (prefixWord ++ tailWord_32584).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32584).length < 2 ^ (prefixWord ++ tailWord_32584).sum := by decide
  have hdescent : baseEnd_32584 < baseStart_32584 := by decide
  rcases family_descends (prefixWord ++ tailWord_32584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32641 : List Nat := [1, 2, 4, 4, 8]
def baseStart_32641 : Nat := 118140960795 + 32641 * 2 ^ 59
def prefixEnd_32641 : Nat := 4983230072969 + 3 ^ 40 * 32641 * 2
def baseEnd_32641 : Nat := 367857822628521824689

theorem tailTrace_32641 : CollatzResearch.WordTrace tailWord_32641 prefixEnd_32641 367857822628521824689 := by
  unfold tailWord_32641
  simp only [CollatzResearch.WordTrace]
  refine ⟨1190515074754706484089777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 793676716503137656059851 1190515074754706484089777)
  ·
    refine ⟨892886306066029863067333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1190515074754706484089777 892886306066029863067333)
    ·
      refine ⟨167416182387380599325125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 892886306066029863067333 167416182387380599325125)
      ·
        refine ⟨31390534197633862373461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 167416182387380599325125 31390534197633862373461)
        ·
          refine ⟨367857822628521824689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 31390534197633862373461 367857822628521824689)
          ·
            rfl

theorem cell19_32641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 8].length) (baseStart_32641 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_32641 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_32641 prefixEnd_32641 := by exact prefixLift 32641
  have htrace : WordTrace (prefixWord ++ tailWord_32641) baseStart_32641 baseEnd_32641 := by
    simpa [prefixWord, tailWord_32641, baseEnd_32641] using wordTrace_append hprefix tailTrace_32641
  have hstable : (prefixWord ++ tailWord_32641).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32641).length < 2 ^ (prefixWord ++ tailWord_32641).sum := by decide
  have hdescent : baseEnd_32641 < baseStart_32641 := by decide
  rcases family_descends (prefixWord ++ tailWord_32641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32643 : List Nat := [1, 1, 1, 3, 4, 9]
def baseStart_32643 : Nat := 118140960795 + 32643 * 2 ^ 59
def prefixEnd_32643 : Nat := 4983230072969 + 3 ^ 40 * 32643 * 2
def baseEnd_32643 : Nat := 1103641086737186358017

theorem tailTrace_32643 : CollatzResearch.WordTrace tailWord_32643 prefixEnd_32643 1103641086737186358017 := by
  unfold tailWord_32643
  simp only [CollatzResearch.WordTrace]
  refine ⟨1190588020747460825662583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 793725347164973883775055 1190588020747460825662583)
  ·
    refine ⟨1785882031121191238493875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1190588020747460825662583 1785882031121191238493875)
    ·
      refine ⟨2678823046681786857740813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1785882031121191238493875 2678823046681786857740813)
      ·
        refine ⟨1004558642505670071652805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2678823046681786857740813 1004558642505670071652805)
        ·
          refine ⟨188354745469813138434901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1004558642505670071652805 188354745469813138434901)
          ·
            refine ⟨1103641086737186358017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 188354745469813138434901 1103641086737186358017)
            ·
              rfl

theorem cell19_32643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 9].length) (baseStart_32643 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_32643 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_32643 prefixEnd_32643 := by exact prefixLift 32643
  have htrace : WordTrace (prefixWord ++ tailWord_32643) baseStart_32643 baseEnd_32643 := by
    simpa [prefixWord, tailWord_32643, baseEnd_32643] using wordTrace_append hprefix tailTrace_32643
  have hstable : (prefixWord ++ tailWord_32643).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32643).length < 2 ^ (prefixWord ++ tailWord_32643).sum := by decide
  have hdescent : baseEnd_32643 < baseStart_32643 := by decide
  rcases family_descends (prefixWord ++ tailWord_32643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32654 : List Nat := [4, 1, 1, 5, 2, 1, 1, 4]
def baseStart_32654 : Nat := 118140960795 + 32654 * 2 ^ 59
def prefixEnd_32654 : Nat := 4983230072969 + 3 ^ 40 * 32654 * 2
def baseEnd_32654 : Nat := 9936116913789910977679

theorem tailTrace_32654 : CollatzResearch.WordTrace tailWord_32654 prefixEnd_32654 9936116913789910977679 := by
  unfold tailWord_32654
  simp only [CollatzResearch.WordTrace]
  refine ⟨148873652963451213039127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 793992815805073136208677 148873652963451213039127)
  ·
    refine ⟨223310479445176819558691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148873652963451213039127 223310479445176819558691)
    ·
      refine ⟨334965719167765229338037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223310479445176819558691 334965719167765229338037)
      ·
        refine ⟨31403036171977990250441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 334965719167765229338037 31403036171977990250441)
        ·
          refine ⟨23552277128983492687831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31403036171977990250441 23552277128983492687831)
          ·
            refine ⟨35328415693475239031747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23552277128983492687831 35328415693475239031747)
            ·
              refine ⟨52992623540212858547621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35328415693475239031747 52992623540212858547621)
              ·
                refine ⟨9936116913789910977679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52992623540212858547621 9936116913789910977679)
                ·
                  rfl

theorem cell19_32654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 1, 4].length) (baseStart_32654 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_32654 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_32654 prefixEnd_32654 := by exact prefixLift 32654
  have htrace : WordTrace (prefixWord ++ tailWord_32654) baseStart_32654 baseEnd_32654 := by
    simpa [prefixWord, tailWord_32654, baseEnd_32654] using wordTrace_append hprefix tailTrace_32654
  have hstable : (prefixWord ++ tailWord_32654).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32654).length < 2 ^ (prefixWord ++ tailWord_32654).sum := by decide
  have hdescent : baseEnd_32654 < baseStart_32654 := by decide
  rcases family_descends (prefixWord ++ tailWord_32654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32658 : List Nat := [3, 2, 3, 2, 1, 1, 3, 4]
def baseStart_32658 : Nat := 118140960795 + 32658 * 2 ^ 59
def prefixEnd_32658 : Nat := 4983230072969 + 3 ^ 40 * 32658 * 2
def baseEnd_32658 : Nat := 9937334053119086888779

theorem tailTrace_32658 : CollatzResearch.WordTrace tailWord_32658 prefixEnd_32658 9937334053119086888779 := by
  unfold tailWord_32658
  simp only [CollatzResearch.WordTrace]
  refine ⟨297783778923279596864657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 794090077128745591639085 297783778923279596864657)
  ·
    refine ⟨223337834192459697648493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297783778923279596864657 223337834192459697648493)
    ·
      refine ⟨83751687822172386618185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223337834192459697648493 83751687822172386618185)
      ·
        refine ⟨62813765866629289963639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83751687822172386618185 62813765866629289963639)
        ·
          refine ⟨94220648799943934945459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62813765866629289963639 94220648799943934945459)
          ·
            refine ⟨141330973199915902418189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94220648799943934945459 141330973199915902418189)
            ·
              refine ⟨52999114949968463406821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141330973199915902418189 52999114949968463406821)
              ·
                refine ⟨9937334053119086888779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52999114949968463406821 9937334053119086888779)
                ·
                  rfl

theorem cell19_32658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 3, 4].length) (baseStart_32658 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_32658 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_32658 prefixEnd_32658 := by exact prefixLift 32658
  have htrace : WordTrace (prefixWord ++ tailWord_32658) baseStart_32658 baseEnd_32658 := by
    simpa [prefixWord, tailWord_32658, baseEnd_32658] using wordTrace_append hprefix tailTrace_32658
  have hstable : (prefixWord ++ tailWord_32658).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32658).length < 2 ^ (prefixWord ++ tailWord_32658).sum := by decide
  have hdescent : baseEnd_32658 < baseStart_32658 := by decide
  rcases family_descends (prefixWord ++ tailWord_32658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32719 : List Nat := [1, 1, 2, 1, 1, 5, 2, 6]
def baseStart_32719 : Nat := 118140960795 + 32719 * 2 ^ 59
def prefixEnd_32719 : Nat := 4983230072969 + 3 ^ 40 * 32719 * 2
def baseEnd_32719 : Nat := 9955895427889019533057

theorem tailTrace_32719 : CollatzResearch.WordTrace tailWord_32719 prefixEnd_32719 9955895427889019533057 := by
  unfold tailWord_32719
  simp only [CollatzResearch.WordTrace]
  refine ⟨1193359968472125805429211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 795573312314750536952807 1193359968472125805429211)
  ·
    refine ⟨1790039952708188708143817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1193359968472125805429211 1790039952708188708143817)
    ·
      refine ⟨1342529964531141531107863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1790039952708188708143817 1342529964531141531107863)
      ·
        refine ⟨2013794946796712296661795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1342529964531141531107863 2013794946796712296661795)
        ·
          refine ⟨3020692420195068444992693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2013794946796712296661795 3020692420195068444992693)
          ·
            refine ⟨283189914393287666718065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3020692420195068444992693 283189914393287666718065)
            ·
              refine ⟨212392435794965750038549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 283189914393287666718065 212392435794965750038549)
              ·
                refine ⟨9955895427889019533057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 212392435794965750038549 9955895427889019533057)
                ·
                  rfl

theorem cell19_32719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 6].length) (baseStart_32719 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_32719 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_32719 prefixEnd_32719 := by exact prefixLift 32719
  have htrace : WordTrace (prefixWord ++ tailWord_32719) baseStart_32719 baseEnd_32719 := by
    simpa [prefixWord, tailWord_32719, baseEnd_32719] using wordTrace_append hprefix tailTrace_32719
  have hstable : (prefixWord ++ tailWord_32719).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32719).length < 2 ^ (prefixWord ++ tailWord_32719).sum := by decide
  have hdescent : baseEnd_32719 < baseStart_32719 := by decide
  rcases family_descends (prefixWord ++ tailWord_32719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32753 : List Nat := [1, 2, 2, 2, 6, 1, 5]
def baseStart_32753 : Nat := 118140960795 + 32753 * 2 ^ 59
def prefixEnd_32753 : Nat := 4983230072969 + 3 ^ 40 * 32753 * 2
def baseEnd_32753 : Nat := 3322080370729004925803

theorem tailTrace_32753 : CollatzResearch.WordTrace tailWord_32753 prefixEnd_32753 3322080370729004925803 := by
  unfold tailWord_32753
  simp only [CollatzResearch.WordTrace]
  refine ⟨1194600050348949612166913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 796400033565966408111275 1194600050348949612166913)
  ·
    refine ⟨895950037761712209125185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1194600050348949612166913 895950037761712209125185)
    ·
      refine ⟨671962528321284156843889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 895950037761712209125185 671962528321284156843889)
      ·
        refine ⟨503971896240963117632917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 671962528321284156843889 503971896240963117632917)
        ·
          refine ⟨23623682636295146139043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 503971896240963117632917 23623682636295146139043)
          ·
            refine ⟨35435523954442719208565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23623682636295146139043 35435523954442719208565)
            ·
              refine ⟨3322080370729004925803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35435523954442719208565 3322080370729004925803)
              ·
                rfl

theorem cell19_32753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 5].length) (baseStart_32753 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_32753 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_32753 prefixEnd_32753 := by exact prefixLift 32753
  have htrace : WordTrace (prefixWord ++ tailWord_32753) baseStart_32753 baseEnd_32753 := by
    simpa [prefixWord, tailWord_32753, baseEnd_32753] using wordTrace_append hprefix tailTrace_32753
  have hstable : (prefixWord ++ tailWord_32753).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32753).length < 2 ^ (prefixWord ++ tailWord_32753).sum := by decide
  have hdescent : baseEnd_32753 < baseStart_32753 := by decide
  rcases family_descends (prefixWord ++ tailWord_32753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32871 : List Nat := [1, 1, 5, 1, 1, 2, 8]
def baseStart_32871 : Nat := 118140960795 + 32871 * 2 ^ 59
def prefixEnd_32871 : Nat := 4983230072969 + 3 ^ 40 * 32871 * 2
def baseEnd_32871 : Nat := 3334048907465901384955

theorem tailTrace_32871 : CollatzResearch.WordTrace tailWord_32871 prefixEnd_32871 3334048907465901384955 := by
  unfold tailWord_32871
  simp only [CollatzResearch.WordTrace]
  refine ⟨1198903863921455764962467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 799269242614303843308311 1198903863921455764962467)
  ·
    refine ⟨1798355795882183647443701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1198903863921455764962467 1798355795882183647443701)
    ·
      refine ⟨168595855863954716947847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1798355795882183647443701 168595855863954716947847)
      ·
        refine ⟨252893783795932075421771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168595855863954716947847 252893783795932075421771)
        ·
          refine ⟨379340675693898113132657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252893783795932075421771 379340675693898113132657)
          ·
            refine ⟨284505506770423584849493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 379340675693898113132657 284505506770423584849493)
            ·
              refine ⟨3334048907465901384955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 284505506770423584849493 3334048907465901384955)
              ·
                rfl

theorem cell19_32871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 8].length) (baseStart_32871 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_32871 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_32871 prefixEnd_32871 := by exact prefixLift 32871
  have htrace : WordTrace (prefixWord ++ tailWord_32871) baseStart_32871 baseEnd_32871 := by
    simpa [prefixWord, tailWord_32871, baseEnd_32871] using wordTrace_append hprefix tailTrace_32871
  have hstable : (prefixWord ++ tailWord_32871).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32871).length < 2 ^ (prefixWord ++ tailWord_32871).sum := by decide
  have hdescent : baseEnd_32871 < baseStart_32871 := by decide
  rcases family_descends (prefixWord ++ tailWord_32871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32918 : List Nat := [5, 3, 2, 1, 1, 2, 5]
def baseStart_32918 : Nat := 118140960795 + 32918 * 2 ^ 59
def prefixEnd_32918 : Nat := 4983230072969 + 3 ^ 40 * 32918 * 2
def baseEnd_32918 : Nat := 3338816036505173703431

theorem tailTrace_32918 : CollatzResearch.WordTrace tailWord_32918 prefixEnd_32918 3338816036505173703431 := by
  unfold tailWord_32918
  simp only [CollatzResearch.WordTrace]
  refine ⟨75038630921948924495213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 800412063167455194615605 75038630921948924495213)
  ·
    refine ⟨28139486595730846685705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75038630921948924495213 28139486595730846685705)
    ·
      refine ⟨21104614946798135014279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28139486595730846685705 21104614946798135014279)
      ·
        refine ⟨31656922420197202521419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21104614946798135014279 31656922420197202521419)
        ·
          refine ⟨47485383630295803782129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31656922420197202521419 47485383630295803782129)
          ·
            refine ⟨35614037722721852836597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47485383630295803782129 35614037722721852836597)
            ·
              refine ⟨3338816036505173703431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35614037722721852836597 3338816036505173703431)
              ·
                rfl

theorem cell19_32918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 5].length) (baseStart_32918 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_32918 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_32918 prefixEnd_32918 := by exact prefixLift 32918
  have htrace : WordTrace (prefixWord ++ tailWord_32918) baseStart_32918 baseEnd_32918 := by
    simpa [prefixWord, tailWord_32918, baseEnd_32918] using wordTrace_append hprefix tailTrace_32918
  have hstable : (prefixWord ++ tailWord_32918).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32918).length < 2 ^ (prefixWord ++ tailWord_32918).sum := by decide
  have hdescent : baseEnd_32918 < baseStart_32918 := by decide
  rcases family_descends (prefixWord ++ tailWord_32918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32928 : List Nat := [2, 1, 1, 4, 2, 2, 7]
def baseStart_32928 : Nat := 118140960795 + 32928 * 2 ^ 59
def prefixEnd_32928 : Nat := 4983230072969 + 3 ^ 40 * 32928 * 2
def baseEnd_32928 : Nat := 3339830319279486962681

theorem tailTrace_32928 : CollatzResearch.WordTrace tailWord_32928 prefixEnd_32928 3339830319279486962681 := by
  unfold tailWord_32928
  simp only [CollatzResearch.WordTrace]
  refine ⟨600491412357477249893719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 800655216476636333191625 600491412357477249893719)
  ·
    refine ⟨900737118536215874840579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 600491412357477249893719 900737118536215874840579)
    ·
      refine ⟨1351105677804323812260869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 900737118536215874840579 1351105677804323812260869)
      ·
        refine ⟨253332314588310714798913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1351105677804323812260869 253332314588310714798913)
        ·
          refine ⟨189999235941233036099185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 253332314588310714798913 189999235941233036099185)
          ·
            refine ⟨142499426955924777074389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189999235941233036099185 142499426955924777074389)
            ·
              refine ⟨3339830319279486962681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 142499426955924777074389 3339830319279486962681)
              ·
                rfl

theorem cell19_32928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 7].length) (baseStart_32928 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_32928 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_32928 prefixEnd_32928 := by exact prefixLift 32928
  have htrace : WordTrace (prefixWord ++ tailWord_32928) baseStart_32928 baseEnd_32928 := by
    simpa [prefixWord, tailWord_32928, baseEnd_32928] using wordTrace_append hprefix tailTrace_32928
  have hstable : (prefixWord ++ tailWord_32928).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32928).length < 2 ^ (prefixWord ++ tailWord_32928).sum := by decide
  have hdescent : baseEnd_32928 < baseStart_32928 := by decide
  rcases family_descends (prefixWord ++ tailWord_32928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32964 : List Nat := [2, 3, 3, 1, 2, 1, 2, 5]
def baseStart_32964 : Nat := 118140960795 + 32964 * 2 ^ 59
def prefixEnd_32964 : Nat := 4983230072969 + 3 ^ 40 * 32964 * 2
def baseEnd_32964 : Nat := 10030445211801044087945

theorem tailTrace_32964 : CollatzResearch.WordTrace tailWord_32964 prefixEnd_32964 10030445211801044087945 := by
  unfold tailWord_32964
  simp only [CollatzResearch.WordTrace]
  refine ⟨601147926292266324048973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 801530568389688432065297 601147926292266324048973)
  ·
    refine ⟨225430472359599871518365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 601147926292266324048973 225430472359599871518365)
    ·
      refine ⟨84536427134849951819387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225430472359599871518365 84536427134849951819387)
      ·
        refine ⟨126804640702274927729081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84536427134849951819387 126804640702274927729081)
        ·
          refine ⟨95103480526706195796811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126804640702274927729081 95103480526706195796811)
          ·
            refine ⟨142655220790059293695217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95103480526706195796811 142655220790059293695217)
            ·
              refine ⟨106991415592544470271413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142655220790059293695217 106991415592544470271413)
              ·
                refine ⟨10030445211801044087945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 106991415592544470271413 10030445211801044087945)
                ·
                  rfl

theorem cell19_32964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 5].length) (baseStart_32964 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_32964 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_32964 prefixEnd_32964 := by exact prefixLift 32964
  have htrace : WordTrace (prefixWord ++ tailWord_32964) baseStart_32964 baseEnd_32964 := by
    simpa [prefixWord, tailWord_32964, baseEnd_32964] using wordTrace_append hprefix tailTrace_32964
  have hstable : (prefixWord ++ tailWord_32964).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32964).length < 2 ^ (prefixWord ++ tailWord_32964).sum := by decide
  have hdescent : baseEnd_32964 < baseStart_32964 := by decide
  rcases family_descends (prefixWord ++ tailWord_32964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32994 : List Nat := [3, 3, 4, 1, 2, 1, 1, 4]
def baseStart_32994 : Nat := 118140960795 + 32994 * 2 ^ 59
def prefixEnd_32994 : Nat := 4983230072969 + 3 ^ 40 * 32994 * 2
def baseEnd_32994 : Nat := 10039573756769863421197

theorem tailTrace_32994 : CollatzResearch.WordTrace tailWord_32994 prefixEnd_32994 10039573756769863421197 := by
  unfold tailWord_32994
  simp only [CollatzResearch.WordTrace]
  refine ⟨300847510618961942922509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 802260028317231847793357 300847510618961942922509)
  ·
    refine ⟨112817816482110728595941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 300847510618961942922509 112817816482110728595941)
    ·
      refine ⟨21153340590395761611739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112817816482110728595941 21153340590395761611739)
      ·
        refine ⟨31730010885593642417609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21153340590395761611739 31730010885593642417609)
        ·
          refine ⟨23797508164195231813207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31730010885593642417609 23797508164195231813207)
          ·
            refine ⟨35696262246292847719811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23797508164195231813207 35696262246292847719811)
            ·
              refine ⟨53544393369439271579717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35696262246292847719811 53544393369439271579717)
              ·
                refine ⟨10039573756769863421197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53544393369439271579717 10039573756769863421197)
                ·
                  rfl

theorem cell19_32994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 1, 4].length) (baseStart_32994 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_32994 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_32994 prefixEnd_32994 := by exact prefixLift 32994
  have htrace : WordTrace (prefixWord ++ tailWord_32994) baseStart_32994 baseEnd_32994 := by
    simpa [prefixWord, tailWord_32994, baseEnd_32994] using wordTrace_append hprefix tailTrace_32994
  have hstable : (prefixWord ++ tailWord_32994).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32994).length < 2 ^ (prefixWord ++ tailWord_32994).sum := by decide
  have hdescent : baseEnd_32994 < baseStart_32994 := by decide
  rcases family_descends (prefixWord ++ tailWord_32994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33074 : List Nat := [3, 2, 1, 1, 6, 1, 2, 3]
def baseStart_33074 : Nat := 118140960795 + 33074 * 2 ^ 59
def prefixEnd_33074 : Nat := 4983230072969 + 3 ^ 40 * 33074 * 2
def baseEnd_33074 : Nat := 10063916543353381643201

theorem tailTrace_33074 : CollatzResearch.WordTrace tailWord_33074 prefixEnd_33074 10063916543353381643201 := by
  unfold tailWord_33074
  simp only [CollatzResearch.WordTrace]
  refine ⟨301576970546505358650569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 804205254790680956401517 301576970546505358650569)
  ·
    refine ⟨226182727909879018987927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301576970546505358650569 226182727909879018987927)
    ·
      refine ⟨339274091864818528481891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226182727909879018987927 339274091864818528481891)
      ·
        refine ⟨508911137797227792722837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339274091864818528481891 508911137797227792722837)
        ·
          refine ⟨23855209584245052783883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 508911137797227792722837 23855209584245052783883)
          ·
            refine ⟨35782814376367579175825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23855209584245052783883 35782814376367579175825)
            ·
              refine ⟨26837110782275684381869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35782814376367579175825 26837110782275684381869)
              ·
                refine ⟨10063916543353381643201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26837110782275684381869 10063916543353381643201)
                ·
                  rfl

theorem cell19_33074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 2, 3].length) (baseStart_33074 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_33074 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_33074 prefixEnd_33074 := by exact prefixLift 33074
  have htrace : WordTrace (prefixWord ++ tailWord_33074) baseStart_33074 baseEnd_33074 := by
    simpa [prefixWord, tailWord_33074, baseEnd_33074] using wordTrace_append hprefix tailTrace_33074
  have hstable : (prefixWord ++ tailWord_33074).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33074).length < 2 ^ (prefixWord ++ tailWord_33074).sum := by decide
  have hdescent : baseEnd_33074 < baseStart_33074 := by decide
  rcases family_descends (prefixWord ++ tailWord_33074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33076 : List Nat := [2, 5, 1, 1, 1, 2, 4, 3]
def baseStart_33076 : Nat := 118140960795 + 33076 * 2 ^ 59
def prefixEnd_33076 : Nat := 4983230072969 + 3 ^ 40 * 33076 * 2
def baseEnd_33076 : Nat := 10064525113017969598751

theorem tailTrace_33076 : CollatzResearch.WordTrace tailWord_33076 prefixEnd_33076 10064525113017969598751 := by
  unfold tailWord_33076
  simp only [CollatzResearch.WordTrace]
  refine ⟨603190414089387888087541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 804253885452517184116721 603190414089387888087541)
  ·
    refine ⟨56549101320880114508207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 603190414089387888087541 56549101320880114508207)
    ·
      refine ⟨84823651981320171762311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56549101320880114508207 84823651981320171762311)
      ·
        refine ⟨127235477971980257643467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84823651981320171762311 127235477971980257643467)
        ·
          refine ⟨190853216957970386465201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127235477971980257643467 190853216957970386465201)
          ·
            refine ⟨143139912718477789848901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190853216957970386465201 143139912718477789848901)
            ·
              refine ⟨26838733634714585596669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 143139912718477789848901 26838733634714585596669)
              ·
                refine ⟨10064525113017969598751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26838733634714585596669 10064525113017969598751)
                ·
                  rfl

theorem cell19_33076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 4, 3].length) (baseStart_33076 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_33076 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_33076 prefixEnd_33076 := by exact prefixLift 33076
  have htrace : WordTrace (prefixWord ++ tailWord_33076) baseStart_33076 baseEnd_33076 := by
    simpa [prefixWord, tailWord_33076, baseEnd_33076] using wordTrace_append hprefix tailTrace_33076
  have hstable : (prefixWord ++ tailWord_33076).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33076).length < 2 ^ (prefixWord ++ tailWord_33076).sum := by decide
  have hdescent : baseEnd_33076 < baseStart_33076 := by decide
  rcases family_descends (prefixWord ++ tailWord_33076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33154 : List Nat := [3, 4, 2, 1, 9]
def baseStart_33154 : Nat := 118140960795 + 33154 * 2 ^ 59
def prefixEnd_33154 : Nat := 4983230072969 + 3 ^ 40 * 33154 * 2
def baseEnd_33154 : Nat := 373639234442107402415

theorem tailTrace_33154 : CollatzResearch.WordTrace tailWord_33154 prefixEnd_33154 373639234442107402415 := by
  unfold tailWord_33154
  simp only [CollatzResearch.WordTrace]
  refine ⟨302306430474048774378629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 806150481264130065009677 302306430474048774378629)
  ·
    refine ⟨56682455713884145195993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 302306430474048774378629 56682455713884145195993)
    ·
      refine ⟨42511841785413108896995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56682455713884145195993 42511841785413108896995)
      ·
        refine ⟨63767762678119663345493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42511841785413108896995 63767762678119663345493)
        ·
          refine ⟨373639234442107402415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 63767762678119663345493 373639234442107402415)
          ·
            rfl

theorem cell19_33154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 9].length) (baseStart_33154 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_33154 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_33154 prefixEnd_33154 := by exact prefixLift 33154
  have htrace : WordTrace (prefixWord ++ tailWord_33154) baseStart_33154 baseEnd_33154 := by
    simpa [prefixWord, tailWord_33154, baseEnd_33154] using wordTrace_append hprefix tailTrace_33154
  have hstable : (prefixWord ++ tailWord_33154).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33154).length < 2 ^ (prefixWord ++ tailWord_33154).sum := by decide
  have hdescent : baseEnd_33154 < baseStart_33154 := by decide
  rcases family_descends (prefixWord ++ tailWord_33154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33175 : List Nat := [1, 1, 3, 3, 1, 1, 5, 4]
def baseStart_33175 : Nat := 118140960795 + 33175 * 2 ^ 59
def prefixEnd_33175 : Nat := 4983230072969 + 3 ^ 40 * 33175 * 2
def baseEnd_33175 : Nat := 10094649311415073398481

theorem tailTrace_33175 : CollatzResearch.WordTrace tailWord_33175 prefixEnd_33175 10094649311415073398481 := by
  unfold tailWord_33175
  simp only [CollatzResearch.WordTrace]
  refine ⟨1209991654820115684028979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 806661103213410456019319 1209991654820115684028979)
  ·
    refine ⟨1814987482230173526043469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1209991654820115684028979 1814987482230173526043469)
    ·
      refine ⟨680620305836315072266301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1814987482230173526043469 680620305836315072266301)
      ·
        refine ⟨255232614688618152099863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 680620305836315072266301 255232614688618152099863)
        ·
          refine ⟨382848922032927228149795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255232614688618152099863 382848922032927228149795)
          ·
            refine ⟨574273383049390842224693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 382848922032927228149795 574273383049390842224693)
            ·
              refine ⟨53838129660880391458565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 574273383049390842224693 53838129660880391458565)
              ·
                refine ⟨10094649311415073398481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53838129660880391458565 10094649311415073398481)
                ·
                  rfl

theorem cell19_33175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 5, 4].length) (baseStart_33175 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_33175 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_33175 prefixEnd_33175 := by exact prefixLift 33175
  have htrace : WordTrace (prefixWord ++ tailWord_33175) baseStart_33175 baseEnd_33175 := by
    simpa [prefixWord, tailWord_33175, baseEnd_33175] using wordTrace_append hprefix tailTrace_33175
  have hstable : (prefixWord ++ tailWord_33175).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33175).length < 2 ^ (prefixWord ++ tailWord_33175).sum := by decide
  have hdescent : baseEnd_33175 < baseStart_33175 := by decide
  rcases family_descends (prefixWord ++ tailWord_33175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33213 : List Nat := [1, 4, 1, 2, 2, 3, 6]
def baseStart_33213 : Nat := 118140960795 + 33213 * 2 ^ 59
def prefixEnd_33213 : Nat := 4983230072969 + 3 ^ 40 * 33213 * 2
def baseEnd_33213 : Nat := 3368737378347414851311

theorem tailTrace_33213 : CollatzResearch.WordTrace tailWord_33213 prefixEnd_33213 3368737378347414851311 := by
  unfold tailWord_33213
  simp only [CollatzResearch.WordTrace]
  refine ⟨1211377628682448173912293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 807585085788298782608195 1211377628682448173912293)
  ·
    refine ⟨227133305377959032608555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1211377628682448173912293 227133305377959032608555)
    ·
      refine ⟨340699958066938548912833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227133305377959032608555 340699958066938548912833)
      ·
        refine ⟨255524968550203911684625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 340699958066938548912833 255524968550203911684625)
        ·
          refine ⟨191643726412652933763469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255524968550203911684625 191643726412652933763469)
          ·
            refine ⟨71866397404744850161301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191643726412652933763469 71866397404744850161301)
            ·
              refine ⟨3368737378347414851311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 71866397404744850161301 3368737378347414851311)
              ·
                rfl

theorem cell19_33213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 6].length) (baseStart_33213 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_33213 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_33213 prefixEnd_33213 := by exact prefixLift 33213
  have htrace : WordTrace (prefixWord ++ tailWord_33213) baseStart_33213 baseEnd_33213 := by
    simpa [prefixWord, tailWord_33213, baseEnd_33213] using wordTrace_append hprefix tailTrace_33213
  have hstable : (prefixWord ++ tailWord_33213).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33213).length < 2 ^ (prefixWord ++ tailWord_33213).sum := by decide
  have hdescent : baseEnd_33213 < baseStart_33213 := by decide
  rcases family_descends (prefixWord ++ tailWord_33213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33266 : List Nat := [3, 2, 1, 4, 3, 1, 5]
def baseStart_33266 : Nat := 118140960795 + 33266 * 2 ^ 59
def prefixEnd_33266 : Nat := 4983230072969 + 3 ^ 40 * 33266 * 2
def baseEnd_33266 : Nat := 3374113077051275125337

theorem tailTrace_33266 : CollatzResearch.WordTrace tailWord_33266 prefixEnd_33266 3374113077051275125337 := by
  unfold tailWord_33266
  simp only [CollatzResearch.WordTrace]
  refine ⟨303327674372609556397913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 808873798326958817061101 303327674372609556397913)
  ·
    refine ⟨227495755779457167298435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303327674372609556397913 227495755779457167298435)
    ·
      refine ⟨341243633669185750947653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227495755779457167298435 341243633669185750947653)
      ·
        refine ⟨63983181312972328302685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 341243633669185750947653 63983181312972328302685)
        ·
          refine ⟨23993692992364623113507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63983181312972328302685 23993692992364623113507)
          ·
            refine ⟨35990539488546934670261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23993692992364623113507 35990539488546934670261)
            ·
              refine ⟨3374113077051275125337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35990539488546934670261 3374113077051275125337)
              ·
                rfl

theorem cell19_33266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 5].length) (baseStart_33266 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_33266 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_33266 prefixEnd_33266 := by exact prefixLift 33266
  have htrace : WordTrace (prefixWord ++ tailWord_33266) baseStart_33266 baseEnd_33266 := by
    simpa [prefixWord, tailWord_33266, baseEnd_33266] using wordTrace_append hprefix tailTrace_33266
  have hstable : (prefixWord ++ tailWord_33266).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33266).length < 2 ^ (prefixWord ++ tailWord_33266).sum := by decide
  have hdescent : baseEnd_33266 < baseStart_33266 := by decide
  rcases family_descends (prefixWord ++ tailWord_33266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33287 : List Nat := [1, 1, 4, 3, 3, 1, 2, 4]
def baseStart_33287 : Nat := 118140960795 + 33287 * 2 ^ 59
def prefixEnd_33287 : Nat := 4983230072969 + 3 ^ 40 * 33287 * 2
def baseEnd_33287 : Nat := 10128729212631998909287

theorem tailTrace_33287 : CollatzResearch.WordTrace tailWord_33287 prefixEnd_33287 10128729212631998909287 := by
  unfold tailWord_33287
  simp only [CollatzResearch.WordTrace]
  refine ⟨1214076630414358812106115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 809384420276239208070743 1214076630414358812106115)
  ·
    refine ⟨1821114945621538218159173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1214076630414358812106115 1821114945621538218159173)
    ·
      refine ⟨341459052304038415904845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1821114945621538218159173 341459052304038415904845)
      ·
        refine ⟨128047144614014405964317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 341459052304038415904845 128047144614014405964317)
        ·
          refine ⟨48017679230255402236619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128047144614014405964317 48017679230255402236619)
          ·
            refine ⟨72026518845383103354929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48017679230255402236619 72026518845383103354929)
            ·
              refine ⟨54019889134037327516197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72026518845383103354929 54019889134037327516197)
              ·
                refine ⟨10128729212631998909287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54019889134037327516197 10128729212631998909287)
                ·
                  rfl

theorem cell19_33287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 2, 4].length) (baseStart_33287 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_33287 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_33287 prefixEnd_33287 := by exact prefixLift 33287
  have htrace : WordTrace (prefixWord ++ tailWord_33287) baseStart_33287 baseEnd_33287 := by
    simpa [prefixWord, tailWord_33287, baseEnd_33287] using wordTrace_append hprefix tailTrace_33287
  have hstable : (prefixWord ++ tailWord_33287).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33287).length < 2 ^ (prefixWord ++ tailWord_33287).sum := by decide
  have hdescent : baseEnd_33287 < baseStart_33287 := by decide
  rcases family_descends (prefixWord ++ tailWord_33287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33308 : List Nat := [2, 2, 3, 1, 2, 2, 2, 5]
def baseStart_33308 : Nat := 118140960795 + 33308 * 2 ^ 59
def prefixEnd_33308 : Nat := 4983230072969 + 3 ^ 40 * 33308 * 2
def baseEnd_33308 : Nat := 10135119194110172442563

theorem tailTrace_33308 : CollatzResearch.WordTrace tailWord_33308 prefixEnd_33308 10135119194110172442563 := by
  unfold tailWord_33308
  simp only [CollatzResearch.WordTrace]
  refine ⟨607421281669139699310289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 809895042225519599080385 607421281669139699310289)
  ·
    refine ⟨455565961251854774482717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 607421281669139699310289 455565961251854774482717)
    ·
      refine ⟨170837235469445540431019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 455565961251854774482717 170837235469445540431019)
      ·
        refine ⟨256255853204168310646529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170837235469445540431019 256255853204168310646529)
        ·
          refine ⟨192191889903126232984897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256255853204168310646529 192191889903126232984897)
          ·
            refine ⟨144143917427344674738673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192191889903126232984897 144143917427344674738673)
            ·
              refine ⟨108107938070508506054005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144143917427344674738673 108107938070508506054005)
              ·
                refine ⟨10135119194110172442563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 108107938070508506054005 10135119194110172442563)
                ·
                  rfl

theorem cell19_33308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 5].length) (baseStart_33308 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_33308 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_33308 prefixEnd_33308 := by exact prefixLift 33308
  have htrace : WordTrace (prefixWord ++ tailWord_33308) baseStart_33308 baseEnd_33308 := by
    simpa [prefixWord, tailWord_33308, baseEnd_33308] using wordTrace_append hprefix tailTrace_33308
  have hstable : (prefixWord ++ tailWord_33308).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33308).length < 2 ^ (prefixWord ++ tailWord_33308).sum := by decide
  have hdescent : baseEnd_33308 < baseStart_33308 := by decide
  rcases family_descends (prefixWord ++ tailWord_33308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33418 : List Nat := [3, 1, 2, 3, 3, 2, 2, 3]
def baseStart_33418 : Nat := 118140960795 + 33418 * 2 ^ 59
def prefixEnd_33418 : Nat := 4983230072969 + 3 ^ 40 * 33418 * 2
def baseEnd_33418 : Nat := 10168590525662509997819

theorem tailTrace_33418 : CollatzResearch.WordTrace tailWord_33418 prefixEnd_33418 10168590525662509997819 := by
  unfold tailWord_33418
  simp only [CollatzResearch.WordTrace]
  refine ⟨304713648234942046281227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 812569728626512123416605 304713648234942046281227)
  ·
    refine ⟨457070472352413069421841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304713648234942046281227 457070472352413069421841)
    ·
      refine ⟨342802854264309802066381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 457070472352413069421841 342802854264309802066381)
      ·
        refine ⟨128551070349116175774893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 342802854264309802066381 128551070349116175774893)
        ·
          refine ⟨48206651380918565915585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128551070349116175774893 48206651380918565915585)
          ·
            refine ⟨36154988535688924436689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48206651380918565915585 36154988535688924436689)
            ·
              refine ⟨27116241401766693327517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36154988535688924436689 27116241401766693327517)
              ·
                refine ⟨10168590525662509997819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27116241401766693327517 10168590525662509997819)
                ·
                  rfl

theorem cell19_33418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 2, 3].length) (baseStart_33418 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_33418 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_33418 prefixEnd_33418 := by exact prefixLift 33418
  have htrace : WordTrace (prefixWord ++ tailWord_33418) baseStart_33418 baseEnd_33418 := by
    simpa [prefixWord, tailWord_33418, baseEnd_33418] using wordTrace_append hprefix tailTrace_33418
  have hstable : (prefixWord ++ tailWord_33418).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33418).length < 2 ^ (prefixWord ++ tailWord_33418).sum := by decide
  have hdescent : baseEnd_33418 < baseStart_33418 := by decide
  rcases family_descends (prefixWord ++ tailWord_33418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33422 : List Nat := [4, 1, 1, 3, 1, 1, 3, 5]
def baseStart_33422 : Nat := 118140960795 + 33422 * 2 ^ 59
def prefixEnd_33422 : Nat := 4983230072969 + 3 ^ 40 * 33422 * 2
def baseEnd_33422 : Nat := 10169807664991685908919

theorem tailTrace_33422 : CollatzResearch.WordTrace tailWord_33422 prefixEnd_33422 10169807664991685908919 := by
  unfold tailWord_33422
  simp only [CollatzResearch.WordTrace]
  refine ⟨152375060615659608533815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 812666989950184578847013 152375060615659608533815)
  ·
    refine ⟨228562590923489412800723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152375060615659608533815 228562590923489412800723)
    ·
      refine ⟨342843886385234119201085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228562590923489412800723 342843886385234119201085)
      ·
        refine ⟨128566457394462794700407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 342843886385234119201085 128566457394462794700407)
        ·
          refine ⟨192849686091694192050611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128566457394462794700407 192849686091694192050611)
          ·
            refine ⟨289274529137541288075917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192849686091694192050611 289274529137541288075917)
            ·
              refine ⟨108477948426577983028469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 289274529137541288075917 108477948426577983028469)
              ·
                refine ⟨10169807664991685908919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 108477948426577983028469 10169807664991685908919)
                ·
                  rfl

theorem cell19_33422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 5].length) (baseStart_33422 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_33422 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_33422 prefixEnd_33422 := by exact prefixLift 33422
  have htrace : WordTrace (prefixWord ++ tailWord_33422) baseStart_33422 baseEnd_33422 := by
    simpa [prefixWord, tailWord_33422, baseEnd_33422] using wordTrace_append hprefix tailTrace_33422
  have hstable : (prefixWord ++ tailWord_33422).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33422).length < 2 ^ (prefixWord ++ tailWord_33422).sum := by decide
  have hdescent : baseEnd_33422 < baseStart_33422 := by decide
  rcases family_descends (prefixWord ++ tailWord_33422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33557 : List Nat := [1, 3, 2, 1, 2, 2, 8]
def baseStart_33557 : Nat := 118140960795 + 33557 * 2 ^ 59
def prefixEnd_33557 : Nat := 4983230072969 + 3 ^ 40 * 33557 * 2
def baseEnd_33557 : Nat := 3403628705783790969517

theorem tailTrace_33557 : CollatzResearch.WordTrace tailWord_33557 prefixEnd_33557 3403628705783790969517 := by
  unfold tailWord_33557
  simp only [CollatzResearch.WordTrace]
  refine ⟨1223924339436194924434925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 815949559624129949623283 1223924339436194924434925)
  ·
    refine ⟨458971627288573096663097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1223924339436194924434925 458971627288573096663097)
    ·
      refine ⟨344228720466429822497323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 458971627288573096663097 344228720466429822497323)
      ·
        refine ⟨516343080699644733745985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 344228720466429822497323 516343080699644733745985)
        ·
          refine ⟨387257310524733550309489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 516343080699644733745985 387257310524733550309489)
          ·
            refine ⟨290442982893550162732117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 387257310524733550309489 290442982893550162732117)
            ·
              refine ⟨3403628705783790969517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 290442982893550162732117 3403628705783790969517)
              ·
                rfl

theorem cell19_33557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 8].length) (baseStart_33557 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_33557 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_33557 prefixEnd_33557 := by exact prefixLift 33557
  have htrace : WordTrace (prefixWord ++ tailWord_33557) baseStart_33557 baseEnd_33557 := by
    simpa [prefixWord, tailWord_33557, baseEnd_33557] using wordTrace_append hprefix tailTrace_33557
  have hstable : (prefixWord ++ tailWord_33557).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33557).length < 2 ^ (prefixWord ++ tailWord_33557).sum := by decide
  have hdescent : baseEnd_33557 < baseStart_33557 := by decide
  rcases family_descends (prefixWord ++ tailWord_33557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33606 : List Nat := [6, 1, 1, 2, 3, 1, 5]
def baseStart_33606 : Nat := 118140960795 + 33606 * 2 ^ 59
def prefixEnd_33606 : Nat := 4983230072969 + 3 ^ 40 * 33606 * 2
def baseEnd_33606 : Nat := 3408598691377925939843

theorem tailTrace_33606 : CollatzResearch.WordTrace tailWord_33606 prefixEnd_33606 3408598691377925939843 := by
  unfold tailWord_33606
  simp only [CollatzResearch.WordTrace]
  refine ⟨38303484883083634155271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 817141010839117528645781 38303484883083634155271)
  ·
    refine ⟨57455227324625451232907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38303484883083634155271 57455227324625451232907)
    ·
      refine ⟨86182840986938176849361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57455227324625451232907 86182840986938176849361)
      ·
        refine ⟨64637130740203632637021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86182840986938176849361 64637130740203632637021)
        ·
          refine ⟨24238924027576362238883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64637130740203632637021 24238924027576362238883)
          ·
            refine ⟨36358386041364543358325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24238924027576362238883 36358386041364543358325)
            ·
              refine ⟨3408598691377925939843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36358386041364543358325 3408598691377925939843)
              ·
                rfl

theorem cell19_33606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 5].length) (baseStart_33606 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_33606 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_33606 prefixEnd_33606 := by exact prefixLift 33606
  have htrace : WordTrace (prefixWord ++ tailWord_33606) baseStart_33606 baseEnd_33606 := by
    simpa [prefixWord, tailWord_33606, baseEnd_33606] using wordTrace_append hprefix tailTrace_33606
  have hstable : (prefixWord ++ tailWord_33606).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33606).length < 2 ^ (prefixWord ++ tailWord_33606).sum := by decide
  have hdescent : baseEnd_33606 < baseStart_33606 := by decide
  rcases family_descends (prefixWord ++ tailWord_33606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33612 : List Nat := [2, 2, 1, 3, 3, 3, 5]
def baseStart_33612 : Nat := 118140960795 + 33612 * 2 ^ 59
def prefixEnd_33612 : Nat := 4983230072969 + 3 ^ 40 * 33612 * 2
def baseEnd_33612 : Nat := 3409207261042513895393

theorem tailTrace_33612 : CollatzResearch.WordTrace tailWord_33612 prefixEnd_33612 3409207261042513895393 := by
  unfold tailWord_33612
  simp only [CollatzResearch.WordTrace]
  refine ⟨612965177118469658843545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 817286902824626211791393 612965177118469658843545)
  ·
    refine ⟨459723882838852244132659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 612965177118469658843545 459723882838852244132659)
    ·
      refine ⟨689585824258278366198989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 459723882838852244132659 689585824258278366198989)
      ·
        refine ⟨258594684096854387324621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 689585824258278366198989 258594684096854387324621)
        ·
          refine ⟨96973006536320395246733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 258594684096854387324621 96973006536320395246733)
          ·
            refine ⟨36364877451120148217525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96973006536320395246733 36364877451120148217525)
            ·
              refine ⟨3409207261042513895393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36364877451120148217525 3409207261042513895393)
              ·
                rfl

theorem cell19_33612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 5].length) (baseStart_33612 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_33612 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_33612 prefixEnd_33612 := by exact prefixLift 33612
  have htrace : WordTrace (prefixWord ++ tailWord_33612) baseStart_33612 baseEnd_33612 := by
    simpa [prefixWord, tailWord_33612, baseEnd_33612] using wordTrace_append hprefix tailTrace_33612
  have hstable : (prefixWord ++ tailWord_33612).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33612).length < 2 ^ (prefixWord ++ tailWord_33612).sum := by decide
  have hdescent : baseEnd_33612 < baseStart_33612 := by decide
  rcases family_descends (prefixWord ++ tailWord_33612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33671 : List Nat := [1, 1, 4, 2, 3, 8]
def baseStart_33671 : Nat := 118140960795 + 33671 * 2 ^ 59
def prefixEnd_33671 : Nat := 4983230072969 + 3 ^ 40 * 33671 * 2
def baseEnd_33671 : Nat := 1138397176470320708323

theorem tailTrace_33671 : CollatzResearch.WordTrace tailWord_33671 prefixEnd_33671 1138397176470320708323 := by
  unfold tailWord_33671
  simp only [CollatzResearch.WordTrace]
  refine ⟨1228082261023192394084867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 818721507348794929389911 1228082261023192394084867)
  ·
    refine ⟨1842123391534788591127301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1228082261023192394084867 1842123391534788591127301)
    ·
      refine ⟨345398135912772860836369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1842123391534788591127301 345398135912772860836369)
      ·
        refine ⟨259048601934579645627277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 345398135912772860836369 259048601934579645627277)
        ·
          refine ⟨97143225725467367110229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 259048601934579645627277 97143225725467367110229)
          ·
            refine ⟨1138397176470320708323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 97143225725467367110229 1138397176470320708323)
            ·
              rfl

theorem cell19_33671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 8].length) (baseStart_33671 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_33671 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_33671 prefixEnd_33671 := by exact prefixLift 33671
  have htrace : WordTrace (prefixWord ++ tailWord_33671) baseStart_33671 baseEnd_33671 := by
    simpa [prefixWord, tailWord_33671, baseEnd_33671] using wordTrace_append hprefix tailTrace_33671
  have hstable : (prefixWord ++ tailWord_33671).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33671).length < 2 ^ (prefixWord ++ tailWord_33671).sum := by decide
  have hdescent : baseEnd_33671 < baseStart_33671 := by decide
  rcases family_descends (prefixWord ++ tailWord_33671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33728 : List Nat := [2, 1, 1, 2, 3, 4, 6]
def baseStart_33728 : Nat := 118140960795 + 33728 * 2 ^ 59
def prefixEnd_33728 : Nat := 4983230072969 + 3 ^ 40 * 33728 * 2
def baseEnd_33728 : Nat := 3420972941224547702695

theorem tailTrace_33728 : CollatzResearch.WordTrace tailWord_33728 prefixEnd_33728 3420972941224547702695 := by
  unfold tailWord_33728
  simp only [CollatzResearch.WordTrace]
  refine ⟨615080610908345564454919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 820107481211127419273225 615080610908345564454919)
  ·
    refine ⟨922620916362518346682379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 615080610908345564454919 922620916362518346682379)
    ·
      refine ⟨1383931374543777520023569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 922620916362518346682379 1383931374543777520023569)
      ·
        refine ⟨1037948530907833140017677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1383931374543777520023569 1037948530907833140017677)
        ·
          refine ⟨389230699090437427506629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1037948530907833140017677 389230699090437427506629)
          ·
            refine ⟨72980756079457017657493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 389230699090437427506629 72980756079457017657493)
            ·
              refine ⟨3420972941224547702695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 72980756079457017657493 3420972941224547702695)
              ·
                rfl

theorem cell19_33728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 6].length) (baseStart_33728 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_33728 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_33728 prefixEnd_33728 := by exact prefixLift 33728
  have htrace : WordTrace (prefixWord ++ tailWord_33728) baseStart_33728 baseEnd_33728 := by
    simpa [prefixWord, tailWord_33728, baseEnd_33728] using wordTrace_append hprefix tailTrace_33728
  have hstable : (prefixWord ++ tailWord_33728).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33728).length < 2 ^ (prefixWord ++ tailWord_33728).sum := by decide
  have hdescent : baseEnd_33728 < baseStart_33728 := by decide
  rcases family_descends (prefixWord ++ tailWord_33728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33762 : List Nat := [3, 3, 3, 1, 1, 2, 1, 5]
def baseStart_33762 : Nat := 118140960795 + 33762 * 2 ^ 59
def prefixEnd_33762 : Nat := 4983230072969 + 3 ^ 40 * 33762 * 2
def baseEnd_33762 : Nat := 10273264507971638352437

theorem tailTrace_33762 : CollatzResearch.WordTrace tailWord_33762 prefixEnd_33762 10273264507971638352437 := by
  unfold tailWord_33762
  simp only [CollatzResearch.WordTrace]
  refine ⟨307850325923378733911885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 820934202462343290431693 307850325923378733911885)
  ·
    refine ⟨115443872221267025216957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 307850325923378733911885 115443872221267025216957)
    ·
      refine ⟨43291452082975134456359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 115443872221267025216957 43291452082975134456359)
      ·
        refine ⟨64937178124462701684539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43291452082975134456359 64937178124462701684539)
        ·
          refine ⟨97405767186694052526809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64937178124462701684539 97405767186694052526809)
          ·
            refine ⟨73054325390020539395107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97405767186694052526809 73054325390020539395107)
            ·
              refine ⟨109581488085030809092661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73054325390020539395107 109581488085030809092661)
              ·
                refine ⟨10273264507971638352437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 109581488085030809092661 10273264507971638352437)
                ·
                  rfl

theorem cell19_33762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 5].length) (baseStart_33762 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_33762 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_33762 prefixEnd_33762 := by exact prefixLift 33762
  have htrace : WordTrace (prefixWord ++ tailWord_33762) baseStart_33762 baseEnd_33762 := by
    simpa [prefixWord, tailWord_33762, baseEnd_33762] using wordTrace_append hprefix tailTrace_33762
  have hstable : (prefixWord ++ tailWord_33762).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33762).length < 2 ^ (prefixWord ++ tailWord_33762).sum := by decide
  have hdescent : baseEnd_33762 < baseStart_33762 := by decide
  rcases family_descends (prefixWord ++ tailWord_33762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33802 : List Nat := [3, 1, 2, 2, 3, 2, 2, 4]
def baseStart_33802 : Nat := 118140960795 + 33802 * 2 ^ 59
def prefixEnd_33802 : Nat := 4983230072969 + 3 ^ 40 * 33802 * 2
def baseEnd_33802 : Nat := 10285435901263397463439

theorem tailTrace_33802 : CollatzResearch.WordTrace tailWord_33802 prefixEnd_33802 10285435901263397463439 := by
  unfold tailWord_33802
  simp only [CollatzResearch.WordTrace]
  refine ⟨308215055887150441775915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 821906815699067844735773 308215055887150441775915)
  ·
    refine ⟨462322583830725662663873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 308215055887150441775915 462322583830725662663873)
    ·
      refine ⟨346741937873044246997905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 462322583830725662663873 346741937873044246997905)
      ·
        refine ⟨260056453404783185248429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 346741937873044246997905 260056453404783185248429)
        ·
          refine ⟨97521170026793694468161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 260056453404783185248429 97521170026793694468161)
          ·
            refine ⟨73140877520095270851121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97521170026793694468161 73140877520095270851121)
            ·
              refine ⟨54855658140071453138341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73140877520095270851121 54855658140071453138341)
              ·
                refine ⟨10285435901263397463439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54855658140071453138341 10285435901263397463439)
                ·
                  rfl

theorem cell19_33802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 2, 4].length) (baseStart_33802 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_33802 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_33802 prefixEnd_33802 := by exact prefixLift 33802
  have htrace : WordTrace (prefixWord ++ tailWord_33802) baseStart_33802 baseEnd_33802 := by
    simpa [prefixWord, tailWord_33802, baseEnd_33802] using wordTrace_append hprefix tailTrace_33802
  have hstable : (prefixWord ++ tailWord_33802).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33802).length < 2 ^ (prefixWord ++ tailWord_33802).sum := by decide
  have hdescent : baseEnd_33802 < baseStart_33802 := by decide
  rcases family_descends (prefixWord ++ tailWord_33802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33804 : List Nat := [2, 2, 1, 2, 3, 2, 1, 6]
def baseStart_33804 : Nat := 118140960795 + 33804 * 2 ^ 59
def prefixEnd_33804 : Nat := 4983230072969 + 3 ^ 40 * 33804 * 2
def baseEnd_33804 : Nat := 10286044470927985418989

theorem tailTrace_33804 : CollatzResearch.WordTrace tailWord_33804 prefixEnd_33804 10286044470927985418989 := by
  unfold tailWord_33804
  simp only [CollatzResearch.WordTrace]
  refine ⟨616466584770678054338233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 821955446360904072450977 616466584770678054338233)
  ·
    refine ⟨462349938578008540753675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 616466584770678054338233 462349938578008540753675)
    ·
      refine ⟨693524907867012811130513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 462349938578008540753675 693524907867012811130513)
      ·
        refine ⟨520143680900259608347885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 693524907867012811130513 520143680900259608347885)
        ·
          refine ⟨195053880337597353130457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 520143680900259608347885 195053880337597353130457)
          ·
            refine ⟨146290410253198014847843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 195053880337597353130457 146290410253198014847843)
            ·
              refine ⟨219435615379797022271765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 146290410253198014847843 219435615379797022271765)
              ·
                refine ⟨10286044470927985418989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 219435615379797022271765 10286044470927985418989)
                ·
                  rfl

theorem cell19_33804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 6].length) (baseStart_33804 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_33804 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_33804 prefixEnd_33804 := by exact prefixLift 33804
  have htrace : WordTrace (prefixWord ++ tailWord_33804) baseStart_33804 baseEnd_33804 := by
    simpa [prefixWord, tailWord_33804, baseEnd_33804] using wordTrace_append hprefix tailTrace_33804
  have hstable : (prefixWord ++ tailWord_33804).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33804).length < 2 ^ (prefixWord ++ tailWord_33804).sum := by decide
  have hdescent : baseEnd_33804 < baseStart_33804 := by decide
  rcases family_descends (prefixWord ++ tailWord_33804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33823 : List Nat := [1, 1, 2, 4, 1, 3, 2, 5]
def baseStart_33823 : Nat := 118140960795 + 33823 * 2 ^ 59
def prefixEnd_33823 : Nat := 4983230072969 + 3 ^ 40 * 33823 * 2
def baseEnd_33823 : Nat := 10291825882741570996715

theorem tailTrace_33823 : CollatzResearch.WordTrace tailWord_33823 prefixEnd_33823 10291825882741570996715 := by
  unfold tailWord_33823
  simp only [CollatzResearch.WordTrace]
  refine ⟨1233626156472522353618123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 822417437648348235745415 1233626156472522353618123)
  ·
    refine ⟨1850439234708783530427185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1233626156472522353618123 1850439234708783530427185)
    ·
      refine ⟨1387829426031587647820389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1850439234708783530427185 1387829426031587647820389)
      ·
        refine ⟨260218017380922683966323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1387829426031587647820389 260218017380922683966323)
        ·
          refine ⟨390327026071384025949485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 260218017380922683966323 390327026071384025949485)
          ·
            refine ⟨146372634776769009731057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 390327026071384025949485 146372634776769009731057)
            ·
              refine ⟨109779476082576757298293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 146372634776769009731057 109779476082576757298293)
              ·
                refine ⟨10291825882741570996715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 109779476082576757298293 10291825882741570996715)
                ·
                  rfl

theorem cell19_33823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 5].length) (baseStart_33823 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_33823 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_33823 prefixEnd_33823 := by exact prefixLift 33823
  have htrace : WordTrace (prefixWord ++ tailWord_33823) baseStart_33823 baseEnd_33823 := by
    simpa [prefixWord, tailWord_33823, baseEnd_33823] using wordTrace_append hprefix tailTrace_33823
  have hstable : (prefixWord ++ tailWord_33823).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33823).length < 2 ^ (prefixWord ++ tailWord_33823).sum := by decide
  have hdescent : baseEnd_33823 < baseStart_33823 := by decide
  rcases family_descends (prefixWord ++ tailWord_33823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33857 : List Nat := [1, 2, 5, 1, 3, 2, 1, 4]
def baseStart_33857 : Nat := 118140960795 + 33857 * 2 ^ 59
def prefixEnd_33857 : Nat := 4983230072969 + 3 ^ 40 * 33857 * 2
def baseEnd_33857 : Nat := 10302171567039566241067

theorem tailTrace_33857 : CollatzResearch.WordTrace tailWord_33857 prefixEnd_33857 10302171567039566241067 := by
  unfold tailWord_33857
  simp only [CollatzResearch.WordTrace]
  refine ⟨1234866238349346160355825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 823244158899564106903883 1234866238349346160355825)
  ·
    refine ⟨926149678762009620266869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1234866238349346160355825 926149678762009620266869)
    ·
      refine ⟨86826532383938401900019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 926149678762009620266869 86826532383938401900019)
      ·
        refine ⟨130239798575907602850029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86826532383938401900019 130239798575907602850029)
        ·
          refine ⟨48839924465965351068761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 130239798575907602850029 48839924465965351068761)
          ·
            refine ⟨36629943349474013301571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48839924465965351068761 36629943349474013301571)
            ·
              refine ⟨54944915024211019952357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36629943349474013301571 54944915024211019952357)
              ·
                refine ⟨10302171567039566241067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54944915024211019952357 10302171567039566241067)
                ·
                  rfl

theorem cell19_33857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 1, 4].length) (baseStart_33857 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_33857 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_33857 prefixEnd_33857 := by exact prefixLift 33857
  have htrace : WordTrace (prefixWord ++ tailWord_33857) baseStart_33857 baseEnd_33857 := by
    simpa [prefixWord, tailWord_33857, baseEnd_33857] using wordTrace_append hprefix tailTrace_33857
  have hstable : (prefixWord ++ tailWord_33857).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33857).length < 2 ^ (prefixWord ++ tailWord_33857).sum := by decide
  have hdescent : baseEnd_33857 < baseStart_33857 := by decide
  rcases family_descends (prefixWord ++ tailWord_33857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33861 : List Nat := [1, 3, 1, 1, 1, 3, 5, 4]
def baseStart_33861 : Nat := 118140960795 + 33861 * 2 ^ 59
def prefixEnd_33861 : Nat := 4983230072969 + 3 ^ 40 * 33861 * 2
def baseEnd_33861 : Nat := 10303388706368742152167

theorem tailTrace_33861 : CollatzResearch.WordTrace tailWord_33861 prefixEnd_33861 10303388706368742152167 := by
  unfold tailWord_33861
  simp only [CollatzResearch.WordTrace]
  refine ⟨1235012130334854843501437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 823341420223236562334291 1235012130334854843501437)
  ·
    refine ⟨463129548875570566313039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1235012130334854843501437 463129548875570566313039)
    ·
      refine ⟨694694323313355849469559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 463129548875570566313039 694694323313355849469559)
      ·
        refine ⟨1042041484970033774204339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 694694323313355849469559 1042041484970033774204339)
        ·
          refine ⟨1563062227455050661306509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1042041484970033774204339 1563062227455050661306509)
          ·
            refine ⟨586148335295643997989941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1563062227455050661306509 586148335295643997989941)
            ·
              refine ⟨54951406433966624811557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 586148335295643997989941 54951406433966624811557)
              ·
                refine ⟨10303388706368742152167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54951406433966624811557 10303388706368742152167)
                ·
                  rfl

theorem cell19_33861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5, 4].length) (baseStart_33861 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_33861 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_33861 prefixEnd_33861 := by exact prefixLift 33861
  have htrace : WordTrace (prefixWord ++ tailWord_33861) baseStart_33861 baseEnd_33861 := by
    simpa [prefixWord, tailWord_33861, baseEnd_33861] using wordTrace_append hprefix tailTrace_33861
  have hstable : (prefixWord ++ tailWord_33861).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33861).length < 2 ^ (prefixWord ++ tailWord_33861).sum := by decide
  have hdescent : baseEnd_33861 < baseStart_33861 := by decide
  rcases family_descends (prefixWord ++ tailWord_33861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33956 : List Nat := [2, 3, 1, 2, 3, 1, 7]
def baseStart_33956 : Nat := 118140960795 + 33956 * 2 ^ 59
def prefixEnd_33956 : Nat := 4983230072969 + 3 ^ 40 * 33956 * 2
def baseEnd_33956 : Nat := 3444098588478890013599

theorem tailTrace_33956 : CollatzResearch.WordTrace tailWord_33956 prefixEnd_33956 3444098588478890013599 := by
  unfold tailWord_33956
  simp only [CollatzResearch.WordTrace]
  refine ⟨619238532495343034104861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 825651376660457378806481 619238532495343034104861)
  ·
    refine ⟨232214449685753637789323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 619238532495343034104861 232214449685753637789323)
    ·
      refine ⟨348321674528630456683985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 232214449685753637789323 348321674528630456683985)
      ·
        refine ⟨261241255896472842512989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 348321674528630456683985 261241255896472842512989)
        ·
          refine ⟨97965470961177315942371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 261241255896472842512989 97965470961177315942371)
          ·
            refine ⟨146948206441765973913557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97965470961177315942371 146948206441765973913557)
            ·
              refine ⟨3444098588478890013599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 146948206441765973913557 3444098588478890013599)
              ·
                rfl

theorem cell19_33956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 7].length) (baseStart_33956 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_33956 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_33956 prefixEnd_33956 := by exact prefixLift 33956
  have htrace : WordTrace (prefixWord ++ tailWord_33956) baseStart_33956 baseEnd_33956 := by
    simpa [prefixWord, tailWord_33956, baseEnd_33956] using wordTrace_append hprefix tailTrace_33956
  have hstable : (prefixWord ++ tailWord_33956).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33956).length < 2 ^ (prefixWord ++ tailWord_33956).sum := by decide
  have hdescent : baseEnd_33956 < baseStart_33956 := by decide
  rcases family_descends (prefixWord ++ tailWord_33956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33975 : List Nat := [1, 1, 3, 1, 4, 1, 4, 4]
def baseStart_33975 : Nat := 118140960795 + 33975 * 2 ^ 59
def prefixEnd_33975 : Nat := 4983230072969 + 3 ^ 40 * 33975 * 2
def baseEnd_33975 : Nat := 10338077177250255618523

theorem tailTrace_33975 : CollatzResearch.WordTrace tailWord_33975 prefixEnd_33975 10338077177250255618523 := by
  unfold tailWord_33975
  simp only [CollatzResearch.WordTrace]
  refine ⟨1239170051921852313151379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 826113367947901542100919 1239170051921852313151379)
  ·
    refine ⟨1858755077882778469727069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1239170051921852313151379 1858755077882778469727069)
    ·
      refine ⟨697033154206041926147651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1858755077882778469727069 697033154206041926147651)
      ·
        refine ⟨1045549731309062889221477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 697033154206041926147651 1045549731309062889221477)
        ·
          refine ⟨196040574620449291729027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1045549731309062889221477 196040574620449291729027)
          ·
            refine ⟨294060861930673937593541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 196040574620449291729027 294060861930673937593541)
            ·
              refine ⟨55136411612001363298789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 294060861930673937593541 55136411612001363298789)
              ·
                refine ⟨10338077177250255618523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 55136411612001363298789 10338077177250255618523)
                ·
                  rfl

theorem cell19_33975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 4, 4].length) (baseStart_33975 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_33975 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_33975 prefixEnd_33975 := by exact prefixLift 33975
  have htrace : WordTrace (prefixWord ++ tailWord_33975) baseStart_33975 baseEnd_33975 := by
    simpa [prefixWord, tailWord_33975, baseEnd_33975] using wordTrace_append hprefix tailTrace_33975
  have hstable : (prefixWord ++ tailWord_33975).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33975).length < 2 ^ (prefixWord ++ tailWord_33975).sum := by decide
  have hdescent : baseEnd_33975 < baseStart_33975 := by decide
  rcases family_descends (prefixWord ++ tailWord_33975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33994 : List Nat := [3, 1, 2, 1, 3, 2, 2, 5]
def baseStart_33994 : Nat := 118140960795 + 33994 * 2 ^ 59
def prefixEnd_33994 : Nat := 4983230072969 + 3 ^ 40 * 33994 * 2
def baseEnd_33994 : Nat := 10343858589063841196249

theorem tailTrace_33994 : CollatzResearch.WordTrace tailWord_33994 prefixEnd_33994 10343858589063841196249 := by
  unfold tailWord_33994
  simp only [CollatzResearch.WordTrace]
  refine ⟨309965759713254639523259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 826575359235345705395357 309965759713254639523259)
  ·
    refine ⟨464948639569881959284889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 309965759713254639523259 464948639569881959284889)
    ·
      refine ⟨348711479677411469463667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 464948639569881959284889 348711479677411469463667)
      ·
        refine ⟨523067219516117204195501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 348711479677411469463667 523067219516117204195501)
        ·
          refine ⟨196150207318543951573313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 523067219516117204195501 196150207318543951573313)
          ·
            refine ⟨147112655488907963679985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 196150207318543951573313 147112655488907963679985)
            ·
              refine ⟨110334491616680972759989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 147112655488907963679985 110334491616680972759989)
              ·
                refine ⟨10343858589063841196249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 110334491616680972759989 10343858589063841196249)
                ·
                  rfl

theorem cell19_33994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 5].length) (baseStart_33994 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_33994 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_33994 prefixEnd_33994 := by exact prefixLift 33994
  have htrace : WordTrace (prefixWord ++ tailWord_33994) baseStart_33994 baseEnd_33994 := by
    simpa [prefixWord, tailWord_33994, baseEnd_33994] using wordTrace_append hprefix tailTrace_33994
  have hstable : (prefixWord ++ tailWord_33994).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33994).length < 2 ^ (prefixWord ++ tailWord_33994).sum := by decide
  have hdescent : baseEnd_33994 < baseStart_33994 := by decide
  rcases family_descends (prefixWord ++ tailWord_33994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34013 : List Nat := [1, 4, 3, 2, 9]
def baseStart_34013 : Nat := 118140960795 + 34013 * 2 ^ 59
def prefixEnd_34013 : Nat := 4983230072969 + 3 ^ 40 * 34013 * 2
def baseEnd_34013 : Nat := 383320000032497287925

theorem tailTrace_34013 : CollatzResearch.WordTrace tailWord_34013 prefixEnd_34013 383320000032497287925 := by
  unfold tailWord_34013
  simp only [CollatzResearch.WordTrace]
  refine ⟨1240556025784184803034693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 827037350522789868689795 1240556025784184803034693)
  ·
    refine ⟨232604254834534650569005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1240556025784184803034693 232604254834534650569005)
    ·
      refine ⟨87226595562950493963377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 232604254834534650569005 87226595562950493963377)
      ·
        refine ⟨65419946672212870472533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87226595562950493963377 65419946672212870472533)
        ·
          refine ⟨383320000032497287925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 65419946672212870472533 383320000032497287925)
          ·
            rfl

theorem cell19_34013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 9].length) (baseStart_34013 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_34013 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_34013 prefixEnd_34013 := by exact prefixLift 34013
  have htrace : WordTrace (prefixWord ++ tailWord_34013) baseStart_34013 baseEnd_34013 := by
    simpa [prefixWord, tailWord_34013, baseEnd_34013] using wordTrace_append hprefix tailTrace_34013
  have hstable : (prefixWord ++ tailWord_34013).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34013).length < 2 ^ (prefixWord ++ tailWord_34013).sum := by decide
  have hdescent : baseEnd_34013 < baseStart_34013 := by decide
  rcases family_descends (prefixWord ++ tailWord_34013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34049 : List Nat := [1, 2, 4, 1, 1, 4, 3, 3]
def baseStart_34049 : Nat := 118140960795 + 34049 * 2 ^ 59
def prefixEnd_34049 : Nat := 4983230072969 + 3 ^ 40 * 34049 * 2
def baseEnd_34049 : Nat := 10360594254840009973877

theorem tailTrace_34049 : CollatzResearch.WordTrace tailWord_34049 prefixEnd_34049 10360594254840009973877 := by
  unfold tailWord_34049
  simp only [CollatzResearch.WordTrace]
  refine ⟨1241869053653762951345201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 827912702435841967563467 1241869053653762951345201)
  ·
    refine ⟨931401790240322213508901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1241869053653762951345201 931401790240322213508901)
    ·
      refine ⟨174637835670060415032919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 931401790240322213508901 174637835670060415032919)
      ·
        refine ⟨261956753505090622549379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174637835670060415032919 261956753505090622549379)
        ·
          refine ⟨392935130257635933824069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 261956753505090622549379 392935130257635933824069)
          ·
            refine ⟨73675336923306737592013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 392935130257635933824069 73675336923306737592013)
            ·
              refine ⟨27628251346240026597005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73675336923306737592013 27628251346240026597005)
              ·
                refine ⟨10360594254840009973877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27628251346240026597005 10360594254840009973877)
                ·
                  rfl

theorem cell19_34049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 3, 3].length) (baseStart_34049 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_34049 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_34049 prefixEnd_34049 := by exact prefixLift 34049
  have htrace : WordTrace (prefixWord ++ tailWord_34049) baseStart_34049 baseEnd_34049 := by
    simpa [prefixWord, tailWord_34049, baseEnd_34049] using wordTrace_append hprefix tailTrace_34049
  have hstable : (prefixWord ++ tailWord_34049).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34049).length < 2 ^ (prefixWord ++ tailWord_34049).sum := by decide
  have hdescent : baseEnd_34049 < baseStart_34049 := by decide
  rcases family_descends (prefixWord ++ tailWord_34049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34066 : List Nat := [3, 2, 4, 2, 1, 1, 6]
def baseStart_34066 : Nat := 118140960795 + 34066 * 2 ^ 59
def prefixEnd_34066 : Nat := 4983230072969 + 3 ^ 40 * 34066 * 2
def baseEnd_34066 : Nat := 3455255698996335865351

theorem tailTrace_34066 : CollatzResearch.WordTrace tailWord_34066 prefixEnd_34066 3455255698996335865351 := by
  unfold tailWord_34066
  simp only [CollatzResearch.WordTrace]
  refine ⟨310622273648043713678513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 828326063061449903142701 310622273648043713678513)
  ·
    refine ⟨232966705236032785258885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 310622273648043713678513 232966705236032785258885)
    ·
      refine ⟨43681257231756147236041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 232966705236032785258885 43681257231756147236041)
      ·
        refine ⟨32760942923817110427031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43681257231756147236041 32760942923817110427031)
        ·
          refine ⟨49141414385725665640547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32760942923817110427031 49141414385725665640547)
          ·
            refine ⟨73712121578588498460821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49141414385725665640547 73712121578588498460821)
            ·
              refine ⟨3455255698996335865351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 73712121578588498460821 3455255698996335865351)
              ·
                rfl

theorem cell19_34066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 6].length) (baseStart_34066 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_34066 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_34066 prefixEnd_34066 := by exact prefixLift 34066
  have htrace : WordTrace (prefixWord ++ tailWord_34066) baseStart_34066 baseEnd_34066 := by
    simpa [prefixWord, tailWord_34066, baseEnd_34066] using wordTrace_append hprefix tailTrace_34066
  have hstable : (prefixWord ++ tailWord_34066).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34066).length < 2 ^ (prefixWord ++ tailWord_34066).sum := by decide
  have hdescent : baseEnd_34066 < baseStart_34066 := by decide
  rcases family_descends (prefixWord ++ tailWord_34066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34108 : List Nat := [2, 2, 2, 2, 1, 4, 1, 5]
def baseStart_34108 : Nat := 118140960795 + 34108 * 2 ^ 59
def prefixEnd_34108 : Nat := 4983230072969 + 3 ^ 40 * 34108 * 2
def baseEnd_34108 : Nat := 10378547059945354662605

theorem tailTrace_34108 : CollatzResearch.WordTrace tailWord_34108 prefixEnd_34108 10378547059945354662605 := by
  unfold tailWord_34108
  simp only [CollatzResearch.WordTrace]
  refine ⟨622010480220008013871489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 829347306960010685161985 622010480220008013871489)
  ·
    refine ⟨466507860165006010403617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 622010480220008013871489 466507860165006010403617)
    ·
      refine ⟨349880895123754507802713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 466507860165006010403617 349880895123754507802713)
      ·
        refine ⟨262410671342815880852035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 349880895123754507802713 262410671342815880852035)
        ·
          refine ⟨393616007014223821278053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 262410671342815880852035 393616007014223821278053)
          ·
            refine ⟨73803001315166966489635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 393616007014223821278053 73803001315166966489635)
            ·
              refine ⟨110704501972750449734453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73803001315166966489635 110704501972750449734453)
              ·
                refine ⟨10378547059945354662605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 110704501972750449734453 10378547059945354662605)
                ·
                  rfl

theorem cell19_34108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 5].length) (baseStart_34108 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_34108 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_34108 prefixEnd_34108 := by exact prefixLift 34108
  have htrace : WordTrace (prefixWord ++ tailWord_34108) baseStart_34108 baseEnd_34108 := by
    simpa [prefixWord, tailWord_34108, baseEnd_34108] using wordTrace_append hprefix tailTrace_34108
  have hstable : (prefixWord ++ tailWord_34108).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34108).length < 2 ^ (prefixWord ++ tailWord_34108).sum := by decide
  have hdescent : baseEnd_34108 < baseStart_34108 := by decide
  rcases family_descends (prefixWord ++ tailWord_34108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34167 : List Nat := [1, 1, 3, 1, 1, 2, 3, 7]
def baseStart_34167 : Nat := 118140960795 + 34167 * 2 ^ 59
def prefixEnd_34167 : Nat := 4983230072969 + 3 ^ 40 * 34167 * 2
def baseEnd_34167 : Nat := 10396499865050699351333

theorem tailTrace_34167 : CollatzResearch.WordTrace tailWord_34167 prefixEnd_34167 10396499865050699351333 := by
  unfold tailWord_34167
  simp only [CollatzResearch.WordTrace]
  refine ⟨1246172867226269104140755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 830781911484179402760503 1246172867226269104140755)
  ·
    refine ⟨1869259300839403656211133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1246172867226269104140755 1869259300839403656211133)
    ·
      refine ⟨700972237814776371079175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1869259300839403656211133 700972237814776371079175)
      ·
        refine ⟨1051458356722164556618763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 700972237814776371079175 1051458356722164556618763)
        ·
          refine ⟨1577187535083246834928145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1051458356722164556618763 1577187535083246834928145)
          ·
            refine ⟨1182890651312435126196109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1577187535083246834928145 1182890651312435126196109)
            ·
              refine ⟨443583994242163172323541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1182890651312435126196109 443583994242163172323541)
              ·
                refine ⟨10396499865050699351333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 443583994242163172323541 10396499865050699351333)
                ·
                  rfl

theorem cell19_34167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 7].length) (baseStart_34167 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_34167 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_34167 prefixEnd_34167 := by exact prefixLift 34167
  have htrace : WordTrace (prefixWord ++ tailWord_34167) baseStart_34167 baseEnd_34167 := by
    simpa [prefixWord, tailWord_34167, baseEnd_34167] using wordTrace_append hprefix tailTrace_34167
  have hstable : (prefixWord ++ tailWord_34167).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34167).length < 2 ^ (prefixWord ++ tailWord_34167).sum := by decide
  have hdescent : baseEnd_34167 < baseStart_34167 := by decide
  rcases family_descends (prefixWord ++ tailWord_34167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34186 : List Nat := [3, 1, 2, 13]
def baseStart_34186 : Nat := 118140960795 + 34186 * 2 ^ 59
def prefixEnd_34186 : Nat := 4983230072969 + 3 ^ 40 * 34186 * 2
def baseEnd_34186 : Nat := 128423225640299813939

theorem tailTrace_34186 : CollatzResearch.WordTrace tailWord_34186 prefixEnd_34186 128423225640299813939 := by
  unfold tailWord_34186
  simp only [CollatzResearch.WordTrace]
  refine ⟨311716463539358837270603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 831243902771623566054941 311716463539358837270603)
  ·
    refine ⟨467574695309038255905905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 311716463539358837270603 467574695309038255905905)
    ·
      refine ⟨350681021481778691929429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 467574695309038255905905 350681021481778691929429)
      ·
        refine ⟨128423225640299813939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 350681021481778691929429 128423225640299813939)
        ·
          rfl

theorem cell19_34186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 13].length) (baseStart_34186 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_34186 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_34186 prefixEnd_34186 := by exact prefixLift 34186
  have htrace : WordTrace (prefixWord ++ tailWord_34186) baseStart_34186 baseEnd_34186 := by
    simpa [prefixWord, tailWord_34186, baseEnd_34186] using wordTrace_append hprefix tailTrace_34186
  have hstable : (prefixWord ++ tailWord_34186).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34186).length < 2 ^ (prefixWord ++ tailWord_34186).sum := by decide
  have hdescent : baseEnd_34186 < baseStart_34186 := by decide
  rcases family_descends (prefixWord ++ tailWord_34186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34277 : List Nat := [1, 3, 1, 5, 1, 1, 4, 3]
def baseStart_34277 : Nat := 118140960795 + 34277 * 2 ^ 59
def prefixEnd_34277 : Nat := 4983230072969 + 3 ^ 40 * 34277 * 2
def baseEnd_34277 : Nat := 10429971196603036906589

theorem tailTrace_34277 : CollatzResearch.WordTrace tailWord_34277 prefixEnd_34277 10429971196603036906589 := by
  unfold tailWord_34277
  simp only [CollatzResearch.WordTrace]
  refine ⟨1250184896827757890645085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 833456597885171927096723 1250184896827757890645085)
  ·
    refine ⟨468819336310409208991907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1250184896827757890645085 468819336310409208991907)
    ·
      refine ⟨703229004465613813487861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 468819336310409208991907 703229004465613813487861)
      ·
        refine ⟨65927719168651295014487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 703229004465613813487861 65927719168651295014487)
        ·
          refine ⟨98891578752976942521731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65927719168651295014487 98891578752976942521731)
          ·
            refine ⟨148337368129465413782597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98891578752976942521731 148337368129465413782597)
            ·
              refine ⟨27813256524274765084237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 148337368129465413782597 27813256524274765084237)
              ·
                refine ⟨10429971196603036906589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27813256524274765084237 10429971196603036906589)
                ·
                  rfl

theorem cell19_34277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 4, 3].length) (baseStart_34277 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_34277 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_34277 prefixEnd_34277 := by exact prefixLift 34277
  have htrace : WordTrace (prefixWord ++ tailWord_34277) baseStart_34277 baseEnd_34277 := by
    simpa [prefixWord, tailWord_34277, baseEnd_34277] using wordTrace_append hprefix tailTrace_34277
  have hstable : (prefixWord ++ tailWord_34277).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34277).length < 2 ^ (prefixWord ++ tailWord_34277).sum := by decide
  have hdescent : baseEnd_34277 < baseStart_34277 := by decide
  rcases family_descends (prefixWord ++ tailWord_34277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34279 : List Nat := [1, 1, 5, 2, 1, 3, 1, 5]
def baseStart_34279 : Nat := 118140960795 + 34279 * 2 ^ 59
def prefixEnd_34279 : Nat := 4983230072969 + 3 ^ 40 * 34279 * 2
def baseEnd_34279 : Nat := 10430579766267624862139

theorem tailTrace_34279 : CollatzResearch.WordTrace tailWord_34279 prefixEnd_34279 10430579766267624862139 := by
  unfold tailWord_34279
  simp only [CollatzResearch.WordTrace]
  refine ⟨1250257842820512232217891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 833505228547008154811927 1250257842820512232217891)
  ·
    refine ⟨1875386764230768348326837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1250257842820512232217891 1875386764230768348326837)
    ·
      refine ⟨175817509146634532655641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1875386764230768348326837 175817509146634532655641)
      ·
        refine ⟨131863131859975899491731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 175817509146634532655641 131863131859975899491731)
        ·
          refine ⟨197794697789963849237597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131863131859975899491731 197794697789963849237597)
          ·
            refine ⟨74173011671236443464099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 197794697789963849237597 74173011671236443464099)
            ·
              refine ⟨111259517506854665196149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74173011671236443464099 111259517506854665196149)
              ·
                refine ⟨10430579766267624862139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 111259517506854665196149 10430579766267624862139)
                ·
                  rfl

theorem cell19_34279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 5].length) (baseStart_34279 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_34279 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_34279 prefixEnd_34279 := by exact prefixLift 34279
  have htrace : WordTrace (prefixWord ++ tailWord_34279) baseStart_34279 baseEnd_34279 := by
    simpa [prefixWord, tailWord_34279, baseEnd_34279] using wordTrace_append hprefix tailTrace_34279
  have hstable : (prefixWord ++ tailWord_34279).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34279).length < 2 ^ (prefixWord ++ tailWord_34279).sum := by decide
  have hdescent : baseEnd_34279 < baseStart_34279 := by decide
  rcases family_descends (prefixWord ++ tailWord_34279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34300 : List Nat := [2, 2, 2, 1, 2, 1, 9]
def baseStart_34300 : Nat := 118140960795 + 34300 * 2 ^ 59
def prefixEnd_34300 : Nat := 4983230072969 + 3 ^ 40 * 34300 * 2
def baseEnd_34300 : Nat := 3478989915915266131805

theorem tailTrace_34300 : CollatzResearch.WordTrace tailWord_34300 prefixEnd_34300 3478989915915266131805 := by
  unfold tailWord_34300
  simp only [CollatzResearch.WordTrace]
  refine ⟨625511887872216409366177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 834015850496288545821569 625511887872216409366177)
  ·
    refine ⟨469133915904162307024633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 625511887872216409366177 469133915904162307024633)
    ·
      refine ⟨351850436928121730268475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 469133915904162307024633 351850436928121730268475)
      ·
        refine ⟨527775655392182595402713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 351850436928121730268475 527775655392182595402713)
        ·
          refine ⟨395831741544136946552035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 527775655392182595402713 395831741544136946552035)
          ·
            refine ⟨593747612316205419828053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 395831741544136946552035 593747612316205419828053)
            ·
              refine ⟨3478989915915266131805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 593747612316205419828053 3478989915915266131805)
              ·
                rfl

theorem cell19_34300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 9].length) (baseStart_34300 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_34300 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_34300 prefixEnd_34300 := by exact prefixLift 34300
  have htrace : WordTrace (prefixWord ++ tailWord_34300) baseStart_34300 baseEnd_34300 := by
    simpa [prefixWord, tailWord_34300, baseEnd_34300] using wordTrace_append hprefix tailTrace_34300
  have hstable : (prefixWord ++ tailWord_34300).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34300).length < 2 ^ (prefixWord ++ tailWord_34300).sum := by decide
  have hdescent : baseEnd_34300 < baseStart_34300 := by decide
  rcases family_descends (prefixWord ++ tailWord_34300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34336 : List Nat := [2, 1, 1, 6, 1, 1, 2, 5]
def baseStart_34336 : Nat := 118140960795 + 34336 * 2 ^ 59
def prefixEnd_34336 : Nat := 4983230072969 + 3 ^ 40 * 34336 * 2
def baseEnd_34336 : Nat := 10447924001708381595317

theorem tailTrace_34336 : CollatzResearch.WordTrace tailWord_34336 prefixEnd_34336 10447924001708381595317 := by
  unfold tailWord_34336
  simp only [CollatzResearch.WordTrace]
  refine ⟨626168401807005483521431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 834891202409340644695241 626168401807005483521431)
  ·
    refine ⟨939252602710508225282147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 626168401807005483521431 939252602710508225282147)
    ·
      refine ⟨1408878904065762337923221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 939252602710508225282147 1408878904065762337923221)
      ·
        refine ⟨66041198628082609590151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 1408878904065762337923221 66041198628082609590151)
        ·
          refine ⟨99061797942123914385227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66041198628082609590151 99061797942123914385227)
          ·
            refine ⟨148592696913185871577841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99061797942123914385227 148592696913185871577841)
            ·
              refine ⟨111444522684889403683381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 148592696913185871577841 111444522684889403683381)
              ·
                refine ⟨10447924001708381595317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 111444522684889403683381 10447924001708381595317)
                ·
                  rfl

theorem cell19_34336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 5].length) (baseStart_34336 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_34336 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_34336 prefixEnd_34336 := by exact prefixLift 34336
  have htrace : WordTrace (prefixWord ++ tailWord_34336) baseStart_34336 baseEnd_34336 := by
    simpa [prefixWord, tailWord_34336, baseEnd_34336] using wordTrace_append hprefix tailTrace_34336
  have hstable : (prefixWord ++ tailWord_34336).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34336).length < 2 ^ (prefixWord ++ tailWord_34336).sum := by decide
  have hdescent : baseEnd_34336 < baseStart_34336 := by decide
  rcases family_descends (prefixWord ++ tailWord_34336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34357 : List Nat := [1, 3, 3, 1, 1, 10]
def baseStart_34357 : Nat := 118140960795 + 34357 * 2 ^ 59
def prefixEnd_34357 : Nat := 4983230072969 + 3 ^ 40 * 34357 * 2
def baseEnd_34357 : Nat := 1161590442576283903177

theorem tailTrace_34357 : CollatzResearch.WordTrace tailWord_34357 prefixEnd_34357 1161590442576283903177 := by
  unfold tailWord_34357
  simp only [CollatzResearch.WordTrace]
  refine ⟨1253102736537931553557325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 835401824358621035704883 1253102736537931553557325)
  ·
    refine ⟨469913526201724332583997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1253102736537931553557325 469913526201724332583997)
    ·
      refine ⟨176217572325646624718999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 469913526201724332583997 176217572325646624718999)
      ·
        refine ⟨264326358488469937078499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176217572325646624718999 264326358488469937078499)
        ·
          refine ⟨396489537732704905617749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 264326358488469937078499 396489537732704905617749)
          ·
            refine ⟨1161590442576283903177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 396489537732704905617749 1161590442576283903177)
            ·
              rfl

theorem cell19_34357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 10].length) (baseStart_34357 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_34357 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_34357 prefixEnd_34357 := by exact prefixLift 34357
  have htrace : WordTrace (prefixWord ++ tailWord_34357) baseStart_34357 baseEnd_34357 := by
    simpa [prefixWord, tailWord_34357, baseEnd_34357] using wordTrace_append hprefix tailTrace_34357
  have hstable : (prefixWord ++ tailWord_34357).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34357).length < 2 ^ (prefixWord ++ tailWord_34357).sum := by decide
  have hdescent : baseEnd_34357 < baseStart_34357 := by decide
  rcases family_descends (prefixWord ++ tailWord_34357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34486 : List Nat := [5, 1, 3, 1, 1, 1, 1, 6]
def baseStart_34486 : Nat := 118140960795 + 34486 * 2 ^ 59
def prefixEnd_34486 : Nat := 4983230072969 + 3 ^ 40 * 34486 * 2
def baseEnd_34486 : Nat := 10493566726552478261575

theorem tailTrace_34486 : CollatzResearch.WordTrace tailWord_34486 prefixEnd_34486 10493566726552478261575 := by
  unfold tailWord_34486
  simp only [CollatzResearch.WordTrace]
  refine ⟨78612984566911661562707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 838538502047057723335541 78612984566911661562707)
  ·
    refine ⟨117919476850367492344061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78612984566911661562707 117919476850367492344061)
    ·
      refine ⟨44219803818887809629023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117919476850367492344061 44219803818887809629023)
      ·
        refine ⟨66329705728331714443535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44219803818887809629023 66329705728331714443535)
        ·
          refine ⟨99494558592497571665303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66329705728331714443535 99494558592497571665303)
          ·
            refine ⟨149241837888746357497955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99494558592497571665303 149241837888746357497955)
            ·
              refine ⟨223862756833119536246933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 149241837888746357497955 223862756833119536246933)
              ·
                refine ⟨10493566726552478261575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 223862756833119536246933 10493566726552478261575)
                ·
                  rfl

theorem cell19_34486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_34486 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_34486 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_34486 prefixEnd_34486 := by exact prefixLift 34486
  have htrace : WordTrace (prefixWord ++ tailWord_34486) baseStart_34486 baseEnd_34486 := by
    simpa [prefixWord, tailWord_34486, baseEnd_34486] using wordTrace_append hprefix tailTrace_34486
  have hstable : (prefixWord ++ tailWord_34486).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34486).length < 2 ^ (prefixWord ++ tailWord_34486).sum := by decide
  have hdescent : baseEnd_34486 < baseStart_34486 := by decide
  rcases family_descends (prefixWord ++ tailWord_34486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34490 : List Nat := [3, 1, 1, 1, 2, 4, 1, 6]
def baseStart_34490 : Nat := 118140960795 + 34490 * 2 ^ 59
def prefixEnd_34490 : Nat := 4983230072969 + 3 ^ 40 * 34490 * 2
def baseEnd_34490 : Nat := 10494783865881654172675

theorem tailTrace_34490 : CollatzResearch.WordTrace tailWord_34490 prefixEnd_34490 10494783865881654172675 := by
  unfold tailWord_34490
  simp only [CollatzResearch.WordTrace]
  refine ⟨314488411264023817037231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 838635763370730178765949 314488411264023817037231)
  ·
    refine ⟨471732616896035725555847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 314488411264023817037231 471732616896035725555847)
    ·
      refine ⟨707598925344053588333771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 471732616896035725555847 707598925344053588333771)
      ·
        refine ⟨1061398388016080382500657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 707598925344053588333771 1061398388016080382500657)
        ·
          refine ⟨796048791012060286875493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1061398388016080382500657 796048791012060286875493)
          ·
            refine ⟨149259148314761303789155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 796048791012060286875493 149259148314761303789155)
            ·
              refine ⟨223888722472141955683733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 149259148314761303789155 223888722472141955683733)
              ·
                refine ⟨10494783865881654172675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 223888722472141955683733 10494783865881654172675)
                ·
                  rfl

theorem cell19_34490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 6].length) (baseStart_34490 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_34490 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_34490 prefixEnd_34490 := by exact prefixLift 34490
  have htrace : WordTrace (prefixWord ++ tailWord_34490) baseStart_34490 baseEnd_34490 := by
    simpa [prefixWord, tailWord_34490, baseEnd_34490] using wordTrace_append hprefix tailTrace_34490
  have hstable : (prefixWord ++ tailWord_34490).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34490).length < 2 ^ (prefixWord ++ tailWord_34490).sum := by decide
  have hdescent : baseEnd_34490 < baseStart_34490 := by decide
  rcases family_descends (prefixWord ++ tailWord_34490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34524 : List Nat := [2, 2, 5, 1, 3, 6]
def baseStart_34524 : Nat := 118140960795 + 34524 * 2 ^ 59
def prefixEnd_34524 : Nat := 4983230072969 + 3 ^ 40 * 34524 * 2
def baseEnd_34524 : Nat := 1167236616686627713003

theorem tailTrace_34524 : CollatzResearch.WordTrace tailWord_34524 prefixEnd_34524 1167236616686627713003 := by
  unfold tailWord_34524
  simp only [CollatzResearch.WordTrace]
  refine ⟨629596863466459537443313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 839462484621946049924417 629596863466459537443313)
  ·
    refine ⟨472197647599844653082485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 629596863466459537443313 472197647599844653082485)
    ·
      refine ⟨44268529462485436226483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 472197647599844653082485 44268529462485436226483)
      ·
        refine ⟨66402794193728154339725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44268529462485436226483 66402794193728154339725)
        ·
          refine ⟨24901047822648057877397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66402794193728154339725 24901047822648057877397)
          ·
            refine ⟨1167236616686627713003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 24901047822648057877397 1167236616686627713003)
            ·
              rfl

theorem cell19_34524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 6].length) (baseStart_34524 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_34524 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_34524 prefixEnd_34524 := by exact prefixLift 34524
  have htrace : WordTrace (prefixWord ++ tailWord_34524) baseStart_34524 baseEnd_34524 := by
    simpa [prefixWord, tailWord_34524, baseEnd_34524] using wordTrace_append hprefix tailTrace_34524
  have hstable : (prefixWord ++ tailWord_34524).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34524).length < 2 ^ (prefixWord ++ tailWord_34524).sum := by decide
  have hdescent : baseEnd_34524 < baseStart_34524 := by decide
  rcases family_descends (prefixWord ++ tailWord_34524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34545 : List Nat := [1, 2, 2, 2, 2, 5, 1, 4]
def baseStart_34545 : Nat := 118140960795 + 34545 * 2 ^ 59
def prefixEnd_34545 : Nat := 4983230072969 + 3 ^ 40 * 34545 * 2
def baseEnd_34545 : Nat := 10511519531657822950303

theorem tailTrace_34545 : CollatzResearch.WordTrace tailWord_34545 prefixEnd_34545 10511519531657822950303 := by
  unfold tailWord_34545
  simp only [CollatzResearch.WordTrace]
  refine ⟨1259959659856839661401089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 839973106571226440934059 1259959659856839661401089)
  ·
    refine ⟨944969744892629746050817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1259959659856839661401089 944969744892629746050817)
    ·
      refine ⟨708727308669472309538113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 944969744892629746050817 708727308669472309538113)
      ·
        refine ⟨531545481502104232153585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 708727308669472309538113 531545481502104232153585)
        ·
          refine ⟨398659111126578174115189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 531545481502104232153585 398659111126578174115189)
          ·
            refine ⟨37374291668116703823299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 398659111126578174115189 37374291668116703823299)
            ·
              refine ⟨56061437502175055734949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37374291668116703823299 56061437502175055734949)
              ·
                refine ⟨10511519531657822950303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56061437502175055734949 10511519531657822950303)
                ·
                  rfl

theorem cell19_34545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 1, 4].length) (baseStart_34545 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_34545 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_34545 prefixEnd_34545 := by exact prefixLift 34545
  have htrace : WordTrace (prefixWord ++ tailWord_34545) baseStart_34545 baseEnd_34545 := by
    simpa [prefixWord, tailWord_34545, baseEnd_34545] using wordTrace_append hprefix tailTrace_34545
  have hstable : (prefixWord ++ tailWord_34545).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34545).length < 2 ^ (prefixWord ++ tailWord_34545).sum := by decide
  have hdescent : baseEnd_34545 < baseStart_34545 := by decide
  rcases family_descends (prefixWord ++ tailWord_34545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34547 : List Nat := [1, 1, 1, 2, 2, 3, 5, 4]
def baseStart_34547 : Nat := 118140960795 + 34547 * 2 ^ 59
def prefixEnd_34547 : Nat := 4983230072969 + 3 ^ 40 * 34547 * 2
def baseEnd_34547 : Nat := 10512128101322410905853

theorem tailTrace_34547 : CollatzResearch.WordTrace tailWord_34547 prefixEnd_34547 10512128101322410905853 := by
  unfold tailWord_34547
  simp only [CollatzResearch.WordTrace]
  refine ⟨1260032605849594002973895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 840021737233062668649263 1260032605849594002973895)
  ·
    refine ⟨1890048908774391004460843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1260032605849594002973895 1890048908774391004460843)
    ·
      refine ⟨2835073363161586506691265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1890048908774391004460843 2835073363161586506691265)
      ·
        refine ⟨2126305022371189880018449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2835073363161586506691265 2126305022371189880018449)
        ·
          refine ⟨1594728766778392410013837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2126305022371189880018449 1594728766778392410013837)
          ·
            refine ⟨598023287541897153755189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1594728766778392410013837 598023287541897153755189)
            ·
              refine ⟨56064683207052858164549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 598023287541897153755189 56064683207052858164549)
              ·
                refine ⟨10512128101322410905853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56064683207052858164549 10512128101322410905853)
                ·
                  rfl

theorem cell19_34547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 5, 4].length) (baseStart_34547 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_34547 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_34547 prefixEnd_34547 := by exact prefixLift 34547
  have htrace : WordTrace (prefixWord ++ tailWord_34547) baseStart_34547 baseEnd_34547 := by
    simpa [prefixWord, tailWord_34547, baseEnd_34547] using wordTrace_append hprefix tailTrace_34547
  have hstable : (prefixWord ++ tailWord_34547).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34547).length < 2 ^ (prefixWord ++ tailWord_34547).sum := by decide
  have hdescent : baseEnd_34547 < baseStart_34547 := by decide
  rcases family_descends (prefixWord ++ tailWord_34547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34562 : List Nat := [3, 4, 1, 1, 1, 1, 5, 3]
def baseStart_34562 : Nat := 118140960795 + 34562 * 2 ^ 59
def prefixEnd_34562 : Nat := 4983230072969 + 3 ^ 40 * 34562 * 2
def baseEnd_34562 : Nat := 10516692373806820572479

theorem tailTrace_34562 : CollatzResearch.WordTrace tailWord_34562 prefixEnd_34562 10516692373806820572479 := by
  unfold tailWord_34562
  simp only [CollatzResearch.WordTrace]
  refine ⟨315144925198812891192485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 840386467196834376513293 315144925198812891192485)
  ·
    refine ⟨59089673474777417098591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 315144925198812891192485 59089673474777417098591)
    ·
      refine ⟨88634510212166125647887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59089673474777417098591 88634510212166125647887)
      ·
        refine ⟨132951765318249188471831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88634510212166125647887 132951765318249188471831)
        ·
          refine ⟨199427647977373782707747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132951765318249188471831 199427647977373782707747)
          ·
            refine ⟨299141471966060674061621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 199427647977373782707747 299141471966060674061621)
            ·
              refine ⟨28044512996818188193277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 299141471966060674061621 28044512996818188193277)
              ·
                refine ⟨10516692373806820572479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28044512996818188193277 10516692373806820572479)
                ·
                  rfl

theorem cell19_34562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 5, 3].length) (baseStart_34562 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_34562 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_34562 prefixEnd_34562 := by exact prefixLift 34562
  have htrace : WordTrace (prefixWord ++ tailWord_34562) baseStart_34562 baseEnd_34562 := by
    simpa [prefixWord, tailWord_34562, baseEnd_34562] using wordTrace_append hprefix tailTrace_34562
  have hstable : (prefixWord ++ tailWord_34562).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34562).length < 2 ^ (prefixWord ++ tailWord_34562).sum := by decide
  have hdescent : baseEnd_34562 < baseStart_34562 := by decide
  rcases family_descends (prefixWord ++ tailWord_34562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34617 : List Nat := [1, 2, 1, 7, 1, 2, 2, 3]
def baseStart_34617 : Nat := 118140960795 + 34617 * 2 ^ 59
def prefixEnd_34617 : Nat := 4983230072969 + 3 ^ 40 * 34617 * 2
def baseEnd_34617 : Nat := 10533428039582989350107

theorem tailTrace_34617 : CollatzResearch.WordTrace tailWord_34617 prefixEnd_34617 10533428039582989350107 := by
  unfold tailWord_34617
  simp only [CollatzResearch.WordTrace]
  refine ⟨1262585715595995958022105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 841723810397330638681403 1262585715595995958022105)
  ·
    refine ⟨946939286696996968516579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1262585715595995958022105 946939286696996968516579)
    ·
      refine ⟨1420408930045495452774869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 946939286696996968516579 1420408930045495452774869)
      ·
        refine ⟨33290834297941299674411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 1420408930045495452774869 33290834297941299674411)
        ·
          refine ⟨49936251446911949511617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33290834297941299674411 49936251446911949511617)
          ·
            refine ⟨37452188585183962133713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49936251446911949511617 37452188585183962133713)
            ·
              refine ⟨28089141438887971600285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37452188585183962133713 28089141438887971600285)
              ·
                refine ⟨10533428039582989350107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28089141438887971600285 10533428039582989350107)
                ·
                  rfl

theorem cell19_34617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 2, 3].length) (baseStart_34617 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_34617 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_34617 prefixEnd_34617 := by exact prefixLift 34617
  have htrace : WordTrace (prefixWord ++ tailWord_34617) baseStart_34617 baseEnd_34617 := by
    simpa [prefixWord, tailWord_34617, baseEnd_34617] using wordTrace_append hprefix tailTrace_34617
  have hstable : (prefixWord ++ tailWord_34617).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34617).length < 2 ^ (prefixWord ++ tailWord_34617).sum := by decide
  have hdescent : baseEnd_34617 < baseStart_34617 := by decide
  rcases family_descends (prefixWord ++ tailWord_34617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34621 : List Nat := [1, 4, 1, 4, 1, 2, 1, 5]
def baseStart_34621 : Nat := 118140960795 + 34621 * 2 ^ 59
def prefixEnd_34621 : Nat := 4983230072969 + 3 ^ 40 * 34621 * 2
def baseEnd_34621 : Nat := 10534645178912165261207

theorem tailTrace_34621 : CollatzResearch.WordTrace tailWord_34621 prefixEnd_34621 10534645178912165261207 := by
  unfold tailWord_34621
  simp only [CollatzResearch.WordTrace]
  refine ⟨1262731607581504641167717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 841821071721003094111811 1262731607581504641167717)
  ·
    refine ⟨236762176421532120218947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1262731607581504641167717 236762176421532120218947)
    ·
      refine ⟨355143264632298180328421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236762176421532120218947 355143264632298180328421)
      ·
        refine ⟨66589362118555908811579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 355143264632298180328421 66589362118555908811579)
        ·
          refine ⟨99884043177833863217369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66589362118555908811579 99884043177833863217369)
          ·
            refine ⟨74913032383375397413027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99884043177833863217369 74913032383375397413027)
            ·
              refine ⟨112369548575063096119541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74913032383375397413027 112369548575063096119541)
              ·
                refine ⟨10534645178912165261207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 112369548575063096119541 10534645178912165261207)
                ·
                  rfl

theorem cell19_34621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 5].length) (baseStart_34621 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_34621 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_34621 prefixEnd_34621 := by exact prefixLift 34621
  have htrace : WordTrace (prefixWord ++ tailWord_34621) baseStart_34621 baseEnd_34621 := by
    simpa [prefixWord, tailWord_34621, baseEnd_34621] using wordTrace_append hprefix tailTrace_34621
  have hstable : (prefixWord ++ tailWord_34621).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34621).length < 2 ^ (prefixWord ++ tailWord_34621).sum := by decide
  have hdescent : baseEnd_34621 < baseStart_34621 := by decide
  rcases family_descends (prefixWord ++ tailWord_34621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34642 : List Nat := [3, 2, 2, 1, 1, 3, 7]
def baseStart_34642 : Nat := 118140960795 + 34642 * 2 ^ 59
def prefixEnd_34642 : Nat := 4983230072969 + 3 ^ 40 * 34642 * 2
def baseEnd_34642 : Nat := 3513678386796779598161

theorem tailTrace_34642 : CollatzResearch.WordTrace tailWord_34642 prefixEnd_34642 3513678386796779598161 := by
  unfold tailWord_34642
  simp only [CollatzResearch.WordTrace]
  refine ⟨315874385126356306920545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 842331693670283485121453 315874385126356306920545)
  ·
    refine ⟨236905788844767230190409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 315874385126356306920545 236905788844767230190409)
    ·
      refine ⟨177679341633575422642807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 236905788844767230190409 177679341633575422642807)
      ·
        refine ⟨266519012450363133964211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177679341633575422642807 266519012450363133964211)
        ·
          refine ⟨399778518675544700946317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 266519012450363133964211 399778518675544700946317)
          ·
            refine ⟨149916944503329262854869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 399778518675544700946317 149916944503329262854869)
            ·
              refine ⟨3513678386796779598161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 149916944503329262854869 3513678386796779598161)
              ·
                rfl

theorem cell19_34642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 7].length) (baseStart_34642 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_34642 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_34642 prefixEnd_34642 := by exact prefixLift 34642
  have htrace : WordTrace (prefixWord ++ tailWord_34642) baseStart_34642 baseEnd_34642 := by
    simpa [prefixWord, tailWord_34642, baseEnd_34642] using wordTrace_append hprefix tailTrace_34642
  have hstable : (prefixWord ++ tailWord_34642).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34642).length < 2 ^ (prefixWord ++ tailWord_34642).sum := by decide
  have hdescent : baseEnd_34642 < baseStart_34642 := by decide
  rcases family_descends (prefixWord ++ tailWord_34642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34659 : List Nat := [1, 1, 1, 5, 4, 1, 2, 4]
def baseStart_34659 : Nat := 118140960795 + 34659 * 2 ^ 59
def prefixEnd_34659 : Nat := 4983230072969 + 3 ^ 40 * 34659 * 2
def baseEnd_34659 : Nat := 10546208002539336416659

theorem tailTrace_34659 : CollatzResearch.WordTrace tailWord_34659 prefixEnd_34659 10546208002539336416659 := by
  unfold tailWord_34659
  simp only [CollatzResearch.WordTrace]
  refine ⟨1264117581443837131051031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 842745054295891420700687 1264117581443837131051031)
  ·
    refine ⟨1896176372165755696576547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1264117581443837131051031 1896176372165755696576547)
    ·
      refine ⟨2844264558248633544864821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1896176372165755696576547 2844264558248633544864821)
      ·
        refine ⟨266649802335809394831077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2844264558248633544864821 266649802335809394831077)
        ·
          refine ⟨49996837937964261530827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 266649802335809394831077 49996837937964261530827)
          ·
            refine ⟨74995256906946392296241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49996837937964261530827 74995256906946392296241)
            ·
              refine ⟨56246442680209794222181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74995256906946392296241 56246442680209794222181)
              ·
                refine ⟨10546208002539336416659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56246442680209794222181 10546208002539336416659)
                ·
                  rfl

theorem cell19_34659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 2, 4].length) (baseStart_34659 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_34659 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_34659 prefixEnd_34659 := by exact prefixLift 34659
  have htrace : WordTrace (prefixWord ++ tailWord_34659) baseStart_34659 baseEnd_34659 := by
    simpa [prefixWord, tailWord_34659, baseEnd_34659] using wordTrace_append hprefix tailTrace_34659
  have hstable : (prefixWord ++ tailWord_34659).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34659).length < 2 ^ (prefixWord ++ tailWord_34659).sum := by decide
  have hdescent : baseEnd_34659 < baseStart_34659 := by decide
  rcases family_descends (prefixWord ++ tailWord_34659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34710 : List Nat := [5, 3, 1, 1, 2, 2, 1, 4]
def baseStart_34710 : Nat := 118140960795 + 34710 * 2 ^ 59
def prefixEnd_34710 : Nat := 4983230072969 + 3 ^ 40 * 34710 * 2
def baseEnd_34710 : Nat := 10561726528986329283187

theorem tailTrace_34710 : CollatzResearch.WordTrace tailWord_34710 prefixEnd_34710 10561726528986329283187 := by
  unfold tailWord_34710
  simp only [CollatzResearch.WordTrace]
  refine ⟨79123606516192052572349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 843985136172715227438389 79123606516192052572349)
  ·
    refine ⟨29671352443572019714631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79123606516192052572349 29671352443572019714631)
    ·
      refine ⟨44507028665358029571947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29671352443572019714631 44507028665358029571947)
      ·
        refine ⟨66760542998037044357921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44507028665358029571947 66760542998037044357921)
        ·
          refine ⟨50070407248527783268441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66760542998037044357921 50070407248527783268441)
          ·
            refine ⟨37552805436395837451331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50070407248527783268441 37552805436395837451331)
            ·
              refine ⟨56329208154593756176997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37552805436395837451331 56329208154593756176997)
              ·
                refine ⟨10561726528986329283187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56329208154593756176997 10561726528986329283187)
                ·
                  rfl

theorem cell19_34710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 1, 4].length) (baseStart_34710 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_34710 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_34710 prefixEnd_34710 := by exact prefixLift 34710
  have htrace : WordTrace (prefixWord ++ tailWord_34710) baseStart_34710 baseEnd_34710 := by
    simpa [prefixWord, tailWord_34710, baseEnd_34710] using wordTrace_append hprefix tailTrace_34710
  have hstable : (prefixWord ++ tailWord_34710).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34710).length < 2 ^ (prefixWord ++ tailWord_34710).sum := by decide
  have hdescent : baseEnd_34710 < baseStart_34710 := by decide
  rcases family_descends (prefixWord ++ tailWord_34710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34712 : List Nat := [2, 1, 2, 6, 2, 1, 1, 4]
def baseStart_34712 : Nat := 118140960795 + 34712 * 2 ^ 59
def prefixEnd_34712 : Nat := 4983230072969 + 3 ^ 40 * 34712 * 2
def baseEnd_34712 : Nat := 10562335098650917238737

theorem tailTrace_34712 : CollatzResearch.WordTrace tailWord_34712 prefixEnd_34712 10562335098650917238737 := by
  unfold tailWord_34712
  simp only [CollatzResearch.WordTrace]
  refine ⟨633025325125913591365195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 844033766834551455153593 633025325125913591365195)
  ·
    refine ⟨949537987688870387047793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 633025325125913591365195 949537987688870387047793)
    ·
      refine ⟨712153490766652790285845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 949537987688870387047793 712153490766652790285845)
      ·
        refine ⟨33382194879686849544649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 712153490766652790285845 33382194879686849544649)
        ·
          refine ⟨25036646159765137158487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33382194879686849544649 25036646159765137158487)
          ·
            refine ⟨37554969239647705737731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25036646159765137158487 37554969239647705737731)
            ·
              refine ⟨56332453859471558606597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37554969239647705737731 56332453859471558606597)
              ·
                refine ⟨10562335098650917238737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56332453859471558606597 10562335098650917238737)
                ·
                  rfl

theorem cell19_34712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 1, 4].length) (baseStart_34712 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_34712 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_34712 prefixEnd_34712 := by exact prefixLift 34712
  have htrace : WordTrace (prefixWord ++ tailWord_34712) baseStart_34712 baseEnd_34712 := by
    simpa [prefixWord, tailWord_34712, baseEnd_34712] using wordTrace_append hprefix tailTrace_34712
  have hstable : (prefixWord ++ tailWord_34712).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34712).length < 2 ^ (prefixWord ++ tailWord_34712).sum := by decide
  have hdescent : baseEnd_34712 < baseStart_34712 := by decide
  rcases family_descends (prefixWord ++ tailWord_34712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34716 : List Nat := [2, 2, 3, 3, 1, 1, 3, 4]
def baseStart_34716 : Nat := 118140960795 + 34716 * 2 ^ 59
def prefixEnd_34716 : Nat := 4983230072969 + 3 ^ 40 * 34716 * 2
def baseEnd_34716 : Nat := 10563552237980093149837

theorem tailTrace_34716 : CollatzResearch.WordTrace tailWord_34716 prefixEnd_34716 10563552237980093149837 := by
  unfold tailWord_34716
  simp only [CollatzResearch.WordTrace]
  refine ⟨633098271118667932938001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 844131028158223910584001 633098271118667932938001)
  ·
    refine ⟨474823703339000949703501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 633098271118667932938001 474823703339000949703501)
    ·
      refine ⟨178058888752125356138813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 474823703339000949703501 178058888752125356138813)
      ·
        refine ⟨66772083282047008552055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 178058888752125356138813 66772083282047008552055)
        ·
          refine ⟨100158124923070512828083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66772083282047008552055 100158124923070512828083)
          ·
            refine ⟨150237187384605769242125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100158124923070512828083 150237187384605769242125)
            ·
              refine ⟨56338945269227163465797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 150237187384605769242125 56338945269227163465797)
              ·
                refine ⟨10563552237980093149837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56338945269227163465797 10563552237980093149837)
                ·
                  rfl

theorem cell19_34716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 3, 4].length) (baseStart_34716 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_34716 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_34716 prefixEnd_34716 := by exact prefixLift 34716
  have htrace : WordTrace (prefixWord ++ tailWord_34716) baseStart_34716 baseEnd_34716 := by
    simpa [prefixWord, tailWord_34716, baseEnd_34716] using wordTrace_append hprefix tailTrace_34716
  have hstable : (prefixWord ++ tailWord_34716).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34716).length < 2 ^ (prefixWord ++ tailWord_34716).sum := by decide
  have hdescent : baseEnd_34716 < baseStart_34716 := by decide
  rcases family_descends (prefixWord ++ tailWord_34716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34786 : List Nat := [3, 3, 3, 1, 3, 1, 2, 3]
def baseStart_34786 : Nat := 118140960795 + 34786 * 2 ^ 59
def prefixEnd_34786 : Nat := 4983230072969 + 3 ^ 40 * 34786 * 2
def baseEnd_34786 : Nat := 10584852176240671594091

theorem tailTrace_34786 : CollatzResearch.WordTrace tailWord_34786 prefixEnd_34786 10584852176240671594091 := by
  unfold tailWord_34786
  simp only [CollatzResearch.WordTrace]
  refine ⟨317187412995934455231053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 845833101322491880616141 317187412995934455231053)
  ·
    refine ⟨118945279873475420711645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 317187412995934455231053 118945279873475420711645)
    ·
      refine ⟨44604479952553282766867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118945279873475420711645 44604479952553282766867)
      ·
        refine ⟨66906719928829924150301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44604479952553282766867 66906719928829924150301)
        ·
          refine ⟨25090019973311221556363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66906719928829924150301 25090019973311221556363)
          ·
            refine ⟨37635029959966832334545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25090019973311221556363 37635029959966832334545)
            ·
              refine ⟨28226272469975124250909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37635029959966832334545 28226272469975124250909)
              ·
                refine ⟨10584852176240671594091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28226272469975124250909 10584852176240671594091)
                ·
                  rfl

theorem cell19_34786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 2, 3].length) (baseStart_34786 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_34786 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_34786 prefixEnd_34786 := by exact prefixLift 34786
  have htrace : WordTrace (prefixWord ++ tailWord_34786) baseStart_34786 baseEnd_34786 := by
    simpa [prefixWord, tailWord_34786, baseEnd_34786] using wordTrace_append hprefix tailTrace_34786
  have hstable : (prefixWord ++ tailWord_34786).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34786).length < 2 ^ (prefixWord ++ tailWord_34786).sum := by decide
  have hdescent : baseEnd_34786 < baseStart_34786 := by decide
  rcases family_descends (prefixWord ++ tailWord_34786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34794 : List Nat := [3, 1, 3, 1, 2, 1, 3, 5]
def baseStart_34794 : Nat := 118140960795 + 34794 * 2 ^ 59
def prefixEnd_34794 : Nat := 4983230072969 + 3 ^ 40 * 34794 * 2
def baseEnd_34794 : Nat := 10587286454899023416291

theorem tailTrace_34794 : CollatzResearch.WordTrace tailWord_34794 prefixEnd_34794 10587286454899023416291 := by
  unfold tailWord_34794
  simp only [CollatzResearch.WordTrace]
  refine ⟨317260358988688796803859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 846027623969836791476957 317260358988688796803859)
  ·
    refine ⟨475890538483033195205789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 317260358988688796803859 475890538483033195205789)
    ·
      refine ⟨178458951931137448202171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 475890538483033195205789 178458951931137448202171)
      ·
        refine ⟨267688427896706172303257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178458951931137448202171 267688427896706172303257)
        ·
          refine ⟨200766320922529629227443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 267688427896706172303257 200766320922529629227443)
          ·
            refine ⟨301149481383794443841165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 200766320922529629227443 301149481383794443841165)
            ·
              refine ⟨112931055518922916440437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 301149481383794443841165 112931055518922916440437)
              ·
                refine ⟨10587286454899023416291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 112931055518922916440437 10587286454899023416291)
                ·
                  rfl

theorem cell19_34794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 5].length) (baseStart_34794 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_34794 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_34794 prefixEnd_34794 := by exact prefixLift 34794
  have htrace : WordTrace (prefixWord ++ tailWord_34794) baseStart_34794 baseEnd_34794 := by
    simpa [prefixWord, tailWord_34794, baseEnd_34794] using wordTrace_append hprefix tailTrace_34794
  have hstable : (prefixWord ++ tailWord_34794).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34794).length < 2 ^ (prefixWord ++ tailWord_34794).sum := by decide
  have hdescent : baseEnd_34794 < baseStart_34794 := by decide
  rcases family_descends (prefixWord ++ tailWord_34794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34868 : List Nat := [2, 5, 1, 2, 2, 7]
def baseStart_34868 : Nat := 118140960795 + 34868 * 2 ^ 59
def prefixEnd_34868 : Nat := 4983230072969 + 3 ^ 40 * 34868 * 2
def baseEnd_34868 : Nat := 1178867059165419752405

theorem tailTrace_34868 : CollatzResearch.WordTrace tailWord_34868 prefixEnd_34868 1178867059165419752405 := by
  unfold tailWord_34868
  simp only [CollatzResearch.WordTrace]
  refine ⟨635870218843332912704629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 847826958457777216939505 635870218843332912704629)
  ·
    refine ⟨59612833016562460566059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 635870218843332912704629 59612833016562460566059)
    ·
      refine ⟨89419249524843690849089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59612833016562460566059 89419249524843690849089)
      ·
        refine ⟨67064437143632768136817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89419249524843690849089 67064437143632768136817)
        ·
          refine ⟨50298327857724576102613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67064437143632768136817 50298327857724576102613)
          ·
            refine ⟨1178867059165419752405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 50298327857724576102613 1178867059165419752405)
            ·
              rfl

theorem cell19_34868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 7].length) (baseStart_34868 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_34868 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_34868 prefixEnd_34868 := by exact prefixLift 34868
  have htrace : WordTrace (prefixWord ++ tailWord_34868) baseStart_34868 baseEnd_34868 := by
    simpa [prefixWord, tailWord_34868, baseEnd_34868] using wordTrace_append hprefix tailTrace_34868
  have hstable : (prefixWord ++ tailWord_34868).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34868).length < 2 ^ (prefixWord ++ tailWord_34868).sum := by decide
  have hdescent : baseEnd_34868 < baseStart_34868 := by decide
  rcases family_descends (prefixWord ++ tailWord_34868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34872 : List Nat := [2, 1, 2, 1, 13]
def baseStart_34872 : Nat := 118140960795 + 34872 * 2 ^ 59
def prefixEnd_34872 : Nat := 4983230072969 + 3 ^ 40 * 34872 * 2
def baseEnd_34872 : Nat := 393000765622887173435

theorem tailTrace_34872 : CollatzResearch.WordTrace tailWord_34872 prefixEnd_34872 393000765622887173435 := by
  unfold tailWord_34872
  simp only [CollatzResearch.WordTrace]
  refine ⟨635943164836087254277435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 847924219781449672369913 635943164836087254277435)
  ·
    refine ⟨953914747254130881416153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 635943164836087254277435 953914747254130881416153)
    ·
      refine ⟨715436060440598161062115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 953914747254130881416153 715436060440598161062115)
      ·
        refine ⟨1073154090660897241593173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 715436060440598161062115 1073154090660897241593173)
        ·
          refine ⟨393000765622887173435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 1073154090660897241593173 393000765622887173435)
          ·
            rfl

theorem cell19_34872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 13].length) (baseStart_34872 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_34872 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_34872 prefixEnd_34872 := by exact prefixLift 34872
  have htrace : WordTrace (prefixWord ++ tailWord_34872) baseStart_34872 baseEnd_34872 := by
    simpa [prefixWord, tailWord_34872, baseEnd_34872] using wordTrace_append hprefix tailTrace_34872
  have hstable : (prefixWord ++ tailWord_34872).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34872).length < 2 ^ (prefixWord ++ tailWord_34872).sum := by decide
  have hdescent : baseEnd_34872 < baseStart_34872 := by decide
  rcases family_descends (prefixWord ++ tailWord_34872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34902 : List Nat := [5, 2, 2, 1, 1, 2, 3, 3]
def baseStart_34902 : Nat := 118140960795 + 34902 * 2 ^ 59
def prefixEnd_34902 : Nat := 4983230072969 + 3 ^ 40 * 34902 * 2
def baseEnd_34902 : Nat := 10620149216786773015997

theorem tailTrace_34902 : CollatzResearch.WordTrace tailWord_34902 prefixEnd_34902 10620149216786773015997 := by
  unfold tailWord_34902
  simp only [CollatzResearch.WordTrace]
  refine ⟨79561282472718102009185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 848653679708993088097973 79561282472718102009185)
  ·
    refine ⟨59670961854538576506889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79561282472718102009185 59670961854538576506889)
    ·
      refine ⟨44753221390903932380167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59670961854538576506889 44753221390903932380167)
      ·
        refine ⟨67129832086355898570251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44753221390903932380167 67129832086355898570251)
        ·
          refine ⟨100694748129533847855377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67129832086355898570251 100694748129533847855377)
          ·
            refine ⟨75521061097150385891533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100694748129533847855377 75521061097150385891533)
            ·
              refine ⟨28320397911431394709325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75521061097150385891533 28320397911431394709325)
              ·
                refine ⟨10620149216786773015997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28320397911431394709325 10620149216786773015997)
                ·
                  rfl

theorem cell19_34902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 3, 3].length) (baseStart_34902 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_34902 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_34902 prefixEnd_34902 := by exact prefixLift 34902
  have htrace : WordTrace (prefixWord ++ tailWord_34902) baseStart_34902 baseEnd_34902 := by
    simpa [prefixWord, tailWord_34902, baseEnd_34902] using wordTrace_append hprefix tailTrace_34902
  have hstable : (prefixWord ++ tailWord_34902).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34902).length < 2 ^ (prefixWord ++ tailWord_34902).sum := by decide
  have hdescent : baseEnd_34902 < baseStart_34902 := by decide
  rcases family_descends (prefixWord ++ tailWord_34902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34929 : List Nat := [1, 2, 2, 2, 1, 1, 10]
def baseStart_34929 : Nat := 118140960795 + 34929 * 2 ^ 59
def prefixEnd_34929 : Nat := 4983230072969 + 3 ^ 40 * 34929 * 2
def baseEnd_34929 : Nat := 3542788302419570138641

theorem tailTrace_34929 : CollatzResearch.WordTrace tailWord_34929 prefixEnd_34929 3542788302419570138641 := by
  unfold tailWord_34929
  simp only [CollatzResearch.WordTrace]
  refine ⟨1273965290465673243379841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 849310193643782162253227 1273965290465673243379841)
  ·
    refine ⟨955473967849254932534881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1273965290465673243379841 955473967849254932534881)
    ·
      refine ⟨716605475886941199401161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 955473967849254932534881 716605475886941199401161)
      ·
        refine ⟨537454106915205899550871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 716605475886941199401161 537454106915205899550871)
        ·
          refine ⟨806181160372808849326307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 537454106915205899550871 806181160372808849326307)
          ·
            refine ⟨1209271740559213273989461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 806181160372808849326307 1209271740559213273989461)
            ·
              refine ⟨3542788302419570138641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 1209271740559213273989461 3542788302419570138641)
              ·
                rfl

theorem cell19_34929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 10].length) (baseStart_34929 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_34929 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_34929 prefixEnd_34929 := by exact prefixLift 34929
  have htrace : WordTrace (prefixWord ++ tailWord_34929) baseStart_34929 baseEnd_34929 := by
    simpa [prefixWord, tailWord_34929, baseEnd_34929] using wordTrace_append hprefix tailTrace_34929
  have hstable : (prefixWord ++ tailWord_34929).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34929).length < 2 ^ (prefixWord ++ tailWord_34929).sum := by decide
  have hdescent : baseEnd_34929 < baseStart_34929 := by decide
  rcases family_descends (prefixWord ++ tailWord_34929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35022 : List Nat := [4, 1, 1, 1, 4, 1, 2, 5]
def baseStart_35022 : Nat := 118140960795 + 35022 * 2 ^ 59
def prefixEnd_35022 : Nat := 4983230072969 + 3 ^ 40 * 35022 * 2
def baseEnd_35022 : Nat := 10656663396662050349003

theorem tailTrace_35022 : CollatzResearch.WordTrace tailWord_35022 prefixEnd_35022 10656663396662050349003 := by
  unfold tailWord_35022
  simp only [CollatzResearch.WordTrace]
  refine ⟨159669659891093765814415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 851571519419166751010213 159669659891093765814415)
  ·
    refine ⟨239504489836640648721623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159669659891093765814415 239504489836640648721623)
    ·
      refine ⟨359256734754960973082435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239504489836640648721623 359256734754960973082435)
      ·
        refine ⟨538885102132441459623653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 359256734754960973082435 538885102132441459623653)
        ·
          refine ⟨101040956649832773679435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 538885102132441459623653 101040956649832773679435)
          ·
            refine ⟨151561434974749160519153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101040956649832773679435 151561434974749160519153)
            ·
              refine ⟨113671076231061870389365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 151561434974749160519153 113671076231061870389365)
              ·
                refine ⟨10656663396662050349003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 113671076231061870389365 10656663396662050349003)
                ·
                  rfl

theorem cell19_35022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 5].length) (baseStart_35022 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_35022 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_35022 prefixEnd_35022 := by exact prefixLift 35022
  have htrace : WordTrace (prefixWord ++ tailWord_35022) baseStart_35022 baseEnd_35022 := by
    simpa [prefixWord, tailWord_35022, baseEnd_35022] using wordTrace_append hprefix tailTrace_35022
  have hstable : (prefixWord ++ tailWord_35022).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35022).length < 2 ^ (prefixWord ++ tailWord_35022).sum := by decide
  have hdescent : baseEnd_35022 < baseStart_35022 := by decide
  rcases family_descends (prefixWord ++ tailWord_35022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35058 : List Nat := [3, 2, 1, 3, 2, 3, 1, 4]
def baseStart_35058 : Nat := 118140960795 + 35058 * 2 ^ 59
def prefixEnd_35058 : Nat := 4983230072969 + 3 ^ 40 * 35058 * 2
def baseEnd_35058 : Nat := 10667617650624633548905

theorem tailTrace_35058 : CollatzResearch.WordTrace tailWord_35058 prefixEnd_35058 10667617650624633548905 := by
  unfold tailWord_35058
  simp only [CollatzResearch.WordTrace]
  refine ⟨319667576749582068706457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 852446871332218849883885 319667576749582068706457)
  ·
    refine ⟨239750682562186551529843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 319667576749582068706457 239750682562186551529843)
    ·
      refine ⟨359626023843279827294765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239750682562186551529843 359626023843279827294765)
      ·
        refine ⟨134859758941229935235537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 359626023843279827294765 134859758941229935235537)
        ·
          refine ⟨101144819205922451426653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134859758941229935235537 101144819205922451426653)
          ·
            refine ⟨37929307202220919284995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 101144819205922451426653 37929307202220919284995)
            ·
              refine ⟨56893960803331378927493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37929307202220919284995 56893960803331378927493)
              ·
                refine ⟨10667617650624633548905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56893960803331378927493 10667617650624633548905)
                ·
                  rfl

theorem cell19_35058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 1, 4].length) (baseStart_35058 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_35058 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_35058 prefixEnd_35058 := by exact prefixLift 35058
  have htrace : WordTrace (prefixWord ++ tailWord_35058) baseStart_35058 baseEnd_35058 := by
    simpa [prefixWord, tailWord_35058, baseEnd_35058] using wordTrace_append hprefix tailTrace_35058
  have hstable : (prefixWord ++ tailWord_35058).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35058).length < 2 ^ (prefixWord ++ tailWord_35058).sum := by decide
  have hdescent : baseEnd_35058 < baseStart_35058 := by decide
  rcases family_descends (prefixWord ++ tailWord_35058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35098 : List Nat := [3, 1, 1, 3, 4, 1, 6]
def baseStart_35098 : Nat := 118140960795 + 35098 * 2 ^ 59
def prefixEnd_35098 : Nat := 4983230072969 + 3 ^ 40 * 35098 * 2
def baseEnd_35098 : Nat := 3559929681305464219969

theorem tailTrace_35098 : CollatzResearch.WordTrace tailWord_35098 prefixEnd_35098 3559929681305464219969 := by
  unfold tailWord_35098
  simp only [CollatzResearch.WordTrace]
  refine ⟨320032306713353776570487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 853419484568943404187965 320032306713353776570487)
  ·
    refine ⟨480048460070030664855731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 320032306713353776570487 480048460070030664855731)
    ·
      refine ⟨720072690105045997283597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 480048460070030664855731 720072690105045997283597)
      ·
        refine ⟨270027258789392248981349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 720072690105045997283597 270027258789392248981349)
        ·
          refine ⟨50630111023011046684003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 270027258789392248981349 50630111023011046684003)
          ·
            refine ⟨75945166534516570026005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50630111023011046684003 75945166534516570026005)
            ·
              refine ⟨3559929681305464219969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 75945166534516570026005 3559929681305464219969)
              ·
                rfl

theorem cell19_35098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 6].length) (baseStart_35098 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_35098 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_35098 prefixEnd_35098 := by exact prefixLift 35098
  have htrace : WordTrace (prefixWord ++ tailWord_35098) baseStart_35098 baseEnd_35098 := by
    simpa [prefixWord, tailWord_35098, baseEnd_35098] using wordTrace_append hprefix tailTrace_35098
  have hstable : (prefixWord ++ tailWord_35098).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35098).length < 2 ^ (prefixWord ++ tailWord_35098).sum := by decide
  have hdescent : baseEnd_35098 < baseStart_35098 := by decide
  rcases family_descends (prefixWord ++ tailWord_35098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35134 : List Nat := [4, 2, 1, 2, 1, 2, 4, 3]
def baseStart_35134 : Nat := 118140960795 + 35134 * 2 ^ 59
def prefixEnd_35134 : Nat := 4983230072969 + 3 ^ 40 * 35134 * 2
def baseEnd_35134 : Nat := 10690743297878975859809

theorem tailTrace_35134 : CollatzResearch.WordTrace tailWord_35134 prefixEnd_35134 10690743297878975859809 := by
  unfold tailWord_35134
  simp only [CollatzResearch.WordTrace]
  refine ⟨160180281840374156824057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 854294836481995503061637 160180281840374156824057)
  ·
    refine ⟨120135211380280617618043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160180281840374156824057 120135211380280617618043)
    ·
      refine ⟨180202817070420926427065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120135211380280617618043 180202817070420926427065)
      ·
        refine ⟨135152112802815694820299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 180202817070420926427065 135152112802815694820299)
        ·
          refine ⟨202728169204223542230449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135152112802815694820299 202728169204223542230449)
          ·
            refine ⟨152046126903167656672837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 202728169204223542230449 152046126903167656672837)
            ·
              refine ⟨28508648794343935626157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 152046126903167656672837 28508648794343935626157)
              ·
                refine ⟨10690743297878975859809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28508648794343935626157 10690743297878975859809)
                ·
                  rfl

theorem cell19_35134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 4, 3].length) (baseStart_35134 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_35134 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_35134 prefixEnd_35134 := by exact prefixLift 35134
  have htrace : WordTrace (prefixWord ++ tailWord_35134) baseStart_35134 baseEnd_35134 := by
    simpa [prefixWord, tailWord_35134, baseEnd_35134] using wordTrace_append hprefix tailTrace_35134
  have hstable : (prefixWord ++ tailWord_35134).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35134).length < 2 ^ (prefixWord ++ tailWord_35134).sum := by decide
  have hdescent : baseEnd_35134 < baseStart_35134 := by decide
  rcases family_descends (prefixWord ++ tailWord_35134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35166 : List Nat := [4, 4, 2, 1, 1, 1, 2, 4]
def baseStart_35166 : Nat := 118140960795 + 35166 * 2 ^ 59
def prefixEnd_35166 : Nat := 4983230072969 + 3 ^ 40 * 35166 * 2
def baseEnd_35166 : Nat := 10700480412512383148611

theorem tailTrace_35166 : CollatzResearch.WordTrace tailWord_35166 prefixEnd_35166 10700480412512383148611 := by
  unfold tailWord_35166
  simp only [CollatzResearch.WordTrace]
  refine ⟨160326173825882839969669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 855072927071375146504901 160326173825882839969669)
  ·
    refine ⟨30061157592353032494313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 160326173825882839969669 30061157592353032494313)
    ·
      refine ⟨22545868194264774370735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30061157592353032494313 22545868194264774370735)
      ·
        refine ⟨33818802291397161556103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22545868194264774370735 33818802291397161556103)
        ·
          refine ⟨50728203437095742334155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33818802291397161556103 50728203437095742334155)
          ·
            refine ⟨76092305155643613501233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50728203437095742334155 76092305155643613501233)
            ·
              refine ⟨57069228866732710125925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76092305155643613501233 57069228866732710125925)
              ·
                refine ⟨10700480412512383148611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57069228866732710125925 10700480412512383148611)
                ·
                  rfl

theorem cell19_35166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 2, 4].length) (baseStart_35166 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_35166 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_35166 prefixEnd_35166 := by exact prefixLift 35166
  have htrace : WordTrace (prefixWord ++ tailWord_35166) baseStart_35166 baseEnd_35166 := by
    simpa [prefixWord, tailWord_35166, baseEnd_35166] using wordTrace_append hprefix tailTrace_35166
  have hstable : (prefixWord ++ tailWord_35166).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35166).length < 2 ^ (prefixWord ++ tailWord_35166).sum := by decide
  have hdescent : baseEnd_35166 < baseStart_35166 := by decide
  rcases family_descends (prefixWord ++ tailWord_35166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35195 : List Nat := [1, 1, 1, 1, 1, 7, 2, 5]
def baseStart_35195 : Nat := 118140960795 + 35195 * 2 ^ 59
def prefixEnd_35195 : Nat := 4983230072969 + 3 ^ 40 * 35195 * 2
def baseEnd_35195 : Nat := 10709304672648908504087

theorem tailTrace_35195 : CollatzResearch.WordTrace tailWord_35195 prefixEnd_35195 10709304672648908504087 := by
  unfold tailWord_35195
  simp only [CollatzResearch.WordTrace]
  refine ⟨1283667107502000672563039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 855778071668000448375359 1283667107502000672563039)
  ·
    refine ⟨1925500661253001008844559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1283667107502000672563039 1925500661253001008844559)
    ·
      refine ⟨2888250991879501513266839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1925500661253001008844559 2888250991879501513266839)
      ·
        refine ⟨4332376487819252269900259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2888250991879501513266839 4332376487819252269900259)
        ·
          refine ⟨6498564731728878404850389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4332376487819252269900259 6498564731728878404850389)
          ·
            refine ⟨152310110899895587613681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 6498564731728878404850389 152310110899895587613681)
            ·
              refine ⟨114232583174921690710261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 152310110899895587613681 114232583174921690710261)
              ·
                refine ⟨10709304672648908504087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 114232583174921690710261 10709304672648908504087)
                ·
                  rfl

theorem cell19_35195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 5].length) (baseStart_35195 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_35195 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_35195 prefixEnd_35195 := by exact prefixLift 35195
  have htrace : WordTrace (prefixWord ++ tailWord_35195) baseStart_35195 baseEnd_35195 := by
    simpa [prefixWord, tailWord_35195, baseEnd_35195] using wordTrace_append hprefix tailTrace_35195
  have hstable : (prefixWord ++ tailWord_35195).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35195).length < 2 ^ (prefixWord ++ tailWord_35195).sum := by decide
  have hdescent : baseEnd_35195 < baseStart_35195 := by decide
  rcases family_descends (prefixWord ++ tailWord_35195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35210 : List Nat := [3, 1, 2, 5, 2, 6]
def baseStart_35210 : Nat := 118140960795 + 35210 * 2 ^ 59
def prefixEnd_35210 : Nat := 4983230072969 + 3 ^ 40 * 35210 * 2
def baseEnd_35210 : Nat := 1190429882792590907857

theorem tailTrace_35210 : CollatzResearch.WordTrace tailWord_35210 prefixEnd_35210 1190429882792590907857 := by
  unfold tailWord_35210
  simp only [CollatzResearch.WordTrace]
  refine ⟨321053550611914558589771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 856142801631772156239389 321053550611914558589771)
  ·
    refine ⟨481580325917871837884657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 321053550611914558589771 481580325917871837884657)
    ·
      refine ⟨361185244438403878413493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 481580325917871837884657 361185244438403878413493)
      ·
        refine ⟨33861116666100363601265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 361185244438403878413493 33861116666100363601265)
        ·
          refine ⟨25395837499575272700949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33861116666100363601265 25395837499575272700949)
          ·
            refine ⟨1190429882792590907857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 25395837499575272700949 1190429882792590907857)
            ·
              rfl

theorem cell19_35210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 6].length) (baseStart_35210 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_35210 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_35210 prefixEnd_35210 := by exact prefixLift 35210
  have htrace : WordTrace (prefixWord ++ tailWord_35210) baseStart_35210 baseEnd_35210 := by
    simpa [prefixWord, tailWord_35210, baseEnd_35210] using wordTrace_append hprefix tailTrace_35210
  have hstable : (prefixWord ++ tailWord_35210).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35210).length < 2 ^ (prefixWord ++ tailWord_35210).sum := by decide
  have hdescent : baseEnd_35210 < baseStart_35210 := by decide
  rcases family_descends (prefixWord ++ tailWord_35210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35229 : List Nat := [1, 4, 2, 1, 4, 2, 1, 4]
def baseStart_35229 : Nat := 118140960795 + 35229 * 2 ^ 59
def prefixEnd_35229 : Nat := 4983230072969 + 3 ^ 40 * 35229 * 2
def baseEnd_35229 : Nat := 10719650356946903748439

theorem tailTrace_35229 : CollatzResearch.WordTrace tailWord_35229 prefixEnd_35229 10719650356946903748439 := by
  unfold tailWord_35229
  simp only [CollatzResearch.WordTrace]
  refine ⟨1284907189378824479300741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 856604792919216319533827 1284907189378824479300741)
  ·
    refine ⟨240920098008529589868889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1284907189378824479300741 240920098008529589868889)
    ·
      refine ⟨180690073506397192401667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 240920098008529589868889 180690073506397192401667)
      ·
        refine ⟨271035110259595788602501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180690073506397192401667 271035110259595788602501)
        ·
          refine ⟨50819083173674210362969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 271035110259595788602501 50819083173674210362969)
          ·
            refine ⟨38114312380255657772227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50819083173674210362969 38114312380255657772227)
            ·
              refine ⟨57171468570383486658341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38114312380255657772227 57171468570383486658341)
              ·
                refine ⟨10719650356946903748439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57171468570383486658341 10719650356946903748439)
                ·
                  rfl

theorem cell19_35229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 1, 4].length) (baseStart_35229 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_35229 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_35229 prefixEnd_35229 := by exact prefixLift 35229
  have htrace : WordTrace (prefixWord ++ tailWord_35229) baseStart_35229 baseEnd_35229 := by
    simpa [prefixWord, tailWord_35229, baseEnd_35229] using wordTrace_append hprefix tailTrace_35229
  have hstable : (prefixWord ++ tailWord_35229).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35229).length < 2 ^ (prefixWord ++ tailWord_35229).sum := by decide
  have hdescent : baseEnd_35229 < baseStart_35229 := by decide
  rcases family_descends (prefixWord ++ tailWord_35229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35250 : List Nat := [3, 2, 1, 1, 1, 1, 7, 3]
def baseStart_35250 : Nat := 118140960795 + 35250 * 2 ^ 59
def prefixEnd_35250 : Nat := 4983230072969 + 3 ^ 40 * 35250 * 2
def baseEnd_35250 : Nat := 10726040338425077281715

theorem tailTrace_35250 : CollatzResearch.WordTrace tailWord_35250 prefixEnd_35250 10726040338425077281715 := by
  unfold tailWord_35250
  simp only [CollatzResearch.WordTrace]
  refine ⟨321418280575686266453801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 857115414868496710543469 321418280575686266453801)
  ·
    refine ⟨241063710431764699840351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 321418280575686266453801 241063710431764699840351)
    ·
      refine ⟨361595565647647049760527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241063710431764699840351 361595565647647049760527)
      ·
        refine ⟨542393348471470574640791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 361595565647647049760527 542393348471470574640791)
        ·
          refine ⟨813590022707205861961187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 542393348471470574640791 813590022707205861961187)
          ·
            refine ⟨1220385034060808792941781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 813590022707205861961187 1220385034060808792941781)
            ·
              refine ⟨28602774235800206084573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1220385034060808792941781 28602774235800206084573)
              ·
                refine ⟨10726040338425077281715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28602774235800206084573 10726040338425077281715)
                ·
                  rfl

theorem cell19_35250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 7, 3].length) (baseStart_35250 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_35250 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_35250 prefixEnd_35250 := by exact prefixLift 35250
  have htrace : WordTrace (prefixWord ++ tailWord_35250) baseStart_35250 baseEnd_35250 := by
    simpa [prefixWord, tailWord_35250, baseEnd_35250] using wordTrace_append hprefix tailTrace_35250
  have hstable : (prefixWord ++ tailWord_35250).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35250).length < 2 ^ (prefixWord ++ tailWord_35250).sum := by decide
  have hdescent : baseEnd_35250 < baseStart_35250 := by decide
  rcases family_descends (prefixWord ++ tailWord_35250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35265 : List Nat := [1, 2, 7, 1, 1, 1, 6]
def baseStart_35265 : Nat := 118140960795 + 35265 * 2 ^ 59
def prefixEnd_35265 : Nat := 4983230072969 + 3 ^ 40 * 35265 * 2
def baseEnd_35265 : Nat := 3576868203636495649447

theorem tailTrace_35265 : CollatzResearch.WordTrace tailWord_35265 prefixEnd_35265 3576868203636495649447 := by
  unfold tailWord_35265
  simp only [CollatzResearch.WordTrace]
  refine ⟨1286220217248402627611249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 857480144832268418407499 1286220217248402627611249)
  ·
    refine ⟨964665162936301970708437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1286220217248402627611249 964665162936301970708437)
    ·
      refine ⟨22609339756319577438479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 964665162936301970708437 22609339756319577438479)
      ·
        refine ⟨33914009634479366157719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22609339756319577438479 33914009634479366157719)
        ·
          refine ⟨50871014451719049236579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33914009634479366157719 50871014451719049236579)
          ·
            refine ⟨76306521677578573854869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50871014451719049236579 76306521677578573854869)
            ·
              refine ⟨3576868203636495649447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 76306521677578573854869 3576868203636495649447)
              ·
                rfl

theorem cell19_35265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 6].length) (baseStart_35265 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_35265 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_35265 prefixEnd_35265 := by exact prefixLift 35265
  have htrace : WordTrace (prefixWord ++ tailWord_35265) baseStart_35265 baseEnd_35265 := by
    simpa [prefixWord, tailWord_35265, baseEnd_35265] using wordTrace_append hprefix tailTrace_35265
  have hstable : (prefixWord ++ tailWord_35265).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35265).length < 2 ^ (prefixWord ++ tailWord_35265).sum := by decide
  have hdescent : baseEnd_35265 < baseStart_35265 := by decide
  rcases family_descends (prefixWord ++ tailWord_35265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35271 : List Nat := [1, 1, 4, 1, 1, 5, 6]
def baseStart_35271 : Nat := 118140960795 + 35271 * 2 ^ 59
def prefixEnd_35271 : Nat := 4983230072969 + 3 ^ 40 * 35271 * 2
def baseEnd_35271 : Nat := 3577476773301083604997

theorem tailTrace_35271 : CollatzResearch.WordTrace tailWord_35271 prefixEnd_35271 3577476773301083604997 := by
  unfold tailWord_35271
  simp only [CollatzResearch.WordTrace]
  refine ⟨1286439055226665652329667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 857626036817777101553111 1286439055226665652329667)
  ·
    refine ⟨1929658582839998478494501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1286439055226665652329667 1929658582839998478494501)
    ·
      refine ⟨361810984282499714717719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1929658582839998478494501 361810984282499714717719)
      ·
        refine ⟨542716476423749572076579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 361810984282499714717719 542716476423749572076579)
        ·
          refine ⟨814074714635624358114869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 542716476423749572076579 814074714635624358114869)
          ·
            refine ⟨76319504497089783573269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 814074714635624358114869 76319504497089783573269)
            ·
              refine ⟨3577476773301083604997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 76319504497089783573269 3577476773301083604997)
              ·
                rfl

theorem cell19_35271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 6].length) (baseStart_35271 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_35271 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_35271 prefixEnd_35271 := by exact prefixLift 35271
  have htrace : WordTrace (prefixWord ++ tailWord_35271) baseStart_35271 baseEnd_35271 := by
    simpa [prefixWord, tailWord_35271, baseEnd_35271] using wordTrace_append hprefix tailTrace_35271
  have hstable : (prefixWord ++ tailWord_35271).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35271).length < 2 ^ (prefixWord ++ tailWord_35271).sum := by decide
  have hdescent : baseEnd_35271 < baseStart_35271 := by decide
  rcases family_descends (prefixWord ++ tailWord_35271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35290 : List Nat := [3, 1, 1, 2, 3, 1, 2, 6]
def baseStart_35290 : Nat := 118140960795 + 35290 * 2 ^ 59
def prefixEnd_35290 : Nat := 4983230072969 + 3 ^ 40 * 35290 * 2
def baseEnd_35290 : Nat := 10738211731716836392717

theorem tailTrace_35290 : CollatzResearch.WordTrace tailWord_35290 prefixEnd_35290 10738211731716836392717 := by
  unfold tailWord_35290
  simp only [CollatzResearch.WordTrace]
  refine ⟨321783010539457974317831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 858088028105221264847549 321783010539457974317831)
  ·
    refine ⟨482674515809186961476747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 321783010539457974317831 482674515809186961476747)
    ·
      refine ⟨724011773713780442215121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 482674515809186961476747 724011773713780442215121)
      ·
        refine ⟨543008830285335331661341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 724011773713780442215121 543008830285335331661341)
        ·
          refine ⟨203628311357000749373003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 543008830285335331661341 203628311357000749373003)
          ·
            refine ⟨305442467035501124059505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203628311357000749373003 305442467035501124059505)
            ·
              refine ⟨229081850276625843044629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 305442467035501124059505 229081850276625843044629)
              ·
                refine ⟨10738211731716836392717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 229081850276625843044629 10738211731716836392717)
                ·
                  rfl

theorem cell19_35290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 6].length) (baseStart_35290 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_35290 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_35290 prefixEnd_35290 := by exact prefixLift 35290
  have htrace : WordTrace (prefixWord ++ tailWord_35290) baseStart_35290 baseEnd_35290 := by
    simpa [prefixWord, tailWord_35290, baseEnd_35290] using wordTrace_append hprefix tailTrace_35290
  have hstable : (prefixWord ++ tailWord_35290).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35290).length < 2 ^ (prefixWord ++ tailWord_35290).sum := by decide
  have hdescent : baseEnd_35290 < baseStart_35290 := by decide
  rcases family_descends (prefixWord ++ tailWord_35290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35341 : List Nat := [1, 7, 1, 1, 1, 2, 2, 4]
def baseStart_35341 : Nat := 118140960795 + 35341 * 2 ^ 59
def prefixEnd_35341 : Nat := 4983230072969 + 3 ^ 40 * 35341 * 2
def baseEnd_35341 : Nat := 10753730258163829259245

theorem tailTrace_35341 : CollatzResearch.WordTrace tailWord_35341 prefixEnd_35341 10753730258163829259245 := by
  unfold tailWord_35341
  simp only [CollatzResearch.WordTrace]
  refine ⟨1288992164973067607377877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 859328109982045071585251 1288992164973067607377877)
  ·
    refine ⟨30210753866556272047919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 1288992164973067607377877 30210753866556272047919)
    ·
      refine ⟨45316130799834408071879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30210753866556272047919 45316130799834408071879)
      ·
        refine ⟨67974196199751612107819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45316130799834408071879 67974196199751612107819)
        ·
          refine ⟨101961294299627418161729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67974196199751612107819 101961294299627418161729)
          ·
            refine ⟨76470970724720563621297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101961294299627418161729 76470970724720563621297)
            ·
              refine ⟨57353228043540422715973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76470970724720563621297 57353228043540422715973)
              ·
                refine ⟨10753730258163829259245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57353228043540422715973 10753730258163829259245)
                ·
                  rfl

theorem cell19_35341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 2, 4].length) (baseStart_35341 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_35341 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_35341 prefixEnd_35341 := by exact prefixLift 35341
  have htrace : WordTrace (prefixWord ++ tailWord_35341) baseStart_35341 baseEnd_35341 := by
    simpa [prefixWord, tailWord_35341, baseEnd_35341] using wordTrace_append hprefix tailTrace_35341
  have hstable : (prefixWord ++ tailWord_35341).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35341).length < 2 ^ (prefixWord ++ tailWord_35341).sum := by decide
  have hdescent : baseEnd_35341 < baseStart_35341 := by decide
  rcases family_descends (prefixWord ++ tailWord_35341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35347 : List Nat := [1, 1, 1, 2, 1, 5, 4, 4]
def baseStart_35347 : Nat := 118140960795 + 35347 * 2 ^ 59
def prefixEnd_35347 : Nat := 4983230072969 + 3 ^ 40 * 35347 * 2
def baseEnd_35347 : Nat := 10755555967157593125895

theorem tailTrace_35347 : CollatzResearch.WordTrace tailWord_35347 prefixEnd_35347 10755555967157593125895 := by
  unfold tailWord_35347
  simp only [CollatzResearch.WordTrace]
  refine ⟨1289211002951330632096295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 859474001967553754730863 1289211002951330632096295)
  ·
    refine ⟨1933816504426995948144443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1289211002951330632096295 1933816504426995948144443)
    ·
      refine ⟨2900724756640493922216665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1933816504426995948144443 2900724756640493922216665)
      ·
        refine ⟨2175543567480370441662499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2900724756640493922216665 2175543567480370441662499)
        ·
          refine ⟨3263315351220555662493749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2175543567480370441662499 3263315351220555662493749)
          ·
            refine ⟨305935814176927093358789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3263315351220555662493749 305935814176927093358789)
            ·
              refine ⟨57362965158173830004773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 305935814176927093358789 57362965158173830004773)
              ·
                refine ⟨10755555967157593125895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57362965158173830004773 10755555967157593125895)
                ·
                  rfl

theorem cell19_35347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 4, 4].length) (baseStart_35347 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_35347 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_35347 prefixEnd_35347 := by exact prefixLift 35347
  have htrace : WordTrace (prefixWord ++ tailWord_35347) baseStart_35347 baseEnd_35347 := by
    simpa [prefixWord, tailWord_35347, baseEnd_35347] using wordTrace_append hprefix tailTrace_35347
  have hstable : (prefixWord ++ tailWord_35347).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35347).length < 2 ^ (prefixWord ++ tailWord_35347).sum := by decide
  have hdescent : baseEnd_35347 < baseStart_35347 := by decide
  rcases family_descends (prefixWord ++ tailWord_35347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35396 : List Nat := [2, 3, 5, 1, 1, 2, 1, 4]
def baseStart_35396 : Nat := 118140960795 + 35396 * 2 ^ 59
def prefixEnd_35396 : Nat := 4983230072969 + 3 ^ 40 * 35396 * 2
def baseEnd_35396 : Nat := 10770465923939998036873

theorem tailTrace_35396 : CollatzResearch.WordTrace tailWord_35396 prefixEnd_35396 10770465923939998036873 := by
  unfold tailWord_35396
  simp only [CollatzResearch.WordTrace]
  refine ⟨645499089886906000315021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 860665453182541333753361 645499089886906000315021)
  ·
    refine ⟨242062158707589750118133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 645499089886906000315021 242062158707589750118133)
    ·
      refine ⟨22693327378836539073575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 242062158707589750118133 22693327378836539073575)
      ·
        refine ⟨34039991068254808610363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22693327378836539073575 34039991068254808610363)
        ·
          refine ⟨51059986602382212915545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34039991068254808610363 51059986602382212915545)
          ·
            refine ⟨38294989951786659686659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51059986602382212915545 38294989951786659686659)
            ·
              refine ⟨57442484927679989529989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38294989951786659686659 57442484927679989529989)
              ·
                refine ⟨10770465923939998036873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57442484927679989529989 10770465923939998036873)
                ·
                  rfl

theorem cell19_35396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 1, 4].length) (baseStart_35396 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_35396 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_35396 prefixEnd_35396 := by exact prefixLift 35396
  have htrace : WordTrace (prefixWord ++ tailWord_35396) baseStart_35396 baseEnd_35396 := by
    simpa [prefixWord, tailWord_35396, baseEnd_35396] using wordTrace_append hprefix tailTrace_35396
  have hstable : (prefixWord ++ tailWord_35396).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35396).length < 2 ^ (prefixWord ++ tailWord_35396).sum := by decide
  have hdescent : baseEnd_35396 < baseStart_35396 := by decide
  rcases family_descends (prefixWord ++ tailWord_35396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35398 : List Nat := [6, 1, 1, 1, 2, 3, 1, 4]
def baseStart_35398 : Nat := 118140960795 + 35398 * 2 ^ 59
def prefixEnd_35398 : Nat := 4983230072969 + 3 ^ 40 * 35398 * 2
def baseEnd_35398 : Nat := 10771074493604585992423

theorem tailTrace_35398 : CollatzResearch.WordTrace tailWord_35398 prefixEnd_35398 10771074493604585992423 := by
  unfold tailWord_35398
  simp only [CollatzResearch.WordTrace]
  refine ⟨40345972680205198193839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 860714083844377561468565 40345972680205198193839)
  ·
    refine ⟨60518959020307797290759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40345972680205198193839 60518959020307797290759)
    ·
      refine ⟨90778438530461695936139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60518959020307797290759 90778438530461695936139)
      ·
        refine ⟨136167657795692543904209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90778438530461695936139 136167657795692543904209)
        ·
          refine ⟨102125743346769407928157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136167657795692543904209 102125743346769407928157)
          ·
            refine ⟨38297153755038527973059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 102125743346769407928157 38297153755038527973059)
            ·
              refine ⟨57445730632557791959589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38297153755038527973059 57445730632557791959589)
              ·
                refine ⟨10771074493604585992423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57445730632557791959589 10771074493604585992423)
                ·
                  rfl

theorem cell19_35398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_35398 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_35398 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_35398 prefixEnd_35398 := by exact prefixLift 35398
  have htrace : WordTrace (prefixWord ++ tailWord_35398) baseStart_35398 baseEnd_35398 := by
    simpa [prefixWord, tailWord_35398, baseEnd_35398] using wordTrace_append hprefix tailTrace_35398
  have hstable : (prefixWord ++ tailWord_35398).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35398).length < 2 ^ (prefixWord ++ tailWord_35398).sum := by decide
  have hdescent : baseEnd_35398 < baseStart_35398 := by decide
  rcases family_descends (prefixWord ++ tailWord_35398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35402 : List Nat := [3, 1, 2, 1, 1, 6, 1, 4]
def baseStart_35402 : Nat := 118140960795 + 35402 * 2 ^ 59
def prefixEnd_35402 : Nat := 4983230072969 + 3 ^ 40 * 35402 * 2
def baseEnd_35402 : Nat := 10772291632933761903523

theorem tailTrace_35402 : CollatzResearch.WordTrace tailWord_35402 prefixEnd_35402 10772291632933761903523 := by
  unfold tailWord_35402
  simp only [CollatzResearch.WordTrace]
  refine ⟨322804254438018756337115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 860811345168050016898973 322804254438018756337115)
  ·
    refine ⟨484206381657028134505673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 322804254438018756337115 484206381657028134505673)
    ·
      refine ⟨363154786242771100879255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 484206381657028134505673 363154786242771100879255)
      ·
        refine ⟨544732179364156651318883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 363154786242771100879255 544732179364156651318883)
        ·
          refine ⟨817098269046234976978325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 544732179364156651318883 817098269046234976978325)
          ·
            refine ⟨38301481361542264545859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 817098269046234976978325 38301481361542264545859)
            ·
              refine ⟨57452222042313396818789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38301481361542264545859 57452222042313396818789)
              ·
                refine ⟨10772291632933761903523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57452222042313396818789 10772291632933761903523)
                ·
                  rfl

theorem cell19_35402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 1, 4].length) (baseStart_35402 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_35402 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_35402 prefixEnd_35402 := by exact prefixLift 35402
  have htrace : WordTrace (prefixWord ++ tailWord_35402) baseStart_35402 baseEnd_35402 := by
    simpa [prefixWord, tailWord_35402, baseEnd_35402] using wordTrace_append hprefix tailTrace_35402
  have hstable : (prefixWord ++ tailWord_35402).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35402).length < 2 ^ (prefixWord ++ tailWord_35402).sum := by decide
  have hdescent : baseEnd_35402 < baseStart_35402 := by decide
  rcases family_descends (prefixWord ++ tailWord_35402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35476 : List Nat := [2, 4, 2, 2, 1, 1, 4, 3]
def baseStart_35476 : Nat := 118140960795 + 35476 * 2 ^ 59
def prefixEnd_35476 : Nat := 4983230072969 + 3 ^ 40 * 35476 * 2
def baseEnd_35476 : Nat := 10794808710523516258877

theorem tailTrace_35476 : CollatzResearch.WordTrace tailWord_35476 prefixEnd_35476 10794808710523516258877 := by
  unfold tailWord_35476
  simp only [CollatzResearch.WordTrace]
  refine ⟨646958009741992831771141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 862610679655990442361521 646958009741992831771141)
  ·
    refine ⟨121304626826623655957089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 646958009741992831771141 121304626826623655957089)
    ·
      refine ⟨90978470119967741967817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121304626826623655957089 90978470119967741967817)
      ·
        refine ⟨68233852589975806475863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90978470119967741967817 68233852589975806475863)
        ·
          refine ⟨102350778884963709713795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68233852589975806475863 102350778884963709713795)
          ·
            refine ⟨153526168327445564570693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102350778884963709713795 153526168327445564570693)
            ·
              refine ⟨28786156561396043357005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 153526168327445564570693 28786156561396043357005)
              ·
                refine ⟨10794808710523516258877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28786156561396043357005 10794808710523516258877)
                ·
                  rfl

theorem cell19_35476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 4, 3].length) (baseStart_35476 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_35476 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_35476 prefixEnd_35476 := by exact prefixLift 35476
  have htrace : WordTrace (prefixWord ++ tailWord_35476) baseStart_35476 baseEnd_35476 := by
    simpa [prefixWord, tailWord_35476, baseEnd_35476] using wordTrace_append hprefix tailTrace_35476
  have hstable : (prefixWord ++ tailWord_35476).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35476).length < 2 ^ (prefixWord ++ tailWord_35476).sum := by decide
  have hdescent : baseEnd_35476 < baseStart_35476 := by decide
  rcases family_descends (prefixWord ++ tailWord_35476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35480 : List Nat := [2, 1, 2, 4, 1, 1, 3, 5]
def baseStart_35480 : Nat := 118140960795 + 35480 * 2 ^ 59
def prefixEnd_35480 : Nat := 4983230072969 + 3 ^ 40 * 35480 * 2
def baseEnd_35480 : Nat := 10796025849852692169977

theorem tailTrace_35480 : CollatzResearch.WordTrace tailWord_35480 prefixEnd_35480 10796025849852692169977 := by
  unfold tailWord_35480
  simp only [CollatzResearch.WordTrace]
  refine ⟨647030955734747173343947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 862707940979662897791929 647030955734747173343947)
  ·
    refine ⟨970546433602120760015921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 647030955734747173343947 970546433602120760015921)
    ·
      refine ⟨727909825201590570011941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 970546433602120760015921 727909825201590570011941)
      ·
        refine ⟨136483092225298231877239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 727909825201590570011941 136483092225298231877239)
        ·
          refine ⟨204724638337947347815859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136483092225298231877239 204724638337947347815859)
          ·
            refine ⟨307086957506921021723789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 204724638337947347815859 307086957506921021723789)
            ·
              refine ⟨115157609065095383146421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 307086957506921021723789 115157609065095383146421)
              ·
                refine ⟨10796025849852692169977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 115157609065095383146421 10796025849852692169977)
                ·
                  rfl

theorem cell19_35480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 5].length) (baseStart_35480 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_35480 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_35480 prefixEnd_35480 := by exact prefixLift 35480
  have htrace : WordTrace (prefixWord ++ tailWord_35480) baseStart_35480 baseEnd_35480 := by
    simpa [prefixWord, tailWord_35480, baseEnd_35480] using wordTrace_append hprefix tailTrace_35480
  have hstable : (prefixWord ++ tailWord_35480).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35480).length < 2 ^ (prefixWord ++ tailWord_35480).sum := by decide
  have hdescent : baseEnd_35480 < baseStart_35480 := by decide
  rcases family_descends (prefixWord ++ tailWord_35480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35495 : List Nat := [1, 1, 6, 3, 1, 2, 5]
def baseStart_35495 : Nat := 118140960795 + 35495 * 2 ^ 59
def prefixEnd_35495 : Nat := 4983230072969 + 3 ^ 40 * 35495 * 2
def baseEnd_35495 : Nat := 3600196707445700612201

theorem tailTrace_35495 : CollatzResearch.WordTrace tailWord_35495 prefixEnd_35495 3600196707445700612201 := by
  unfold tailWord_35495
  simp only [CollatzResearch.WordTrace]
  refine ⟨1294609006415151908483939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 863072670943434605655959 1294609006415151908483939)
  ·
    refine ⟨1941913509622727862725909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1294609006415151908483939 1941913509622727862725909)
    ·
      refine ⟨91027195763565368565277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 1941913509622727862725909 91027195763565368565277)
      ·
        refine ⟨34135198411337013211979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91027195763565368565277 34135198411337013211979)
        ·
          refine ⟨51202797617005519817969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34135198411337013211979 51202797617005519817969)
          ·
            refine ⟨38402098212754139863477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51202797617005519817969 38402098212754139863477)
            ·
              refine ⟨3600196707445700612201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38402098212754139863477 3600196707445700612201)
              ·
                rfl

theorem cell19_35495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 5].length) (baseStart_35495 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_35495 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_35495 prefixEnd_35495 := by exact prefixLift 35495
  have htrace : WordTrace (prefixWord ++ tailWord_35495) baseStart_35495 baseEnd_35495 := by
    simpa [prefixWord, tailWord_35495, baseEnd_35495] using wordTrace_append hprefix tailTrace_35495
  have hstable : (prefixWord ++ tailWord_35495).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35495).length < 2 ^ (prefixWord ++ tailWord_35495).sum := by decide
  have hdescent : baseEnd_35495 < baseStart_35495 := by decide
  rcases family_descends (prefixWord ++ tailWord_35495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35592 : List Nat := [2, 1, 3, 2, 2, 3, 3, 3]
def baseStart_35592 : Nat := 118140960795 + 35592 * 2 ^ 59
def prefixEnd_35592 : Nat := 4983230072969 + 3 ^ 40 * 35592 * 2
def baseEnd_35592 : Nat := 10830105751069617680783

theorem tailTrace_35592 : CollatzResearch.WordTrace tailWord_35592 prefixEnd_35592 10830105751069617680783 := by
  unfold tailWord_35592
  simp only [CollatzResearch.WordTrace]
  refine ⟨649073443531868737382515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 865431258042491649843353 649073443531868737382515)
  ·
    refine ⟨973610165297803106073773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 649073443531868737382515 973610165297803106073773)
    ·
      refine ⟨365103811986676164777665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 973610165297803106073773 365103811986676164777665)
      ·
        refine ⟨273827858990007123583249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 365103811986676164777665 273827858990007123583249)
        ·
          refine ⟨205370894242505342687437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 273827858990007123583249 205370894242505342687437)
          ·
            refine ⟨77014085340939503507789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 205370894242505342687437 77014085340939503507789)
            ·
              refine ⟨28880282002852313815421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77014085340939503507789 28880282002852313815421)
              ·
                refine ⟨10830105751069617680783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28880282002852313815421 10830105751069617680783)
                ·
                  rfl

theorem cell19_35592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 3, 3].length) (baseStart_35592 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_35592 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_35592 prefixEnd_35592 := by exact prefixLift 35592
  have htrace : WordTrace (prefixWord ++ tailWord_35592) baseStart_35592 baseEnd_35592 := by
    simpa [prefixWord, tailWord_35592, baseEnd_35592] using wordTrace_append hprefix tailTrace_35592
  have hstable : (prefixWord ++ tailWord_35592).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35592).length < 2 ^ (prefixWord ++ tailWord_35592).sum := by decide
  have hdescent : baseEnd_35592 < baseStart_35592 := by decide
  rcases family_descends (prefixWord ++ tailWord_35592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35645 : List Nat := [1, 4, 1, 4, 3, 1, 2, 3]
def baseStart_35645 : Nat := 118140960795 + 35645 * 2 ^ 59
def prefixEnd_35645 : Nat := 4983230072969 + 3 ^ 40 * 35645 * 2
def baseEnd_35645 : Nat := 10846232847181198502861

theorem tailTrace_35645 : CollatzResearch.WordTrace tailWord_35645 prefixEnd_35645 10846232847181198502861 := by
  unfold tailWord_35645
  simp only [CollatzResearch.WordTrace]
  refine ⟨1300079955871727526444389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 866719970581151684296259 1300079955871727526444389)
  ·
    refine ⟨243764991725948911208323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1300079955871727526444389 243764991725948911208323)
    ·
      refine ⟨365647487588923366812485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 243764991725948911208323 365647487588923366812485)
      ·
        refine ⟨68558903922923131277341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 365647487588923366812485 68558903922923131277341)
        ·
          refine ⟨25709588971096174229003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68558903922923131277341 25709588971096174229003)
          ·
            refine ⟨38564383456644261343505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25709588971096174229003 38564383456644261343505)
            ·
              refine ⟨28923287592483196007629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38564383456644261343505 28923287592483196007629)
              ·
                refine ⟨10846232847181198502861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28923287592483196007629 10846232847181198502861)
                ·
                  rfl

theorem cell19_35645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 2, 3].length) (baseStart_35645 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_35645 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_35645 prefixEnd_35645 := by exact prefixLift 35645
  have htrace : WordTrace (prefixWord ++ tailWord_35645) baseStart_35645 baseEnd_35645 := by
    simpa [prefixWord, tailWord_35645, baseEnd_35645] using wordTrace_append hprefix tailTrace_35645
  have hstable : (prefixWord ++ tailWord_35645).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35645).length < 2 ^ (prefixWord ++ tailWord_35645).sum := by decide
  have hdescent : baseEnd_35645 < baseStart_35645 := by decide
  rcases family_descends (prefixWord ++ tailWord_35645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35668 : List Nat := [2, 4, 1, 1, 4, 2, 5]
def baseStart_35668 : Nat := 118140960795 + 35668 * 2 ^ 59
def prefixEnd_35668 : Nat := 4983230072969 + 3 ^ 40 * 35668 * 2
def baseEnd_35668 : Nat := 3617743799441319997229

theorem tailTrace_35668 : CollatzResearch.WordTrace tailWord_35668 prefixEnd_35668 3617743799441319997229 := by
  unfold tailWord_35668
  simp only [CollatzResearch.WordTrace]
  refine ⟨650459417394201227265829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 867279223192268303021105 650459417394201227265829)
  ·
    refine ⟨121961140761412730112343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 650459417394201227265829 121961140761412730112343)
    ·
      refine ⟨182941711142119095168515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121961140761412730112343 182941711142119095168515)
      ·
        refine ⟨274412566713178642752773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182941711142119095168515 274412566713178642752773)
        ·
          refine ⟨51452356258720995516145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 274412566713178642752773 51452356258720995516145)
          ·
            refine ⟨38589267194040746637109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51452356258720995516145 38589267194040746637109)
            ·
              refine ⟨3617743799441319997229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38589267194040746637109 3617743799441319997229)
              ·
                rfl

theorem cell19_35668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 5].length) (baseStart_35668 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_35668 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_35668 prefixEnd_35668 := by exact prefixLift 35668
  have htrace : WordTrace (prefixWord ++ tailWord_35668) baseStart_35668 baseEnd_35668 := by
    simpa [prefixWord, tailWord_35668, baseEnd_35668] using wordTrace_append hprefix tailTrace_35668
  have hstable : (prefixWord ++ tailWord_35668).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35668).length < 2 ^ (prefixWord ++ tailWord_35668).sum := by decide
  have hdescent : baseEnd_35668 < baseStart_35668 := by decide
  rcases family_descends (prefixWord ++ tailWord_35668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35691 : List Nat := [1, 1, 1, 1, 2, 2, 5, 6]
def baseStart_35691 : Nat := 118140960795 + 35691 * 2 ^ 59
def prefixEnd_35691 : Nat := 4983230072969 + 3 ^ 40 * 35691 * 2
def baseEnd_35691 : Nat := 10860229949466721480513

theorem tailTrace_35691 : CollatzResearch.WordTrace tailWord_35691 prefixEnd_35691 10860229949466721480513 := by
  unfold tailWord_35691
  simp only [CollatzResearch.WordTrace]
  refine ⟨1301757713705077382618927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 867838475803384921745951 1301757713705077382618927)
  ·
    refine ⟨1952636570557616073928391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1301757713705077382618927 1952636570557616073928391)
    ·
      refine ⟨2928954855836424110892587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1952636570557616073928391 2928954855836424110892587)
      ·
        refine ⟨4393432283754636166338881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2928954855836424110892587 4393432283754636166338881)
        ·
          refine ⟨3295074212815977124754161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4393432283754636166338881 3295074212815977124754161)
          ·
            refine ⟨2471305659611982843565621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3295074212815977124754161 2471305659611982843565621)
            ·
              refine ⟨231684905588623391584277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2471305659611982843565621 231684905588623391584277)
              ·
                refine ⟨10860229949466721480513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 231684905588623391584277 10860229949466721480513)
                ·
                  rfl

theorem cell19_35691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 6].length) (baseStart_35691 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_35691 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_35691 prefixEnd_35691 := by exact prefixLift 35691
  have htrace : WordTrace (prefixWord ++ tailWord_35691) baseStart_35691 baseEnd_35691 := by
    simpa [prefixWord, tailWord_35691, baseEnd_35691] using wordTrace_append hprefix tailTrace_35691
  have hstable : (prefixWord ++ tailWord_35691).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35691).length < 2 ^ (prefixWord ++ tailWord_35691).sum := by decide
  have hdescent : baseEnd_35691 < baseStart_35691 := by decide
  rcases family_descends (prefixWord ++ tailWord_35691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35767 : List Nat := [1, 1, 3, 1, 3, 1, 2, 7]
def baseStart_35767 : Nat := 118140960795 + 35767 * 2 ^ 59
def prefixEnd_35767 : Nat := 4983230072969 + 3 ^ 40 * 35767 * 2
def baseEnd_35767 : Nat := 10883355596721063791417

theorem tailTrace_35767 : CollatzResearch.WordTrace tailWord_35767 prefixEnd_35767 10883355596721063791417 := by
  unfold tailWord_35767
  simp only [CollatzResearch.WordTrace]
  refine ⟨1304529661429742362385555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 869686440953161574923703 1304529661429742362385555)
  ·
    refine ⟨1956794492144613543578333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1304529661429742362385555 1956794492144613543578333)
    ·
      refine ⟨733797934554230078841875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1956794492144613543578333 733797934554230078841875)
      ·
        refine ⟨1100696901831345118262813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 733797934554230078841875 1100696901831345118262813)
        ·
          refine ⟨412761338186754419348555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1100696901831345118262813 412761338186754419348555)
          ·
            refine ⟨619142007280131629022833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 412761338186754419348555 619142007280131629022833)
            ·
              refine ⟨464356505460098721767125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 619142007280131629022833 464356505460098721767125)
              ·
                refine ⟨10883355596721063791417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 464356505460098721767125 10883355596721063791417)
                ·
                  rfl

theorem cell19_35767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 7].length) (baseStart_35767 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_35767 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_35767 prefixEnd_35767 := by exact prefixLift 35767
  have htrace : WordTrace (prefixWord ++ tailWord_35767) baseStart_35767 baseEnd_35767 := by
    simpa [prefixWord, tailWord_35767, baseEnd_35767] using wordTrace_append hprefix tailTrace_35767
  have hstable : (prefixWord ++ tailWord_35767).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35767).length < 2 ^ (prefixWord ++ tailWord_35767).sum := by decide
  have hdescent : baseEnd_35767 < baseStart_35767 := by decide
  rcases family_descends (prefixWord ++ tailWord_35767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35784 : List Nat := [2, 1, 3, 1, 5, 1, 6]
def baseStart_35784 : Nat := 118140960795 + 35784 * 2 ^ 59
def prefixEnd_35784 : Nat := 4983230072969 + 3 ^ 40 * 35784 * 2
def baseEnd_35784 : Nat := 3629509479623353804531

theorem tailTrace_35784 : CollatzResearch.WordTrace tailWord_35784 prefixEnd_35784 3629509479623353804531 := by
  unfold tailWord_35784
  simp only [CollatzResearch.WordTrace]
  refine ⟨652574851184077132877203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 870099801578769510502937 652574851184077132877203)
  ·
    refine ⟨978862276776115699315805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 652574851184077132877203 978862276776115699315805)
    ·
      refine ⟨367073353791043387243427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 978862276776115699315805 367073353791043387243427)
      ·
        refine ⟨550610030686565080865141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 367073353791043387243427 550610030686565080865141)
        ·
          refine ⟨51619690376865476331107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 550610030686565080865141 51619690376865476331107)
          ·
            refine ⟨77429535565298214496661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51619690376865476331107 77429535565298214496661)
            ·
              refine ⟨3629509479623353804531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 77429535565298214496661 3629509479623353804531)
              ·
                rfl

theorem cell19_35784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 6].length) (baseStart_35784 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_35784 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_35784 prefixEnd_35784 := by exact prefixLift 35784
  have htrace : WordTrace (prefixWord ++ tailWord_35784) baseStart_35784 baseEnd_35784 := by
    simpa [prefixWord, tailWord_35784, baseEnd_35784] using wordTrace_append hprefix tailTrace_35784
  have hstable : (prefixWord ++ tailWord_35784).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35784).length < 2 ^ (prefixWord ++ tailWord_35784).sum := by decide
  have hdescent : baseEnd_35784 < baseStart_35784 := by decide
  rcases family_descends (prefixWord ++ tailWord_35784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35841 : List Nat := [1, 2, 4, 1, 2, 4, 5]
def baseStart_35841 : Nat := 118140960795 + 35841 * 2 ^ 59
def prefixEnd_35841 : Nat := 4983230072969 + 3 ^ 40 * 35841 * 2
def baseEnd_35841 : Nat := 3635290891436939382257

theorem tailTrace_35841 : CollatzResearch.WordTrace tailWord_35841 prefixEnd_35841 3635290891436939382257 := by
  unfold tailWord_35841
  simp only [CollatzResearch.WordTrace]
  refine ⟨1307228663161653000579377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 871485775441102000386251 1307228663161653000579377)
  ·
    refine ⟨980421497371239750434533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1307228663161653000579377 980421497371239750434533)
    ·
      refine ⟨183829030757107453206475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 980421497371239750434533 183829030757107453206475)
      ·
        refine ⟨275743546135661179809713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183829030757107453206475 275743546135661179809713)
        ·
          refine ⟨206807659601745884857285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 275743546135661179809713 206807659601745884857285)
          ·
            refine ⟨38776436175327353410741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 206807659601745884857285 38776436175327353410741)
            ·
              refine ⟨3635290891436939382257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38776436175327353410741 3635290891436939382257)
              ·
                rfl

theorem cell19_35841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 5].length) (baseStart_35841 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_35841 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_35841 prefixEnd_35841 := by exact prefixLift 35841
  have htrace : WordTrace (prefixWord ++ tailWord_35841) baseStart_35841 baseEnd_35841 := by
    simpa [prefixWord, tailWord_35841, baseEnd_35841] using wordTrace_append hprefix tailTrace_35841
  have hstable : (prefixWord ++ tailWord_35841).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35841).length < 2 ^ (prefixWord ++ tailWord_35841).sum := by decide
  have hdescent : baseEnd_35841 < baseStart_35841 := by decide
  rcases family_descends (prefixWord ++ tailWord_35841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35900 : List Nat := [2, 2, 2, 2, 2, 9]
def baseStart_35900 : Nat := 118140960795 + 35900 * 2 ^ 59
def prefixEnd_35900 : Nat := 4983230072969 + 3 ^ 40 * 35900 * 2
def baseEnd_35900 : Nat := 1213758386601795870611

theorem tailTrace_35900 : CollatzResearch.WordTrace tailWord_35900 prefixEnd_35900 1213758386601795870611 := by
  unfold tailWord_35900
  simp only [CollatzResearch.WordTrace]
  refine ⟨654690284973953038488577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 872920379965270717984769 654690284973953038488577)
  ·
    refine ⟨491017713730464778866433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 654690284973953038488577 491017713730464778866433)
    ·
      refine ⟨368263285297848584149825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 491017713730464778866433 368263285297848584149825)
      ·
        refine ⟨276197463973386438112369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 368263285297848584149825 276197463973386438112369)
        ·
          refine ⟨207148097980039828584277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 276197463973386438112369 207148097980039828584277)
          ·
            refine ⟨1213758386601795870611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 207148097980039828584277 1213758386601795870611)
            ·
              rfl

theorem cell19_35900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 9].length) (baseStart_35900 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_35900 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_35900 prefixEnd_35900 := by exact prefixLift 35900
  have htrace : WordTrace (prefixWord ++ tailWord_35900) baseStart_35900 baseEnd_35900 := by
    simpa [prefixWord, tailWord_35900, baseEnd_35900] using wordTrace_append hprefix tailTrace_35900
  have hstable : (prefixWord ++ tailWord_35900).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35900).length < 2 ^ (prefixWord ++ tailWord_35900).sum := by decide
  have hdescent : baseEnd_35900 < baseStart_35900 := by decide
  rcases family_descends (prefixWord ++ tailWord_35900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35936 : List Nat := [2, 1, 1, 3, 2, 2, 5, 3]
def baseStart_35936 : Nat := 118140960795 + 35936 * 2 ^ 59
def prefixEnd_35936 : Nat := 4983230072969 + 3 ^ 40 * 35936 * 2
def baseEnd_35936 : Nat := 10934779733378746035401

theorem tailTrace_35936 : CollatzResearch.WordTrace tailWord_35936 prefixEnd_35936 10934779733378746035401 := by
  unfold tailWord_35936
  simp only [CollatzResearch.WordTrace]
  refine ⟨655346798908742112643831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 873795731878322816858441 655346798908742112643831)
  ·
    refine ⟨983020198363113168965747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 655346798908742112643831 983020198363113168965747)
    ·
      refine ⟨1474530297544669753448621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 983020198363113168965747 1474530297544669753448621)
      ·
        refine ⟨552948861579251157543233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1474530297544669753448621 552948861579251157543233)
        ·
          refine ⟨414711646184438368157425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 552948861579251157543233 414711646184438368157425)
          ·
            refine ⟨311033734638328776118069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 414711646184438368157425 311033734638328776118069)
            ·
              refine ⟨29159412622343322761069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 311033734638328776118069 29159412622343322761069)
              ·
                refine ⟨10934779733378746035401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29159412622343322761069 10934779733378746035401)
                ·
                  rfl

theorem cell19_35936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 5, 3].length) (baseStart_35936 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_35936 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_35936 prefixEnd_35936 := by exact prefixLift 35936
  have htrace : WordTrace (prefixWord ++ tailWord_35936) baseStart_35936 baseEnd_35936 := by
    simpa [prefixWord, tailWord_35936, baseEnd_35936] using wordTrace_append hprefix tailTrace_35936
  have hstable : (prefixWord ++ tailWord_35936).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35936).length < 2 ^ (prefixWord ++ tailWord_35936).sum := by decide
  have hdescent : baseEnd_35936 < baseStart_35936 := by decide
  rcases family_descends (prefixWord ++ tailWord_35936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35991 : List Nat := [1, 1, 3, 3, 3, 3, 2, 3]
def baseStart_35991 : Nat := 118140960795 + 35991 * 2 ^ 59
def prefixEnd_35991 : Nat := 4983230072969 + 3 ^ 40 * 35991 * 2
def baseEnd_35991 : Nat := 10951515399154914813029

theorem tailTrace_35991 : CollatzResearch.WordTrace tailWord_35991 prefixEnd_35991 10951515399154914813029 := by
  unfold tailWord_35991
  simp only [CollatzResearch.WordTrace]
  refine ⟨1312699612618228618539827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 875133075078819079026551 1312699612618228618539827)
  ·
    refine ⟨1969049418927342927809741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1312699612618228618539827 1969049418927342927809741)
    ·
      refine ⟨738393532097753597928653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1969049418927342927809741 738393532097753597928653)
      ·
        refine ⟨276897574536657599223245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 738393532097753597928653 276897574536657599223245)
        ·
          refine ⟨103836590451246599708717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 276897574536657599223245 103836590451246599708717)
          ·
            refine ⟨38938721419217474890769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 103836590451246599708717 38938721419217474890769)
            ·
              refine ⟨29204041064413106168077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38938721419217474890769 29204041064413106168077)
              ·
                refine ⟨10951515399154914813029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29204041064413106168077 10951515399154914813029)
                ·
                  rfl

theorem cell19_35991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 2, 3].length) (baseStart_35991 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_35991 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_35991 prefixEnd_35991 := by exact prefixLift 35991
  have htrace : WordTrace (prefixWord ++ tailWord_35991) baseStart_35991 baseEnd_35991 := by
    simpa [prefixWord, tailWord_35991, baseEnd_35991] using wordTrace_append hprefix tailTrace_35991
  have hstable : (prefixWord ++ tailWord_35991).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35991).length < 2 ^ (prefixWord ++ tailWord_35991).sum := by decide
  have hdescent : baseEnd_35991 < baseStart_35991 := by decide
  rcases family_descends (prefixWord ++ tailWord_35991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36010 : List Nat := [3, 1, 5, 1, 1, 3, 5]
def baseStart_36010 : Nat := 118140960795 + 36010 * 2 ^ 59
def prefixEnd_36010 : Nat := 4983230072969 + 3 ^ 40 * 36010 * 2
def baseEnd_36010 : Nat := 3652432270322833463585

theorem tailTrace_36010 : CollatzResearch.WordTrace tailWord_36010 prefixEnd_36010 3652432270322833463585 := by
  unfold tailWord_36010
  simp only [CollatzResearch.WordTrace]
  refine ⟨328348149887348715870371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 875595066366263242320989 328348149887348715870371)
  ·
    refine ⟨492522224831023073805557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 328348149887348715870371 492522224831023073805557)
    ·
      refine ⟨46173958577908413169271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 492522224831023073805557 46173958577908413169271)
      ·
        refine ⟨69260937866862619753907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46173958577908413169271 69260937866862619753907)
        ·
          refine ⟨103891406800293929630861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69260937866862619753907 103891406800293929630861)
          ·
            refine ⟨38959277550110223611573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 103891406800293929630861 38959277550110223611573)
            ·
              refine ⟨3652432270322833463585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38959277550110223611573 3652432270322833463585)
              ·
                rfl

theorem cell19_36010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 5].length) (baseStart_36010 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_36010 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_36010 prefixEnd_36010 := by exact prefixLift 36010
  have htrace : WordTrace (prefixWord ++ tailWord_36010) baseStart_36010 baseEnd_36010 := by
    simpa [prefixWord, tailWord_36010, baseEnd_36010] using wordTrace_append hprefix tailTrace_36010
  have hstable : (prefixWord ++ tailWord_36010).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36010).length < 2 ^ (prefixWord ++ tailWord_36010).sum := by decide
  have hdescent : baseEnd_36010 < baseStart_36010 := by decide
  rcases family_descends (prefixWord ++ tailWord_36010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36069 : List Nat := [1, 3, 1, 4, 4, 6]
def baseStart_36069 : Nat := 118140960795 + 36069 * 2 ^ 59
def prefixEnd_36069 : Nat := 4983230072969 + 3 ^ 40 * 36069 * 2
def baseEnd_36069 : Nat := 1219472179563760564387

theorem tailTrace_36069 : CollatzResearch.WordTrace tailWord_36069 prefixEnd_36069 1219472179563760564387 := by
  unfold tailWord_36069
  simp only [CollatzResearch.WordTrace]
  refine ⟨1315544506335647939879261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 877029670890431959919507 1315544506335647939879261)
  ·
    refine ⟨493329189875867977454723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1315544506335647939879261 493329189875867977454723)
    ·
      refine ⟨739993784813801966182085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 493329189875867977454723 739993784813801966182085)
      ·
        refine ⟨138748834652587868659141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 739993784813801966182085 138748834652587868659141)
        ·
          refine ⟨26015406497360225373589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 138748834652587868659141 26015406497360225373589)
          ·
            refine ⟨1219472179563760564387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 26015406497360225373589 1219472179563760564387)
            ·
              rfl

theorem cell19_36069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 6].length) (baseStart_36069 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_36069 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_36069 prefixEnd_36069 := by exact prefixLift 36069
  have htrace : WordTrace (prefixWord ++ tailWord_36069) baseStart_36069 baseEnd_36069 := by
    simpa [prefixWord, tailWord_36069, baseEnd_36069] using wordTrace_append hprefix tailTrace_36069
  have hstable : (prefixWord ++ tailWord_36069).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36069).length < 2 ^ (prefixWord ++ tailWord_36069).sum := by decide
  have hdescent : baseEnd_36069 < baseStart_36069 := by decide
  rcases family_descends (prefixWord ++ tailWord_36069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36071 : List Nat := [1, 1, 5, 3, 9]
def baseStart_36071 : Nat := 118140960795 + 36071 * 2 ^ 59
def prefixEnd_36071 : Nat := 4983230072969 + 3 ^ 40 * 36071 * 2
def baseEnd_36071 : Nat := 406513266138460482779

theorem tailTrace_36071 : CollatzResearch.WordTrace tailWord_36071 prefixEnd_36071 406513266138460482779 := by
  unfold tailWord_36071
  simp only [CollatzResearch.WordTrace]
  refine ⟨1315617452328402281452067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 877078301552268187634711 1315617452328402281452067)
  ·
    refine ⟨1973426178492603422178101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1315617452328402281452067 1973426178492603422178101)
    ·
      refine ⟨185008704233681570829197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1973426178492603422178101 185008704233681570829197)
      ·
        refine ⟨69378264087630589060949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 185008704233681570829197 69378264087630589060949)
        ·
          refine ⟨406513266138460482779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 69378264087630589060949 406513266138460482779)
          ·
            rfl

theorem cell19_36071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 9].length) (baseStart_36071 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_36071 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_36071 prefixEnd_36071 := by exact prefixLift 36071
  have htrace : WordTrace (prefixWord ++ tailWord_36071) baseStart_36071 baseEnd_36071 := by
    simpa [prefixWord, tailWord_36071, baseEnd_36071] using wordTrace_append hprefix tailTrace_36071
  have hstable : (prefixWord ++ tailWord_36071).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36071).length < 2 ^ (prefixWord ++ tailWord_36071).sum := by decide
  have hdescent : baseEnd_36071 < baseStart_36071 := by decide
  rcases family_descends (prefixWord ++ tailWord_36071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36107 : List Nat := [1, 1, 1, 1, 5, 4, 3, 3]
def baseStart_36107 : Nat := 118140960795 + 36107 * 2 ^ 59
def prefixEnd_36107 : Nat := 4983230072969 + 3 ^ 40 * 36107 * 2
def baseEnd_36107 : Nat := 10986812439701016234935

theorem tailTrace_36107 : CollatzResearch.WordTrace tailWord_36107 prefixEnd_36107 10986812439701016234935 := by
  unfold tailWord_36107
  simp only [CollatzResearch.WordTrace]
  refine ⟨1316930480197980429762575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 877953653465320286508383 1316930480197980429762575)
  ·
    refine ⟨1975395720296970644643863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1316930480197980429762575 1975395720296970644643863)
    ·
      refine ⟨2963093580445455966965795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1975395720296970644643863 2963093580445455966965795)
      ·
        refine ⟨4444640370668183950448693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2963093580445455966965795 4444640370668183950448693)
        ·
          refine ⟨416685034750142245354565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4444640370668183950448693 416685034750142245354565)
          ·
            refine ⟨78128444015651671003981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 416685034750142245354565 78128444015651671003981)
            ·
              refine ⟨29298166505869376626493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78128444015651671003981 29298166505869376626493)
              ·
                refine ⟨10986812439701016234935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29298166505869376626493 10986812439701016234935)
                ·
                  rfl

theorem cell19_36107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 3, 3].length) (baseStart_36107 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_36107 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_36107 prefixEnd_36107 := by exact prefixLift 36107
  have htrace : WordTrace (prefixWord ++ tailWord_36107) baseStart_36107 baseEnd_36107 := by
    simpa [prefixWord, tailWord_36107, baseEnd_36107] using wordTrace_append hprefix tailTrace_36107
  have hstable : (prefixWord ++ tailWord_36107).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36107).length < 2 ^ (prefixWord ++ tailWord_36107).sum := by decide
  have hdescent : baseEnd_36107 < baseStart_36107 := by decide
  rcases family_descends (prefixWord ++ tailWord_36107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36204 : List Nat := [2, 2, 1, 1, 5, 1, 1, 6]
def baseStart_36204 : Nat := 118140960795 + 36204 * 2 ^ 59
def prefixEnd_36204 : Nat := 4983230072969 + 3 ^ 40 * 36204 * 2
def baseEnd_36204 : Nat := 11016328068433532079115

theorem tailTrace_36204 : CollatzResearch.WordTrace tailWord_36204 prefixEnd_36204 11016328068433532079115 := by
  unfold tailWord_36204
  simp only [CollatzResearch.WordTrace]
  refine ⟨660234180423282998021833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 880312240564377330695777 660234180423282998021833)
  ·
    refine ⟨495175635317462248516375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 660234180423282998021833 495175635317462248516375)
    ·
      refine ⟨742763452976193372774563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 495175635317462248516375 742763452976193372774563)
      ·
        refine ⟨1114145179464290059161845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 742763452976193372774563 1114145179464290059161845)
        ·
          refine ⟨104451110574777193046423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1114145179464290059161845 104451110574777193046423)
          ·
            refine ⟨156676665862165789569635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104451110574777193046423 156676665862165789569635)
            ·
              refine ⟨235014998793248684354453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 156676665862165789569635 235014998793248684354453)
              ·
                refine ⟨11016328068433532079115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 235014998793248684354453 11016328068433532079115)
                ·
                  rfl

theorem cell19_36204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 6].length) (baseStart_36204 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_36204 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_36204 prefixEnd_36204 := by exact prefixLift 36204
  have htrace : WordTrace (prefixWord ++ tailWord_36204) baseStart_36204 baseEnd_36204 := by
    simpa [prefixWord, tailWord_36204, baseEnd_36204] using wordTrace_append hprefix tailTrace_36204
  have hstable : (prefixWord ++ tailWord_36204).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36204).length < 2 ^ (prefixWord ++ tailWord_36204).sum := by decide
  have hdescent : baseEnd_36204 < baseStart_36204 := by decide
  rcases family_descends (prefixWord ++ tailWord_36204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36337 : List Nat := [1, 2, 2, 2, 3, 3, 1, 5]
def baseStart_36337 : Nat := 118140960795 + 36337 * 2 ^ 59
def prefixEnd_36337 : Nat := 4983230072969 + 3 ^ 40 * 36337 * 2
def baseEnd_36337 : Nat := 11056797951128631123197

theorem tailTrace_36337 : CollatzResearch.WordTrace tailWord_36337 prefixEnd_36337 11056797951128631123197 := by
  unfold tailWord_36337
  simp only [CollatzResearch.WordTrace]
  refine ⟨1325319269364729710635265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 883546179576486473756843 1325319269364729710635265)
  ·
    refine ⟨993989452023547282976449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1325319269364729710635265 993989452023547282976449)
    ·
      refine ⟨745492089017660462232337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 993989452023547282976449 745492089017660462232337)
      ·
        refine ⟨559119066763245346674253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 745492089017660462232337 559119066763245346674253)
        ·
          refine ⟨209669650036217005002845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 559119066763245346674253 209669650036217005002845)
          ·
            refine ⟨78626118763581376876067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 209669650036217005002845 78626118763581376876067)
            ·
              refine ⟨117939178145372065314101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78626118763581376876067 117939178145372065314101)
              ·
                refine ⟨11056797951128631123197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 117939178145372065314101 11056797951128631123197)
                ·
                  rfl

theorem cell19_36337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 5].length) (baseStart_36337 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_36337 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_36337 prefixEnd_36337 := by exact prefixLift 36337
  have htrace : WordTrace (prefixWord ++ tailWord_36337) baseStart_36337 baseEnd_36337 := by
    simpa [prefixWord, tailWord_36337, baseEnd_36337] using wordTrace_append hprefix tailTrace_36337
  have hstable : (prefixWord ++ tailWord_36337).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36337).length < 2 ^ (prefixWord ++ tailWord_36337).sum := by decide
  have hdescent : baseEnd_36337 < baseStart_36337 := by decide
  rcases family_descends (prefixWord ++ tailWord_36337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36350 : List Nat := [4, 2, 2, 3, 2, 1, 5]
def baseStart_36350 : Nat := 118140960795 + 36350 * 2 ^ 59
def prefixEnd_36350 : Nat := 4983230072969 + 3 ^ 40 * 36350 * 2
def baseEnd_36350 : Nat := 3686917884649484278091

theorem tailTrace_36350 : CollatzResearch.WordTrace tailWord_36350 prefixEnd_36350 3686917884649484278091 := by
  unfold tailWord_36350
  simp only [CollatzResearch.WordTrace]
  refine ⟨165724177289704116357313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 883862278878421953905669 165724177289704116357313)
  ·
    refine ⟨124293132967278087267985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165724177289704116357313 124293132967278087267985)
    ·
      refine ⟨93219849725458565450989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124293132967278087267985 93219849725458565450989)
      ·
        refine ⟨34957443647046962044121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93219849725458565450989 34957443647046962044121)
        ·
          refine ⟨26218082735285221533091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34957443647046962044121 26218082735285221533091)
          ·
            refine ⟨39327124102927832299637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26218082735285221533091 39327124102927832299637)
            ·
              refine ⟨3686917884649484278091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39327124102927832299637 3686917884649484278091)
              ·
                rfl

theorem cell19_36350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 5].length) (baseStart_36350 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_36350 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_36350 prefixEnd_36350 := by exact prefixLift 36350
  have htrace : WordTrace (prefixWord ++ tailWord_36350) baseStart_36350 baseEnd_36350 := by
    simpa [prefixWord, tailWord_36350, baseEnd_36350] using wordTrace_append hprefix tailTrace_36350
  have hstable : (prefixWord ++ tailWord_36350).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36350).length < 2 ^ (prefixWord ++ tailWord_36350).sum := by decide
  have hdescent : baseEnd_36350 < baseStart_36350 := by decide
  rcases family_descends (prefixWord ++ tailWord_36350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36354 : List Nat := [3, 4, 1, 2, 1, 1, 7]
def baseStart_36354 : Nat := 118140960795 + 36354 * 2 ^ 59
def prefixEnd_36354 : Nat := 4983230072969 + 3 ^ 40 * 36354 * 2
def baseEnd_36354 : Nat := 3687323597759209581791

theorem tailTrace_36354 : CollatzResearch.WordTrace tailWord_36354 prefixEnd_36354 3687323597759209581791 := by
  unfold tailWord_36354
  simp only [CollatzResearch.WordTrace]
  refine ⟨331484827575785403501029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 883959540202094409336077 331484827575785403501029)
  ·
    refine ⟨62153405170459763156443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 331484827575785403501029 62153405170459763156443)
    ·
      refine ⟨93230107755689644734665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62153405170459763156443 93230107755689644734665)
      ·
        refine ⟨69922580816767233550999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93230107755689644734665 69922580816767233550999)
        ·
          refine ⟨104883871225150850326499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69922580816767233550999 104883871225150850326499)
          ·
            refine ⟨157325806837726275489749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104883871225150850326499 157325806837726275489749)
            ·
              refine ⟨3687323597759209581791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 157325806837726275489749 3687323597759209581791)
              ·
                rfl

theorem cell19_36354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 7].length) (baseStart_36354 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_36354 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_36354 prefixEnd_36354 := by exact prefixLift 36354
  have htrace : WordTrace (prefixWord ++ tailWord_36354) baseStart_36354 baseEnd_36354 := by
    simpa [prefixWord, tailWord_36354, baseEnd_36354] using wordTrace_append hprefix tailTrace_36354
  have hstable : (prefixWord ++ tailWord_36354).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36354).length < 2 ^ (prefixWord ++ tailWord_36354).sum := by decide
  have hdescent : baseEnd_36354 < baseStart_36354 := by decide
  rcases family_descends (prefixWord ++ tailWord_36354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36394 : List Nat := [3, 1, 4, 1, 1, 1, 1, 7]
def baseStart_36394 : Nat := 118140960795 + 36394 * 2 ^ 59
def prefixEnd_36394 : Nat := 4983230072969 + 3 ^ 40 * 36394 * 2
def baseEnd_36394 : Nat := 11074142186569387856375

theorem tailTrace_36394 : CollatzResearch.WordTrace tailWord_36394 prefixEnd_36394 11074142186569387856375 := by
  unfold tailWord_36394
  simp only [CollatzResearch.WordTrace]
  refine ⟨331849557539557111365059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 884932153438818963640157 331849557539557111365059)
  ·
    refine ⟨497774336309335667047589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 331849557539557111365059 497774336309335667047589)
    ·
      refine ⟨93332688058000437571423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 497774336309335667047589 93332688058000437571423)
      ·
        refine ⟨139999032087000656357135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93332688058000437571423 139999032087000656357135)
        ·
          refine ⟨209998548130500984535703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139999032087000656357135 209998548130500984535703)
          ·
            refine ⟨314997822195751476803555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 209998548130500984535703 314997822195751476803555)
            ·
              refine ⟨472496733293627215205333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 314997822195751476803555 472496733293627215205333)
              ·
                refine ⟨11074142186569387856375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 472496733293627215205333 11074142186569387856375)
                ·
                  rfl

theorem cell19_36394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 7].length) (baseStart_36394 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_36394 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_36394 prefixEnd_36394 := by exact prefixLift 36394
  have htrace : WordTrace (prefixWord ++ tailWord_36394) baseStart_36394 baseEnd_36394 := by
    simpa [prefixWord, tailWord_36394, baseEnd_36394] using wordTrace_append hprefix tailTrace_36394
  have hstable : (prefixWord ++ tailWord_36394).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36394).length < 2 ^ (prefixWord ++ tailWord_36394).sum := by decide
  have hdescent : baseEnd_36394 < baseStart_36394 := by decide
  rcases family_descends (prefixWord ++ tailWord_36394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36413 : List Nat := [1, 4, 1, 3, 3, 7]
def baseStart_36413 : Nat := 118140960795 + 36413 * 2 ^ 59
def prefixEnd_36413 : Nat := 4983230072969 + 3 ^ 40 * 36413 * 2
def baseEnd_36413 : Nat := 1231102622042552603789

theorem tailTrace_36413 : CollatzResearch.WordTrace tailWord_36413 prefixEnd_36413 1231102622042552603789 := by
  unfold tailWord_36413
  simp only [CollatzResearch.WordTrace]
  refine ⟨1328091217089394690401893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 885394144726263126934595 1328091217089394690401893)
  ·
    refine ⟨249017103204261504450355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1328091217089394690401893 249017103204261504450355)
    ·
      refine ⟨373525654806392256675533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 249017103204261504450355 373525654806392256675533)
      ·
        refine ⟨140072120552397096253325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 373525654806392256675533 140072120552397096253325)
        ·
          refine ⟨52527045207148911094997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 140072120552397096253325 52527045207148911094997)
          ·
            refine ⟨1231102622042552603789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 52527045207148911094997 1231102622042552603789)
            ·
              rfl

theorem cell19_36413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 7].length) (baseStart_36413 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_36413 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_36413 prefixEnd_36413 := by exact prefixLift 36413
  have htrace : WordTrace (prefixWord ++ tailWord_36413) baseStart_36413 baseEnd_36413 := by
    simpa [prefixWord, tailWord_36413, baseEnd_36413] using wordTrace_append hprefix tailTrace_36413
  have hstable : (prefixWord ++ tailWord_36413).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36413).length < 2 ^ (prefixWord ++ tailWord_36413).sum := by decide
  have hdescent : baseEnd_36413 < baseStart_36413 := by decide
  rcases family_descends (prefixWord ++ tailWord_36413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36415 : List Nat := [1, 1, 2, 2, 3, 10]
def baseStart_36415 : Nat := 118140960795 + 36415 * 2 ^ 59
def prefixEnd_36415 : Nat := 4983230072969 + 3 ^ 40 * 36415 * 2
def baseEnd_36415 : Nat := 1231170240894173487739

theorem tailTrace_36415 : CollatzResearch.WordTrace tailWord_36415 prefixEnd_36415 1231170240894173487739 := by
  unfold tailWord_36415
  simp only [CollatzResearch.WordTrace]
  refine ⟨1328164163082149031974699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 885442775388099354649799 1328164163082149031974699)
  ·
    refine ⟨1992246244623223547962049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1328164163082149031974699 1992246244623223547962049)
    ·
      refine ⟨1494184683467417660971537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1992246244623223547962049 1494184683467417660971537)
      ·
        refine ⟨1120638512600563245728653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1494184683467417660971537 1120638512600563245728653)
        ·
          refine ⟨420239442225211217148245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1120638512600563245728653 420239442225211217148245)
          ·
            refine ⟨1231170240894173487739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 420239442225211217148245 1231170240894173487739)
            ·
              rfl

theorem cell19_36415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 10].length) (baseStart_36415 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_36415 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_36415 prefixEnd_36415 := by exact prefixLift 36415
  have htrace : WordTrace (prefixWord ++ tailWord_36415) baseStart_36415 baseEnd_36415 := by
    simpa [prefixWord, tailWord_36415, baseEnd_36415] using wordTrace_append hprefix tailTrace_36415
  have hstable : (prefixWord ++ tailWord_36415).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36415).length < 2 ^ (prefixWord ++ tailWord_36415).sum := by decide
  have hdescent : baseEnd_36415 < baseStart_36415 := by decide
  rcases family_descends (prefixWord ++ tailWord_36415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36445 : List Nat := [1, 4, 4, 2, 1, 1, 3, 3]
def baseStart_36445 : Nat := 118140960795 + 36445 * 2 ^ 59
def prefixEnd_36445 : Nat := 4983230072969 + 3 ^ 40 * 36445 * 2
def baseEnd_36445 : Nat := 11089660713016380722903

theorem tailTrace_36445 : CollatzResearch.WordTrace tailWord_36445 prefixEnd_36445 11089660713016380722903 := by
  unfold tailWord_36445
  simp only [CollatzResearch.WordTrace]
  refine ⟨1329258352973464155566789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 886172235315642770377859 1329258352973464155566789)
  ·
    refine ⟨249235941182524529168773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1329258352973464155566789 249235941182524529168773)
    ·
      refine ⟨46731738971723349219145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 249235941182524529168773 46731738971723349219145)
      ·
        refine ⟨35048804228792511914359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46731738971723349219145 35048804228792511914359)
        ·
          refine ⟨52573206343188767871539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35048804228792511914359 52573206343188767871539)
          ·
            refine ⟨78859809514783151807309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52573206343188767871539 78859809514783151807309)
            ·
              refine ⟨29572428568043681927741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78859809514783151807309 29572428568043681927741)
              ·
                refine ⟨11089660713016380722903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29572428568043681927741 11089660713016380722903)
                ·
                  rfl

theorem cell19_36445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 3, 3].length) (baseStart_36445 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_36445 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_36445 prefixEnd_36445 := by exact prefixLift 36445
  have htrace : WordTrace (prefixWord ++ tailWord_36445) baseStart_36445 baseEnd_36445 := by
    simpa [prefixWord, tailWord_36445, baseEnd_36445] using wordTrace_append hprefix tailTrace_36445
  have hstable : (prefixWord ++ tailWord_36445).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36445).length < 2 ^ (prefixWord ++ tailWord_36445).sum := by decide
  have hdescent : baseEnd_36445 < baseStart_36445 := by decide
  rcases family_descends (prefixWord ++ tailWord_36445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36491 : List Nat := [1, 1, 1, 1, 4, 1, 4, 6]
def baseStart_36491 : Nat := 118140960795 + 36491 * 2 ^ 59
def prefixEnd_36491 : Nat := 4983230072969 + 3 ^ 40 * 36491 * 2
def baseEnd_36491 : Nat := 11103657815301903700555

theorem tailTrace_36491 : CollatzResearch.WordTrace tailWord_36491 prefixEnd_36491 11103657815301903700555 := by
  unfold tailWord_36491
  simp only [CollatzResearch.WordTrace]
  refine ⟨1330936110806814011741327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 887290740537876007827551 1330936110806814011741327)
  ·
    refine ⟨1996404166210221017611991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1330936110806814011741327 1996404166210221017611991)
    ·
      refine ⟨2994606249315331526417987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1996404166210221017611991 2994606249315331526417987)
      ·
        refine ⟨4491909373972997289626981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2994606249315331526417987 4491909373972997289626981)
        ·
          refine ⟨842233007619936991805059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4491909373972997289626981 842233007619936991805059)
          ·
            refine ⟨1263349511429905487707589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 842233007619936991805059 1263349511429905487707589)
            ·
              refine ⟨236878033393107278945173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1263349511429905487707589 236878033393107278945173)
              ·
                refine ⟨11103657815301903700555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 236878033393107278945173 11103657815301903700555)
                ·
                  rfl

theorem cell19_36491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 6].length) (baseStart_36491 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_36491 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_36491 prefixEnd_36491 := by exact prefixLift 36491
  have htrace : WordTrace (prefixWord ++ tailWord_36491) baseStart_36491 baseEnd_36491 := by
    simpa [prefixWord, tailWord_36491, baseEnd_36491] using wordTrace_append hprefix tailTrace_36491
  have hstable : (prefixWord ++ tailWord_36491).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36491).length < 2 ^ (prefixWord ++ tailWord_36491).sum := by decide
  have hdescent : baseEnd_36491 < baseStart_36491 := by decide
  rcases family_descends (prefixWord ++ tailWord_36491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36567 : List Nat := [1, 1, 3, 2, 1, 3, 1, 7]
def baseStart_36567 : Nat := 118140960795 + 36567 * 2 ^ 59
def prefixEnd_36567 : Nat := 4983230072969 + 3 ^ 40 * 36567 * 2
def baseEnd_36567 : Nat := 11126783462556246011459

theorem tailTrace_36567 : CollatzResearch.WordTrace tailWord_36567 prefixEnd_36567 11126783462556246011459 := by
  unfold tailWord_36567
  simp only [CollatzResearch.WordTrace]
  refine ⟨1333708058531478991507955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 889138705687652661005303 1333708058531478991507955)
  ·
    refine ⟨2000562087797218487261933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1333708058531478991507955 2000562087797218487261933)
    ·
      refine ⟨750210782923956932723225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2000562087797218487261933 750210782923956932723225)
      ·
        refine ⟨562658087192967699542419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 750210782923956932723225 562658087192967699542419)
        ·
          refine ⟨843987130789451549313629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 562658087192967699542419 843987130789451549313629)
          ·
            refine ⟨316495174046044330992611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 843987130789451549313629 316495174046044330992611)
            ·
              refine ⟨474742761069066496488917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 316495174046044330992611 474742761069066496488917)
              ·
                refine ⟨11126783462556246011459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 474742761069066496488917 11126783462556246011459)
                ·
                  rfl

theorem cell19_36567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 7].length) (baseStart_36567 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_36567 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_36567 prefixEnd_36567 := by exact prefixLift 36567
  have htrace : WordTrace (prefixWord ++ tailWord_36567) baseStart_36567 baseEnd_36567 := by
    simpa [prefixWord, tailWord_36567, baseEnd_36567] using wordTrace_append hprefix tailTrace_36567
  have hstable : (prefixWord ++ tailWord_36567).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36567).length < 2 ^ (prefixWord ++ tailWord_36567).sum := by decide
  have hdescent : baseEnd_36567 < baseStart_36567 := by decide
  rcases family_descends (prefixWord ++ tailWord_36567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36605 : List Nat := [1, 4, 1, 1, 1, 1, 2, 8]
def baseStart_36605 : Nat := 118140960795 + 36605 * 2 ^ 59
def prefixEnd_36605 : Nat := 4983230072969 + 3 ^ 40 * 36605 * 2
def baseEnd_36605 : Nat := 11138346286183417166911

theorem tailTrace_36605 : CollatzResearch.WordTrace tailWord_36605 prefixEnd_36605 11138346286183417166911 := by
  unfold tailWord_36605
  simp only [CollatzResearch.WordTrace]
  refine ⟨1335094032393811481391269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 890062688262540987594179 1335094032393811481391269)
  ·
    refine ⟨250330131073839652760863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1335094032393811481391269 250330131073839652760863)
    ·
      refine ⟨375495196610759479141295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 250330131073839652760863 375495196610759479141295)
      ·
        refine ⟨563242794916139218711943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 375495196610759479141295 563242794916139218711943)
        ·
          refine ⟨844864192374208828067915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 563242794916139218711943 844864192374208828067915)
          ·
            refine ⟨1267296288561313242101873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 844864192374208828067915 1267296288561313242101873)
            ·
              refine ⟨950472216420984931576405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1267296288561313242101873 950472216420984931576405)
              ·
                refine ⟨11138346286183417166911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 950472216420984931576405 11138346286183417166911)
                ·
                  rfl

theorem cell19_36605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 8].length) (baseStart_36605 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_36605 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_36605 prefixEnd_36605 := by exact prefixLift 36605
  have htrace : WordTrace (prefixWord ++ tailWord_36605) baseStart_36605 baseEnd_36605 := by
    simpa [prefixWord, tailWord_36605, baseEnd_36605] using wordTrace_append hprefix tailTrace_36605
  have hstable : (prefixWord ++ tailWord_36605).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36605).length < 2 ^ (prefixWord ++ tailWord_36605).sum := by decide
  have hdescent : baseEnd_36605 < baseStart_36605 := by decide
  rcases family_descends (prefixWord ++ tailWord_36605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36679 : List Nat := [1, 1, 4, 1, 2, 1, 6, 3]
def baseStart_36679 : Nat := 118140960795 + 36679 * 2 ^ 59
def prefixEnd_36679 : Nat := 4983230072969 + 3 ^ 40 * 36679 * 2
def baseEnd_36679 : Nat := 11160863363773171522265

theorem tailTrace_36679 : CollatzResearch.WordTrace tailWord_36679 prefixEnd_36679 11160863363773171522265 := by
  unfold tailWord_36679
  simp only [CollatzResearch.WordTrace]
  refine ⟨1337793034125722119585091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 891862022750481413056727 1337793034125722119585091)
  ·
    refine ⟨2006689551188583179377637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1337793034125722119585091 2006689551188583179377637)
    ·
      refine ⟨376254290847859346133307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2006689551188583179377637 376254290847859346133307)
      ·
        refine ⟨564381436271789019199961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 376254290847859346133307 564381436271789019199961)
        ·
          refine ⟨423286077203841764399971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 564381436271789019199961 423286077203841764399971)
          ·
            refine ⟨634929115805762646599957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 423286077203841764399971 634929115805762646599957)
            ·
              refine ⟨29762302303395124059373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 634929115805762646599957 29762302303395124059373)
              ·
                refine ⟨11160863363773171522265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29762302303395124059373 11160863363773171522265)
                ·
                  rfl

theorem cell19_36679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 6, 3].length) (baseStart_36679 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_36679 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_36679 prefixEnd_36679 := by exact prefixLift 36679
  have htrace : WordTrace (prefixWord ++ tailWord_36679) baseStart_36679 baseEnd_36679 := by
    simpa [prefixWord, tailWord_36679, baseEnd_36679] using wordTrace_append hprefix tailTrace_36679
  have hstable : (prefixWord ++ tailWord_36679).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36679).length < 2 ^ (prefixWord ++ tailWord_36679).sum := by decide
  have hdescent : baseEnd_36679 < baseStart_36679 := by decide
  rcases family_descends (prefixWord ++ tailWord_36679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36681 : List Nat := [1, 2, 1, 1, 2, 4, 3, 5]
def baseStart_36681 : Nat := 118140960795 + 36681 * 2 ^ 59
def prefixEnd_36681 : Nat := 4983230072969 + 3 ^ 40 * 36681 * 2
def baseEnd_36681 : Nat := 11161471933437759477815

theorem tailTrace_36681 : CollatzResearch.WordTrace tailWord_36681 prefixEnd_36681 11161471933437759477815 := by
  unfold tailWord_36681
  simp only [CollatzResearch.WordTrace]
  refine ⟨1337865980118476461157897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 891910653412317640771931 1337865980118476461157897)
  ·
    refine ⟨1003399485088857345868423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1337865980118476461157897 1003399485088857345868423)
    ·
      refine ⟨1505099227633286018802635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1003399485088857345868423 1505099227633286018802635)
      ·
        refine ⟨2257648841449929028203953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1505099227633286018802635 2257648841449929028203953)
        ·
          refine ⟨1693236631087446771152965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2257648841449929028203953 1693236631087446771152965)
          ·
            refine ⟨317481868328896269591181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1693236631087446771152965 317481868328896269591181)
            ·
              refine ⟨119055700623336101096693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 317481868328896269591181 119055700623336101096693)
              ·
                refine ⟨11161471933437759477815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 119055700623336101096693 11161471933437759477815)
                ·
                  rfl

theorem cell19_36681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 5].length) (baseStart_36681 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_36681 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_36681 prefixEnd_36681 := by exact prefixLift 36681
  have htrace : WordTrace (prefixWord ++ tailWord_36681) baseStart_36681 baseEnd_36681 := by
    simpa [prefixWord, tailWord_36681, baseEnd_36681] using wordTrace_append hprefix tailTrace_36681
  have hstable : (prefixWord ++ tailWord_36681).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36681).length < 2 ^ (prefixWord ++ tailWord_36681).sum := by decide
  have hdescent : baseEnd_36681 < baseStart_36681 := by decide
  rcases family_descends (prefixWord ++ tailWord_36681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36734 : List Nat := [4, 2, 3, 1, 1, 1, 2, 5]
def baseStart_36734 : Nat := 118140960795 + 36734 * 2 ^ 59
def prefixEnd_36734 : Nat := 4983230072969 + 3 ^ 40 * 36734 * 2
def baseEnd_36734 : Nat := 11177599029549340299893

theorem tailTrace_36734 : CollatzResearch.WordTrace tailWord_36734 prefixEnd_36734 11177599029549340299893 := by
  unfold tailWord_36734
  simp only [CollatzResearch.WordTrace]
  refine ⟨167474881115808314104657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 893199365950977675224837 167474881115808314104657)
  ·
    refine ⟨125606160836856235578493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167474881115808314104657 125606160836856235578493)
    ·
      refine ⟨47102310313821088341935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125606160836856235578493 47102310313821088341935)
      ·
        refine ⟨70653465470731632512903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47102310313821088341935 70653465470731632512903)
        ·
          refine ⟨105980198206097448769355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70653465470731632512903 105980198206097448769355)
          ·
            refine ⟨158970297309146173154033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105980198206097448769355 158970297309146173154033)
            ·
              refine ⟨119227722981859629865525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 158970297309146173154033 119227722981859629865525)
              ·
                refine ⟨11177599029549340299893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 119227722981859629865525 11177599029549340299893)
                ·
                  rfl

theorem cell19_36734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 5].length) (baseStart_36734 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_36734 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_36734 prefixEnd_36734 := by exact prefixLift 36734
  have htrace : WordTrace (prefixWord ++ tailWord_36734) baseStart_36734 baseEnd_36734 := by
    simpa [prefixWord, tailWord_36734, baseEnd_36734] using wordTrace_append hprefix tailTrace_36734
  have hstable : (prefixWord ++ tailWord_36734).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36734).length < 2 ^ (prefixWord ++ tailWord_36734).sum := by decide
  have hdescent : baseEnd_36734 < baseStart_36734 := by decide
  rcases family_descends (prefixWord ++ tailWord_36734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36770 : List Nat := [3, 3, 1, 2, 4, 1, 1, 4]
def baseStart_36770 : Nat := 118140960795 + 36770 * 2 ^ 59
def prefixEnd_36770 : Nat := 4983230072969 + 3 ^ 40 * 36770 * 2
def baseEnd_36770 : Nat := 11188553283511923499795

theorem tailTrace_36770 : CollatzResearch.WordTrace tailWord_36770 prefixEnd_36770 11188553283511923499795 := by
  unfold tailWord_36770
  simp only [CollatzResearch.WordTrace]
  refine ⟨335278019199011165286941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 894074717864029774098509 335278019199011165286941)
  ·
    refine ⟨125729257199629186982603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 335278019199011165286941 125729257199629186982603)
    ·
      refine ⟨188593885799443780473905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125729257199629186982603 188593885799443780473905)
      ·
        refine ⟨141445414349582835355429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 188593885799443780473905 141445414349582835355429)
        ·
          refine ⟨26521015190546781629143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 141445414349582835355429 26521015190546781629143)
          ·
            refine ⟨39781522785820172443715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26521015190546781629143 39781522785820172443715)
            ·
              refine ⟨59672284178730258665573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39781522785820172443715 59672284178730258665573)
              ·
                refine ⟨11188553283511923499795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59672284178730258665573 11188553283511923499795)
                ·
                  rfl

theorem cell19_36770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 1, 4].length) (baseStart_36770 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_36770 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_36770 prefixEnd_36770 := by exact prefixLift 36770
  have htrace : WordTrace (prefixWord ++ tailWord_36770) baseStart_36770 baseEnd_36770 := by
    simpa [prefixWord, tailWord_36770, baseEnd_36770] using wordTrace_append hprefix tailTrace_36770
  have hstable : (prefixWord ++ tailWord_36770).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36770).length < 2 ^ (prefixWord ++ tailWord_36770).sum := by decide
  have hdescent : baseEnd_36770 < baseStart_36770 := by decide
  rcases family_descends (prefixWord ++ tailWord_36770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36793 : List Nat := [1, 2, 1, 4, 2, 1, 5, 3]
def baseStart_36793 : Nat := 118140960795 + 36793 * 2 ^ 59
def prefixEnd_36793 : Nat := 4983230072969 + 3 ^ 40 * 36793 * 2
def baseEnd_36793 : Nat := 11195551834654684988621

theorem tailTrace_36793 : CollatzResearch.WordTrace tailWord_36793 prefixEnd_36793 11195551834654684988621 := by
  unfold tailWord_36793
  simp only [CollatzResearch.WordTrace]
  refine ⟨1341950955712719589235033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 894633970475146392823355 1341950955712719589235033)
  ·
    refine ⟨1006463216784539691926275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1341950955712719589235033 1006463216784539691926275)
    ·
      refine ⟨1509694825176809537889413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1006463216784539691926275 1509694825176809537889413)
      ·
        refine ⟨283067779720651788354265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1509694825176809537889413 283067779720651788354265)
        ·
          refine ⟨212300834790488841265699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 283067779720651788354265 212300834790488841265699)
          ·
            refine ⟨318451252185733261898549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 212300834790488841265699 318451252185733261898549)
            ·
              refine ⟨29854804892412493302989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 318451252185733261898549 29854804892412493302989)
              ·
                refine ⟨11195551834654684988621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29854804892412493302989 11195551834654684988621)
                ·
                  rfl

theorem cell19_36793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 5, 3].length) (baseStart_36793 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_36793 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_36793 prefixEnd_36793 := by exact prefixLift 36793
  have htrace : WordTrace (prefixWord ++ tailWord_36793) baseStart_36793 baseEnd_36793 := by
    simpa [prefixWord, tailWord_36793, baseEnd_36793] using wordTrace_append hprefix tailTrace_36793
  have hstable : (prefixWord ++ tailWord_36793).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36793).length < 2 ^ (prefixWord ++ tailWord_36793).sum := by decide
  have hdescent : baseEnd_36793 < baseStart_36793 := by decide
  rcases family_descends (prefixWord ++ tailWord_36793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36814 : List Nat := [4, 1, 1, 1, 2, 2, 8]
def baseStart_36814 : Nat := 118140960795 + 36814 * 2 ^ 59
def prefixEnd_36814 : Nat := 4983230072969 + 3 ^ 40 * 36814 * 2
def baseEnd_36814 : Nat := 3733980605377619507299

theorem tailTrace_36814 : CollatzResearch.WordTrace tailWord_36814 prefixEnd_36814 3733980605377619507299 := by
  unfold tailWord_36814
  simp only [CollatzResearch.WordTrace]
  refine ⟨167839611079580021968687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 895144592424426783832997 167839611079580021968687)
  ·
    refine ⟨251759416619370032953031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167839611079580021968687 251759416619370032953031)
    ·
      refine ⟨377639124929055049429547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 251759416619370032953031 377639124929055049429547)
      ·
        refine ⟨566458687393582574144321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 377639124929055049429547 566458687393582574144321)
        ·
          refine ⟨424844015545186930608241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 566458687393582574144321 424844015545186930608241)
          ·
            refine ⟨318633011658890197956181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 424844015545186930608241 318633011658890197956181)
            ·
              refine ⟨3733980605377619507299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 318633011658890197956181 3733980605377619507299)
              ·
                rfl

theorem cell19_36814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 8].length) (baseStart_36814 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_36814 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_36814 prefixEnd_36814 := by exact prefixLift 36814
  have htrace : WordTrace (prefixWord ++ tailWord_36814) baseStart_36814 baseEnd_36814 := by
    simpa [prefixWord, tailWord_36814, baseEnd_36814] using wordTrace_append hprefix tailTrace_36814
  have hstable : (prefixWord ++ tailWord_36814).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36814).length < 2 ^ (prefixWord ++ tailWord_36814).sum := by decide
  have hdescent : baseEnd_36814 < baseStart_36814 := by decide
  rcases family_descends (prefixWord ++ tailWord_36814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36871 : List Nat := [1, 1, 4, 3, 1, 2, 7]
def baseStart_36871 : Nat := 118140960795 + 36871 * 2 ^ 59
def prefixEnd_36871 : Nat := 4983230072969 + 3 ^ 40 * 36871 * 2
def baseEnd_36871 : Nat := 3739762017191205085025

theorem tailTrace_36871 : CollatzResearch.WordTrace tailWord_36871 prefixEnd_36871 3739762017191205085025 := by
  unfold tailWord_36871
  simp only [CollatzResearch.WordTrace]
  refine ⟨1344795849430138910574467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 896530566286759273716311 1344795849430138910574467)
  ·
    refine ⟨2017193774145208365861701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1344795849430138910574467 2017193774145208365861701)
    ·
      refine ⟨378223832652226568599069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2017193774145208365861701 378223832652226568599069)
      ·
        refine ⟨141833937244584963224651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 378223832652226568599069 141833937244584963224651)
        ·
          refine ⟨212750905866877444836977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141833937244584963224651 212750905866877444836977)
          ·
            refine ⟨159563179400158083627733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 212750905866877444836977 159563179400158083627733)
            ·
              refine ⟨3739762017191205085025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 159563179400158083627733 3739762017191205085025)
              ·
                rfl

theorem cell19_36871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 7].length) (baseStart_36871 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_36871 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_36871 prefixEnd_36871 := by exact prefixLift 36871
  have htrace : WordTrace (prefixWord ++ tailWord_36871) baseStart_36871 baseEnd_36871 := by
    simpa [prefixWord, tailWord_36871, baseEnd_36871] using wordTrace_append hprefix tailTrace_36871
  have hstable : (prefixWord ++ tailWord_36871).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36871).length < 2 ^ (prefixWord ++ tailWord_36871).sum := by decide
  have hdescent : baseEnd_36871 < baseStart_36871 := by decide
  rcases family_descends (prefixWord ++ tailWord_36871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36884 : List Nat := [2, 4, 3, 2, 1, 1, 2, 4]
def baseStart_36884 : Nat := 118140960795 + 36884 * 2 ^ 59
def prefixEnd_36884 : Nat := 4983230072969 + 3 ^ 40 * 36884 * 2
def baseEnd_36884 : Nat := 11223241754393436966151

theorem tailTrace_36884 : CollatzResearch.WordTrace tailWord_36884 prefixEnd_36884 11223241754393436966151 := by
  unfold tailWord_36884
  simp only [CollatzResearch.WordTrace]
  refine ⟨672634999191521065398853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 896846665588694753865137 672634999191521065398853)
  ·
    refine ⟨126119062348410199762285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 672634999191521065398853 126119062348410199762285)
    ·
      refine ⟨47294648380653824910857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126119062348410199762285 47294648380653824910857)
      ·
        refine ⟨35470986285490368683143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47294648380653824910857 35470986285490368683143)
        ·
          refine ⟨53206479428235553024715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35470986285490368683143 53206479428235553024715)
          ·
            refine ⟨79809719142353329537073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53206479428235553024715 79809719142353329537073)
            ·
              refine ⟨59857289356764997152805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79809719142353329537073 59857289356764997152805)
              ·
                refine ⟨11223241754393436966151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59857289356764997152805 11223241754393436966151)
                ·
                  rfl

theorem cell19_36884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 2, 4].length) (baseStart_36884 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_36884 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_36884 prefixEnd_36884 := by exact prefixLift 36884
  have htrace : WordTrace (prefixWord ++ tailWord_36884) baseStart_36884 baseEnd_36884 := by
    simpa [prefixWord, tailWord_36884, baseEnd_36884] using wordTrace_append hprefix tailTrace_36884
  have hstable : (prefixWord ++ tailWord_36884).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36884).length < 2 ^ (prefixWord ++ tailWord_36884).sum := by decide
  have hdescent : baseEnd_36884 < baseStart_36884 := by decide
  rcases family_descends (prefixWord ++ tailWord_36884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36890 : List Nat := [3, 1, 1, 3, 1, 3, 1, 6]
def baseStart_36890 : Nat := 118140960795 + 36890 * 2 ^ 59
def prefixEnd_36890 : Nat := 4983230072969 + 3 ^ 40 * 36890 * 2
def baseEnd_36890 : Nat := 11225067463387200832801

theorem tailTrace_36890 : CollatzResearch.WordTrace tailWord_36890 prefixEnd_36890 11225067463387200832801 := by
  unfold tailWord_36890
  simp only [CollatzResearch.WordTrace]
  refine ⟨336372209090326288879031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 896992557574203437010749 336372209090326288879031)
  ·
    refine ⟨504558313635489433318547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 336372209090326288879031 504558313635489433318547)
    ·
      refine ⟨756837470453234149977821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 504558313635489433318547 756837470453234149977821)
      ·
        refine ⟨283814051419962806241683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 756837470453234149977821 283814051419962806241683)
        ·
          refine ⟨425721077129944209362525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 283814051419962806241683 425721077129944209362525)
          ·
            refine ⟨159645403923729078510947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 425721077129944209362525 159645403923729078510947)
            ·
              refine ⟨239468105885593617766421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 159645403923729078510947 239468105885593617766421)
              ·
                refine ⟨11225067463387200832801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 239468105885593617766421 11225067463387200832801)
                ·
                  rfl

theorem cell19_36890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 6].length) (baseStart_36890 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_36890 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_36890 prefixEnd_36890 := by exact prefixLift 36890
  have htrace : WordTrace (prefixWord ++ tailWord_36890) baseStart_36890 baseEnd_36890 := by
    simpa [prefixWord, tailWord_36890, baseEnd_36890] using wordTrace_append hprefix tailTrace_36890
  have hstable : (prefixWord ++ tailWord_36890).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36890).length < 2 ^ (prefixWord ++ tailWord_36890).sum := by decide
  have hdescent : baseEnd_36890 < baseStart_36890 := by decide
  rcases family_descends (prefixWord ++ tailWord_36890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36926 : List Nat := [4, 2, 1, 3, 2, 7]
def baseStart_36926 : Nat := 118140960795 + 36926 * 2 ^ 59
def prefixEnd_36926 : Nat := 4983230072969 + 3 ^ 40 * 36926 * 2
def baseEnd_36926 : Nat := 1248446857483309336967

theorem tailTrace_36926 : CollatzResearch.WordTrace tailWord_36926 prefixEnd_36926 1248446857483309336967 := by
  unfold tailWord_36926
  simp only [CollatzResearch.WordTrace]
  refine ⟨168350233028860412978329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 897867909487255535884421 168350233028860412978329)
  ·
    refine ⟨126262674771645309733747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168350233028860412978329 126262674771645309733747)
    ·
      refine ⟨189394012157467964600621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126262674771645309733747 189394012157467964600621)
      ·
        refine ⟨71022754559050486725233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 189394012157467964600621 71022754559050486725233)
        ·
          refine ⟨53267065919287865043925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71022754559050486725233 53267065919287865043925)
          ·
            refine ⟨1248446857483309336967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 53267065919287865043925 1248446857483309336967)
            ·
              rfl

theorem cell19_36926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 7].length) (baseStart_36926 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_36926 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_36926 prefixEnd_36926 := by exact prefixLift 36926
  have htrace : WordTrace (prefixWord ++ tailWord_36926) baseStart_36926 baseEnd_36926 := by
    simpa [prefixWord, tailWord_36926, baseEnd_36926] using wordTrace_append hprefix tailTrace_36926
  have hstable : (prefixWord ++ tailWord_36926).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36926).length < 2 ^ (prefixWord ++ tailWord_36926).sum := by decide
  have hdescent : baseEnd_36926 < baseStart_36926 := by decide
  rcases family_descends (prefixWord ++ tailWord_36926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36958 : List Nat := [4, 4, 1, 1, 2, 1, 3, 3]
def baseStart_36958 : Nat := 118140960795 + 36958 * 2 ^ 59
def prefixEnd_36958 : Nat := 4983230072969 + 3 ^ 40 * 36958 * 2
def baseEnd_36958 : Nat := 11245758831983191321505

theorem tailTrace_36958 : CollatzResearch.WordTrace tailWord_36958 prefixEnd_36958 11245758831983191321505 := by
  unfold tailWord_36958
  simp only [CollatzResearch.WordTrace]
  refine ⟨168496125014369096123941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 898646000076635179327685 168496125014369096123941)
  ·
    refine ⟨31593023440194205523239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 168496125014369096123941 31593023440194205523239)
    ·
      refine ⟨47389535160291308284859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31593023440194205523239 47389535160291308284859)
      ·
        refine ⟨71084302740436962427289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47389535160291308284859 71084302740436962427289)
        ·
          refine ⟨53313227055327721820467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71084302740436962427289 53313227055327721820467)
          ·
            refine ⟨79969840582991582730701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53313227055327721820467 79969840582991582730701)
            ·
              refine ⟨29988690218621843524013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79969840582991582730701 29988690218621843524013)
              ·
                refine ⟨11245758831983191321505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29988690218621843524013 11245758831983191321505)
                ·
                  rfl

theorem cell19_36958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 3, 3].length) (baseStart_36958 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_36958 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_36958 prefixEnd_36958 := by exact prefixLift 36958
  have htrace : WordTrace (prefixWord ++ tailWord_36958) baseStart_36958 baseEnd_36958 := by
    simpa [prefixWord, tailWord_36958, baseEnd_36958] using wordTrace_append hprefix tailTrace_36958
  have hstable : (prefixWord ++ tailWord_36958).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36958).length < 2 ^ (prefixWord ++ tailWord_36958).sum := by decide
  have hdescent : baseEnd_36958 < baseStart_36958 := by decide
  rcases family_descends (prefixWord ++ tailWord_36958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36985 : List Nat := [1, 2, 1, 3, 4, 2, 6]
def baseStart_36985 : Nat := 118140960795 + 36985 * 2 ^ 59
def prefixEnd_36985 : Nat := 4983230072969 + 3 ^ 40 * 36985 * 2
def baseEnd_36985 : Nat := 3751324840818376240477

theorem tailTrace_36985 : CollatzResearch.WordTrace tailWord_36985 prefixEnd_36985 3751324840818376240477 := by
  unfold tailWord_36985
  simp only [CollatzResearch.WordTrace]
  refine ⟨1348953771017136380224409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 899302514011424253482939 1348953771017136380224409)
  ·
    refine ⟨1011715328262852285168307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1348953771017136380224409 1011715328262852285168307)
    ·
      refine ⟨1517572992394278427752461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1011715328262852285168307 1517572992394278427752461)
      ·
        refine ⟨569089872147854410407173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1517572992394278427752461 569089872147854410407173)
        ·
          refine ⟨106704351027722701951345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 569089872147854410407173 106704351027722701951345)
          ·
            refine ⟨80028263270792026463509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106704351027722701951345 80028263270792026463509)
            ·
              refine ⟨3751324840818376240477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 80028263270792026463509 3751324840818376240477)
              ·
                rfl

theorem cell19_36985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 6].length) (baseStart_36985 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_36985 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_36985 prefixEnd_36985 := by exact prefixLift 36985
  have htrace : WordTrace (prefixWord ++ tailWord_36985) baseStart_36985 baseEnd_36985 := by
    simpa [prefixWord, tailWord_36985, baseEnd_36985] using wordTrace_append hprefix tailTrace_36985
  have hstable : (prefixWord ++ tailWord_36985).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36985).length < 2 ^ (prefixWord ++ tailWord_36985).sum := by decide
  have hdescent : baseEnd_36985 < baseStart_36985 := by decide
  rcases family_descends (prefixWord ++ tailWord_36985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37021 : List Nat := [1, 4, 2, 1, 1, 3, 4, 3]
def baseStart_37021 : Nat := 118140960795 + 37021 * 2 ^ 59
def prefixEnd_37021 : Nat := 4983230072969 + 3 ^ 40 * 37021 * 2
def baseEnd_37021 : Nat := 11264928776417711921333

theorem tailTrace_37021 : CollatzResearch.WordTrace tailWord_37021 prefixEnd_37021 11264928776417711921333 := by
  unfold tailWord_37021
  simp only [CollatzResearch.WordTrace]
  refine ⟨1350266798886714528534917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 900177865924476352356611 1350266798886714528534917)
  ·
    refine ⟨253175024791258974100297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1350266798886714528534917 253175024791258974100297)
    ·
      refine ⟨189881268593444230575223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 253175024791258974100297 189881268593444230575223)
      ·
        refine ⟨284821902890166345862835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189881268593444230575223 284821902890166345862835)
        ·
          refine ⟨427232854335249518794253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 284821902890166345862835 427232854335249518794253)
          ·
            refine ⟨160212320375718569547845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 427232854335249518794253 160212320375718569547845)
            ·
              refine ⟨30039810070447231790221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 160212320375718569547845 30039810070447231790221)
              ·
                refine ⟨11264928776417711921333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30039810070447231790221 11264928776417711921333)
                ·
                  rfl

theorem cell19_37021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 4, 3].length) (baseStart_37021 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_37021 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_37021 prefixEnd_37021 := by exact prefixLift 37021
  have htrace : WordTrace (prefixWord ++ tailWord_37021) baseStart_37021 baseEnd_37021 := by
    simpa [prefixWord, tailWord_37021, baseEnd_37021] using wordTrace_append hprefix tailTrace_37021
  have hstable : (prefixWord ++ tailWord_37021).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37021).length < 2 ^ (prefixWord ++ tailWord_37021).sum := by decide
  have hdescent : baseEnd_37021 < baseStart_37021 := by decide
  rcases family_descends (prefixWord ++ tailWord_37021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37057 : List Nat := [1, 2, 6, 1, 2, 1, 2, 4]
def baseStart_37057 : Nat := 118140960795 + 37057 * 2 ^ 59
def prefixEnd_37057 : Nat := 4983230072969 + 3 ^ 40 * 37057 * 2
def baseEnd_37057 : Nat := 11275883030380295121235

theorem tailTrace_37057 : CollatzResearch.WordTrace tailWord_37057 prefixEnd_37057 11275883030380295121235 := by
  unfold tailWord_37057
  simp only [CollatzResearch.WordTrace]
  refine ⟨1351579826756292676845425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 901053217837528451230283 1351579826756292676845425)
  ·
    refine ⟨1013684870067219507634069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1351579826756292676845425 1013684870067219507634069)
    ·
      refine ⟨47516478284400914420347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 1013684870067219507634069 47516478284400914420347)
      ·
        refine ⟨71274717426601371630521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47516478284400914420347 71274717426601371630521)
        ·
          refine ⟨53456038069951028722891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71274717426601371630521 53456038069951028722891)
          ·
            refine ⟨80184057104926543084337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53456038069951028722891 80184057104926543084337)
            ·
              refine ⟨60138042828694907313253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80184057104926543084337 60138042828694907313253)
              ·
                refine ⟨11275883030380295121235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60138042828694907313253 11275883030380295121235)
                ·
                  rfl

theorem cell19_37057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 2, 4].length) (baseStart_37057 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_37057 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_37057 prefixEnd_37057 := by exact prefixLift 37057
  have htrace : WordTrace (prefixWord ++ tailWord_37057) baseStart_37057 baseEnd_37057 := by
    simpa [prefixWord, tailWord_37057, baseEnd_37057] using wordTrace_append hprefix tailTrace_37057
  have hstable : (prefixWord ++ tailWord_37057).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37057).length < 2 ^ (prefixWord ++ tailWord_37057).sum := by decide
  have hdescent : baseEnd_37057 < baseStart_37057 := by decide
  rcases family_descends (prefixWord ++ tailWord_37057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37080 : List Nat := [2, 1, 2, 2, 4, 1, 2, 5]
def baseStart_37080 : Nat := 118140960795 + 37080 * 2 ^ 59
def prefixEnd_37080 : Nat := 4983230072969 + 3 ^ 40 * 37080 * 2
def baseEnd_37080 : Nat := 11282881581523056610061

theorem tailTrace_37080 : CollatzResearch.WordTrace tailWord_37080 prefixEnd_37080 11282881581523056610061 := by
  unfold tailWord_37080
  simp only [CollatzResearch.WordTrace]
  refine ⟨676209352836483802466347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 901612470448645069955129 676209352836483802466347)
  ·
    refine ⟨1014314029254725703699521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 676209352836483802466347 1014314029254725703699521)
    ·
      refine ⟨760735521941044277774641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1014314029254725703699521 760735521941044277774641)
      ·
        refine ⟨570551641455783208330981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 760735521941044277774641 570551641455783208330981)
        ·
          refine ⟨106978432772959351562059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 570551641455783208330981 106978432772959351562059)
          ·
            refine ⟨160467649159439027343089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106978432772959351562059 160467649159439027343089)
            ·
              refine ⟨120350736869579270507317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 160467649159439027343089 120350736869579270507317)
              ·
                refine ⟨11282881581523056610061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 120350736869579270507317 11282881581523056610061)
                ·
                  rfl

theorem cell19_37080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 5].length) (baseStart_37080 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_37080 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_37080 prefixEnd_37080 := by exact prefixLift 37080
  have htrace : WordTrace (prefixWord ++ tailWord_37080) baseStart_37080 baseEnd_37080 := by
    simpa [prefixWord, tailWord_37080, baseEnd_37080] using wordTrace_append hprefix tailTrace_37080
  have hstable : (prefixWord ++ tailWord_37080).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37080).length < 2 ^ (prefixWord ++ tailWord_37080).sum := by decide
  have hdescent : baseEnd_37080 < baseStart_37080 := by decide
  rcases family_descends (prefixWord ++ tailWord_37080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37116 : List Nat := [2, 2, 2, 1, 4, 3, 1, 4]
def baseStart_37116 : Nat := 118140960795 + 37116 * 2 ^ 59
def prefixEnd_37116 : Nat := 4983230072969 + 3 ^ 40 * 37116 * 2
def baseEnd_37116 : Nat := 11293835835485639809963

theorem tailTrace_37116 : CollatzResearch.WordTrace tailWord_37116 prefixEnd_37116 11293835835485639809963 := by
  unfold tailWord_37116
  simp only [CollatzResearch.WordTrace]
  refine ⟨676865866771272876621601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 902487822361697168828801 676865866771272876621601)
  ·
    refine ⟨507649400078454657466201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 676865866771272876621601 507649400078454657466201)
    ·
      refine ⟨380737050058840993099651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 507649400078454657466201 380737050058840993099651)
      ·
        refine ⟨571105575088261489649477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 380737050058840993099651 571105575088261489649477)
        ·
          refine ⟨107082295329049029309277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 571105575088261489649477 107082295329049029309277)
          ·
            refine ⟨40155860748393385990979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 107082295329049029309277 40155860748393385990979)
            ·
              refine ⟨60233791122590078986469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40155860748393385990979 60233791122590078986469)
              ·
                refine ⟨11293835835485639809963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60233791122590078986469 11293835835485639809963)
                ·
                  rfl

theorem cell19_37116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 1, 4].length) (baseStart_37116 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_37116 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_37116 prefixEnd_37116 := by exact prefixLift 37116
  have htrace : WordTrace (prefixWord ++ tailWord_37116) baseStart_37116 baseEnd_37116 := by
    simpa [prefixWord, tailWord_37116, baseEnd_37116] using wordTrace_append hprefix tailTrace_37116
  have hstable : (prefixWord ++ tailWord_37116).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37116).length < 2 ^ (prefixWord ++ tailWord_37116).sum := by decide
  have hdescent : baseEnd_37116 < baseStart_37116 := by decide
  rcases family_descends (prefixWord ++ tailWord_37116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37139 : List Nat := [1, 1, 1, 2, 1, 3, 1, 9]
def baseStart_37139 : Nat := 118140960795 + 37139 * 2 ^ 59
def prefixEnd_37139 : Nat := 4983230072969 + 3 ^ 40 * 37139 * 2
def baseEnd_37139 : Nat := 11300834386628401298789

theorem tailTrace_37139 : CollatzResearch.WordTrace tailWord_37139 prefixEnd_37139 11300834386628401298789 := by
  unfold tailWord_37139
  simp only [CollatzResearch.WordTrace]
  refine ⟨1354570612459220681330471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 903047074972813787553647 1354570612459220681330471)
  ·
    refine ⟨2031855918688831021995707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1354570612459220681330471 2031855918688831021995707)
    ·
      refine ⟨3047783878033246532993561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2031855918688831021995707 3047783878033246532993561)
      ·
        refine ⟨2285837908524934899745171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3047783878033246532993561 2285837908524934899745171)
        ·
          refine ⟨3428756862787402349617757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2285837908524934899745171 3428756862787402349617757)
          ·
            refine ⟨1285783823545275881106659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3428756862787402349617757 1285783823545275881106659)
            ·
              refine ⟨1928675735317913821659989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1285783823545275881106659 1928675735317913821659989)
              ·
                refine ⟨11300834386628401298789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1928675735317913821659989 11300834386628401298789)
                ·
                  rfl

theorem cell19_37139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 9].length) (baseStart_37139 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_37139 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_37139 prefixEnd_37139 := by exact prefixLift 37139
  have htrace : WordTrace (prefixWord ++ tailWord_37139) baseStart_37139 baseEnd_37139 := by
    simpa [prefixWord, tailWord_37139, baseEnd_37139] using wordTrace_append hprefix tailTrace_37139
  have hstable : (prefixWord ++ tailWord_37139).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37139).length < 2 ^ (prefixWord ++ tailWord_37139).sum := by decide
  have hdescent : baseEnd_37139 < baseStart_37139 := by decide
  rcases family_descends (prefixWord ++ tailWord_37139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37156 : List Nat := [2, 3, 1, 3, 1, 3, 6]
def baseStart_37156 : Nat := 118140960795 + 37156 * 2 ^ 59
def prefixEnd_37156 : Nat := 4983230072969 + 3 ^ 40 * 37156 * 2
def baseEnd_37156 : Nat := 3768669076259132973655

theorem tailTrace_37156 : CollatzResearch.WordTrace tailWord_37156 prefixEnd_37156 3768669076259132973655 := by
  unfold tailWord_37156
  simp only [CollatzResearch.WordTrace]
  refine ⟨677595326698816292349661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 903460435598421723132881 677595326698816292349661)
  ·
    refine ⟨254098247512056109631123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 677595326698816292349661 254098247512056109631123)
    ·
      refine ⟨381147371268084164446685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 254098247512056109631123 381147371268084164446685)
      ·
        refine ⟨142930264225531561667507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 381147371268084164446685 142930264225531561667507)
        ·
          refine ⟨214395396338297342501261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142930264225531561667507 214395396338297342501261)
          ·
            refine ⟨80398273626861503437973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 214395396338297342501261 80398273626861503437973)
            ·
              refine ⟨3768669076259132973655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 80398273626861503437973 3768669076259132973655)
              ·
                rfl

theorem cell19_37156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 6].length) (baseStart_37156 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_37156 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_37156 prefixEnd_37156 := by exact prefixLift 37156
  have htrace : WordTrace (prefixWord ++ tailWord_37156) baseStart_37156 baseEnd_37156 := by
    simpa [prefixWord, tailWord_37156, baseEnd_37156] using wordTrace_append hprefix tailTrace_37156
  have hstable : (prefixWord ++ tailWord_37156).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37156).length < 2 ^ (prefixWord ++ tailWord_37156).sum := by decide
  have hdescent : baseEnd_37156 < baseStart_37156 := by decide
  rcases family_descends (prefixWord ++ tailWord_37156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37188 : List Nat := [2, 3, 4, 1, 2, 2, 2, 3]
def baseStart_37188 : Nat := 118140960795 + 37188 * 2 ^ 59
def prefixEnd_37188 : Nat := 4983230072969 + 3 ^ 40 * 37188 * 2
def baseEnd_37188 : Nat := 11315744343410806209767

theorem tailTrace_37188 : CollatzResearch.WordTrace tailWord_37188 prefixEnd_37188 11315744343410806209767 := by
  unfold tailWord_37188
  simp only [CollatzResearch.WordTrace]
  refine ⟨678178894640851024932109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 904238526187801366576145 678178894640851024932109)
  ·
    refine ⟨254317085490319134349541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 678178894640851024932109 254317085490319134349541)
    ·
      refine ⟨47684453529434837690539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 254317085490319134349541 47684453529434837690539)
      ·
        refine ⟨71526680294152256535809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47684453529434837690539 71526680294152256535809)
        ·
          refine ⟨53645010220614192401857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71526680294152256535809 53645010220614192401857)
          ·
            refine ⟨40233757665460644301393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53645010220614192401857 40233757665460644301393)
            ·
              refine ⟨30175318249095483226045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40233757665460644301393 30175318249095483226045)
              ·
                refine ⟨11315744343410806209767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30175318249095483226045 11315744343410806209767)
                ·
                  rfl

theorem cell19_37188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 2, 3].length) (baseStart_37188 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_37188 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_37188 prefixEnd_37188 := by exact prefixLift 37188
  have htrace : WordTrace (prefixWord ++ tailWord_37188) baseStart_37188 baseEnd_37188 := by
    simpa [prefixWord, tailWord_37188, baseEnd_37188] using wordTrace_append hprefix tailTrace_37188
  have hstable : (prefixWord ++ tailWord_37188).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37188).length < 2 ^ (prefixWord ++ tailWord_37188).sum := by decide
  have hdescent : baseEnd_37188 < baseStart_37188 := by decide
  rcases family_descends (prefixWord ++ tailWord_37188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37215 : List Nat := [1, 1, 2, 3, 1, 2, 9]
def baseStart_37215 : Nat := 118140960795 + 37215 * 2 ^ 59
def prefixEnd_37215 : Nat := 4983230072969 + 3 ^ 40 * 37215 * 2
def baseEnd_37215 : Nat := 3774653344627581203231

theorem tailTrace_37215 : CollatzResearch.WordTrace tailWord_37215 prefixEnd_37215 3774653344627581203231 := by
  unfold tailWord_37215
  simp only [CollatzResearch.WordTrace]
  refine ⟨1357342560183885661097099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 904895040122590440731399 1357342560183885661097099)
  ·
    refine ⟨2036013840275828491645649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1357342560183885661097099 2036013840275828491645649)
    ·
      refine ⟨1527010380206871368734237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2036013840275828491645649 1527010380206871368734237)
      ·
        refine ⟨572628892577576763275339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1527010380206871368734237 572628892577576763275339)
        ·
          refine ⟨858943338866365144913009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 572628892577576763275339 858943338866365144913009)
          ·
            refine ⟨644207504149773858684757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 858943338866365144913009 644207504149773858684757)
            ·
              refine ⟨3774653344627581203231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 644207504149773858684757 3774653344627581203231)
              ·
                rfl

theorem cell19_37215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 9].length) (baseStart_37215 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_37215 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_37215 prefixEnd_37215 := by exact prefixLift 37215
  have htrace : WordTrace (prefixWord ++ tailWord_37215) baseStart_37215 baseEnd_37215 := by
    simpa [prefixWord, tailWord_37215, baseEnd_37215] using wordTrace_append hprefix tailTrace_37215
  have hstable : (prefixWord ++ tailWord_37215).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37215).length < 2 ^ (prefixWord ++ tailWord_37215).sum := by decide
  have hdescent : baseEnd_37215 < baseStart_37215 := by decide
  rcases family_descends (prefixWord ++ tailWord_37215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37232 : List Nat := [2, 1, 1, 1, 4, 4, 2, 4]
def baseStart_37232 : Nat := 118140960795 + 37232 * 2 ^ 59
def prefixEnd_37232 : Nat := 4983230072969 + 3 ^ 40 * 37232 * 2
def baseEnd_37232 : Nat := 11329132876031741231869

theorem tailTrace_37232 : CollatzResearch.WordTrace tailWord_37232 prefixEnd_37232 11329132876031741231869 := by
  unfold tailWord_37232
  simp only [CollatzResearch.WordTrace]
  refine ⟨678981300561148782232975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 905308400748198376310633 678981300561148782232975)
  ·
    refine ⟨1018471950841723173349463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 678981300561148782232975 1018471950841723173349463)
    ·
      refine ⟨1527707926262584760024195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1018471950841723173349463 1527707926262584760024195)
      ·
        refine ⟨2291561889393877140036293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1527707926262584760024195 2291561889393877140036293)
        ·
          refine ⟨429667854261351963756805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2291561889393877140036293 429667854261351963756805)
          ·
            refine ⟨80562722674003493204401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 429667854261351963756805 80562722674003493204401)
            ·
              refine ⟨60422042005502619903301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80562722674003493204401 60422042005502619903301)
              ·
                refine ⟨11329132876031741231869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60422042005502619903301 11329132876031741231869)
                ·
                  rfl

theorem cell19_37232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 2, 4].length) (baseStart_37232 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_37232 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_37232 prefixEnd_37232 := by exact prefixLift 37232
  have htrace : WordTrace (prefixWord ++ tailWord_37232) baseStart_37232 baseEnd_37232 := by
    simpa [prefixWord, tailWord_37232, baseEnd_37232] using wordTrace_append hprefix tailTrace_37232
  have hstable : (prefixWord ++ tailWord_37232).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37232).length < 2 ^ (prefixWord ++ tailWord_37232).sum := by decide
  have hdescent : baseEnd_37232 < baseStart_37232 := by decide
  rcases family_descends (prefixWord ++ tailWord_37232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37268 : List Nat := [2, 4, 2, 1, 4, 6]
def baseStart_37268 : Nat := 118140960795 + 37268 * 2 ^ 59
def prefixEnd_37268 : Nat := 4983230072969 + 3 ^ 40 * 37268 * 2
def baseEnd_37268 : Nat := 1260009681110480492419

theorem tailTrace_37268 : CollatzResearch.WordTrace tailWord_37268 prefixEnd_37268 1260009681110480492419 := by
  unfold tailWord_37268
  simp only [CollatzResearch.WordTrace]
  refine ⟨679637814495937856388229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 906183752661250475184305 679637814495937856388229)
  ·
    refine ⟨127432090217988348072793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 679637814495937856388229 127432090217988348072793)
    ·
      refine ⟨95574067663491261054595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127432090217988348072793 95574067663491261054595)
      ·
        refine ⟨143361101495236891581893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95574067663491261054595 143361101495236891581893)
        ·
          refine ⟨26880206530356917171605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 143361101495236891581893 26880206530356917171605)
          ·
            refine ⟨1260009681110480492419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 26880206530356917171605 1260009681110480492419)
            ·
              rfl

theorem cell19_37268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 6].length) (baseStart_37268 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_37268 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_37268 prefixEnd_37268 := by exact prefixLift 37268
  have htrace : WordTrace (prefixWord ++ tailWord_37268) baseStart_37268 baseEnd_37268 := by
    simpa [prefixWord, tailWord_37268, baseEnd_37268] using wordTrace_append hprefix tailTrace_37268
  have hstable : (prefixWord ++ tailWord_37268).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37268).length < 2 ^ (prefixWord ++ tailWord_37268).sum := by decide
  have hdescent : baseEnd_37268 < baseStart_37268 := by decide
  rcases family_descends (prefixWord ++ tailWord_37268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37287 : List Nat := [1, 1, 6, 1, 1, 4, 1, 4]
def baseStart_37287 : Nat := 118140960795 + 37287 * 2 ^ 59
def prefixEnd_37287 : Nat := 4983230072969 + 3 ^ 40 * 37287 * 2
def baseEnd_37287 : Nat := 11345868541807910009497

theorem tailTrace_37287 : CollatzResearch.WordTrace tailWord_37287 prefixEnd_37287 11345868541807910009497 := by
  unfold tailWord_37287
  simp only [CollatzResearch.WordTrace]
  refine ⟨1359968615923041957718115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 906645743948694638478743 1359968615923041957718115)
  ·
    refine ⟨2039952923884562936577173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1359968615923041957718115 2039952923884562936577173)
    ·
      refine ⟨95622793307088887652055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 2039952923884562936577173 95622793307088887652055)
      ·
        refine ⟨143434189960633331478083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95622793307088887652055 143434189960633331478083)
        ·
          refine ⟨215151284940949997217125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143434189960633331478083 215151284940949997217125)
          ·
            refine ⟨40340865926428124478211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 215151284940949997217125 40340865926428124478211)
            ·
              refine ⟨60511298889642186717317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40340865926428124478211 60511298889642186717317)
              ·
                refine ⟨11345868541807910009497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60511298889642186717317 11345868541807910009497)
                ·
                  rfl

theorem cell19_37287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 1, 4].length) (baseStart_37287 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_37287 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_37287 prefixEnd_37287 := by exact prefixLift 37287
  have htrace : WordTrace (prefixWord ++ tailWord_37287) baseStart_37287 baseEnd_37287 := by
    simpa [prefixWord, tailWord_37287, baseEnd_37287] using wordTrace_append hprefix tailTrace_37287
  have hstable : (prefixWord ++ tailWord_37287).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37287).length < 2 ^ (prefixWord ++ tailWord_37287).sum := by decide
  have hdescent : baseEnd_37287 < baseStart_37287 := by decide
  rcases family_descends (prefixWord ++ tailWord_37287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37424 : List Nat := [2, 1, 1, 1, 2, 3, 4, 5]
def baseStart_37424 : Nat := 118140960795 + 37424 * 2 ^ 59
def prefixEnd_37424 : Nat := 4983230072969 + 3 ^ 40 * 37424 * 2
def baseEnd_37424 : Nat := 11387555563832184964679

theorem tailTrace_37424 : CollatzResearch.WordTrace tailWord_37424 prefixEnd_37424 11387555563832184964679 := by
  unfold tailWord_37424
  simp only [CollatzResearch.WordTrace]
  refine ⟨682482708213357177727663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 909976944284476236970217 682482708213357177727663)
  ·
    refine ⟨1023724062320035766591495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 682482708213357177727663 1023724062320035766591495)
    ·
      refine ⟨1535586093480053649887243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1023724062320035766591495 1535586093480053649887243)
      ·
        refine ⟨2303379140220080474830865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1535586093480053649887243 2303379140220080474830865)
        ·
          refine ⟨1727534355165060356123149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2303379140220080474830865 1727534355165060356123149)
          ·
            refine ⟨647825383186897633546181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1727534355165060356123149 647825383186897633546181)
            ·
              refine ⟨121467259347543306289909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 647825383186897633546181 121467259347543306289909)
              ·
                refine ⟨11387555563832184964679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 121467259347543306289909 11387555563832184964679)
                ·
                  rfl

theorem cell19_37424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 5].length) (baseStart_37424 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_37424 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_37424 prefixEnd_37424 := by exact prefixLift 37424
  have htrace : WordTrace (prefixWord ++ tailWord_37424) baseStart_37424 baseEnd_37424 := by
    simpa [prefixWord, tailWord_37424, baseEnd_37424] using wordTrace_append hprefix tailTrace_37424
  have hstable : (prefixWord ++ tailWord_37424).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37424).length < 2 ^ (prefixWord ++ tailWord_37424).sum := by decide
  have hdescent : baseEnd_37424 < baseStart_37424 := by decide
  rcases family_descends (prefixWord ++ tailWord_37424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37460 : List Nat := [2, 4, 1, 1, 1, 3, 3, 4]
def baseStart_37460 : Nat := 118140960795 + 37460 * 2 ^ 59
def prefixEnd_37460 : Nat := 4983230072969 + 3 ^ 40 * 37460 * 2
def baseEnd_37460 : Nat := 11398509817794768164581

theorem tailTrace_37460 : CollatzResearch.WordTrace tailWord_37460 prefixEnd_37460 11398509817794768164581 := by
  unfold tailWord_37460
  simp only [CollatzResearch.WordTrace]
  refine ⟨683139222148146251882917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 910852296197528335843889 683139222148146251882917)
  ·
    refine ⟨128088604152777422228047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 683139222148146251882917 128088604152777422228047)
    ·
      refine ⟨192132906229166133342071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128088604152777422228047 192132906229166133342071)
      ·
        refine ⟨288199359343749200013107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192132906229166133342071 288199359343749200013107)
        ·
          refine ⟨432299039015623800019661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 288199359343749200013107 432299039015623800019661)
          ·
            refine ⟨162112139630858925007373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 432299039015623800019661 162112139630858925007373)
            ·
              refine ⟨60792052361572096877765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 162112139630858925007373 60792052361572096877765)
              ·
                refine ⟨11398509817794768164581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60792052361572096877765 11398509817794768164581)
                ·
                  rfl

theorem cell19_37460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 3, 4].length) (baseStart_37460 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_37460 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_37460 prefixEnd_37460 := by exact prefixLift 37460
  have htrace : WordTrace (prefixWord ++ tailWord_37460) baseStart_37460 baseEnd_37460 := by
    simpa [prefixWord, tailWord_37460, baseEnd_37460] using wordTrace_append hprefix tailTrace_37460
  have hstable : (prefixWord ++ tailWord_37460).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37460).length < 2 ^ (prefixWord ++ tailWord_37460).sum := by decide
  have hdescent : baseEnd_37460 < baseStart_37460 := by decide
  rcases family_descends (prefixWord ++ tailWord_37460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37477 : List Nat := [1, 3, 1, 3, 4, 1, 3, 3]
def baseStart_37477 : Nat := 118140960795 + 37477 * 2 ^ 59
def prefixEnd_37477 : Nat := 4983230072969 + 3 ^ 40 * 37477 * 2
def baseEnd_37477 : Nat := 11403682659943765786757

theorem tailTrace_37477 : CollatzResearch.WordTrace tailWord_37477 prefixEnd_37477 11403682659943765786757 := by
  unfold tailWord_37477
  simp only [CollatzResearch.WordTrace]
  refine ⟨1366898485234704407134685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 911265656823136271423123 1366898485234704407134685)
  ·
    refine ⟨512586931963014152675507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1366898485234704407134685 512586931963014152675507)
    ·
      refine ⟨768880397944521229013261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 512586931963014152675507 768880397944521229013261)
      ·
        refine ⟨288330149229195460879973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 768880397944521229013261 288330149229195460879973)
        ·
          refine ⟨54061902980474148914995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 288330149229195460879973 54061902980474148914995)
          ·
            refine ⟨81092854470711223372493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54061902980474148914995 81092854470711223372493)
            ·
              refine ⟨30409820426516708764685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81092854470711223372493 30409820426516708764685)
              ·
                refine ⟨11403682659943765786757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30409820426516708764685 11403682659943765786757)
                ·
                  rfl

theorem cell19_37477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 3, 3].length) (baseStart_37477 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_37477 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_37477 prefixEnd_37477 := by exact prefixLift 37477
  have htrace : WordTrace (prefixWord ++ tailWord_37477) baseStart_37477 baseEnd_37477 := by
    simpa [prefixWord, tailWord_37477, baseEnd_37477] using wordTrace_append hprefix tailTrace_37477
  have hstable : (prefixWord ++ tailWord_37477).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37477).length < 2 ^ (prefixWord ++ tailWord_37477).sum := by decide
  have hdescent : baseEnd_37477 < baseStart_37477 := by decide
  rcases family_descends (prefixWord ++ tailWord_37477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37530 : List Nat := [3, 1, 1, 6, 2, 1, 2, 3]
def baseStart_37530 : Nat := 118140960795 + 37530 * 2 ^ 59
def prefixEnd_37530 : Nat := 4983230072969 + 3 ^ 40 * 37530 * 2
def baseEnd_37530 : Nat := 11419809756055346608835

theorem tailTrace_37530 : CollatzResearch.WordTrace tailWord_37530 prefixEnd_37530 11419809756055346608835 := by
  unfold tailWord_37530
  simp only [CollatzResearch.WordTrace]
  refine ⟨342207888510673614703511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 912554369361796305876029 342207888510673614703511)
  ·
    refine ⟨513311832766010422055267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 342207888510673614703511 513311832766010422055267)
    ·
      refine ⟨769967749149015633082901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 513311832766010422055267 769967749149015633082901)
      ·
        refine ⟨36092238241360107800761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 769967749149015633082901 36092238241360107800761)
        ·
          refine ⟨27069178681020080850571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36092238241360107800761 27069178681020080850571)
          ·
            refine ⟨40603768021530121275857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27069178681020080850571 40603768021530121275857)
            ·
              refine ⟨30452826016147590956893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40603768021530121275857 30452826016147590956893)
              ·
                refine ⟨11419809756055346608835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30452826016147590956893 11419809756055346608835)
                ·
                  rfl

theorem cell19_37530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 2, 3].length) (baseStart_37530 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_37530 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_37530 prefixEnd_37530 := by exact prefixLift 37530
  have htrace : WordTrace (prefixWord ++ tailWord_37530) baseStart_37530 baseEnd_37530 := by
    simpa [prefixWord, tailWord_37530, baseEnd_37530] using wordTrace_append hprefix tailTrace_37530
  have hstable : (prefixWord ++ tailWord_37530).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37530).length < 2 ^ (prefixWord ++ tailWord_37530).sum := by decide
  have hdescent : baseEnd_37530 < baseStart_37530 := by decide
  rcases family_descends (prefixWord ++ tailWord_37530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37536 : List Nat := [2, 1, 1, 4, 4, 1, 1, 5]
def baseStart_37536 : Nat := 118140960795 + 37536 * 2 ^ 59
def prefixEnd_37536 : Nat := 4983230072969 + 3 ^ 40 * 37536 * 2
def baseEnd_37536 : Nat := 11421635465049110475485

theorem tailTrace_37536 : CollatzResearch.WordTrace tailWord_37536 prefixEnd_37536 11421635465049110475485 := by
  unfold tailWord_37536
  simp only [CollatzResearch.WordTrace]
  refine ⟨684525196010478741766231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 912700261347304989021641 684525196010478741766231)
  ·
    refine ⟨1026787794015718112649347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 684525196010478741766231 1026787794015718112649347)
    ·
      refine ⟨1540181691023577168974021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1026787794015718112649347 1540181691023577168974021)
      ·
        refine ⟨288784067066920719182629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1540181691023577168974021 288784067066920719182629)
        ·
          refine ⟨54147012575047634846743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 288784067066920719182629 54147012575047634846743)
          ·
            refine ⟨81220518862571452270115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54147012575047634846743 81220518862571452270115)
            ·
              refine ⟨121830778293857178405173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81220518862571452270115 121830778293857178405173)
              ·
                refine ⟨11421635465049110475485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 121830778293857178405173 11421635465049110475485)
                ·
                  rfl

theorem cell19_37536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 5].length) (baseStart_37536 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_37536 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_37536 prefixEnd_37536 := by exact prefixLift 37536
  have htrace : WordTrace (prefixWord ++ tailWord_37536) baseStart_37536 baseEnd_37536 := by
    simpa [prefixWord, tailWord_37536, baseEnd_37536] using wordTrace_append hprefix tailTrace_37536
  have hstable : (prefixWord ++ tailWord_37536).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37536).length < 2 ^ (prefixWord ++ tailWord_37536).sum := by decide
  have hdescent : baseEnd_37536 < baseStart_37536 := by decide
  rcases family_descends (prefixWord ++ tailWord_37536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37553 : List Nat := [1, 2, 2, 6, 1, 2, 5]
def baseStart_37553 : Nat := 118140960795 + 37553 * 2 ^ 59
def prefixEnd_37553 : Nat := 4983230072969 + 3 ^ 40 * 37553 * 2
def baseEnd_37553 : Nat := 3808936102399369365887

theorem tailTrace_37553 : CollatzResearch.WordTrace tailWord_37553 prefixEnd_37553 3808936102399369365887 := by
  unfold tailWord_37553
  simp only [CollatzResearch.WordTrace]
  refine ⟨1369670432959369386901313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 913113621972912924600875 1369670432959369386901313)
  ·
    refine ⟨1027252824719527040175985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1369670432959369386901313 1027252824719527040175985)
    ·
      refine ⟨770439618539645280131989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1027252824719527040175985 770439618539645280131989)
      ·
        refine ⟨36114357119045872506187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 770439618539645280131989 36114357119045872506187)
        ·
          refine ⟨54171535678568808759281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36114357119045872506187 54171535678568808759281)
          ·
            refine ⟨40628651758926606569461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54171535678568808759281 40628651758926606569461)
            ·
              refine ⟨3808936102399369365887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40628651758926606569461 3808936102399369365887)
              ·
                rfl

theorem cell19_37553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 5].length) (baseStart_37553 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_37553 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_37553 prefixEnd_37553 := by exact prefixLift 37553
  have htrace : WordTrace (prefixWord ++ tailWord_37553) baseStart_37553 baseEnd_37553 := by
    simpa [prefixWord, tailWord_37553, baseEnd_37553] using wordTrace_append hprefix tailTrace_37553
  have hstable : (prefixWord ++ tailWord_37553).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37553).length < 2 ^ (prefixWord ++ tailWord_37553).sum := by decide
  have hdescent : baseEnd_37553 < baseStart_37553 := by decide
  rcases family_descends (prefixWord ++ tailWord_37553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37576 : List Nat := [2, 1, 3, 1, 2, 3, 1, 6]
def baseStart_37576 : Nat := 118140960795 + 37576 * 2 ^ 59
def prefixEnd_37576 : Nat := 4983230072969 + 3 ^ 40 * 37576 * 2
def baseEnd_37576 : Nat := 11433806858340869586487

theorem tailTrace_37576 : CollatzResearch.WordTrace tailWord_37576 prefixEnd_37576 11433806858340869586487 := by
  unfold tailWord_37576
  simp only [CollatzResearch.WordTrace]
  refine ⟨685254655938022157494291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 913672874584029543325721 685254655938022157494291)
  ·
    refine ⟨1027881983907033236241437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 685254655938022157494291 1027881983907033236241437)
    ·
      refine ⟨385455743965137463590539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1027881983907033236241437 385455743965137463590539)
      ·
        refine ⟨578183615947706195385809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 385455743965137463590539 578183615947706195385809)
        ·
          refine ⟨433637711960779646539357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 578183615947706195385809 433637711960779646539357)
          ·
            refine ⟨162614141985292367452259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 433637711960779646539357 162614141985292367452259)
            ·
              refine ⟨243921212977938551178389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 162614141985292367452259 243921212977938551178389)
              ·
                refine ⟨11433806858340869586487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 243921212977938551178389 11433806858340869586487)
                ·
                  rfl

theorem cell19_37576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 6].length) (baseStart_37576 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_37576 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_37576 prefixEnd_37576 := by exact prefixLift 37576
  have htrace : WordTrace (prefixWord ++ tailWord_37576) baseStart_37576 baseEnd_37576 := by
    simpa [prefixWord, tailWord_37576, baseEnd_37576] using wordTrace_append hprefix tailTrace_37576
  have hstable : (prefixWord ++ tailWord_37576).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37576).length < 2 ^ (prefixWord ++ tailWord_37576).sum := by decide
  have hdescent : baseEnd_37576 < baseStart_37576 := by decide
  rcases family_descends (prefixWord ++ tailWord_37576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37614 : List Nat := [4, 1, 2, 1, 1, 10]
def baseStart_37614 : Nat := 118140960795 + 37614 * 2 ^ 59
def prefixEnd_37614 : Nat := 4983230072969 + 3 ^ 40 * 37614 * 2
def baseEnd_37614 : Nat := 1271707742440893415771

theorem tailTrace_37614 : CollatzResearch.WordTrace tailWord_37614 prefixEnd_37614 1271707742440893415771 := by
  unfold tailWord_37614
  simp only [CollatzResearch.WordTrace]
  refine ⟨171486910717297100608987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 914596857158917869914597 171486910717297100608987)
  ·
    refine ⟨257230366075945650913481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171486910717297100608987 257230366075945650913481)
    ·
      refine ⟨192922774556959238185111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 257230366075945650913481 192922774556959238185111)
      ·
        refine ⟨289384161835438857277667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192922774556959238185111 289384161835438857277667)
        ·
          refine ⟨434076242753158285916501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 289384161835438857277667 434076242753158285916501)
          ·
            refine ⟨1271707742440893415771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 434076242753158285916501 1271707742440893415771)
            ·
              rfl

theorem cell19_37614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 10].length) (baseStart_37614 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_37614 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_37614 prefixEnd_37614 := by exact prefixLift 37614
  have htrace : WordTrace (prefixWord ++ tailWord_37614) baseStart_37614 baseEnd_37614 := by
    simpa [prefixWord, tailWord_37614, baseEnd_37614] using wordTrace_append hprefix tailTrace_37614
  have hstable : (prefixWord ++ tailWord_37614).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37614).length < 2 ^ (prefixWord ++ tailWord_37614).sum := by decide
  have hdescent : baseEnd_37614 < baseStart_37614 := by decide
  rcases family_descends (prefixWord ++ tailWord_37614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37874 : List Nat := [3, 2, 1, 5, 1, 2, 2, 3]
def baseStart_37874 : Nat := 118140960795 + 37874 * 2 ^ 59
def prefixEnd_37874 : Nat := 4983230072969 + 3 ^ 40 * 37874 * 2
def baseEnd_37874 : Nat := 11524483738364474963453

theorem tailTrace_37874 : CollatzResearch.WordTrace tailWord_37874 prefixEnd_37874 11524483738364474963453 := by
  unfold tailWord_37874
  simp only [CollatzResearch.WordTrace]
  refine ⟨345344566199110302334169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 920918843197627472891117 345344566199110302334169)
  ·
    refine ⟨259008424649332726750627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 345344566199110302334169 259008424649332726750627)
    ·
      refine ⟨388512636973999090125941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 259008424649332726750627 388512636973999090125941)
      ·
        refine ⟨36423059716312414699307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 388512636973999090125941 36423059716312414699307)
        ·
          refine ⟨54634589574468622048961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36423059716312414699307 54634589574468622048961)
          ·
            refine ⟨40975942180851466536721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54634589574468622048961 40975942180851466536721)
            ·
              refine ⟨30731956635638599902541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40975942180851466536721 30731956635638599902541)
              ·
                refine ⟨11524483738364474963453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30731956635638599902541 11524483738364474963453)
                ·
                  rfl

theorem cell19_37874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 2, 3].length) (baseStart_37874 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_37874 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_37874 prefixEnd_37874 := by exact prefixLift 37874
  have htrace : WordTrace (prefixWord ++ tailWord_37874) baseStart_37874 baseEnd_37874 := by
    simpa [prefixWord, tailWord_37874, baseEnd_37874] using wordTrace_append hprefix tailTrace_37874
  have hstable : (prefixWord ++ tailWord_37874).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37874).length < 2 ^ (prefixWord ++ tailWord_37874).sum := by decide
  have hdescent : baseEnd_37874 < baseStart_37874 := by decide
  rcases family_descends (prefixWord ++ tailWord_37874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37878 : List Nat := [5, 1, 1, 1, 3, 2, 1, 5]
def baseStart_37878 : Nat := 118140960795 + 37878 * 2 ^ 59
def prefixEnd_37878 : Nat := 4983230072969 + 3 ^ 40 * 37878 * 2
def baseEnd_37878 : Nat := 11525700877693650874553

theorem tailTrace_37878 : CollatzResearch.WordTrace tailWord_37878 prefixEnd_37878 11525700877693650874553 := by
  unfold tailWord_37878
  simp only [CollatzResearch.WordTrace]
  refine ⟨86345259798871868280143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 921016104521299928321525 86345259798871868280143)
  ·
    refine ⟨129517889698307802420215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86345259798871868280143 129517889698307802420215)
    ·
      refine ⟨194276834547461703630323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129517889698307802420215 194276834547461703630323)
      ·
        refine ⟨291415251821192555445485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194276834547461703630323 291415251821192555445485)
        ·
          refine ⟨109280719432947208292057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 291415251821192555445485 109280719432947208292057)
          ·
            refine ⟨81960539574710406219043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109280719432947208292057 81960539574710406219043)
            ·
              refine ⟨122940809362065609328565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81960539574710406219043 122940809362065609328565)
              ·
                refine ⟨11525700877693650874553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 122940809362065609328565 11525700877693650874553)
                ·
                  rfl

theorem cell19_37878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_37878 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_37878 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_37878 prefixEnd_37878 := by exact prefixLift 37878
  have htrace : WordTrace (prefixWord ++ tailWord_37878) baseStart_37878 baseEnd_37878 := by
    simpa [prefixWord, tailWord_37878, baseEnd_37878] using wordTrace_append hprefix tailTrace_37878
  have hstable : (prefixWord ++ tailWord_37878).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37878).length < 2 ^ (prefixWord ++ tailWord_37878).sum := by decide
  have hdescent : baseEnd_37878 < baseStart_37878 := by decide
  rcases family_descends (prefixWord ++ tailWord_37878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37899 : List Nat := [1, 1, 1, 1, 6, 4, 5]
def baseStart_37899 : Nat := 118140960795 + 37899 * 2 ^ 59
def prefixEnd_37899 : Nat := 4983230072969 + 3 ^ 40 * 37899 * 2
def baseEnd_37899 : Nat := 3844030286390608135943

theorem tailTrace_37899 : CollatzResearch.WordTrace tailWord_37899 prefixEnd_37899 3844030286390608135943 := by
  unfold tailWord_37899
  simp only [CollatzResearch.WordTrace]
  refine ⟨1382290089705870478996751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 921526726470580319331167 1382290089705870478996751)
  ·
    refine ⟨2073435134558805718495127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1382290089705870478996751 2073435134558805718495127)
    ·
      refine ⟨3110152701838208577742691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2073435134558805718495127 3110152701838208577742691)
      ·
        refine ⟨4665229052757312866614037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3110152701838208577742691 4665229052757312866614037)
        ·
          refine ⟨218682611847999040622533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 4665229052757312866614037 218682611847999040622533)
          ·
            refine ⟨41002989721499820116725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 218682611847999040622533 41002989721499820116725)
            ·
              refine ⟨3844030286390608135943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41002989721499820116725 3844030286390608135943)
              ·
                rfl

theorem cell19_37899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 5].length) (baseStart_37899 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_37899 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_37899 prefixEnd_37899 := by exact prefixLift 37899
  have htrace : WordTrace (prefixWord ++ tailWord_37899) baseStart_37899 baseEnd_37899 := by
    simpa [prefixWord, tailWord_37899, baseEnd_37899] using wordTrace_append hprefix tailTrace_37899
  have hstable : (prefixWord ++ tailWord_37899).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37899).length < 2 ^ (prefixWord ++ tailWord_37899).sum := by decide
  have hdescent : baseEnd_37899 < baseStart_37899 := by decide
  rcases family_descends (prefixWord ++ tailWord_37899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37916 : List Nat := [2, 2, 3, 1, 4, 1, 2, 4]
def baseStart_37916 : Nat := 118140960795 + 37916 * 2 ^ 59
def prefixEnd_37916 : Nat := 4983230072969 + 3 ^ 40 * 37916 * 2
def baseEnd_37916 : Nat := 11537263701320822030005

theorem tailTrace_37916 : CollatzResearch.WordTrace tailWord_37916 prefixEnd_37916 11537263701320822030005 := by
  unfold tailWord_37916
  simp only [CollatzResearch.WordTrace]
  refine ⟨691455065322141191182801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 921940087096188254910401 691455065322141191182801)
  ·
    refine ⟨518591298991605893387101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 691455065322141191182801 518591298991605893387101)
    ·
      refine ⟨194471737121852210020163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 518591298991605893387101 194471737121852210020163)
      ·
        refine ⟨291707605682778315030245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194471737121852210020163 291707605682778315030245)
        ·
          refine ⟨54695176065520934068171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 291707605682778315030245 54695176065520934068171)
          ·
            refine ⟨82042764098281401102257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54695176065520934068171 82042764098281401102257)
            ·
              refine ⟨61532073073711050826693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82042764098281401102257 61532073073711050826693)
              ·
                refine ⟨11537263701320822030005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61532073073711050826693 11537263701320822030005)
                ·
                  rfl

theorem cell19_37916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 2, 4].length) (baseStart_37916 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_37916 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_37916 prefixEnd_37916 := by exact prefixLift 37916
  have htrace : WordTrace (prefixWord ++ tailWord_37916) baseStart_37916 baseEnd_37916 := by
    simpa [prefixWord, tailWord_37916, baseEnd_37916] using wordTrace_append hprefix tailTrace_37916
  have hstable : (prefixWord ++ tailWord_37916).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37916).length < 2 ^ (prefixWord ++ tailWord_37916).sum := by decide
  have hdescent : baseEnd_37916 < baseStart_37916 := by decide
  rcases family_descends (prefixWord ++ tailWord_37916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37977 : List Nat := [1, 2, 1, 2, 2, 1, 2, 8]
def baseStart_37977 : Nat := 118140960795 + 37977 * 2 ^ 59
def prefixEnd_37977 : Nat := 4983230072969 + 3 ^ 40 * 37977 * 2
def baseEnd_37977 : Nat := 11555825076090754674283

theorem tailTrace_37977 : CollatzResearch.WordTrace tailWord_37977 prefixEnd_37977 11555825076090754674283 := by
  unfold tailWord_37977
  simp only [CollatzResearch.WordTrace]
  refine ⟨1385134983423289800336185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 923423322282193200224123 1385134983423289800336185)
  ·
    refine ⟨1038851237567467350252139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1385134983423289800336185 1038851237567467350252139)
    ·
      refine ⟨1558276856351201025378209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1038851237567467350252139 1558276856351201025378209)
      ·
        refine ⟨1168707642263400769033657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1558276856351201025378209 1168707642263400769033657)
        ·
          refine ⟨876530731697550576775243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1168707642263400769033657 876530731697550576775243)
          ·
            refine ⟨1314796097546325865162865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 876530731697550576775243 1314796097546325865162865)
            ·
              refine ⟨986097073159744398872149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1314796097546325865162865 986097073159744398872149)
              ·
                refine ⟨11555825076090754674283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 986097073159744398872149 11555825076090754674283)
                ·
                  rfl

theorem cell19_37977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 8].length) (baseStart_37977 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_37977 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_37977 prefixEnd_37977 := by exact prefixLift 37977
  have htrace : WordTrace (prefixWord ++ tailWord_37977) baseStart_37977 baseEnd_37977 := by
    simpa [prefixWord, tailWord_37977, baseEnd_37977] using wordTrace_append hprefix tailTrace_37977
  have hstable : (prefixWord ++ tailWord_37977).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37977).length < 2 ^ (prefixWord ++ tailWord_37977).sum := by decide
  have hdescent : baseEnd_37977 < baseStart_37977 := by decide
  rcases family_descends (prefixWord ++ tailWord_37977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38047 : List Nat := [1, 1, 2, 6, 2, 2, 2, 3]
def baseStart_38047 : Nat := 118140960795 + 38047 * 2 ^ 59
def prefixEnd_38047 : Nat := 4983230072969 + 3 ^ 40 * 38047 * 2
def baseEnd_38047 : Nat := 11577125014351333118537

theorem tailTrace_38047 : CollatzResearch.WordTrace tailWord_38047 prefixEnd_38047 11577125014351333118537 := by
  unfold tailWord_38047
  simp only [CollatzResearch.WordTrace]
  refine ⟨1387688093169691755384395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 925125395446461170256263 1387688093169691755384395)
  ·
    refine ⟨2081532139754537633076593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1387688093169691755384395 2081532139754537633076593)
    ·
      refine ⟨1561149104815903224807445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2081532139754537633076593 1561149104815903224807445)
      ·
        refine ⟨73178864288245463662849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 1561149104815903224807445 73178864288245463662849)
        ·
          refine ⟨54884148216184097747137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73178864288245463662849 54884148216184097747137)
          ·
            refine ⟨41163111162138073310353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54884148216184097747137 41163111162138073310353)
            ·
              refine ⟨30872333371603554982765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41163111162138073310353 30872333371603554982765)
              ·
                refine ⟨11577125014351333118537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30872333371603554982765 11577125014351333118537)
                ·
                  rfl

theorem cell19_38047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 2, 3].length) (baseStart_38047 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_38047 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_38047 prefixEnd_38047 := by exact prefixLift 38047
  have htrace : WordTrace (prefixWord ++ tailWord_38047) baseStart_38047 baseEnd_38047 := by
    simpa [prefixWord, tailWord_38047, baseEnd_38047] using wordTrace_append hprefix tailTrace_38047
  have hstable : (prefixWord ++ tailWord_38047).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38047).length < 2 ^ (prefixWord ++ tailWord_38047).sum := by decide
  have hdescent : baseEnd_38047 < baseStart_38047 := by decide
  rcases family_descends (prefixWord ++ tailWord_38047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38127 : List Nat := [1, 1, 2, 1, 8, 6]
def baseStart_38127 : Nat := 118140960795 + 38127 * 2 ^ 59
def prefixEnd_38127 : Nat := 4983230072969 + 3 ^ 40 * 38127 * 2
def baseEnd_38127 : Nat := 1289051977881650148949

theorem tailTrace_38127 : CollatzResearch.WordTrace tailWord_38127 prefixEnd_38127 1289051977881650148949 := by
  unfold tailWord_38127
  simp only [CollatzResearch.WordTrace]
  refine ⟨1390605932879865418296635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 927070621919910278864423 1390605932879865418296635)
  ·
    refine ⟨2085908899319798127444953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1390605932879865418296635 2085908899319798127444953)
    ·
      refine ⟨1564431674489848595583715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2085908899319798127444953 1564431674489848595583715)
      ·
        refine ⟨2346647511734772893375573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1564431674489848595583715 2346647511734772893375573)
        ·
          refine ⟨27499775528141869844245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 2346647511734772893375573 27499775528141869844245)
          ·
            refine ⟨1289051977881650148949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 27499775528141869844245 1289051977881650148949)
            ·
              rfl

theorem cell19_38127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 6].length) (baseStart_38127 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_38127 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_38127 prefixEnd_38127 := by exact prefixLift 38127
  have htrace : WordTrace (prefixWord ++ tailWord_38127) baseStart_38127 baseEnd_38127 := by
    simpa [prefixWord, tailWord_38127, baseEnd_38127] using wordTrace_append hprefix tailTrace_38127
  have hstable : (prefixWord ++ tailWord_38127).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38127).length < 2 ^ (prefixWord ++ tailWord_38127).sum := by decide
  have hdescent : baseEnd_38127 < baseStart_38127 := by decide
  rcases family_descends (prefixWord ++ tailWord_38127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38184 : List Nat := [2, 1, 5, 1, 2, 2, 6]
def baseStart_38184 : Nat := 118140960795 + 38184 * 2 ^ 59
def prefixEnd_38184 : Nat := 4983230072969 + 3 ^ 40 * 38184 * 2
def baseEnd_38184 : Nat := 3872937345458536024573

theorem tailTrace_38184 : CollatzResearch.WordTrace tailWord_38184 prefixEnd_38184 3872937345458536024573 := by
  unfold tailWord_38184
  simp only [CollatzResearch.WordTrace]
  refine ⟨696342446836682076560803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 928456595782242768747737 696342446836682076560803)
  ·
    refine ⟨1044513670255023114841205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 696342446836682076560803 1044513670255023114841205)
    ·
      refine ⟨97923156586408417016363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1044513670255023114841205 97923156586408417016363)
      ·
        refine ⟨146884734879612625524545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97923156586408417016363 146884734879612625524545)
        ·
          refine ⟨110163551159709469143409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146884734879612625524545 110163551159709469143409)
          ·
            refine ⟨82622663369782101857557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110163551159709469143409 82622663369782101857557)
            ·
              refine ⟨3872937345458536024573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 82622663369782101857557 3872937345458536024573)
              ·
                rfl

theorem cell19_38184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 6].length) (baseStart_38184 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_38184 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_38184 prefixEnd_38184 := by exact prefixLift 38184
  have htrace : WordTrace (prefixWord ++ tailWord_38184) baseStart_38184 baseEnd_38184 := by
    simpa [prefixWord, tailWord_38184, baseEnd_38184] using wordTrace_append hprefix tailTrace_38184
  have hstable : (prefixWord ++ tailWord_38184).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38184).length < 2 ^ (prefixWord ++ tailWord_38184).sum := by decide
  have hdescent : baseEnd_38184 < baseStart_38184 := by decide
  rcases family_descends (prefixWord ++ tailWord_38184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38214 : List Nat := [6, 1, 1, 3, 1, 2, 2, 3]
def baseStart_38214 : Nat := 118140960795 + 38214 * 2 ^ 59
def prefixEnd_38214 : Nat := 4983230072969 + 3 ^ 40 * 38214 * 2
def baseEnd_38214 : Nat := 11627940581344427406971

theorem tailTrace_38214 : CollatzResearch.WordTrace tailWord_38214 prefixEnd_38214 11627940581344427406971 := by
  unfold tailWord_38214
  simp only [CollatzResearch.WordTrace]
  refine ⟨43555596361396227397303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 929186055709786184475797 43555596361396227397303)
  ·
    refine ⟨65333394542094341095955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43555596361396227397303 65333394542094341095955)
    ·
      refine ⟨98000091813141511643933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65333394542094341095955 98000091813141511643933)
      ·
        refine ⟨36750034429928066866475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98000091813141511643933 36750034429928066866475)
        ·
          refine ⟨55125051644892100299713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36750034429928066866475 55125051644892100299713)
          ·
            refine ⟨41343788733669075224785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55125051644892100299713 41343788733669075224785)
            ·
              refine ⟨31007841550251806418589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41343788733669075224785 31007841550251806418589)
              ·
                refine ⟨11627940581344427406971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31007841550251806418589 11627940581344427406971)
                ·
                  rfl

theorem cell19_38214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_38214 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_38214 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_38214 prefixEnd_38214 := by exact prefixLift 38214
  have htrace : WordTrace (prefixWord ++ tailWord_38214) baseStart_38214 baseEnd_38214 := by
    simpa [prefixWord, tailWord_38214, baseEnd_38214] using wordTrace_append hprefix tailTrace_38214
  have hstable : (prefixWord ++ tailWord_38214).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38214).length < 2 ^ (prefixWord ++ tailWord_38214).sum := by decide
  have hdescent : baseEnd_38214 < baseStart_38214 := by decide
  rcases family_descends (prefixWord ++ tailWord_38214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38220 : List Nat := [2, 2, 1, 3, 2, 4, 2, 3]
def baseStart_38220 : Nat := 118140960795 + 38220 * 2 ^ 59
def prefixEnd_38220 : Nat := 4983230072969 + 3 ^ 40 * 38220 * 2
def baseEnd_38220 : Nat := 11629766290338191273621

theorem tailTrace_38220 : CollatzResearch.WordTrace tailWord_38220 prefixEnd_38220 11629766290338191273621 := by
  unfold tailWord_38220
  simp only [CollatzResearch.WordTrace]
  refine ⟨696998960771471150716057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 929331947695294867621409 696998960771471150716057)
  ·
    refine ⟨522749220578603363037043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 696998960771471150716057 522749220578603363037043)
    ·
      refine ⟨784123830867905044555565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 522749220578603363037043 784123830867905044555565)
      ·
        refine ⟨294046436575464391708337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 784123830867905044555565 294046436575464391708337)
        ·
          refine ⟨220534827431598293781253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 294046436575464391708337 220534827431598293781253)
          ·
            refine ⟨41350280143424680083985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 220534827431598293781253 41350280143424680083985)
            ·
              refine ⟨31012710107568510062989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41350280143424680083985 31012710107568510062989)
              ·
                refine ⟨11629766290338191273621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31012710107568510062989 11629766290338191273621)
                ·
                  rfl

theorem cell19_38220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 2, 3].length) (baseStart_38220 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_38220 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_38220 prefixEnd_38220 := by exact prefixLift 38220
  have htrace : WordTrace (prefixWord ++ tailWord_38220) baseStart_38220 baseEnd_38220 := by
    simpa [prefixWord, tailWord_38220, baseEnd_38220] using wordTrace_append hprefix tailTrace_38220
  have hstable : (prefixWord ++ tailWord_38220).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38220).length < 2 ^ (prefixWord ++ tailWord_38220).sum := by decide
  have hdescent : baseEnd_38220 < baseStart_38220 := by decide
  rcases family_descends (prefixWord ++ tailWord_38220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38224 : List Nat := [2, 1, 1, 1, 1, 5, 3, 5]
def baseStart_38224 : Nat := 118140960795 + 38224 * 2 ^ 59
def prefixEnd_38224 : Nat := 4983230072969 + 3 ^ 40 * 38224 * 2
def baseEnd_38224 : Nat := 11630983429667367184721

theorem tailTrace_38224 : CollatzResearch.WordTrace tailWord_38224 prefixEnd_38224 11630983429667367184721 := by
  unfold tailWord_38224
  simp only [CollatzResearch.WordTrace]
  refine ⟨697071906764225492288863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 929429209018967323051817 697071906764225492288863)
  ·
    refine ⟨1045607860146338238433295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 697071906764225492288863 1045607860146338238433295)
    ·
      refine ⟨1568411790219507357649943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1045607860146338238433295 1568411790219507357649943)
      ·
        refine ⟨2352617685329261036474915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1568411790219507357649943 2352617685329261036474915)
        ·
          refine ⟨3528926527993891554712373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2352617685329261036474915 3528926527993891554712373)
          ·
            refine ⟨330836861999427333254285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3528926527993891554712373 330836861999427333254285)
            ·
              refine ⟨124063823249785249970357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 330836861999427333254285 124063823249785249970357)
              ·
                refine ⟨11630983429667367184721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 124063823249785249970357 11630983429667367184721)
                ·
                  rfl

theorem cell19_38224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 5].length) (baseStart_38224 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_38224 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_38224 prefixEnd_38224 := by exact prefixLift 38224
  have htrace : WordTrace (prefixWord ++ tailWord_38224) baseStart_38224 baseEnd_38224 := by
    simpa [prefixWord, tailWord_38224, baseEnd_38224] using wordTrace_append hprefix tailTrace_38224
  have hstable : (prefixWord ++ tailWord_38224).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38224).length < 2 ^ (prefixWord ++ tailWord_38224).sum := by decide
  have hdescent : baseEnd_38224 < baseStart_38224 := by decide
  rcases family_descends (prefixWord ++ tailWord_38224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38243 : List Nat := [1, 1, 1, 5, 2, 2, 7]
def baseStart_38243 : Nat := 118140960795 + 38243 * 2 ^ 59
def prefixEnd_38243 : Nat := 4983230072969 + 3 ^ 40 * 38243 * 2
def baseEnd_38243 : Nat := 3878921613826984254149

theorem tailTrace_38243 : CollatzResearch.WordTrace tailWord_38243 prefixEnd_38243 3878921613826984254149 := by
  unfold tailWord_38243
  simp only [CollatzResearch.WordTrace]
  refine ⟨1394836800459617229519383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 929891200306411486346255 1394836800459617229519383)
  ·
    refine ⟨2092255200689425844279075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1394836800459617229519383 2092255200689425844279075)
    ·
      refine ⟨3138382801034138766418613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2092255200689425844279075 3138382801034138766418613)
      ·
        refine ⟨294223387596950509351745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3138382801034138766418613 294223387596950509351745)
        ·
          refine ⟨220667540697712882013809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 294223387596950509351745 220667540697712882013809)
          ·
            refine ⟨165500655523284661510357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 220667540697712882013809 165500655523284661510357)
            ·
              refine ⟨3878921613826984254149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 165500655523284661510357 3878921613826984254149)
              ·
                rfl

theorem cell19_38243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 7].length) (baseStart_38243 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_38243 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_38243 prefixEnd_38243 := by exact prefixLift 38243
  have htrace : WordTrace (prefixWord ++ tailWord_38243) baseStart_38243 baseEnd_38243 := by
    simpa [prefixWord, tailWord_38243, baseEnd_38243] using wordTrace_append hprefix tailTrace_38243
  have hstable : (prefixWord ++ tailWord_38243).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38243).length < 2 ^ (prefixWord ++ tailWord_38243).sum := by decide
  have hdescent : baseEnd_38243 < baseStart_38243 := by decide
  rcases family_descends (prefixWord ++ tailWord_38243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38357 : List Nat := [1, 3, 2, 3, 1, 1, 8]
def baseStart_38357 : Nat := 118140960795 + 38357 * 2 ^ 59
def prefixEnd_38357 : Nat := 4983230072969 + 3 ^ 40 * 38357 * 2
def baseEnd_38357 : Nat := 3890484437454155409601

theorem tailTrace_38357 : CollatzResearch.WordTrace tailWord_38357 prefixEnd_38357 3890484437454155409601 := by
  unfold tailWord_38357
  simp only [CollatzResearch.WordTrace]
  refine ⟨1398994722046614699169325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 932663148031076466112883 1398994722046614699169325)
  ·
    refine ⟨524623020767480512188497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1398994722046614699169325 524623020767480512188497)
    ·
      refine ⟨393467265575610384141373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 524623020767480512188497 393467265575610384141373)
      ·
        refine ⟨147550224590853894053015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 393467265575610384141373 147550224590853894053015)
        ·
          refine ⟨221325336886280841079523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147550224590853894053015 221325336886280841079523)
          ·
            refine ⟨331988005329421261619285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 221325336886280841079523 331988005329421261619285)
            ·
              refine ⟨3890484437454155409601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 331988005329421261619285 3890484437454155409601)
              ·
                rfl

theorem cell19_38357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 8].length) (baseStart_38357 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_38357 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_38357 prefixEnd_38357 := by exact prefixLift 38357
  have htrace : WordTrace (prefixWord ++ tailWord_38357) baseStart_38357 baseEnd_38357 := by
    simpa [prefixWord, tailWord_38357, baseEnd_38357] using wordTrace_append hprefix tailTrace_38357
  have hstable : (prefixWord ++ tailWord_38357).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38357).length < 2 ^ (prefixWord ++ tailWord_38357).sum := by decide
  have hdescent : baseEnd_38357 < baseStart_38357 := by decide
  rcases family_descends (prefixWord ++ tailWord_38357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38376 : List Nat := [2, 1, 4, 1, 1, 2, 2, 6]
def baseStart_38376 : Nat := 118140960795 + 38376 * 2 ^ 59
def prefixEnd_38376 : Nat := 4983230072969 + 3 ^ 40 * 38376 * 2
def baseEnd_38376 : Nat := 11677234724176051806529

theorem tailTrace_38376 : CollatzResearch.WordTrace tailWord_38376 prefixEnd_38376 11677234724176051806529 := by
  unfold tailWord_38376
  simp only [CollatzResearch.WordTrace]
  refine ⟨699843854488890472055491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 933125139318520629407321 699843854488890472055491)
  ·
    refine ⟨1049765781733335708083237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 699843854488890472055491 1049765781733335708083237)
    ·
      refine ⟨196831084075000445265607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1049765781733335708083237 196831084075000445265607)
      ·
        refine ⟨295246626112500667898411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196831084075000445265607 295246626112500667898411)
        ·
          refine ⟨442869939168751001847617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 295246626112500667898411 442869939168751001847617)
          ·
            refine ⟨332152454376563251385713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 442869939168751001847617 332152454376563251385713)
            ·
              refine ⟨249114340782422438539285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 332152454376563251385713 249114340782422438539285)
              ·
                refine ⟨11677234724176051806529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 249114340782422438539285 11677234724176051806529)
                ·
                  rfl

theorem cell19_38376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 6].length) (baseStart_38376 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_38376 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_38376 prefixEnd_38376 := by exact prefixLift 38376
  have htrace : WordTrace (prefixWord ++ tailWord_38376) baseStart_38376 baseEnd_38376 := by
    simpa [prefixWord, tailWord_38376, baseEnd_38376] using wordTrace_append hprefix tailTrace_38376
  have hstable : (prefixWord ++ tailWord_38376).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38376).length < 2 ^ (prefixWord ++ tailWord_38376).sum := by decide
  have hdescent : baseEnd_38376 < baseStart_38376 := by decide
  rcases family_descends (prefixWord ++ tailWord_38376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38389 : List Nat := [1, 3, 5, 1, 1, 3, 2, 3]
def baseStart_38389 : Nat := 118140960795 + 38389 * 2 ^ 59
def prefixEnd_38389 : Nat := 4983230072969 + 3 ^ 40 * 38389 * 2
def baseEnd_38389 : Nat := 11681190426995873517605

theorem tailTrace_38389 : CollatzResearch.WordTrace tailWord_38389 prefixEnd_38389 11681190426995873517605 := by
  unfold tailWord_38389
  simp only [CollatzResearch.WordTrace]
  refine ⟨1400161857930684164334221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 933441238620456109556147 1400161857930684164334221)
  ·
    refine ⟨525060696724006561625333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1400161857930684164334221 525060696724006561625333)
    ·
      refine ⟨49224440317875615152375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 525060696724006561625333 49224440317875615152375)
      ·
        refine ⟨73836660476813422728563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49224440317875615152375 73836660476813422728563)
        ·
          refine ⟨110754990715220134092845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73836660476813422728563 110754990715220134092845)
          ·
            refine ⟨41533121518207550284817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 110754990715220134092845 41533121518207550284817)
            ·
              refine ⟨31149841138655662713613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41533121518207550284817 31149841138655662713613)
              ·
                refine ⟨11681190426995873517605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31149841138655662713613 11681190426995873517605)
                ·
                  rfl

theorem cell19_38389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 2, 3].length) (baseStart_38389 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_38389 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_38389 prefixEnd_38389 := by exact prefixLift 38389
  have htrace : WordTrace (prefixWord ++ tailWord_38389) baseStart_38389 baseEnd_38389 := by
    simpa [prefixWord, tailWord_38389, baseEnd_38389] using wordTrace_append hprefix tailTrace_38389
  have hstable : (prefixWord ++ tailWord_38389).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38389).length < 2 ^ (prefixWord ++ tailWord_38389).sum := by decide
  have hdescent : baseEnd_38389 < baseStart_38389 := by decide
  rcases family_descends (prefixWord ++ tailWord_38389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38406 : List Nat := [6, 2, 1, 1, 2, 2, 5]
def baseStart_38406 : Nat := 118140960795 + 38406 * 2 ^ 59
def prefixEnd_38406 : Nat := 4983230072969 + 3 ^ 40 * 38406 * 2
def baseEnd_38406 : Nat := 3895454423048290379927

theorem tailTrace_38406 : CollatzResearch.WordTrace tailWord_38406 prefixEnd_38406 3895454423048290379927 := by
  unfold tailWord_38406
  simp only [CollatzResearch.WordTrace]
  refine ⟨43774434339659252115721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 933854599246064045135381 43774434339659252115721)
  ·
    refine ⟨32830825754744439086791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43774434339659252115721 32830825754744439086791)
    ·
      refine ⟨49246238632116658630187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32830825754744439086791 49246238632116658630187)
      ·
        refine ⟨73869357948174987945281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49246238632116658630187 73869357948174987945281)
        ·
          refine ⟨55402018461131240958961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73869357948174987945281 55402018461131240958961)
          ·
            refine ⟨41551513845848430719221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55402018461131240958961 41551513845848430719221)
            ·
              refine ⟨3895454423048290379927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41551513845848430719221 3895454423048290379927)
              ·
                rfl

theorem cell19_38406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 5].length) (baseStart_38406 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_38406 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_38406 prefixEnd_38406 := by exact prefixLift 38406
  have htrace : WordTrace (prefixWord ++ tailWord_38406) baseStart_38406 baseEnd_38406 := by
    simpa [prefixWord, tailWord_38406, baseEnd_38406] using wordTrace_append hprefix tailTrace_38406
  have hstable : (prefixWord ++ tailWord_38406).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38406).length < 2 ^ (prefixWord ++ tailWord_38406).sum := by decide
  have hdescent : baseEnd_38406 < baseStart_38406 := by decide
  rcases family_descends (prefixWord ++ tailWord_38406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38412 : List Nat := [2, 2, 1, 2, 5, 2, 5]
def baseStart_38412 : Nat := 118140960795 + 38412 * 2 ^ 59
def prefixEnd_38412 : Nat := 4983230072969 + 3 ^ 40 * 38412 * 2
def baseEnd_38412 : Nat := 3896062992712878335477

theorem tailTrace_38412 : CollatzResearch.WordTrace tailWord_38412 prefixEnd_38412 3896062992712878335477 := by
  unfold tailWord_38412
  simp only [CollatzResearch.WordTrace]
  refine ⟨700500368423679546210745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 934000491231572728280993 700500368423679546210745)
  ·
    refine ⟨525375276317759659658059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 700500368423679546210745 525375276317759659658059)
    ·
      refine ⟨788062914476639489487089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 525375276317759659658059 788062914476639489487089)
      ·
        refine ⟨591047185857479617115317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 788062914476639489487089 591047185857479617115317)
        ·
          refine ⟨55410673674138714104561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 591047185857479617115317 55410673674138714104561)
          ·
            refine ⟨41558005255604035578421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55410673674138714104561 41558005255604035578421)
            ·
              refine ⟨3896062992712878335477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41558005255604035578421 3896062992712878335477)
              ·
                rfl

theorem cell19_38412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 5].length) (baseStart_38412 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_38412 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_38412 prefixEnd_38412 := by exact prefixLift 38412
  have htrace : WordTrace (prefixWord ++ tailWord_38412) baseStart_38412 baseEnd_38412 := by
    simpa [prefixWord, tailWord_38412, baseEnd_38412] using wordTrace_append hprefix tailTrace_38412
  have hstable : (prefixWord ++ tailWord_38412).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38412).length < 2 ^ (prefixWord ++ tailWord_38412).sum := by decide
  have hdescent : baseEnd_38412 < baseStart_38412 := by decide
  rcases family_descends (prefixWord ++ tailWord_38412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38433 : List Nat := [1, 2, 3, 2, 2, 2, 1, 6]
def baseStart_38433 : Nat := 118140960795 + 38433 * 2 ^ 59
def prefixEnd_38433 : Nat := 4983230072969 + 3 ^ 40 * 38433 * 2
def baseEnd_38433 : Nat := 11694578959616808539707

theorem tailTrace_38433 : CollatzResearch.WordTrace tailWord_38433 prefixEnd_38433 11694578959616808539707 := by
  unfold tailWord_38433
  simp only [CollatzResearch.WordTrace]
  refine ⟨1401766669771279678935953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 934511113180853119290635 1401766669771279678935953)
  ·
    refine ⟨1051325002328459759201965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1401766669771279678935953 1051325002328459759201965)
    ·
      refine ⟨394246875873172409700737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1051325002328459759201965 394246875873172409700737)
      ·
        refine ⟨295685156904879307275553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 394246875873172409700737 295685156904879307275553)
        ·
          refine ⟨221763867678659480456665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 295685156904879307275553 221763867678659480456665)
          ·
            refine ⟨166322900758994610342499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 221763867678659480456665 166322900758994610342499)
            ·
              refine ⟨249484351138491915513749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 166322900758994610342499 249484351138491915513749)
              ·
                refine ⟨11694578959616808539707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 249484351138491915513749 11694578959616808539707)
                ·
                  rfl

theorem cell19_38433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 6].length) (baseStart_38433 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_38433 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_38433 prefixEnd_38433 := by exact prefixLift 38433
  have htrace : WordTrace (prefixWord ++ tailWord_38433) baseStart_38433 baseEnd_38433 := by
    simpa [prefixWord, tailWord_38433, baseEnd_38433] using wordTrace_append hprefix tailTrace_38433
  have hstable : (prefixWord ++ tailWord_38433).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38433).length < 2 ^ (prefixWord ++ tailWord_38433).sum := by decide
  have hdescent : baseEnd_38433 < baseStart_38433 := by decide
  rcases family_descends (prefixWord ++ tailWord_38433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38471 : List Nat := [1, 1, 4, 1, 5, 7]
def baseStart_38471 : Nat := 118140960795 + 38471 * 2 ^ 59
def prefixEnd_38471 : Nat := 4983230072969 + 3 ^ 40 * 38471 * 2
def baseEnd_38471 : Nat := 1300682420360442188351

theorem tailTrace_38471 : CollatzResearch.WordTrace tailWord_38471 prefixEnd_38471 1300682420360442188351 := by
  unfold tailWord_38471
  simp only [CollatzResearch.WordTrace]
  refine ⟨1403152643633612168819267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 935435095755741445879511 1403152643633612168819267)
  ·
    refine ⟨2104728965450418253228901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1403152643633612168819267 2104728965450418253228901)
    ·
      refine ⟨394636681021953422480419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2104728965450418253228901 394636681021953422480419)
      ·
        refine ⟨591955021532930133720629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 394636681021953422480419 591955021532930133720629)
        ·
          refine ⟨55495783268712200036309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 591955021532930133720629 55495783268712200036309)
          ·
            refine ⟨1300682420360442188351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 55495783268712200036309 1300682420360442188351)
            ·
              rfl

theorem cell19_38471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 7].length) (baseStart_38471 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_38471 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_38471 prefixEnd_38471 := by exact prefixLift 38471
  have htrace : WordTrace (prefixWord ++ tailWord_38471) baseStart_38471 baseEnd_38471 := by
    simpa [prefixWord, tailWord_38471, baseEnd_38471] using wordTrace_append hprefix tailTrace_38471
  have hstable : (prefixWord ++ tailWord_38471).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38471).length < 2 ^ (prefixWord ++ tailWord_38471).sum := by decide
  have hdescent : baseEnd_38471 < baseStart_38471 := by decide
  rcases family_descends (prefixWord ++ tailWord_38471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38562 : List Nat := [3, 3, 1, 4, 1, 1, 1, 5]
def baseStart_38562 : Nat := 118140960795 + 38562 * 2 ^ 59
def prefixEnd_38562 : Nat := 4983230072969 + 3 ^ 40 * 38562 * 2
def baseEnd_38562 : Nat := 11733831702982731672689

theorem tailTrace_38562 : CollatzResearch.WordTrace tailWord_38562 prefixEnd_38562 11733831702982731672689 := by
  unfold tailWord_38562
  simp only [CollatzResearch.WordTrace]
  refine ⟨351617921575983677595485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 937647790869289806921293 351617921575983677595485)
  ·
    refine ⟨131856720590993879098307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 351617921575983677595485 131856720590993879098307)
    ·
      refine ⟨197785080886490818647461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131856720590993879098307 197785080886490818647461)
      ·
        refine ⟨37084702666217028496399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 197785080886490818647461 37084702666217028496399)
        ·
          refine ⟨55627053999325542744599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37084702666217028496399 55627053999325542744599)
          ·
            refine ⟨83440580998988314116899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55627053999325542744599 83440580998988314116899)
            ·
              refine ⟨125160871498482471175349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83440580998988314116899 125160871498482471175349)
              ·
                refine ⟨11733831702982731672689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 125160871498482471175349 11733831702982731672689)
                ·
                  rfl

theorem cell19_38562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 5].length) (baseStart_38562 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_38562 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_38562 prefixEnd_38562 := by exact prefixLift 38562
  have htrace : WordTrace (prefixWord ++ tailWord_38562) baseStart_38562 baseEnd_38562 := by
    simpa [prefixWord, tailWord_38562, baseEnd_38562] using wordTrace_append hprefix tailTrace_38562
  have hstable : (prefixWord ++ tailWord_38562).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38562).length < 2 ^ (prefixWord ++ tailWord_38562).sum := by decide
  have hdescent : baseEnd_38562 < baseStart_38562 := by decide
  rcases family_descends (prefixWord ++ tailWord_38562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38564 : List Nat := [2, 3, 1, 2, 2, 2, 4, 3]
def baseStart_38564 : Nat := 118140960795 + 38564 * 2 ^ 59
def prefixEnd_38564 : Nat := 4983230072969 + 3 ^ 40 * 38564 * 2
def baseEnd_38564 : Nat := 11734440272647319628239

theorem tailTrace_38564 : CollatzResearch.WordTrace tailWord_38564 prefixEnd_38564 11734440272647319628239 := by
  unfold tailWord_38564
  simp only [CollatzResearch.WordTrace]
  refine ⟨703272316148344525977373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 937696421531126034636497 703272316148344525977373)
  ·
    refine ⟨263727118555629197241515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 703272316148344525977373 263727118555629197241515)
    ·
      refine ⟨395590677833443795862273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 263727118555629197241515 395590677833443795862273)
      ·
        refine ⟨296693008375082846896705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 395590677833443795862273 296693008375082846896705)
        ·
          refine ⟨222519756281312135172529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 296693008375082846896705 222519756281312135172529)
          ·
            refine ⟨166889817210984101379397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 222519756281312135172529 166889817210984101379397)
            ·
              refine ⟨31291840727059519008637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 166889817210984101379397 31291840727059519008637)
              ·
                refine ⟨11734440272647319628239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31291840727059519008637 11734440272647319628239)
                ·
                  rfl

theorem cell19_38564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 4, 3].length) (baseStart_38564 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_38564 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_38564 prefixEnd_38564 := by exact prefixLift 38564
  have htrace : WordTrace (prefixWord ++ tailWord_38564) baseStart_38564 baseEnd_38564 := by
    simpa [prefixWord, tailWord_38564, baseEnd_38564] using wordTrace_append hprefix tailTrace_38564
  have hstable : (prefixWord ++ tailWord_38564).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38564).length < 2 ^ (prefixWord ++ tailWord_38564).sum := by decide
  have hdescent : baseEnd_38564 < baseStart_38564 := by decide
  rcases family_descends (prefixWord ++ tailWord_38564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38581 : List Nat := [1, 3, 3, 3, 3, 1, 5]
def baseStart_38581 : Nat := 118140960795 + 38581 * 2 ^ 59
def prefixEnd_38581 : Nat := 4983230072969 + 3 ^ 40 * 38581 * 2
def baseEnd_38581 : Nat := 3913204371598772416805

theorem tailTrace_38581 : CollatzResearch.WordTrace tailWord_38581 prefixEnd_38581 3913204371598772416805 := by
  unfold tailWord_38581
  simp only [CollatzResearch.WordTrace]
  refine ⟨1407164673235100955323597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 938109782156733970215731 1407164673235100955323597)
  ·
    refine ⟨527686752463162858246349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1407164673235100955323597 527686752463162858246349)
    ·
      refine ⟨197882532173686071842381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 527686752463162858246349 197882532173686071842381)
      ·
        refine ⟨74205949565132276940893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 197882532173686071842381 74205949565132276940893)
        ·
          refine ⟨27827231086924603852835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74205949565132276940893 27827231086924603852835)
          ·
            refine ⟨41740846630386905779253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27827231086924603852835 41740846630386905779253)
            ·
              refine ⟨3913204371598772416805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41740846630386905779253 3913204371598772416805)
              ·
                rfl

theorem cell19_38581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 5].length) (baseStart_38581 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_38581 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_38581 prefixEnd_38581 := by exact prefixLift 38581
  have htrace : WordTrace (prefixWord ++ tailWord_38581) baseStart_38581 baseEnd_38581 := by
    simpa [prefixWord, tailWord_38581, baseEnd_38581] using wordTrace_append hprefix tailTrace_38581
  have hstable : (prefixWord ++ tailWord_38581).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38581).length < 2 ^ (prefixWord ++ tailWord_38581).sum := by decide
  have hdescent : baseEnd_38581 < baseStart_38581 := by decide
  rcases family_descends (prefixWord ++ tailWord_38581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38598 : List Nat := [6, 1, 2, 1, 1, 2, 2, 4]
def baseStart_38598 : Nat := 118140960795 + 38598 * 2 ^ 59
def prefixEnd_38598 : Nat := 4983230072969 + 3 ^ 40 * 38598 * 2
def baseEnd_38598 : Nat := 11744785956945314872591

theorem tailTrace_38598 : CollatzResearch.WordTrace tailWord_38598 prefixEnd_38598 11744785956945314872591 := by
  unfold tailWord_38598
  simp only [CollatzResearch.WordTrace]
  refine ⟨43993272317922276834139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 938523142782341905794965 43993272317922276834139)
  ·
    refine ⟨65989908476883415251209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43993272317922276834139 65989908476883415251209)
    ·
      refine ⟨49492431357662561438407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65989908476883415251209 49492431357662561438407)
      ·
        refine ⟨74238647036493842157611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49492431357662561438407 74238647036493842157611)
        ·
          refine ⟨111357970554740763236417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74238647036493842157611 111357970554740763236417)
          ·
            refine ⟨83518477916055572427313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111357970554740763236417 83518477916055572427313)
            ·
              refine ⟨62638858437041679320485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83518477916055572427313 62638858437041679320485)
              ·
                refine ⟨11744785956945314872591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62638858437041679320485 11744785956945314872591)
                ·
                  rfl

theorem cell19_38598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_38598 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_38598 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_38598 prefixEnd_38598 := by exact prefixLift 38598
  have htrace : WordTrace (prefixWord ++ tailWord_38598) baseStart_38598 baseEnd_38598 := by
    simpa [prefixWord, tailWord_38598, baseEnd_38598] using wordTrace_append hprefix tailTrace_38598
  have hstable : (prefixWord ++ tailWord_38598).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38598).length < 2 ^ (prefixWord ++ tailWord_38598).sum := by decide
  have hdescent : baseEnd_38598 < baseStart_38598 := by decide
  rcases family_descends (prefixWord ++ tailWord_38598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38602 : List Nat := [3, 1, 2, 1, 5, 1, 2, 4]
def baseStart_38602 : Nat := 118140960795 + 38602 * 2 ^ 59
def prefixEnd_38602 : Nat := 4983230072969 + 3 ^ 40 * 38602 * 2
def baseEnd_38602 : Nat := 11746003096274490783691

theorem tailTrace_38602 : CollatzResearch.WordTrace tailWord_38602 prefixEnd_38602 11746003096274490783691 := by
  unfold tailWord_38602
  simp only [CollatzResearch.WordTrace]
  refine ⟨351982651539755385459515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 938620404106014361225373 351982651539755385459515)
  ·
    refine ⟨527973977309633078189273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 351982651539755385459515 527973977309633078189273)
    ·
      refine ⟨395980482982224808641955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 527973977309633078189273 395980482982224808641955)
      ·
        refine ⟨593970724473337212962933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 395980482982224808641955 593970724473337212962933)
        ·
          refine ⟨55684755419375363715275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 593970724473337212962933 55684755419375363715275)
          ·
            refine ⟨83527133129063045572913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55684755419375363715275 83527133129063045572913)
            ·
              refine ⟨62645349846797284179685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83527133129063045572913 62645349846797284179685)
              ·
                refine ⟨11746003096274490783691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62645349846797284179685 11746003096274490783691)
                ·
                  rfl

theorem cell19_38602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 2, 4].length) (baseStart_38602 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_38602 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_38602 prefixEnd_38602 := by exact prefixLift 38602
  have htrace : WordTrace (prefixWord ++ tailWord_38602) baseStart_38602 baseEnd_38602 := by
    simpa [prefixWord, tailWord_38602, baseEnd_38602] using wordTrace_append hprefix tailTrace_38602
  have hstable : (prefixWord ++ tailWord_38602).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38602).length < 2 ^ (prefixWord ++ tailWord_38602).sum := by decide
  have hdescent : baseEnd_38602 < baseStart_38602 := by decide
  rcases family_descends (prefixWord ++ tailWord_38602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38733 : List Nat := [1, 6, 1, 2, 1, 1, 4, 3]
def baseStart_38733 : Nat := 118140960795 + 38733 * 2 ^ 59
def prefixEnd_38733 : Nat := 4983230072969 + 3 ^ 40 * 38733 * 2
def baseEnd_38733 : Nat := 11785864409305001872223

theorem tailTrace_38733 : CollatzResearch.WordTrace tailWord_38733 prefixEnd_38733 11785864409305001872223 := by
  unfold tailWord_38733
  simp only [CollatzResearch.WordTrace]
  refine ⟨1412708568684430914856853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 941805712456287276571235 1412708568684430914856853)
  ·
    refine ⟨66220714157082699133915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 1412708568684430914856853 66220714157082699133915)
    ·
      refine ⟨99331071235624048700873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66220714157082699133915 99331071235624048700873)
      ·
        refine ⟨74498303426718036525655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99331071235624048700873 74498303426718036525655)
        ·
          refine ⟨111747455140077054788483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74498303426718036525655 111747455140077054788483)
          ·
            refine ⟨167621182710115582182725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111747455140077054788483 167621182710115582182725)
            ·
              refine ⟨31428971758146671659261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 167621182710115582182725 31428971758146671659261)
              ·
                refine ⟨11785864409305001872223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31428971758146671659261 11785864409305001872223)
                ·
                  rfl

theorem cell19_38733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 4, 3].length) (baseStart_38733 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_38733 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_38733 prefixEnd_38733 := by exact prefixLift 38733
  have htrace : WordTrace (prefixWord ++ tailWord_38733) baseStart_38733 baseEnd_38733 := by
    simpa [prefixWord, tailWord_38733, baseEnd_38733] using wordTrace_append hprefix tailTrace_38733
  have hstable : (prefixWord ++ tailWord_38733).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38733).length < 2 ^ (prefixWord ++ tailWord_38733).sum := by decide
  have hdescent : baseEnd_38733 < baseStart_38733 := by decide
  rcases family_descends (prefixWord ++ tailWord_38733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38737 : List Nat := [1, 2, 2, 1, 5, 2, 1, 5]
def baseStart_38737 : Nat := 118140960795 + 38737 * 2 ^ 59
def prefixEnd_38737 : Nat := 4983230072969 + 3 ^ 40 * 38737 * 2
def baseEnd_38737 : Nat := 11787081548634177783323

theorem tailTrace_38737 : CollatzResearch.WordTrace tailWord_38737 prefixEnd_38737 11787081548634177783323 := by
  unfold tailWord_38737
  simp only [CollatzResearch.WordTrace]
  refine ⟨1412854460669939598002465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 941902973779959732001643 1412854460669939598002465)
  ·
    refine ⟨1059640845502454698501849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1412854460669939598002465 1059640845502454698501849)
    ·
      refine ⟨794730634126841023876387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1059640845502454698501849 794730634126841023876387)
      ·
        refine ⟨1192095951190261535814581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 794730634126841023876387 1192095951190261535814581)
        ·
          refine ⟨111758995424087018982617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1192095951190261535814581 111758995424087018982617)
          ·
            refine ⟨83819246568065264236963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111758995424087018982617 83819246568065264236963)
            ·
              refine ⟨125728869852097896355445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83819246568065264236963 125728869852097896355445)
              ·
                refine ⟨11787081548634177783323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 125728869852097896355445 11787081548634177783323)
                ·
                  rfl

theorem cell19_38737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 5].length) (baseStart_38737 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_38737 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_38737 prefixEnd_38737 := by exact prefixLift 38737
  have htrace : WordTrace (prefixWord ++ tailWord_38737) baseStart_38737 baseEnd_38737 := by
    simpa [prefixWord, tailWord_38737, baseEnd_38737] using wordTrace_append hprefix tailTrace_38737
  have hstable : (prefixWord ++ tailWord_38737).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38737).length < 2 ^ (prefixWord ++ tailWord_38737).sum := by decide
  have hdescent : baseEnd_38737 < baseStart_38737 := by decide
  rcases family_descends (prefixWord ++ tailWord_38737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38754 : List Nat := [3, 3, 2, 1, 2, 3, 5]
def baseStart_38754 : Nat := 118140960795 + 38754 * 2 ^ 59
def prefixEnd_38754 : Nat := 4983230072969 + 3 ^ 40 * 38754 * 2
def baseEnd_38754 : Nat := 3930751463594391801833

theorem tailTrace_38754 : CollatzResearch.WordTrace tailWord_38754 prefixEnd_38754 3930751463594391801833 := by
  unfold tailWord_38754
  simp only [CollatzResearch.WordTrace]
  refine ⟨353368625402087875342829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 942316334405567667580877 353368625402087875342829)
  ·
    refine ⟨132513234525782953253561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 353368625402087875342829 132513234525782953253561)
    ·
      refine ⟨99384925894337214940171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132513234525782953253561 99384925894337214940171)
      ·
        refine ⟨149077388841505822410257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99384925894337214940171 149077388841505822410257)
        ·
          refine ⟨111808041631129366807693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149077388841505822410257 111808041631129366807693)
          ·
            refine ⟨41928015611673512552885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 111808041631129366807693 41928015611673512552885)
            ·
              refine ⟨3930751463594391801833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41928015611673512552885 3930751463594391801833)
              ·
                rfl

theorem cell19_38754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 5].length) (baseStart_38754 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_38754 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_38754 prefixEnd_38754 := by exact prefixLift 38754
  have htrace : WordTrace (prefixWord ++ tailWord_38754) baseStart_38754 baseEnd_38754 := by
    simpa [prefixWord, tailWord_38754, baseEnd_38754] using wordTrace_append hprefix tailTrace_38754
  have hstable : (prefixWord ++ tailWord_38754).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38754).length < 2 ^ (prefixWord ++ tailWord_38754).sum := by decide
  have hdescent : baseEnd_38754 < baseStart_38754 := by decide
  rcases family_descends (prefixWord ++ tailWord_38754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38815 : List Nat := [1, 1, 2, 5, 10]
def baseStart_38815 : Nat := 118140960795 + 38815 * 2 ^ 59
def prefixEnd_38815 : Nat := 4983230072969 + 3 ^ 40 * 38815 * 2
def baseEnd_38815 : Nat := 437437620946411409251

theorem tailTrace_38815 : CollatzResearch.WordTrace tailWord_38815 prefixEnd_38815 437437620946411409251 := by
  unfold tailWord_38815
  simp only [CollatzResearch.WordTrace]
  refine ⟨1415699354387358919341899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 943799569591572612894599 1415699354387358919341899)
  ·
    refine ⟨2123549031581038379012849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1415699354387358919341899 2123549031581038379012849)
    ·
      refine ⟨1592661773685778784259637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2123549031581038379012849 1592661773685778784259637)
      ·
        refine ⟨149312041283041761024341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1592661773685778784259637 149312041283041761024341)
        ·
          refine ⟨437437620946411409251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 149312041283041761024341 437437620946411409251)
          ·
            rfl

theorem cell19_38815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 10].length) (baseStart_38815 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_38815 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_38815 prefixEnd_38815 := by exact prefixLift 38815
  have htrace : WordTrace (prefixWord ++ tailWord_38815) baseStart_38815 baseEnd_38815 := by
    simpa [prefixWord, tailWord_38815, baseEnd_38815] using wordTrace_append hprefix tailTrace_38815
  have hstable : (prefixWord ++ tailWord_38815).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38815).length < 2 ^ (prefixWord ++ tailWord_38815).sum := by decide
  have hdescent : baseEnd_38815 < baseStart_38815 := by decide
  rcases family_descends (prefixWord ++ tailWord_38815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38872 : List Nat := [2, 1, 2, 2, 2, 2, 8]
def baseStart_38872 : Nat := 118140960795 + 38872 * 2 ^ 59
def prefixEnd_38872 : Nat := 4983230072969 + 3 ^ 40 * 38872 * 2
def baseEnd_38872 : Nat := 3942720000331288260985

theorem tailTrace_38872 : CollatzResearch.WordTrace tailWord_38872 prefixEnd_38872 3942720000331288260985 := by
  unfold tailWord_38872
  simp only [CollatzResearch.WordTrace]
  refine ⟨708889157590428827083435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 945185543453905102777913 708889157590428827083435)
  ·
    refine ⟨1063333736385643240625153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 708889157590428827083435 1063333736385643240625153)
    ·
      refine ⟨797500302289232430468865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1063333736385643240625153 797500302289232430468865)
      ·
        refine ⟨598125226716924322851649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 797500302289232430468865 598125226716924322851649)
        ·
          refine ⟨448593920037693242138737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 598125226716924322851649 448593920037693242138737)
          ·
            refine ⟨336445440028269931604053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 448593920037693242138737 336445440028269931604053)
            ·
              refine ⟨3942720000331288260985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 336445440028269931604053 3942720000331288260985)
              ·
                rfl

theorem cell19_38872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 8].length) (baseStart_38872 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_38872 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_38872 prefixEnd_38872 := by exact prefixLift 38872
  have htrace : WordTrace (prefixWord ++ tailWord_38872) baseStart_38872 baseEnd_38872 := by
    simpa [prefixWord, tailWord_38872, baseEnd_38872] using wordTrace_append hprefix tailTrace_38872
  have hstable : (prefixWord ++ tailWord_38872).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38872).length < 2 ^ (prefixWord ++ tailWord_38872).sum := by decide
  have hdescent : baseEnd_38872 < baseStart_38872 := by decide
  rcases family_descends (prefixWord ++ tailWord_38872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38902 : List Nat := [5, 1, 1, 1, 5, 1, 2, 3]
def baseStart_38902 : Nat := 118140960795 + 38902 * 2 ^ 59
def prefixEnd_38902 : Nat := 4983230072969 + 3 ^ 40 * 38902 * 2
def baseEnd_38902 : Nat := 11837288545962684116207

theorem tailTrace_38902 : CollatzResearch.WordTrace tailWord_38902 prefixEnd_38902 11837288545962684116207 := by
  unfold tailWord_38902
  simp only [CollatzResearch.WordTrace]
  refine ⟨88679531567010798609935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 945915003381448518505973 88679531567010798609935)
  ·
    refine ⟨133019297350516197914903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88679531567010798609935 133019297350516197914903)
    ·
      refine ⟨199528946025774296872355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133019297350516197914903 199528946025774296872355)
      ·
        refine ⟨299293419038661445308533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199528946025774296872355 299293419038661445308533)
        ·
          refine ⟨28058758034874510497675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 299293419038661445308533 28058758034874510497675)
          ·
            refine ⟨42088137052311765746513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28058758034874510497675 42088137052311765746513)
            ·
              refine ⟨31566102789233824309885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42088137052311765746513 31566102789233824309885)
              ·
                refine ⟨11837288545962684116207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31566102789233824309885 11837288545962684116207)
                ·
                  rfl

theorem cell19_38902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 2, 3].length) (baseStart_38902 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_38902 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_38902 prefixEnd_38902 := by exact prefixLift 38902
  have htrace : WordTrace (prefixWord ++ tailWord_38902) baseStart_38902 baseEnd_38902 := by
    simpa [prefixWord, tailWord_38902, baseEnd_38902] using wordTrace_append hprefix tailTrace_38902
  have hstable : (prefixWord ++ tailWord_38902).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38902).length < 2 ^ (prefixWord ++ tailWord_38902).sum := by decide
  have hdescent : baseEnd_38902 < baseStart_38902 := by decide
  rcases family_descends (prefixWord ++ tailWord_38902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38946 : List Nat := [3, 3, 1, 1, 1, 2, 4, 4]
def baseStart_38946 : Nat := 118140960795 + 38946 * 2 ^ 59
def prefixEnd_38946 : Nat := 4983230072969 + 3 ^ 40 * 38946 * 2
def baseEnd_38946 : Nat := 11850677078583619138309

theorem tailTrace_38946 : CollatzResearch.WordTrace tailWord_38946 prefixEnd_38946 11850677078583619138309 := by
  unfold tailWord_38946
  simp only [CollatzResearch.WordTrace]
  refine ⟨355119329228192073090173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 946984877941845528240461 355119329228192073090173)
  ·
    refine ⟨133169748460572027408815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 355119329228192073090173 133169748460572027408815)
    ·
      refine ⟨199754622690858041113223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133169748460572027408815 199754622690858041113223)
      ·
        refine ⟨299631934036287061669835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199754622690858041113223 299631934036287061669835)
        ·
          refine ⟨449447901054430592504753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 299631934036287061669835 449447901054430592504753)
          ·
            refine ⟨337085925790822944378565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 449447901054430592504753 337085925790822944378565)
            ·
              refine ⟨63203611085779302070981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 337085925790822944378565 63203611085779302070981)
              ·
                refine ⟨11850677078583619138309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63203611085779302070981 11850677078583619138309)
                ·
                  rfl

theorem cell19_38946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4, 4].length) (baseStart_38946 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_38946 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_38946 prefixEnd_38946 := by exact prefixLift 38946
  have htrace : WordTrace (prefixWord ++ tailWord_38946) baseStart_38946 baseEnd_38946 := by
    simpa [prefixWord, tailWord_38946, baseEnd_38946] using wordTrace_append hprefix tailTrace_38946
  have hstable : (prefixWord ++ tailWord_38946).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38946).length < 2 ^ (prefixWord ++ tailWord_38946).sum := by decide
  have hdescent : baseEnd_38946 < baseStart_38946 := by decide
  rcases family_descends (prefixWord ++ tailWord_38946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38967 : List Nat := [1, 1, 3, 1, 2, 2, 4, 5]
def baseStart_38967 : Nat := 118140960795 + 38967 * 2 ^ 59
def prefixEnd_38967 : Nat := 4983230072969 + 3 ^ 40 * 38967 * 2
def baseEnd_38967 : Nat := 11857067060061792671585

theorem tailTrace_38967 : CollatzResearch.WordTrace tailWord_38967 prefixEnd_38967 11857067060061792671585 := by
  unfold tailWord_38967
  simp only [CollatzResearch.WordTrace]
  refine ⟨1421243249836688878875155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 947495499891125919250103 1421243249836688878875155)
  ·
    refine ⟨2131864874755033318312733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1421243249836688878875155 2131864874755033318312733)
    ·
      refine ⟨799449328033137494367275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2131864874755033318312733 799449328033137494367275)
      ·
        refine ⟨1199173992049706241550913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 799449328033137494367275 1199173992049706241550913)
        ·
          refine ⟨899380494037279681163185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1199173992049706241550913 899380494037279681163185)
          ·
            refine ⟨674535370527959760872389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 899380494037279681163185 674535370527959760872389)
            ·
              refine ⟨126475381973992455163573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 674535370527959760872389 126475381973992455163573)
              ·
                refine ⟨11857067060061792671585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 126475381973992455163573 11857067060061792671585)
                ·
                  rfl

theorem cell19_38967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 5].length) (baseStart_38967 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_38967 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_38967 prefixEnd_38967 := by exact prefixLift 38967
  have htrace : WordTrace (prefixWord ++ tailWord_38967) baseStart_38967 baseEnd_38967 := by
    simpa [prefixWord, tailWord_38967, baseEnd_38967] using wordTrace_append hprefix tailTrace_38967
  have hstable : (prefixWord ++ tailWord_38967).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38967).length < 2 ^ (prefixWord ++ tailWord_38967).sum := by decide
  have hdescent : baseEnd_38967 < baseStart_38967 := by decide
  rcases family_descends (prefixWord ++ tailWord_38967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39041 : List Nat := [1, 2, 4, 2, 3, 1, 6]
def baseStart_39041 : Nat := 118140960795 + 39041 * 2 ^ 59
def prefixEnd_39041 : Nat := 4983230072969 + 3 ^ 40 * 39041 * 2
def baseEnd_39041 : Nat := 3959861379217182342313

theorem tailTrace_39041 : CollatzResearch.WordTrace tailWord_39041 prefixEnd_39041 3959861379217182342313 := by
  unfold tailWord_39041
  simp only [CollatzResearch.WordTrace]
  refine ⟨1423942251568599517068977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 949294834379066344712651 1423942251568599517068977)
  ·
    refine ⟨1067956688676449637801733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1423942251568599517068977 1067956688676449637801733)
    ·
      refine ⟨200241879126834307087825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1067956688676449637801733 200241879126834307087825)
      ·
        refine ⟨150181409345125730315869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 200241879126834307087825 150181409345125730315869)
        ·
          refine ⟨56318028504422148868451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 150181409345125730315869 56318028504422148868451)
          ·
            refine ⟨84477042756633223302677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56318028504422148868451 84477042756633223302677)
            ·
              refine ⟨3959861379217182342313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 84477042756633223302677 3959861379217182342313)
              ·
                rfl

theorem cell19_39041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 6].length) (baseStart_39041 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_39041 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_39041 prefixEnd_39041 := by exact prefixLift 39041
  have htrace : WordTrace (prefixWord ++ tailWord_39041) baseStart_39041 baseEnd_39041 := by
    simpa [prefixWord, tailWord_39041, baseEnd_39041] using wordTrace_append hprefix tailTrace_39041
  have hstable : (prefixWord ++ tailWord_39041).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39041).length < 2 ^ (prefixWord ++ tailWord_39041).sum := by decide
  have hdescent : baseEnd_39041 < baseStart_39041 := by decide
  rcases family_descends (prefixWord ++ tailWord_39041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39043 : List Nat := [1, 1, 1, 3, 3, 4, 6]
def baseStart_39043 : Nat := 118140960795 + 39043 * 2 ^ 59
def prefixEnd_39043 : Nat := 4983230072969 + 3 ^ 40 * 39043 * 2
def baseEnd_39043 : Nat := 3960064235772044994163

theorem tailTrace_39043 : CollatzResearch.WordTrace tailWord_39043 prefixEnd_39043 3960064235772044994163 := by
  unfold tailWord_39043
  simp only [CollatzResearch.WordTrace]
  refine ⟨1424015197561353858641783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 949343465040902572427855 1424015197561353858641783)
  ·
    refine ⟨2136022796342030787962675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1424015197561353858641783 2136022796342030787962675)
    ·
      refine ⟨3204034194513046181944013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2136022796342030787962675 3204034194513046181944013)
      ·
        refine ⟨1201512822942392318229005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3204034194513046181944013 1201512822942392318229005)
        ·
          refine ⟨450567308603397119335877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1201512822942392318229005 450567308603397119335877)
          ·
            refine ⟨84481370363136959875477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 450567308603397119335877 84481370363136959875477)
            ·
              refine ⟨3960064235772044994163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 84481370363136959875477 3960064235772044994163)
              ·
                rfl

theorem cell19_39043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 6].length) (baseStart_39043 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_39043 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_39043 prefixEnd_39043 := by exact prefixLift 39043
  have htrace : WordTrace (prefixWord ++ tailWord_39043) baseStart_39043 baseEnd_39043 := by
    simpa [prefixWord, tailWord_39043, baseEnd_39043] using wordTrace_append hprefix tailTrace_39043
  have hstable : (prefixWord ++ tailWord_39043).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39043).length < 2 ^ (prefixWord ++ tailWord_39043).sum := by decide
  have hdescent : baseEnd_39043 < baseStart_39043 := by decide
  rcases family_descends (prefixWord ++ tailWord_39043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39092 : List Nat := [2, 5, 3, 1, 1, 2, 5]
def baseStart_39092 : Nat := 118140960795 + 39092 * 2 ^ 59
def prefixEnd_39092 : Nat := 4983230072969 + 3 ^ 40 * 39092 * 2
def baseEnd_39092 : Nat := 3965034221366179964489

theorem tailTrace_39092 : CollatzResearch.WordTrace tailWord_39092 prefixEnd_39092 3965034221366179964489 := by
  unfold tailWord_39092
  simp only [CollatzResearch.WordTrace]
  refine ⟨712901187191917613587765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 950534916255890151450353 712901187191917613587765)
  ·
    refine ⟨66834486299242276273853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 712901187191917613587765 66834486299242276273853)
    ·
      refine ⟨25062932362215853602695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66834486299242276273853 25062932362215853602695)
      ·
        refine ⟨37594398543323780404043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25062932362215853602695 37594398543323780404043)
        ·
          refine ⟨56391597814985670606065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37594398543323780404043 56391597814985670606065)
          ·
            refine ⟨42293698361239252954549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56391597814985670606065 42293698361239252954549)
            ·
              refine ⟨3965034221366179964489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42293698361239252954549 3965034221366179964489)
              ·
                rfl

theorem cell19_39092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 5].length) (baseStart_39092 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_39092 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_39092 prefixEnd_39092 := by exact prefixLift 39092
  have htrace : WordTrace (prefixWord ++ tailWord_39092) baseStart_39092 baseEnd_39092 := by
    simpa [prefixWord, tailWord_39092, baseEnd_39092] using wordTrace_append hprefix tailTrace_39092
  have hstable : (prefixWord ++ tailWord_39092).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39092).length < 2 ^ (prefixWord ++ tailWord_39092).sum := by decide
  have hdescent : baseEnd_39092 < baseStart_39092 := by decide
  rcases family_descends (prefixWord ++ tailWord_39092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39119 : List Nat := [1, 1, 2, 1, 1, 3, 6, 4]
def baseStart_39119 : Nat := 118140960795 + 39119 * 2 ^ 59
def prefixEnd_39119 : Nat := 4983230072969 + 3 ^ 40 * 39119 * 2
def baseEnd_39119 : Nat := 11903318354570477293393

theorem tailTrace_39119 : CollatzResearch.WordTrace tailWord_39119 prefixEnd_39119 11903318354570477293393 := by
  unfold tailWord_39119
  simp only [CollatzResearch.WordTrace]
  refine ⟨1426787145286018838408411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 951191430190679225605607 1426787145286018838408411)
  ·
    refine ⟨2140180717929028257612617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1426787145286018838408411 2140180717929028257612617)
    ·
      refine ⟨1605135538446771193209463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2140180717929028257612617 1605135538446771193209463)
      ·
        refine ⟨2407703307670156789814195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1605135538446771193209463 2407703307670156789814195)
        ·
          refine ⟨3611554961505235184721293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2407703307670156789814195 3611554961505235184721293)
          ·
            refine ⟨1354333110564463194270485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3611554961505235184721293 1354333110564463194270485)
            ·
              refine ⟨63484364557709212231429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1354333110564463194270485 63484364557709212231429)
              ·
                refine ⟨11903318354570477293393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63484364557709212231429 11903318354570477293393)
                ·
                  rfl

theorem cell19_39119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 6, 4].length) (baseStart_39119 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_39119 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_39119 prefixEnd_39119 := by exact prefixLift 39119
  have htrace : WordTrace (prefixWord ++ tailWord_39119) baseStart_39119 baseEnd_39119 := by
    simpa [prefixWord, tailWord_39119, baseEnd_39119] using wordTrace_append hprefix tailTrace_39119
  have hstable : (prefixWord ++ tailWord_39119).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39119).length < 2 ^ (prefixWord ++ tailWord_39119).sum := by decide
  have hdescent : baseEnd_39119 < baseStart_39119 := by decide
  rcases family_descends (prefixWord ++ tailWord_39119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39172 : List Nat := [2, 3, 2, 2, 3, 2, 1, 4]
def baseStart_39172 : Nat := 118140960795 + 39172 * 2 ^ 59
def prefixEnd_39172 : Nat := 4983230072969 + 3 ^ 40 * 39172 * 2
def baseEnd_39172 : Nat := 11919445450682058115471

theorem tailTrace_39172 : CollatzResearch.WordTrace tailWord_39172 prefixEnd_39172 11919445450682058115471 := by
  unfold tailWord_39172
  simp only [CollatzResearch.WordTrace]
  refine ⟨714360107047004445043885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 952480142729339260058513 714360107047004445043885)
  ·
    refine ⟨267885040142626666891457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 714360107047004445043885 267885040142626666891457)
    ·
      refine ⟨200913780106970000168593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 267885040142626666891457 200913780106970000168593)
      ·
        refine ⟨150685335080227500126445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 200913780106970000168593 150685335080227500126445)
        ·
          refine ⟨56507000655085312547417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 150685335080227500126445 56507000655085312547417)
          ·
            refine ⟨42380250491313984410563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56507000655085312547417 42380250491313984410563)
            ·
              refine ⟨63570375736970976615845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42380250491313984410563 63570375736970976615845)
              ·
                refine ⟨11919445450682058115471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63570375736970976615845 11919445450682058115471)
                ·
                  rfl

theorem cell19_39172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 1, 4].length) (baseStart_39172 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_39172 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_39172 prefixEnd_39172 := by exact prefixLift 39172
  have htrace : WordTrace (prefixWord ++ tailWord_39172) baseStart_39172 baseEnd_39172 := by
    simpa [prefixWord, tailWord_39172, baseEnd_39172] using wordTrace_append hprefix tailTrace_39172
  have hstable : (prefixWord ++ tailWord_39172).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39172).length < 2 ^ (prefixWord ++ tailWord_39172).sum := by decide
  have hdescent : baseEnd_39172 < baseStart_39172 := by decide
  rcases family_descends (prefixWord ++ tailWord_39172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39250 : List Nat := [3, 2, 2, 1, 1, 1, 6, 3]
def baseStart_39250 : Nat := 118140960795 + 39250 * 2 ^ 59
def prefixEnd_39250 : Nat := 4983230072969 + 3 ^ 40 * 39250 * 2
def baseEnd_39250 : Nat := 11943179667600988381925

theorem tailTrace_39250 : CollatzResearch.WordTrace tailWord_39250 prefixEnd_39250 11943179667600988381925 := by
  unfold tailWord_39250
  simp only [CollatzResearch.WordTrace]
  refine ⟨357891276952857052856801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 954376738540952140951469 357891276952857052856801)
  ·
    refine ⟨268418457714642789642601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 357891276952857052856801 268418457714642789642601)
    ·
      refine ⟨201313843285982092231951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 268418457714642789642601 201313843285982092231951)
      ·
        refine ⟨301970764928973138347927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201313843285982092231951 301970764928973138347927)
        ·
          refine ⟨452956147393459707521891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 301970764928973138347927 452956147393459707521891)
          ·
            refine ⟨679434221090189561282837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 452956147393459707521891 679434221090189561282837)
            ·
              refine ⟨31848479113602635685133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 679434221090189561282837 31848479113602635685133)
              ·
                refine ⟨11943179667600988381925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31848479113602635685133 11943179667600988381925)
                ·
                  rfl

theorem cell19_39250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 6, 3].length) (baseStart_39250 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_39250 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_39250 prefixEnd_39250 := by exact prefixLift 39250
  have htrace : WordTrace (prefixWord ++ tailWord_39250) baseStart_39250 baseEnd_39250 := by
    simpa [prefixWord, tailWord_39250, baseEnd_39250] using wordTrace_append hprefix tailTrace_39250
  have hstable : (prefixWord ++ tailWord_39250).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39250).length < 2 ^ (prefixWord ++ tailWord_39250).sum := by decide
  have hdescent : baseEnd_39250 < baseStart_39250 := by decide
  rcases family_descends (prefixWord ++ tailWord_39250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39271 : List Nat := [1, 1, 5, 1, 3, 1, 7]
def baseStart_39271 : Nat := 118140960795 + 39271 * 2 ^ 59
def prefixEnd_39271 : Nat := 4983230072969 + 3 ^ 40 * 39271 * 2
def baseEnd_39271 : Nat := 3983189883026387305067

theorem tailTrace_39271 : CollatzResearch.WordTrace tailWord_39271 prefixEnd_39271 3983189883026387305067 := by
  unfold tailWord_39271
  simp only [CollatzResearch.WordTrace]
  refine ⟨1432331040735348797941667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 954887360490232531961111 1432331040735348797941667)
  ·
    refine ⟨2148496561103023196912501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1432331040735348797941667 2148496561103023196912501)
    ·
      refine ⟨201421552603408424710547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2148496561103023196912501 201421552603408424710547)
      ·
        refine ⟨302132328905112637065821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201421552603408424710547 302132328905112637065821)
        ·
          refine ⟨113299623339417238899683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 302132328905112637065821 113299623339417238899683)
          ·
            refine ⟨169949435009125858349525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113299623339417238899683 169949435009125858349525)
            ·
              refine ⟨3983189883026387305067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 169949435009125858349525 3983189883026387305067)
              ·
                rfl

theorem cell19_39271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 7].length) (baseStart_39271 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_39271 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_39271 prefixEnd_39271 := by exact prefixLift 39271
  have htrace : WordTrace (prefixWord ++ tailWord_39271) baseStart_39271 baseEnd_39271 := by
    simpa [prefixWord, tailWord_39271, baseEnd_39271] using wordTrace_append hprefix tailTrace_39271
  have hstable : (prefixWord ++ tailWord_39271).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39271).length < 2 ^ (prefixWord ++ tailWord_39271).sum := by decide
  have hdescent : baseEnd_39271 < baseStart_39271 := by decide
  rcases family_descends (prefixWord ++ tailWord_39271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39326 : List Nat := [4, 3, 1, 2, 1, 8]
def baseStart_39326 : Nat := 118140960795 + 39326 * 2 ^ 59
def prefixEnd_39326 : Nat := 4983230072969 + 3 ^ 40 * 39326 * 2
def baseEnd_39326 : Nat := 1329589479428370076981

theorem tailTrace_39326 : CollatzResearch.WordTrace tailWord_39326 prefixEnd_39326 1329589479428370076981 := by
  unfold tailWord_39326
  simp only [CollatzResearch.WordTrace]
  refine ⟨179292131942011648899229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 956224703690728794129221 179292131942011648899229)
  ·
    refine ⟨67234549478254368337211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 179292131942011648899229 67234549478254368337211)
    ·
      refine ⟨100851824217381552505817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67234549478254368337211 100851824217381552505817)
      ·
        refine ⟨75638868163036164379363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100851824217381552505817 75638868163036164379363)
        ·
          refine ⟨113458302244554246569045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75638868163036164379363 113458302244554246569045)
          ·
            refine ⟨1329589479428370076981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 113458302244554246569045 1329589479428370076981)
            ·
              rfl

theorem cell19_39326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 8].length) (baseStart_39326 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_39326 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_39326 prefixEnd_39326 := by exact prefixLift 39326
  have htrace : WordTrace (prefixWord ++ tailWord_39326) baseStart_39326 baseEnd_39326 := by
    simpa [prefixWord, tailWord_39326, baseEnd_39326] using wordTrace_append hprefix tailTrace_39326
  have hstable : (prefixWord ++ tailWord_39326).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39326).length < 2 ^ (prefixWord ++ tailWord_39326).sum := by decide
  have hdescent : baseEnd_39326 < baseStart_39326 := by decide
  rcases family_descends (prefixWord ++ tailWord_39326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39341 : List Nat := [1, 5, 2, 2, 3, 1, 1, 4]
def baseStart_39341 : Nat := 118140960795 + 39341 * 2 ^ 59
def prefixEnd_39341 : Nat := 4983230072969 + 3 ^ 40 * 39341 * 2
def baseEnd_39341 : Nat := 11970869587339740359455

theorem tailTrace_39341 : CollatzResearch.WordTrace tailWord_39341 prefixEnd_39341 11970869587339740359455 := by
  unfold tailWord_39341
  simp only [CollatzResearch.WordTrace]
  refine ⟨1434884150481750752989877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 956589433654500501993251 1434884150481750752989877)
  ·
    refine ⟨134520389107664133092801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1434884150481750752989877 134520389107664133092801)
    ·
      refine ⟨100890291830748099819601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134520389107664133092801 100890291830748099819601)
      ·
        refine ⟨75667718873061074864701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100890291830748099819601 75667718873061074864701)
        ·
          refine ⟨28375394577397903074263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75667718873061074864701 28375394577397903074263)
          ·
            refine ⟨42563091866096854611395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28375394577397903074263 42563091866096854611395)
            ·
              refine ⟨63844637799145281917093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42563091866096854611395 63844637799145281917093)
              ·
                refine ⟨11970869587339740359455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63844637799145281917093 11970869587339740359455)
                ·
                  rfl

theorem cell19_39341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 1, 4].length) (baseStart_39341 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_39341 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_39341 prefixEnd_39341 := by exact prefixLift 39341
  have htrace : WordTrace (prefixWord ++ tailWord_39341) baseStart_39341 baseEnd_39341 := by
    simpa [prefixWord, tailWord_39341, baseEnd_39341] using wordTrace_append hprefix tailTrace_39341
  have hstable : (prefixWord ++ tailWord_39341).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39341).length < 2 ^ (prefixWord ++ tailWord_39341).sum := by decide
  have hdescent : baseEnd_39341 < baseStart_39341 := by decide
  rcases family_descends (prefixWord ++ tailWord_39341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39345 : List Nat := [1, 2, 2, 4, 1, 4, 1, 4]
def baseStart_39345 : Nat := 118140960795 + 39345 * 2 ^ 59
def prefixEnd_39345 : Nat := 4983230072969 + 3 ^ 40 * 39345 * 2
def baseEnd_39345 : Nat := 11972086726668916270555

theorem tailTrace_39345 : CollatzResearch.WordTrace tailWord_39345 prefixEnd_39345 11972086726668916270555 := by
  unfold tailWord_39345
  simp only [CollatzResearch.WordTrace]
  refine ⟨1435030042467259436135489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 956686694978172957423659 1435030042467259436135489)
  ·
    refine ⟨1076272531850444577101617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1435030042467259436135489 1076272531850444577101617)
    ·
      refine ⟨807204398887833432826213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1076272531850444577101617 807204398887833432826213)
      ·
        refine ⟨151350824791468768654915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 807204398887833432826213 151350824791468768654915)
        ·
          refine ⟨227026237187203152982373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151350824791468768654915 227026237187203152982373)
          ·
            refine ⟨42567419472600591184195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 227026237187203152982373 42567419472600591184195)
            ·
              refine ⟨63851129208900886776293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42567419472600591184195 63851129208900886776293)
              ·
                refine ⟨11972086726668916270555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63851129208900886776293 11972086726668916270555)
                ·
                  rfl

theorem cell19_39345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 1, 4].length) (baseStart_39345 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_39345 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_39345 prefixEnd_39345 := by exact prefixLift 39345
  have htrace : WordTrace (prefixWord ++ tailWord_39345) baseStart_39345 baseEnd_39345 := by
    simpa [prefixWord, tailWord_39345, baseEnd_39345] using wordTrace_append hprefix tailTrace_39345
  have hstable : (prefixWord ++ tailWord_39345).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39345).length < 2 ^ (prefixWord ++ tailWord_39345).sum := by decide
  have hdescent : baseEnd_39345 < baseStart_39345 := by decide
  rcases family_descends (prefixWord ++ tailWord_39345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39478 : List Nat := [5, 1, 2, 1, 2, 1, 2, 5]
def baseStart_39478 : Nat := 118140960795 + 39478 * 2 ^ 59
def prefixEnd_39478 : Nat := 4983230072969 + 3 ^ 40 * 39478 * 2
def baseEnd_39478 : Nat := 12012556609364015314637

theorem tailTrace_39478 : CollatzResearch.WordTrace tailWord_39478 prefixEnd_39478 12012556609364015314637 := by
  unfold tailWord_39478
  simp only [CollatzResearch.WordTrace]
  refine ⟨89992559436588946920443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 959920633990282100484725 89992559436588946920443)
  ·
    refine ⟨134988839154883420380665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89992559436588946920443 134988839154883420380665)
    ·
      refine ⟨101241629366162565285499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134988839154883420380665 101241629366162565285499)
      ·
        refine ⟨151862444049243847928249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101241629366162565285499 151862444049243847928249)
        ·
          refine ⟨113896833036932885946187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151862444049243847928249 113896833036932885946187)
          ·
            refine ⟨170845249555399328919281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113896833036932885946187 170845249555399328919281)
            ·
              refine ⟨128133937166549496689461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 170845249555399328919281 128133937166549496689461)
              ·
                refine ⟨12012556609364015314637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 128133937166549496689461 12012556609364015314637)
                ·
                  rfl

theorem cell19_39478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_39478 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_39478 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_39478 prefixEnd_39478 := by exact prefixLift 39478
  have htrace : WordTrace (prefixWord ++ tailWord_39478) baseStart_39478 baseEnd_39478 := by
    simpa [prefixWord, tailWord_39478, baseEnd_39478] using wordTrace_append hprefix tailTrace_39478
  have hstable : (prefixWord ++ tailWord_39478).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39478).length < 2 ^ (prefixWord ++ tailWord_39478).sum := by decide
  have hdescent : baseEnd_39478 < baseStart_39478 := by decide
  rcases family_descends (prefixWord ++ tailWord_39478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39556 : List Nat := [2, 3, 2, 1, 3, 2, 6]
def baseStart_39556 : Nat := 118140960795 + 39556 * 2 ^ 59
def prefixEnd_39556 : Nat := 4983230072969 + 3 ^ 40 * 39556 * 2
def baseEnd_39556 : Nat := 4012096942094315193697

theorem tailTrace_39556 : CollatzResearch.WordTrace tailWord_39556 prefixEnd_39556 4012096942094315193697 := by
  unfold tailWord_39556
  simp only [CollatzResearch.WordTrace]
  refine ⟨721362922351421236033261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 961817229801894981377681 721362922351421236033261)
  ·
    refine ⟨270511095881782963512473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 721362922351421236033261 270511095881782963512473)
    ·
      refine ⟨202883321911337222634355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 270511095881782963512473 202883321911337222634355)
      ·
        refine ⟨304324982867005833951533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202883321911337222634355 304324982867005833951533)
        ·
          refine ⟨114121868575127187731825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 304324982867005833951533 114121868575127187731825)
          ·
            refine ⟨85591401431345390798869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114121868575127187731825 85591401431345390798869)
            ·
              refine ⟨4012096942094315193697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 85591401431345390798869 4012096942094315193697)
              ·
                rfl

theorem cell19_39556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 6].length) (baseStart_39556 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_39556 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_39556 prefixEnd_39556 := by exact prefixLift 39556
  have htrace : WordTrace (prefixWord ++ tailWord_39556) baseStart_39556 baseEnd_39556 := by
    simpa [prefixWord, tailWord_39556, baseEnd_39556] using wordTrace_append hprefix tailTrace_39556
  have hstable : (prefixWord ++ tailWord_39556).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39556).length < 2 ^ (prefixWord ++ tailWord_39556).sum := by decide
  have hdescent : baseEnd_39556 < baseStart_39556 := by decide
  rcases family_descends (prefixWord ++ tailWord_39556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39577 : List Nat := [1, 2, 1, 2, 1, 2, 4, 6]
def baseStart_39577 : Nat := 118140960795 + 39577 * 2 ^ 59
def prefixEnd_39577 : Nat := 4983230072969 + 3 ^ 40 * 39577 * 2
def baseEnd_39577 : Nat := 12042680807761119114367

theorem tailTrace_39577 : CollatzResearch.WordTrace tailWord_39577 prefixEnd_39577 12042680807761119114367 := by
  unfold tailWord_39577
  simp only [CollatzResearch.WordTrace]
  refine ⟨1443491777626763058580985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 962327851751175372387323 1443491777626763058580985)
  ·
    refine ⟨1082618833220072293935739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1443491777626763058580985 1082618833220072293935739)
    ·
      refine ⟨1623928249830108440903609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1082618833220072293935739 1623928249830108440903609)
      ·
        refine ⟨1217946187372581330677707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1623928249830108440903609 1217946187372581330677707)
        ·
          refine ⟨1826919281058871996016561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1217946187372581330677707 1826919281058871996016561)
          ·
            refine ⟨1370189460794153997012421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1826919281058871996016561 1370189460794153997012421)
            ·
              refine ⟨256910523898903874439829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1370189460794153997012421 256910523898903874439829)
              ·
                refine ⟨12042680807761119114367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 256910523898903874439829 12042680807761119114367)
                ·
                  rfl

theorem cell19_39577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 6].length) (baseStart_39577 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_39577 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_39577 prefixEnd_39577 := by exact prefixLift 39577
  have htrace : WordTrace (prefixWord ++ tailWord_39577) baseStart_39577 baseEnd_39577 := by
    simpa [prefixWord, tailWord_39577, baseEnd_39577] using wordTrace_append hprefix tailTrace_39577
  have hstable : (prefixWord ++ tailWord_39577).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39577).length < 2 ^ (prefixWord ++ tailWord_39577).sum := by decide
  have hdescent : baseEnd_39577 < baseStart_39577 := by decide
  rcases family_descends (prefixWord ++ tailWord_39577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39613 : List Nat := [1, 4, 1, 2, 1, 5, 5]
def baseStart_39613 : Nat := 118140960795 + 39613 * 2 ^ 59
def prefixEnd_39613 : Nat := 4983230072969 + 3 ^ 40 * 39613 * 2
def baseEnd_39613 : Nat := 4017878353907900771423

theorem tailTrace_39613 : CollatzResearch.WordTrace tailWord_39613 prefixEnd_39613 4017878353907900771423 := by
  unfold tailWord_39613
  simp only [CollatzResearch.WordTrace]
  refine ⟨1444804805496341206891493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 963203203664227471260995 1444804805496341206891493)
  ·
    refine ⟨270900901030563976292155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1444804805496341206891493 270900901030563976292155)
    ·
      refine ⟨406351351545845964438233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270900901030563976292155 406351351545845964438233)
      ·
        refine ⟨304763513659384473328675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 406351351545845964438233 304763513659384473328675)
        ·
          refine ⟨457145270489076709993013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 304763513659384473328675 457145270489076709993013)
          ·
            refine ⟨42857369108350941561845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 457145270489076709993013 42857369108350941561845)
            ·
              refine ⟨4017878353907900771423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42857369108350941561845 4017878353907900771423)
              ·
                rfl

theorem cell19_39613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 5].length) (baseStart_39613 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_39613 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_39613 prefixEnd_39613 := by exact prefixLift 39613
  have htrace : WordTrace (prefixWord ++ tailWord_39613) baseStart_39613 baseEnd_39613 := by
    simpa [prefixWord, tailWord_39613, baseEnd_39613] using wordTrace_append hprefix tailTrace_39613
  have hstable : (prefixWord ++ tailWord_39613).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39613).length < 2 ^ (prefixWord ++ tailWord_39613).sum := by decide
  have hdescent : baseEnd_39613 < baseStart_39613 := by decide
  rcases family_descends (prefixWord ++ tailWord_39613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39615 : List Nat := [1, 1, 2, 2, 2, 4, 7]
def baseStart_39615 : Nat := 118140960795 + 39615 * 2 ^ 59
def prefixEnd_39615 : Nat := 4983230072969 + 3 ^ 40 * 39615 * 2
def baseEnd_39615 : Nat := 4018081210462763423273

theorem tailTrace_39615 : CollatzResearch.WordTrace tailWord_39615 prefixEnd_39615 4018081210462763423273 := by
  unfold tailWord_39615
  simp only [CollatzResearch.WordTrace]
  refine ⟨1444877751489095548464299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 963251834326063698976199 1444877751489095548464299)
  ·
    refine ⟨2167316627233643322696449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1444877751489095548464299 2167316627233643322696449)
    ·
      refine ⟨1625487470425232492022337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2167316627233643322696449 1625487470425232492022337)
      ·
        refine ⟨1219115602818924369016753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1625487470425232492022337 1219115602818924369016753)
        ·
          refine ⟨914336702114193276762565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1219115602818924369016753 914336702114193276762565)
          ·
            refine ⟨171438131646411239392981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 914336702114193276762565 171438131646411239392981)
            ·
              refine ⟨4018081210462763423273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 171438131646411239392981 4018081210462763423273)
              ·
                rfl

theorem cell19_39615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 7].length) (baseStart_39615 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_39615 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_39615 prefixEnd_39615 := by exact prefixLift 39615
  have htrace : WordTrace (prefixWord ++ tailWord_39615) baseStart_39615 baseEnd_39615 := by
    simpa [prefixWord, tailWord_39615, baseEnd_39615] using wordTrace_append hprefix tailTrace_39615
  have hstable : (prefixWord ++ tailWord_39615).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39615).length < 2 ^ (prefixWord ++ tailWord_39615).sum := by decide
  have hdescent : baseEnd_39615 < baseStart_39615 := by decide
  rcases family_descends (prefixWord ++ tailWord_39615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39651 : List Nat := [1, 1, 1, 7, 1, 1, 2, 5]
def baseStart_39651 : Nat := 118140960795 + 39651 * 2 ^ 59
def prefixEnd_39651 : Nat := 4983230072969 + 3 ^ 40 * 39651 * 2
def baseEnd_39651 : Nat := 12065197885350873469721

theorem tailTrace_39651 : CollatzResearch.WordTrace tailWord_39651 prefixEnd_39651 12065197885350873469721 := by
  unfold tailWord_39651
  simp only [CollatzResearch.WordTrace]
  refine ⟨1446190779358673696774807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 964127186239115797849871 1446190779358673696774807)
  ·
    refine ⟨2169286169038010545162211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1446190779358673696774807 2169286169038010545162211)
    ·
      refine ⟨3253929253557015817743317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2169286169038010545162211 3253929253557015817743317)
      ·
        refine ⟨76263966880242558228359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 3253929253557015817743317 76263966880242558228359)
        ·
          refine ⟨114395950320363837342539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76263966880242558228359 114395950320363837342539)
          ·
            refine ⟨171593925480545756013809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114395950320363837342539 171593925480545756013809)
            ·
              refine ⟨128695444110409317010357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 171593925480545756013809 128695444110409317010357)
              ·
                refine ⟨12065197885350873469721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 128695444110409317010357 12065197885350873469721)
                ·
                  rfl

theorem cell19_39651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 5].length) (baseStart_39651 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_39651 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_39651 prefixEnd_39651 := by exact prefixLift 39651
  have htrace : WordTrace (prefixWord ++ tailWord_39651) baseStart_39651 baseEnd_39651 := by
    simpa [prefixWord, tailWord_39651, baseEnd_39651] using wordTrace_append hprefix tailTrace_39651
  have hstable : (prefixWord ++ tailWord_39651).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39651).length < 2 ^ (prefixWord ++ tailWord_39651).sum := by decide
  have hdescent : baseEnd_39651 < baseStart_39651 := by decide
  rcases family_descends (prefixWord ++ tailWord_39651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39668 : List Nat := [2, 6, 1, 1, 9]
def baseStart_39668 : Nat := 118140960795 + 39668 * 2 ^ 59
def prefixEnd_39668 : Nat := 4983230072969 + 3 ^ 40 * 39668 * 2
def baseEnd_39668 : Nat := 447050767685180410811

theorem tailTrace_39668 : CollatzResearch.WordTrace tailWord_39668 prefixEnd_39668 447050767685180410811 := by
  unfold tailWord_39668
  simp only [CollatzResearch.WordTrace]
  refine ⟨723405410148542800071829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 964540546864723733429105 723405410148542800071829)
  ·
    refine ⟨33909628600712943753367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 723405410148542800071829 33909628600712943753367)
    ·
      refine ⟨50864442901069415630051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33909628600712943753367 50864442901069415630051)
      ·
        refine ⟨76296664351604123445077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50864442901069415630051 76296664351604123445077)
        ·
          refine ⟨447050767685180410811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 76296664351604123445077 447050767685180410811)
          ·
            rfl

theorem cell19_39668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 9].length) (baseStart_39668 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_39668 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_39668 prefixEnd_39668 := by exact prefixLift 39668
  have htrace : WordTrace (prefixWord ++ tailWord_39668) baseStart_39668 baseEnd_39668 := by
    simpa [prefixWord, tailWord_39668, baseEnd_39668] using wordTrace_append hprefix tailTrace_39668
  have hstable : (prefixWord ++ tailWord_39668).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39668).length < 2 ^ (prefixWord ++ tailWord_39668).sum := by decide
  have hdescent : baseEnd_39668 < baseStart_39668 := by decide
  rcases family_descends (prefixWord ++ tailWord_39668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39687 : List Nat := [1, 1, 4, 4, 1, 3, 1, 4]
def baseStart_39687 : Nat := 118140960795 + 39687 * 2 ^ 59
def prefixEnd_39687 : Nat := 4983230072969 + 3 ^ 40 * 39687 * 2
def baseEnd_39687 : Nat := 12076152139313456669623

theorem tailTrace_39687 : CollatzResearch.WordTrace tailWord_39687 prefixEnd_39687 12076152139313456669623 := by
  unfold tailWord_39687
  simp only [CollatzResearch.WordTrace]
  refine ⟨1447503807228251845085315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 965002538152167896723543 1447503807228251845085315)
  ·
    refine ⟨2171255710842377767627973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1447503807228251845085315 2171255710842377767627973)
    ·
      refine ⟨407110445782945831430245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2171255710842377767627973 407110445782945831430245)
      ·
        refine ⟨76333208584302343393171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 407110445782945831430245 76333208584302343393171)
        ·
          refine ⟨114499812876453515089757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76333208584302343393171 114499812876453515089757)
          ·
            refine ⟨42937429828670068158659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 114499812876453515089757 42937429828670068158659)
            ·
              refine ⟨64406144743005102237989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42937429828670068158659 64406144743005102237989)
              ·
                refine ⟨12076152139313456669623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64406144743005102237989 12076152139313456669623)
                ·
                  rfl

theorem cell19_39687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 1, 4].length) (baseStart_39687 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_39687 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_39687 prefixEnd_39687 := by exact prefixLift 39687
  have htrace : WordTrace (prefixWord ++ tailWord_39687) baseStart_39687 baseEnd_39687 := by
    simpa [prefixWord, tailWord_39687, baseEnd_39687] using wordTrace_append hprefix tailTrace_39687
  have hstable : (prefixWord ++ tailWord_39687).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39687).length < 2 ^ (prefixWord ++ tailWord_39687).sum := by decide
  have hdescent : baseEnd_39687 < baseStart_39687 := by decide
  rcases family_descends (prefixWord ++ tailWord_39687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39729 : List Nat := [1, 2, 2, 3, 2, 1, 8]
def baseStart_39729 : Nat := 118140960795 + 39729 * 2 ^ 59
def prefixEnd_39729 : Nat := 4983230072969 + 3 ^ 40 * 39729 * 2
def baseEnd_39729 : Nat := 4029644034089934578725

theorem tailTrace_39729 : CollatzResearch.WordTrace tailWord_39729 prefixEnd_39729 4029644034089934578725 := by
  unfold tailWord_39729
  simp only [CollatzResearch.WordTrace]
  refine ⟨1449035673076093018114241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 966023782050728678742827 1449035673076093018114241)
  ·
    refine ⟨1086776754807069763585681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1449035673076093018114241 1086776754807069763585681)
    ·
      refine ⟨815082566105302322689261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1086776754807069763585681 815082566105302322689261)
      ·
        refine ⟨305655962289488371008473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 815082566105302322689261 305655962289488371008473)
        ·
          refine ⟨229241971717116278256355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 305655962289488371008473 229241971717116278256355)
          ·
            refine ⟨343862957575674417384533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 229241971717116278256355 343862957575674417384533)
            ·
              refine ⟨4029644034089934578725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 343862957575674417384533 4029644034089934578725)
              ·
                rfl

theorem cell19_39729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 8].length) (baseStart_39729 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_39729 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_39729 prefixEnd_39729 := by exact prefixLift 39729
  have htrace : WordTrace (prefixWord ++ tailWord_39729) baseStart_39729 baseEnd_39729 := by
    simpa [prefixWord, tailWord_39729, baseEnd_39729] using wordTrace_append hprefix tailTrace_39729
  have hstable : (prefixWord ++ tailWord_39729).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39729).length < 2 ^ (prefixWord ++ tailWord_39729).sum := by decide
  have hdescent : baseEnd_39729 < baseStart_39729 := by decide
  rcases family_descends (prefixWord ++ tailWord_39729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39761 : List Nat := [1, 2, 2, 1, 7, 1, 2, 3]
def baseStart_39761 : Nat := 118140960795 + 39761 * 2 ^ 59
def prefixEnd_39761 : Nat := 4983230072969 + 3 ^ 40 * 39761 * 2
def baseEnd_39761 : Nat := 12098669216903211024977

theorem tailTrace_39761 : CollatzResearch.WordTrace tailWord_39761 prefixEnd_39761 12098669216903211024977 := by
  unfold tailWord_39761
  simp only [CollatzResearch.WordTrace]
  refine ⟨1450202808960162483279137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 966801872640108322186091 1450202808960162483279137)
  ·
    refine ⟨1087652106720121862459353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1450202808960162483279137 1087652106720121862459353)
    ·
      refine ⟨815739080040091396844515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1087652106720121862459353 815739080040091396844515)
      ·
        refine ⟨1223608620060137095266773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 815739080040091396844515 1223608620060137095266773)
        ·
          refine ⟨28678327032659463170315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 1223608620060137095266773 28678327032659463170315)
          ·
            refine ⟨43017490548989194755473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28678327032659463170315 43017490548989194755473)
            ·
              refine ⟨32263117911741896066605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43017490548989194755473 32263117911741896066605)
              ·
                refine ⟨12098669216903211024977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32263117911741896066605 12098669216903211024977)
                ·
                  rfl

theorem cell19_39761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 2, 3].length) (baseStart_39761 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_39761 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_39761 prefixEnd_39761 := by exact prefixLift 39761
  have htrace : WordTrace (prefixWord ++ tailWord_39761) baseStart_39761 baseEnd_39761 := by
    simpa [prefixWord, tailWord_39761, baseEnd_39761] using wordTrace_append hprefix tailTrace_39761
  have hstable : (prefixWord ++ tailWord_39761).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39761).length < 2 ^ (prefixWord ++ tailWord_39761).sum := by decide
  have hdescent : baseEnd_39761 < baseStart_39761 := by decide
  rcases family_descends (prefixWord ++ tailWord_39761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39784 : List Nat := [2, 1, 4, 2, 1, 4, 5]
def baseStart_39784 : Nat := 118140960795 + 39784 * 2 ^ 59
def prefixEnd_39784 : Nat := 4983230072969 + 3 ^ 40 * 39784 * 2
def baseEnd_39784 : Nat := 4035222589348657504601

theorem tailTrace_39784 : CollatzResearch.WordTrace tailWord_39784 prefixEnd_39784 4035222589348657504601 := by
  unfold tailWord_39784
  simp only [CollatzResearch.WordTrace]
  refine ⟨725520843938418705683203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 967361125251224940910937 725520843938418705683203)
  ·
    refine ⟨1088281265907628058524805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 725520843938418705683203 1088281265907628058524805)
    ·
      refine ⟨204052737357680260973401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1088281265907628058524805 204052737357680260973401)
      ·
        refine ⟨153039553018260195730051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 204052737357680260973401 153039553018260195730051)
        ·
          refine ⟨229559329527390293595077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153039553018260195730051 229559329527390293595077)
          ·
            refine ⟨43042374286385680049077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 229559329527390293595077 43042374286385680049077)
            ·
              refine ⟨4035222589348657504601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43042374286385680049077 4035222589348657504601)
              ·
                rfl

theorem cell19_39784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 5].length) (baseStart_39784 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_39784 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_39784 prefixEnd_39784 := by exact prefixLift 39784
  have htrace : WordTrace (prefixWord ++ tailWord_39784) baseStart_39784 baseEnd_39784 := by
    simpa [prefixWord, tailWord_39784, baseEnd_39784] using wordTrace_append hprefix tailTrace_39784
  have hstable : (prefixWord ++ tailWord_39784).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39784).length < 2 ^ (prefixWord ++ tailWord_39784).sum := by decide
  have hdescent : baseEnd_39784 < baseStart_39784 := by decide
  rcases family_descends (prefixWord ++ tailWord_39784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39805 : List Nat := [1, 4, 1, 1, 2, 1, 3, 6]
def baseStart_39805 : Nat := 118140960795 + 39805 * 2 ^ 59
def prefixEnd_39805 : Nat := 4983230072969 + 3 ^ 40 * 39805 * 2
def baseEnd_39805 : Nat := 12112057749524146047079

theorem tailTrace_39805 : CollatzResearch.WordTrace tailWord_39805 prefixEnd_39805 12112057749524146047079 := by
  unfold tailWord_39805
  simp only [CollatzResearch.WordTrace]
  refine ⟨1451807620800757997880869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 967871747200505331920579 1451807620800757997880869)
  ·
    refine ⟨272213928900142124602663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1451807620800757997880869 272213928900142124602663)
    ·
      refine ⟨408320893350213186903995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272213928900142124602663 408320893350213186903995)
      ·
        refine ⟨612481340025319780355993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 408320893350213186903995 612481340025319780355993)
        ·
          refine ⟨459361005018989835266995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 612481340025319780355993 459361005018989835266995)
          ·
            refine ⟨689041507528484752900493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 459361005018989835266995 689041507528484752900493)
            ·
              refine ⟨258390565323181782337685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 689041507528484752900493 258390565323181782337685)
              ·
                refine ⟨12112057749524146047079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 258390565323181782337685 12112057749524146047079)
                ·
                  rfl

theorem cell19_39805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 6].length) (baseStart_39805 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_39805 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_39805 prefixEnd_39805 := by exact prefixLift 39805
  have htrace : WordTrace (prefixWord ++ tailWord_39805) baseStart_39805 baseEnd_39805 := by
    simpa [prefixWord, tailWord_39805, baseEnd_39805] using wordTrace_append hprefix tailTrace_39805
  have hstable : (prefixWord ++ tailWord_39805).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39805).length < 2 ^ (prefixWord ++ tailWord_39805).sum := by decide
  have hdescent : baseEnd_39805 < baseStart_39805 := by decide
  rcases family_descends (prefixWord ++ tailWord_39805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39934 : List Nat := [4, 2, 2, 2, 2, 1, 1, 5]
def baseStart_39934 : Nat := 118140960795 + 39934 * 2 ^ 59
def prefixEnd_39934 : Nat := 4983230072969 + 3 ^ 40 * 39934 * 2
def baseEnd_39934 : Nat := 12151310492890069180061

theorem tailTrace_39934 : CollatzResearch.WordTrace tailWord_39934 prefixEnd_39934 12151310492890069180061 := by
  unfold tailWord_39934
  simp only [CollatzResearch.WordTrace]
  refine ⟨182064079666676628665857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 971008424888942019551237 182064079666676628665857)
  ·
    refine ⟨136548059750007471499393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182064079666676628665857 136548059750007471499393)
    ·
      refine ⟨102411044812505603624545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136548059750007471499393 102411044812505603624545)
      ·
        refine ⟨76808283609379202718409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102411044812505603624545 76808283609379202718409)
        ·
          refine ⟨57606212707034402038807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76808283609379202718409 57606212707034402038807)
          ·
            refine ⟨86409319060551603058211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57606212707034402038807 86409319060551603058211)
            ·
              refine ⟨129613978590827404587317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86409319060551603058211 129613978590827404587317)
              ·
                refine ⟨12151310492890069180061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 129613978590827404587317 12151310492890069180061)
                ·
                  rfl

theorem cell19_39934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 5].length) (baseStart_39934 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_39934 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_39934 prefixEnd_39934 := by exact prefixLift 39934
  have htrace : WordTrace (prefixWord ++ tailWord_39934) baseStart_39934 baseEnd_39934 := by
    simpa [prefixWord, tailWord_39934, baseEnd_39934] using wordTrace_append hprefix tailTrace_39934
  have hstable : (prefixWord ++ tailWord_39934).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39934).length < 2 ^ (prefixWord ++ tailWord_39934).sum := by decide
  have hdescent : baseEnd_39934 < baseStart_39934 := by decide
  rcases family_descends (prefixWord ++ tailWord_39934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39957 : List Nat := [1, 3, 2, 1, 4, 1, 7]
def baseStart_39957 : Nat := 118140960795 + 39957 * 2 ^ 59
def prefixEnd_39957 : Nat := 4983230072969 + 3 ^ 40 * 39957 * 2
def baseEnd_39957 : Nat := 4052769681344276889629

theorem tailTrace_39957 : CollatzResearch.WordTrace tailWord_39957 prefixEnd_39957 4052769681344276889629 := by
  unfold tailWord_39957
  simp only [CollatzResearch.WordTrace]
  refine ⟨1457351516250087957414125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 971567677500058638276083 1457351516250087957414125)
  ·
    refine ⟨546506818593782984030297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1457351516250087957414125 546506818593782984030297)
    ·
      refine ⟨409880113945337238022723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 546506818593782984030297 409880113945337238022723)
      ·
        refine ⟨614820170918005857034085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 409880113945337238022723 614820170918005857034085)
        ·
          refine ⟨115278782047126098193891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 614820170918005857034085 115278782047126098193891)
          ·
            refine ⟨172918173070689147290837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115278782047126098193891 172918173070689147290837)
            ·
              refine ⟨4052769681344276889629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 172918173070689147290837 4052769681344276889629)
              ·
                rfl

theorem cell19_39957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 7].length) (baseStart_39957 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_39957 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_39957 prefixEnd_39957 := by exact prefixLift 39957
  have htrace : WordTrace (prefixWord ++ tailWord_39957) baseStart_39957 baseEnd_39957 := by
    simpa [prefixWord, tailWord_39957, baseEnd_39957] using wordTrace_append hprefix tailTrace_39957
  have hstable : (prefixWord ++ tailWord_39957).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39957).length < 2 ^ (prefixWord ++ tailWord_39957).sum := by decide
  have hdescent : baseEnd_39957 < baseStart_39957 := by decide
  rcases family_descends (prefixWord ++ tailWord_39957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan19Incremental
