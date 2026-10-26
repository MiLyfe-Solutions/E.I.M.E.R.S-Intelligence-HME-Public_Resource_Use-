import V185TrunkScan19Chunk009

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental

namespace V185TrunkScan19Incremental

def tailWord_101202 : List Nat := [3, 2, 2, 1, 1, 2, 1, 7]
def baseStart_101202 : Nat := 118140960795 + 101202 * 2 ^ 59
def prefixEnd_101202 : Nat := 4983230072969 + 3 ^ 40 * 101202 * 2
def baseEnd_101202 : Nat := 30794233597877499501977

theorem tailTrace_101202 : CollatzResearch.WordTrace tailWord_101202 prefixEnd_101202 30794233597877499501977 := by
  unfold tailWord_101202
  simp only [CollatzResearch.WordTrace]
  refine ⟨922785044842478192666465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2460760119579941847110573 922785044842478192666465)
  ·
    refine ⟨692088783631858644499849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 922785044842478192666465 692088783631858644499849)
    ·
      refine ⟨519066587723893983374887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 692088783631858644499849 519066587723893983374887)
      ·
        refine ⟨778599881585840975062331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 519066587723893983374887 778599881585840975062331)
        ·
          refine ⟨1167899822378761462593497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 778599881585840975062331 1167899822378761462593497)
          ·
            refine ⟨875924866784071096945123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1167899822378761462593497 875924866784071096945123)
            ·
              refine ⟨1313887300176106645417685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 875924866784071096945123 1313887300176106645417685)
              ·
                refine ⟨30794233597877499501977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1313887300176106645417685 30794233597877499501977)
                ·
                  rfl

theorem cell19_101202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 7].length) (baseStart_101202 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_101202 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_101202 prefixEnd_101202 := by exact prefixLift 101202
  have htrace : WordTrace (prefixWord ++ tailWord_101202) baseStart_101202 baseEnd_101202 := by
    simpa [prefixWord, tailWord_101202, baseEnd_101202] using wordTrace_append hprefix tailTrace_101202
  have hstable : (prefixWord ++ tailWord_101202).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101202).length < 2 ^ (prefixWord ++ tailWord_101202).sum := by decide
  have hdescent : baseEnd_101202 < baseStart_101202 := by decide
  rcases family_descends (prefixWord ++ tailWord_101202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101257 : List Nat := [1, 2, 1, 1, 5, 3, 3, 3]
def baseStart_101257 : Nat := 118140960795 + 101257 * 2 ^ 59
def prefixEnd_101257 : Nat := 4983230072969 + 3 ^ 40 * 101257 * 2
def baseEnd_101257 : Nat := 30810969263653668279605

theorem tailTrace_101257 : CollatzResearch.WordTrace tailWord_101257 prefixEnd_101257 30810969263653668279605 := by
  unfold tailWord_101257
  simp only [CollatzResearch.WordTrace]
  refine ⟨3693146194170657163918025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2462097462780438109278683 3693146194170657163918025)
  ·
    refine ⟨2769859645627992872938519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3693146194170657163918025 2769859645627992872938519)
    ·
      refine ⟨4154789468441989309407779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2769859645627992872938519 4154789468441989309407779)
      ·
        refine ⟨6232184202662983964111669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4154789468441989309407779 6232184202662983964111669)
        ·
          refine ⟨584267268999654746635469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6232184202662983964111669 584267268999654746635469)
          ·
            refine ⟨219100225874870529988301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 584267268999654746635469 219100225874870529988301)
            ·
              refine ⟨82162584703076448745613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 219100225874870529988301 82162584703076448745613)
              ·
                refine ⟨30810969263653668279605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82162584703076448745613 30810969263653668279605)
                ·
                  rfl

theorem cell19_101257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 3, 3].length) (baseStart_101257 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_101257 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_101257 prefixEnd_101257 := by exact prefixLift 101257
  have htrace : WordTrace (prefixWord ++ tailWord_101257) baseStart_101257 baseEnd_101257 := by
    simpa [prefixWord, tailWord_101257, baseEnd_101257] using wordTrace_append hprefix tailTrace_101257
  have hstable : (prefixWord ++ tailWord_101257).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101257).length < 2 ^ (prefixWord ++ tailWord_101257).sum := by decide
  have hdescent : baseEnd_101257 < baseStart_101257 := by decide
  rcases family_descends (prefixWord ++ tailWord_101257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101276 : List Nat := [2, 2, 3, 3, 2, 1, 6]
def baseStart_101276 : Nat := 118140960795 + 101276 * 2 ^ 59
def prefixEnd_101276 : Nat := 4983230072969 + 3 ^ 40 * 101276 * 2
def baseEnd_101276 : Nat := 10272250225155751285777

theorem tailTrace_101276 : CollatzResearch.WordTrace tailWord_101276 prefixEnd_101276 10272250225155751285777 := by
  unfold tailWord_101276
  simp only [CollatzResearch.WordTrace]
  refine ⟨1846919590550911704429841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2462559454067882272573121 1846919590550911704429841)
  ·
    refine ⟨1385189692913183778322381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1846919590550911704429841 1385189692913183778322381)
    ·
      refine ⟨519446134842443916870893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1385189692913183778322381 519446134842443916870893)
      ·
        refine ⟨194792300565916468826585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 519446134842443916870893 194792300565916468826585)
        ·
          refine ⟨146094225424437351619939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194792300565916468826585 146094225424437351619939)
          ·
            refine ⟨219141338136656027429909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146094225424437351619939 219141338136656027429909)
            ·
              refine ⟨10272250225155751285777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 219141338136656027429909 10272250225155751285777)
              ·
                rfl

theorem cell19_101276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 6].length) (baseStart_101276 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_101276 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_101276 prefixEnd_101276 := by exact prefixLift 101276
  have htrace : WordTrace (prefixWord ++ tailWord_101276) baseStart_101276 baseEnd_101276 := by
    simpa [prefixWord, tailWord_101276, baseEnd_101276] using wordTrace_append hprefix tailTrace_101276
  have hstable : (prefixWord ++ tailWord_101276).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101276).length < 2 ^ (prefixWord ++ tailWord_101276).sum := by decide
  have hdescent : baseEnd_101276 < baseStart_101276 := by decide
  rcases family_descends (prefixWord ++ tailWord_101276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101333 : List Nat := [1, 3, 2, 3, 3, 2, 5]
def baseStart_101333 : Nat := 118140960795 + 101333 * 2 ^ 59
def prefixEnd_101333 : Nat := 4983230072969 + 3 ^ 40 * 101333 * 2
def baseEnd_101333 : Nat := 10278031636969336863503

theorem tailTrace_101333 : CollatzResearch.WordTrace tailWord_101333 prefixEnd_101333 10278031636969336863503 := by
  unfold tailWord_101333
  simp only [CollatzResearch.WordTrace]
  refine ⟨3695918141895322143684653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2463945427930214762456435 3695918141895322143684653)
  ·
    refine ⟨1385969303210745803881745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3695918141895322143684653 1385969303210745803881745)
    ·
      refine ⟨1039476977408059352911309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1385969303210745803881745 1039476977408059352911309)
      ·
        refine ⟨389803866528022257341741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1039476977408059352911309 389803866528022257341741)
        ·
          refine ⟨146176449948008346503153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 389803866528022257341741 146176449948008346503153)
          ·
            refine ⟨109632337461006259877365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146176449948008346503153 109632337461006259877365)
            ·
              refine ⟨10278031636969336863503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 109632337461006259877365 10278031636969336863503)
              ·
                rfl

theorem cell19_101333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 5].length) (baseStart_101333 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_101333 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_101333 prefixEnd_101333 := by exact prefixLift 101333
  have htrace : WordTrace (prefixWord ++ tailWord_101333) baseStart_101333 baseEnd_101333 := by
    simpa [prefixWord, tailWord_101333, baseEnd_101333] using wordTrace_append hprefix tailTrace_101333
  have hstable : (prefixWord ++ tailWord_101333).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101333).length < 2 ^ (prefixWord ++ tailWord_101333).sum := by decide
  have hdescent : baseEnd_101333 < baseStart_101333 := by decide
  rcases family_descends (prefixWord ++ tailWord_101333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101354 : List Nat := [3, 1, 3, 1, 2, 2, 1, 6]
def baseStart_101354 : Nat := 118140960795 + 101354 * 2 ^ 59
def prefixEnd_101354 : Nat := 4983230072969 + 3 ^ 40 * 101354 * 2
def baseEnd_101354 : Nat := 30840484892386184123785

theorem tailTrace_101354 : CollatzResearch.WordTrace tailWord_101354 prefixEnd_101354 30840484892386184123785 := by
  unfold tailWord_101354
  simp only [CollatzResearch.WordTrace]
  refine ⟨924171018704810682549779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2464456049879495153466077 924171018704810682549779)
  ·
    refine ⟨1386256528057216023824669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 924171018704810682549779 1386256528057216023824669)
    ·
      refine ⟨519846198021456008934251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1386256528057216023824669 519846198021456008934251)
      ·
        refine ⟨779769297032184013401377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 519846198021456008934251 779769297032184013401377)
        ·
          refine ⟨584826972774138010051033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 779769297032184013401377 584826972774138010051033)
          ·
            refine ⟨438620229580603507538275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 584826972774138010051033 438620229580603507538275)
            ·
              refine ⟨657930344370905261307413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 438620229580603507538275 657930344370905261307413)
              ·
                refine ⟨30840484892386184123785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 657930344370905261307413 30840484892386184123785)
                ·
                  rfl

theorem cell19_101354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 6].length) (baseStart_101354 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_101354 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_101354 prefixEnd_101354 := by exact prefixLift 101354
  have htrace : WordTrace (prefixWord ++ tailWord_101354) baseStart_101354 baseEnd_101354 := by
    simpa [prefixWord, tailWord_101354, baseEnd_101354] using wordTrace_append hprefix tailTrace_101354
  have hstable : (prefixWord ++ tailWord_101354).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101354).length < 2 ^ (prefixWord ++ tailWord_101354).sum := by decide
  have hdescent : baseEnd_101354 < baseStart_101354 := by decide
  rcases family_descends (prefixWord ++ tailWord_101354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101409 : List Nat := [1, 2, 3, 2, 3, 3, 1, 4]
def baseStart_101409 : Nat := 118140960795 + 101409 * 2 ^ 59
def prefixEnd_101409 : Nat := 4983230072969 + 3 ^ 40 * 101409 * 2
def baseEnd_101409 : Nat := 30857220558162352901413

theorem tailTrace_101409 : CollatzResearch.WordTrace tailWord_101409 prefixEnd_101409 30857220558162352901413 := by
  unfold tailWord_101409
  simp only [CollatzResearch.WordTrace]
  refine ⟨3698690089619987123451281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2465793393079991415634187 3698690089619987123451281)
  ·
    refine ⟨2774017567214990342588461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3698690089619987123451281 2774017567214990342588461)
    ·
      refine ⟨1040256587705621378470673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2774017567214990342588461 1040256587705621378470673)
      ·
        refine ⟨780192440779216033853005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1040256587705621378470673 780192440779216033853005)
        ·
          refine ⟨292572165292206012694877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 780192440779216033853005 292572165292206012694877)
          ·
            refine ⟨109714561984577254760579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 292572165292206012694877 109714561984577254760579)
            ·
              refine ⟨164571842976865882140869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109714561984577254760579 164571842976865882140869)
              ·
                refine ⟨30857220558162352901413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 164571842976865882140869 30857220558162352901413)
                ·
                  rfl

theorem cell19_101409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 1, 4].length) (baseStart_101409 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_101409 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_101409 prefixEnd_101409 := by exact prefixLift 101409
  have htrace : WordTrace (prefixWord ++ tailWord_101409) baseStart_101409 baseEnd_101409 := by
    simpa [prefixWord, tailWord_101409, baseEnd_101409] using wordTrace_append hprefix tailTrace_101409
  have hstable : (prefixWord ++ tailWord_101409).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101409).length < 2 ^ (prefixWord ++ tailWord_101409).sum := by decide
  have hdescent : baseEnd_101409 < baseStart_101409 := by decide
  rcases family_descends (prefixWord ++ tailWord_101409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101411 : List Nat := [1, 1, 1, 4, 3, 2, 3, 4]
def baseStart_101411 : Nat := 118140960795 + 101411 * 2 ^ 59
def prefixEnd_101411 : Nat := 4983230072969 + 3 ^ 40 * 101411 * 2
def baseEnd_101411 : Nat := 30857829127826940856963

theorem tailTrace_101411 : CollatzResearch.WordTrace tailWord_101411 prefixEnd_101411 30857829127826940856963 := by
  unfold tailWord_101411
  simp only [CollatzResearch.WordTrace]
  refine ⟨3698763035612741465024087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2465842023741827643349391 3698763035612741465024087)
  ·
    refine ⟨5548144553419112197536131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3698763035612741465024087 5548144553419112197536131)
    ·
      refine ⟨8322216830128668296304197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5548144553419112197536131 8322216830128668296304197)
      ·
        refine ⟨1560415655649125305557037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8322216830128668296304197 1560415655649125305557037)
        ·
          refine ⟨585155870868421989583889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1560415655649125305557037 585155870868421989583889)
          ·
            refine ⟨438866903151316492187917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 585155870868421989583889 438866903151316492187917)
            ·
              refine ⟨164575088681743684570469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 438866903151316492187917 164575088681743684570469)
              ·
                refine ⟨30857829127826940856963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 164575088681743684570469 30857829127826940856963)
                ·
                  rfl

theorem cell19_101411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 3, 4].length) (baseStart_101411 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_101411 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_101411 prefixEnd_101411 := by exact prefixLift 101411
  have htrace : WordTrace (prefixWord ++ tailWord_101411) baseStart_101411 baseEnd_101411 := by
    simpa [prefixWord, tailWord_101411, baseEnd_101411] using wordTrace_append hprefix tailTrace_101411
  have hstable : (prefixWord ++ tailWord_101411).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101411).length < 2 ^ (prefixWord ++ tailWord_101411).sum := by decide
  have hdescent : baseEnd_101411 < baseStart_101411 := by decide
  rcases family_descends (prefixWord ++ tailWord_101411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101468 : List Nat := [2, 2, 4, 1, 1, 1, 2, 6]
def baseStart_101468 : Nat := 118140960795 + 101468 * 2 ^ 59
def prefixEnd_101468 : Nat := 4983230072969 + 3 ^ 40 * 101468 * 2
def baseEnd_101468 : Nat := 30875173363267697590141

theorem tailTrace_101468 : CollatzResearch.WordTrace tailWord_101468 prefixEnd_101468 30875173363267697590141 := by
  unfold tailWord_101468
  simp only [CollatzResearch.WordTrace]
  refine ⟨1850420998203120099924529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2467227997604160133232705 1850420998203120099924529)
  ·
    refine ⟨1387815748652340074943397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1850420998203120099924529 1387815748652340074943397)
    ·
      refine ⟨260215452872313764051887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1387815748652340074943397 260215452872313764051887)
      ·
        refine ⟨390323179308470646077831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260215452872313764051887 390323179308470646077831)
        ·
          refine ⟨585484768962705969116747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 390323179308470646077831 585484768962705969116747)
          ·
            refine ⟨878227153444058953675121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 585484768962705969116747 878227153444058953675121)
            ·
              refine ⟨658670365083044215256341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 878227153444058953675121 658670365083044215256341)
              ·
                refine ⟨30875173363267697590141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 658670365083044215256341 30875173363267697590141)
                ·
                  rfl

theorem cell19_101468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 6].length) (baseStart_101468 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_101468 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_101468 prefixEnd_101468 := by exact prefixLift 101468
  have htrace : WordTrace (prefixWord ++ tailWord_101468) baseStart_101468 baseEnd_101468 := by
    simpa [prefixWord, tailWord_101468, baseEnd_101468] using wordTrace_append hprefix tailTrace_101468
  have hstable : (prefixWord ++ tailWord_101468).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101468).length < 2 ^ (prefixWord ++ tailWord_101468).sum := by decide
  have hdescent : baseEnd_101468 < baseStart_101468 := by decide
  rcases family_descends (prefixWord ++ tailWord_101468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101485 : List Nat := [1, 5, 1, 1, 2, 2, 4, 3]
def baseStart_101485 : Nat := 118140960795 + 101485 * 2 ^ 59
def prefixEnd_101485 : Nat := 4983230072969 + 3 ^ 40 * 101485 * 2
def baseEnd_101485 : Nat := 30880346205416695212317

theorem tailTrace_101485 : CollatzResearch.WordTrace tailWord_101485 prefixEnd_101485 30880346205416695212317 := by
  unfold tailWord_101485
  simp only [CollatzResearch.WordTrace]
  refine ⟨3701462037344652103217909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2467641358229768068811939 3701462037344652103217909)
  ·
    refine ⟨347012066001061134676679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3701462037344652103217909 347012066001061134676679)
    ·
      refine ⟨520518099001591702015019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 347012066001061134676679 520518099001591702015019)
      ·
        refine ⟨780777148502387553022529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 520518099001591702015019 780777148502387553022529)
        ·
          refine ⟨585582861376790664766897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 780777148502387553022529 585582861376790664766897)
          ·
            refine ⟨439187146032592998575173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 585582861376790664766897 439187146032592998575173)
            ·
              refine ⟨82347589881111187232845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 439187146032592998575173 82347589881111187232845)
              ·
                refine ⟨30880346205416695212317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82347589881111187232845 30880346205416695212317)
                ·
                  rfl

theorem cell19_101485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 4, 3].length) (baseStart_101485 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_101485 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_101485 prefixEnd_101485 := by exact prefixLift 101485
  have htrace : WordTrace (prefixWord ++ tailWord_101485) baseStart_101485 baseEnd_101485 := by
    simpa [prefixWord, tailWord_101485, baseEnd_101485] using wordTrace_append hprefix tailTrace_101485
  have hstable : (prefixWord ++ tailWord_101485).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101485).length < 2 ^ (prefixWord ++ tailWord_101485).sum := by decide
  have hdescent : baseEnd_101485 < baseStart_101485 := by decide
  rcases family_descends (prefixWord ++ tailWord_101485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101574 : List Nat := [6, 1, 2, 2, 1, 2, 1, 4]
def baseStart_101574 : Nat := 118140960795 + 101574 * 2 ^ 59
def prefixEnd_101574 : Nat := 4983230072969 + 3 ^ 40 * 101574 * 2
def baseEnd_101574 : Nat := 30907427555490859234297

theorem tailTrace_101574 : CollatzResearch.WordTrace tailWord_101574 prefixEnd_101574 30907427555490859234297 := by
  unfold tailWord_101574
  simp only [CollatzResearch.WordTrace]
  refine ⟨115772129188194384475243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 2469805422681480202138517 115772129188194384475243)
  ·
    refine ⟨173658193782291576712865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115772129188194384475243 173658193782291576712865)
    ·
      refine ⟨130243645336718682534649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173658193782291576712865 130243645336718682534649)
      ·
        refine ⟨97682734002539011900987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130243645336718682534649 97682734002539011900987)
        ·
          refine ⟨146524101003808517851481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97682734002539011900987 146524101003808517851481)
          ·
            refine ⟨109893075752856388388611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146524101003808517851481 109893075752856388388611)
            ·
              refine ⟨164839613629284582582917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109893075752856388388611 164839613629284582582917)
              ·
                refine ⟨30907427555490859234297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 164839613629284582582917 30907427555490859234297)
                ·
                  rfl

theorem cell19_101574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_101574 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_101574 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_101574 prefixEnd_101574 := by exact prefixLift 101574
  have htrace : WordTrace (prefixWord ++ tailWord_101574) baseStart_101574 baseEnd_101574 := by
    simpa [prefixWord, tailWord_101574, baseEnd_101574] using wordTrace_append hprefix tailTrace_101574
  have hstable : (prefixWord ++ tailWord_101574).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101574).length < 2 ^ (prefixWord ++ tailWord_101574).sum := by decide
  have hdescent : baseEnd_101574 < baseStart_101574 := by decide
  rcases family_descends (prefixWord ++ tailWord_101574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101597 : List Nat := [1, 4, 3, 2, 2, 1, 3, 3]
def baseStart_101597 : Nat := 118140960795 + 101597 * 2 ^ 59
def prefixEnd_101597 : Nat := 4983230072969 + 3 ^ 40 * 101597 * 2
def baseEnd_101597 : Nat := 30914426106633620723123

theorem tailTrace_101597 : CollatzResearch.WordTrace tailWord_101597 prefixEnd_101597 30914426106633620723123 := by
  unfold tailWord_101597
  simp only [CollatzResearch.WordTrace]
  refine ⟨3705547012938895231295045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2470364675292596820863363 3705547012938895231295045)
  ·
    refine ⟨694790064926042855867821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3705547012938895231295045 694790064926042855867821)
    ·
      refine ⟨260546274347266070950433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 694790064926042855867821 260546274347266070950433)
      ·
        refine ⟨195409705760449553212825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 260546274347266070950433 195409705760449553212825)
        ·
          refine ⟨146557279320337164909619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 195409705760449553212825 146557279320337164909619)
          ·
            refine ⟨219835918980505747364429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146557279320337164909619 219835918980505747364429)
            ·
              refine ⟨82438469617689655261661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 219835918980505747364429 82438469617689655261661)
              ·
                refine ⟨30914426106633620723123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82438469617689655261661 30914426106633620723123)
                ·
                  rfl

theorem cell19_101597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 3, 3].length) (baseStart_101597 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_101597 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_101597 prefixEnd_101597 := by exact prefixLift 101597
  have htrace : WordTrace (prefixWord ++ tailWord_101597) baseStart_101597 baseEnd_101597 := by
    simpa [prefixWord, tailWord_101597, baseEnd_101597] using wordTrace_append hprefix tailTrace_101597
  have hstable : (prefixWord ++ tailWord_101597).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101597).length < 2 ^ (prefixWord ++ tailWord_101597).sum := by decide
  have hdescent : baseEnd_101597 < baseStart_101597 := by decide
  rcases family_descends (prefixWord ++ tailWord_101597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101641 : List Nat := [1, 2, 1, 1, 3, 3, 2, 6]
def baseStart_101641 : Nat := 118140960795 + 101641 * 2 ^ 59
def prefixEnd_101641 : Nat := 4983230072969 + 3 ^ 40 * 101641 * 2
def baseEnd_101641 : Nat := 30927814639254555745225

theorem tailTrace_101641 : CollatzResearch.WordTrace tailWord_101641 prefixEnd_101641 30927814639254555745225 := by
  unfold tailWord_101641
  simp only [CollatzResearch.WordTrace]
  refine ⟨3707151824779490745896777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2471434549852993830597851 3707151824779490745896777)
  ·
    refine ⟨2780363868584618059422583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3707151824779490745896777 2780363868584618059422583)
    ·
      refine ⟨4170545802876927089133875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2780363868584618059422583 4170545802876927089133875)
      ·
        refine ⟨6255818704315390633700813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4170545802876927089133875 6255818704315390633700813)
        ·
          refine ⟨2345932014118271487637805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6255818704315390633700813 2345932014118271487637805)
          ·
            refine ⟨879724505294351807864177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2345932014118271487637805 879724505294351807864177)
            ·
              refine ⟨659793378970763855898133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 879724505294351807864177 659793378970763855898133)
              ·
                refine ⟨30927814639254555745225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 659793378970763855898133 30927814639254555745225)
                ·
                  rfl

theorem cell19_101641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 6].length) (baseStart_101641 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_101641 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_101641 prefixEnd_101641 := by exact prefixLift 101641
  have htrace : WordTrace (prefixWord ++ tailWord_101641) baseStart_101641 baseEnd_101641 := by
    simpa [prefixWord, tailWord_101641, baseEnd_101641] using wordTrace_append hprefix tailTrace_101641
  have hstable : (prefixWord ++ tailWord_101641).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101641).length < 2 ^ (prefixWord ++ tailWord_101641).sum := by decide
  have hdescent : baseEnd_101641 < baseStart_101641 := by decide
  rcases family_descends (prefixWord ++ tailWord_101641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101650 : List Nat := [3, 2, 4, 2, 2, 1, 2, 3]
def baseStart_101650 : Nat := 118140960795 + 101650 * 2 ^ 59
def prefixEnd_101650 : Nat := 4983230072969 + 3 ^ 40 * 101650 * 2
def baseEnd_101650 : Nat := 30930553202745201545201

theorem tailTrace_101650 : CollatzResearch.WordTrace tailWord_101650 prefixEnd_101650 30930553202745201545201 := by
  unfold tailWord_101650
  simp only [CollatzResearch.WordTrace]
  refine ⟨926870020436721320743601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2471653387831256855316269 926870020436721320743601)
  ·
    refine ⟨695152515327540990557701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 926870020436721320743601 695152515327540990557701)
    ·
      refine ⟨130341096623913935729569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 695152515327540990557701 130341096623913935729569)
      ·
        refine ⟨97755822467935451797177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130341096623913935729569 97755822467935451797177)
        ·
          refine ⟨73316866850951588847883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97755822467935451797177 73316866850951588847883)
          ·
            refine ⟨109975300276427383271825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73316866850951588847883 109975300276427383271825)
            ·
              refine ⟨82481475207320537453869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109975300276427383271825 82481475207320537453869)
              ·
                refine ⟨30930553202745201545201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82481475207320537453869 30930553202745201545201)
                ·
                  rfl

theorem cell19_101650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 2, 3].length) (baseStart_101650 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_101650 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_101650 prefixEnd_101650 := by exact prefixLift 101650
  have htrace : WordTrace (prefixWord ++ tailWord_101650) baseStart_101650 baseEnd_101650 := by
    simpa [prefixWord, tailWord_101650, baseEnd_101650] using wordTrace_append hprefix tailTrace_101650
  have hstable : (prefixWord ++ tailWord_101650).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101650).length < 2 ^ (prefixWord ++ tailWord_101650).sum := by decide
  have hdescent : baseEnd_101650 < baseStart_101650 := by decide
  rcases family_descends (prefixWord ++ tailWord_101650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101656 : List Nat := [2, 1, 2, 3, 1, 5, 2, 3]
def baseStart_101656 : Nat := 118140960795 + 101656 * 2 ^ 59
def prefixEnd_101656 : Nat := 4983230072969 + 3 ^ 40 * 101656 * 2
def baseEnd_101656 : Nat := 30932378911738965411851

theorem tailTrace_101656 : CollatzResearch.WordTrace tailWord_101656 prefixEnd_101656 30932378911738965411851 := by
  unfold tailWord_101656
  simp only [CollatzResearch.WordTrace]
  refine ⟨1853849459862574153846411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2471799279816765538461881 1853849459862574153846411)
  ·
    refine ⟨2780774189793861230769617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1853849459862574153846411 2780774189793861230769617)
    ·
      refine ⟨2085580642345395923077213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2780774189793861230769617 2085580642345395923077213)
      ·
        refine ⟨782092740879523471153955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2085580642345395923077213 782092740879523471153955)
        ·
          refine ⟨1173139111319285206730933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 782092740879523471153955 1173139111319285206730933)
          ·
            refine ⟨109981791686182988131025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1173139111319285206730933 109981791686182988131025)
            ·
              refine ⟨82486343764637241098269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109981791686182988131025 82486343764637241098269)
              ·
                refine ⟨30932378911738965411851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82486343764637241098269 30932378911738965411851)
                ·
                  rfl

theorem cell19_101656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 2, 3].length) (baseStart_101656 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_101656 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_101656 prefixEnd_101656 := by exact prefixLift 101656
  have htrace : WordTrace (prefixWord ++ tailWord_101656) baseStart_101656 baseEnd_101656 := by
    simpa [prefixWord, tailWord_101656, baseEnd_101656] using wordTrace_append hprefix tailTrace_101656
  have hstable : (prefixWord ++ tailWord_101656).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101656).length < 2 ^ (prefixWord ++ tailWord_101656).sum := by decide
  have hdescent : baseEnd_101656 < baseStart_101656 := by decide
  rcases family_descends (prefixWord ++ tailWord_101656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101658 : List Nat := [3, 1, 1, 3, 3, 2, 1, 5]
def baseStart_101658 : Nat := 118140960795 + 101658 * 2 ^ 59
def prefixEnd_101658 : Nat := 4983230072969 + 3 ^ 40 * 101658 * 2
def baseEnd_101658 : Nat := 30932987481403553367401

theorem tailTrace_101658 : CollatzResearch.WordTrace tailWord_101658 prefixEnd_101658 30932987481403553367401 := by
  unfold tailWord_101658
  simp only [CollatzResearch.WordTrace]
  refine ⟨926942966429475662316407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2471847910478601766177085 926942966429475662316407)
  ·
    refine ⟨1390414449644213493474611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 926942966429475662316407 1390414449644213493474611)
    ·
      refine ⟨2085621674466320240211917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1390414449644213493474611 2085621674466320240211917)
      ·
        refine ⟨782108127924870090079469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2085621674466320240211917 782108127924870090079469)
        ·
          refine ⟨293290547971826283779801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 782108127924870090079469 293290547971826283779801)
          ·
            refine ⟨219967910978869712834851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 293290547971826283779801 219967910978869712834851)
            ·
              refine ⟨329951866468304569252277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 219967910978869712834851 329951866468304569252277)
              ·
                refine ⟨30932987481403553367401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 329951866468304569252277 30932987481403553367401)
                ·
                  rfl

theorem cell19_101658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 5].length) (baseStart_101658 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_101658 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_101658 prefixEnd_101658 := by exact prefixLift 101658
  have htrace : WordTrace (prefixWord ++ tailWord_101658) baseStart_101658 baseEnd_101658 := by
    simpa [prefixWord, tailWord_101658, baseEnd_101658] using wordTrace_append hprefix tailTrace_101658
  have hstable : (prefixWord ++ tailWord_101658).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101658).length < 2 ^ (prefixWord ++ tailWord_101658).sum := by decide
  have hdescent : baseEnd_101658 < baseStart_101658 := by decide
  rcases family_descends (prefixWord ++ tailWord_101658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101736 : List Nat := [2, 1, 4, 2, 10]
def baseStart_101736 : Nat := 118140960795 + 101736 * 2 ^ 59
def prefixEnd_101736 : Nat := 4983230072969 + 3 ^ 40 * 101736 * 2
def baseEnd_101736 : Nat := 1146545248086017912365

theorem tailTrace_101736 : CollatzResearch.WordTrace tailWord_101736 prefixEnd_101736 1146545248086017912365 := by
  unfold tailWord_101736
  simp only [CollatzResearch.WordTrace]
  refine ⟨1855308379717660985302531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2473744506290214647070041 1855308379717660985302531)
  ·
    refine ⟨2782962569576491477953797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1855308379717660985302531 2782962569576491477953797)
    ·
      refine ⟨521805481795592152116337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2782962569576491477953797 521805481795592152116337)
      ·
        refine ⟨391354111346694114087253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 521805481795592152116337 391354111346694114087253)
        ·
          refine ⟨1146545248086017912365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 391354111346694114087253 1146545248086017912365)
          ·
            rfl

theorem cell19_101736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 10].length) (baseStart_101736 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_101736 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_101736 prefixEnd_101736 := by exact prefixLift 101736
  have htrace : WordTrace (prefixWord ++ tailWord_101736) baseStart_101736 baseEnd_101736 := by
    simpa [prefixWord, tailWord_101736, baseEnd_101736] using wordTrace_append hprefix tailTrace_101736
  have hstable : (prefixWord ++ tailWord_101736).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101736).length < 2 ^ (prefixWord ++ tailWord_101736).sum := by decide
  have hdescent : baseEnd_101736 < baseStart_101736 := by decide
  rcases family_descends (prefixWord ++ tailWord_101736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101749 : List Nat := [1, 3, 4, 1, 4, 1, 1, 4]
def baseStart_101749 : Nat := 118140960795 + 101749 * 2 ^ 59
def prefixEnd_101749 : Nat := 4983230072969 + 3 ^ 40 * 101749 * 2
def baseEnd_101749 : Nat := 30960677401142305344931

theorem tailTrace_101749 : CollatzResearch.WordTrace tailWord_101749 prefixEnd_101749 30960677401142305344931 := by
  unfold tailWord_101749
  simp only [CollatzResearch.WordTrace]
  refine ⟨3711090908388225190828301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2474060605592150127218867 3711090908388225190828301)
  ·
    refine ⟨1391659090645584446560613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3711090908388225190828301 1391659090645584446560613)
    ·
      refine ⟨260936079496047083730115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1391659090645584446560613 260936079496047083730115)
      ·
        refine ⟨391404119244070625595173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260936079496047083730115 391404119244070625595173)
        ·
          refine ⟨73388272358263242299095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 391404119244070625595173 73388272358263242299095)
          ·
            refine ⟨110082408537394863448643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73388272358263242299095 110082408537394863448643)
            ·
              refine ⟨165123612806092295172965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110082408537394863448643 165123612806092295172965)
              ·
                refine ⟨30960677401142305344931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 165123612806092295172965 30960677401142305344931)
                ·
                  rfl

theorem cell19_101749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 1, 4].length) (baseStart_101749 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_101749 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_101749 prefixEnd_101749 := by exact prefixLift 101749
  have htrace : WordTrace (prefixWord ++ tailWord_101749) baseStart_101749 baseEnd_101749 := by
    simpa [prefixWord, tailWord_101749, baseEnd_101749] using wordTrace_append hprefix tailTrace_101749
  have hstable : (prefixWord ++ tailWord_101749).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101749).length < 2 ^ (prefixWord ++ tailWord_101749).sum := by decide
  have hdescent : baseEnd_101749 < baseStart_101749 := by decide
  rcases family_descends (prefixWord ++ tailWord_101749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101772 : List Nat := [2, 2, 1, 2, 1, 3, 5, 3]
def baseStart_101772 : Nat := 118140960795 + 101772 * 2 ^ 59
def prefixEnd_101772 : Nat := 4983230072969 + 3 ^ 40 * 101772 * 2
def baseEnd_101772 : Nat := 30967675952285066833757

theorem tailTrace_101772 : CollatzResearch.WordTrace tailWord_101772 prefixEnd_101772 30967675952285066833757 := by
  unfold tailWord_101772
  simp only [CollatzResearch.WordTrace]
  refine ⟨1855964893652450059457785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2474619858203266745943713 1855964893652450059457785)
  ·
    refine ⟨1391973670239337544593339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1855964893652450059457785 1391973670239337544593339)
    ·
      refine ⟨2087960505359006316890009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1391973670239337544593339 2087960505359006316890009)
      ·
        refine ⟨1565970379019254737667507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2087960505359006316890009 1565970379019254737667507)
        ·
          refine ⟨2348955568528882106501261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1565970379019254737667507 2348955568528882106501261)
          ·
            refine ⟨880858338198330789937973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2348955568528882106501261 880858338198330789937973)
            ·
              refine ⟨82580469206093511556685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 880858338198330789937973 82580469206093511556685)
              ·
                refine ⟨30967675952285066833757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82580469206093511556685 30967675952285066833757)
                ·
                  rfl

theorem cell19_101772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 5, 3].length) (baseStart_101772 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_101772 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_101772 prefixEnd_101772 := by exact prefixLift 101772
  have htrace : WordTrace (prefixWord ++ tailWord_101772) baseStart_101772 baseEnd_101772 := by
    simpa [prefixWord, tailWord_101772, baseEnd_101772] using wordTrace_append hprefix tailTrace_101772
  have hstable : (prefixWord ++ tailWord_101772).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101772).length < 2 ^ (prefixWord ++ tailWord_101772).sum := by decide
  have hdescent : baseEnd_101772 < baseStart_101772 := by decide
  rcases family_descends (prefixWord ++ tailWord_101772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101831 : List Nat := [1, 1, 4, 1, 1, 3, 3, 5]
def baseStart_101831 : Nat := 118140960795 + 101831 * 2 ^ 59
def prefixEnd_101831 : Nat := 4983230072969 + 3 ^ 40 * 101831 * 2
def baseEnd_101831 : Nat := 30985628757390411522485

theorem tailTrace_101831 : CollatzResearch.WordTrace tailWord_101831 prefixEnd_101831 30985628757390411522485 := by
  unfold tailWord_101831
  simp only [CollatzResearch.WordTrace]
  refine ⟨3714081694091153195313347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2476054462727435463542231 3714081694091153195313347)
  ·
    refine ⟨5571122541136729792970021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3714081694091153195313347 5571122541136729792970021)
    ·
      refine ⟨1044585476463136836181879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5571122541136729792970021 1044585476463136836181879)
      ·
        refine ⟨1566878214694705254272819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1044585476463136836181879 1566878214694705254272819)
        ·
          refine ⟨2350317322042057881409229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1566878214694705254272819 2350317322042057881409229)
          ·
            refine ⟨881368995765771705528461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2350317322042057881409229 881368995765771705528461)
            ·
              refine ⟨330513373412164389573173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 881368995765771705528461 330513373412164389573173)
              ·
                refine ⟨30985628757390411522485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 330513373412164389573173 30985628757390411522485)
                ·
                  rfl

theorem cell19_101831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 5].length) (baseStart_101831 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_101831 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_101831 prefixEnd_101831 := by exact prefixLift 101831
  have htrace : WordTrace (prefixWord ++ tailWord_101831) baseStart_101831 baseEnd_101831 := by
    simpa [prefixWord, tailWord_101831, baseEnd_101831] using wordTrace_append hprefix tailTrace_101831
  have hstable : (prefixWord ++ tailWord_101831).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101831).length < 2 ^ (prefixWord ++ tailWord_101831).sum := by decide
  have hdescent : baseEnd_101831 < baseStart_101831 := by decide
  rcases family_descends (prefixWord ++ tailWord_101831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101846 : List Nat := [5, 2, 1, 1, 1, 4, 5]
def baseStart_101846 : Nat := 118140960795 + 101846 * 2 ^ 59
def prefixEnd_101846 : Nat := 4983230072969 + 3 ^ 40 * 101846 * 2
def baseEnd_101846 : Nat := 10330064343291607063037

theorem tailTrace_101846 : CollatzResearch.WordTrace tailWord_101846 prefixEnd_101846 10330064343291607063037 := by
  unfold tailWord_101846
  simp only [CollatzResearch.WordTrace]
  refine ⟨232164299314800672319337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2476419192691207171406261 232164299314800672319337)
  ·
    refine ⟨174123224486100504239503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232164299314800672319337 174123224486100504239503)
    ·
      refine ⟨261184836729150756359255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174123224486100504239503 261184836729150756359255)
      ·
        refine ⟨391777255093726134538883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261184836729150756359255 391777255093726134538883)
        ·
          refine ⟨587665882640589201808325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 391777255093726134538883 587665882640589201808325)
          ·
            refine ⟨110187352995110475339061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 587665882640589201808325 110187352995110475339061)
            ·
              refine ⟨10330064343291607063037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 110187352995110475339061 10330064343291607063037)
              ·
                rfl

theorem cell19_101846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 5].length) (baseStart_101846 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_101846 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_101846 prefixEnd_101846 := by exact prefixLift 101846
  have htrace : WordTrace (prefixWord ++ tailWord_101846) baseStart_101846 baseEnd_101846 := by
    simpa [prefixWord, tailWord_101846, baseEnd_101846] using wordTrace_append hprefix tailTrace_101846
  have hstable : (prefixWord ++ tailWord_101846).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101846).length < 2 ^ (prefixWord ++ tailWord_101846).sum := by decide
  have hdescent : baseEnd_101846 < baseStart_101846 := by decide
  rcases family_descends (prefixWord ++ tailWord_101846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101850 : List Nat := [3, 1, 1, 2, 3, 2, 7]
def baseStart_101850 : Nat := 118140960795 + 101850 * 2 ^ 59
def prefixEnd_101850 : Nat := 4983230072969 + 3 ^ 40 * 101850 * 2
def baseEnd_101850 : Nat := 10330470056401332366737

theorem tailTrace_101850 : CollatzResearch.WordTrace tailWord_101850 prefixEnd_101850 10330470056401332366737 := by
  unfold tailWord_101850
  simp only [CollatzResearch.WordTrace]
  refine ⟨928693670255579860063751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2476516454014879626836669 928693670255579860063751)
  ·
    refine ⟨1393040505383369790095627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 928693670255579860063751 1393040505383369790095627)
    ·
      refine ⟨2089560758075054685143441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1393040505383369790095627 2089560758075054685143441)
      ·
        refine ⟨1567170568556291013857581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2089560758075054685143441 1567170568556291013857581)
        ·
          refine ⟨587688963208609130196593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1567170568556291013857581 587688963208609130196593)
          ·
            refine ⟨440766722406456847647445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 587688963208609130196593 440766722406456847647445)
            ·
              refine ⟨10330470056401332366737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 440766722406456847647445 10330470056401332366737)
              ·
                rfl

theorem cell19_101850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 7].length) (baseStart_101850 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_101850 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_101850 prefixEnd_101850 := by exact prefixLift 101850
  have htrace : WordTrace (prefixWord ++ tailWord_101850) baseStart_101850 baseEnd_101850 := by
    simpa [prefixWord, tailWord_101850, baseEnd_101850] using wordTrace_append hprefix tailTrace_101850
  have hstable : (prefixWord ++ tailWord_101850).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101850).length < 2 ^ (prefixWord ++ tailWord_101850).sum := by decide
  have hdescent : baseEnd_101850 < baseStart_101850 := by decide
  rcases family_descends (prefixWord ++ tailWord_101850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101901 : List Nat := [1, 7, 1, 1, 3, 6]
def baseStart_101901 : Nat := 118140960795 + 101901 * 2 ^ 59
def prefixEnd_101901 : Nat := 4983230072969 + 3 ^ 40 * 101901 * 2
def baseEnd_101901 : Nat := 3445214299516776662971

theorem tailTrace_101901 : CollatzResearch.WordTrace tailWord_101901 prefixEnd_101901 3445214299516776662971 := by
  unfold tailWord_101901
  simp only [CollatzResearch.WordTrace]
  refine ⟨3716634803837555150361557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2477756535891703433574371 3716634803837555150361557)
  ·
    refine ⟨87108628214942698836599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 3716634803837555150361557 87108628214942698836599)
    ·
      refine ⟨130662942322414048254899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87108628214942698836599 130662942322414048254899)
      ·
        refine ⟨195994413483621072382349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130662942322414048254899 195994413483621072382349)
        ·
          refine ⟨73497905056357902143381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 195994413483621072382349 73497905056357902143381)
          ·
            refine ⟨3445214299516776662971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 73497905056357902143381 3445214299516776662971)
            ·
              rfl

theorem cell19_101901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 6].length) (baseStart_101901 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_101901 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_101901 prefixEnd_101901 := by exact prefixLift 101901
  have htrace : WordTrace (prefixWord ++ tailWord_101901) baseStart_101901 baseEnd_101901 := by
    simpa [prefixWord, tailWord_101901, baseEnd_101901] using wordTrace_append hprefix tailTrace_101901
  have hstable : (prefixWord ++ tailWord_101901).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101901).length < 2 ^ (prefixWord ++ tailWord_101901).sum := by decide
  have hdescent : baseEnd_101901 < baseStart_101901 := by decide
  rcases family_descends (prefixWord ++ tailWord_101901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101943 : List Nat := [1, 1, 3, 1, 2, 5, 3, 3]
def baseStart_101943 : Nat := 118140960795 + 101943 * 2 ^ 59
def prefixEnd_101943 : Nat := 4983230072969 + 3 ^ 40 * 101943 * 2
def baseEnd_101943 : Nat := 31019708658607337033291

theorem tailTrace_101943 : CollatzResearch.WordTrace tailWord_101943 prefixEnd_101943 31019708658607337033291 := by
  unfold tailWord_101943
  simp only [CollatzResearch.WordTrace]
  refine ⟨3718166669685396323390483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2478777779790264215593655 3718166669685396323390483)
  ·
    refine ⟨5577250004528094485085725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3718166669685396323390483 5577250004528094485085725)
    ·
      refine ⟨2091468751698035431907147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5577250004528094485085725 2091468751698035431907147)
      ·
        refine ⟨3137203127547053147860721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2091468751698035431907147 3137203127547053147860721)
        ·
          refine ⟨2352902345660289860895541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3137203127547053147860721 2352902345660289860895541)
          ·
            refine ⟨220584594905652174458957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2352902345660289860895541 220584594905652174458957)
            ·
              refine ⟨82719223089619565422109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 220584594905652174458957 82719223089619565422109)
              ·
                refine ⟨31019708658607337033291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82719223089619565422109 31019708658607337033291)
                ·
                  rfl

theorem cell19_101943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 3, 3].length) (baseStart_101943 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_101943 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_101943 prefixEnd_101943 := by exact prefixLift 101943
  have htrace : WordTrace (prefixWord ++ tailWord_101943) baseStart_101943 baseEnd_101943 := by
    simpa [prefixWord, tailWord_101943, baseEnd_101943] using wordTrace_append hprefix tailTrace_101943
  have hstable : (prefixWord ++ tailWord_101943).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101943).length < 2 ^ (prefixWord ++ tailWord_101943).sum := by decide
  have hdescent : baseEnd_101943 < baseStart_101943 := by decide
  rcases family_descends (prefixWord ++ tailWord_101943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101964 : List Nat := [2, 2, 1, 3, 1, 4, 6]
def baseStart_101964 : Nat := 118140960795 + 101964 * 2 ^ 59
def prefixEnd_101964 : Nat := 4983230072969 + 3 ^ 40 * 101964 * 2
def baseEnd_101964 : Nat := 10342032880028503522189

theorem tailTrace_101964 : CollatzResearch.WordTrace tailWord_101964 prefixEnd_101964 10342032880028503522189 := by
  unfold tailWord_101964
  simp only [CollatzResearch.WordTrace]
  refine ⟨1859466301304658454952473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2479288401739544606603297 1859466301304658454952473)
  ·
    refine ⟨1394599725978493841214355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1859466301304658454952473 1394599725978493841214355)
    ·
      refine ⟨2091899588967740761821533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1394599725978493841214355 2091899588967740761821533)
      ·
        refine ⟨784462345862902785683075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2091899588967740761821533 784462345862902785683075)
        ·
          refine ⟨1176693518794354178524613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 784462345862902785683075 1176693518794354178524613)
          ·
            refine ⟨220630034773941408473365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1176693518794354178524613 220630034773941408473365)
            ·
              refine ⟨10342032880028503522189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 220630034773941408473365 10342032880028503522189)
              ·
                rfl

theorem cell19_101964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 6].length) (baseStart_101964 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_101964 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_101964 prefixEnd_101964 := by exact prefixLift 101964
  have htrace : WordTrace (prefixWord ++ tailWord_101964) baseStart_101964 baseEnd_101964 := by
    simpa [prefixWord, tailWord_101964, baseEnd_101964] using wordTrace_append hprefix tailTrace_101964
  have hstable : (prefixWord ++ tailWord_101964).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101964).length < 2 ^ (prefixWord ++ tailWord_101964).sum := by decide
  have hdescent : baseEnd_101964 < baseStart_101964 := by decide
  rcases family_descends (prefixWord ++ tailWord_101964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102000 : List Nat := [2, 1, 1, 1, 6, 1, 4, 3]
def baseStart_102000 : Nat := 118140960795 + 102000 * 2 ^ 59
def prefixEnd_102000 : Nat := 4983230072969 + 3 ^ 40 * 102000 * 2
def baseEnd_102000 : Nat := 31037052894048093766469

theorem tailTrace_102000 : CollatzResearch.WordTrace tailWord_102000 prefixEnd_102000 31037052894048093766469 := by
  unfold tailWord_102000
  simp only [CollatzResearch.WordTrace]
  refine ⟨1860122815239447529107727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2480163753652596705476969 1860122815239447529107727)
  ·
    refine ⟨2790184222859171293661591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1860122815239447529107727 2790184222859171293661591)
    ·
      refine ⟨4185276334288756940492387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2790184222859171293661591 4185276334288756940492387)
      ·
        refine ⟨6277914501433135410738581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4185276334288756940492387 6277914501433135410738581)
        ·
          refine ⟨294277242254678222378371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 6277914501433135410738581 294277242254678222378371)
          ·
            refine ⟨441415863382017333567557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 294277242254678222378371 441415863382017333567557)
            ·
              refine ⟨82765474384128250043917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 441415863382017333567557 82765474384128250043917)
              ·
                refine ⟨31037052894048093766469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82765474384128250043917 31037052894048093766469)
                ·
                  rfl

theorem cell19_102000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 4, 3].length) (baseStart_102000 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_102000 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_102000 prefixEnd_102000 := by exact prefixLift 102000
  have htrace : WordTrace (prefixWord ++ tailWord_102000) baseStart_102000 baseEnd_102000 := by
    simpa [prefixWord, tailWord_102000, baseEnd_102000] using wordTrace_append hprefix tailTrace_102000
  have hstable : (prefixWord ++ tailWord_102000).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102000).length < 2 ^ (prefixWord ++ tailWord_102000).sum := by decide
  have hdescent : baseEnd_102000 < baseStart_102000 := by decide
  rcases family_descends (prefixWord ++ tailWord_102000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102036 : List Nat := [2, 4, 2, 2, 2, 1, 2, 4]
def baseStart_102036 : Nat := 118140960795 + 102036 * 2 ^ 59
def prefixEnd_102036 : Nat := 4983230072969 + 3 ^ 40 * 102036 * 2
def baseEnd_102036 : Nat := 31048007148010676966371

theorem tailTrace_102036 : CollatzResearch.WordTrace tailWord_102036 prefixEnd_102036 31048007148010676966371 := by
  unfold tailWord_102036
  simp only [CollatzResearch.WordTrace]
  refine ⟨1860779329174236603262981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2481039105565648804350641 1860779329174236603262981)
  ·
    refine ⟨348896124220169363111809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1860779329174236603262981 348896124220169363111809)
    ·
      refine ⟨261672093165127022333857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 348896124220169363111809 261672093165127022333857)
      ·
        refine ⟨196254069873845266750393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 261672093165127022333857 196254069873845266750393)
        ·
          refine ⟨147190552405383950062795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196254069873845266750393 147190552405383950062795)
          ·
            refine ⟨220785828608075925094193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147190552405383950062795 220785828608075925094193)
            ·
              refine ⟨165589371456056943820645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 220785828608075925094193 165589371456056943820645)
              ·
                refine ⟨31048007148010676966371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 165589371456056943820645 31048007148010676966371)
                ·
                  rfl

theorem cell19_102036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 2, 4].length) (baseStart_102036 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_102036 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_102036 prefixEnd_102036 := by exact prefixLift 102036
  have htrace : WordTrace (prefixWord ++ tailWord_102036) baseStart_102036 baseEnd_102036 := by
    simpa [prefixWord, tailWord_102036, baseEnd_102036] using wordTrace_append hprefix tailTrace_102036
  have hstable : (prefixWord ++ tailWord_102036).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102036).length < 2 ^ (prefixWord ++ tailWord_102036).sum := by decide
  have hdescent : baseEnd_102036 < baseStart_102036 := by decide
  rcases family_descends (prefixWord ++ tailWord_102036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102040 : List Nat := [2, 1, 2, 4, 1, 2, 1, 6]
def baseStart_102040 : Nat := 118140960795 + 102040 * 2 ^ 59
def prefixEnd_102040 : Nat := 4983230072969 + 3 ^ 40 * 102040 * 2
def baseEnd_102040 : Nat := 31049224287339852877471

theorem tailTrace_102040 : CollatzResearch.WordTrace tailWord_102040 prefixEnd_102040 31049224287339852877471 := by
  unfold tailWord_102040
  simp only [CollatzResearch.WordTrace]
  refine ⟨1860852275166990944835787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2481136366889321259781049 1860852275166990944835787)
  ·
    refine ⟨2791278412750486417253681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1860852275166990944835787 2791278412750486417253681)
    ·
      refine ⟨2093458809562864812940261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2791278412750486417253681 2093458809562864812940261)
      ·
        refine ⟨392523526793037152426299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2093458809562864812940261 392523526793037152426299)
        ·
          refine ⟨588785290189555728639449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 392523526793037152426299 588785290189555728639449)
          ·
            refine ⟨441588967642166796479587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 588785290189555728639449 441588967642166796479587)
            ·
              refine ⟨662383451463250194719381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 441588967642166796479587 662383451463250194719381)
              ·
                refine ⟨31049224287339852877471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 662383451463250194719381 31049224287339852877471)
                ·
                  rfl

theorem cell19_102040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 6].length) (baseStart_102040 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_102040 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_102040 prefixEnd_102040 := by exact prefixLift 102040
  have htrace : WordTrace (prefixWord ++ tailWord_102040) baseStart_102040 baseEnd_102040 := by
    simpa [prefixWord, tailWord_102040, baseEnd_102040] using wordTrace_append hprefix tailTrace_102040
  have hstable : (prefixWord ++ tailWord_102040).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102040).length < 2 ^ (prefixWord ++ tailWord_102040).sum := by decide
  have hdescent : baseEnd_102040 < baseStart_102040 := by decide
  rcases family_descends (prefixWord ++ tailWord_102040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102078 : List Nat := [4, 2, 1, 1, 2, 9]
def baseStart_102078 : Nat := 118140960795 + 102078 * 2 ^ 59
def prefixEnd_102078 : Nat := 4983230072969 + 3 ^ 40 * 102078 * 2
def baseEnd_102078 : Nat := 3451198567885224892547

theorem tailTrace_102078 : CollatzResearch.WordTrace tailWord_102078 prefixEnd_102078 3451198567885224892547 := by
  unfold tailWord_102078
  simp only [CollatzResearch.WordTrace]
  refine ⟨465386315524539297444361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2482060349464209586369925 465386315524539297444361)
  ·
    refine ⟨349039736643404473083271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 465386315524539297444361 349039736643404473083271)
    ·
      refine ⟨523559604965106709624907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 349039736643404473083271 523559604965106709624907)
      ·
        refine ⟨785339407447660064437361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 523559604965106709624907 785339407447660064437361)
        ·
          refine ⟨589004555585745048328021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 785339407447660064437361 589004555585745048328021)
          ·
            refine ⟨3451198567885224892547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 589004555585745048328021 3451198567885224892547)
            ·
              rfl

theorem cell19_102078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 9].length) (baseStart_102078 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_102078 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_102078 prefixEnd_102078 := by exact prefixLift 102078
  have htrace : WordTrace (prefixWord ++ tailWord_102078) baseStart_102078 baseEnd_102078 := by
    simpa [prefixWord, tailWord_102078, baseEnd_102078] using wordTrace_append hprefix tailTrace_102078
  have hstable : (prefixWord ++ tailWord_102078).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102078).length < 2 ^ (prefixWord ++ tailWord_102078).sum := by decide
  have hdescent : baseEnd_102078 < baseStart_102078 := by decide
  rcases family_descends (prefixWord ++ tailWord_102078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102093 : List Nat := [1, 6, 2, 1, 1, 1, 3, 4]
def baseStart_102093 : Nat := 118140960795 + 102093 * 2 ^ 59
def prefixEnd_102093 : Nat := 4983230072969 + 3 ^ 40 * 102093 * 2
def baseEnd_102093 : Nat := 31065351383451433699549

theorem tailTrace_102093 : CollatzResearch.WordTrace tailWord_102093 prefixEnd_102093 31065351383451433699549 := by
  unfold tailWord_102093
  simp only [CollatzResearch.WordTrace]
  refine ⟨3723637619141971941350933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2482425079427981294233955 3723637619141971941350933)
  ·
    refine ⟨174545513397279934750825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 3723637619141971941350933 174545513397279934750825)
    ·
      refine ⟨130909135047959951063119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174545513397279934750825 130909135047959951063119)
      ·
        refine ⟨196363702571939926594679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130909135047959951063119 196363702571939926594679)
        ·
          refine ⟨294545553857909889892019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196363702571939926594679 294545553857909889892019)
          ·
            refine ⟨441818330786864834838029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 294545553857909889892019 441818330786864834838029)
            ·
              refine ⟨165681874045074313064261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 441818330786864834838029 165681874045074313064261)
              ·
                refine ⟨31065351383451433699549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 165681874045074313064261 31065351383451433699549)
                ·
                  rfl

theorem cell19_102093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 3, 4].length) (baseStart_102093 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_102093 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_102093 prefixEnd_102093 := by exact prefixLift 102093
  have htrace : WordTrace (prefixWord ++ tailWord_102093) baseStart_102093 baseEnd_102093 := by
    simpa [prefixWord, tailWord_102093, baseEnd_102093] using wordTrace_append hprefix tailTrace_102093
  have hstable : (prefixWord ++ tailWord_102093).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102093).length < 2 ^ (prefixWord ++ tailWord_102093).sum := by decide
  have hdescent : baseEnd_102093 < baseStart_102093 := by decide
  rcases family_descends (prefixWord ++ tailWord_102093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102097 : List Nat := [1, 2, 2, 1, 2, 4, 3, 4]
def baseStart_102097 : Nat := 118140960795 + 102097 * 2 ^ 59
def prefixEnd_102097 : Nat := 4983230072969 + 3 ^ 40 * 102097 * 2
def baseEnd_102097 : Nat := 31066568522780609610649

theorem tailTrace_102097 : CollatzResearch.WordTrace tailWord_102097 prefixEnd_102097 31066568522780609610649 := by
  unfold tailWord_102097
  simp only [CollatzResearch.WordTrace]
  refine ⟨3723783511127480624496545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2482522340751653749664363 3723783511127480624496545)
  ·
    refine ⟨2792837633345610468372409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3723783511127480624496545 2792837633345610468372409)
    ·
      refine ⟨2094628225009207851279307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2792837633345610468372409 2094628225009207851279307)
      ·
        refine ⟨3141942337513811776918961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2094628225009207851279307 3141942337513811776918961)
        ·
          refine ⟨2356456753135358832689221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3141942337513811776918961 2356456753135358832689221)
          ·
            refine ⟨441835641212879781129229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2356456753135358832689221 441835641212879781129229)
            ·
              refine ⟨165688365454829917923461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 441835641212879781129229 165688365454829917923461)
              ·
                refine ⟨31066568522780609610649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 165688365454829917923461 31066568522780609610649)
                ·
                  rfl

theorem cell19_102097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 3, 4].length) (baseStart_102097 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_102097 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_102097 prefixEnd_102097 := by exact prefixLift 102097
  have htrace : WordTrace (prefixWord ++ tailWord_102097) baseStart_102097 baseEnd_102097 := by
    simpa [prefixWord, tailWord_102097, baseEnd_102097] using wordTrace_append hprefix tailTrace_102097
  have hstable : (prefixWord ++ tailWord_102097).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102097).length < 2 ^ (prefixWord ++ tailWord_102097).sum := by decide
  have hdescent : baseEnd_102097 < baseStart_102097 := by decide
  rcases family_descends (prefixWord ++ tailWord_102097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102211 : List Nat := [1, 1, 1, 3, 1, 6, 2, 4]
def baseStart_102211 : Nat := 118140960795 + 102211 * 2 ^ 59
def prefixEnd_102211 : Nat := 4983230072969 + 3 ^ 40 * 102211 * 2
def baseEnd_102211 : Nat := 31101256993662123077005

theorem tailTrace_102211 : CollatzResearch.WordTrace tailWord_102211 prefixEnd_102211 31101256993662123077005 := by
  unfold tailWord_102211
  simp only [CollatzResearch.WordTrace]
  refine ⟨3727941432714478094146487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2485294288476318729430991 3727941432714478094146487)
  ·
    refine ⟨5591912149071717141219731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3727941432714478094146487 5591912149071717141219731)
    ·
      refine ⟨8387868223607575711829597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5591912149071717141219731 8387868223607575711829597)
      ·
        refine ⟨3145450583852840891936099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8387868223607575711829597 3145450583852840891936099)
        ·
          refine ⟨4718175875779261337904149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3145450583852840891936099 4718175875779261337904149)
          ·
            refine ⟨221164494177152875214257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 4718175875779261337904149 221164494177152875214257)
            ·
              refine ⟨165873370632864656410693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 221164494177152875214257 165873370632864656410693)
              ·
                refine ⟨31101256993662123077005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 165873370632864656410693 31101256993662123077005)
                ·
                  rfl

theorem cell19_102211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 2, 4].length) (baseStart_102211 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_102211 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_102211 prefixEnd_102211 := by exact prefixLift 102211
  have htrace : WordTrace (prefixWord ++ tailWord_102211) baseStart_102211 baseEnd_102211 := by
    simpa [prefixWord, tailWord_102211, baseEnd_102211] using wordTrace_append hprefix tailTrace_102211
  have hstable : (prefixWord ++ tailWord_102211).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102211).length < 2 ^ (prefixWord ++ tailWord_102211).sum := by decide
  have hdescent : baseEnd_102211 < baseStart_102211 := by decide
  rcases family_descends (prefixWord ++ tailWord_102211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102262 : List Nat := [5, 1, 1, 3, 3, 1, 1, 4]
def baseStart_102262 : Nat := 118140960795 + 102262 * 2 ^ 59
def prefixEnd_102262 : Nat := 4983230072969 + 3 ^ 40 * 102262 * 2
def baseEnd_102262 : Nat := 31116775520109115943533

theorem tailTrace_102262 : CollatzResearch.WordTrace tailWord_102262 prefixEnd_102262 31116775520109115943533 := by
  unfold tailWord_102262
  simp only [CollatzResearch.WordTrace]
  refine ⟨233112597220607112765815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2486534370353142536168693 233112597220607112765815)
  ·
    refine ⟨349668895830910669148723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233112597220607112765815 349668895830910669148723)
    ·
      refine ⟨524503343746366003723085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 349668895830910669148723 524503343746366003723085)
      ·
        refine ⟨196688753904887251396157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 524503343746366003723085 196688753904887251396157)
        ·
          refine ⟨73758282714332719273559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 196688753904887251396157 73758282714332719273559)
          ·
            refine ⟨110637424071499078910339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73758282714332719273559 110637424071499078910339)
            ·
              refine ⟨165956136107248618365509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110637424071499078910339 165956136107248618365509)
              ·
                refine ⟨31116775520109115943533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 165956136107248618365509 31116775520109115943533)
                ·
                  rfl

theorem cell19_102262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 1, 4].length) (baseStart_102262 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_102262 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_102262 prefixEnd_102262 := by exact prefixLift 102262
  have htrace : WordTrace (prefixWord ++ tailWord_102262) baseStart_102262 baseEnd_102262 := by
    simpa [prefixWord, tailWord_102262, baseEnd_102262] using wordTrace_append hprefix tailTrace_102262
  have hstable : (prefixWord ++ tailWord_102262).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102262).length < 2 ^ (prefixWord ++ tailWord_102262).sum := by decide
  have hdescent : baseEnd_102262 < baseStart_102262 := by decide
  rcases family_descends (prefixWord ++ tailWord_102262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102289 : List Nat := [1, 2, 2, 1, 1, 1, 4, 7]
def baseStart_102289 : Nat := 118140960795 + 102289 * 2 ^ 59
def prefixEnd_102289 : Nat := 4983230072969 + 3 ^ 40 * 102289 * 2
def baseEnd_102289 : Nat := 31124991210581053343459

theorem tailTrace_102289 : CollatzResearch.WordTrace tailWord_102289 prefixEnd_102289 31124991210581053343459 := by
  unfold tailWord_102289
  simp only [CollatzResearch.WordTrace]
  refine ⟨3730786326431897415485921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2487190884287931610323947 3730786326431897415485921)
  ·
    refine ⟨2798089744823923061614441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3730786326431897415485921 2798089744823923061614441)
    ·
      refine ⟨2098567308617942296210831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2798089744823923061614441 2098567308617942296210831)
      ·
        refine ⟨3147850962926913444316247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2098567308617942296210831 3147850962926913444316247)
        ·
          refine ⟨4721776444390370166474371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3147850962926913444316247 4721776444390370166474371)
          ·
            refine ⟨7082664666585555249711557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4721776444390370166474371 7082664666585555249711557)
            ·
              refine ⟨1327999624984791609320917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7082664666585555249711557 1327999624984791609320917)
              ·
                refine ⟨31124991210581053343459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1327999624984791609320917 31124991210581053343459)
                ·
                  rfl

theorem cell19_102289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 7].length) (baseStart_102289 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_102289 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_102289 prefixEnd_102289 := by exact prefixLift 102289
  have htrace : WordTrace (prefixWord ++ tailWord_102289) baseStart_102289 baseEnd_102289 := by
    simpa [prefixWord, tailWord_102289, baseEnd_102289] using wordTrace_append hprefix tailTrace_102289
  have hstable : (prefixWord ++ tailWord_102289).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102289).length < 2 ^ (prefixWord ++ tailWord_102289).sum := by decide
  have hdescent : baseEnd_102289 < baseStart_102289 := by decide
  rcases family_descends (prefixWord ++ tailWord_102289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102302 : List Nat := [4, 3, 1, 3, 1, 1, 6]
def baseStart_102302 : Nat := 118140960795 + 102302 * 2 ^ 59
def prefixEnd_102302 : Nat := 4983230072969 + 3 ^ 40 * 102302 * 2
def baseEnd_102302 : Nat := 10376315637800291684845

theorem tailTrace_102302 : CollatzResearch.WordTrace tailWord_102302 prefixEnd_102302 10376315637800291684845 := by
  unfold tailWord_102302
  simp only [CollatzResearch.WordTrace]
  refine ⟨466407559423100079463645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2487506983589867090472773 466407559423100079463645)
  ·
    refine ⟨174902834783662529798867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 466407559423100079463645 174902834783662529798867)
    ·
      refine ⟨262354252175493794698301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174902834783662529798867 262354252175493794698301)
      ·
        refine ⟨98382844565810173011863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 262354252175493794698301 98382844565810173011863)
        ·
          refine ⟨147574266848715259517795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98382844565810173011863 147574266848715259517795)
          ·
            refine ⟨221361400273072889276693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147574266848715259517795 221361400273072889276693)
            ·
              refine ⟨10376315637800291684845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 221361400273072889276693 10376315637800291684845)
              ·
                rfl

theorem cell19_102302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 6].length) (baseStart_102302 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_102302 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_102302 prefixEnd_102302 := by exact prefixLift 102302
  have htrace : WordTrace (prefixWord ++ tailWord_102302) baseStart_102302 baseEnd_102302 := by
    simpa [prefixWord, tailWord_102302, baseEnd_102302] using wordTrace_append hprefix tailTrace_102302
  have hstable : (prefixWord ++ tailWord_102302).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102302).length < 2 ^ (prefixWord ++ tailWord_102302).sum := by decide
  have hdescent : baseEnd_102302 < baseStart_102302 := by decide
  rcases family_descends (prefixWord ++ tailWord_102302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102327 : List Nat := [1, 1, 3, 1, 3, 1, 1, 8]
def baseStart_102327 : Nat := 118140960795 + 102327 * 2 ^ 59
def prefixEnd_102327 : Nat := 4983230072969 + 3 ^ 40 * 102327 * 2
def baseEnd_102327 : Nat := 31136554034208224498911

theorem tailTrace_102327 : CollatzResearch.WordTrace tailWord_102327 prefixEnd_102327 31136554034208224498911 := by
  unfold tailWord_102327
  simp only [CollatzResearch.WordTrace]
  refine ⟨3732172300294229905369235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2488114866862819936912823 3732172300294229905369235)
  ·
    refine ⟨5598258450441344858053853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3732172300294229905369235 5598258450441344858053853)
    ·
      refine ⟨2099346918915504321770195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5598258450441344858053853 2099346918915504321770195)
      ·
        refine ⟨3149020378373256482655293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2099346918915504321770195 3149020378373256482655293)
        ·
          refine ⟨1180882641889971180995735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3149020378373256482655293 1180882641889971180995735)
          ·
            refine ⟨1771323962834956771493603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1180882641889971180995735 1771323962834956771493603)
            ·
              refine ⟨2656985944252435157240405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1771323962834956771493603 2656985944252435157240405)
              ·
                refine ⟨31136554034208224498911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2656985944252435157240405 31136554034208224498911)
                ·
                  rfl

theorem cell19_102327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 8].length) (baseStart_102327 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_102327 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_102327 prefixEnd_102327 := by exact prefixLift 102327
  have htrace : WordTrace (prefixWord ++ tailWord_102327) baseStart_102327 baseEnd_102327 := by
    simpa [prefixWord, tailWord_102327, baseEnd_102327] using wordTrace_append hprefix tailTrace_102327
  have hstable : (prefixWord ++ tailWord_102327).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102327).length < 2 ^ (prefixWord ++ tailWord_102327).sum := by decide
  have hdescent : baseEnd_102327 < baseStart_102327 := by decide
  rcases family_descends (prefixWord ++ tailWord_102327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102344 : List Nat := [2, 1, 3, 1, 4, 2, 1, 5]
def baseStart_102344 : Nat := 118140960795 + 102344 * 2 ^ 59
def prefixEnd_102344 : Nat := 4983230072969 + 3 ^ 40 * 102344 * 2
def baseEnd_102344 : Nat := 31141726876357222121087

theorem tailTrace_102344 : CollatzResearch.WordTrace tailWord_102344 prefixEnd_102344 31141726876357222121087 := by
  unfold tailWord_102344
  simp only [CollatzResearch.WordTrace]
  refine ⟨1866396170616320904369043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2488528227488427872492057 1866396170616320904369043)
  ·
    refine ⟨2799594255924481356553565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1866396170616320904369043 2799594255924481356553565)
    ·
      refine ⟨1049847845971680508707587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2799594255924481356553565 1049847845971680508707587)
      ·
        refine ⟨1574771768957520763061381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1049847845971680508707587 1574771768957520763061381)
        ·
          refine ⟨295269706679535143074009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1574771768957520763061381 295269706679535143074009)
          ·
            refine ⟨221452280009651357305507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 295269706679535143074009 221452280009651357305507)
            ·
              refine ⟨332178420014477035958261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 221452280009651357305507 332178420014477035958261)
              ·
                refine ⟨31141726876357222121087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 332178420014477035958261 31141726876357222121087)
                ·
                  rfl

theorem cell19_102344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 5].length) (baseStart_102344 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_102344 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_102344 prefixEnd_102344 := by exact prefixLift 102344
  have htrace : WordTrace (prefixWord ++ tailWord_102344) baseStart_102344 baseEnd_102344 := by
    simpa [prefixWord, tailWord_102344, baseEnd_102344] using wordTrace_append hprefix tailTrace_102344
  have hstable : (prefixWord ++ tailWord_102344).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102344).length < 2 ^ (prefixWord ++ tailWord_102344).sum := by decide
  have hdescent : baseEnd_102344 < baseStart_102344 := by decide
  rcases family_descends (prefixWord ++ tailWord_102344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102361 : List Nat := [1, 2, 1, 2, 7, 1, 5]
def baseStart_102361 : Nat := 118140960795 + 102361 * 2 ^ 59
def prefixEnd_102361 : Nat := 4983230072969 + 3 ^ 40 * 102361 * 2
def baseEnd_102361 : Nat := 10382299906168739914421

theorem tailTrace_102361 : CollatzResearch.WordTrace tailWord_102361 prefixEnd_102361 10382299906168739914421 := by
  unfold tailWord_102361
  simp only [CollatzResearch.WordTrace]
  refine ⟨3733412382171053712106937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2488941588114035808071291 3733412382171053712106937)
  ·
    refine ⟨2800059286628290284080203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3733412382171053712106937 2800059286628290284080203)
    ·
      refine ⟨4200088929942435426120305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2800059286628290284080203 4200088929942435426120305)
      ·
        refine ⟨3150066697456826569590229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4200088929942435426120305 3150066697456826569590229)
        ·
          refine ⟨73829688221644372724771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 3150066697456826569590229 73829688221644372724771)
          ·
            refine ⟨110744532332466559087157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73829688221644372724771 110744532332466559087157)
            ·
              refine ⟨10382299906168739914421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 110744532332466559087157 10382299906168739914421)
              ·
                rfl

theorem cell19_102361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 5].length) (baseStart_102361 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_102361 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_102361 prefixEnd_102361 := by exact prefixLift 102361
  have htrace : WordTrace (prefixWord ++ tailWord_102361) baseStart_102361 baseEnd_102361 := by
    simpa [prefixWord, tailWord_102361, baseEnd_102361] using wordTrace_append hprefix tailTrace_102361
  have hstable : (prefixWord ++ tailWord_102361).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102361).length < 2 ^ (prefixWord ++ tailWord_102361).sum := by decide
  have hdescent : baseEnd_102361 < baseStart_102361 := by decide
  rcases family_descends (prefixWord ++ tailWord_102361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102382 : List Nat := [4, 1, 2, 1, 3, 1, 1, 6]
def baseStart_102382 : Nat := 118140960795 + 102382 * 2 ^ 59
def prefixEnd_102382 : Nat := 4983230072969 + 3 ^ 40 * 102382 * 2
def baseEnd_102382 : Nat := 31153289699984393276539

theorem tailTrace_102382 : CollatzResearch.WordTrace tailWord_102382 prefixEnd_102382 31153289699984393276539 := by
  unfold tailWord_102382
  simp only [CollatzResearch.WordTrace]
  refine ⟨466772289386871787327675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2489452210063316199080933 466772289386871787327675)
  ·
    refine ⟨700158434080307680991513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 466772289386871787327675 700158434080307680991513)
    ·
      refine ⟨525118825560230760743635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 700158434080307680991513 525118825560230760743635)
      ·
        refine ⟨787678238340346141115453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 525118825560230760743635 787678238340346141115453)
        ·
          refine ⟨295379339377629802918295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 787678238340346141115453 295379339377629802918295)
          ·
            refine ⟨443069009066444704377443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 295379339377629802918295 443069009066444704377443)
            ·
              refine ⟨664603513599667056566165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 443069009066444704377443 664603513599667056566165)
              ·
                refine ⟨31153289699984393276539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 664603513599667056566165 31153289699984393276539)
                ·
                  rfl

theorem cell19_102382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 6].length) (baseStart_102382 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_102382 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_102382 prefixEnd_102382 := by exact prefixLift 102382
  have htrace : WordTrace (prefixWord ++ tailWord_102382) baseStart_102382 baseEnd_102382 := by
    simpa [prefixWord, tailWord_102382, baseEnd_102382] using wordTrace_append hprefix tailTrace_102382
  have hstable : (prefixWord ++ tailWord_102382).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102382).length < 2 ^ (prefixWord ++ tailWord_102382).sum := by decide
  have hdescent : baseEnd_102382 < baseStart_102382 := by decide
  rcases family_descends (prefixWord ++ tailWord_102382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102384 : List Nat := [2, 1, 1, 1, 3, 2, 3, 6]
def baseStart_102384 : Nat := 118140960795 + 102384 * 2 ^ 59
def prefixEnd_102384 : Nat := 4983230072969 + 3 ^ 40 * 102384 * 2
def baseEnd_102384 : Nat := 31153898269648981232089

theorem tailTrace_102384 : CollatzResearch.WordTrace tailWord_102384 prefixEnd_102384 31153898269648981232089 := by
  unfold tailWord_102384
  simp only [CollatzResearch.WordTrace]
  refine ⟨1867125630543864320097103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2489500840725152426796137 1867125630543864320097103)
  ·
    refine ⟨2800688445815796480145655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1867125630543864320097103 2800688445815796480145655)
    ·
      refine ⟨4201032668723694720218483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2800688445815796480145655 4201032668723694720218483)
      ·
        refine ⟨6301549003085542080327725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4201032668723694720218483 6301549003085542080327725)
        ·
          refine ⟨2363080876157078280122897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6301549003085542080327725 2363080876157078280122897)
          ·
            refine ⟨1772310657117808710092173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2363080876157078280122897 1772310657117808710092173)
            ·
              refine ⟨664616496419178266284565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1772310657117808710092173 664616496419178266284565)
              ·
                refine ⟨31153898269648981232089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 664616496419178266284565 31153898269648981232089)
                ·
                  rfl

theorem cell19_102384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 6].length) (baseStart_102384 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_102384 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_102384 prefixEnd_102384 := by exact prefixLift 102384
  have htrace : WordTrace (prefixWord ++ tailWord_102384) baseStart_102384 baseEnd_102384 := by
    simpa [prefixWord, tailWord_102384, baseEnd_102384] using wordTrace_append hprefix tailTrace_102384
  have hstable : (prefixWord ++ tailWord_102384).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102384).length < 2 ^ (prefixWord ++ tailWord_102384).sum := by decide
  have hdescent : baseEnd_102384 < baseStart_102384 := by decide
  rcases family_descends (prefixWord ++ tailWord_102384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102422 : List Nat := [5, 14]
def baseStart_102422 : Nat := 118140960795 + 102422 * 2 ^ 59
def prefixEnd_102422 : Nat := 4983230072969 + 3 ^ 40 * 102422 * 2
def baseEnd_102422 : Nat := 42750975436592801629

theorem tailTrace_102422 : CollatzResearch.WordTrace tailWord_102422 prefixEnd_102422 42750975436592801629 := by
  unfold tailWord_102422
  simp only [CollatzResearch.WordTrace]
  refine ⟨233477327184378820629845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2490424823300040753385013 233477327184378820629845)
  ·
    refine ⟨42750975436592801629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 14 233477327184378820629845 42750975436592801629)
    ·
      rfl

theorem cell19_102422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 14].length) (baseStart_102422 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_102422 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_102422 prefixEnd_102422 := by exact prefixLift 102422
  have htrace : WordTrace (prefixWord ++ tailWord_102422) baseStart_102422 baseEnd_102422 := by
    simpa [prefixWord, tailWord_102422, baseEnd_102422] using wordTrace_append hprefix tailTrace_102422
  have hstable : (prefixWord ++ tailWord_102422).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102422).length < 2 ^ (prefixWord ++ tailWord_102422).sum := by decide
  have hdescent : baseEnd_102422 < baseStart_102422 := by decide
  rcases family_descends (prefixWord ++ tailWord_102422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102456 : List Nat := [2, 1, 2, 1, 6, 1, 3, 3]
def baseStart_102456 : Nat := 118140960795 + 102456 * 2 ^ 59
def prefixEnd_102456 : Nat := 4983230072969 + 3 ^ 40 * 102456 * 2
def baseEnd_102456 : Nat := 31175806777574147631893

theorem tailTrace_102456 : CollatzResearch.WordTrace tailWord_102456 prefixEnd_102456 31175806777574147631893 := by
  unfold tailWord_102456
  simp only [CollatzResearch.WordTrace]
  refine ⟨1868438658413442468407611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2491251544551256624543481 1868438658413442468407611)
  ·
    refine ⟨2802657987620163702611417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1868438658413442468407611 2802657987620163702611417)
    ·
      refine ⟨2101993490715122776958563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2802657987620163702611417 2101993490715122776958563)
      ·
        refine ⟨3152990236072684165437845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2101993490715122776958563 3152990236072684165437845)
        ·
          refine ⟨147796417315907070254899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 3152990236072684165437845 147796417315907070254899)
          ·
            refine ⟨221694625973860605382349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147796417315907070254899 221694625973860605382349)
            ·
              refine ⟨83135484740197727018381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 221694625973860605382349 83135484740197727018381)
              ·
                refine ⟨31175806777574147631893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83135484740197727018381 31175806777574147631893)
                ·
                  rfl

theorem cell19_102456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 3, 3].length) (baseStart_102456 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_102456 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_102456 prefixEnd_102456 := by exact prefixLift 102456
  have htrace : WordTrace (prefixWord ++ tailWord_102456) baseStart_102456 baseEnd_102456 := by
    simpa [prefixWord, tailWord_102456, baseEnd_102456] using wordTrace_append hprefix tailTrace_102456
  have hstable : (prefixWord ++ tailWord_102456).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102456).length < 2 ^ (prefixWord ++ tailWord_102456).sum := by decide
  have hdescent : baseEnd_102456 < baseStart_102456 := by decide
  rcases family_descends (prefixWord ++ tailWord_102456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102477 : List Nat := [1, 6, 1, 1, 1, 1, 8]
def baseStart_102477 : Nat := 118140960795 + 102477 * 2 ^ 59
def prefixEnd_102477 : Nat := 4983230072969 + 3 ^ 40 * 102477 * 2
def baseEnd_102477 : Nat := 10394065586350773721723

theorem tailTrace_102477 : CollatzResearch.WordTrace tailWord_102477 prefixEnd_102477 10394065586350773721723 := by
  unfold tailWord_102477
  simp only [CollatzResearch.WordTrace]
  refine ⟨3737643249750805523329685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2491762166500537015553123 3737643249750805523329685)
  ·
    refine ⟨175202027332069008906079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 3737643249750805523329685 175202027332069008906079)
    ·
      refine ⟨262803040998103513359119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175202027332069008906079 262803040998103513359119)
      ·
        refine ⟨394204561497155270038679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262803040998103513359119 394204561497155270038679)
        ·
          refine ⟨591306842245732905058019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 394204561497155270038679 591306842245732905058019)
          ·
            refine ⟨886960263368599357587029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 591306842245732905058019 886960263368599357587029)
            ·
              refine ⟨10394065586350773721723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 886960263368599357587029 10394065586350773721723)
              ·
                rfl

theorem cell19_102477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 8].length) (baseStart_102477 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_102477 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_102477 prefixEnd_102477 := by exact prefixLift 102477
  have htrace : WordTrace (prefixWord ++ tailWord_102477) baseStart_102477 baseEnd_102477 := by
    simpa [prefixWord, tailWord_102477, baseEnd_102477] using wordTrace_append hprefix tailTrace_102477
  have hstable : (prefixWord ++ tailWord_102477).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102477).length < 2 ^ (prefixWord ++ tailWord_102477).sum := by decide
  have hdescent : baseEnd_102477 < baseStart_102477 := by decide
  rcases family_descends (prefixWord ++ tailWord_102477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102610 : List Nat := [3, 2, 2, 2, 1, 2, 3, 4]
def baseStart_102610 : Nat := 118140960795 + 102610 * 2 ^ 59
def prefixEnd_102610 : Nat := 4983230072969 + 3 ^ 40 * 102610 * 2
def baseEnd_102610 : Nat := 31222666641747420209251

theorem tailTrace_102610 : CollatzResearch.WordTrace tailWord_102610 prefixEnd_102610 31222666641747420209251 := by
  unfold tailWord_102610
  simp only [CollatzResearch.WordTrace]
  refine ⟨935623539567242309480321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2494996105512646158614189 935623539567242309480321)
  ·
    refine ⟨701717654675431732110241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 935623539567242309480321 701717654675431732110241)
    ·
      refine ⟨526288241006573799082681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 701717654675431732110241 526288241006573799082681)
      ·
        refine ⟨394716180754930349312011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 526288241006573799082681 394716180754930349312011)
        ·
          refine ⟨592074271132395523968017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 394716180754930349312011 592074271132395523968017)
          ·
            refine ⟨444055703349296642976013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 592074271132395523968017 444055703349296642976013)
            ·
              refine ⟨166520888755986241116005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 444055703349296642976013 166520888755986241116005)
              ·
                refine ⟨31222666641747420209251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 166520888755986241116005 31222666641747420209251)
                ·
                  rfl

theorem cell19_102610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3, 4].length) (baseStart_102610 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_102610 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_102610 prefixEnd_102610 := by exact prefixLift 102610
  have htrace : WordTrace (prefixWord ++ tailWord_102610) baseStart_102610 baseEnd_102610 := by
    simpa [prefixWord, tailWord_102610, baseEnd_102610] using wordTrace_append hprefix tailTrace_102610
  have hstable : (prefixWord ++ tailWord_102610).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102610).length < 2 ^ (prefixWord ++ tailWord_102610).sum := by decide
  have hdescent : baseEnd_102610 < baseStart_102610 := by decide
  rcases family_descends (prefixWord ++ tailWord_102610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102650 : List Nat := [3, 1, 1, 1, 1, 6, 6]
def baseStart_102650 : Nat := 118140960795 + 102650 * 2 ^ 59
def prefixEnd_102650 : Nat := 4983230072969 + 3 ^ 40 * 102650 * 2
def baseEnd_102650 : Nat := 10411612678346393106751

theorem tailTrace_102650 : CollatzResearch.WordTrace tailWord_102650 prefixEnd_102650 10411612678346393106751 := by
  unfold tailWord_102650
  simp only [CollatzResearch.WordTrace]
  refine ⟨935988269531014017344351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2495968718749370712918269 935988269531014017344351)
  ·
    refine ⟨1403982404296521026016527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 935988269531014017344351 1403982404296521026016527)
    ·
      refine ⟨2105973606444781539024791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1403982404296521026016527 2105973606444781539024791)
      ·
        refine ⟨3158960409667172308537187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2105973606444781539024791 3158960409667172308537187)
        ·
          refine ⟨4738440614500758462805781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3158960409667172308537187 4738440614500758462805781)
          ·
            refine ⟨222114403804723052944021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 4738440614500758462805781 222114403804723052944021)
            ·
              refine ⟨10411612678346393106751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 222114403804723052944021 10411612678346393106751)
              ·
                rfl

theorem cell19_102650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 6].length) (baseStart_102650 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_102650 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_102650 prefixEnd_102650 := by exact prefixLift 102650
  have htrace : WordTrace (prefixWord ++ tailWord_102650) baseStart_102650 baseEnd_102650 := by
    simpa [prefixWord, tailWord_102650, baseEnd_102650] using wordTrace_append hprefix tailTrace_102650
  have hstable : (prefixWord ++ tailWord_102650).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102650).length < 2 ^ (prefixWord ++ tailWord_102650).sum := by decide
  have hdescent : baseEnd_102650 < baseStart_102650 := by decide
  rcases family_descends (prefixWord ++ tailWord_102650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102682 : List Nat := [3, 1, 1, 3, 5, 1, 2, 3]
def baseStart_102682 : Nat := 118140960795 + 102682 * 2 ^ 59
def prefixEnd_102682 : Nat := 4983230072969 + 3 ^ 40 * 102682 * 2
def baseEnd_102682 : Nat := 31244575149672586609055

theorem tailTrace_102682 : CollatzResearch.WordTrace tailWord_102682 prefixEnd_102682 31244575149672586609055 := by
  unfold tailWord_102682
  simp only [CollatzResearch.WordTrace]
  refine ⟨936280053502031383635575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2496746809338750356361533 936280053502031383635575)
  ·
    refine ⟨1404420080253047075453363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 936280053502031383635575 1404420080253047075453363)
    ·
      refine ⟨2106630120379570613180045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1404420080253047075453363 2106630120379570613180045)
      ·
        refine ⟨789986295142338979942517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2106630120379570613180045 789986295142338979942517)
        ·
          refine ⟨74061215169594279369611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 789986295142338979942517 74061215169594279369611)
          ·
            refine ⟨111091822754391419054417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74061215169594279369611 111091822754391419054417)
            ·
              refine ⟨83318867065793564290813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111091822754391419054417 83318867065793564290813)
              ·
                refine ⟨31244575149672586609055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83318867065793564290813 31244575149672586609055)
                ·
                  rfl

theorem cell19_102682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 2, 3].length) (baseStart_102682 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_102682 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_102682 prefixEnd_102682 := by exact prefixLift 102682
  have htrace : WordTrace (prefixWord ++ tailWord_102682) baseStart_102682 baseEnd_102682 := by
    simpa [prefixWord, tailWord_102682, baseEnd_102682] using wordTrace_append hprefix tailTrace_102682
  have hstable : (prefixWord ++ tailWord_102682).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102682).length < 2 ^ (prefixWord ++ tailWord_102682).sum := by decide
  have hdescent : baseEnd_102682 < baseStart_102682 := by decide
  rcases family_descends (prefixWord ++ tailWord_102682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102701 : List Nat := [1, 5, 3, 1, 3, 1, 5]
def baseStart_102701 : Nat := 118140960795 + 102701 * 2 ^ 59
def prefixEnd_102701 : Nat := 4983230072969 + 3 ^ 40 * 102701 * 2
def baseEnd_102701 : Nat := 10416785520495390728927

theorem tailTrace_102701 : CollatzResearch.WordTrace tailWord_102701 prefixEnd_102701 10416785520495390728927 := by
  unfold tailWord_102701
  simp only [CollatzResearch.WordTrace]
  refine ⟨3745813200939291779483957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2497208800626194519655971 3745813200939291779483957)
  ·
    refine ⟨351169987588058604326621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3745813200939291779483957 351169987588058604326621)
    ·
      refine ⟨131688745345521976622483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 351169987588058604326621 131688745345521976622483)
      ·
        refine ⟨197533118018282964933725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131688745345521976622483 197533118018282964933725)
        ·
          refine ⟨74074919256856111850147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 197533118018282964933725 74074919256856111850147)
          ·
            refine ⟨111112378885284167775221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74074919256856111850147 111112378885284167775221)
            ·
              refine ⟨10416785520495390728927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 111112378885284167775221 10416785520495390728927)
              ·
                rfl

theorem cell19_102701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 5].length) (baseStart_102701 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_102701 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_102701 prefixEnd_102701 := by exact prefixLift 102701
  have htrace : WordTrace (prefixWord ++ tailWord_102701) baseStart_102701 baseEnd_102701 := by
    simpa [prefixWord, tailWord_102701, baseEnd_102701] using wordTrace_append hprefix tailTrace_102701
  have hstable : (prefixWord ++ tailWord_102701).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102701).length < 2 ^ (prefixWord ++ tailWord_102701).sum := by decide
  have hdescent : baseEnd_102701 < baseStart_102701 := by decide
  rcases family_descends (prefixWord ++ tailWord_102701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102705 : List Nat := [1, 2, 2, 3, 4, 2, 5]
def baseStart_102705 : Nat := 118140960795 + 102705 * 2 ^ 59
def prefixEnd_102705 : Nat := 4983230072969 + 3 ^ 40 * 102705 * 2
def baseEnd_102705 : Nat := 10417191233605116032627

theorem tailTrace_102705 : CollatzResearch.WordTrace tailWord_102705 prefixEnd_102705 10417191233605116032627 := by
  unfold tailWord_102705
  simp only [CollatzResearch.WordTrace]
  refine ⟨3745959092924800462629569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2497306061949866975086379 3745959092924800462629569)
  ·
    refine ⟨2809469319693600346972177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3745959092924800462629569 2809469319693600346972177)
    ·
      refine ⟨2107101989770200260229133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2809469319693600346972177 2107101989770200260229133)
      ·
        refine ⟨790163246163825097585925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2107101989770200260229133 790163246163825097585925)
        ·
          refine ⟨148155608655717205797361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 790163246163825097585925 148155608655717205797361)
          ·
            refine ⟨111116706491787904348021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148155608655717205797361 111116706491787904348021)
            ·
              refine ⟨10417191233605116032627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 111116706491787904348021 10417191233605116032627)
              ·
                rfl

theorem cell19_102705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 5].length) (baseStart_102705 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_102705 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_102705 prefixEnd_102705 := by exact prefixLift 102705
  have htrace : WordTrace (prefixWord ++ tailWord_102705) baseStart_102705 baseEnd_102705 := by
    simpa [prefixWord, tailWord_102705, baseEnd_102705] using wordTrace_append hprefix tailTrace_102705
  have hstable : (prefixWord ++ tailWord_102705).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102705).length < 2 ^ (prefixWord ++ tailWord_102705).sum := by decide
  have hdescent : baseEnd_102705 < baseStart_102705 := by decide
  rcases family_descends (prefixWord ++ tailWord_102705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102764 : List Nat := [2, 2, 1, 1, 6, 7]
def baseStart_102764 : Nat := 118140960795 + 102764 * 2 ^ 59
def prefixEnd_102764 : Nat := 4983230072969 + 3 ^ 40 * 102764 * 2
def baseEnd_102764 : Nat := 3474391833991188087401

theorem tailTrace_102764 : CollatzResearch.WordTrace tailWord_102764 prefixEnd_102764 3474391833991188087401 := by
  unfold tailWord_102764
  simp only [CollatzResearch.WordTrace]
  refine ⟨1874055499855526769513673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2498740666474035692684897 1874055499855526769513673)
  ·
    refine ⟨1405541624891645077135255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1874055499855526769513673 1405541624891645077135255)
    ·
      refine ⟨2108312437337467615702883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1405541624891645077135255 2108312437337467615702883)
      ·
        refine ⟨3162468656006201423554325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2108312437337467615702883 3162468656006201423554325)
        ·
          refine ⟨148240718250290691729109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 3162468656006201423554325 148240718250290691729109)
          ·
            refine ⟨3474391833991188087401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 148240718250290691729109 3474391833991188087401)
            ·
              rfl

theorem cell19_102764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 7].length) (baseStart_102764 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_102764 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_102764 prefixEnd_102764 := by exact prefixLift 102764
  have htrace : WordTrace (prefixWord ++ tailWord_102764) baseStart_102764 baseEnd_102764 := by
    simpa [prefixWord, tailWord_102764, baseEnd_102764] using wordTrace_append hprefix tailTrace_102764
  have hstable : (prefixWord ++ tailWord_102764).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102764).length < 2 ^ (prefixWord ++ tailWord_102764).sum := by decide
  have hdescent : baseEnd_102764 < baseStart_102764 := by decide
  rcases family_descends (prefixWord ++ tailWord_102764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102781 : List Nat := [1, 4, 1, 1, 2, 5, 1, 4]
def baseStart_102781 : Nat := 118140960795 + 102781 * 2 ^ 59
def prefixEnd_102781 : Nat := 4983230072969 + 3 ^ 40 * 102781 * 2
def baseEnd_102781 : Nat := 31274699348069690408785

theorem tailTrace_102781 : CollatzResearch.WordTrace tailWord_102781 prefixEnd_102781 31274699348069690408785 := by
  unfold tailWord_102781
  simp only [CollatzResearch.WordTrace]
  refine ⟨3748731040649465442396197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2499154027099643628264131 3748731040649465442396197)
  ·
    refine ⟨702887070121774770449287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3748731040649465442396197 702887070121774770449287)
    ·
      refine ⟨1054330605182662155673931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 702887070121774770449287 1054330605182662155673931)
      ·
        refine ⟨1581495907773993233510897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1054330605182662155673931 1581495907773993233510897)
        ·
          refine ⟨1186121930830494925133173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1581495907773993233510897 1186121930830494925133173)
          ·
            refine ⟨111198931015358899231235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1186121930830494925133173 111198931015358899231235)
            ·
              refine ⟨166798396523038348846853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111198931015358899231235 166798396523038348846853)
              ·
                refine ⟨31274699348069690408785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 166798396523038348846853 31274699348069690408785)
                ·
                  rfl

theorem cell19_102781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 1, 4].length) (baseStart_102781 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_102781 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_102781 prefixEnd_102781 := by exact prefixLift 102781
  have htrace : WordTrace (prefixWord ++ tailWord_102781) baseStart_102781 baseEnd_102781 := by
    simpa [prefixWord, tailWord_102781, baseEnd_102781] using wordTrace_append hprefix tailTrace_102781
  have hstable : (prefixWord ++ tailWord_102781).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102781).length < 2 ^ (prefixWord ++ tailWord_102781).sum := by decide
  have hdescent : baseEnd_102781 < baseStart_102781 := by decide
  rcases family_descends (prefixWord ++ tailWord_102781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102798 : List Nat := [4, 1, 1, 4, 1, 2, 3, 3]
def baseStart_102798 : Nat := 118140960795 + 102798 * 2 ^ 59
def prefixEnd_102798 : Nat := 4983230072969 + 3 ^ 40 * 102798 * 2
def baseEnd_102798 : Nat := 31279872190218688030961

theorem tailTrace_102798 : CollatzResearch.WordTrace tailWord_102798 prefixEnd_102798 31279872190218688030961 := by
  unfold tailWord_102798
  simp only [CollatzResearch.WordTrace]
  refine ⟨468668885198484668220631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2499567387725251563843365 468668885198484668220631)
  ·
    refine ⟨703003327797727002330947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 468668885198484668220631 703003327797727002330947)
    ·
      refine ⟨1054504991696590503496421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 703003327797727002330947 1054504991696590503496421)
      ·
        refine ⟨197719685943110719405579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1054504991696590503496421 197719685943110719405579)
        ·
          refine ⟨296579528914666079108369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197719685943110719405579 296579528914666079108369)
          ·
            refine ⟨222434646685999559331277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 296579528914666079108369 222434646685999559331277)
            ·
              refine ⟨83412992507249834749229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 222434646685999559331277 83412992507249834749229)
              ·
                refine ⟨31279872190218688030961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83412992507249834749229 31279872190218688030961)
                ·
                  rfl

theorem cell19_102798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 3, 3].length) (baseStart_102798 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_102798 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_102798 prefixEnd_102798 := by exact prefixLift 102798
  have htrace : WordTrace (prefixWord ++ tailWord_102798) baseStart_102798 baseEnd_102798 := by
    simpa [prefixWord, tailWord_102798, baseEnd_102798] using wordTrace_append hprefix tailTrace_102798
  have hstable : (prefixWord ++ tailWord_102798).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102798).length < 2 ^ (prefixWord ++ tailWord_102798).sum := by decide
  have hdescent : baseEnd_102798 < baseStart_102798 := by decide
  rcases family_descends (prefixWord ++ tailWord_102798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102849 : List Nat := [1, 2, 7, 1, 2, 1, 2, 3]
def baseStart_102849 : Nat := 118140960795 + 102849 * 2 ^ 59
def prefixEnd_102849 : Nat := 4983230072969 + 3 ^ 40 * 102849 * 2
def baseEnd_102849 : Nat := 31295390716665680897489

theorem tailTrace_102849 : CollatzResearch.WordTrace tailWord_102849 prefixEnd_102849 31295390716665680897489 := by
  unfold tailWord_102849
  simp only [CollatzResearch.WordTrace]
  refine ⟨3751211204403113055871601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2500807469602075370581067 3751211204403113055871601)
  ·
    refine ⟨2813408403302334791903701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3751211204403113055871601 2813408403302334791903701)
    ·
      refine ⟨65939259452398471685243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 2813408403302334791903701 65939259452398471685243)
      ·
        refine ⟨98908889178597707527865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65939259452398471685243 98908889178597707527865)
        ·
          refine ⟨74181666883948280645899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98908889178597707527865 74181666883948280645899)
          ·
            refine ⟨111272500325922420968849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74181666883948280645899 111272500325922420968849)
            ·
              refine ⟨83454375244441815726637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111272500325922420968849 83454375244441815726637)
              ·
                refine ⟨31295390716665680897489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83454375244441815726637 31295390716665680897489)
                ·
                  rfl

theorem cell19_102849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 2, 3].length) (baseStart_102849 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_102849 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_102849 prefixEnd_102849 := by exact prefixLift 102849
  have htrace : WordTrace (prefixWord ++ tailWord_102849) baseStart_102849 baseEnd_102849 := by
    simpa [prefixWord, tailWord_102849, baseEnd_102849] using wordTrace_append hprefix tailTrace_102849
  have hstable : (prefixWord ++ tailWord_102849).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102849).length < 2 ^ (prefixWord ++ tailWord_102849).sum := by decide
  have hdescent : baseEnd_102849 < baseStart_102849 := by decide
  rcases family_descends (prefixWord ++ tailWord_102849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102897 : List Nat := [1, 2, 2, 2, 3, 1, 4, 4]
def baseStart_102897 : Nat := 118140960795 + 102897 * 2 ^ 59
def prefixEnd_102897 : Nat := 4983230072969 + 3 ^ 40 * 102897 * 2
def baseEnd_102897 : Nat := 31309996388615791830691

theorem tailTrace_102897 : CollatzResearch.WordTrace tailWord_102897 prefixEnd_102897 31309996388615791830691 := by
  unfold tailWord_102897
  simp only [CollatzResearch.WordTrace]
  refine ⟨3752961908229217253618945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2501974605486144835745963 3752961908229217253618945)
  ·
    refine ⟨2814721431171912940214209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3752961908229217253618945 2814721431171912940214209)
    ·
      refine ⟨2111041073378934705160657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2814721431171912940214209 2111041073378934705160657)
      ·
        refine ⟨1583280805034201028870493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2111041073378934705160657 1583280805034201028870493)
        ·
          refine ⟨593730301887825385826435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1583280805034201028870493 593730301887825385826435)
          ·
            refine ⟨890595452831738078739653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 593730301887825385826435 890595452831738078739653)
            ·
              refine ⟨166986647405950889763685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 890595452831738078739653 166986647405950889763685)
              ·
                refine ⟨31309996388615791830691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 166986647405950889763685 31309996388615791830691)
                ·
                  rfl

theorem cell19_102897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 4, 4].length) (baseStart_102897 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_102897 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_102897 prefixEnd_102897 := by exact prefixLift 102897
  have htrace : WordTrace (prefixWord ++ tailWord_102897) baseStart_102897 baseEnd_102897 := by
    simpa [prefixWord, tailWord_102897, baseEnd_102897] using wordTrace_append hprefix tailTrace_102897
  have hstable : (prefixWord ++ tailWord_102897).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102897).length < 2 ^ (prefixWord ++ tailWord_102897).sum := by decide
  have hdescent : baseEnd_102897 < baseStart_102897 := by decide
  rcases family_descends (prefixWord ++ tailWord_102897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102935 : List Nat := [1, 1, 3, 6, 8]
def baseStart_102935 : Nat := 118140960795 + 102935 * 2 ^ 59
def prefixEnd_102935 : Nat := 4983230072969 + 3 ^ 40 * 102935 * 2
def baseEnd_102935 : Nat := 1160057748601591221709

theorem tailTrace_102935 : CollatzResearch.WordTrace tailWord_102935 prefixEnd_102935 1160057748601591221709 := by
  unfold tailWord_102935
  simp only [CollatzResearch.WordTrace]
  refine ⟨3754347882091549743502259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2502898588061033162334839 3754347882091549743502259)
  ·
    refine ⟨5631521823137324615253389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3754347882091549743502259 5631521823137324615253389)
    ·
      refine ⟨2111820683676496730720021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5631521823137324615253389 2111820683676496730720021)
      ·
        refine ⟨98991594547335784252501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 2111820683676496730720021 98991594547335784252501)
        ·
          refine ⟨1160057748601591221709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 98991594547335784252501 1160057748601591221709)
          ·
            rfl

theorem cell19_102935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 8].length) (baseStart_102935 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_102935 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_102935 prefixEnd_102935 := by exact prefixLift 102935
  have htrace : WordTrace (prefixWord ++ tailWord_102935) baseStart_102935 baseEnd_102935 := by
    simpa [prefixWord, tailWord_102935, baseEnd_102935] using wordTrace_append hprefix tailTrace_102935
  have hstable : (prefixWord ++ tailWord_102935).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102935).length < 2 ^ (prefixWord ++ tailWord_102935).sum := by decide
  have hdescent : baseEnd_102935 < baseStart_102935 := by decide
  rcases family_descends (prefixWord ++ tailWord_102935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102948 : List Nat := [2, 3, 1, 5, 2, 1, 1, 4]
def baseStart_102948 : Nat := 118140960795 + 102948 * 2 ^ 59
def prefixEnd_102948 : Nat := 4983230072969 + 3 ^ 40 * 102948 * 2
def baseEnd_102948 : Nat := 31325514915062784697219

theorem tailTrace_102948 : CollatzResearch.WordTrace tailWord_102948 prefixEnd_102948 31325514915062784697219 := by
  unfold tailWord_102948
  simp only [CollatzResearch.WordTrace]
  refine ⟨1877411015522226481862749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2503214687362968642483665 1877411015522226481862749)
  ·
    refine ⟨704029130820834930698531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1877411015522226481862749 704029130820834930698531)
    ·
      refine ⟨1056043696231252396047797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 704029130820834930698531 1056043696231252396047797)
      ·
        refine ⟨99004096521679912129481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1056043696231252396047797 99004096521679912129481)
        ·
          refine ⟨74253072391259934097111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99004096521679912129481 74253072391259934097111)
          ·
            refine ⟨111379608586889901145667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74253072391259934097111 111379608586889901145667)
            ·
              refine ⟨167069412880334851718501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111379608586889901145667 167069412880334851718501)
              ·
                refine ⟨31325514915062784697219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 167069412880334851718501 31325514915062784697219)
                ·
                  rfl

theorem cell19_102948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 1, 4].length) (baseStart_102948 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_102948 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_102948 prefixEnd_102948 := by exact prefixLift 102948
  have htrace : WordTrace (prefixWord ++ tailWord_102948) baseStart_102948 baseEnd_102948 := by
    simpa [prefixWord, tailWord_102948, baseEnd_102948] using wordTrace_append hprefix tailTrace_102948
  have hstable : (prefixWord ++ tailWord_102948).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102948).length < 2 ^ (prefixWord ++ tailWord_102948).sum := by decide
  have hdescent : baseEnd_102948 < baseStart_102948 := by decide
  rcases family_descends (prefixWord ++ tailWord_102948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102952 : List Nat := [2, 1, 5, 2, 1, 1, 3, 4]
def baseStart_102952 : Nat := 118140960795 + 102952 * 2 ^ 59
def prefixEnd_102952 : Nat := 4983230072969 + 3 ^ 40 * 102952 * 2
def baseEnd_102952 : Nat := 31326732054391960608319

theorem tailTrace_102952 : CollatzResearch.WordTrace tailWord_102952 prefixEnd_102952 31326732054391960608319 := by
  unfold tailWord_102952
  simp only [CollatzResearch.WordTrace]
  refine ⟨1877483961514980823435555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2503311948686641097914073 1877483961514980823435555)
  ·
    refine ⟨2816225942272471235153333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1877483961514980823435555 2816225942272471235153333)
    ·
      refine ⟨264021182088044178295625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2816225942272471235153333 264021182088044178295625)
      ·
        refine ⟨198015886566033133721719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264021182088044178295625 198015886566033133721719)
        ·
          refine ⟨297023829849049700582579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198015886566033133721719 297023829849049700582579)
          ·
            refine ⟨445535744773574550873869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 297023829849049700582579 445535744773574550873869)
            ·
              refine ⟨167075904290090456577701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 445535744773574550873869 167075904290090456577701)
              ·
                refine ⟨31326732054391960608319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 167075904290090456577701 31326732054391960608319)
                ·
                  rfl

theorem cell19_102952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 3, 4].length) (baseStart_102952 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_102952 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_102952 prefixEnd_102952 := by exact prefixLift 102952
  have htrace : WordTrace (prefixWord ++ tailWord_102952) baseStart_102952 baseEnd_102952 := by
    simpa [prefixWord, tailWord_102952, baseEnd_102952] using wordTrace_append hprefix tailTrace_102952
  have hstable : (prefixWord ++ tailWord_102952).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102952).length < 2 ^ (prefixWord ++ tailWord_102952).sum := by decide
  have hdescent : baseEnd_102952 < baseStart_102952 := by decide
  rcases family_descends (prefixWord ++ tailWord_102952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103026 : List Nat := [3, 2, 1, 2, 4, 2, 2, 3]
def baseStart_103026 : Nat := 118140960795 + 103026 * 2 ^ 59
def prefixEnd_103026 : Nat := 4983230072969 + 3 ^ 40 * 103026 * 2
def baseEnd_103026 : Nat := 31349249131981714963673

theorem tailTrace_103026 : CollatzResearch.WordTrace tailWord_103026 prefixEnd_103026 31349249131981714963673 := by
  unfold tailWord_103026
  simp only [CollatzResearch.WordTrace]
  refine ⟨939416731190468071266233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2505111283174581523376621 939416731190468071266233)
  ·
    refine ⟨704562548392851053449675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 939416731190468071266233 704562548392851053449675)
    ·
      refine ⟨1056843822589276580174513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 704562548392851053449675 1056843822589276580174513)
      ·
        refine ⟨792632866941957435130885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1056843822589276580174513 792632866941957435130885)
        ·
          refine ⟨148618662551617019087041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 792632866941957435130885 148618662551617019087041)
          ·
            refine ⟨111463996913712764315281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148618662551617019087041 111463996913712764315281)
            ·
              refine ⟨83597997685284573236461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111463996913712764315281 83597997685284573236461)
              ·
                refine ⟨31349249131981714963673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83597997685284573236461 31349249131981714963673)
                ·
                  rfl

theorem cell19_103026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 2, 3].length) (baseStart_103026 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_103026 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_103026 prefixEnd_103026 := by exact prefixLift 103026
  have htrace : WordTrace (prefixWord ++ tailWord_103026) baseStart_103026 baseEnd_103026 := by
    simpa [prefixWord, tailWord_103026, baseEnd_103026] using wordTrace_append hprefix tailTrace_103026
  have hstable : (prefixWord ++ tailWord_103026).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103026).length < 2 ^ (prefixWord ++ tailWord_103026).sum := by decide
  have hdescent : baseEnd_103026 < baseStart_103026 := by decide
  rcases family_descends (prefixWord ++ tailWord_103026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103032 : List Nat := [2, 1, 2, 1, 1, 1, 2, 9]
def baseStart_103032 : Nat := 118140960795 + 103032 * 2 ^ 59
def prefixEnd_103032 : Nat := 4983230072969 + 3 ^ 40 * 103032 * 2
def baseEnd_103032 : Nat := 31351074840975478830323

theorem tailTrace_103032 : CollatzResearch.WordTrace tailWord_103032 prefixEnd_103032 31351074840975478830323 := by
  unfold tailWord_103032
  simp only [CollatzResearch.WordTrace]
  refine ⟨1878942881370067654891675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2505257175160090206522233 1878942881370067654891675)
  ·
    refine ⟨2818414322055101482337513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1878942881370067654891675 2818414322055101482337513)
    ·
      refine ⟨2113810741541326111753135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2818414322055101482337513 2113810741541326111753135)
      ·
        refine ⟨3170716112311989167629703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2113810741541326111753135 3170716112311989167629703)
        ·
          refine ⟨4756074168467983751444555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3170716112311989167629703 4756074168467983751444555)
          ·
            refine ⟨7134111252701975627166833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4756074168467983751444555 7134111252701975627166833)
            ·
              refine ⟨5350583439526481720375125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7134111252701975627166833 5350583439526481720375125)
              ·
                refine ⟨31351074840975478830323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5350583439526481720375125 31351074840975478830323)
                ·
                  rfl

theorem cell19_103032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 9].length) (baseStart_103032 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_103032 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_103032 prefixEnd_103032 := by exact prefixLift 103032
  have htrace : WordTrace (prefixWord ++ tailWord_103032) baseStart_103032 baseEnd_103032 := by
    simpa [prefixWord, tailWord_103032, baseEnd_103032] using wordTrace_append hprefix tailTrace_103032
  have hstable : (prefixWord ++ tailWord_103032).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103032).length < 2 ^ (prefixWord ++ tailWord_103032).sum := by decide
  have hdescent : baseEnd_103032 < baseStart_103032 := by decide
  rcases family_descends (prefixWord ++ tailWord_103032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103068 : List Nat := [2, 2, 3, 2, 2, 1, 1, 6]
def baseStart_103068 : Nat := 118140960795 + 103068 * 2 ^ 59
def prefixEnd_103068 : Nat := 4983230072969 + 3 ^ 40 * 103068 * 2
def baseEnd_103068 : Nat := 31362029094938062030225

theorem tailTrace_103068 : CollatzResearch.WordTrace tailWord_103068 prefixEnd_103068 31362029094938062030225 := by
  unfold tailWord_103068
  simp only [CollatzResearch.WordTrace]
  refine ⟨1879599395304856729046929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2506132527073142305395905 1879599395304856729046929)
  ·
    refine ⟨1409699546478642546785197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1879599395304856729046929 1409699546478642546785197)
    ·
      refine ⟨528637329929490955044449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1409699546478642546785197 528637329929490955044449)
      ·
        refine ⟨396477997447118216283337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 528637329929490955044449 396477997447118216283337)
        ·
          refine ⟨297358498085338662212503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 396477997447118216283337 297358498085338662212503)
          ·
            refine ⟨446037747128007993318755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 297358498085338662212503 446037747128007993318755)
            ·
              refine ⟨669056620692011989978133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 446037747128007993318755 669056620692011989978133)
              ·
                refine ⟨31362029094938062030225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 669056620692011989978133 31362029094938062030225)
                ·
                  rfl

theorem cell19_103068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 6].length) (baseStart_103068 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_103068 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_103068 prefixEnd_103068 := by exact prefixLift 103068
  have htrace : WordTrace (prefixWord ++ tailWord_103068) baseStart_103068 baseEnd_103068 := by
    simpa [prefixWord, tailWord_103068, baseEnd_103068] using wordTrace_append hprefix tailTrace_103068
  have hstable : (prefixWord ++ tailWord_103068).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103068).length < 2 ^ (prefixWord ++ tailWord_103068).sum := by decide
  have hdescent : baseEnd_103068 < baseStart_103068 := by decide
  rcases family_descends (prefixWord ++ tailWord_103068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103165 : List Nat := [1, 4, 1, 1, 1, 1, 10]
def baseStart_103165 : Nat := 118140960795 + 103165 * 2 ^ 59
def prefixEnd_103165 : Nat := 4983230072969 + 3 ^ 40 * 103165 * 2
def baseEnd_103165 : Nat := 10463848241223525958135

theorem tailTrace_103165 : CollatzResearch.WordTrace tailWord_103165 prefixEnd_103165 10463848241223525958135 := by
  unfold tailWord_103165
  simp only [CollatzResearch.WordTrace]
  refine ⟨3762736671258299024374949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2508491114172199349583299 3762736671258299024374949)
  ·
    refine ⟨705513125860931067070303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3762736671258299024374949 705513125860931067070303)
    ·
      refine ⟨1058269688791396600605455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 705513125860931067070303 1058269688791396600605455)
      ·
        refine ⟨1587404533187094900908183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1058269688791396600605455 1587404533187094900908183)
        ·
          refine ⟨2381106799780642351362275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1587404533187094900908183 2381106799780642351362275)
          ·
            refine ⟨3571660199670963527043413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2381106799780642351362275 3571660199670963527043413)
            ·
              refine ⟨10463848241223525958135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 3571660199670963527043413 10463848241223525958135)
              ·
                rfl

theorem cell19_103165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 10].length) (baseStart_103165 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_103165 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_103165 prefixEnd_103165 := by exact prefixLift 103165
  have htrace : WordTrace (prefixWord ++ tailWord_103165) baseStart_103165 baseEnd_103165 := by
    simpa [prefixWord, tailWord_103165, baseEnd_103165] using wordTrace_append hprefix tailTrace_103165
  have hstable : (prefixWord ++ tailWord_103165).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103165).length < 2 ^ (prefixWord ++ tailWord_103165).sum := by decide
  have hdescent : baseEnd_103165 < baseStart_103165 := by decide
  rcases family_descends (prefixWord ++ tailWord_103165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103199 : List Nat := [1, 1, 2, 4, 2, 4, 2, 3]
def baseStart_103199 : Nat := 118140960795 + 103199 * 2 ^ 59
def prefixEnd_103199 : Nat := 4983230072969 + 3 ^ 40 * 103199 * 2
def baseEnd_103199 : Nat := 31401890407968573118757

theorem tailTrace_103199 : CollatzResearch.WordTrace tailWord_103199 prefixEnd_103199 31401890407968573118757 := by
  unfold tailWord_103199
  simp only [CollatzResearch.WordTrace]
  refine ⟨3763976753135122831112651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2509317835423415220741767 3763976753135122831112651)
  ·
    refine ⟨5645965129702684246668977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3763976753135122831112651 5645965129702684246668977)
    ·
      refine ⟨4234473847277013185001733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5645965129702684246668977 4234473847277013185001733)
      ·
        refine ⟨793963846364439972187825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4234473847277013185001733 793963846364439972187825)
        ·
          refine ⟨595472884773329979140869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 793963846364439972187825 595472884773329979140869)
          ·
            refine ⟨111651165894999371088913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 595472884773329979140869 111651165894999371088913)
            ·
              refine ⟨83738374421249528316685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111651165894999371088913 83738374421249528316685)
              ·
                refine ⟨31401890407968573118757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83738374421249528316685 31401890407968573118757)
                ·
                  rfl

theorem cell19_103199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 2, 3].length) (baseStart_103199 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_103199 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_103199 prefixEnd_103199 := by exact prefixLift 103199
  have htrace : WordTrace (prefixWord ++ tailWord_103199) baseStart_103199 baseEnd_103199 := by
    simpa [prefixWord, tailWord_103199, baseEnd_103199] using wordTrace_append hprefix tailTrace_103199
  have hstable : (prefixWord ++ tailWord_103199).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103199).length < 2 ^ (prefixWord ++ tailWord_103199).sum := by decide
  have hdescent : baseEnd_103199 < baseStart_103199 := by decide
  rcases family_descends (prefixWord ++ tailWord_103199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103241 : List Nat := [1, 2, 1, 1, 2, 5, 1, 6]
def baseStart_103241 : Nat := 118140960795 + 103241 * 2 ^ 59
def prefixEnd_103241 : Nat := 4983230072969 + 3 ^ 40 * 103241 * 2
def baseEnd_103241 : Nat := 31414670370924920185309

theorem tailTrace_103241 : CollatzResearch.WordTrace tailWord_103241 prefixEnd_103241 31414670370924920185309 := by
  unfold tailWord_103241
  simp only [CollatzResearch.WordTrace]
  refine ⟨3765508618982964004141577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2510339079321976002761051 3765508618982964004141577)
  ·
    refine ⟨2824131464237223003106183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3765508618982964004141577 2824131464237223003106183)
    ·
      refine ⟨4236197196355834504659275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2824131464237223003106183 4236197196355834504659275)
      ·
        refine ⟨6354295794533751756988913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4236197196355834504659275 6354295794533751756988913)
        ·
          refine ⟨4765721845900313817741685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6354295794533751756988913 4765721845900313817741685)
          ·
            refine ⟨446786423053154420413283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4765721845900313817741685 446786423053154420413283)
            ·
              refine ⟨670179634579731630619925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 446786423053154420413283 670179634579731630619925)
              ·
                refine ⟨31414670370924920185309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 670179634579731630619925 31414670370924920185309)
                ·
                  rfl

theorem cell19_103241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 6].length) (baseStart_103241 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_103241 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_103241 prefixEnd_103241 := by exact prefixLift 103241
  have htrace : WordTrace (prefixWord ++ tailWord_103241) baseStart_103241 baseEnd_103241 := by
    simpa [prefixWord, tailWord_103241, baseEnd_103241] using wordTrace_append hprefix tailTrace_103241
  have hstable : (prefixWord ++ tailWord_103241).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103241).length < 2 ^ (prefixWord ++ tailWord_103241).sum := by decide
  have hdescent : baseEnd_103241 < baseStart_103241 := by decide
  rcases family_descends (prefixWord ++ tailWord_103241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103368 : List Nat := [2, 1, 3, 1, 6, 1, 2, 3]
def baseStart_103368 : Nat := 118140960795 + 103368 * 2 ^ 59
def prefixEnd_103368 : Nat := 4983230072969 + 3 ^ 40 * 103368 * 2
def baseEnd_103368 : Nat := 31453314544626255362741

theorem tailTrace_103368 : CollatzResearch.WordTrace tailWord_103368 prefixEnd_103368 31453314544626255362741 := by
  unfold tailWord_103368
  simp only [CollatzResearch.WordTrace]
  refine ⟨1885070344761432347007379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2513427126348576462676505 1885070344761432347007379)
  ·
    refine ⟨2827605517142148520511069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1885070344761432347007379 2827605517142148520511069)
    ·
      refine ⟨1060352068928305695191651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2827605517142148520511069 1060352068928305695191651)
      ·
        refine ⟨1590528103392458542787477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1060352068928305695191651 1590528103392458542787477)
        ·
          refine ⟨74556004846521494193163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 1590528103392458542787477 74556004846521494193163)
          ·
            refine ⟨111834007269782241289745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74556004846521494193163 111834007269782241289745)
            ·
              refine ⟨83875505452336680967309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111834007269782241289745 83875505452336680967309)
              ·
                refine ⟨31453314544626255362741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83875505452336680967309 31453314544626255362741)
                ·
                  rfl

theorem cell19_103368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 2, 3].length) (baseStart_103368 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_103368 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_103368 prefixEnd_103368 := by exact prefixLift 103368
  have htrace : WordTrace (prefixWord ++ tailWord_103368) baseStart_103368 baseEnd_103368 := by
    simpa [prefixWord, tailWord_103368, baseEnd_103368] using wordTrace_append hprefix tailTrace_103368
  have hstable : (prefixWord ++ tailWord_103368).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103368).length < 2 ^ (prefixWord ++ tailWord_103368).sum := by decide
  have hdescent : baseEnd_103368 < baseStart_103368 := by decide
  rcases family_descends (prefixWord ++ tailWord_103368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103391 : List Nat := [1, 1, 2, 3, 5, 2, 5]
def baseStart_103391 : Nat := 118140960795 + 103391 * 2 ^ 59
def prefixEnd_103391 : Nat := 4983230072969 + 3 ^ 40 * 103391 * 2
def baseEnd_103391 : Nat := 10486771031923005617189

theorem tailTrace_103391 : CollatzResearch.WordTrace tailWord_103391 prefixEnd_103391 10486771031923005617189 := by
  unfold tailWord_103391
  simp only [CollatzResearch.WordTrace]
  refine ⟨3770979568439539622102027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2513986378959693081401351 3770979568439539622102027)
  ·
    refine ⟨5656469352659309433153041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3770979568439539622102027 5656469352659309433153041)
    ·
      refine ⟨4242352014494482074864781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5656469352659309433153041 4242352014494482074864781)
      ·
        refine ⟨1590882005435430778074293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4242352014494482074864781 1590882005435430778074293)
        ·
          refine ⟨149145188009571635444465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1590882005435430778074293 149145188009571635444465)
          ·
            refine ⟨111858891007178726583349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149145188009571635444465 111858891007178726583349)
            ·
              refine ⟨10486771031923005617189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 111858891007178726583349 10486771031923005617189)
              ·
                rfl

theorem cell19_103391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 5].length) (baseStart_103391 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_103391 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_103391 prefixEnd_103391 := by exact prefixLift 103391
  have htrace : WordTrace (prefixWord ++ tailWord_103391) baseStart_103391 baseEnd_103391 := by
    simpa [prefixWord, tailWord_103391, baseEnd_103391] using wordTrace_append hprefix tailTrace_103391
  have hstable : (prefixWord ++ tailWord_103391).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103391).length < 2 ^ (prefixWord ++ tailWord_103391).sum := by decide
  have hdescent : baseEnd_103391 < baseStart_103391 := by decide
  rcases family_descends (prefixWord ++ tailWord_103391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103431 : List Nat := [1, 1, 4, 3, 1, 1, 1, 7]
def baseStart_103431 : Nat := 118140960795 + 103431 * 2 ^ 59
def prefixEnd_103431 : Nat := 4983230072969 + 3 ^ 40 * 103431 * 2
def baseEnd_103431 : Nat := 31472484489060775962569

theorem tailTrace_103431 : CollatzResearch.WordTrace tailWord_103431 prefixEnd_103431 31472484489060775962569 := by
  unfold tailWord_103431
  simp only [CollatzResearch.WordTrace]
  refine ⟨3772438488294626453558147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2514958992196417635705431 3772438488294626453558147)
  ·
    refine ⟨5658657732441939680337221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3772438488294626453558147 5658657732441939680337221)
    ·
      refine ⟨1060998324832863690063229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5658657732441939680337221 1060998324832863690063229)
      ·
        refine ⟨397874371812323883773711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1060998324832863690063229 397874371812323883773711)
        ·
          refine ⟨596811557718485825660567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 397874371812323883773711 596811557718485825660567)
          ·
            refine ⟨895217336577728738490851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 596811557718485825660567 895217336577728738490851)
            ·
              refine ⟨1342826004866593107736277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 895217336577728738490851 1342826004866593107736277)
              ·
                refine ⟨31472484489060775962569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1342826004866593107736277 31472484489060775962569)
                ·
                  rfl

theorem cell19_103431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 7].length) (baseStart_103431 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_103431 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_103431 prefixEnd_103431 := by exact prefixLift 103431
  have htrace : WordTrace (prefixWord ++ tailWord_103431) baseStart_103431 baseEnd_103431 := by
    simpa [prefixWord, tailWord_103431, baseEnd_103431] using wordTrace_append hprefix tailTrace_103431
  have hstable : (prefixWord ++ tailWord_103431).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103431).length < 2 ^ (prefixWord ++ tailWord_103431).sum := by decide
  have hdescent : baseEnd_103431 < baseStart_103431 := by decide
  rcases family_descends (prefixWord ++ tailWord_103431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103541 : List Nat := [1, 3, 4, 3, 1, 1, 1, 5]
def baseStart_103541 : Nat := 118140960795 + 103541 * 2 ^ 59
def prefixEnd_103541 : Nat := 4983230072969 + 3 ^ 40 * 103541 * 2
def baseEnd_103541 : Nat := 31505955820613113517825

theorem tailTrace_103541 : CollatzResearch.WordTrace tailWord_103541 prefixEnd_103541 31505955820613113517825 := by
  unfold tailWord_103541
  simp only [CollatzResearch.WordTrace]
  refine ⟨3776450517896115240062477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2517633678597410160041651 3776450517896115240062477)
  ·
    refine ⟨1416168944211043215023429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3776450517896115240062477 1416168944211043215023429)
    ·
      refine ⟨265531677039570602816893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1416168944211043215023429 265531677039570602816893)
      ·
        refine ⟨99574378889838976056335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 265531677039570602816893 99574378889838976056335)
        ·
          refine ⟨149361568334758464084503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99574378889838976056335 149361568334758464084503)
          ·
            refine ⟨224042352502137696126755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149361568334758464084503 224042352502137696126755)
            ·
              refine ⟨336063528753206544190133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 224042352502137696126755 336063528753206544190133)
              ·
                refine ⟨31505955820613113517825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 336063528753206544190133 31505955820613113517825)
                ·
                  rfl

theorem cell19_103541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 5].length) (baseStart_103541 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_103541 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_103541 prefixEnd_103541 := by exact prefixLift 103541
  have htrace : WordTrace (prefixWord ++ tailWord_103541) baseStart_103541 baseEnd_103541 := by
    simpa [prefixWord, tailWord_103541, baseEnd_103541] using wordTrace_append hprefix tailTrace_103541
  have hstable : (prefixWord ++ tailWord_103541).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103541).length < 2 ^ (prefixWord ++ tailWord_103541).sum := by decide
  have hdescent : baseEnd_103541 < baseStart_103541 := by decide
  rcases family_descends (prefixWord ++ tailWord_103541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103560 : List Nat := [2, 1, 3, 4, 3, 1, 5]
def baseStart_103560 : Nat := 118140960795 + 103560 * 2 ^ 59
def prefixEnd_103560 : Nat := 4983230072969 + 3 ^ 40 * 103560 * 2
def baseEnd_103560 : Nat := 10503912410808899698517

theorem tailTrace_103560 : CollatzResearch.WordTrace tailWord_103560 prefixEnd_103560 10503912410808899698517 := by
  unfold tailWord_103560
  simp only [CollatzResearch.WordTrace]
  refine ⟨1888571752413640742502067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2518095669884854323336089 1888571752413640742502067)
  ·
    refine ⟨2832857628620461113753101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1888571752413640742502067 2832857628620461113753101)
    ·
      refine ⟨1062321610732672917657413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2832857628620461113753101 1062321610732672917657413)
      ·
        refine ⟨199185302012376172060765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1062321610732672917657413 199185302012376172060765)
        ·
          refine ⟨74694488254641064522787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 199185302012376172060765 74694488254641064522787)
          ·
            refine ⟨112041732381961596784181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74694488254641064522787 112041732381961596784181)
            ·
              refine ⟨10503912410808899698517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 112041732381961596784181 10503912410808899698517)
              ·
                rfl

theorem cell19_103560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 5].length) (baseStart_103560 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_103560 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_103560 prefixEnd_103560 := by exact prefixLift 103560
  have htrace : WordTrace (prefixWord ++ tailWord_103560) baseStart_103560 baseEnd_103560 := by
    simpa [prefixWord, tailWord_103560, baseEnd_103560] using wordTrace_append hprefix tailTrace_103560
  have hstable : (prefixWord ++ tailWord_103560).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103560).length < 2 ^ (prefixWord ++ tailWord_103560).sum := by decide
  have hdescent : baseEnd_103560 < baseStart_103560 := by decide
  rcases family_descends (prefixWord ++ tailWord_103560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103602 : List Nat := [3, 2, 1, 1, 1, 4, 2, 5]
def baseStart_103602 : Nat := 118140960795 + 103602 * 2 ^ 59
def prefixEnd_103602 : Nat := 4983230072969 + 3 ^ 40 * 103602 * 2
def baseEnd_103602 : Nat := 31524517195383046162103

theorem tailTrace_103602 : CollatzResearch.WordTrace tailWord_103602 prefixEnd_103602 31524517195383046162103 := by
  unfold tailWord_103602
  simp only [CollatzResearch.WordTrace]
  refine ⟨944668842668780664508265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2519116913783415105355373 944668842668780664508265)
  ·
    refine ⟨708501632001585498381199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 944668842668780664508265 708501632001585498381199)
    ·
      refine ⟨1062752448002378247571799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 708501632001585498381199 1062752448002378247571799)
      ·
        refine ⟨1594128672003567371357699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1062752448002378247571799 1594128672003567371357699)
        ·
          refine ⟨2391193008005351057036549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1594128672003567371357699 2391193008005351057036549)
          ·
            refine ⟨448348689001003323194353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2391193008005351057036549 448348689001003323194353)
            ·
              refine ⟨336261516750752492395765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 448348689001003323194353 336261516750752492395765)
              ·
                refine ⟨31524517195383046162103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 336261516750752492395765 31524517195383046162103)
                ·
                  rfl

theorem cell19_103602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 5].length) (baseStart_103602 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_103602 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_103602 prefixEnd_103602 := by exact prefixLift 103602
  have htrace : WordTrace (prefixWord ++ tailWord_103602) baseStart_103602 baseEnd_103602 := by
    simpa [prefixWord, tailWord_103602, baseEnd_103602] using wordTrace_append hprefix tailTrace_103602
  have hstable : (prefixWord ++ tailWord_103602).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103602).length < 2 ^ (prefixWord ++ tailWord_103602).sum := by decide
  have hdescent : baseEnd_103602 < baseStart_103602 := by decide
  rcases family_descends (prefixWord ++ tailWord_103602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103655 : List Nat := [1, 1, 5, 3, 2, 1, 3, 3]
def baseStart_103655 : Nat := 118140960795 + 103655 * 2 ^ 59
def prefixEnd_103655 : Nat := 4983230072969 + 3 ^ 40 * 103655 * 2
def baseEnd_103655 : Nat := 31540644291494626984181

theorem tailTrace_103655 : CollatzResearch.WordTrace tailWord_103655 prefixEnd_103655 31540644291494626984181 := by
  unfold tailWord_103655
  simp only [CollatzResearch.WordTrace]
  refine ⟨3780608439483112709712419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2520405626322075139808279 3780608439483112709712419)
  ·
    refine ⟨5670912659224669064568629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3780608439483112709712419 5670912659224669064568629)
    ·
      refine ⟨531648061802312724803309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5670912659224669064568629 531648061802312724803309)
      ·
        refine ⟨199368023175867271801241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 531648061802312724803309 199368023175867271801241)
        ·
          refine ⟨149526017381900453850931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199368023175867271801241 149526017381900453850931)
          ·
            refine ⟨224289026072850680776397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149526017381900453850931 224289026072850680776397)
            ·
              refine ⟨84108384777319005291149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 224289026072850680776397 84108384777319005291149)
              ·
                refine ⟨31540644291494626984181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84108384777319005291149 31540644291494626984181)
                ·
                  rfl

theorem cell19_103655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 3, 3].length) (baseStart_103655 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_103655 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_103655 prefixEnd_103655 := by exact prefixLift 103655
  have htrace : WordTrace (prefixWord ++ tailWord_103655) baseStart_103655 baseEnd_103655 := by
    simpa [prefixWord, tailWord_103655, baseEnd_103655] using wordTrace_append hprefix tailTrace_103655
  have hstable : (prefixWord ++ tailWord_103655).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103655).length < 2 ^ (prefixWord ++ tailWord_103655).sum := by decide
  have hdescent : baseEnd_103655 < baseStart_103655 := by decide
  rcases family_descends (prefixWord ++ tailWord_103655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103712 : List Nat := [2, 1, 1, 5, 3, 2, 2, 3]
def baseStart_103712 : Nat := 118140960795 + 103712 * 2 ^ 59
def prefixEnd_103712 : Nat := 4983230072969 + 3 ^ 40 * 103712 * 2
def baseEnd_103712 : Nat := 31557988526935383717359

theorem tailTrace_103712 : CollatzResearch.WordTrace tailWord_103712 prefixEnd_103712 31557988526935383717359 := by
  unfold tailWord_103712
  simp only [CollatzResearch.WordTrace]
  refine ⟨1891343700138305722268695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2521791600184407629691593 1891343700138305722268695)
  ·
    refine ⟨2837015550207458583403043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1891343700138305722268695 2837015550207458583403043)
    ·
      refine ⟨4255523325311187875104565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2837015550207458583403043 4255523325311187875104565)
      ·
        refine ⟨398955311747923863291053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4255523325311187875104565 398955311747923863291053)
        ·
          refine ⟨149608241905471448734145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 398955311747923863291053 149608241905471448734145)
          ·
            refine ⟨112206181429103586550609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149608241905471448734145 112206181429103586550609)
            ·
              refine ⟨84154636071827689912957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112206181429103586550609 84154636071827689912957)
              ·
                refine ⟨31557988526935383717359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84154636071827689912957 31557988526935383717359)
                ·
                  rfl

theorem cell19_103712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 2, 3].length) (baseStart_103712 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_103712 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_103712 prefixEnd_103712 := by exact prefixLift 103712
  have htrace : WordTrace (prefixWord ++ tailWord_103712) baseStart_103712 baseEnd_103712 := by
    simpa [prefixWord, tailWord_103712, baseEnd_103712] using wordTrace_append hprefix tailTrace_103712
  have hstable : (prefixWord ++ tailWord_103712).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103712).length < 2 ^ (prefixWord ++ tailWord_103712).sum := by decide
  have hdescent : baseEnd_103712 < baseStart_103712 := by decide
  rcases family_descends (prefixWord ++ tailWord_103712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103714 : List Nat := [3, 3, 1, 1, 4, 1, 1, 5]
def baseStart_103714 : Nat := 118140960795 + 103714 * 2 ^ 59
def prefixEnd_103714 : Nat := 4983230072969 + 3 ^ 40 * 103714 * 2
def baseEnd_103714 : Nat := 31558597096599971672909

theorem tailTrace_103714 : CollatzResearch.WordTrace tailWord_103714 prefixEnd_103714 31558597096599971672909 := by
  unfold tailWord_103714
  simp only [CollatzResearch.WordTrace]
  refine ⟨945690086567341446527549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2521840230846243857406797 945690086567341446527549)
  ·
    refine ⟨354633782462753042447831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 945690086567341446527549 354633782462753042447831)
    ·
      refine ⟨531950673694129563671747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 354633782462753042447831 531950673694129563671747)
      ·
        refine ⟨797926010541194345507621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 531950673694129563671747 797926010541194345507621)
        ·
          refine ⟨149611126976473939782679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 797926010541194345507621 149611126976473939782679)
          ·
            refine ⟨224416690464710909674019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149611126976473939782679 224416690464710909674019)
            ·
              refine ⟨336625035697066364511029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 224416690464710909674019 336625035697066364511029)
              ·
                refine ⟨31558597096599971672909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 336625035697066364511029 31558597096599971672909)
                ·
                  rfl

theorem cell19_103714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 5].length) (baseStart_103714 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_103714 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_103714 prefixEnd_103714 := by exact prefixLift 103714
  have htrace : WordTrace (prefixWord ++ tailWord_103714) baseStart_103714 baseEnd_103714 := by
    simpa [prefixWord, tailWord_103714, baseEnd_103714] using wordTrace_append hprefix tailTrace_103714
  have hstable : (prefixWord ++ tailWord_103714).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103714).length < 2 ^ (prefixWord ++ tailWord_103714).sum := by decide
  have hdescent : baseEnd_103714 < baseStart_103714 := by decide
  rcases family_descends (prefixWord ++ tailWord_103714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103716 : List Nat := [2, 3, 1, 3, 1, 1, 3, 5]
def baseStart_103716 : Nat := 118140960795 + 103716 * 2 ^ 59
def prefixEnd_103716 : Nat := 4983230072969 + 3 ^ 40 * 103716 * 2
def baseEnd_103716 : Nat := 31559205666264559628459

theorem tailTrace_103716 : CollatzResearch.WordTrace tailWord_103716 prefixEnd_103716 31559205666264559628459 := by
  unfold tailWord_103716
  simp only [CollatzResearch.WordTrace]
  refine ⟨1891416646131060063841501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2521888861508080085122001 1891416646131060063841501)
  ·
    refine ⟨709281242299147523940563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1891416646131060063841501 709281242299147523940563)
    ·
      refine ⟨1063921863448721285910845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 709281242299147523940563 1063921863448721285910845)
      ·
        refine ⟨398970698793270482216567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1063921863448721285910845 398970698793270482216567)
        ·
          refine ⟨598456048189905723324851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 398970698793270482216567 598456048189905723324851)
          ·
            refine ⟨897684072284858584987277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 598456048189905723324851 897684072284858584987277)
            ·
              refine ⟨336631527106821969370229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 897684072284858584987277 336631527106821969370229)
              ·
                refine ⟨31559205666264559628459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 336631527106821969370229 31559205666264559628459)
                ·
                  rfl

theorem cell19_103716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 5].length) (baseStart_103716 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_103716 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_103716 prefixEnd_103716 := by exact prefixLift 103716
  have htrace : WordTrace (prefixWord ++ tailWord_103716) baseStart_103716 baseEnd_103716 := by
    simpa [prefixWord, tailWord_103716, baseEnd_103716] using wordTrace_append hprefix tailTrace_103716
  have hstable : (prefixWord ++ tailWord_103716).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103716).length < 2 ^ (prefixWord ++ tailWord_103716).sum := by decide
  have hdescent : baseEnd_103716 < baseStart_103716 := by decide
  rcases family_descends (prefixWord ++ tailWord_103716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103790 : List Nat := [4, 1, 2, 4, 1, 7]
def baseStart_103790 : Nat := 118140960795 + 103790 * 2 ^ 59
def prefixEnd_103790 : Nat := 4983230072969 + 3 ^ 40 * 103790 * 2
def baseEnd_103790 : Nat := 3509080304872701553757

theorem tailTrace_103790 : CollatzResearch.WordTrace tailWord_103790 prefixEnd_103790 3509080304872701553757 := by
  unfold tailWord_103790
  simp only [CollatzResearch.WordTrace]
  refine ⟨473191536749253845734603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2523688195996020510584549 473191536749253845734603)
  ·
    refine ⟨709787305123880768601905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 473191536749253845734603 709787305123880768601905)
    ·
      refine ⟨532340478842910576451429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 709787305123880768601905 532340478842910576451429)
      ·
        refine ⟨99813839783045733084643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 532340478842910576451429 99813839783045733084643)
        ·
          refine ⟨149720759674568599626965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99813839783045733084643 149720759674568599626965)
          ·
            refine ⟨3509080304872701553757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 149720759674568599626965 3509080304872701553757)
            ·
              rfl

theorem cell19_103790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 7].length) (baseStart_103790 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_103790 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_103790 prefixEnd_103790 := by exact prefixLift 103790
  have htrace : WordTrace (prefixWord ++ tailWord_103790) baseStart_103790 baseEnd_103790 := by
    simpa [prefixWord, tailWord_103790, baseEnd_103790] using wordTrace_append hprefix tailTrace_103790
  have hstable : (prefixWord ++ tailWord_103790).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103790).length < 2 ^ (prefixWord ++ tailWord_103790).sum := by decide
  have hdescent : baseEnd_103790 < baseStart_103790 := by decide
  rcases family_descends (prefixWord ++ tailWord_103790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103811 : List Nat := [1, 1, 1, 3, 5, 1, 3, 4]
def baseStart_103811 : Nat := 118140960795 + 103811 * 2 ^ 59
def prefixEnd_103811 : Nat := 4983230072969 + 3 ^ 40 * 103811 * 2
def baseEnd_103811 : Nat := 31588112725332487517089

theorem tailTrace_103811 : CollatzResearch.WordTrace tailWord_103811 prefixEnd_103811 31588112725332487517089 := by
  unfold tailWord_103811
  simp only [CollatzResearch.WordTrace]
  refine ⟨3786298226917951352391287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2524198817945300901594191 3786298226917951352391287)
  ·
    refine ⟨5679447340376927028586931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3786298226917951352391287 5679447340376927028586931)
    ·
      refine ⟨8519171010565390542880397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5679447340376927028586931 8519171010565390542880397)
      ·
        refine ⟨3194689128962021453580149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8519171010565390542880397 3194689128962021453580149)
        ·
          refine ⟨299502105840189511273139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3194689128962021453580149 299502105840189511273139)
          ·
            refine ⟨449253158760284266909709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 299502105840189511273139 449253158760284266909709)
            ·
              refine ⟨168469934535106600091141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 449253158760284266909709 168469934535106600091141)
              ·
                refine ⟨31588112725332487517089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 168469934535106600091141 31588112725332487517089)
                ·
                  rfl

theorem cell19_103811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 3, 4].length) (baseStart_103811 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_103811 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_103811 prefixEnd_103811 := by exact prefixLift 103811
  have htrace : WordTrace (prefixWord ++ tailWord_103811) baseStart_103811 baseEnd_103811 := by
    simpa [prefixWord, tailWord_103811, baseEnd_103811] using wordTrace_append hprefix tailTrace_103811
  have hstable : (prefixWord ++ tailWord_103811).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103811).length < 2 ^ (prefixWord ++ tailWord_103811).sum := by decide
  have hdescent : baseEnd_103811 < baseStart_103811 := by decide
  rcases family_descends (prefixWord ++ tailWord_103811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103887 : List Nat := [1, 1, 2, 1, 1, 4, 6, 3]
def baseStart_103887 : Nat := 118140960795 + 103887 * 2 ^ 59
def prefixEnd_103887 : Nat := 4983230072969 + 3 ^ 40 * 103887 * 2
def baseEnd_103887 : Nat := 31611238372586829827993

theorem tailTrace_103887 : CollatzResearch.WordTrace tailWord_103887 prefixEnd_103887 31611238372586829827993 := by
  unfold tailWord_103887
  simp only [CollatzResearch.WordTrace]
  refine ⟨3789070174642616332157915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2526046783095077554771943 3789070174642616332157915)
  ·
    refine ⟨5683605261963924498236873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3789070174642616332157915 5683605261963924498236873)
    ·
      refine ⟨4262703946472943373677655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5683605261963924498236873 4262703946472943373677655)
      ·
        refine ⟨6394055919709415060516483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4262703946472943373677655 6394055919709415060516483)
        ·
          refine ⟨9591083879564122590774725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6394055919709415060516483 9591083879564122590774725)
          ·
            refine ⟨1798328227418272985770261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9591083879564122590774725 1798328227418272985770261)
            ·
              refine ⟨84296635660231546207981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1798328227418272985770261 84296635660231546207981)
              ·
                refine ⟨31611238372586829827993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84296635660231546207981 31611238372586829827993)
                ·
                  rfl

theorem cell19_103887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 6, 3].length) (baseStart_103887 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_103887 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_103887 prefixEnd_103887 := by exact prefixLift 103887
  have htrace : WordTrace (prefixWord ++ tailWord_103887) baseStart_103887 baseEnd_103887 := by
    simpa [prefixWord, tailWord_103887, baseEnd_103887] using wordTrace_append hprefix tailTrace_103887
  have hstable : (prefixWord ++ tailWord_103887).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103887).length < 2 ^ (prefixWord ++ tailWord_103887).sum := by decide
  have hdescent : baseEnd_103887 < baseStart_103887 := by decide
  rcases family_descends (prefixWord ++ tailWord_103887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104054 : List Nat := [5, 1, 1, 2, 2, 3, 2, 3]
def baseStart_104054 : Nat := 118140960795 + 104054 * 2 ^ 59
def prefixEnd_104054 : Nat := 4983230072969 + 3 ^ 40 * 104054 * 2
def baseEnd_104054 : Nat := 31662053939579924116427

theorem tailTrace_104054 : CollatzResearch.WordTrace tailWord_104054 prefixEnd_104054 31662053939579924116427 := by
  unfold tailWord_104054
  simp only [CollatzResearch.WordTrace]
  refine ⟨237197572814850240842951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2530107443358402568991477 237197572814850240842951)
  ·
    refine ⟨355796359222275361264427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237197572814850240842951 355796359222275361264427)
    ·
      refine ⟨533694538833413041896641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 355796359222275361264427 533694538833413041896641)
      ·
        refine ⟨400270904125059781422481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 533694538833413041896641 400270904125059781422481)
        ·
          refine ⟨300203178093794836066861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 400270904125059781422481 300203178093794836066861)
          ·
            refine ⟨112576191785173063525073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 300203178093794836066861 112576191785173063525073)
            ·
              refine ⟨84432143838879797643805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112576191785173063525073 84432143838879797643805)
              ·
                refine ⟨31662053939579924116427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84432143838879797643805 31662053939579924116427)
                ·
                  rfl

theorem cell19_104054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 2, 3].length) (baseStart_104054 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_104054 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_104054 prefixEnd_104054 := by exact prefixLift 104054
  have htrace : WordTrace (prefixWord ++ tailWord_104054) baseStart_104054 baseEnd_104054 := by
    simpa [prefixWord, tailWord_104054, baseEnd_104054] using wordTrace_append hprefix tailTrace_104054
  have hstable : (prefixWord ++ tailWord_104054).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104054).length < 2 ^ (prefixWord ++ tailWord_104054).sum := by decide
  have hdescent : baseEnd_104054 < baseStart_104054 := by decide
  rcases family_descends (prefixWord ++ tailWord_104054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104094 : List Nat := [4, 3, 1, 1, 1, 3, 2, 4]
def baseStart_104094 : Nat := 118140960795 + 104094 * 2 ^ 59
def prefixEnd_104094 : Nat := 4983230072969 + 3 ^ 40 * 104094 * 2
def baseEnd_104094 : Nat := 31674225332871683227429

theorem tailTrace_104094 : CollatzResearch.WordTrace tailWord_104094 prefixEnd_104094 31674225332871683227429 := by
  unfold tailWord_104094
  simp only [CollatzResearch.WordTrace]
  refine ⟨474577510611586335617917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2531080056595127123295557 474577510611586335617917)
  ·
    refine ⟨177966566479344875856719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 474577510611586335617917 177966566479344875856719)
    ·
      refine ⟨266949849719017313785079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177966566479344875856719 266949849719017313785079)
      ·
        refine ⟨400424774578525970677619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266949849719017313785079 400424774578525970677619)
        ·
          refine ⟨600637161867788956016429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 400424774578525970677619 600637161867788956016429)
          ·
            refine ⟨225238935700420858506161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 600637161867788956016429 225238935700420858506161)
            ·
              refine ⟨168929201775315643879621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 225238935700420858506161 168929201775315643879621)
              ·
                refine ⟨31674225332871683227429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 168929201775315643879621 31674225332871683227429)
                ·
                  rfl

theorem cell19_104094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 2, 4].length) (baseStart_104094 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_104094 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_104094 prefixEnd_104094 := by exact prefixLift 104094
  have htrace : WordTrace (prefixWord ++ tailWord_104094) baseStart_104094 baseEnd_104094 := by
    simpa [prefixWord, tailWord_104094, baseEnd_104094] using wordTrace_append hprefix tailTrace_104094
  have hstable : (prefixWord ++ tailWord_104094).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104094).length < 2 ^ (prefixWord ++ tailWord_104094).sum := by decide
  have hdescent : baseEnd_104094 < baseStart_104094 := by decide
  rcases family_descends (prefixWord ++ tailWord_104094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104096 : List Nat := [2, 1, 1, 4, 3, 2, 2, 4]
def baseStart_104096 : Nat := 118140960795 + 104096 * 2 ^ 59
def prefixEnd_104096 : Nat := 4983230072969 + 3 ^ 40 * 104096 * 2
def baseEnd_104096 : Nat := 31674833902536271182979

theorem tailTrace_104096 : CollatzResearch.WordTrace tailWord_104096 prefixEnd_104096 31674833902536271182979 := by
  unfold tailWord_104096
  simp only [CollatzResearch.WordTrace]
  refine ⟨1898346515442722513258071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2531128687256963351010761 1898346515442722513258071)
  ·
    refine ⟨2847519773164083769887107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1898346515442722513258071 2847519773164083769887107)
    ·
      refine ⟨4271279659746125654830661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2847519773164083769887107 4271279659746125654830661)
      ·
        refine ⟨800864936202398560280749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4271279659746125654830661 800864936202398560280749)
        ·
          refine ⟨300324351075899460105281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 800864936202398560280749 300324351075899460105281)
          ·
            refine ⟨225243263306924595078961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 300324351075899460105281 225243263306924595078961)
            ·
              refine ⟨168932447480193446309221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 225243263306924595078961 168932447480193446309221)
              ·
                refine ⟨31674833902536271182979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 168932447480193446309221 31674833902536271182979)
                ·
                  rfl

theorem cell19_104096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2, 4].length) (baseStart_104096 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_104096 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_104096 prefixEnd_104096 := by exact prefixLift 104096
  have htrace : WordTrace (prefixWord ++ tailWord_104096) baseStart_104096 baseEnd_104096 := by
    simpa [prefixWord, tailWord_104096, baseEnd_104096] using wordTrace_append hprefix tailTrace_104096
  have hstable : (prefixWord ++ tailWord_104096).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104096).length < 2 ^ (prefixWord ++ tailWord_104096).sum := by decide
  have hdescent : baseEnd_104096 < baseStart_104096 := by decide
  rcases family_descends (prefixWord ++ tailWord_104096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104130 : List Nat := [3, 5, 1, 2, 1, 7]
def baseStart_104130 : Nat := 118140960795 + 104130 * 2 ^ 59
def prefixEnd_104130 : Nat := 4983230072969 + 3 ^ 40 * 104130 * 2
def baseEnd_104130 : Nat := 3520575509648251825259

theorem tailTrace_104130 : CollatzResearch.WordTrace tailWord_104130 prefixEnd_104130 3520575509648251825259 := by
  unfold tailWord_104130
  simp only [CollatzResearch.WordTrace]
  refine ⟨949483278190567208313461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2531955408508179222169229 949483278190567208313461)
  ·
    refine ⟨89014057330365675779387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 949483278190567208313461 89014057330365675779387)
    ·
      refine ⟨133521085995548513669081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89014057330365675779387 133521085995548513669081)
      ·
        refine ⟨100140814496661385251811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133521085995548513669081 100140814496661385251811)
        ·
          refine ⟨150211221744992077877717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100140814496661385251811 150211221744992077877717)
          ·
            refine ⟨3520575509648251825259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 150211221744992077877717 3520575509648251825259)
            ·
              rfl

theorem cell19_104130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 7].length) (baseStart_104130 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_104130 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_104130 prefixEnd_104130 := by exact prefixLift 104130
  have htrace : WordTrace (prefixWord ++ tailWord_104130) baseStart_104130 baseEnd_104130 := by
    simpa [prefixWord, tailWord_104130, baseEnd_104130] using wordTrace_append hprefix tailTrace_104130
  have hstable : (prefixWord ++ tailWord_104130).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104130).length < 2 ^ (prefixWord ++ tailWord_104130).sum := by decide
  have hdescent : baseEnd_104130 < baseStart_104130 := by decide
  rcases family_descends (prefixWord ++ tailWord_104130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104153 : List Nat := [1, 2, 1, 2, 3, 5, 1, 4]
def baseStart_104153 : Nat := 118140960795 + 104153 * 2 ^ 59
def prefixEnd_104153 : Nat := 4983230072969 + 3 ^ 40 * 104153 * 2
def baseEnd_104153 : Nat := 31692178137977027916157

theorem tailTrace_104153 : CollatzResearch.WordTrace tailWord_104153 prefixEnd_104153 31692178137977027916157 := by
  unfold tailWord_104153
  simp only [CollatzResearch.WordTrace]
  refine ⟨3798771991678943761341113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2532514661119295840894075 3798771991678943761341113)
  ·
    refine ⟨2849078993759207821005835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3798771991678943761341113 2849078993759207821005835)
    ·
      refine ⟨4273618490638811731508753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2849078993759207821005835 4273618490638811731508753)
      ·
        refine ⟨3205213867979108798631565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4273618490638811731508753 3205213867979108798631565)
        ·
          refine ⟨1201955200492165799486837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3205213867979108798631565 1201955200492165799486837)
          ·
            refine ⟨112683300046140543701891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1201955200492165799486837 112683300046140543701891)
            ·
              refine ⟨169024950069210815552837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112683300046140543701891 169024950069210815552837)
              ·
                refine ⟨31692178137977027916157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 169024950069210815552837 31692178137977027916157)
                ·
                  rfl

theorem cell19_104153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 1, 4].length) (baseStart_104153 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_104153 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_104153 prefixEnd_104153 := by exact prefixLift 104153
  have htrace : WordTrace (prefixWord ++ tailWord_104153) baseStart_104153 baseEnd_104153 := by
    simpa [prefixWord, tailWord_104153, baseEnd_104153] using wordTrace_append hprefix tailTrace_104153
  have hstable : (prefixWord ++ tailWord_104153).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104153).length < 2 ^ (prefixWord ++ tailWord_104153).sum := by decide
  have hdescent : baseEnd_104153 < baseStart_104153 := by decide
  rcases family_descends (prefixWord ++ tailWord_104153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104229 : List Nat := [1, 3, 1, 2, 3, 2, 4, 3]
def baseStart_104229 : Nat := 118140960795 + 104229 * 2 ^ 59
def prefixEnd_104229 : Nat := 4983230072969 + 3 ^ 40 * 104229 * 2
def baseEnd_104229 : Nat := 31715303785231370227061

theorem tailTrace_104229 : CollatzResearch.WordTrace tailWord_104229 prefixEnd_104229 31715303785231370227061 := by
  unfold tailWord_104229
  simp only [CollatzResearch.WordTrace]
  refine ⟨3801543939403608741107741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2534362626269072494071827 3801543939403608741107741)
  ·
    refine ⟨1425578977276353277915403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3801543939403608741107741 1425578977276353277915403)
    ·
      refine ⟨2138368465914529916873105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1425578977276353277915403 2138368465914529916873105)
      ·
        refine ⟨1603776349435897437654829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2138368465914529916873105 1603776349435897437654829)
        ·
          refine ⟨601416131038461539120561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1603776349435897437654829 601416131038461539120561)
          ·
            refine ⟨451062098278846154340421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 601416131038461539120561 451062098278846154340421)
            ·
              refine ⟨84574143427283653938829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 451062098278846154340421 84574143427283653938829)
              ·
                refine ⟨31715303785231370227061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84574143427283653938829 31715303785231370227061)
                ·
                  rfl

theorem cell19_104229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 4, 3].length) (baseStart_104229 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_104229 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_104229 prefixEnd_104229 := by exact prefixLift 104229
  have htrace : WordTrace (prefixWord ++ tailWord_104229) baseStart_104229 baseEnd_104229 := by
    simpa [prefixWord, tailWord_104229, baseEnd_104229] using wordTrace_append hprefix tailTrace_104229
  have hstable : (prefixWord ++ tailWord_104229).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104229).length < 2 ^ (prefixWord ++ tailWord_104229).sum := by decide
  have hdescent : baseEnd_104229 < baseStart_104229 := by decide
  rcases family_descends (prefixWord ++ tailWord_104229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104246 : List Nat := [5, 1, 2, 2, 1, 3, 5]
def baseStart_104246 : Nat := 118140960795 + 104246 * 2 ^ 59
def prefixEnd_104246 : Nat := 4983230072969 + 3 ^ 40 * 104246 * 2
def baseEnd_104246 : Nat := 10573492209126789283079

theorem tailTrace_104246 : CollatzResearch.WordTrace tailWord_104246 prefixEnd_104246 10573492209126789283079 := by
  unfold tailWord_104246
  simp only [CollatzResearch.WordTrace]
  refine ⟨237635248771376290279787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2534775986894680429651061 237635248771376290279787)
  ·
    refine ⟨356452873157064435419681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237635248771376290279787 356452873157064435419681)
    ·
      refine ⟨267339654867798326564761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 356452873157064435419681 267339654867798326564761)
      ·
        refine ⟨200504741150848744923571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 267339654867798326564761 200504741150848744923571)
        ·
          refine ⟨300757111726273117385357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200504741150848744923571 300757111726273117385357)
          ·
            refine ⟨112783916897352419019509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 300757111726273117385357 112783916897352419019509)
            ·
              refine ⟨10573492209126789283079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 112783916897352419019509 10573492209126789283079)
              ·
                rfl

theorem cell19_104246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 5].length) (baseStart_104246 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_104246 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_104246 prefixEnd_104246 := by exact prefixLift 104246
  have htrace : WordTrace (prefixWord ++ tailWord_104246) baseStart_104246 baseEnd_104246 := by
    simpa [prefixWord, tailWord_104246, baseEnd_104246] using wordTrace_append hprefix tailTrace_104246
  have hstable : (prefixWord ++ tailWord_104246).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104246).length < 2 ^ (prefixWord ++ tailWord_104246).sum := by decide
  have hdescent : baseEnd_104246 < baseStart_104246 := by decide
  rcases family_descends (prefixWord ++ tailWord_104246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104250 : List Nat := [3, 1, 1, 1, 5, 1, 7]
def baseStart_104250 : Nat := 118140960795 + 104250 * 2 ^ 59
def prefixEnd_104250 : Nat := 4983230072969 + 3 ^ 40 * 104250 * 2
def baseEnd_104250 : Nat := 10573897922236514586779

theorem tailTrace_104250 : CollatzResearch.WordTrace tailWord_104250 prefixEnd_104250 10573897922236514586779 := by
  unfold tailWord_104250
  simp only [CollatzResearch.WordTrace]
  refine ⟨950577468081882331905551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2534873248218352885081469 950577468081882331905551)
  ·
    refine ⟨1425866202122823497858327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 950577468081882331905551 1425866202122823497858327)
    ·
      refine ⟨2138799303184235246787491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1425866202122823497858327 2138799303184235246787491)
      ·
        refine ⟨3208198954776352870181237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2138799303184235246787491 3208198954776352870181237)
        ·
          refine ⟨300768652010283081579491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3208198954776352870181237 300768652010283081579491)
          ·
            refine ⟨451152978015424622369237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 300768652010283081579491 451152978015424622369237)
            ·
              refine ⟨10573897922236514586779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 451152978015424622369237 10573897922236514586779)
              ·
                rfl

theorem cell19_104250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 7].length) (baseStart_104250 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_104250 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_104250 prefixEnd_104250 := by exact prefixLift 104250
  have htrace : WordTrace (prefixWord ++ tailWord_104250) baseStart_104250 baseEnd_104250 := by
    simpa [prefixWord, tailWord_104250, baseEnd_104250] using wordTrace_append hprefix tailTrace_104250
  have hstable : (prefixWord ++ tailWord_104250).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104250).length < 2 ^ (prefixWord ++ tailWord_104250).sum := by decide
  have hdescent : baseEnd_104250 < baseStart_104250 := by decide
  rcases family_descends (prefixWord ++ tailWord_104250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104288 : List Nat := [2, 1, 1, 3, 3, 2, 2, 5]
def baseStart_104288 : Nat := 118140960795 + 104288 * 2 ^ 59
def prefixEnd_104288 : Nat := 4983230072969 + 3 ^ 40 * 104288 * 2
def baseEnd_104288 : Nat := 31733256590336714915789

theorem tailTrace_104288 : CollatzResearch.WordTrace tailWord_104288 prefixEnd_104288 31733256590336714915789 := by
  unfold tailWord_104288
  simp only [CollatzResearch.WordTrace]
  refine ⟨1901847923094930908752759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2535797230793241211670345 1901847923094930908752759)
  ·
    refine ⟨2852771884642396363129139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1901847923094930908752759 2852771884642396363129139)
    ·
      refine ⟨4279157826963594544693709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2852771884642396363129139 4279157826963594544693709)
      ·
        refine ⟨1604684185111347954260141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4279157826963594544693709 1604684185111347954260141)
        ·
          refine ⟨601756569416755482847553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1604684185111347954260141 601756569416755482847553)
          ·
            refine ⟨451317427062566612135665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 601756569416755482847553 451317427062566612135665)
            ·
              refine ⟨338488070296924959101749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 451317427062566612135665 338488070296924959101749)
              ·
                refine ⟨31733256590336714915789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 338488070296924959101749 31733256590336714915789)
                ·
                  rfl

theorem cell19_104288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 5].length) (baseStart_104288 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_104288 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_104288 prefixEnd_104288 := by exact prefixLift 104288
  have htrace : WordTrace (prefixWord ++ tailWord_104288) baseStart_104288 baseEnd_104288 := by
    simpa [prefixWord, tailWord_104288, baseEnd_104288] using wordTrace_append hprefix tailTrace_104288
  have hstable : (prefixWord ++ tailWord_104288).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104288).length < 2 ^ (prefixWord ++ tailWord_104288).sum := by decide
  have hdescent : baseEnd_104288 < baseStart_104288 := by decide
  rcases family_descends (prefixWord ++ tailWord_104288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104343 : List Nat := [1, 1, 3, 3, 1, 4, 3, 3]
def baseStart_104343 : Nat := 118140960795 + 104343 * 2 ^ 59
def prefixEnd_104343 : Nat := 4983230072969 + 3 ^ 40 * 104343 * 2
def baseEnd_104343 : Nat := 31749992256112883693417

theorem tailTrace_104343 : CollatzResearch.WordTrace tailWord_104343 prefixEnd_104343 31749992256112883693417 := by
  unfold tailWord_104343
  simp only [CollatzResearch.WordTrace]
  refine ⟨3805701860990606210757683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2537134573993737473838455 3805701860990606210757683)
  ·
    refine ⟨5708552791485909316136525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3805701860990606210757683 5708552791485909316136525)
    ·
      refine ⟨2140707296807215993551197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5708552791485909316136525 2140707296807215993551197)
      ·
        refine ⟨802765236302705997581699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2140707296807215993551197 802765236302705997581699)
        ·
          refine ⟨1204147854454058996372549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 802765236302705997581699 1204147854454058996372549)
          ·
            refine ⟨225777722710136061819853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1204147854454058996372549 225777722710136061819853)
            ·
              refine ⟨84666646016301023182445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 225777722710136061819853 84666646016301023182445)
              ·
                refine ⟨31749992256112883693417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84666646016301023182445 31749992256112883693417)
                ·
                  rfl

theorem cell19_104343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 3, 3].length) (baseStart_104343 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_104343 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_104343 prefixEnd_104343 := by exact prefixLift 104343
  have htrace : WordTrace (prefixWord ++ tailWord_104343) baseStart_104343 baseEnd_104343 := by
    simpa [prefixWord, tailWord_104343, baseEnd_104343] using wordTrace_append hprefix tailTrace_104343
  have hstable : (prefixWord ++ tailWord_104343).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104343).length < 2 ^ (prefixWord ++ tailWord_104343).sum := by decide
  have hdescent : baseEnd_104343 < baseStart_104343 := by decide
  rcases family_descends (prefixWord ++ tailWord_104343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104360 : List Nat := [2, 1, 6, 2, 1, 1, 6]
def baseStart_104360 : Nat := 118140960795 + 104360 * 2 ^ 59
def prefixEnd_104360 : Nat := 4983230072969 + 3 ^ 40 * 104360 * 2
def baseEnd_104360 : Nat := 10585055032753960438531

theorem tailTrace_104360 : CollatzResearch.WordTrace tailWord_104360 prefixEnd_104360 10585055032753960438531 := by
  unfold tailWord_104360
  simp only [CollatzResearch.WordTrace]
  refine ⟨1903160950964509057063267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2537547934619345409417689 1903160950964509057063267)
  ·
    refine ⟨2854741426446763585594901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1903160950964509057063267 2854741426446763585594901)
    ·
      refine ⟨133816004364692043074761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 2854741426446763585594901 133816004364692043074761)
      ·
        refine ⟨100362003273519032306071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133816004364692043074761 100362003273519032306071)
        ·
          refine ⟨150543004910278548459107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100362003273519032306071 150543004910278548459107)
          ·
            refine ⟨225814507365417822688661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150543004910278548459107 225814507365417822688661)
            ·
              refine ⟨10585055032753960438531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 225814507365417822688661 10585055032753960438531)
              ·
                rfl

theorem cell19_104360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 6].length) (baseStart_104360 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_104360 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_104360 prefixEnd_104360 := by exact prefixLift 104360
  have htrace : WordTrace (prefixWord ++ tailWord_104360) baseStart_104360 baseEnd_104360 := by
    simpa [prefixWord, tailWord_104360, baseEnd_104360] using wordTrace_append hprefix tailTrace_104360
  have hstable : (prefixWord ++ tailWord_104360).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104360).length < 2 ^ (prefixWord ++ tailWord_104360).sum := by decide
  have hdescent : baseEnd_104360 < baseStart_104360 := by decide
  rcases family_descends (prefixWord ++ tailWord_104360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104480 : List Nat := [2, 1, 1, 15]
def baseStart_104480 : Nat := 118140960795 + 104480 * 2 ^ 59
def prefixEnd_104480 : Nat := 4983230072969 + 3 ^ 40 * 104480 * 2
def baseEnd_104480 : Nat := 392489867631322946279

theorem tailTrace_104480 : CollatzResearch.WordTrace tailWord_104480 prefixEnd_104480 392489867631322946279 := by
  unfold tailWord_104480
  simp only [CollatzResearch.WordTrace]
  refine ⟨1905349330747139304247447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2540465774329519072329929 1905349330747139304247447)
  ·
    refine ⟨2858023996120708956371171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1905349330747139304247447 2858023996120708956371171)
    ·
      refine ⟨4287035994181063434556757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2858023996120708956371171 4287035994181063434556757)
      ·
        refine ⟨392489867631322946279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 15 4287035994181063434556757 392489867631322946279)
        ·
          rfl

theorem cell19_104480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 15].length) (baseStart_104480 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_104480 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_104480 prefixEnd_104480 := by exact prefixLift 104480
  have htrace : WordTrace (prefixWord ++ tailWord_104480) baseStart_104480 baseEnd_104480 := by
    simpa [prefixWord, tailWord_104480, baseEnd_104480] using wordTrace_append hprefix tailTrace_104480
  have hstable : (prefixWord ++ tailWord_104480).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104480).length < 2 ^ (prefixWord ++ tailWord_104480).sum := by decide
  have hdescent : baseEnd_104480 < baseStart_104480 := by decide
  rcases family_descends (prefixWord ++ tailWord_104480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104497 : List Nat := [1, 2, 2, 3, 1, 3, 3, 4]
def baseStart_104497 : Nat := 118140960795 + 104497 * 2 ^ 59
def prefixEnd_104497 : Nat := 4983230072969 + 3 ^ 40 * 104497 * 2
def baseEnd_104497 : Nat := 31796852120286156270775

theorem tailTrace_104497 : CollatzResearch.WordTrace tailWord_104497 prefixEnd_104497 31796852120286156270775 := by
  unfold tailWord_104497
  simp only [CollatzResearch.WordTrace]
  refine ⟨3811318702432690511863745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2540879134955127007909163 3811318702432690511863745)
  ·
    refine ⟨2858489026824517883897809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3811318702432690511863745 2858489026824517883897809)
    ·
      refine ⟨2143866770118388412923357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2858489026824517883897809 2143866770118388412923357)
      ·
        refine ⟨803950038794395654846259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2143866770118388412923357 803950038794395654846259)
        ·
          refine ⟨1205925058191593482269389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 803950038794395654846259 1205925058191593482269389)
          ·
            refine ⟨452221896821847555851021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1205925058191593482269389 452221896821847555851021)
            ·
              refine ⟨169583211308192833444133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 452221896821847555851021 169583211308192833444133)
              ·
                refine ⟨31796852120286156270775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 169583211308192833444133 31796852120286156270775)
                ·
                  rfl

theorem cell19_104497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 3, 4].length) (baseStart_104497 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_104497 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_104497 prefixEnd_104497 := by exact prefixLift 104497
  have htrace : WordTrace (prefixWord ++ tailWord_104497) baseStart_104497 baseEnd_104497 := by
    simpa [prefixWord, tailWord_104497, baseEnd_104497] using wordTrace_append hprefix tailTrace_104497
  have hstable : (prefixWord ++ tailWord_104497).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104497).length < 2 ^ (prefixWord ++ tailWord_104497).sum := by decide
  have hdescent : baseEnd_104497 < baseStart_104497 := by decide
  rcases family_descends (prefixWord ++ tailWord_104497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104537 : List Nat := [1, 2, 1, 2, 2, 1, 10]
def baseStart_104537 : Nat := 118140960795 + 104537 * 2 ^ 59
def prefixEnd_104537 : Nat := 4983230072969 + 3 ^ 40 * 104537 * 2
def baseEnd_104537 : Nat := 10603007837859305127259

theorem tailTrace_104537 : CollatzResearch.WordTrace tailWord_104537 prefixEnd_104537 10603007837859305127259 := by
  unfold tailWord_104537
  simp only [CollatzResearch.WordTrace]
  refine ⟨3812777622287777343319865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2541851748191851562213243 3812777622287777343319865)
  ·
    refine ⟨2859583216715833007489899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3812777622287777343319865 2859583216715833007489899)
    ·
      refine ⟨4289374825073749511234849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2859583216715833007489899 4289374825073749511234849)
      ·
        refine ⟨3217031118805312133426137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4289374825073749511234849 3217031118805312133426137)
        ·
          refine ⟨2412773339103984100069603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3217031118805312133426137 2412773339103984100069603)
          ·
            refine ⟨3619160008655976150104405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2412773339103984100069603 3619160008655976150104405)
            ·
              refine ⟨10603007837859305127259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 3619160008655976150104405 10603007837859305127259)
              ·
                rfl

theorem cell19_104537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 10].length) (baseStart_104537 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_104537 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_104537 prefixEnd_104537 := by exact prefixLift 104537
  have htrace : WordTrace (prefixWord ++ tailWord_104537) baseStart_104537 baseEnd_104537 := by
    simpa [prefixWord, tailWord_104537, baseEnd_104537] using wordTrace_append hprefix tailTrace_104537
  have hstable : (prefixWord ++ tailWord_104537).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104537).length < 2 ^ (prefixWord ++ tailWord_104537).sum := by decide
  have hdescent : baseEnd_104537 < baseStart_104537 := by decide
  rcases family_descends (prefixWord ++ tailWord_104537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104573 : List Nat := [1, 4, 1, 1, 3, 3, 1, 5]
def baseStart_104573 : Nat := 118140960795 + 104573 * 2 ^ 59
def prefixEnd_104573 : Nat := 4983230072969 + 3 ^ 40 * 104573 * 2
def baseEnd_104573 : Nat := 31819977767540498581679

theorem tailTrace_104573 : CollatzResearch.WordTrace tailWord_104573 prefixEnd_104573 31819977767540498581679 := by
  unfold tailWord_104573
  simp only [CollatzResearch.WordTrace]
  refine ⟨3814090650157355491630373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2542727100104903661086915 3814090650157355491630373)
  ·
    refine ⟨715141996904504154680695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3814090650157355491630373 715141996904504154680695)
    ·
      refine ⟨1072712995356756232021043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 715141996904504154680695 1072712995356756232021043)
      ·
        refine ⟨1609069493035134348031565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1072712995356756232021043 1609069493035134348031565)
        ·
          refine ⟨603401059888175380511837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1609069493035134348031565 603401059888175380511837)
          ·
            refine ⟨226275397458065767691939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 603401059888175380511837 226275397458065767691939)
            ·
              refine ⟨339413096187098651537909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 226275397458065767691939 339413096187098651537909)
              ·
                refine ⟨31819977767540498581679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 339413096187098651537909 31819977767540498581679)
                ·
                  rfl

theorem cell19_104573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 5].length) (baseStart_104573 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_104573 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_104573 prefixEnd_104573 := by exact prefixLift 104573
  have htrace : WordTrace (prefixWord ++ tailWord_104573) baseStart_104573 baseEnd_104573 := by
    simpa [prefixWord, tailWord_104573, baseEnd_104573] using wordTrace_append hprefix tailTrace_104573
  have hstable : (prefixWord ++ tailWord_104573).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104573).length < 2 ^ (prefixWord ++ tailWord_104573).sum := by decide
  have hdescent : baseEnd_104573 < baseStart_104573 := by decide
  rcases family_descends (prefixWord ++ tailWord_104573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104590 : List Nat := [4, 1, 1, 3, 3, 2, 5]
def baseStart_104590 : Nat := 118140960795 + 104590 * 2 ^ 59
def prefixEnd_104590 : Nat := 4983230072969 + 3 ^ 40 * 104590 * 2
def baseEnd_104590 : Nat := 10608383536563165401285

theorem tailTrace_104590 : CollatzResearch.WordTrace tailWord_104590 prefixEnd_104590 10608383536563165401285 := by
  unfold tailWord_104590
  simp only [CollatzResearch.WordTrace]
  refine ⟨476838836386970924374903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2543140460730511596666149 476838836386970924374903)
  ·
    refine ⟨715258254580456386562355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 476838836386970924374903 715258254580456386562355)
    ·
      refine ⟨1072887381870684579843533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 715258254580456386562355 1072887381870684579843533)
      ·
        refine ⟨402332768201506717441325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1072887381870684579843533 402332768201506717441325)
        ·
          refine ⟨150874788075565019040497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 402332768201506717441325 150874788075565019040497)
          ·
            refine ⟨113156091056673764280373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150874788075565019040497 113156091056673764280373)
            ·
              refine ⟨10608383536563165401285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 113156091056673764280373 10608383536563165401285)
              ·
                rfl

theorem cell19_104590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 5].length) (baseStart_104590 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_104590 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_104590 prefixEnd_104590 := by exact prefixLift 104590
  have htrace : WordTrace (prefixWord ++ tailWord_104590) baseStart_104590 baseEnd_104590 := by
    simpa [prefixWord, tailWord_104590, baseEnd_104590] using wordTrace_append hprefix tailTrace_104590
  have hstable : (prefixWord ++ tailWord_104590).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104590).length < 2 ^ (prefixWord ++ tailWord_104590).sum := by decide
  have hdescent : baseEnd_104590 < baseStart_104590 := by decide
  rcases family_descends (prefixWord ++ tailWord_104590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104632 : List Nat := [2, 1, 2, 1, 2, 1, 3, 7]
def baseStart_104632 : Nat := 118140960795 + 104632 * 2 ^ 59
def prefixEnd_104632 : Nat := 4983230072969 + 3 ^ 40 * 104632 * 2
def baseEnd_104632 : Nat := 31837930572645843270407

theorem tailTrace_104632 : CollatzResearch.WordTrace tailWord_104632 prefixEnd_104632 31837930572645843270407 := by
  unfold tailWord_104632
  simp only [CollatzResearch.WordTrace]
  refine ⟨1908121278471804284014075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2544161704629072378685433 1908121278471804284014075)
  ·
    refine ⟨2862181917707706426021113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1908121278471804284014075 2862181917707706426021113)
    ·
      refine ⟨2146636438280779819515835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2862181917707706426021113 2146636438280779819515835)
      ·
        refine ⟨3219954657421169729273753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2146636438280779819515835 3219954657421169729273753)
        ·
          refine ⟨2414965993065877296955315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3219954657421169729273753 2414965993065877296955315)
          ·
            refine ⟨3622448989598815945432973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2414965993065877296955315 3622448989598815945432973)
            ·
              refine ⟨1358418371099555979537365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3622448989598815945432973 1358418371099555979537365)
              ·
                refine ⟨31837930572645843270407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1358418371099555979537365 31837930572645843270407)
                ·
                  rfl

theorem cell19_104632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 7].length) (baseStart_104632 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_104632 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_104632 prefixEnd_104632 := by exact prefixLift 104632
  have htrace : WordTrace (prefixWord ++ tailWord_104632) baseStart_104632 baseEnd_104632 := by
    simpa [prefixWord, tailWord_104632, baseEnd_104632] using wordTrace_append hprefix tailTrace_104632
  have hstable : (prefixWord ++ tailWord_104632).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104632).length < 2 ^ (prefixWord ++ tailWord_104632).sum := by decide
  have hdescent : baseEnd_104632 < baseStart_104632 := by decide
  rcases family_descends (prefixWord ++ tailWord_104632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104689 : List Nat := [1, 2, 2, 2, 2, 1, 2, 7]
def baseStart_104689 : Nat := 118140960795 + 104689 * 2 ^ 59
def prefixEnd_104689 : Nat := 4983230072969 + 3 ^ 40 * 104689 * 2
def baseEnd_104689 : Nat := 31855274808086600003585

theorem tailTrace_104689 : CollatzResearch.WordTrace tailWord_104689 prefixEnd_104689 31855274808086600003585 := by
  unfold tailWord_104689
  simp only [CollatzResearch.WordTrace]
  refine ⟨3818321517737107302853121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2545547678491404868568747 3818321517737107302853121)
  ·
    refine ⟨2863741138302830477139841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3818321517737107302853121 2863741138302830477139841)
    ·
      refine ⟨2147805853727122857854881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2863741138302830477139841 2147805853727122857854881)
      ·
        refine ⟨1610854390295342143391161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2147805853727122857854881 1610854390295342143391161)
        ·
          refine ⟨1208140792721506607543371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1610854390295342143391161 1208140792721506607543371)
          ·
            refine ⟨1812211189082259911315057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1208140792721506607543371 1812211189082259911315057)
            ·
              refine ⟨1359158391811694933486293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1812211189082259911315057 1359158391811694933486293)
              ·
                refine ⟨31855274808086600003585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1359158391811694933486293 31855274808086600003585)
                ·
                  rfl

theorem cell19_104689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 7].length) (baseStart_104689 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_104689 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_104689 prefixEnd_104689 := by exact prefixLift 104689
  have htrace : WordTrace (prefixWord ++ tailWord_104689) baseStart_104689 baseEnd_104689 := by
    simpa [prefixWord, tailWord_104689, baseEnd_104689] using wordTrace_append hprefix tailTrace_104689
  have hstable : (prefixWord ++ tailWord_104689).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104689).length < 2 ^ (prefixWord ++ tailWord_104689).sum := by decide
  have hdescent : baseEnd_104689 < baseStart_104689 := by decide
  rcases family_descends (prefixWord ++ tailWord_104689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104784 : List Nat := [2, 1, 1, 1, 1, 6, 1, 6]
def baseStart_104784 : Nat := 118140960795 + 104784 * 2 ^ 59
def prefixEnd_104784 : Nat := 4983230072969 + 3 ^ 40 * 104784 * 2
def baseEnd_104784 : Nat := 31884181867154527892215

theorem tailTrace_104784 : CollatzResearch.WordTrace tailWord_104784 prefixEnd_104784 31884181867154527892215 := by
  unfold tailWord_104784
  simp only [CollatzResearch.WordTrace]
  refine ⟨1910893226196469263780703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2547857634928625685040937 1910893226196469263780703)
  ·
    refine ⟨2866339839294703895671055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1910893226196469263780703 2866339839294703895671055)
    ·
      refine ⟨4299509758942055843506583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2866339839294703895671055 4299509758942055843506583)
      ·
        refine ⟨6449264638413083765259875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4299509758942055843506583 6449264638413083765259875)
        ·
          refine ⟨9673896957619625647889813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6449264638413083765259875 9673896957619625647889813)
          ·
            refine ⟨453463919888419952244835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 9673896957619625647889813 453463919888419952244835)
            ·
              refine ⟨680195879832629928367253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 453463919888419952244835 680195879832629928367253)
              ·
                refine ⟨31884181867154527892215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 680195879832629928367253 31884181867154527892215)
                ·
                  rfl

theorem cell19_104784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 6].length) (baseStart_104784 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_104784 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_104784 prefixEnd_104784 := by exact prefixLift 104784
  have htrace : WordTrace (prefixWord ++ tailWord_104784) baseStart_104784 baseEnd_104784 := by
    simpa [prefixWord, tailWord_104784, baseEnd_104784] using wordTrace_append hprefix tailTrace_104784
  have hstable : (prefixWord ++ tailWord_104784).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104784).length < 2 ^ (prefixWord ++ tailWord_104784).sum := by decide
  have hdescent : baseEnd_104784 < baseStart_104784 := by decide
  rcases family_descends (prefixWord ++ tailWord_104784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104803 : List Nat := [1, 1, 1, 5, 2, 1, 1, 7]
def baseStart_104803 : Nat := 118140960795 + 104803 * 2 ^ 59
def prefixEnd_104803 : Nat := 4983230072969 + 3 ^ 40 * 104803 * 2
def baseEnd_104803 : Nat := 31889963278968113469941

theorem tailTrace_104803 : CollatzResearch.WordTrace tailWord_104803 prefixEnd_104803 31889963278968113469941 := by
  unfold tailWord_104803
  simp only [CollatzResearch.WordTrace]
  refine ⟨3822479439324104772503063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2548319626216069848335375 3822479439324104772503063)
  ·
    refine ⟨5733719158986157158754595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3822479439324104772503063 5733719158986157158754595)
    ·
      refine ⟨8600578738479235738131893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5733719158986157158754595 8600578738479235738131893)
      ·
        refine ⟨806304256732428350449865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8600578738479235738131893 806304256732428350449865)
        ·
          refine ⟨604728192549321262837399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 806304256732428350449865 604728192549321262837399)
          ·
            refine ⟨907092288823981894256099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 604728192549321262837399 907092288823981894256099)
            ·
              refine ⟨1360638433235972841384149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 907092288823981894256099 1360638433235972841384149)
              ·
                refine ⟨31889963278968113469941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1360638433235972841384149 31889963278968113469941)
                ·
                  rfl

theorem cell19_104803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 7].length) (baseStart_104803 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_104803 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_104803 prefixEnd_104803 := by exact prefixLift 104803
  have htrace : WordTrace (prefixWord ++ tailWord_104803) baseStart_104803 baseEnd_104803 := by
    simpa [prefixWord, tailWord_104803, baseEnd_104803] using wordTrace_append hprefix tailTrace_104803
  have hstable : (prefixWord ++ tailWord_104803).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104803).length < 2 ^ (prefixWord ++ tailWord_104803).sum := by decide
  have hdescent : baseEnd_104803 < baseStart_104803 := by decide
  rcases family_descends (prefixWord ++ tailWord_104803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104856 : List Nat := [2, 1, 2, 5, 1, 2, 3, 3]
def baseStart_104856 : Nat := 118140960795 + 104856 * 2 ^ 59
def prefixEnd_104856 : Nat := 4983230072969 + 3 ^ 40 * 104856 * 2
def baseEnd_104856 : Nat := 31906090375079694292019

theorem tailTrace_104856 : CollatzResearch.WordTrace tailWord_104856 prefixEnd_104856 31906090375079694292019 := by
  unfold tailWord_104856
  simp only [CollatzResearch.WordTrace]
  refine ⟨1912206254066047412091211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2549608338754729882788281 1912206254066047412091211)
  ·
    refine ⟨2868309381099071118136817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1912206254066047412091211 2868309381099071118136817)
    ·
      refine ⟨2151232035824303338602613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2868309381099071118136817 2151232035824303338602613)
      ·
        refine ⟨201678003358528437993995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2151232035824303338602613 201678003358528437993995)
        ·
          refine ⟨302517005037792656990993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201678003358528437993995 302517005037792656990993)
          ·
            refine ⟨226887753778344492743245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 302517005037792656990993 226887753778344492743245)
            ·
              refine ⟨85082907666879184778717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 226887753778344492743245 85082907666879184778717)
              ·
                refine ⟨31906090375079694292019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85082907666879184778717 31906090375079694292019)
                ·
                  rfl

theorem cell19_104856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 3, 3].length) (baseStart_104856 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_104856 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_104856 prefixEnd_104856 := by exact prefixLift 104856
  have htrace : WordTrace (prefixWord ++ tailWord_104856) baseStart_104856 baseEnd_104856 := by
    simpa [prefixWord, tailWord_104856, baseEnd_104856] using wordTrace_append hprefix tailTrace_104856
  have hstable : (prefixWord ++ tailWord_104856).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104856).length < 2 ^ (prefixWord ++ tailWord_104856).sum := by decide
  have hdescent : baseEnd_104856 < baseStart_104856 := by decide
  rcases family_descends (prefixWord ++ tailWord_104856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104930 : List Nat := [3, 3, 3, 2, 1, 2, 5]
def baseStart_104930 : Nat := 118140960795 + 104930 * 2 ^ 59
def prefixEnd_104930 : Nat := 4983230072969 + 3 ^ 40 * 104930 * 2
def baseEnd_104930 : Nat := 10642869150889816215791

theorem tailTrace_104930 : CollatzResearch.WordTrace tailWord_104930 prefixEnd_104930 10642869150889816215791 := by
  unfold tailWord_104930
  simp only [CollatzResearch.WordTrace]
  refine ⟨956777877466001365594061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2551407673242670308250829 956777877466001365594061)
  ·
    refine ⟨358791704049750512097773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 956777877466001365594061 358791704049750512097773)
    ·
      refine ⟨134546889018656442036665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 358791704049750512097773 134546889018656442036665)
      ·
        refine ⟨100910166763992331527499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134546889018656442036665 100910166763992331527499)
        ·
          refine ⟨151365250145988497291249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100910166763992331527499 151365250145988497291249)
          ·
            refine ⟨113523937609491372968437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151365250145988497291249 113523937609491372968437)
            ·
              refine ⟨10642869150889816215791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 113523937609491372968437 10642869150889816215791)
              ·
                rfl

theorem cell19_104930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 5].length) (baseStart_104930 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_104930 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_104930 prefixEnd_104930 := by exact prefixLift 104930
  have htrace : WordTrace (prefixWord ++ tailWord_104930) baseStart_104930 baseEnd_104930 := by
    simpa [prefixWord, tailWord_104930, baseEnd_104930] using wordTrace_append hprefix tailTrace_104930
  have hstable : (prefixWord ++ tailWord_104930).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104930).length < 2 ^ (prefixWord ++ tailWord_104930).sum := by decide
  have hdescent : baseEnd_104930 < baseStart_104930 := by decide
  rcases family_descends (prefixWord ++ tailWord_104930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104936 : List Nat := [2, 1, 4, 1, 1, 3, 7]
def baseStart_104936 : Nat := 118140960795 + 104936 * 2 ^ 59
def prefixEnd_104936 : Nat := 4983230072969 + 3 ^ 40 * 104936 * 2
def baseEnd_104936 : Nat := 10643477720554404171341

theorem tailTrace_104936 : CollatzResearch.WordTrace tailWord_104936 prefixEnd_104936 10643477720554404171341 := by
  unfold tailWord_104936
  simp only [CollatzResearch.WordTrace]
  refine ⟨1913665173921134243547331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2551553565228178991396441 1913665173921134243547331)
  ·
    refine ⟨2870497760881701365320997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1913665173921134243547331 2870497760881701365320997)
    ·
      refine ⟨538218330165319005997687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2870497760881701365320997 538218330165319005997687)
      ·
        refine ⟨807327495247978508996531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 538218330165319005997687 807327495247978508996531)
        ·
          refine ⟨1210991242871967763494797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 807327495247978508996531 1210991242871967763494797)
          ·
            refine ⟨454121716076987911310549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1210991242871967763494797 454121716076987911310549)
            ·
              refine ⟨10643477720554404171341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 454121716076987911310549 10643477720554404171341)
              ·
                rfl

theorem cell19_104936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 7].length) (baseStart_104936 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_104936 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_104936 prefixEnd_104936 := by exact prefixLift 104936
  have htrace : WordTrace (prefixWord ++ tailWord_104936) baseStart_104936 baseEnd_104936 := by
    simpa [prefixWord, tailWord_104936, baseEnd_104936] using wordTrace_append hprefix tailTrace_104936
  have hstable : (prefixWord ++ tailWord_104936).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104936).length < 2 ^ (prefixWord ++ tailWord_104936).sum := by decide
  have hdescent : baseEnd_104936 < baseStart_104936 := by decide
  rcases family_descends (prefixWord ++ tailWord_104936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105006 : List Nat := [4, 1, 3, 1, 4, 1, 1, 4]
def baseStart_105006 : Nat := 118140960795 + 105006 * 2 ^ 59
def prefixEnd_105006 : Nat := 4983230072969 + 3 ^ 40 * 105006 * 2
def baseEnd_105006 : Nat := 31951733099923790958277

theorem tailTrace_105006 : CollatzResearch.WordTrace tailWord_105006 prefixEnd_105006 31951733099923790958277 := by
  unfold tailWord_105006
  simp only [CollatzResearch.WordTrace]
  refine ⟨478735432198583805267859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2553255638392446961428581 478735432198583805267859)
  ·
    refine ⟨718103148297875707901789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 478735432198583805267859 718103148297875707901789)
    ·
      refine ⟨269288680611703390463171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 718103148297875707901789 269288680611703390463171)
      ·
        refine ⟨403933020917555085694757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269288680611703390463171 403933020917555085694757)
        ·
          refine ⟨75737441422041578567767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 403933020917555085694757 75737441422041578567767)
          ·
            refine ⟨113606162133062367851651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75737441422041578567767 113606162133062367851651)
            ·
              refine ⟨170409243199593551777477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113606162133062367851651 170409243199593551777477)
              ·
                refine ⟨31951733099923790958277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 170409243199593551777477 31951733099923790958277)
                ·
                  rfl

theorem cell19_105006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 1, 4].length) (baseStart_105006 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_105006 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_105006 prefixEnd_105006 := by exact prefixLift 105006
  have htrace : WordTrace (prefixWord ++ tailWord_105006) baseStart_105006 baseEnd_105006 := by
    simpa [prefixWord, tailWord_105006, baseEnd_105006] using wordTrace_append hprefix tailTrace_105006
  have hstable : (prefixWord ++ tailWord_105006).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105006).length < 2 ^ (prefixWord ++ tailWord_105006).sum := by decide
  have hdescent : baseEnd_105006 < baseStart_105006 := by decide
  rcases family_descends (prefixWord ++ tailWord_105006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105029 : List Nat := [1, 3, 1, 1, 1, 6, 3, 3]
def baseStart_105029 : Nat := 118140960795 + 105029 * 2 ^ 59
def prefixEnd_105029 : Nat := 4983230072969 + 3 ^ 40 * 105029 * 2
def baseEnd_105029 : Nat := 31958731651066552447103

theorem tailTrace_105029 : CollatzResearch.WordTrace tailWord_105029 prefixEnd_105029 31958731651066552447103 := by
  unfold tailWord_105029
  simp only [CollatzResearch.WordTrace]
  refine ⟨3830722336505345370230141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2553814891003563580153427 3830722336505345370230141)
  ·
    refine ⟨1436520876189504513836303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3830722336505345370230141 1436520876189504513836303)
    ·
      refine ⟨2154781314284256770754455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1436520876189504513836303 2154781314284256770754455)
      ·
        refine ⟨3232171971426385156131683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2154781314284256770754455 3232171971426385156131683)
        ·
          refine ⟨4848257957139577734197525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3232171971426385156131683 4848257957139577734197525)
          ·
            refine ⟨227262091740917706290509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 4848257957139577734197525 227262091740917706290509)
            ·
              refine ⟨85223284402844139858941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 227262091740917706290509 85223284402844139858941)
              ·
                refine ⟨31958731651066552447103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85223284402844139858941 31958731651066552447103)
                ·
                  rfl

theorem cell19_105029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 3, 3].length) (baseStart_105029 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_105029 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_105029 prefixEnd_105029 := by exact prefixLift 105029
  have htrace : WordTrace (prefixWord ++ tailWord_105029) baseStart_105029 baseEnd_105029 := by
    simpa [prefixWord, tailWord_105029, baseEnd_105029] using wordTrace_append hprefix tailTrace_105029
  have hstable : (prefixWord ++ tailWord_105029).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105029).length < 2 ^ (prefixWord ++ tailWord_105029).sum := by decide
  have hdescent : baseEnd_105029 < baseStart_105029 := by decide
  rcases family_descends (prefixWord ++ tailWord_105029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105088 : List Nat := [2, 1, 1, 2, 1, 6, 1, 5]
def baseStart_105088 : Nat := 118140960795 + 105088 * 2 ^ 59
def prefixEnd_105088 : Nat := 4983230072969 + 3 ^ 40 * 105088 * 2
def baseEnd_105088 : Nat := 31976684456171897135831

theorem tailTrace_105088 : CollatzResearch.WordTrace tailWord_105088 prefixEnd_105088 31976684456171897135831 := by
  unfold tailWord_105088
  simp only [CollatzResearch.WordTrace]
  refine ⟨1916437121645799223313959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2555249495527732297751945 1916437121645799223313959)
  ·
    refine ⟨2874655682468698834970939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1916437121645799223313959 2874655682468698834970939)
    ·
      refine ⟨4311983523703048252456409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2874655682468698834970939 4311983523703048252456409)
      ·
        refine ⟨3233987642777286189342307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4311983523703048252456409 3233987642777286189342307)
        ·
          refine ⟨4850981464165929284013461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3233987642777286189342307 4850981464165929284013461)
          ·
            refine ⟨227389756132777935188131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 4850981464165929284013461 227389756132777935188131)
            ·
              refine ⟨341084634199166902782197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 227389756132777935188131 341084634199166902782197)
              ·
                refine ⟨31976684456171897135831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 341084634199166902782197 31976684456171897135831)
                ·
                  rfl

theorem cell19_105088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 5].length) (baseStart_105088 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_105088 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_105088 prefixEnd_105088 := by exact prefixLift 105088
  have htrace : WordTrace (prefixWord ++ tailWord_105088) baseStart_105088 baseEnd_105088 := by
    simpa [prefixWord, tailWord_105088, baseEnd_105088] using wordTrace_append hprefix tailTrace_105088
  have hstable : (prefixWord ++ tailWord_105088).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105088).length < 2 ^ (prefixWord ++ tailWord_105088).sum := by decide
  have hdescent : baseEnd_105088 < baseStart_105088 := by decide
  rcases family_descends (prefixWord ++ tailWord_105088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105158 : List Nat := [6, 1, 2, 1, 3, 6]
def baseStart_105158 : Nat := 118140960795 + 105158 * 2 ^ 59
def prefixEnd_105158 : Nat := 4983230072969 + 3 ^ 40 * 105158 * 2
def baseEnd_105158 : Nat := 3555331599381386175565

theorem tailTrace_105158 : CollatzResearch.WordTrace tailWord_105158 prefixEnd_105158 3555331599381386175565 := by
  unfold tailWord_105158
  simp only [CollatzResearch.WordTrace]
  refine ⟨119857104782437512552379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 2556951568692000267784085 119857104782437512552379)
  ·
    refine ⟨179785657173656268828569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119857104782437512552379 179785657173656268828569)
    ·
      refine ⟨134839242880242201621427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179785657173656268828569 134839242880242201621427)
      ·
        refine ⟨202258864320363302432141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134839242880242201621427 202258864320363302432141)
        ·
          refine ⟨75847074120136238412053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 202258864320363302432141 75847074120136238412053)
          ·
            refine ⟨3555331599381386175565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 75847074120136238412053 3555331599381386175565)
            ·
              rfl

theorem cell19_105158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 6].length) (baseStart_105158 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_105158 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_105158 prefixEnd_105158 := by exact prefixLift 105158
  have htrace : WordTrace (prefixWord ++ tailWord_105158) baseStart_105158 baseEnd_105158 := by
    simpa [prefixWord, tailWord_105158, baseEnd_105158] using wordTrace_append hprefix tailTrace_105158
  have hstable : (prefixWord ++ tailWord_105158).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105158).length < 2 ^ (prefixWord ++ tailWord_105158).sum := by decide
  have hdescent : baseEnd_105158 < baseStart_105158 := by decide
  rcases family_descends (prefixWord ++ tailWord_105158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105164 : List Nat := [2, 2, 1, 5, 1, 8]
def baseStart_105164 : Nat := 118140960795 + 105164 * 2 ^ 59
def prefixEnd_105164 : Nat := 4983230072969 + 3 ^ 40 * 105164 * 2
def baseEnd_105164 : Nat := 3555534455936248827415

theorem tailTrace_105164 : CollatzResearch.WordTrace tailWord_105164 prefixEnd_105164 3555534455936248827415 := by
  unfold tailWord_105164
  simp only [CollatzResearch.WordTrace]
  refine ⟨1917823095508131713197273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2557097460677508950929697 1917823095508131713197273)
  ·
    refine ⟨1438367321631098784897955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1917823095508131713197273 1438367321631098784897955)
    ·
      refine ⟨2157550982446648177346933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1438367321631098784897955 2157550982446648177346933)
      ·
        refine ⟨202270404604373266626275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2157550982446648177346933 202270404604373266626275)
        ·
          refine ⟨303405606906559899939413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202270404604373266626275 303405606906559899939413)
          ·
            refine ⟨3555534455936248827415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 303405606906559899939413 3555534455936248827415)
            ·
              rfl

theorem cell19_105164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 8].length) (baseStart_105164 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_105164 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_105164 prefixEnd_105164 := by exact prefixLift 105164
  have htrace : WordTrace (prefixWord ++ tailWord_105164) baseStart_105164 baseEnd_105164 := by
    simpa [prefixWord, tailWord_105164, baseEnd_105164] using wordTrace_append hprefix tailTrace_105164
  have hstable : (prefixWord ++ tailWord_105164).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105164).length < 2 ^ (prefixWord ++ tailWord_105164).sum := by decide
  have hdescent : baseEnd_105164 < baseStart_105164 := by decide
  rcases family_descends (prefixWord ++ tailWord_105164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105183 : List Nat := [1, 1, 2, 3, 2, 3, 3, 4]
def baseStart_105183 : Nat := 118140960795 + 105183 * 2 ^ 59
def prefixEnd_105183 : Nat := 4983230072969 + 3 ^ 40 * 105183 * 2
def baseEnd_105183 : Nat := 32005591515239825024461

theorem tailTrace_105183 : CollatzResearch.WordTrace tailWord_105183 prefixEnd_105183 32005591515239825024461 := by
  unfold tailWord_105183
  simp only [CollatzResearch.WordTrace]
  refine ⟨3836339177947429671336203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2557559451964953114224135 3836339177947429671336203)
  ·
    refine ⟨5754508766921144507004305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3836339177947429671336203 5754508766921144507004305)
    ·
      refine ⟨4315881575190858380253229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5754508766921144507004305 4315881575190858380253229)
      ·
        refine ⟨1618455590696571892594961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4315881575190858380253229 1618455590696571892594961)
        ·
          refine ⟨1213841693022428919446221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1618455590696571892594961 1213841693022428919446221)
          ·
            refine ⟨455190634883410844792333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1213841693022428919446221 455190634883410844792333)
            ·
              refine ⟨170696488081279066797125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 455190634883410844792333 170696488081279066797125)
              ·
                refine ⟨32005591515239825024461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 170696488081279066797125 32005591515239825024461)
                ·
                  rfl

theorem cell19_105183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 3, 4].length) (baseStart_105183 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_105183 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_105183 prefixEnd_105183 := by exact prefixLift 105183
  have htrace : WordTrace (prefixWord ++ tailWord_105183) baseStart_105183 baseEnd_105183 := by
    simpa [prefixWord, tailWord_105183, baseEnd_105183] using wordTrace_append hprefix tailTrace_105183
  have hstable : (prefixWord ++ tailWord_105183).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105183).length < 2 ^ (prefixWord ++ tailWord_105183).sum := by decide
  have hdescent : baseEnd_105183 < baseStart_105183 := by decide
  rcases family_descends (prefixWord ++ tailWord_105183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105293 : List Nat := [1, 6, 1, 2, 2, 1, 2, 4]
def baseStart_105293 : Nat := 118140960795 + 105293 * 2 ^ 59
def prefixEnd_105293 : Nat := 4983230072969 + 3 ^ 40 * 105293 * 2
def baseEnd_105293 : Nat := 32039062846792162579717

theorem tailTrace_105293 : CollatzResearch.WordTrace tailWord_105293 prefixEnd_105293 32039062846792162579717 := by
  unfold tailWord_105293
  simp only [CollatzResearch.WordTrace]
  refine ⟨3840351207548918457840533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2560234138365945638560355 3840351207548918457840533)
  ·
    refine ⟨180016462853855552711275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 3840351207548918457840533 180016462853855552711275)
    ·
      refine ⟨270024694280783329066913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180016462853855552711275 270024694280783329066913)
      ·
        refine ⟨202518520710587496800185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 270024694280783329066913 202518520710587496800185)
        ·
          refine ⟨151888890532940622600139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 202518520710587496800185 151888890532940622600139)
          ·
            refine ⟨227833335799410933900209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151888890532940622600139 227833335799410933900209)
            ·
              refine ⟨170875001849558200425157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 227833335799410933900209 170875001849558200425157)
              ·
                refine ⟨32039062846792162579717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 170875001849558200425157 32039062846792162579717)
                ·
                  rfl

theorem cell19_105293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 2, 4].length) (baseStart_105293 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_105293 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_105293 prefixEnd_105293 := by exact prefixLift 105293
  have htrace : WordTrace (prefixWord ++ tailWord_105293) baseStart_105293 baseEnd_105293 := by
    simpa [prefixWord, tailWord_105293, baseEnd_105293] using wordTrace_append hprefix tailTrace_105293
  have hstable : (prefixWord ++ tailWord_105293).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105293).length < 2 ^ (prefixWord ++ tailWord_105293).sum := by decide
  have hdescent : baseEnd_105293 < baseStart_105293 := by decide
  rcases family_descends (prefixWord ++ tailWord_105293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105316 : List Nat := [2, 3, 1, 1, 4, 1, 2, 5]
def baseStart_105316 : Nat := 118140960795 + 105316 * 2 ^ 59
def prefixEnd_105316 : Nat := 4983230072969 + 3 ^ 40 * 105316 * 2
def baseEnd_105316 : Nat := 32046061397934924068543

theorem tailTrace_105316 : CollatzResearch.WordTrace tailWord_105316 prefixEnd_105316 32046061397934924068543 := by
  unfold tailWord_105316
  simp only [CollatzResearch.WordTrace]
  refine ⟨1920595043232796692963901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2560793390977062257285201 1920595043232796692963901)
  ·
    refine ⟨720223141212298759861463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1920595043232796692963901 720223141212298759861463)
    ·
      refine ⟨1080334711818448139792195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 720223141212298759861463 1080334711818448139792195)
      ·
        refine ⟨1620502067727672209688293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1080334711818448139792195 1620502067727672209688293)
        ·
          refine ⟨303844137698938539316555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1620502067727672209688293 303844137698938539316555)
          ·
            refine ⟨455766206548407808974833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 303844137698938539316555 455766206548407808974833)
            ·
              refine ⟨341824654911305856731125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 455766206548407808974833 341824654911305856731125)
              ·
                refine ⟨32046061397934924068543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 341824654911305856731125 32046061397934924068543)
                ·
                  rfl

theorem cell19_105316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 5].length) (baseStart_105316 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_105316 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_105316 prefixEnd_105316 := by exact prefixLift 105316
  have htrace : WordTrace (prefixWord ++ tailWord_105316) baseStart_105316 baseEnd_105316 := by
    simpa [prefixWord, tailWord_105316, baseEnd_105316] using wordTrace_append hprefix tailTrace_105316
  have hstable : (prefixWord ++ tailWord_105316).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105316).length < 2 ^ (prefixWord ++ tailWord_105316).sum := by decide
  have hdescent : baseEnd_105316 < baseStart_105316 := by decide
  rcases family_descends (prefixWord ++ tailWord_105316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105337 : List Nat := [1, 2, 1, 3, 2, 10]
def baseStart_105337 : Nat := 118140960795 + 105337 * 2 ^ 59
def prefixEnd_105337 : Nat := 4983230072969 + 3 ^ 40 * 105337 * 2
def baseEnd_105337 : Nat := 3561383486601455289091

theorem tailTrace_105337 : CollatzResearch.WordTrace tailWord_105337 prefixEnd_105337 3561383486601455289091 := by
  unfold tailWord_105337
  simp only [CollatzResearch.WordTrace]
  refine ⟨3841956019389513972442265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2561304012926342648294843 3841956019389513972442265)
  ·
    refine ⟨2881467014542135479331699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3841956019389513972442265 2881467014542135479331699)
    ·
      refine ⟨4322200521813203218997549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2881467014542135479331699 4322200521813203218997549)
      ·
        refine ⟨1620825195679951207124081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4322200521813203218997549 1620825195679951207124081)
        ·
          refine ⟨1215618896759963405343061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1620825195679951207124081 1215618896759963405343061)
          ·
            refine ⟨3561383486601455289091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1215618896759963405343061 3561383486601455289091)
            ·
              rfl

theorem cell19_105337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 10].length) (baseStart_105337 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_105337 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_105337 prefixEnd_105337 := by exact prefixLift 105337
  have htrace : WordTrace (prefixWord ++ tailWord_105337) baseStart_105337 baseEnd_105337 := by
    simpa [prefixWord, tailWord_105337, baseEnd_105337] using wordTrace_append hprefix tailTrace_105337
  have hstable : (prefixWord ++ tailWord_105337).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105337).length < 2 ^ (prefixWord ++ tailWord_105337).sum := by decide
  have hdescent : baseEnd_105337 < baseStart_105337 := by decide
  rcases family_descends (prefixWord ++ tailWord_105337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105346 : List Nat := [3, 4, 2, 2, 2, 1, 1, 4]
def baseStart_105346 : Nat := 118140960795 + 105346 * 2 ^ 59
def prefixEnd_105346 : Nat := 4983230072969 + 3 ^ 40 * 105346 * 2
def baseEnd_105346 : Nat := 32055189942903743401795

theorem tailTrace_105346 : CollatzResearch.WordTrace tailWord_105346 prefixEnd_105346 32055189942903743401795 := by
  unfold tailWord_105346
  simp only [CollatzResearch.WordTrace]
  refine ⟨960571069089227127379973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2561522850904605673013261 960571069089227127379973)
  ·
    refine ⟨180107075454230086383745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 960571069089227127379973 180107075454230086383745)
    ·
      refine ⟨135080306590672564787809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180107075454230086383745 135080306590672564787809)
      ·
        refine ⟨101310229943004423590857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135080306590672564787809 101310229943004423590857)
        ·
          refine ⟨75982672457253317693143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101310229943004423590857 75982672457253317693143)
          ·
            refine ⟨113974008685879976539715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75982672457253317693143 113974008685879976539715)
            ·
              refine ⟨170961013028819964809573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113974008685879976539715 170961013028819964809573)
              ·
                refine ⟨32055189942903743401795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 170961013028819964809573 32055189942903743401795)
                ·
                  rfl

theorem cell19_105346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 1, 4].length) (baseStart_105346 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_105346 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_105346 prefixEnd_105346 := by exact prefixLift 105346
  have htrace : WordTrace (prefixWord ++ tailWord_105346) baseStart_105346 baseEnd_105346 := by
    simpa [prefixWord, tailWord_105346, baseEnd_105346] using wordTrace_append hprefix tailTrace_105346
  have hstable : (prefixWord ++ tailWord_105346).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105346).length < 2 ^ (prefixWord ++ tailWord_105346).sum := by decide
  have hdescent : baseEnd_105346 < baseStart_105346 := by decide
  rcases family_descends (prefixWord ++ tailWord_105346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105352 : List Nat := [2, 1, 3, 3, 2, 3, 1, 4]
def baseStart_105352 : Nat := 118140960795 + 105352 * 2 ^ 59
def prefixEnd_105352 : Nat := 4983230072969 + 3 ^ 40 * 105352 * 2
def baseEnd_105352 : Nat := 32057015651897507268445

theorem tailTrace_105352 : CollatzResearch.WordTrace tailWord_105352 prefixEnd_105352 32057015651897507268445 := by
  unfold tailWord_105352
  simp only [CollatzResearch.WordTrace]
  refine ⟨1921251557167585767119155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2561668742890114356158873 1921251557167585767119155)
  ·
    refine ⟨2881877335751378650678733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1921251557167585767119155 2881877335751378650678733)
    ·
      refine ⟨1080704000906766994004525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2881877335751378650678733 1080704000906766994004525)
      ·
        refine ⟨405264000340037622751697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1080704000906766994004525 405264000340037622751697)
        ·
          refine ⟨303948000255028217063773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 405264000340037622751697 303948000255028217063773)
          ·
            refine ⟨113980500095635581398915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 303948000255028217063773 113980500095635581398915)
            ·
              refine ⟨170970750143453372098373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113980500095635581398915 170970750143453372098373)
              ·
                refine ⟨32057015651897507268445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 170970750143453372098373 32057015651897507268445)
                ·
                  rfl

theorem cell19_105352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 1, 4].length) (baseStart_105352 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_105352 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_105352 prefixEnd_105352 := by exact prefixLift 105352
  have htrace : WordTrace (prefixWord ++ tailWord_105352) baseStart_105352 baseEnd_105352 := by
    simpa [prefixWord, tailWord_105352, baseEnd_105352] using wordTrace_append hprefix tailTrace_105352
  have hstable : (prefixWord ++ tailWord_105352).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105352).length < 2 ^ (prefixWord ++ tailWord_105352).sum := by decide
  have hdescent : baseEnd_105352 < baseStart_105352 := by decide
  rcases family_descends (prefixWord ++ tailWord_105352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105426 : List Nat := [3, 2, 2, 3, 1, 3, 2, 3]
def baseStart_105426 : Nat := 118140960795 + 105426 * 2 ^ 59
def prefixEnd_105426 : Nat := 4983230072969 + 3 ^ 40 * 105426 * 2
def baseEnd_105426 : Nat := 32079532729487261623799

theorem tailTrace_105426 : CollatzResearch.WordTrace tailWord_105426 prefixEnd_105426 32079532729487261623799 := by
  unfold tailWord_105426
  simp only [CollatzResearch.WordTrace]
  refine ⟨961300529016770543108033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2563468077378054781621421 961300529016770543108033)
  ·
    refine ⟨720975396762577907331025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 961300529016770543108033 720975396762577907331025)
    ·
      refine ⟨540731547571933430498269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 720975396762577907331025 540731547571933430498269)
      ·
        refine ⟨202774330339475036436851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 540731547571933430498269 202774330339475036436851)
        ·
          refine ⟨304161495509212554655277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202774330339475036436851 304161495509212554655277)
          ·
            refine ⟨114060560815954707995729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 304161495509212554655277 114060560815954707995729)
            ·
              refine ⟨85545420611966030996797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114060560815954707995729 85545420611966030996797)
              ·
                refine ⟨32079532729487261623799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85545420611966030996797 32079532729487261623799)
                ·
                  rfl

theorem cell19_105426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 2, 3].length) (baseStart_105426 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_105426 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_105426 prefixEnd_105426 := by exact prefixLift 105426
  have htrace : WordTrace (prefixWord ++ tailWord_105426) baseStart_105426 baseEnd_105426 := by
    simpa [prefixWord, tailWord_105426, baseEnd_105426] using wordTrace_append hprefix tailTrace_105426
  have hstable : (prefixWord ++ tailWord_105426).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105426).length < 2 ^ (prefixWord ++ tailWord_105426).sum := by decide
  have hdescent : baseEnd_105426 < baseStart_105426 := by decide
  rcases family_descends (prefixWord ++ tailWord_105426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105428 : List Nat := [2, 4, 1, 2, 1, 2, 4, 3]
def baseStart_105428 : Nat := 118140960795 + 105428 * 2 ^ 59
def prefixEnd_105428 : Nat := 4983230072969 + 3 ^ 40 * 105428 * 2
def baseEnd_105428 : Nat := 32080141299151849579349

theorem tailTrace_105428 : CollatzResearch.WordTrace tailWord_105428 prefixEnd_105428 32080141299151849579349 := by
  unfold tailWord_105428
  simp only [CollatzResearch.WordTrace]
  refine ⟨1922637531029918257002469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2563516708039891009336625 1922637531029918257002469)
  ·
    refine ⟨360494537068109673187963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1922637531029918257002469 360494537068109673187963)
    ·
      refine ⟨540741805602164509781945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 360494537068109673187963 540741805602164509781945)
      ·
        refine ⟨405556354201623382336459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 540741805602164509781945 405556354201623382336459)
        ·
          refine ⟨608334531302435073504689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 405556354201623382336459 608334531302435073504689)
          ·
            refine ⟨456250898476826305128517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 608334531302435073504689 456250898476826305128517)
            ·
              refine ⟨85547043464404932211597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 456250898476826305128517 85547043464404932211597)
              ·
                refine ⟨32080141299151849579349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85547043464404932211597 32080141299151849579349)
                ·
                  rfl

theorem cell19_105428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 4, 3].length) (baseStart_105428 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_105428 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_105428 prefixEnd_105428 := by exact prefixLift 105428
  have htrace : WordTrace (prefixWord ++ tailWord_105428) baseStart_105428 baseEnd_105428 := by
    simpa [prefixWord, tailWord_105428, baseEnd_105428] using wordTrace_append hprefix tailTrace_105428
  have hstable : (prefixWord ++ tailWord_105428).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105428).length < 2 ^ (prefixWord ++ tailWord_105428).sum := by decide
  have hdescent : baseEnd_105428 < baseStart_105428 := by decide
  rcases family_descends (prefixWord ++ tailWord_105428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105445 : List Nat := [1, 3, 1, 6, 2, 1, 5]
def baseStart_105445 : Nat := 118140960795 + 105445 * 2 ^ 59
def prefixEnd_105445 : Nat := 4983230072969 + 3 ^ 40 * 105445 * 2
def baseEnd_105445 : Nat := 10695104713766949067175

theorem tailTrace_105445 : CollatzResearch.WordTrace tailWord_105445 prefixEnd_105445 10695104713766949067175 := by
  unfold tailWord_105445
  simp only [CollatzResearch.WordTrace]
  refine ⟨3845895102998248417373789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2563930068665498944915859 3845895102998248417373789)
  ·
    refine ⟨1442210663624343156515171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3845895102998248417373789 1442210663624343156515171)
    ·
      refine ⟨2163315995436514734772757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1442210663624343156515171 2163315995436514734772757)
      ·
        refine ⟨101405437286086628192473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 2163315995436514734772757 101405437286086628192473)
        ·
          refine ⟨76054077964564971144355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101405437286086628192473 76054077964564971144355)
          ·
            refine ⟨114081116946847456716533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76054077964564971144355 114081116946847456716533)
            ·
              refine ⟨10695104713766949067175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 114081116946847456716533 10695104713766949067175)
              ·
                rfl

theorem cell19_105445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 5].length) (baseStart_105445 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_105445 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_105445 prefixEnd_105445 := by exact prefixLift 105445
  have htrace : WordTrace (prefixWord ++ tailWord_105445) baseStart_105445 baseEnd_105445 := by
    simpa [prefixWord, tailWord_105445, baseEnd_105445] using wordTrace_append hprefix tailTrace_105445
  have hstable : (prefixWord ++ tailWord_105445).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105445).length < 2 ^ (prefixWord ++ tailWord_105445).sum := by decide
  have hdescent : baseEnd_105445 < baseStart_105445 := by decide
  rcases family_descends (prefixWord ++ tailWord_105445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105460 : List Nat := [2, 6, 2, 1, 1, 1, 2, 4]
def baseStart_105460 : Nat := 118140960795 + 105460 * 2 ^ 59
def prefixEnd_105460 : Nat := 4983230072969 + 3 ^ 40 * 105460 * 2
def baseEnd_105460 : Nat := 32089878413785256868151

theorem tailTrace_105460 : CollatzResearch.WordTrace tailWord_105460 prefixEnd_105460 32089878413785256868151 := by
  unfold tailWord_105460
  simp only [CollatzResearch.WordTrace]
  refine ⟨1923221098971952989584917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2564294798629270652779889 1923221098971952989584917)
  ·
    refine ⟨90150989014310296386793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 1923221098971952989584917 90150989014310296386793)
    ·
      refine ⟨67613241760732722290095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90150989014310296386793 67613241760732722290095)
      ·
        refine ⟨101419862641099083435143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67613241760732722290095 101419862641099083435143)
        ·
          refine ⟨152129793961648625152715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101419862641099083435143 152129793961648625152715)
          ·
            refine ⟨228194690942472937729073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152129793961648625152715 228194690942472937729073)
            ·
              refine ⟨171146018206854703296805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 228194690942472937729073 171146018206854703296805)
              ·
                refine ⟨32089878413785256868151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 171146018206854703296805 32089878413785256868151)
                ·
                  rfl

theorem cell19_105460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 2, 4].length) (baseStart_105460 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_105460 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_105460 prefixEnd_105460 := by exact prefixLift 105460
  have htrace : WordTrace (prefixWord ++ tailWord_105460) baseStart_105460 baseEnd_105460 := by
    simpa [prefixWord, tailWord_105460, baseEnd_105460] using wordTrace_append hprefix tailTrace_105460
  have hstable : (prefixWord ++ tailWord_105460).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105460).length < 2 ^ (prefixWord ++ tailWord_105460).sum := by decide
  have hdescent : baseEnd_105460 < baseStart_105460 := by decide
  rcases family_descends (prefixWord ++ tailWord_105460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105468 : List Nat := [2, 2, 2, 1, 2, 4, 2, 4]
def baseStart_105468 : Nat := 118140960795 + 105468 * 2 ^ 59
def prefixEnd_105468 : Nat := 4983230072969 + 3 ^ 40 * 105468 * 2
def baseEnd_105468 : Nat := 32092312692443608690351

theorem tailTrace_105468 : CollatzResearch.WordTrace tailWord_105468 prefixEnd_105468 32092312692443608690351 := by
  unfold tailWord_105468
  simp only [CollatzResearch.WordTrace]
  refine ⟨1923366990957461672730529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2564489321276615563640705 1923366990957461672730529)
  ·
    refine ⟨1442525243218096254547897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1923366990957461672730529 1442525243218096254547897)
    ·
      refine ⟨1081893932413572190910923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1442525243218096254547897 1081893932413572190910923)
      ·
        refine ⟨1622840898620358286366385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1081893932413572190910923 1622840898620358286366385)
        ·
          refine ⟨1217130673965268714774789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1622840898620358286366385 1217130673965268714774789)
          ·
            refine ⟨228212001368487884020273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1217130673965268714774789 228212001368487884020273)
            ·
              refine ⟨171159001026365913015205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 228212001368487884020273 171159001026365913015205)
              ·
                refine ⟨32092312692443608690351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 171159001026365913015205 32092312692443608690351)
                ·
                  rfl

theorem cell19_105468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 2, 4].length) (baseStart_105468 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_105468 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_105468 prefixEnd_105468 := by exact prefixLift 105468
  have htrace : WordTrace (prefixWord ++ tailWord_105468) baseStart_105468 baseEnd_105468 := by
    simpa [prefixWord, tailWord_105468, baseEnd_105468] using wordTrace_append hprefix tailTrace_105468
  have hstable : (prefixWord ++ tailWord_105468).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105468).length < 2 ^ (prefixWord ++ tailWord_105468).sum := by decide
  have hdescent : baseEnd_105468 < baseStart_105468 := by decide
  rcases family_descends (prefixWord ++ tailWord_105468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105504 : List Nat := [2, 1, 1, 7, 2, 6]
def baseStart_105504 : Nat := 118140960795 + 105504 * 2 ^ 59
def prefixEnd_105504 : Nat := 4983230072969 + 3 ^ 40 * 105504 * 2
def baseEnd_105504 : Nat := 3567029660711799098917

theorem tailTrace_105504 : CollatzResearch.WordTrace tailWord_105504 prefixEnd_105504 3567029660711799098917 := by
  unfold tailWord_105504
  simp only [CollatzResearch.WordTrace]
  refine ⟨1924023504892250746885783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2565364673189667662514377 1924023504892250746885783)
  ·
    refine ⟨2886035257338376120328675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1924023504892250746885783 2886035257338376120328675)
    ·
      refine ⟨4329052886007564180493013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2886035257338376120328675 4329052886007564180493013)
      ·
        refine ⟨101462177015802285480305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 4329052886007564180493013 101462177015802285480305)
        ·
          refine ⟨76096632761851714110229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101462177015802285480305 76096632761851714110229)
          ·
            refine ⟨3567029660711799098917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 76096632761851714110229 3567029660711799098917)
            ·
              rfl

theorem cell19_105504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 6].length) (baseStart_105504 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_105504 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_105504 prefixEnd_105504 := by exact prefixLift 105504
  have htrace : WordTrace (prefixWord ++ tailWord_105504) baseStart_105504 baseEnd_105504 := by
    simpa [prefixWord, tailWord_105504, baseEnd_105504] using wordTrace_append hprefix tailTrace_105504
  have hstable : (prefixWord ++ tailWord_105504).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105504).length < 2 ^ (prefixWord ++ tailWord_105504).sum := by decide
  have hdescent : baseEnd_105504 < baseStart_105504 := by decide
  rcases family_descends (prefixWord ++ tailWord_105504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105544 : List Nat := [2, 1, 3, 1, 1, 1, 7, 3]
def baseStart_105544 : Nat := 118140960795 + 105544 * 2 ^ 59
def prefixEnd_105544 : Nat := 4983230072969 + 3 ^ 40 * 105544 * 2
def baseEnd_105544 : Nat := 32115438339697951001255

theorem tailTrace_105544 : CollatzResearch.WordTrace tailWord_105544 prefixEnd_105544 32115438339697951001255 := by
  unfold tailWord_105544
  simp only [CollatzResearch.WordTrace]
  refine ⟨1924752964819794162613843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2566337286426392216818457 1924752964819794162613843)
  ·
    refine ⟨2887129447229691243920765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1924752964819794162613843 2887129447229691243920765)
    ·
      refine ⟨1082673542711134216470287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2887129447229691243920765 1082673542711134216470287)
      ·
        refine ⟨1624010314066701324705431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1082673542711134216470287 1624010314066701324705431)
        ·
          refine ⟨2436015471100051987058147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1624010314066701324705431 2436015471100051987058147)
          ·
            refine ⟨3654023206650077980587221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2436015471100051987058147 3654023206650077980587221)
            ·
              refine ⟨85641168905861202670013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 3654023206650077980587221 85641168905861202670013)
              ·
                refine ⟨32115438339697951001255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85641168905861202670013 32115438339697951001255)
                ·
                  rfl

theorem cell19_105544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 7, 3].length) (baseStart_105544 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_105544 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_105544 prefixEnd_105544 := by exact prefixLift 105544
  have htrace : WordTrace (prefixWord ++ tailWord_105544) baseStart_105544 baseEnd_105544 := by
    simpa [prefixWord, tailWord_105544, baseEnd_105544] using wordTrace_append hprefix tailTrace_105544
  have hstable : (prefixWord ++ tailWord_105544).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105544).length < 2 ^ (prefixWord ++ tailWord_105544).sum := by decide
  have hdescent : baseEnd_105544 < baseStart_105544 := by decide
  rcases family_descends (prefixWord ++ tailWord_105544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105546 : List Nat := [3, 1, 2, 1, 1, 2, 2, 7]
def baseStart_105546 : Nat := 118140960795 + 105546 * 2 ^ 59
def prefixEnd_105546 : Nat := 4983230072969 + 3 ^ 40 * 105546 * 2
def baseEnd_105546 : Nat := 32116046909362538956805

theorem tailTrace_105546 : CollatzResearch.WordTrace tailWord_105546 prefixEnd_105546 32116046909362538956805 := by
  unfold tailWord_105546
  simp only [CollatzResearch.WordTrace]
  refine ⟨962394718908085666700123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2566385917088228444533661 962394718908085666700123)
  ·
    refine ⟨1443592078362128500050185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 962394718908085666700123 1443592078362128500050185)
    ·
      refine ⟨1082694058771596375037639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1443592078362128500050185 1082694058771596375037639)
      ·
        refine ⟨1624041088157394562556459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1082694058771596375037639 1624041088157394562556459)
        ·
          refine ⟨2436061632236091843834689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1624041088157394562556459 2436061632236091843834689)
          ·
            refine ⟨1827046224177068882876017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2436061632236091843834689 1827046224177068882876017)
            ·
              refine ⟨1370284668132801662157013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1827046224177068882876017 1370284668132801662157013)
              ·
                refine ⟨32116046909362538956805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1370284668132801662157013 32116046909362538956805)
                ·
                  rfl

theorem cell19_105546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 7].length) (baseStart_105546 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_105546 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_105546 prefixEnd_105546 := by exact prefixLift 105546
  have htrace : WordTrace (prefixWord ++ tailWord_105546) baseStart_105546 baseEnd_105546 := by
    simpa [prefixWord, tailWord_105546, baseEnd_105546] using wordTrace_append hprefix tailTrace_105546
  have hstable : (prefixWord ++ tailWord_105546).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105546).length < 2 ^ (prefixWord ++ tailWord_105546).sum := by decide
  have hdescent : baseEnd_105546 < baseStart_105546 := by decide
  rcases family_descends (prefixWord ++ tailWord_105546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105584 : List Nat := [2, 1, 1, 1, 5, 1, 2, 6]
def baseStart_105584 : Nat := 118140960795 + 105584 * 2 ^ 59
def prefixEnd_105584 : Nat := 4983230072969 + 3 ^ 40 * 105584 * 2
def baseEnd_105584 : Nat := 32127609732989710112257

theorem tailTrace_105584 : CollatzResearch.WordTrace tailWord_105584 prefixEnd_105584 32127609732989710112257 := by
  unfold tailWord_105584
  simp only [CollatzResearch.WordTrace]
  refine ⟨1925482424747337578341903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2567309899663116771122537 1925482424747337578341903)
  ·
    refine ⟨2888223637121006367512855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1925482424747337578341903 2888223637121006367512855)
    ·
      refine ⟨4332335455681509551269283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2888223637121006367512855 4332335455681509551269283)
      ·
        refine ⟨6498503183522264326903925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4332335455681509551269283 6498503183522264326903925)
        ·
          refine ⟨609234673455212280647243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6498503183522264326903925 609234673455212280647243)
          ·
            refine ⟨913852010182818420970865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 609234673455212280647243 913852010182818420970865)
            ·
              refine ⟨685389007637113815728149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 913852010182818420970865 685389007637113815728149)
              ·
                refine ⟨32127609732989710112257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 685389007637113815728149 32127609732989710112257)
                ·
                  rfl

theorem cell19_105584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 6].length) (baseStart_105584 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_105584 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_105584 prefixEnd_105584 := by exact prefixLift 105584
  have htrace : WordTrace (prefixWord ++ tailWord_105584) baseStart_105584 baseEnd_105584 := by
    simpa [prefixWord, tailWord_105584, baseEnd_105584] using wordTrace_append hprefix tailTrace_105584
  have hstable : (prefixWord ++ tailWord_105584).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105584).length < 2 ^ (prefixWord ++ tailWord_105584).sum := by decide
  have hdescent : baseEnd_105584 < baseStart_105584 := by decide
  rcases family_descends (prefixWord ++ tailWord_105584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105601 : List Nat := [1, 2, 4, 2, 2, 2, 1, 5]
def baseStart_105601 : Nat := 118140960795 + 105601 * 2 ^ 59
def prefixEnd_105601 : Nat := 4983230072969 + 3 ^ 40 * 105601 * 2
def baseEnd_105601 : Nat := 32132782575138707734433

theorem tailTrace_105601 : CollatzResearch.WordTrace tailWord_105601 prefixEnd_105601 32132782575138707734433 := by
  unfold tailWord_105601
  simp only [CollatzResearch.WordTrace]
  refine ⟨3851584890433087060052657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2567723260288724706701771 3851584890433087060052657)
  ·
    refine ⟨2888688667824815295039493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3851584890433087060052657 2888688667824815295039493)
    ·
      refine ⟨541629125217152867819905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2888688667824815295039493 541629125217152867819905)
      ·
        refine ⟨406221843912864650864929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 541629125217152867819905 406221843912864650864929)
        ·
          refine ⟨304666382934648488148697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 406221843912864650864929 304666382934648488148697)
          ·
            refine ⟨228499787200986366111523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 304666382934648488148697 228499787200986366111523)
            ·
              refine ⟨342749680801479549167285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 228499787200986366111523 342749680801479549167285)
              ·
                refine ⟨32132782575138707734433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 342749680801479549167285 32132782575138707734433)
                ·
                  rfl

theorem cell19_105601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 5].length) (baseStart_105601 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_105601 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_105601 prefixEnd_105601 := by exact prefixLift 105601
  have htrace : WordTrace (prefixWord ++ tailWord_105601) baseStart_105601 baseEnd_105601 := by
    simpa [prefixWord, tailWord_105601, baseEnd_105601] using wordTrace_append hprefix tailTrace_105601
  have hstable : (prefixWord ++ tailWord_105601).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105601).length < 2 ^ (prefixWord ++ tailWord_105601).sum := by decide
  have hdescent : baseEnd_105601 < baseStart_105601 := by decide
  rcases family_descends (prefixWord ++ tailWord_105601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105603 : List Nat := [1, 1, 1, 3, 3, 2, 3, 5]
def baseStart_105603 : Nat := 118140960795 + 105603 * 2 ^ 59
def prefixEnd_105603 : Nat := 4983230072969 + 3 ^ 40 * 105603 * 2
def baseEnd_105603 : Nat := 32133391144803295689983

theorem tailTrace_105603 : CollatzResearch.WordTrace tailWord_105603 prefixEnd_105603 32133391144803295689983 := by
  unfold tailWord_105603
  simp only [CollatzResearch.WordTrace]
  refine ⟨3851657836425841401625463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2567771890950560934416975 3851657836425841401625463)
  ·
    refine ⟨5777486754638762102438195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3851657836425841401625463 5777486754638762102438195)
    ·
      refine ⟨8666230131958143153657293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5777486754638762102438195 8666230131958143153657293)
      ·
        refine ⟨3249836299484303682621485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8666230131958143153657293 3249836299484303682621485)
        ·
          refine ⟨1218688612306613880983057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3249836299484303682621485 1218688612306613880983057)
          ·
            refine ⟨914016459229960410737293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1218688612306613880983057 914016459229960410737293)
            ·
              refine ⟨342756172211235154026485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 914016459229960410737293 342756172211235154026485)
              ·
                refine ⟨32133391144803295689983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 342756172211235154026485 32133391144803295689983)
                ·
                  rfl

theorem cell19_105603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 5].length) (baseStart_105603 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_105603 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_105603 prefixEnd_105603 := by exact prefixLift 105603
  have htrace : WordTrace (prefixWord ++ tailWord_105603) baseStart_105603 baseEnd_105603 := by
    simpa [prefixWord, tailWord_105603, baseEnd_105603] using wordTrace_append hprefix tailTrace_105603
  have hstable : (prefixWord ++ tailWord_105603).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105603).length < 2 ^ (prefixWord ++ tailWord_105603).sum := by decide
  have hdescent : baseEnd_105603 < baseStart_105603 := by decide
  rcases family_descends (prefixWord ++ tailWord_105603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105639 : List Nat := [1, 1, 6, 2, 1, 1, 1, 6]
def baseStart_105639 : Nat := 118140960795 + 105639 * 2 ^ 59
def prefixEnd_105639 : Nat := 4983230072969 + 3 ^ 40 * 105639 * 2
def baseEnd_105639 : Nat := 32144345398765878889885

theorem tailTrace_105639 : CollatzResearch.WordTrace tailWord_105639 prefixEnd_105639 32144345398765878889885 := by
  unfold tailWord_105639
  simp only [CollatzResearch.WordTrace]
  refine ⟨3852970864295419549935971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2568647242863613033290647 3852970864295419549935971)
  ·
    refine ⟨5779456296443129324903957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3852970864295419549935971 5779456296443129324903957)
    ·
      refine ⟨270912013895771687104873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 5779456296443129324903957 270912013895771687104873)
      ·
        refine ⟨203184010421828765328655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 270912013895771687104873 203184010421828765328655)
        ·
          refine ⟨304776015632743147992983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203184010421828765328655 304776015632743147992983)
          ·
            refine ⟨457164023449114721989475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 304776015632743147992983 457164023449114721989475)
            ·
              refine ⟨685746035173672082984213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 457164023449114721989475 685746035173672082984213)
              ·
                refine ⟨32144345398765878889885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 685746035173672082984213 32144345398765878889885)
                ·
                  rfl

theorem cell19_105639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 6].length) (baseStart_105639 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_105639 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_105639 prefixEnd_105639 := by exact prefixLift 105639
  have htrace : WordTrace (prefixWord ++ tailWord_105639) baseStart_105639 baseEnd_105639 := by
    simpa [prefixWord, tailWord_105639, baseEnd_105639] using wordTrace_append hprefix tailTrace_105639
  have hstable : (prefixWord ++ tailWord_105639).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105639).length < 2 ^ (prefixWord ++ tailWord_105639).sum := by decide
  have hdescent : baseEnd_105639 < baseStart_105639 := by decide
  rcases family_descends (prefixWord ++ tailWord_105639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105696 : List Nat := [2, 1, 1, 3, 1, 6, 1, 4]
def baseStart_105696 : Nat := 118140960795 + 105696 * 2 ^ 59
def prefixEnd_105696 : Nat := 4983230072969 + 3 ^ 40 * 105696 * 2
def baseEnd_105696 : Nat := 32161689634206635623063

theorem tailTrace_105696 : CollatzResearch.WordTrace tailWord_105696 prefixEnd_105696 32161689634206635623063 := by
  unfold tailWord_105696
  simp only [CollatzResearch.WordTrace]
  refine ⟨1927524912544459142380471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2570033216725945523173961 1927524912544459142380471)
  ·
    refine ⟨2891287368816688713570707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1927524912544459142380471 2891287368816688713570707)
    ·
      refine ⟨4336931053225033070356061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2891287368816688713570707 4336931053225033070356061)
      ·
        refine ⟨1626349144959387401383523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4336931053225033070356061 1626349144959387401383523)
        ·
          refine ⟨2439523717439081102075285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1626349144959387401383523 2439523717439081102075285)
          ·
            refine ⟨114352674254956926659779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 2439523717439081102075285 114352674254956926659779)
            ·
              refine ⟨171529011382435389989669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114352674254956926659779 171529011382435389989669)
              ·
                refine ⟨32161689634206635623063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 171529011382435389989669 32161689634206635623063)
                ·
                  rfl

theorem cell19_105696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 1, 4].length) (baseStart_105696 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_105696 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_105696 prefixEnd_105696 := by exact prefixLift 105696
  have htrace : WordTrace (prefixWord ++ tailWord_105696) baseStart_105696 baseEnd_105696 := by
    simpa [prefixWord, tailWord_105696, baseEnd_105696] using wordTrace_append hprefix tailTrace_105696
  have hstable : (prefixWord ++ tailWord_105696).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105696).length < 2 ^ (prefixWord ++ tailWord_105696).sum := by decide
  have hdescent : baseEnd_105696 < baseStart_105696 := by decide
  rcases family_descends (prefixWord ++ tailWord_105696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105715 : List Nat := [1, 1, 1, 2, 2, 6, 3, 3]
def baseStart_105715 : Nat := 118140960795 + 105715 * 2 ^ 59
def prefixEnd_105715 : Nat := 4983230072969 + 3 ^ 40 * 105715 * 2
def baseEnd_105715 : Nat := 32167471046020221200789

theorem tailTrace_105715 : CollatzResearch.WordTrace tailWord_105715 prefixEnd_105715 32167471046020221200789 := by
  unfold tailWord_105715
  simp only [CollatzResearch.WordTrace]
  refine ⟨3855742812020084529702599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2570495208013389686468399 3855742812020084529702599)
  ·
    refine ⟨5783614218030126794553899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3855742812020084529702599 5783614218030126794553899)
    ·
      refine ⟨8675421327045190191830849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5783614218030126794553899 8675421327045190191830849)
      ·
        refine ⟨6506565995283892643873137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8675421327045190191830849 6506565995283892643873137)
        ·
          refine ⟨4879924496462919482904853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6506565995283892643873137 4879924496462919482904853)
          ·
            refine ⟨228746460771699350761165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 4879924496462919482904853 228746460771699350761165)
            ·
              refine ⟨85779922789387256535437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 228746460771699350761165 85779922789387256535437)
              ·
                refine ⟨32167471046020221200789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85779922789387256535437 32167471046020221200789)
                ·
                  rfl

theorem cell19_105715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 3, 3].length) (baseStart_105715 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_105715 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_105715 prefixEnd_105715 := by exact prefixLift 105715
  have htrace : WordTrace (prefixWord ++ tailWord_105715) baseStart_105715 baseEnd_105715 := by
    simpa [prefixWord, tailWord_105715, baseEnd_105715] using wordTrace_append hprefix tailTrace_105715
  have hstable : (prefixWord ++ tailWord_105715).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105715).length < 2 ^ (prefixWord ++ tailWord_105715).sum := by decide
  have hdescent : baseEnd_105715 < baseStart_105715 := by decide
  rcases family_descends (prefixWord ++ tailWord_105715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105770 : List Nat := [3, 1, 4, 2, 1, 1, 4, 3]
def baseStart_105770 : Nat := 118140960795 + 105770 * 2 ^ 59
def prefixEnd_105770 : Nat := 4983230072969 + 3 ^ 40 * 105770 * 2
def baseEnd_105770 : Nat := 32184206711796389978417

theorem tailTrace_105770 : CollatzResearch.WordTrace tailWord_105770 prefixEnd_105770 32184206711796389978417 := by
  unfold tailWord_105770
  simp only [CollatzResearch.WordTrace]
  refine ⟨964437206705207230738691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2571832551213885948636509 964437206705207230738691)
  ·
    refine ⟨1446655810057810846108037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 964437206705207230738691 1446655810057810846108037)
    ·
      refine ⟨271247964385839533645257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1446655810057810846108037 271247964385839533645257)
      ·
        refine ⟨203435973289379650233943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 271247964385839533645257 203435973289379650233943)
        ·
          refine ⟨305153959934069475350915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203435973289379650233943 305153959934069475350915)
          ·
            refine ⟨457730939901104213026373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 305153959934069475350915 457730939901104213026373)
            ·
              refine ⟨85824551231457039942445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 457730939901104213026373 85824551231457039942445)
              ·
                refine ⟨32184206711796389978417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85824551231457039942445 32184206711796389978417)
                ·
                  rfl

theorem cell19_105770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 4, 3].length) (baseStart_105770 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_105770 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_105770 prefixEnd_105770 := by exact prefixLift 105770
  have htrace : WordTrace (prefixWord ++ tailWord_105770) baseStart_105770 baseEnd_105770 := by
    simpa [prefixWord, tailWord_105770, baseEnd_105770] using wordTrace_append hprefix tailTrace_105770
  have hstable : (prefixWord ++ tailWord_105770).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105770).length < 2 ^ (prefixWord ++ tailWord_105770).sum := by decide
  have hdescent : baseEnd_105770 < baseStart_105770 := by decide
  rcases family_descends (prefixWord ++ tailWord_105770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105789 : List Nat := [1, 4, 1, 5, 1, 2, 5]
def baseStart_105789 : Nat := 118140960795 + 105789 * 2 ^ 59
def prefixEnd_105789 : Nat := 4983230072969 + 3 ^ 40 * 105789 * 2
def baseEnd_105789 : Nat := 10729996041203325185381

theorem tailTrace_105789 : CollatzResearch.WordTrace tailWord_105789 prefixEnd_105789 10729996041203325185381 := by
  unfold tailWord_105789
  simp only [CollatzResearch.WordTrace]
  refine ⟨3858441813751995167896421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2572294542501330111930947 3858441813751995167896421)
  ·
    refine ⟨723457840078499093980579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3858441813751995167896421 723457840078499093980579)
    ·
      refine ⟨1085186760117748640970869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 723457840078499093980579 1085186760117748640970869)
      ·
        refine ⟨101736258761038935091019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1085186760117748640970869 101736258761038935091019)
        ·
          refine ⟨152604388141558402636529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101736258761038935091019 152604388141558402636529)
          ·
            refine ⟨114453291106168801977397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152604388141558402636529 114453291106168801977397)
            ·
              refine ⟨10729996041203325185381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 114453291106168801977397 10729996041203325185381)
              ·
                rfl

theorem cell19_105789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 5].length) (baseStart_105789 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_105789 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_105789 prefixEnd_105789 := by exact prefixLift 105789
  have htrace : WordTrace (prefixWord ++ tailWord_105789) baseStart_105789 baseEnd_105789 := by
    simpa [prefixWord, tailWord_105789, baseEnd_105789] using wordTrace_append hprefix tailTrace_105789
  have hstable : (prefixWord ++ tailWord_105789).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105789).length < 2 ^ (prefixWord ++ tailWord_105789).sum := by decide
  have hdescent : baseEnd_105789 < baseStart_105789 := by decide
  rcases family_descends (prefixWord ++ tailWord_105789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105865 : List Nat := [1, 2, 1, 1, 8, 1, 1, 4]
def baseStart_105865 : Nat := 118140960795 + 105865 * 2 ^ 59
def prefixEnd_105865 : Nat := 4983230072969 + 3 ^ 40 * 105865 * 2
def baseEnd_105865 : Nat := 32213113770864317867047

theorem tailTrace_105865 : CollatzResearch.WordTrace tailWord_105865 prefixEnd_105865 32213113770864317867047 := by
  unfold tailWord_105865
  simp only [CollatzResearch.WordTrace]
  refine ⟨3861213761476660147663049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2574142507651106765108699 3861213761476660147663049)
  ·
    refine ⟨2895910321107495110747287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3861213761476660147663049 2895910321107495110747287)
    ·
      refine ⟨4343865481661242666120931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2895910321107495110747287 4343865481661242666120931)
      ·
        refine ⟨6515798222491863999181397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4343865481661242666120931 6515798222491863999181397)
        ·
          refine ⟨76357010419826531240407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 6515798222491863999181397 76357010419826531240407)
          ·
            refine ⟨114535515629739796860611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76357010419826531240407 114535515629739796860611)
            ·
              refine ⟨171803273444609695290917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114535515629739796860611 171803273444609695290917)
              ·
                refine ⟨32213113770864317867047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 171803273444609695290917 32213113770864317867047)
                ·
                  rfl

theorem cell19_105865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 1, 4].length) (baseStart_105865 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_105865 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_105865 prefixEnd_105865 := by exact prefixLift 105865
  have htrace : WordTrace (prefixWord ++ tailWord_105865) baseStart_105865 baseEnd_105865 := by
    simpa [prefixWord, tailWord_105865, baseEnd_105865] using wordTrace_append hprefix tailTrace_105865
  have hstable : (prefixWord ++ tailWord_105865).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105865).length < 2 ^ (prefixWord ++ tailWord_105865).sum := by decide
  have hdescent : baseEnd_105865 < baseStart_105865 := by decide
  rcases family_descends (prefixWord ++ tailWord_105865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105945 : List Nat := [1, 2, 1, 2, 4, 3, 1, 5]
def baseStart_105945 : Nat := 118140960795 + 105945 * 2 ^ 59
def prefixEnd_105945 : Nat := 4983230072969 + 3 ^ 40 * 105945 * 2
def baseEnd_105945 : Nat := 32237456557447836089051

theorem tailTrace_105945 : CollatzResearch.WordTrace tailWord_105945 prefixEnd_105945 32237456557447836089051 := by
  unfold tailWord_105945
  simp only [CollatzResearch.WordTrace]
  refine ⟨3864131601186833810575289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2576087734124555873716859 3864131601186833810575289)
  ·
    refine ⟨2898098700890125357931467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3864131601186833810575289 2898098700890125357931467)
    ·
      refine ⟨4347148051335188036897201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2898098700890125357931467 4347148051335188036897201)
      ·
        refine ⟨3260361038501391027672901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4347148051335188036897201 3260361038501391027672901)
        ·
          refine ⟨611317694719010817688669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3260361038501391027672901 611317694719010817688669)
          ·
            refine ⟨229244135519629056633251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 611317694719010817688669 229244135519629056633251)
            ·
              refine ⟨343866203279443584949877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 229244135519629056633251 343866203279443584949877)
              ·
                refine ⟨32237456557447836089051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 343866203279443584949877 32237456557447836089051)
                ·
                  rfl

theorem cell19_105945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 5].length) (baseStart_105945 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_105945 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_105945 prefixEnd_105945 := by exact prefixLift 105945
  have htrace : WordTrace (prefixWord ++ tailWord_105945) baseStart_105945 baseEnd_105945 := by
    simpa [prefixWord, tailWord_105945, baseEnd_105945] using wordTrace_append hprefix tailTrace_105945
  have hstable : (prefixWord ++ tailWord_105945).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105945).length < 2 ^ (prefixWord ++ tailWord_105945).sum := by decide
  have hdescent : baseEnd_105945 < baseStart_105945 := by decide
  rcases family_descends (prefixWord ++ tailWord_105945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105962 : List Nat := [3, 1, 3, 1, 4, 2, 5]
def baseStart_105962 : Nat := 118140960795 + 105962 * 2 ^ 59
def prefixEnd_105962 : Nat := 4983230072969 + 3 ^ 40 * 105962 * 2
def baseEnd_105962 : Nat := 10747543133198944570409

theorem tailTrace_105962 : CollatzResearch.WordTrace tailWord_105962 prefixEnd_105962 10747543133198944570409 := by
  unfold tailWord_105962
  simp only [CollatzResearch.WordTrace]
  refine ⟨966187910531311428486035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2576501094750163809296093 966187910531311428486035)
  ·
    refine ⟨1449281865796967142729053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 966187910531311428486035 1449281865796967142729053)
    ·
      refine ⟨543480699673862678523395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1449281865796967142729053 543480699673862678523395)
      ·
        refine ⟨815221049510794017785093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 543480699673862678523395 815221049510794017785093)
        ·
          refine ⟨152853946783273878334705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 815221049510794017785093 152853946783273878334705)
          ·
            refine ⟨114640460087455408751029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152853946783273878334705 114640460087455408751029)
            ·
              refine ⟨10747543133198944570409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 114640460087455408751029 10747543133198944570409)
              ·
                rfl

theorem cell19_105962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 5].length) (baseStart_105962 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_105962 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_105962 prefixEnd_105962 := by exact prefixLift 105962
  have htrace : WordTrace (prefixWord ++ tailWord_105962) baseStart_105962 baseEnd_105962 := by
    simpa [prefixWord, tailWord_105962, baseEnd_105962] using wordTrace_append hprefix tailTrace_105962
  have hstable : (prefixWord ++ tailWord_105962).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105962).length < 2 ^ (prefixWord ++ tailWord_105962).sum := by decide
  have hdescent : baseEnd_105962 < baseStart_105962 := by decide
  rcases family_descends (prefixWord ++ tailWord_105962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106040 : List Nat := [2, 1, 2, 1, 4, 2, 3, 4]
def baseStart_106040 : Nat := 118140960795 + 106040 * 2 ^ 59
def prefixEnd_106040 : Nat := 4983230072969 + 3 ^ 40 * 106040 * 2
def baseEnd_106040 : Nat := 32266363616515763977681

theorem tailTrace_106040 : CollatzResearch.WordTrace tailWord_106040 prefixEnd_106040 32266363616515763977681 := by
  unfold tailWord_106040
  simp only [CollatzResearch.WordTrace]
  refine ⟨1933798267921332517641787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2578397690561776690189049 1933798267921332517641787)
  ·
    refine ⟨2900697401881998776462681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1933798267921332517641787 2900697401881998776462681)
    ·
      refine ⟨2175523051411499082347011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2900697401881998776462681 2175523051411499082347011)
      ·
        refine ⟨3263284577117248623520517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2175523051411499082347011 3263284577117248623520517)
        ·
          refine ⟨611865858209484116910097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3263284577117248623520517 611865858209484116910097)
          ·
            refine ⟨458899393657113087682573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 611865858209484116910097 458899393657113087682573)
            ·
              refine ⟨172087272621417407880965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 458899393657113087682573 172087272621417407880965)
              ·
                refine ⟨32266363616515763977681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 172087272621417407880965 32266363616515763977681)
                ·
                  rfl

theorem cell19_106040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 3, 4].length) (baseStart_106040 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_106040 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_106040 prefixEnd_106040 := by exact prefixLift 106040
  have htrace : WordTrace (prefixWord ++ tailWord_106040) baseStart_106040 baseEnd_106040 := by
    simpa [prefixWord, tailWord_106040, baseEnd_106040] using wordTrace_append hprefix tailTrace_106040
  have hstable : (prefixWord ++ tailWord_106040).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106040).length < 2 ^ (prefixWord ++ tailWord_106040).sum := by decide
  have hdescent : baseEnd_106040 < baseStart_106040 := by decide
  rcases family_descends (prefixWord ++ tailWord_106040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106135 : List Nat := [1, 1, 3, 3, 2, 4, 5]
def baseStart_106135 : Nat := 118140960795 + 106135 * 2 ^ 59
def prefixEnd_106135 : Nat := 4983230072969 + 3 ^ 40 * 106135 * 2
def baseEnd_106135 : Nat := 10765090225194563955437

theorem tailTrace_106135 : CollatzResearch.WordTrace tailWord_106135 prefixEnd_106135 10765090225194563955437 := by
  unfold tailWord_106135
  simp only [CollatzResearch.WordTrace]
  refine ⟨3871061470498496259991859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2580707646998997506661239 3871061470498496259991859)
  ·
    refine ⟨5806592205747744389987789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3871061470498496259991859 5806592205747744389987789)
    ·
      refine ⟨2177472077155404146245421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5806592205747744389987789 2177472077155404146245421)
      ·
        refine ⟨816552028933276554842033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2177472077155404146245421 816552028933276554842033)
        ·
          refine ⟨612414021699957416131525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 816552028933276554842033 612414021699957416131525)
          ·
            refine ⟨114827629068742015524661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 612414021699957416131525 114827629068742015524661)
            ·
              refine ⟨10765090225194563955437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 114827629068742015524661 10765090225194563955437)
              ·
                rfl

theorem cell19_106135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 5].length) (baseStart_106135 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_106135 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_106135 prefixEnd_106135 := by exact prefixLift 106135
  have htrace : WordTrace (prefixWord ++ tailWord_106135) baseStart_106135 baseEnd_106135 := by
    simpa [prefixWord, tailWord_106135, baseEnd_106135] using wordTrace_append hprefix tailTrace_106135
  have hstable : (prefixWord ++ tailWord_106135).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106135).length < 2 ^ (prefixWord ++ tailWord_106135).sum := by decide
  have hdescent : baseEnd_106135 < baseStart_106135 := by decide
  rcases family_descends (prefixWord ++ tailWord_106135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106175 : List Nat := [1, 1, 2, 2, 2, 3, 1, 7]
def baseStart_106175 : Nat := 118140960795 + 106175 * 2 ^ 59
def prefixEnd_106175 : Nat := 4983230072969 + 3 ^ 40 * 106175 * 2
def baseEnd_106175 : Nat := 32307442068875450977313

theorem tailTrace_106175 : CollatzResearch.WordTrace tailWord_106175 prefixEnd_106175 32307442068875450977313 := by
  unfold tailWord_106175
  simp only [CollatzResearch.WordTrace]
  refine ⟨3872520390353583091447979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2581680260235722060965319 3872520390353583091447979)
  ·
    refine ⟨5808780585530374637171969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3872520390353583091447979 5808780585530374637171969)
    ·
      refine ⟨4356585439147780977878977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5808780585530374637171969 4356585439147780977878977)
      ·
        refine ⟨3267439079360835733409233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4356585439147780977878977 3267439079360835733409233)
        ·
          refine ⟨2450579309520626800056925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3267439079360835733409233 2450579309520626800056925)
          ·
            refine ⟨918967241070235050021347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2450579309520626800056925 918967241070235050021347)
            ·
              refine ⟨1378450861605352575032021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 918967241070235050021347 1378450861605352575032021)
              ·
                refine ⟨32307442068875450977313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1378450861605352575032021 32307442068875450977313)
                ·
                  rfl

theorem cell19_106175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 7].length) (baseStart_106175 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_106175 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_106175 prefixEnd_106175 := by exact prefixLift 106175
  have htrace : WordTrace (prefixWord ++ tailWord_106175) baseStart_106175 baseEnd_106175 := by
    simpa [prefixWord, tailWord_106175, baseEnd_106175] using wordTrace_append hprefix tailTrace_106175
  have hstable : (prefixWord ++ tailWord_106175).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106175).length < 2 ^ (prefixWord ++ tailWord_106175).sum := by decide
  have hdescent : baseEnd_106175 < baseStart_106175 := by decide
  rcases family_descends (prefixWord ++ tailWord_106175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106205 : List Nat := [1, 4, 3, 3, 2, 1, 1, 4]
def baseStart_106205 : Nat := 118140960795 + 106205 * 2 ^ 59
def prefixEnd_106205 : Nat := 4983230072969 + 3 ^ 40 * 106205 * 2
def baseEnd_106205 : Nat := 32316570613844270310565

theorem tailTrace_106205 : CollatzResearch.WordTrace tailWord_106205 prefixEnd_106205 32316570613844270310565 := by
  unfold tailWord_106205
  simp only [CollatzResearch.WordTrace]
  refine ⟨3873614580244898215040069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2582409720163265476693379 3873614580244898215040069)
  ·
    refine ⟨726302733795918415320013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3873614580244898215040069 726302733795918415320013)
    ·
      refine ⟨272363525173469405745005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 726302733795918415320013 272363525173469405745005)
      ·
        refine ⟨102136321940051027154377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 272363525173469405745005 102136321940051027154377)
        ·
          refine ⟨76602241455038270365783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102136321940051027154377 76602241455038270365783)
          ·
            refine ⟨114903362182557405548675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76602241455038270365783 114903362182557405548675)
            ·
              refine ⟨172355043273836108323013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114903362182557405548675 172355043273836108323013)
              ·
                refine ⟨32316570613844270310565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 172355043273836108323013 32316570613844270310565)
                ·
                  rfl

theorem cell19_106205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 1, 4].length) (baseStart_106205 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_106205 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_106205 prefixEnd_106205 := by exact prefixLift 106205
  have htrace : WordTrace (prefixWord ++ tailWord_106205) baseStart_106205 baseEnd_106205 := by
    simpa [prefixWord, tailWord_106205, baseEnd_106205] using wordTrace_append hprefix tailTrace_106205
  have hstable : (prefixWord ++ tailWord_106205).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106205).length < 2 ^ (prefixWord ++ tailWord_106205).sum := by decide
  have hdescent : baseEnd_106205 < baseStart_106205 := by decide
  rcases family_descends (prefixWord ++ tailWord_106205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106209 : List Nat := [1, 2, 3, 1, 5, 2, 1, 4]
def baseStart_106209 : Nat := 118140960795 + 106209 * 2 ^ 59
def prefixEnd_106209 : Nat := 4983230072969 + 3 ^ 40 * 106209 * 2
def baseEnd_106209 : Nat := 32317787753173446221665

theorem tailTrace_106209 : CollatzResearch.WordTrace tailWord_106209 prefixEnd_106209 32317787753173446221665 := by
  unfold tailWord_106209
  simp only [CollatzResearch.WordTrace]
  refine ⟨3873760472230406898185681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2582506981486937932123787 3873760472230406898185681)
  ·
    refine ⟨2905320354172805173639261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3873760472230406898185681 2905320354172805173639261)
    ·
      refine ⟨1089495132814801940114723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2905320354172805173639261 1089495132814801940114723)
      ·
        refine ⟨1634242699222202910172085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1089495132814801940114723 1634242699222202910172085)
        ·
          refine ⟨153210253052081522828633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1634242699222202910172085 153210253052081522828633)
          ·
            refine ⟨114907689789061142121475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153210253052081522828633 114907689789061142121475)
            ·
              refine ⟨172361534683591713182213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114907689789061142121475 172361534683591713182213)
              ·
                refine ⟨32317787753173446221665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 172361534683591713182213 32317787753173446221665)
                ·
                  rfl

theorem cell19_106209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 1, 4].length) (baseStart_106209 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_106209 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_106209 prefixEnd_106209 := by exact prefixLift 106209
  have htrace : WordTrace (prefixWord ++ tailWord_106209) baseStart_106209 baseEnd_106209 := by
    simpa [prefixWord, tailWord_106209, baseEnd_106209] using wordTrace_append hprefix tailTrace_106209
  have hstable : (prefixWord ++ tailWord_106209).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106209).length < 2 ^ (prefixWord ++ tailWord_106209).sum := by decide
  have hdescent : baseEnd_106209 < baseStart_106209 := by decide
  rcases family_descends (prefixWord ++ tailWord_106209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106325 : List Nat := [1, 3, 2, 2, 2, 3, 2, 4]
def baseStart_106325 : Nat := 118140960795 + 106325 * 2 ^ 59
def prefixEnd_106325 : Nat := 4983230072969 + 3 ^ 40 * 106325 * 2
def baseEnd_106325 : Nat := 32353084793719547643571

theorem tailTrace_106325 : CollatzResearch.WordTrace tailWord_106325 prefixEnd_106325 32353084793719547643571 := by
  unfold tailWord_106325
  simp only [CollatzResearch.WordTrace]
  refine ⟨3877991339810158709408429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2585327559873439139605619 3877991339810158709408429)
  ·
    refine ⟨1454246752428809516028161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3877991339810158709408429 1454246752428809516028161)
    ·
      refine ⟨1090685064321607137021121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1454246752428809516028161 1090685064321607137021121)
      ·
        refine ⟨818013798241205352765841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1090685064321607137021121 818013798241205352765841)
        ·
          refine ⟨613510348680904014574381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 818013798241205352765841 613510348680904014574381)
          ·
            refine ⟨230066380755339005465393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 613510348680904014574381 230066380755339005465393)
            ·
              refine ⟨172549785566504254099045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 230066380755339005465393 172549785566504254099045)
              ·
                refine ⟨32353084793719547643571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 172549785566504254099045 32353084793719547643571)
                ·
                  rfl

theorem cell19_106325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 2, 4].length) (baseStart_106325 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_106325 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_106325 prefixEnd_106325 := by exact prefixLift 106325
  have htrace : WordTrace (prefixWord ++ tailWord_106325) baseStart_106325 baseEnd_106325 := by
    simpa [prefixWord, tailWord_106325, baseEnd_106325] using wordTrace_append hprefix tailTrace_106325
  have hstable : (prefixWord ++ tailWord_106325).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106325).length < 2 ^ (prefixWord ++ tailWord_106325).sum := by decide
  have hdescent : baseEnd_106325 < baseStart_106325 := by decide
  rcases family_descends (prefixWord ++ tailWord_106325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106378 : List Nat := [3, 1, 2, 4, 3, 1, 1, 4]
def baseStart_106378 : Nat := 118140960795 + 106378 * 2 ^ 59
def prefixEnd_106378 : Nat := 4983230072969 + 3 ^ 40 * 106378 * 2
def baseEnd_106378 : Nat := 32369211889831128465649

theorem tailTrace_106378 : CollatzResearch.WordTrace tailWord_106378 prefixEnd_106378 32369211889831128465649 := by
  unfold tailWord_106378
  simp only [CollatzResearch.WordTrace]
  refine ⟨969981102154537190271947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2586616272412099174058525 969981102154537190271947)
  ·
    refine ⟨1454971653231805785407921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 969981102154537190271947 1454971653231805785407921)
    ·
      refine ⟨1091228739923854339055941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1454971653231805785407921 1091228739923854339055941)
      ·
        refine ⟨204605388735722688572989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1091228739923854339055941 204605388735722688572989)
        ·
          refine ⟨76727020775896008214871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 204605388735722688572989 76727020775896008214871)
          ·
            refine ⟨115090531163844012322307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76727020775896008214871 115090531163844012322307)
            ·
              refine ⟨172635796745766018483461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115090531163844012322307 172635796745766018483461)
              ·
                refine ⟨32369211889831128465649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 172635796745766018483461 32369211889831128465649)
                ·
                  rfl

theorem cell19_106378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 1, 4].length) (baseStart_106378 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_106378 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_106378 prefixEnd_106378 := by exact prefixLift 106378
  have htrace : WordTrace (prefixWord ++ tailWord_106378) baseStart_106378 baseEnd_106378 := by
    simpa [prefixWord, tailWord_106378, baseEnd_106378] using wordTrace_append hprefix tailTrace_106378
  have hstable : (prefixWord ++ tailWord_106378).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106378).length < 2 ^ (prefixWord ++ tailWord_106378).sum := by decide
  have hdescent : baseEnd_106378 < baseStart_106378 := by decide
  rcases family_descends (prefixWord ++ tailWord_106378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106399 : List Nat := [1, 1, 2, 5, 3, 1, 3, 3]
def baseStart_106399 : Nat := 118140960795 + 106399 * 2 ^ 59
def prefixEnd_106399 : Nat := 4983230072969 + 3 ^ 40 * 106399 * 2
def baseEnd_106399 : Nat := 32375601871309301998925

theorem tailTrace_106399 : CollatzResearch.WordTrace tailWord_106399 prefixEnd_106399 32375601871309301998925 := by
  unfold tailWord_106399
  simp only [CollatzResearch.WordTrace]
  refine ⟨3880690341542069347602251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2587126894361379565068167 3880690341542069347602251)
  ·
    refine ⟨5821035512313104021403377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3880690341542069347602251 5821035512313104021403377)
    ·
      refine ⟨4365776634234828016052533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5821035512313104021403377 4365776634234828016052533)
      ·
        refine ⟨409291559459515126504925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4365776634234828016052533 409291559459515126504925)
        ·
          refine ⟨153484334797318172439347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 409291559459515126504925 153484334797318172439347)
          ·
            refine ⟨230226502195977258659021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153484334797318172439347 230226502195977258659021)
            ·
              refine ⟨86334938323491471997133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 230226502195977258659021 86334938323491471997133)
              ·
                refine ⟨32375601871309301998925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86334938323491471997133 32375601871309301998925)
                ·
                  rfl

theorem cell19_106399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 3, 3].length) (baseStart_106399 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_106399 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_106399 prefixEnd_106399 := by exact prefixLift 106399
  have htrace : WordTrace (prefixWord ++ tailWord_106399) baseStart_106399 baseEnd_106399 := by
    simpa [prefixWord, tailWord_106399, baseEnd_106399] using wordTrace_append hprefix tailTrace_106399
  have hstable : (prefixWord ++ tailWord_106399).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106399).length < 2 ^ (prefixWord ++ tailWord_106399).sum := by decide
  have hdescent : baseEnd_106399 < baseStart_106399 := by decide
  rcases family_descends (prefixWord ++ tailWord_106399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106458 : List Nat := [3, 1, 1, 2, 5, 1, 1, 5]
def baseStart_106458 : Nat := 118140960795 + 106458 * 2 ^ 59
def prefixEnd_106458 : Nat := 4983230072969 + 3 ^ 40 * 106458 * 2
def baseEnd_106458 : Nat := 32393554676414646687653

theorem tailTrace_106458 : CollatzResearch.WordTrace tailWord_106458 prefixEnd_106458 32393554676414646687653 := by
  unfold tailWord_106458
  simp only [CollatzResearch.WordTrace]
  refine ⟨970710562082080606000007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2588561498885548282666685 970710562082080606000007)
  ·
    refine ⟨1456065843123120909000011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 970710562082080606000007 1456065843123120909000011)
    ·
      refine ⟨2184098764684681363500017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1456065843123120909000011 2184098764684681363500017)
      ·
        refine ⟨1638074073513511022625013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2184098764684681363500017 1638074073513511022625013)
        ·
          refine ⟨153569444391891658371095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1638074073513511022625013 153569444391891658371095)
          ·
            refine ⟨230354166587837487556643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153569444391891658371095 230354166587837487556643)
            ·
              refine ⟨345531249881756231334965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 230354166587837487556643 345531249881756231334965)
              ·
                refine ⟨32393554676414646687653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 345531249881756231334965 32393554676414646687653)
                ·
                  rfl

theorem cell19_106458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 5].length) (baseStart_106458 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_106458 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_106458 prefixEnd_106458 := by exact prefixLift 106458
  have htrace : WordTrace (prefixWord ++ tailWord_106458) baseStart_106458 baseEnd_106458 := by
    simpa [prefixWord, tailWord_106458, baseEnd_106458] using wordTrace_append hprefix tailTrace_106458
  have hstable : (prefixWord ++ tailWord_106458).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106458).length < 2 ^ (prefixWord ++ tailWord_106458).sum := by decide
  have hdescent : baseEnd_106458 < baseStart_106458 := by decide
  rcases family_descends (prefixWord ++ tailWord_106458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106494 : List Nat := [4, 2, 2, 2, 1, 2, 2, 4]
def baseStart_106494 : Nat := 118140960795 + 106494 * 2 ^ 59
def prefixEnd_106494 : Nat := 4983230072969 + 3 ^ 40 * 106494 * 2
def baseEnd_106494 : Nat := 32404508930377229887555

theorem tailTrace_106494 : CollatzResearch.WordTrace tailWord_106494 prefixEnd_106494 32404508930377229887555 := by
  unfold tailWord_106494
  simp only [CollatzResearch.WordTrace]
  refine ⟨485519409524737571538817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2589436850798600381540357 485519409524737571538817)
  ·
    refine ⟨364139557143553178654113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 485519409524737571538817 364139557143553178654113)
    ·
      refine ⟨273104667857664883990585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 364139557143553178654113 273104667857664883990585)
      ·
        refine ⟨204828500893248662992939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 273104667857664883990585 204828500893248662992939)
        ·
          refine ⟨307242751339872994489409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204828500893248662992939 307242751339872994489409)
          ·
            refine ⟨230432063504904745867057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 307242751339872994489409 230432063504904745867057)
            ·
              refine ⟨172824047628678559400293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 230432063504904745867057 172824047628678559400293)
              ·
                refine ⟨32404508930377229887555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 172824047628678559400293 32404508930377229887555)
                ·
                  rfl

theorem cell19_106494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 2, 4].length) (baseStart_106494 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_106494 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_106494 prefixEnd_106494 := by exact prefixLift 106494
  have htrace : WordTrace (prefixWord ++ tailWord_106494) baseStart_106494 baseEnd_106494 := by
    simpa [prefixWord, tailWord_106494, baseEnd_106494] using wordTrace_append hprefix tailTrace_106494
  have hstable : (prefixWord ++ tailWord_106494).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106494).length < 2 ^ (prefixWord ++ tailWord_106494).sum := by decide
  have hdescent : baseEnd_106494 < baseStart_106494 := by decide
  rcases family_descends (prefixWord ++ tailWord_106494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106625 : List Nat := [1, 2, 4, 2, 4, 1, 2, 3]
def baseStart_106625 : Nat := 118140960795 + 106625 * 2 ^ 59
def prefixEnd_106625 : Nat := 4983230072969 + 3 ^ 40 * 106625 * 2
def baseEnd_106625 : Nat := 32444370243407740976087

theorem tailTrace_106625 : CollatzResearch.WordTrace tailWord_106625 prefixEnd_106625 32444370243407740976087 := by
  unfold tailWord_106625
  simp only [CollatzResearch.WordTrace]
  refine ⟨3888933238723309945329329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2592622159148873296886219 3888933238723309945329329)
  ·
    refine ⟨2916699929042482458996997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3888933238723309945329329 2916699929042482458996997)
    ·
      refine ⟨546881236695465461061937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2916699929042482458996997 546881236695465461061937)
      ·
        refine ⟨410160927521599095796453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 546881236695465461061937 410160927521599095796453)
        ·
          refine ⟨76905173910299830461835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 410160927521599095796453 76905173910299830461835)
          ·
            refine ⟨115357760865449745692753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76905173910299830461835 115357760865449745692753)
            ·
              refine ⟨86518320649087309269565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115357760865449745692753 86518320649087309269565)
              ·
                refine ⟨32444370243407740976087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86518320649087309269565 32444370243407740976087)
                ·
                  rfl

theorem cell19_106625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 2, 3].length) (baseStart_106625 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_106625 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_106625 prefixEnd_106625 := by exact prefixLift 106625
  have htrace : WordTrace (prefixWord ++ tailWord_106625) baseStart_106625 baseEnd_106625 := by
    simpa [prefixWord, tailWord_106625, baseEnd_106625] using wordTrace_append hprefix tailTrace_106625
  have hstable : (prefixWord ++ tailWord_106625).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106625).length < 2 ^ (prefixWord ++ tailWord_106625).sum := by decide
  have hdescent : baseEnd_106625 < baseStart_106625 := by decide
  rcases family_descends (prefixWord ++ tailWord_106625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106629 : List Nat := [1, 3, 1, 1, 5, 1, 4, 3]
def baseStart_106629 : Nat := 118140960795 + 106629 * 2 ^ 59
def prefixEnd_106629 : Nat := 4983230072969 + 3 ^ 40 * 106629 * 2
def baseEnd_106629 : Nat := 32445587382736916887187

theorem tailTrace_106629 : CollatzResearch.WordTrace tailWord_106629 prefixEnd_106629 32445587382736916887187 := by
  unfold tailWord_106629
  simp only [CollatzResearch.WordTrace]
  refine ⟨3889079130708818628474941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2592719420472545752316627 3889079130708818628474941)
  ·
    refine ⟨1458404674015806985678103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3889079130708818628474941 1458404674015806985678103)
    ·
      refine ⟨2187607011023710478517155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1458404674015806985678103 2187607011023710478517155)
      ·
        refine ⟨3281410516535565717775733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2187607011023710478517155 3281410516535565717775733)
        ·
          refine ⟨307632235925209286041475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3281410516535565717775733 307632235925209286041475)
          ·
            refine ⟨461448353887813929062213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 307632235925209286041475 461448353887813929062213)
            ·
              refine ⟨86521566353965111699165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 461448353887813929062213 86521566353965111699165)
              ·
                refine ⟨32445587382736916887187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86521566353965111699165 32445587382736916887187)
                ·
                  rfl

theorem cell19_106629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 4, 3].length) (baseStart_106629 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_106629 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_106629 prefixEnd_106629 := by exact prefixLift 106629
  have htrace : WordTrace (prefixWord ++ tailWord_106629) baseStart_106629 baseEnd_106629 := by
    simpa [prefixWord, tailWord_106629, baseEnd_106629] using wordTrace_append hprefix tailTrace_106629
  have hstable : (prefixWord ++ tailWord_106629).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106629).length < 2 ^ (prefixWord ++ tailWord_106629).sum := by decide
  have hdescent : baseEnd_106629 < baseStart_106629 := by decide
  rcases family_descends (prefixWord ++ tailWord_106629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106644 : List Nat := [2, 4, 2, 3, 2, 1, 5]
def baseStart_106644 : Nat := 118140960795 + 106644 * 2 ^ 59
def prefixEnd_106644 : Nat := 4983230072969 + 3 ^ 40 * 106644 * 2
def baseEnd_106644 : Nat := 10816717218407108851271

theorem tailTrace_106644 : CollatzResearch.WordTrace tailWord_106644 prefixEnd_106644 10816717218407108851271 := by
  unfold tailWord_106644
  simp only [CollatzResearch.WordTrace]
  refine ⟨1944813112827238095135493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2593084150436317460180657 1944813112827238095135493)
  ·
    refine ⟨364652458655107142837905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1944813112827238095135493 364652458655107142837905)
    ·
      refine ⟨273489343991330357128429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 364652458655107142837905 273489343991330357128429)
      ·
        refine ⟨102558503996748883923161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 273489343991330357128429 102558503996748883923161)
        ·
          refine ⟨76918877997561662942371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102558503996748883923161 76918877997561662942371)
          ·
            refine ⟨115378316996342494413557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76918877997561662942371 115378316996342494413557)
            ·
              refine ⟨10816717218407108851271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 115378316996342494413557 10816717218407108851271)
              ·
                rfl

theorem cell19_106644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 5].length) (baseStart_106644 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_106644 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_106644 prefixEnd_106644 := by exact prefixLift 106644
  have htrace : WordTrace (prefixWord ++ tailWord_106644) baseStart_106644 baseEnd_106644 := by
    simpa [prefixWord, tailWord_106644, baseEnd_106644] using wordTrace_append hprefix tailTrace_106644
  have hstable : (prefixWord ++ tailWord_106644).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106644).length < 2 ^ (prefixWord ++ tailWord_106644).sum := by decide
  have hdescent : baseEnd_106644 < baseStart_106644 := by decide
  rcases family_descends (prefixWord ++ tailWord_106644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106648 : List Nat := [2, 1, 2, 4, 3, 2, 5]
def baseStart_106648 : Nat := 118140960795 + 106648 * 2 ^ 59
def prefixEnd_106648 : Nat := 4983230072969 + 3 ^ 40 * 106648 * 2
def baseEnd_106648 : Nat := 10817122931516834154971

theorem tailTrace_106648 : CollatzResearch.WordTrace tailWord_106648 prefixEnd_106648 10817122931516834154971 := by
  unfold tailWord_106648
  simp only [CollatzResearch.WordTrace]
  refine ⟨1944886058819992436708299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2593181411759989915611065 1944886058819992436708299)
  ·
    refine ⟨2917329088229988655062449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1944886058819992436708299 2917329088229988655062449)
    ·
      refine ⟨2187996816172491491296837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2917329088229988655062449 2187996816172491491296837)
      ·
        refine ⟨410249403032342154618157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2187996816172491491296837 410249403032342154618157)
        ·
          refine ⟨153843526137128307981809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 410249403032342154618157 153843526137128307981809)
          ·
            refine ⟨115382644602846230986357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153843526137128307981809 115382644602846230986357)
            ·
              refine ⟨10817122931516834154971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 115382644602846230986357 10817122931516834154971)
              ·
                rfl

theorem cell19_106648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 5].length) (baseStart_106648 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_106648 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_106648 prefixEnd_106648 := by exact prefixLift 106648
  have htrace : WordTrace (prefixWord ++ tailWord_106648) baseStart_106648 baseEnd_106648 := by
    simpa [prefixWord, tailWord_106648, baseEnd_106648] using wordTrace_append hprefix tailTrace_106648
  have hstable : (prefixWord ++ tailWord_106648).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106648).length < 2 ^ (prefixWord ++ tailWord_106648).sum := by decide
  have hdescent : baseEnd_106648 < baseStart_106648 := by decide
  rcases family_descends (prefixWord ++ tailWord_106648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106688 : List Nat := [2, 1, 1, 2, 5, 1, 2, 5]
def baseStart_106688 : Nat := 118140960795 + 106688 * 2 ^ 59
def prefixEnd_106688 : Nat := 4983230072969 + 3 ^ 40 * 106688 * 2
def baseEnd_106688 : Nat := 32463540187842261575915

theorem tailTrace_106688 : CollatzResearch.WordTrace tailWord_106688 prefixEnd_106688 32463540187842261575915 := by
  unfold tailWord_106688
  simp only [CollatzResearch.WordTrace]
  refine ⟨1945615518747535852436359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2594154024996714469915145 1945615518747535852436359)
  ·
    refine ⟨2918423278121303778654539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1945615518747535852436359 2918423278121303778654539)
    ·
      refine ⟨4377634917181955667981809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2918423278121303778654539 4377634917181955667981809)
      ·
        refine ⟨3283226187886466750986357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4377634917181955667981809 3283226187886466750986357)
        ·
          refine ⟨307802455114356257904971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3283226187886466750986357 307802455114356257904971)
          ·
            refine ⟨461703682671534386857457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 307802455114356257904971 461703682671534386857457)
            ·
              refine ⟨346277762003650790143093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 461703682671534386857457 346277762003650790143093)
              ·
                refine ⟨32463540187842261575915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 346277762003650790143093 32463540187842261575915)
                ·
                  rfl

theorem cell19_106688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 5].length) (baseStart_106688 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_106688 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_106688 prefixEnd_106688 := by exact prefixLift 106688
  have htrace : WordTrace (prefixWord ++ tailWord_106688) baseStart_106688 baseEnd_106688 := by
    simpa [prefixWord, tailWord_106688, baseEnd_106688] using wordTrace_append hprefix tailTrace_106688
  have hstable : (prefixWord ++ tailWord_106688).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106688).length < 2 ^ (prefixWord ++ tailWord_106688).sum := by decide
  have hdescent : baseEnd_106688 < baseStart_106688 := by decide
  rcases family_descends (prefixWord ++ tailWord_106688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106798 : List Nat := [4, 1, 3, 3, 1, 1, 1, 5]
def baseStart_106798 : Nat := 118140960795 + 106798 * 2 ^ 59
def prefixEnd_106798 : Nat := 4983230072969 + 3 ^ 40 * 106798 * 2
def baseEnd_106798 : Nat := 32497011519394599131171

theorem tailTrace_106798 : CollatzResearch.WordTrace tailWord_106798 prefixEnd_106798 32497011519394599131171 := by
  unfold tailWord_106798
  simp only [CollatzResearch.WordTrace]
  refine ⟨486905383387070061422131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2596828711397706994251365 486905383387070061422131)
  ·
    refine ⟨730358075080605092133197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 486905383387070061422131 730358075080605092133197)
    ·
      refine ⟨273884278155226909549949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 730358075080605092133197 273884278155226909549949)
      ·
        refine ⟨102706604308210091081231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 273884278155226909549949 102706604308210091081231)
        ·
          refine ⟨154059906462315136621847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102706604308210091081231 154059906462315136621847)
          ·
            refine ⟨231089859693472704932771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154059906462315136621847 231089859693472704932771)
            ·
              refine ⟨346634789540209057399157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 231089859693472704932771 346634789540209057399157)
              ·
                refine ⟨32497011519394599131171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 346634789540209057399157 32497011519394599131171)
                ·
                  rfl

theorem cell19_106798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 5].length) (baseStart_106798 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_106798 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_106798 prefixEnd_106798 := by exact prefixLift 106798
  have htrace : WordTrace (prefixWord ++ tailWord_106798) baseStart_106798 baseEnd_106798 := by
    simpa [prefixWord, tailWord_106798, baseEnd_106798] using wordTrace_append hprefix tailTrace_106798
  have hstable : (prefixWord ++ tailWord_106798).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106798).length < 2 ^ (prefixWord ++ tailWord_106798).sum := by decide
  have hdescent : baseEnd_106798 < baseStart_106798 := by decide
  rcases family_descends (prefixWord ++ tailWord_106798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106817 : List Nat := [1, 2, 5, 2, 3, 1, 5]
def baseStart_106817 : Nat := 118140960795 + 106817 * 2 ^ 59
def prefixEnd_106817 : Nat := 4983230072969 + 3 ^ 40 * 106817 * 2
def baseEnd_106817 : Nat := 10834264310402728236299

theorem tailTrace_106817 : CollatzResearch.WordTrace tailWord_106817 prefixEnd_106817 10834264310402728236299 := by
  unfold tailWord_106817
  simp only [CollatzResearch.WordTrace]
  refine ⟨3895936054027726736318705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2597290702685151157545803 3895936054027726736318705)
  ·
    refine ⟨2921952040520795052239029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3895936054027726736318705 2921952040520795052239029)
    ·
      refine ⟨273933003798824536147409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2921952040520795052239029 273933003798824536147409)
      ·
        refine ⟨205449752849118402110557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 273933003798824536147409 205449752849118402110557)
        ·
          refine ⟨77043657318419400791459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 205449752849118402110557 77043657318419400791459)
          ·
            refine ⟨115565485977629101187189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77043657318419400791459 115565485977629101187189)
            ·
              refine ⟨10834264310402728236299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 115565485977629101187189 10834264310402728236299)
              ·
                rfl

theorem cell19_106817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 5].length) (baseStart_106817 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_106817 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_106817 prefixEnd_106817 := by exact prefixLift 106817
  have htrace : WordTrace (prefixWord ++ tailWord_106817) baseStart_106817 baseEnd_106817 := by
    simpa [prefixWord, tailWord_106817, baseEnd_106817] using wordTrace_append hprefix tailTrace_106817
  have hstable : (prefixWord ++ tailWord_106817).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106817).length < 2 ^ (prefixWord ++ tailWord_106817).sum := by decide
  have hdescent : baseEnd_106817 < baseStart_106817 := by decide
  rcases family_descends (prefixWord ++ tailWord_106817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106878 : List Nat := [4, 2, 3, 10]
def baseStart_106878 : Nat := 118140960795 + 106878 * 2 ^ 59
def prefixEnd_106878 : Nat := 4983230072969 + 3 ^ 40 * 106878 * 2
def baseEnd_106878 : Nat := 401498201308371819175

theorem tailTrace_106878 : CollatzResearch.WordTrace tailWord_106878 prefixEnd_106878 401498201308371819175 := by
  unfold tailWord_106878
  simp only [CollatzResearch.WordTrace]
  refine ⟨487270113350841769286161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2598773937871156102859525 487270113350841769286161)
  ·
    refine ⟨365452585013131326964621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 487270113350841769286161 365452585013131326964621)
    ·
      refine ⟨137044719379924247611733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 365452585013131326964621 137044719379924247611733)
      ·
        refine ⟨401498201308371819175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 10 137044719379924247611733 401498201308371819175)
        ·
          rfl

theorem cell19_106878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 10].length) (baseStart_106878 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_106878 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_106878 prefixEnd_106878 := by exact prefixLift 106878
  have htrace : WordTrace (prefixWord ++ tailWord_106878) baseStart_106878 baseEnd_106878 := by
    simpa [prefixWord, tailWord_106878, baseEnd_106878] using wordTrace_append hprefix tailTrace_106878
  have hstable : (prefixWord ++ tailWord_106878).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106878).length < 2 ^ (prefixWord ++ tailWord_106878).sum := by decide
  have hdescent : baseEnd_106878 < baseStart_106878 := by decide
  rcases family_descends (prefixWord ++ tailWord_106878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106914 : List Nat := [3, 3, 1, 2, 1, 1, 5, 3]
def baseStart_106914 : Nat := 118140960795 + 106914 * 2 ^ 59
def prefixEnd_106914 : Nat := 4983230072969 + 3 ^ 40 * 106914 * 2
def baseEnd_106914 : Nat := 32532308559940700553077

theorem tailTrace_106914 : CollatzResearch.WordTrace tailWord_106914 prefixEnd_106914 32532308559940700553077 := by
  unfold tailWord_106914
  simp only [CollatzResearch.WordTrace]
  refine ⟨974868483669078075649949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2599649289784208201733197 974868483669078075649949)
  ·
    refine ⟨365575681375904278368731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 974868483669078075649949 365575681375904278368731)
    ·
      refine ⟨548363522063856417553097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365575681375904278368731 548363522063856417553097)
      ·
        refine ⟨411272641547892313164823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 548363522063856417553097 411272641547892313164823)
        ·
          refine ⟨616908962321838469747235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 411272641547892313164823 616908962321838469747235)
          ·
            refine ⟨925363443482757704620853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 616908962321838469747235 925363443482757704620853)
            ·
              refine ⟨86752822826508534808205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 925363443482757704620853 86752822826508534808205)
              ·
                refine ⟨32532308559940700553077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86752822826508534808205 32532308559940700553077)
                ·
                  rfl

theorem cell19_106914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 5, 3].length) (baseStart_106914 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_106914 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_106914 prefixEnd_106914 := by exact prefixLift 106914
  have htrace : WordTrace (prefixWord ++ tailWord_106914) baseStart_106914 baseEnd_106914 := by
    simpa [prefixWord, tailWord_106914, baseEnd_106914] using wordTrace_append hprefix tailTrace_106914
  have hstable : (prefixWord ++ tailWord_106914).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106914).length < 2 ^ (prefixWord ++ tailWord_106914).sum := by decide
  have hdescent : baseEnd_106914 < baseStart_106914 := by decide
  rcases family_descends (prefixWord ++ tailWord_106914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106973 : List Nat := [1, 4, 3, 1, 1, 1, 3, 5]
def baseStart_106973 : Nat := 118140960795 + 106973 * 2 ^ 59
def prefixEnd_106973 : Nat := 4983230072969 + 3 ^ 40 * 106973 * 2
def baseEnd_106973 : Nat := 32550261365046045241805

theorem tailTrace_106973 : CollatzResearch.WordTrace tailWord_106973 prefixEnd_106973 32550261365046045241805 := by
  unfold tailWord_106973
  simp only [CollatzResearch.WordTrace]
  refine ⟨3901625841462565378997573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2601083894308376919331715 3901625841462565378997573)
  ·
    refine ⟨731554845274231008562045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3901625841462565378997573 731554845274231008562045)
    ·
      refine ⟨274333066977836628210767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 731554845274231008562045 274333066977836628210767)
      ·
        refine ⟨411499600466754942316151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274333066977836628210767 411499600466754942316151)
        ·
          refine ⟨617249400700132413474227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 411499600466754942316151 617249400700132413474227)
          ·
            refine ⟨925874101050198620211341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 617249400700132413474227 925874101050198620211341)
            ·
              refine ⟨347202787893824482579253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 925874101050198620211341 347202787893824482579253)
              ·
                refine ⟨32550261365046045241805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 347202787893824482579253 32550261365046045241805)
                ·
                  rfl

theorem cell19_106973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 5].length) (baseStart_106973 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_106973 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_106973 prefixEnd_106973 := by exact prefixLift 106973
  have htrace : WordTrace (prefixWord ++ tailWord_106973) baseStart_106973 baseEnd_106973 := by
    simpa [prefixWord, tailWord_106973, baseEnd_106973] using wordTrace_append hprefix tailTrace_106973
  have hstable : (prefixWord ++ tailWord_106973).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106973).length < 2 ^ (prefixWord ++ tailWord_106973).sum := by decide
  have hdescent : baseEnd_106973 < baseStart_106973 := by decide
  rcases family_descends (prefixWord ++ tailWord_106973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107013 : List Nat := [1, 3, 1, 1, 2, 2, 3, 6]
def baseStart_107013 : Nat := 118140960795 + 107013 * 2 ^ 59
def prefixEnd_107013 : Nat := 4983230072969 + 3 ^ 40 * 107013 * 2
def baseEnd_107013 : Nat := 32562432758337804352807

theorem tailTrace_107013 : CollatzResearch.WordTrace tailWord_107013 prefixEnd_107013 32562432758337804352807 := by
  unfold tailWord_107013
  simp only [CollatzResearch.WordTrace]
  refine ⟨3903084761317652210453693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2602056507545101473635795 3903084761317652210453693)
  ·
    refine ⟨1463656785494119578920135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3903084761317652210453693 1463656785494119578920135)
    ·
      refine ⟨2195485178241179368380203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1463656785494119578920135 2195485178241179368380203)
      ·
        refine ⟨3293227767361769052570305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2195485178241179368380203 3293227767361769052570305)
        ·
          refine ⟨2469920825521326789427729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3293227767361769052570305 2469920825521326789427729)
          ·
            refine ⟨1852440619140995092070797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2469920825521326789427729 1852440619140995092070797)
            ·
              refine ⟨694665232177873159526549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1852440619140995092070797 694665232177873159526549)
              ·
                refine ⟨32562432758337804352807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 694665232177873159526549 32562432758337804352807)
                ·
                  rfl

theorem cell19_107013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 6].length) (baseStart_107013 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_107013 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_107013 prefixEnd_107013 := by exact prefixLift 107013
  have htrace : WordTrace (prefixWord ++ tailWord_107013) baseStart_107013 baseEnd_107013 := by
    simpa [prefixWord, tailWord_107013, baseEnd_107013] using wordTrace_append hprefix tailTrace_107013
  have hstable : (prefixWord ++ tailWord_107013).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107013).length < 2 ^ (prefixWord ++ tailWord_107013).sum := by decide
  have hdescent : baseEnd_107013 < baseStart_107013 := by decide
  rcases family_descends (prefixWord ++ tailWord_107013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107028 : List Nat := [2, 4, 3, 1, 1, 1, 2, 5]
def baseStart_107028 : Nat := 118140960795 + 107028 * 2 ^ 59
def prefixEnd_107028 : Nat := 4983230072969 + 3 ^ 40 * 107028 * 2
def baseEnd_107028 : Nat := 32566997030822214019433

theorem tailTrace_107028 : CollatzResearch.WordTrace tailWord_107028 prefixEnd_107028 32566997030822214019433 := by
  unfold tailWord_107028
  simp only [CollatzResearch.WordTrace]
  refine ⟨1951815928131654886124869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2602421237508873181499825 1951815928131654886124869)
  ·
    refine ⟨365965486524685291148413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1951815928131654886124869 365965486524685291148413)
    ·
      refine ⟨137237057446756984180655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 365965486524685291148413 137237057446756984180655)
      ·
        refine ⟨205855586170135476270983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137237057446756984180655 205855586170135476270983)
        ·
          refine ⟨308783379255203214406475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205855586170135476270983 308783379255203214406475)
          ·
            refine ⟨463175068882804821609713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 308783379255203214406475 463175068882804821609713)
            ·
              refine ⟨347381301662103616207285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 463175068882804821609713 347381301662103616207285)
              ·
                refine ⟨32566997030822214019433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 347381301662103616207285 32566997030822214019433)
                ·
                  rfl

theorem cell19_107028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 5].length) (baseStart_107028 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_107028 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_107028 prefixEnd_107028 := by exact prefixLift 107028
  have htrace : WordTrace (prefixWord ++ tailWord_107028) baseStart_107028 baseEnd_107028 := by
    simpa [prefixWord, tailWord_107028, baseEnd_107028] using wordTrace_append hprefix tailTrace_107028
  have hstable : (prefixWord ++ tailWord_107028).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107028).length < 2 ^ (prefixWord ++ tailWord_107028).sum := by decide
  have hdescent : baseEnd_107028 < baseStart_107028 := by decide
  rcases family_descends (prefixWord ++ tailWord_107028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107047 : List Nat := [1, 1, 7, 2, 1, 7]
def baseStart_107047 : Nat := 118140960795 + 107047 * 2 ^ 59
def prefixEnd_107047 : Nat := 4983230072969 + 3 ^ 40 * 107047 * 2
def baseEnd_107047 : Nat := 3619197604737311066351

theorem tailTrace_107047 : CollatzResearch.WordTrace tailWord_107047 prefixEnd_107047 3619197604737311066351 := by
  unfold tailWord_107047
  simp only [CollatzResearch.WordTrace]
  refine ⟨3904324843194476017191395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2602883228796317344794263 3904324843194476017191395)
  ·
    refine ⟨5856487264791714025787093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3904324843194476017191395 5856487264791714025787093)
    ·
      refine ⟨137261420268555797479385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 5856487264791714025787093 137261420268555797479385)
      ·
        refine ⟨102946065201416848109539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137261420268555797479385 102946065201416848109539)
        ·
          refine ⟨154419097802125272164309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102946065201416848109539 154419097802125272164309)
          ·
            refine ⟨3619197604737311066351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 154419097802125272164309 3619197604737311066351)
            ·
              rfl

theorem cell19_107047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 7].length) (baseStart_107047 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_107047 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_107047 prefixEnd_107047 := by exact prefixLift 107047
  have htrace : WordTrace (prefixWord ++ tailWord_107047) baseStart_107047 baseEnd_107047 := by
    simpa [prefixWord, tailWord_107047, baseEnd_107047] using wordTrace_append hprefix tailTrace_107047
  have hstable : (prefixWord ++ tailWord_107047).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107047).length < 2 ^ (prefixWord ++ tailWord_107047).sum := by decide
  have hdescent : baseEnd_107047 < baseStart_107047 := by decide
  rcases family_descends (prefixWord ++ tailWord_107047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107068 : List Nat := [2, 2, 2, 2, 3, 1, 3, 4]
def baseStart_107068 : Nat := 118140960795 + 107068 * 2 ^ 59
def prefixEnd_107068 : Nat := 4983230072969 + 3 ^ 40 * 107068 * 2
def baseEnd_107068 : Nat := 32579168424113973130435

theorem tailTrace_107068 : CollatzResearch.WordTrace tailWord_107068 prefixEnd_107068 32579168424113973130435 := by
  unfold tailWord_107068
  simp only [CollatzResearch.WordTrace]
  refine ⟨1952545388059198301852929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2603393850745597735803905 1952545388059198301852929)
  ·
    refine ⟨1464409041044398726389697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1952545388059198301852929 1464409041044398726389697)
    ·
      refine ⟨1098306780783299044792273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1464409041044398726389697 1098306780783299044792273)
      ·
        refine ⟨823730085587474283594205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1098306780783299044792273 823730085587474283594205)
        ·
          refine ⟨308898782095302856347827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 823730085587474283594205 308898782095302856347827)
          ·
            refine ⟨463348173142954284521741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 308898782095302856347827 463348173142954284521741)
            ·
              refine ⟨173755564928607856695653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 463348173142954284521741 173755564928607856695653)
              ·
                refine ⟨32579168424113973130435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 173755564928607856695653 32579168424113973130435)
                ·
                  rfl

theorem cell19_107068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 3, 4].length) (baseStart_107068 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_107068 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_107068 prefixEnd_107068 := by exact prefixLift 107068
  have htrace : WordTrace (prefixWord ++ tailWord_107068) baseStart_107068 baseEnd_107068 := by
    simpa [prefixWord, tailWord_107068, baseEnd_107068] using wordTrace_append hprefix tailTrace_107068
  have hstable : (prefixWord ++ tailWord_107068).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107068).length < 2 ^ (prefixWord ++ tailWord_107068).sum := by decide
  have hdescent : baseEnd_107068 < baseStart_107068 := by decide
  rcases family_descends (prefixWord ++ tailWord_107068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107108 : List Nat := [2, 3, 1, 1, 2, 2, 8]
def baseStart_107108 : Nat := 118140960795 + 107108 * 2 ^ 59
def prefixEnd_107108 : Nat := 4983230072969 + 3 ^ 40 * 107108 * 2
def baseEnd_107108 : Nat := 10863779939135244080479

theorem tailTrace_107108 : CollatzResearch.WordTrace tailWord_107108 prefixEnd_107108 10863779939135244080479 := by
  unfold tailWord_107108
  simp only [CollatzResearch.WordTrace]
  refine ⟨1953274847986741717580989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2604366463982322290107985 1953274847986741717580989)
  ·
    refine ⟨732478067995028144092871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1953274847986741717580989 732478067995028144092871)
    ·
      refine ⟨1098717101992542216139307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 732478067995028144092871 1098717101992542216139307)
      ·
        refine ⟨1648075652988813324208961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1098717101992542216139307 1648075652988813324208961)
        ·
          refine ⟨1236056739741609993156721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1648075652988813324208961 1236056739741609993156721)
          ·
            refine ⟨927042554806207494867541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1236056739741609993156721 927042554806207494867541)
            ·
              refine ⟨10863779939135244080479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 927042554806207494867541 10863779939135244080479)
              ·
                rfl

theorem cell19_107108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 8].length) (baseStart_107108 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_107108 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_107108 prefixEnd_107108 := by exact prefixLift 107108
  have htrace : WordTrace (prefixWord ++ tailWord_107108) baseStart_107108 baseEnd_107108 := by
    simpa [prefixWord, tailWord_107108, baseEnd_107108] using wordTrace_append hprefix tailTrace_107108
  have hstable : (prefixWord ++ tailWord_107108).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107108).length < 2 ^ (prefixWord ++ tailWord_107108).sum := by decide
  have hdescent : baseEnd_107108 < baseStart_107108 := by decide
  rcases family_descends (prefixWord ++ tailWord_107108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107138 : List Nat := [3, 4, 3, 1, 1, 1, 1, 5]
def baseStart_107138 : Nat := 118140960795 + 107138 * 2 ^ 59
def prefixEnd_107138 : Nat := 4983230072969 + 3 ^ 40 * 107138 * 2
def baseEnd_107138 : Nat := 32600468362374551574689

theorem tailTrace_107138 : CollatzResearch.WordTrace tailWord_107138 prefixEnd_107138 32600468362374551574689 := by
  unfold tailWord_107138
  simp only [CollatzResearch.WordTrace]
  refine ⟨976910971466199639688517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2605095923909865705836045 976910971466199639688517)
  ·
    refine ⟨183170807149912432441597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 976910971466199639688517 183170807149912432441597)
    ·
      refine ⟨68689052681217162165599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183170807149912432441597 68689052681217162165599)
      ·
        refine ⟨103033579021825743248399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68689052681217162165599 103033579021825743248399)
        ·
          refine ⟨154550368532738614872599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103033579021825743248399 154550368532738614872599)
          ·
            refine ⟨231825552799107922308899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154550368532738614872599 231825552799107922308899)
            ·
              refine ⟨347738329198661883463349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 231825552799107922308899 347738329198661883463349)
              ·
                refine ⟨32600468362374551574689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 347738329198661883463349 32600468362374551574689)
                ·
                  rfl

theorem cell19_107138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 5].length) (baseStart_107138 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_107138 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_107138 prefixEnd_107138 := by exact prefixLift 107138
  have htrace : WordTrace (prefixWord ++ tailWord_107138) baseStart_107138 baseEnd_107138 := by
    simpa [prefixWord, tailWord_107138, baseEnd_107138] using wordTrace_append hprefix tailTrace_107138
  have hstable : (prefixWord ++ tailWord_107138).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107138).length < 2 ^ (prefixWord ++ tailWord_107138).sum := by decide
  have hdescent : baseEnd_107138 < baseStart_107138 := by decide
  rcases family_descends (prefixWord ++ tailWord_107138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107165 : List Nat := [1, 4, 2, 1, 1, 1, 9]
def baseStart_107165 : Nat := 118140960795 + 107165 * 2 ^ 59
def prefixEnd_107165 : Nat := 4983230072969 + 3 ^ 40 * 107165 * 2
def baseEnd_107165 : Nat := 10869561350948829658205

theorem tailTrace_107165 : CollatzResearch.WordTrace tailWord_107165 prefixEnd_107165 10869561350948829658205 := by
  unfold tailWord_107165
  simp only [CollatzResearch.WordTrace]
  refine ⟨3908628656766982169986949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2605752437844654779991299 3908628656766982169986949)
  ·
    refine ⟨732867873143809156872553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3908628656766982169986949 732867873143809156872553)
    ·
      refine ⟨549650904857856867654415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 732867873143809156872553 549650904857856867654415)
      ·
        refine ⟨824476357286785301481623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 549650904857856867654415 824476357286785301481623)
        ·
          refine ⟨1236714535930177952222435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 824476357286785301481623 1236714535930177952222435)
          ·
            refine ⟨1855071803895266928333653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1236714535930177952222435 1855071803895266928333653)
            ·
              refine ⟨10869561350948829658205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1855071803895266928333653 10869561350948829658205)
              ·
                rfl

theorem cell19_107165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 9].length) (baseStart_107165 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_107165 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_107165 prefixEnd_107165 := by exact prefixLift 107165
  have htrace : WordTrace (prefixWord ++ tailWord_107165) baseStart_107165 baseEnd_107165 := by
    simpa [prefixWord, tailWord_107165, baseEnd_107165] using wordTrace_append hprefix tailTrace_107165
  have hstable : (prefixWord ++ tailWord_107165).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107165).length < 2 ^ (prefixWord ++ tailWord_107165).sum := by decide
  have hdescent : baseEnd_107165 < baseStart_107165 := by decide
  rcases family_descends (prefixWord ++ tailWord_107165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107178 : List Nat := [3, 1, 5, 2, 1, 1, 2, 4]
def baseStart_107178 : Nat := 118140960795 + 107178 * 2 ^ 59
def prefixEnd_107178 : Nat := 4983230072969 + 3 ^ 40 * 107178 * 2
def baseEnd_107178 : Nat := 32612639755666310685691

theorem tailTrace_107178 : CollatzResearch.WordTrace tailWord_107178 prefixEnd_107178 32612639755666310685691 := by
  unfold tailWord_107178
  simp only [CollatzResearch.WordTrace]
  refine ⟨977275701429971347552547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2606068537146590260140125 977275701429971347552547)
  ·
    refine ⟨1465913552144957021328821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 977275701429971347552547 1465913552144957021328821)
    ·
      refine ⟨137429395513589720749577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1465913552144957021328821 137429395513589720749577)
      ·
        refine ⟨103072046635192290562183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137429395513589720749577 103072046635192290562183)
        ·
          refine ⟨154608069952788435843275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103072046635192290562183 154608069952788435843275)
          ·
            refine ⟨231912104929182653764913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154608069952788435843275 231912104929182653764913)
            ·
              refine ⟨173934078696886990323685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 231912104929182653764913 173934078696886990323685)
              ·
                refine ⟨32612639755666310685691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 173934078696886990323685 32612639755666310685691)
                ·
                  rfl

theorem cell19_107178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 2, 4].length) (baseStart_107178 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_107178 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_107178 prefixEnd_107178 := by exact prefixLift 107178
  have htrace : WordTrace (prefixWord ++ tailWord_107178) baseStart_107178 baseEnd_107178 := by
    simpa [prefixWord, tailWord_107178, baseEnd_107178] using wordTrace_append hprefix tailTrace_107178
  have hstable : (prefixWord ++ tailWord_107178).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107178).length < 2 ^ (prefixWord ++ tailWord_107178).sum := by decide
  have hdescent : baseEnd_107178 < baseStart_107178 := by decide
  rcases family_descends (prefixWord ++ tailWord_107178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107220 : List Nat := [2, 4, 1, 3, 2, 7]
def baseStart_107220 : Nat := 118140960795 + 107220 * 2 ^ 59
def prefixEnd_107220 : Nat := 4983230072969 + 3 ^ 40 * 107220 * 2
def baseEnd_107220 : Nat := 3625046635402517528027

theorem tailTrace_107220 : CollatzResearch.WordTrace tailWord_107220 prefixEnd_107220 3625046635402517528027 := by
  unfold tailWord_107220
  simp only [CollatzResearch.WordTrace]
  refine ⟨1955317335783863281619557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2607089781045151042159409 1955317335783863281619557)
  ·
    refine ⟨366622000459474365303667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1955317335783863281619557 366622000459474365303667)
    ·
      refine ⟨549933000689211547955501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 366622000459474365303667 549933000689211547955501)
      ·
        refine ⟨206224875258454330483313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 549933000689211547955501 206224875258454330483313)
        ·
          refine ⟨154668656443840747862485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206224875258454330483313 154668656443840747862485)
          ·
            refine ⟨3625046635402517528027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 154668656443840747862485 3625046635402517528027)
            ·
              rfl

theorem cell19_107220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 7].length) (baseStart_107220 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_107220 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_107220 prefixEnd_107220 := by exact prefixLift 107220
  have htrace : WordTrace (prefixWord ++ tailWord_107220) baseStart_107220 baseEnd_107220 := by
    simpa [prefixWord, tailWord_107220, baseEnd_107220] using wordTrace_append hprefix tailTrace_107220
  have hstable : (prefixWord ++ tailWord_107220).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107220).length < 2 ^ (prefixWord ++ tailWord_107220).sum := by decide
  have hdescent : baseEnd_107220 < baseStart_107220 := by decide
  rcases family_descends (prefixWord ++ tailWord_107220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107241 : List Nat := [1, 2, 1, 1, 1, 2, 7, 4]
def baseStart_107241 : Nat := 118140960795 + 107241 * 2 ^ 59
def prefixEnd_107241 : Nat := 4983230072969 + 3 ^ 40 * 107241 * 2
def baseEnd_107241 : Nat := 32631809700100831285519

theorem tailTrace_107241 : CollatzResearch.WordTrace tailWord_107241 prefixEnd_107241 32631809700100831285519 := by
  unfold tailWord_107241
  simp only [CollatzResearch.WordTrace]
  refine ⟨3911400604491647149753577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2607600402994431433169051 3911400604491647149753577)
  ·
    refine ⟨2933550453368735362315183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3911400604491647149753577 2933550453368735362315183)
    ·
      refine ⟨4400325680053103043472775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2933550453368735362315183 4400325680053103043472775)
      ·
        refine ⟨6600488520079654565209163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4400325680053103043472775 6600488520079654565209163)
        ·
          refine ⟨9900732780119481847813745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6600488520079654565209163 9900732780119481847813745)
          ·
            refine ⟨7425549585089611385860309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9900732780119481847813745 7425549585089611385860309)
            ·
              refine ⟨174036318400537766856101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 7425549585089611385860309 174036318400537766856101)
              ·
                refine ⟨32631809700100831285519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 174036318400537766856101 32631809700100831285519)
                ·
                  rfl

theorem cell19_107241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 7, 4].length) (baseStart_107241 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_107241 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_107241 prefixEnd_107241 := by exact prefixLift 107241
  have htrace : WordTrace (prefixWord ++ tailWord_107241) baseStart_107241 baseEnd_107241 := by
    simpa [prefixWord, tailWord_107241, baseEnd_107241] using wordTrace_append hprefix tailTrace_107241
  have hstable : (prefixWord ++ tailWord_107241).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107241).length < 2 ^ (prefixWord ++ tailWord_107241).sum := by decide
  have hdescent : baseEnd_107241 < baseStart_107241 := by decide
  rcases family_descends (prefixWord ++ tailWord_107241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107252 : List Nat := [2, 6, 1, 1, 2, 1, 3, 3]
def baseStart_107252 : Nat := 118140960795 + 107252 * 2 ^ 59
def prefixEnd_107252 : Nat := 4983230072969 + 3 ^ 40 * 107252 * 2
def baseEnd_107252 : Nat := 32635156833256065041045

theorem tailTrace_107252 : CollatzResearch.WordTrace tailWord_107252 prefixEnd_107252 32635156833256065041045 := by
  unfold tailWord_107252
  simp only [CollatzResearch.WordTrace]
  refine ⟨1955900903725898014202005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2607867871634530685602673 1955900903725898014202005)
  ·
    refine ⟨91682854862151469415719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 1955900903725898014202005 91682854862151469415719)
    ·
      refine ⟨137524282293227204123579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91682854862151469415719 137524282293227204123579)
      ·
        refine ⟨206286423439840806185369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137524282293227204123579 206286423439840806185369)
        ·
          refine ⟨154714817579880604639027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206286423439840806185369 154714817579880604639027)
          ·
            refine ⟨232072226369820906958541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154714817579880604639027 232072226369820906958541)
            ·
              refine ⟨87027084888682840109453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 232072226369820906958541 87027084888682840109453)
              ·
                refine ⟨32635156833256065041045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87027084888682840109453 32635156833256065041045)
                ·
                  rfl

theorem cell19_107252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 3, 3].length) (baseStart_107252 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_107252 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_107252 prefixEnd_107252 := by exact prefixLift 107252
  have htrace : WordTrace (prefixWord ++ tailWord_107252) baseStart_107252 baseEnd_107252 := by
    simpa [prefixWord, tailWord_107252, baseEnd_107252] using wordTrace_append hprefix tailTrace_107252
  have hstable : (prefixWord ++ tailWord_107252).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107252).length < 2 ^ (prefixWord ++ tailWord_107252).sum := by decide
  have hdescent : baseEnd_107252 < baseStart_107252 := by decide
  rcases family_descends (prefixWord ++ tailWord_107252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107309 : List Nat := [1, 5, 3, 2, 1, 2, 2, 3]
def baseStart_107309 : Nat := 118140960795 + 107309 * 2 ^ 59
def prefixEnd_107309 : Nat := 4983230072969 + 3 ^ 40 * 107309 * 2
def baseEnd_107309 : Nat := 32652501068696821774223

theorem tailTrace_107309 : CollatzResearch.WordTrace tailWord_107309 prefixEnd_107309 32652501068696821774223 := by
  unfold tailWord_107309
  simp only [CollatzResearch.WordTrace]
  refine ⟨3913880768245294763228981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2609253845496863175485987 3913880768245294763228981)
  ·
    refine ⟨366926322022996384052717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3913880768245294763228981 366926322022996384052717)
    ·
      refine ⟨137597370758623644019769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 366926322022996384052717 137597370758623644019769)
      ·
        refine ⟨103198028068967733014827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137597370758623644019769 103198028068967733014827)
        ·
          refine ⟨154797042103451599522241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103198028068967733014827 154797042103451599522241)
          ·
            refine ⟨116097781577588699641681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154797042103451599522241 116097781577588699641681)
            ·
              refine ⟨87073336183191524731261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116097781577588699641681 87073336183191524731261)
              ·
                refine ⟨32652501068696821774223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87073336183191524731261 32652501068696821774223)
                ·
                  rfl

theorem cell19_107309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 2, 3].length) (baseStart_107309 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_107309 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_107309 prefixEnd_107309 := by exact prefixLift 107309
  have htrace : WordTrace (prefixWord ++ tailWord_107309) baseStart_107309 baseEnd_107309 := by
    simpa [prefixWord, tailWord_107309, baseEnd_107309] using wordTrace_append hprefix tailTrace_107309
  have hstable : (prefixWord ++ tailWord_107309).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107309).length < 2 ^ (prefixWord ++ tailWord_107309).sum := by decide
  have hdescent : baseEnd_107309 < baseStart_107309 := by decide
  rcases family_descends (prefixWord ++ tailWord_107309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107315 : List Nat := [1, 1, 1, 2, 6, 1, 4, 3]
def baseStart_107315 : Nat := 118140960795 + 107315 * 2 ^ 59
def prefixEnd_107315 : Nat := 4983230072969 + 3 ^ 40 * 107315 * 2
def baseEnd_107315 : Nat := 32654326777690585640873

theorem tailTrace_107315 : CollatzResearch.WordTrace tailWord_107315 prefixEnd_107315 32654326777690585640873 := by
  unfold tailWord_107315
  simp only [CollatzResearch.WordTrace]
  refine ⟨3914099606223557787947399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2609399737482371858631599 3914099606223557787947399)
  ·
    refine ⟨5871149409335336681921099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3914099606223557787947399 5871149409335336681921099)
    ·
      refine ⟨8806724114003005022881649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5871149409335336681921099 8806724114003005022881649)
      ·
        refine ⟨6605043085502253767161237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8806724114003005022881649 6605043085502253767161237)
        ·
          refine ⟨309611394632918145335683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 6605043085502253767161237 309611394632918145335683)
          ·
            refine ⟨464417091949377218003525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 309611394632918145335683 464417091949377218003525)
            ·
              refine ⟨87078204740508228375661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 464417091949377218003525 87078204740508228375661)
              ·
                refine ⟨32654326777690585640873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87078204740508228375661 32654326777690585640873)
                ·
                  rfl

theorem cell19_107315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 4, 3].length) (baseStart_107315 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_107315 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_107315 prefixEnd_107315 := by exact prefixLift 107315
  have htrace : WordTrace (prefixWord ++ tailWord_107315) baseStart_107315 baseEnd_107315 := by
    simpa [prefixWord, tailWord_107315, baseEnd_107315] using wordTrace_append hprefix tailTrace_107315
  have hstable : (prefixWord ++ tailWord_107315).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107315).length < 2 ^ (prefixWord ++ tailWord_107315).sum := by decide
  have hdescent : baseEnd_107315 < baseStart_107315 := by decide
  rcases family_descends (prefixWord ++ tailWord_107315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107562 : List Nat := [3, 1, 4, 1, 4, 6]
def baseStart_107562 : Nat := 118140960795 + 107562 * 2 ^ 59
def prefixEnd_107562 : Nat := 4983230072969 + 3 ^ 40 * 107562 * 2
def baseEnd_107562 : Nat := 3636609459029688683479

theorem tailTrace_107562 : CollatzResearch.WordTrace tailWord_107562 prefixEnd_107562 3636609459029688683479 := by
  unfold tailWord_107562
  simp only [CollatzResearch.WordTrace]
  refine ⟨980777109082179743047235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2615405624219145981459293 980777109082179743047235)
  ·
    refine ⟨1471165663623269614570853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 980777109082179743047235 1471165663623269614570853)
    ·
      refine ⟨275843561929363052732035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1471165663623269614570853 275843561929363052732035)
      ·
        refine ⟨413765342894044579098053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275843561929363052732035 413765342894044579098053)
        ·
          refine ⟨77581001792633358580885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 413765342894044579098053 77581001792633358580885)
          ·
            refine ⟨3636609459029688683479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 77581001792633358580885 3636609459029688683479)
            ·
              rfl

theorem cell19_107562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 6].length) (baseStart_107562 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_107562 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_107562 prefixEnd_107562 := by exact prefixLift 107562
  have htrace : WordTrace (prefixWord ++ tailWord_107562) baseStart_107562 baseEnd_107562 := by
    simpa [prefixWord, tailWord_107562, baseEnd_107562] using wordTrace_append hprefix tailTrace_107562
  have hstable : (prefixWord ++ tailWord_107562).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107562).length < 2 ^ (prefixWord ++ tailWord_107562).sum := by decide
  have hdescent : baseEnd_107562 < baseStart_107562 := by decide
  rcases family_descends (prefixWord ++ tailWord_107562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107581 : List Nat := [1, 4, 1, 3, 1, 4, 1, 4]
def baseStart_107581 : Nat := 118140960795 + 107581 * 2 ^ 59
def prefixEnd_107581 : Nat := 4983230072969 + 3 ^ 40 * 107581 * 2
def baseEnd_107581 : Nat := 32735266543080783729037

theorem tailTrace_107581 : CollatzResearch.WordTrace tailWord_107581 prefixEnd_107581 32735266543080783729037 := by
  unfold tailWord_107581
  simp only [CollatzResearch.WordTrace]
  refine ⟨3923801423259885217130597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2615867615506590144753731 3923801423259885217130597)
  ·
    refine ⟨735712766861228478211987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3923801423259885217130597 735712766861228478211987)
    ·
      refine ⟨1103569150291842717317981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 735712766861228478211987 1103569150291842717317981)
      ·
        refine ⟨413838431359441018994243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1103569150291842717317981 413838431359441018994243)
        ·
          refine ⟨620757647039161528491365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 413838431359441018994243 620757647039161528491365)
          ·
            refine ⟨116392058819842786592131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 620757647039161528491365 116392058819842786592131)
            ·
              refine ⟨174588088229764179888197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116392058819842786592131 174588088229764179888197)
              ·
                refine ⟨32735266543080783729037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 174588088229764179888197 32735266543080783729037)
                ·
                  rfl

theorem cell19_107581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 1, 4].length) (baseStart_107581 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_107581 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_107581 prefixEnd_107581 := by exact prefixLift 107581
  have htrace : WordTrace (prefixWord ++ tailWord_107581) baseStart_107581 baseEnd_107581 := by
    simpa [prefixWord, tailWord_107581, baseEnd_107581] using wordTrace_append hprefix tailTrace_107581
  have hstable : (prefixWord ++ tailWord_107581).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107581).length < 2 ^ (prefixWord ++ tailWord_107581).sum := by decide
  have hdescent : baseEnd_107581 < baseStart_107581 := by decide
  rcases family_descends (prefixWord ++ tailWord_107581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107657 : List Nat := [1, 2, 1, 1, 4, 5, 2, 3]
def baseStart_107657 : Nat := 118140960795 + 107657 * 2 ^ 59
def prefixEnd_107657 : Nat := 4983230072969 + 3 ^ 40 * 107657 * 2
def baseEnd_107657 : Nat := 32758392190335126039941

theorem tailTrace_107657 : CollatzResearch.WordTrace tailWord_107657 prefixEnd_107657 32758392190335126039941 := by
  unfold tailWord_107657
  simp only [CollatzResearch.WordTrace]
  refine ⟨3926573370984550196897225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2617715580656366797931483 3926573370984550196897225)
  ·
    refine ⟨2944930028238412647672919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3926573370984550196897225 2944930028238412647672919)
    ·
      refine ⟨4417395042357618971509379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2944930028238412647672919 4417395042357618971509379)
      ·
        refine ⟨6626092563536428457264069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4417395042357618971509379 6626092563536428457264069)
        ·
          refine ⟨1242392355663080335737013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6626092563536428457264069 1242392355663080335737013)
          ·
            refine ⟨116474283343413781475345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1242392355663080335737013 116474283343413781475345)
            ·
              refine ⟨87355712507560336106509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116474283343413781475345 87355712507560336106509)
              ·
                refine ⟨32758392190335126039941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87355712507560336106509 32758392190335126039941)
                ·
                  rfl

theorem cell19_107657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 2, 3].length) (baseStart_107657 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_107657 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_107657 prefixEnd_107657 := by exact prefixLift 107657
  have htrace : WordTrace (prefixWord ++ tailWord_107657) baseStart_107657 baseEnd_107657 := by
    simpa [prefixWord, tailWord_107657, baseEnd_107657] using wordTrace_append hprefix tailTrace_107657
  have hstable : (prefixWord ++ tailWord_107657).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107657).length < 2 ^ (prefixWord ++ tailWord_107657).sum := by decide
  have hdescent : baseEnd_107657 < baseStart_107657 := by decide
  rcases family_descends (prefixWord ++ tailWord_107657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107697 : List Nat := [1, 2, 2, 5, 1, 1, 1, 6]
def baseStart_107697 : Nat := 118140960795 + 107697 * 2 ^ 59
def prefixEnd_107697 : Nat := 4983230072969 + 3 ^ 40 * 107697 * 2
def baseEnd_107697 : Nat := 32770563583626885150943

theorem tailTrace_107697 : CollatzResearch.WordTrace tailWord_107697 prefixEnd_107697 32770563583626885150943 := by
  unfold tailWord_107697
  simp only [CollatzResearch.WordTrace]
  refine ⟨3928032290839637028353345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2618688193893091352235563 3928032290839637028353345)
  ·
    refine ⟨2946024218129727771265009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3928032290839637028353345 2946024218129727771265009)
    ·
      refine ⟨2209518163597295828448757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2946024218129727771265009 2209518163597295828448757)
      ·
        refine ⟨207142327837246483917071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2209518163597295828448757 207142327837246483917071)
        ·
          refine ⟨310713491755869725875607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207142327837246483917071 310713491755869725875607)
          ·
            refine ⟨466070237633804588813411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 310713491755869725875607 466070237633804588813411)
            ·
              refine ⟨699105356450706883220117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 466070237633804588813411 699105356450706883220117)
              ·
                refine ⟨32770563583626885150943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 699105356450706883220117 32770563583626885150943)
                ·
                  rfl

theorem cell19_107697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 6].length) (baseStart_107697 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_107697 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_107697 prefixEnd_107697 := by exact prefixLift 107697
  have htrace : WordTrace (prefixWord ++ tailWord_107697) baseStart_107697 baseEnd_107697 := by
    simpa [prefixWord, tailWord_107697, baseEnd_107697] using wordTrace_append hprefix tailTrace_107697
  have hstable : (prefixWord ++ tailWord_107697).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107697).length < 2 ^ (prefixWord ++ tailWord_107697).sum := by decide
  have hdescent : baseEnd_107697 < baseStart_107697 := by decide
  rcases family_descends (prefixWord ++ tailWord_107697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107699 : List Nat := [1, 1, 1, 2, 3, 2, 3, 6]
def baseStart_107699 : Nat := 118140960795 + 107699 * 2 ^ 59
def prefixEnd_107699 : Nat := 4983230072969 + 3 ^ 40 * 107699 * 2
def baseEnd_107699 : Nat := 32771172153291473106493

theorem tailTrace_107699 : CollatzResearch.WordTrace tailWord_107699 prefixEnd_107699 32771172153291473106493 := by
  unfold tailWord_107699
  simp only [CollatzResearch.WordTrace]
  refine ⟨3928105236832391369926151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2618736824554927579950767 3928105236832391369926151)
  ·
    refine ⟨5892157855248587054889227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3928105236832391369926151 5892157855248587054889227)
    ·
      refine ⟨8838236782872880582333841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5892157855248587054889227 8838236782872880582333841)
      ·
        refine ⟨6628677587154660436750381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8838236782872880582333841 6628677587154660436750381)
        ·
          refine ⟨2485754095182997663781393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6628677587154660436750381 2485754095182997663781393)
          ·
            refine ⟨1864315571387248247836045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2485754095182997663781393 1864315571387248247836045)
            ·
              refine ⟨699118339270218092938517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1864315571387248247836045 699118339270218092938517)
              ·
                refine ⟨32771172153291473106493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 699118339270218092938517 32771172153291473106493)
                ·
                  rfl

theorem cell19_107699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 6].length) (baseStart_107699 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_107699 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_107699 prefixEnd_107699 := by exact prefixLift 107699
  have htrace : WordTrace (prefixWord ++ tailWord_107699) baseStart_107699 baseEnd_107699 := by
    simpa [prefixWord, tailWord_107699, baseEnd_107699] using wordTrace_append hprefix tailTrace_107699
  have hstable : (prefixWord ++ tailWord_107699).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107699).length < 2 ^ (prefixWord ++ tailWord_107699).sum := by decide
  have hdescent : baseEnd_107699 < baseStart_107699 := by decide
  rcases family_descends (prefixWord ++ tailWord_107699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107754 : List Nat := [3, 1, 3, 1, 1, 3, 3, 4]
def baseStart_107754 : Nat := 118140960795 + 107754 * 2 ^ 59
def prefixEnd_107754 : Nat := 4983230072969 + 3 ^ 40 * 107754 * 2
def baseEnd_107754 : Nat := 32787907819067641884121

theorem tailTrace_107754 : CollatzResearch.WordTrace tailWord_107754 prefixEnd_107754 32787907819067641884121 := by
  unfold tailWord_107754
  simp only [CollatzResearch.WordTrace]
  refine ⟨982527812908283940794579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2620074167755423842118877 982527812908283940794579)
  ·
    refine ⟨1473791719362425911191869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 982527812908283940794579 1473791719362425911191869)
    ·
      refine ⟨552671894760909716696951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1473791719362425911191869 552671894760909716696951)
      ·
        refine ⟨829007842141364575045427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 552671894760909716696951 829007842141364575045427)
        ·
          refine ⟨1243511763212046862568141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 829007842141364575045427 1243511763212046862568141)
          ·
            refine ⟨466316911204517573463053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1243511763212046862568141 466316911204517573463053)
            ·
              refine ⟨174868841701694090048645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 466316911204517573463053 174868841701694090048645)
              ·
                refine ⟨32787907819067641884121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 174868841701694090048645 32787907819067641884121)
                ·
                  rfl

theorem cell19_107754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 3, 4].length) (baseStart_107754 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_107754 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_107754 prefixEnd_107754 := by exact prefixLift 107754
  have htrace : WordTrace (prefixWord ++ tailWord_107754) baseStart_107754 baseEnd_107754 := by
    simpa [prefixWord, tailWord_107754, baseEnd_107754] using wordTrace_append hprefix tailTrace_107754
  have hstable : (prefixWord ++ tailWord_107754).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107754).length < 2 ^ (prefixWord ++ tailWord_107754).sum := by decide
  have hdescent : baseEnd_107754 < baseStart_107754 := by decide
  rcases family_descends (prefixWord ++ tailWord_107754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107889 : List Nat := [1, 2, 2, 2, 1, 2, 4, 5]
def baseStart_107889 : Nat := 118140960795 + 107889 * 2 ^ 59
def prefixEnd_107889 : Nat := 4983230072969 + 3 ^ 40 * 107889 * 2
def baseEnd_107889 : Nat := 32828986271427328883753

theorem tailTrace_107889 : CollatzResearch.WordTrace tailWord_107889 prefixEnd_107889 32828986271427328883753 := by
  unfold tailWord_107889
  simp only [CollatzResearch.WordTrace]
  refine ⟨3935035106144053819342721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2623356737429369212895147 3935035106144053819342721)
  ·
    refine ⟨2951276329608040364507041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3935035106144053819342721 2951276329608040364507041)
    ·
      refine ⟨2213457247206030273380281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2951276329608040364507041 2213457247206030273380281)
      ·
        refine ⟨1660092935404522705035211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2213457247206030273380281 1660092935404522705035211)
        ·
          refine ⟨2490139403106784057552817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1660092935404522705035211 2490139403106784057552817)
          ·
            refine ⟨1867604552330088043164613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2490139403106784057552817 1867604552330088043164613)
            ·
              refine ⟨350175853561891508093365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1867604552330088043164613 350175853561891508093365)
              ·
                refine ⟨32828986271427328883753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 350175853561891508093365 32828986271427328883753)
                ·
                  rfl

theorem cell19_107889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 5].length) (baseStart_107889 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_107889 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_107889 prefixEnd_107889 := by exact prefixLift 107889
  have htrace : WordTrace (prefixWord ++ tailWord_107889) baseStart_107889 baseEnd_107889 := by
    simpa [prefixWord, tailWord_107889, baseEnd_107889] using wordTrace_append hprefix tailTrace_107889
  have hstable : (prefixWord ++ tailWord_107889).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107889).length < 2 ^ (prefixWord ++ tailWord_107889).sum := by decide
  have hdescent : baseEnd_107889 < baseStart_107889 := by decide
  rcases family_descends (prefixWord ++ tailWord_107889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107902 : List Nat := [4, 2, 3, 2, 2, 6]
def baseStart_107902 : Nat := 118140960795 + 107902 * 2 ^ 59
def prefixEnd_107902 : Nat := 4983230072969 + 3 ^ 40 * 107902 * 2
def baseEnd_107902 : Nat := 3648104663805238954981

theorem tailTrace_107902 : CollatzResearch.WordTrace tailWord_107902 prefixEnd_107902 3648104663805238954981 := by
  unfold tailWord_107902
  simp only [CollatzResearch.WordTrace]
  refine ⟨491938656887119629945745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2623672836731304693043973 491938656887119629945745)
  ·
    refine ⟨368953992665339722459309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 491938656887119629945745 368953992665339722459309)
    ·
      refine ⟨138357747249502395922241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 368953992665339722459309 138357747249502395922241)
      ·
        refine ⟨103768310437126796941681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138357747249502395922241 103768310437126796941681)
        ·
          refine ⟨77826232827845097706261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103768310437126796941681 77826232827845097706261)
          ·
            refine ⟨3648104663805238954981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 77826232827845097706261 3648104663805238954981)
            ·
              rfl

theorem cell19_107902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 6].length) (baseStart_107902 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_107902 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_107902 prefixEnd_107902 := by exact prefixLift 107902
  have htrace : WordTrace (prefixWord ++ tailWord_107902) baseStart_107902 baseEnd_107902 := by
    simpa [prefixWord, tailWord_107902, baseEnd_107902] using wordTrace_append hprefix tailTrace_107902
  have hstable : (prefixWord ++ tailWord_107902).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107902).length < 2 ^ (prefixWord ++ tailWord_107902).sum := by decide
  have hdescent : baseEnd_107902 < baseStart_107902 := by decide
  rcases family_descends (prefixWord ++ tailWord_107902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107908 : List Nat := [2, 3, 2, 1, 1, 10]
def baseStart_107908 : Nat := 118140960795 + 107908 * 2 ^ 59
def prefixEnd_107908 : Nat := 4983230072969 + 3 ^ 40 * 107908 * 2
def baseEnd_107908 : Nat := 3648307520360101606831

theorem tailTrace_107908 : CollatzResearch.WordTrace tailWord_107908 prefixEnd_107908 3648307520360101606831 := by
  unfold tailWord_107908
  simp only [CollatzResearch.WordTrace]
  refine ⟨1967864046537610032142189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2623818728716813376189585 1967864046537610032142189)
  ·
    refine ⟨737949017451603762053321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1967864046537610032142189 737949017451603762053321)
    ·
      refine ⟨553461763088702821539991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 737949017451603762053321 553461763088702821539991)
      ·
        refine ⟨830192644633054232309987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 553461763088702821539991 830192644633054232309987)
        ·
          refine ⟨1245288966949581348464981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 830192644633054232309987 1245288966949581348464981)
          ·
            refine ⟨3648307520360101606831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1245288966949581348464981 3648307520360101606831)
            ·
              rfl

theorem cell19_107908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 10].length) (baseStart_107908 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_107908 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_107908 prefixEnd_107908 := by exact prefixLift 107908
  have htrace : WordTrace (prefixWord ++ tailWord_107908) baseStart_107908 baseEnd_107908 := by
    simpa [prefixWord, tailWord_107908, baseEnd_107908] using wordTrace_append hprefix tailTrace_107908
  have hstable : (prefixWord ++ tailWord_107908).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107908).length < 2 ^ (prefixWord ++ tailWord_107908).sum := by decide
  have hdescent : baseEnd_107908 < baseStart_107908 := by decide
  rcases family_descends (prefixWord ++ tailWord_107908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107965 : List Nat := [1, 4, 1, 2, 2, 1, 8]
def baseStart_107965 : Nat := 118140960795 + 107965 * 2 ^ 59
def prefixEnd_107965 : Nat := 4983230072969 + 3 ^ 40 * 107965 * 2
def baseEnd_107965 : Nat := 10950703972893890398219

theorem tailTrace_107965 : CollatzResearch.WordTrace tailWord_107965 prefixEnd_107965 10950703972893890398219 := by
  unfold tailWord_107965
  simp only [CollatzResearch.WordTrace]
  refine ⟨3937807053868718799109349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2625204702579145866072899 3937807053868718799109349)
  ·
    refine ⟨738338822600384774833003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3937807053868718799109349 738338822600384774833003)
    ·
      refine ⟨1107508233900577162249505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 738338822600384774833003 1107508233900577162249505)
      ·
        refine ⟨830631175425432871687129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1107508233900577162249505 830631175425432871687129)
        ·
          refine ⟨622973381569074653765347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 830631175425432871687129 622973381569074653765347)
          ·
            refine ⟨934460072353611980648021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 622973381569074653765347 934460072353611980648021)
            ·
              refine ⟨10950703972893890398219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 934460072353611980648021 10950703972893890398219)
              ·
                rfl

theorem cell19_107965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 8].length) (baseStart_107965 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_107965 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_107965 prefixEnd_107965 := by exact prefixLift 107965
  have htrace : WordTrace (prefixWord ++ tailWord_107965) baseStart_107965 baseEnd_107965 := by
    simpa [prefixWord, tailWord_107965, baseEnd_107965] using wordTrace_append hprefix tailTrace_107965
  have hstable : (prefixWord ++ tailWord_107965).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107965).length < 2 ^ (prefixWord ++ tailWord_107965).sum := by decide
  have hdescent : baseEnd_107965 < baseStart_107965 := by decide
  rcases family_descends (prefixWord ++ tailWord_107965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108001 : List Nat := [1, 2, 3, 1, 2, 3, 4, 3]
def baseStart_108001 : Nat := 118140960795 + 108001 * 2 ^ 59
def prefixEnd_108001 : Nat := 4983230072969 + 3 ^ 40 * 108001 * 2
def baseEnd_108001 : Nat := 32863066172644254394559

theorem tailTrace_108001 : CollatzResearch.WordTrace tailWord_108001 prefixEnd_108001 32863066172644254394559 := by
  unfold tailWord_108001
  simp only [CollatzResearch.WordTrace]
  refine ⟨3939120081738296947419857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2626080054492197964946571 3939120081738296947419857)
  ·
    refine ⟨2954340061303722710564893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3939120081738296947419857 2954340061303722710564893)
    ·
      refine ⟨1107877522988896016461835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2954340061303722710564893 1107877522988896016461835)
      ·
        refine ⟨1661816284483344024692753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1107877522988896016461835 1661816284483344024692753)
        ·
          refine ⟨1246362213362508018519565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1661816284483344024692753 1246362213362508018519565)
          ·
            refine ⟨467385830010940506944837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1246362213362508018519565 467385830010940506944837)
            ·
              refine ⟨87634843127051345052157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 467385830010940506944837 87634843127051345052157)
              ·
                refine ⟨32863066172644254394559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87634843127051345052157 32863066172644254394559)
                ·
                  rfl

theorem cell19_108001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 4, 3].length) (baseStart_108001 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_108001 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_108001 prefixEnd_108001 := by exact prefixLift 108001
  have htrace : WordTrace (prefixWord ++ tailWord_108001) baseStart_108001 baseEnd_108001 := by
    simpa [prefixWord, tailWord_108001, baseEnd_108001] using wordTrace_append hprefix tailTrace_108001
  have hstable : (prefixWord ++ tailWord_108001).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108001).length < 2 ^ (prefixWord ++ tailWord_108001).sum := by decide
  have hdescent : baseEnd_108001 < baseStart_108001 := by decide
  rcases family_descends (prefixWord ++ tailWord_108001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108039 : List Nat := [1, 1, 4, 3, 2, 2, 2, 4]
def baseStart_108039 : Nat := 118140960795 + 108039 * 2 ^ 59
def prefixEnd_108039 : Nat := 4983230072969 + 3 ^ 40 * 108039 * 2
def baseEnd_108039 : Nat := 32874628996271425550011

theorem tailTrace_108039 : CollatzResearch.WordTrace tailWord_108039 prefixEnd_108039 32874628996271425550011 := by
  unfold tailWord_108039
  simp only [CollatzResearch.WordTrace]
  refine ⟨3940506055600629437303171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2627004037067086291535447 3940506055600629437303171)
  ·
    refine ⟨5910759083400944155954757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3940506055600629437303171 5910759083400944155954757)
    ·
      refine ⟨1108267328137677029241517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5910759083400944155954757 1108267328137677029241517)
      ·
        refine ⟨415600248051628885965569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1108267328137677029241517 415600248051628885965569)
        ·
          refine ⟨311700186038721664474177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 415600248051628885965569 311700186038721664474177)
          ·
            refine ⟨233775139529041248355633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 311700186038721664474177 233775139529041248355633)
            ·
              refine ⟨175331354646780936266725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 233775139529041248355633 175331354646780936266725)
              ·
                refine ⟨32874628996271425550011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 175331354646780936266725 32874628996271425550011)
                ·
                  rfl

theorem cell19_108039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 2, 4].length) (baseStart_108039 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_108039 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_108039 prefixEnd_108039 := by exact prefixLift 108039
  have htrace : WordTrace (prefixWord ++ tailWord_108039) baseStart_108039 baseEnd_108039 := by
    simpa [prefixWord, tailWord_108039, baseEnd_108039] using wordTrace_append hprefix tailTrace_108039
  have hstable : (prefixWord ++ tailWord_108039).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108039).length < 2 ^ (prefixWord ++ tailWord_108039).sum := by decide
  have hdescent : baseEnd_108039 < baseStart_108039 := by decide
  rcases family_descends (prefixWord ++ tailWord_108039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108041 : List Nat := [1, 2, 1, 1, 3, 1, 6, 4]
def baseStart_108041 : Nat := 118140960795 + 108041 * 2 ^ 59
def prefixEnd_108041 : Nat := 4983230072969 + 3 ^ 40 * 108041 * 2
def baseEnd_108041 : Nat := 32875237565936013505561

theorem tailTrace_108041 : CollatzResearch.WordTrace tailWord_108041 prefixEnd_108041 32875237565936013505561 := by
  unfold tailWord_108041
  simp only [CollatzResearch.WordTrace]
  refine ⟨3940579001593383778875977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2627052667728922519250651 3940579001593383778875977)
  ·
    refine ⟨2955434251195037834156983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3940579001593383778875977 2955434251195037834156983)
    ·
      refine ⟨4433151376792556751235475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2955434251195037834156983 4433151376792556751235475)
      ·
        refine ⟨6649727065188835126853213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4433151376792556751235475 6649727065188835126853213)
        ·
          refine ⟨2493647649445813172569955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6649727065188835126853213 2493647649445813172569955)
          ·
            refine ⟨3740471474168719758854933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2493647649445813172569955 3740471474168719758854933)
            ·
              refine ⟨175334600351658738696325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 3740471474168719758854933 175334600351658738696325)
              ·
                refine ⟨32875237565936013505561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 175334600351658738696325 32875237565936013505561)
                ·
                  rfl

theorem cell19_108041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 6, 4].length) (baseStart_108041 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_108041 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_108041 prefixEnd_108041 := by exact prefixLift 108041
  have htrace : WordTrace (prefixWord ++ tailWord_108041) baseStart_108041 baseEnd_108041 := by
    simpa [prefixWord, tailWord_108041, baseEnd_108041] using wordTrace_append hprefix tailTrace_108041
  have hstable : (prefixWord ++ tailWord_108041).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108041).length < 2 ^ (prefixWord ++ tailWord_108041).sum := by decide
  have hdescent : baseEnd_108041 < baseStart_108041 := by decide
  rcases family_descends (prefixWord ++ tailWord_108041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108060 : List Nat := [2, 2, 3, 1, 2, 1, 1, 7]
def baseStart_108060 : Nat := 118140960795 + 108060 * 2 ^ 59
def prefixEnd_108060 : Nat := 4983230072969 + 3 ^ 40 * 108060 * 2
def baseEnd_108060 : Nat := 32881018977749599083287

theorem tailTrace_108060 : CollatzResearch.WordTrace tailWord_108060 prefixEnd_108060 32881018977749599083287 := by
  unfold tailWord_108060
  simp only [CollatzResearch.WordTrace]
  refine ⟨1970635994262275011908817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2627514659016366682545089 1970635994262275011908817)
  ·
    refine ⟨1477976995696706258931613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1970635994262275011908817 1477976995696706258931613)
    ·
      refine ⟨554241373386264847099355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1477976995696706258931613 554241373386264847099355)
      ·
        refine ⟨831362060079397270649033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 554241373386264847099355 831362060079397270649033)
        ·
          refine ⟨623521545059547952986775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 831362060079397270649033 623521545059547952986775)
          ·
            refine ⟨935282317589321929480163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 623521545059547952986775 935282317589321929480163)
            ·
              refine ⟨1402923476383982894220245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 935282317589321929480163 1402923476383982894220245)
              ·
                refine ⟨32881018977749599083287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1402923476383982894220245 32881018977749599083287)
                ·
                  rfl

theorem cell19_108060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 7].length) (baseStart_108060 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_108060 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_108060 prefixEnd_108060 := by exact prefixLift 108060
  have htrace : WordTrace (prefixWord ++ tailWord_108060) baseStart_108060 baseEnd_108060 := by
    simpa [prefixWord, tailWord_108060, baseEnd_108060] using wordTrace_append hprefix tailTrace_108060
  have hstable : (prefixWord ++ tailWord_108060).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108060).length < 2 ^ (prefixWord ++ tailWord_108060).sum := by decide
  have hdescent : baseEnd_108060 < baseStart_108060 := by decide
  rcases family_descends (prefixWord ++ tailWord_108060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108077 : List Nat := [1, 5, 4, 9]
def baseStart_108077 : Nat := 118140960795 + 108077 * 2 ^ 59
def prefixEnd_108077 : Nat := 4983230072969 + 3 ^ 40 * 108077 * 2
def baseEnd_108077 : Nat := 406002368146896255623

theorem tailTrace_108077 : CollatzResearch.WordTrace tailWord_108077 prefixEnd_108077 406002368146896255623 := by
  unfold tailWord_108077
  simp only [CollatzResearch.WordTrace]
  refine ⟨3941892029462961927186485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2627928019641974618124323 3941892029462961927186485)
  ·
    refine ⟨369552377762152680673733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3941892029462961927186485 369552377762152680673733)
    ·
      refine ⟨69291070830403627626325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 369552377762152680673733 69291070830403627626325)
      ·
        refine ⟨406002368146896255623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 9 69291070830403627626325 406002368146896255623)
        ·
          rfl

theorem cell19_108077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 9].length) (baseStart_108077 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_108077 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_108077 prefixEnd_108077 := by exact prefixLift 108077
  have htrace : WordTrace (prefixWord ++ tailWord_108077) baseStart_108077 baseEnd_108077 := by
    simpa [prefixWord, tailWord_108077, baseEnd_108077] using wordTrace_append hprefix tailTrace_108077
  have hstable : (prefixWord ++ tailWord_108077).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108077).length < 2 ^ (prefixWord ++ tailWord_108077).sum := by decide
  have hdescent : baseEnd_108077 < baseStart_108077 := by decide
  rcases family_descends (prefixWord ++ tailWord_108077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108168 : List Nat := [2, 1, 3, 5, 1, 2, 2, 3]
def baseStart_108168 : Nat := 118140960795 + 108168 * 2 ^ 59
def prefixEnd_108168 : Nat := 4983230072969 + 3 ^ 40 * 108168 * 2
def baseEnd_108168 : Nat := 32913881739637348682993

theorem tailTrace_108168 : CollatzResearch.WordTrace tailWord_108168 prefixEnd_108168 32913881739637348682993 := by
  unfold tailWord_108168
  simp only [CollatzResearch.WordTrace]
  refine ⟨1972605536066642234374579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2630140714755522979166105 1972605536066642234374579)
  ·
    refine ⟨2958908304099963351561869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1972605536066642234374579 2958908304099963351561869)
    ·
      refine ⟨1109590614037486256835701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2958908304099963351561869 1109590614037486256835701)
      ·
        refine ⟨104024120066014336578347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1109590614037486256835701 104024120066014336578347)
        ·
          refine ⟨156036180099021504867521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104024120066014336578347 156036180099021504867521)
          ·
            refine ⟨117027135074266128650641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156036180099021504867521 117027135074266128650641)
            ·
              refine ⟨87770351305699596487981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117027135074266128650641 87770351305699596487981)
              ·
                refine ⟨32913881739637348682993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87770351305699596487981 32913881739637348682993)
                ·
                  rfl

theorem cell19_108168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 2, 3].length) (baseStart_108168 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_108168 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_108168 prefixEnd_108168 := by exact prefixLift 108168
  have htrace : WordTrace (prefixWord ++ tailWord_108168) baseStart_108168 baseEnd_108168 := by
    simpa [prefixWord, tailWord_108168, baseEnd_108168] using wordTrace_append hprefix tailTrace_108168
  have hstable : (prefixWord ++ tailWord_108168).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108168).length < 2 ^ (prefixWord ++ tailWord_108168).sum := by decide
  have hdescent : baseEnd_108168 < baseStart_108168 := by decide
  rcases family_descends (prefixWord ++ tailWord_108168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108170 : List Nat := [3, 1, 2, 3, 2, 3, 2, 3]
def baseStart_108170 : Nat := 118140960795 + 108170 * 2 ^ 59
def prefixEnd_108170 : Nat := 4983230072969 + 3 ^ 40 * 108170 * 2
def baseEnd_108170 : Nat := 32914490309301936638543

theorem tailTrace_108170 : CollatzResearch.WordTrace tailWord_108170 prefixEnd_108170 32914490309301936638543 := by
  unfold tailWord_108170
  simp only [CollatzResearch.WordTrace]
  refine ⟨986321004531509702580491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2630189345417359206881309 986321004531509702580491)
  ·
    refine ⟨1479481506797264553870737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 986321004531509702580491 1479481506797264553870737)
    ·
      refine ⟨1109611130097948415403053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1479481506797264553870737 1109611130097948415403053)
      ·
        refine ⟨416104173786730655776145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1109611130097948415403053 416104173786730655776145)
        ·
          refine ⟨312078130340047991832109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 416104173786730655776145 312078130340047991832109)
          ·
            refine ⟨117029298877517996937041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 312078130340047991832109 117029298877517996937041)
            ·
              refine ⟨87771974158138497702781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117029298877517996937041 87771974158138497702781)
              ·
                refine ⟨32914490309301936638543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87771974158138497702781 32914490309301936638543)
                ·
                  rfl

theorem cell19_108170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 2, 3].length) (baseStart_108170 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_108170 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_108170 prefixEnd_108170 := by exact prefixLift 108170
  have htrace : WordTrace (prefixWord ++ tailWord_108170) baseStart_108170 baseEnd_108170 := by
    simpa [prefixWord, tailWord_108170, baseEnd_108170] using wordTrace_append hprefix tailTrace_108170
  have hstable : (prefixWord ++ tailWord_108170).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108170).length < 2 ^ (prefixWord ++ tailWord_108170).sum := by decide
  have hdescent : baseEnd_108170 < baseStart_108170 := by decide
  rcases family_descends (prefixWord ++ tailWord_108170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108193 : List Nat := [1, 2, 3, 3, 2, 1, 7]
def baseStart_108193 : Nat := 118140960795 + 108193 * 2 ^ 59
def prefixEnd_108193 : Nat := 4983230072969 + 3 ^ 40 * 108193 * 2
def baseEnd_108193 : Nat := 10973829620148232709123

theorem tailTrace_108193 : CollatzResearch.WordTrace tailWord_108193 prefixEnd_108193 10973829620148232709123 := by
  unfold tailWord_108193
  simp only [CollatzResearch.WordTrace]
  refine ⟨3946122897042713738409233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2630748598028475825606155 3946122897042713738409233)
  ·
    refine ⟨2959592172782035303806925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3946122897042713738409233 2959592172782035303806925)
    ·
      refine ⟨1109847064793263238927597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2959592172782035303806925 1109847064793263238927597)
      ·
        refine ⟨416192649297473714597849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1109847064793263238927597 416192649297473714597849)
        ·
          refine ⟨312144486973105285948387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 416192649297473714597849 312144486973105285948387)
          ·
            refine ⟨468216730459657928922581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 312144486973105285948387 468216730459657928922581)
            ·
              refine ⟨10973829620148232709123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 468216730459657928922581 10973829620148232709123)
              ·
                rfl

theorem cell19_108193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 7].length) (baseStart_108193 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_108193 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_108193 prefixEnd_108193 := by exact prefixLift 108193
  have htrace : WordTrace (prefixWord ++ tailWord_108193) baseStart_108193 baseEnd_108193 := by
    simpa [prefixWord, tailWord_108193, baseEnd_108193] using wordTrace_append hprefix tailTrace_108193
  have hstable : (prefixWord ++ tailWord_108193).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108193).length < 2 ^ (prefixWord ++ tailWord_108193).sum := by decide
  have hdescent : baseEnd_108193 < baseStart_108193 := by decide
  rcases family_descends (prefixWord ++ tailWord_108193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108246 : List Nat := [5, 2, 1, 3, 1, 7]
def baseStart_108246 : Nat := 118140960795 + 108246 * 2 ^ 59
def prefixEnd_108246 : Nat := 4983230072969 + 3 ^ 40 * 108246 * 2
def baseEnd_108246 : Nat := 3659735106284030994383

theorem tailTrace_108246 : CollatzResearch.WordTrace tailWord_108246 prefixEnd_108246 3659735106284030994383 := by
  unfold tailWord_108246
  simp only [CollatzResearch.WordTrace]
  refine ⟨246753497865668986880537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2632037310567135860059061 246753497865668986880537)
  ·
    refine ⟨185065123399251740160403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246753497865668986880537 185065123399251740160403)
    ·
      refine ⟨277597685098877610240605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185065123399251740160403 277597685098877610240605)
      ·
        refine ⟨104099131912079103840227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 277597685098877610240605 104099131912079103840227)
        ·
          refine ⟨156148697868118655760341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104099131912079103840227 156148697868118655760341)
          ·
            refine ⟨3659735106284030994383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 156148697868118655760341 3659735106284030994383)
            ·
              rfl

theorem cell19_108246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 7].length) (baseStart_108246 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_108246 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_108246 prefixEnd_108246 := by exact prefixLift 108246
  have htrace : WordTrace (prefixWord ++ tailWord_108246) baseStart_108246 baseEnd_108246 := by
    simpa [prefixWord, tailWord_108246, baseEnd_108246] using wordTrace_append hprefix tailTrace_108246
  have hstable : (prefixWord ++ tailWord_108246).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108246).length < 2 ^ (prefixWord ++ tailWord_108246).sum := by decide
  have hdescent : baseEnd_108246 < baseStart_108246 := by decide
  rcases family_descends (prefixWord ++ tailWord_108246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108263 : List Nat := [1, 1, 5, 4, 2, 1, 1, 4]
def baseStart_108263 : Nat := 118140960795 + 108263 * 2 ^ 59
def prefixEnd_108263 : Nat := 4983230072969 + 3 ^ 40 * 108263 * 2
def baseEnd_108263 : Nat := 32942788798705276571623

theorem tailTrace_108263 : CollatzResearch.WordTrace tailWord_108263 prefixEnd_108263 32942788798705276571623 := by
  unfold tailWord_108263
  simp only [CollatzResearch.WordTrace]
  refine ⟨3948676006789115693457443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2632450671192743795638295 3948676006789115693457443)
  ·
    refine ⟨5923014010183673540186165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3948676006789115693457443 5923014010183673540186165)
    ·
      refine ⟨555282563454719394392453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5923014010183673540186165 555282563454719394392453)
      ·
        refine ⟨104115480647759886448585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 555282563454719394392453 104115480647759886448585)
        ·
          refine ⟨78086610485819914836439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104115480647759886448585 78086610485819914836439)
          ·
            refine ⟨117129915728729872254659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78086610485819914836439 117129915728729872254659)
            ·
              refine ⟨175694873593094808381989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117129915728729872254659 175694873593094808381989)
              ·
                refine ⟨32942788798705276571623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 175694873593094808381989 32942788798705276571623)
                ·
                  rfl

theorem cell19_108263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 1, 4].length) (baseStart_108263 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_108263 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_108263 prefixEnd_108263 := by exact prefixLift 108263
  have htrace : WordTrace (prefixWord ++ tailWord_108263) baseStart_108263 baseEnd_108263 := by
    simpa [prefixWord, tailWord_108263, baseEnd_108263] using wordTrace_append hprefix tailTrace_108263
  have hstable : (prefixWord ++ tailWord_108263).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108263).length < 2 ^ (prefixWord ++ tailWord_108263).sum := by decide
  have hdescent : baseEnd_108263 < baseStart_108263 := by decide
  rcases family_descends (prefixWord ++ tailWord_108263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108341 : List Nat := [1, 3, 3, 1, 4, 2, 2, 3]
def baseStart_108341 : Nat := 118140960795 + 108341 * 2 ^ 59
def prefixEnd_108341 : Nat := 4983230072969 + 3 ^ 40 * 108341 * 2
def baseEnd_108341 : Nat := 32966523015624206838077

theorem tailTrace_108341 : CollatzResearch.WordTrace tailWord_108341 prefixEnd_108341 32966523015624206838077 := by
  unfold tailWord_108341
  simp only [CollatzResearch.WordTrace]
  refine ⟨3951520900506535014796877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2634347267004356676531251 3951520900506535014796877)
  ·
    refine ⟨1481820337689950630548829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3951520900506535014796877 1481820337689950630548829)
    ·
      refine ⟨555682626633731486455811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1481820337689950630548829 555682626633731486455811)
      ·
        refine ⟨833523939950597229683717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 555682626633731486455811 833523939950597229683717)
        ·
          refine ⟨156285738740736980565697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 833523939950597229683717 156285738740736980565697)
          ·
            refine ⟨117214304055552735424273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156285738740736980565697 117214304055552735424273)
            ·
              refine ⟨87910728041664551568205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117214304055552735424273 87910728041664551568205)
              ·
                refine ⟨32966523015624206838077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87910728041664551568205 32966523015624206838077)
                ·
                  rfl

theorem cell19_108341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 2, 3].length) (baseStart_108341 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_108341 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_108341 prefixEnd_108341 := by exact prefixLift 108341
  have htrace : WordTrace (prefixWord ++ tailWord_108341) baseStart_108341 baseEnd_108341 := by
    simpa [prefixWord, tailWord_108341, baseEnd_108341] using wordTrace_append hprefix tailTrace_108341
  have hstable : (prefixWord ++ tailWord_108341).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108341).length < 2 ^ (prefixWord ++ tailWord_108341).sum := by decide
  have hdescent : baseEnd_108341 < baseStart_108341 := by decide
  rcases family_descends (prefixWord ++ tailWord_108341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108383 : List Nat := [1, 1, 2, 3, 1, 5, 2, 4]
def baseStart_108383 : Nat := 118140960795 + 108383 * 2 ^ 59
def prefixEnd_108383 : Nat := 4983230072969 + 3 ^ 40 * 108383 * 2
def baseEnd_108383 : Nat := 32979302978580553904629

theorem tailTrace_108383 : CollatzResearch.WordTrace tailWord_108383 prefixEnd_108383 32979302978580553904629 := by
  unfold tailWord_108383
  simp only [CollatzResearch.WordTrace]
  refine ⟨3953052766354376187825803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2635368510902917458550535 3953052766354376187825803)
  ·
    refine ⟨5929579149531564281738705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3953052766354376187825803 5929579149531564281738705)
    ·
      refine ⟨4447184362148673211304029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5929579149531564281738705 4447184362148673211304029)
      ·
        refine ⟨1667694135805752454239011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4447184362148673211304029 1667694135805752454239011)
        ·
          refine ⟨2501541203708628681358517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1667694135805752454239011 2501541203708628681358517)
          ·
            refine ⟨234519487847683938877361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2501541203708628681358517 234519487847683938877361)
            ·
              refine ⟨175889615885762954158021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 234519487847683938877361 175889615885762954158021)
              ·
                refine ⟨32979302978580553904629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 175889615885762954158021 32979302978580553904629)
                ·
                  rfl

theorem cell19_108383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 2, 4].length) (baseStart_108383 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_108383 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_108383 prefixEnd_108383 := by exact prefixLift 108383
  have htrace : WordTrace (prefixWord ++ tailWord_108383) baseStart_108383 baseEnd_108383 := by
    simpa [prefixWord, tailWord_108383, baseEnd_108383] using wordTrace_append hprefix tailTrace_108383
  have hstable : (prefixWord ++ tailWord_108383).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108383).length < 2 ^ (prefixWord ++ tailWord_108383).sum := by decide
  have hdescent : baseEnd_108383 < baseStart_108383 := by decide
  rcases family_descends (prefixWord ++ tailWord_108383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108423 : List Nat := [1, 1, 4, 2, 11]
def baseStart_108423 : Nat := 118140960795 + 108423 * 2 ^ 59
def prefixEnd_108423 : Nat := 4983230072969 + 3 ^ 40 * 108423 * 2
def baseEnd_108423 : Nat := 1221906458217493074653

theorem tailTrace_108423 : CollatzResearch.WordTrace tailWord_108423 prefixEnd_108423 1221906458217493074653 := by
  unfold tailWord_108423
  simp only [CollatzResearch.WordTrace]
  refine ⟨3954511686209463019281923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2636341124139642012854615 3954511686209463019281923)
  ·
    refine ⟨5931767529314194528922885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3954511686209463019281923 5931767529314194528922885)
    ·
      refine ⟨1112206411746411474173041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5931767529314194528922885 1112206411746411474173041)
      ·
        refine ⟨834154808809808605629781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1112206411746411474173041 834154808809808605629781)
        ·
          refine ⟨1221906458217493074653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 834154808809808605629781 1221906458217493074653)
          ·
            rfl

theorem cell19_108423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 11].length) (baseStart_108423 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_108423 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_108423 prefixEnd_108423 := by exact prefixLift 108423
  have htrace : WordTrace (prefixWord ++ tailWord_108423) baseStart_108423 baseEnd_108423 := by
    simpa [prefixWord, tailWord_108423, baseEnd_108423] using wordTrace_append hprefix tailTrace_108423
  have hstable : (prefixWord ++ tailWord_108423).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108423).length < 2 ^ (prefixWord ++ tailWord_108423).sum := by decide
  have hdescent : baseEnd_108423 < baseStart_108423 := by decide
  rcases family_descends (prefixWord ++ tailWord_108423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108476 : List Nat := [2, 2, 2, 5, 1, 1, 6]
def baseStart_108476 : Nat := 118140960795 + 108476 * 2 ^ 59
def prefixEnd_108476 : Nat := 4983230072969 + 3 ^ 40 * 108476 * 2
def baseEnd_108476 : Nat := 11002533822661297945903

theorem tailTrace_108476 : CollatzResearch.WordTrace tailWord_108476 prefixEnd_108476 11002533822661297945903 := by
  unfold tailWord_108476
  simp only [CollatzResearch.WordTrace]
  refine ⟨1978222377508726535480641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2637629836678302047307521 1978222377508726535480641)
  ·
    refine ⟨1483666783131544901610481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1978222377508726535480641 1483666783131544901610481)
    ·
      refine ⟨1112750087348658676207861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1483666783131544901610481 1112750087348658676207861)
      ·
        refine ⟨104320320688936750894487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1112750087348658676207861 104320320688936750894487)
        ·
          refine ⟨156480481033405126341731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104320320688936750894487 156480481033405126341731)
          ·
            refine ⟨234720721550107689512597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156480481033405126341731 234720721550107689512597)
            ·
              refine ⟨11002533822661297945903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 234720721550107689512597 11002533822661297945903)
              ·
                rfl

theorem cell19_108476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 6].length) (baseStart_108476 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_108476 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_108476 prefixEnd_108476 := by exact prefixLift 108476
  have htrace : WordTrace (prefixWord ++ tailWord_108476) baseStart_108476 baseEnd_108476 := by
    simpa [prefixWord, tailWord_108476, baseEnd_108476] using wordTrace_append hprefix tailTrace_108476
  have hstable : (prefixWord ++ tailWord_108476).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108476).length < 2 ^ (prefixWord ++ tailWord_108476).sum := by decide
  have hdescent : baseEnd_108476 < baseStart_108476 := by decide
  rcases family_descends (prefixWord ++ tailWord_108476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108478 : List Nat := [4, 2, 1, 1, 1, 4, 6]
def baseStart_108478 : Nat := 118140960795 + 108478 * 2 ^ 59
def prefixEnd_108478 : Nat := 4983230072969 + 3 ^ 40 * 108478 * 2
def baseEnd_108478 : Nat := 11002736679216160597753

theorem tailTrace_108478 : CollatzResearch.WordTrace tailWord_108478 prefixEnd_108478 11002736679216160597753 := by
  unfold tailWord_108478
  simp only [CollatzResearch.WordTrace]
  refine ⟨494564712626275926566761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2637678467340138275022725 494564712626275926566761)
  ·
    refine ⟨370923534469706944925071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 494564712626275926566761 370923534469706944925071)
    ·
      refine ⟨556385301704560417387607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 370923534469706944925071 556385301704560417387607)
      ·
        refine ⟨834577952556840626081411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 556385301704560417387607 834577952556840626081411)
        ·
          refine ⟨1251866928835260939122117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 834577952556840626081411 1251866928835260939122117)
          ·
            refine ⟨234725049156611426085397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1251866928835260939122117 234725049156611426085397)
            ·
              refine ⟨11002736679216160597753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 234725049156611426085397 11002736679216160597753)
              ·
                rfl

theorem cell19_108478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 6].length) (baseStart_108478 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_108478 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_108478 prefixEnd_108478 := by exact prefixLift 108478
  have htrace : WordTrace (prefixWord ++ tailWord_108478) baseStart_108478 baseEnd_108478 := by
    simpa [prefixWord, tailWord_108478, baseEnd_108478] using wordTrace_append hprefix tailTrace_108478
  have hstable : (prefixWord ++ tailWord_108478).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108478).length < 2 ^ (prefixWord ++ tailWord_108478).sum := by decide
  have hdescent : baseEnd_108478 < baseStart_108478 := by decide
  rcases family_descends (prefixWord ++ tailWord_108478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108480 : List Nat := [2, 1, 1, 2, 3, 2, 8]
def baseStart_108480 : Nat := 118140960795 + 108480 * 2 ^ 59
def prefixEnd_108480 : Nat := 4983230072969 + 3 ^ 40 * 108480 * 2
def baseEnd_108480 : Nat := 11002939535771023249603

theorem tailTrace_108480 : CollatzResearch.WordTrace tailWord_108480 prefixEnd_108480 11002939535771023249603 := by
  unfold tailWord_108480
  simp only [CollatzResearch.WordTrace]
  refine ⟨1978295323501480877053447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2637727098001974502737929 1978295323501480877053447)
  ·
    refine ⟨2967442985252221315580171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1978295323501480877053447 2967442985252221315580171)
    ·
      refine ⟨4451164477878331973370257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2967442985252221315580171 4451164477878331973370257)
      ·
        refine ⟨3338373358408748980027693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4451164477878331973370257 3338373358408748980027693)
        ·
          refine ⟨1251890009403280867510385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3338373358408748980027693 1251890009403280867510385)
          ·
            refine ⟨938917507052460650632789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1251890009403280867510385 938917507052460650632789)
            ·
              refine ⟨11002939535771023249603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 938917507052460650632789 11002939535771023249603)
              ·
                rfl

theorem cell19_108480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 8].length) (baseStart_108480 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_108480 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_108480 prefixEnd_108480 := by exact prefixLift 108480
  have htrace : WordTrace (prefixWord ++ tailWord_108480) baseStart_108480 baseEnd_108480 := by
    simpa [prefixWord, tailWord_108480, baseEnd_108480] using wordTrace_append hprefix tailTrace_108480
  have hstable : (prefixWord ++ tailWord_108480).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108480).length < 2 ^ (prefixWord ++ tailWord_108480).sum := by decide
  have hdescent : baseEnd_108480 < baseStart_108480 := by decide
  rcases family_descends (prefixWord ++ tailWord_108480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108508 : List Nat := [2, 2, 6, 1, 1, 2, 2, 3]
def baseStart_108508 : Nat := 118140960795 + 108508 * 2 ^ 59
def prefixEnd_108508 : Nat := 4983230072969 + 3 ^ 40 * 108508 * 2
def baseEnd_108508 : Nat := 33017338582617301126511

theorem tailTrace_108508 : CollatzResearch.WordTrace tailWord_108508 prefixEnd_108508 33017338582617301126511 := by
  unfold tailWord_108508
  simp only [CollatzResearch.WordTrace]
  refine ⟨1978805945450761268063089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2638407927267681690750785 1978805945450761268063089)
  ·
    refine ⟨1484104459088070951047317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1978805945450761268063089 1484104459088070951047317)
    ·
      refine ⟨69567396519753325830343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 1484104459088070951047317 69567396519753325830343)
      ·
        refine ⟨104351094779629988745515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69567396519753325830343 104351094779629988745515)
        ·
          refine ⟨156526642169444983118273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104351094779629988745515 156526642169444983118273)
          ·
            refine ⟨117394981627083737338705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156526642169444983118273 117394981627083737338705)
            ·
              refine ⟨88046236220312803004029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117394981627083737338705 88046236220312803004029)
              ·
                refine ⟨33017338582617301126511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88046236220312803004029 33017338582617301126511)
                ·
                  rfl

theorem cell19_108508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 2, 3].length) (baseStart_108508 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_108508 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_108508 prefixEnd_108508 := by exact prefixLift 108508
  have htrace : WordTrace (prefixWord ++ tailWord_108508) baseStart_108508 baseEnd_108508 := by
    simpa [prefixWord, tailWord_108508, baseEnd_108508] using wordTrace_append hprefix tailTrace_108508
  have hstable : (prefixWord ++ tailWord_108508).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108508).length < 2 ^ (prefixWord ++ tailWord_108508).sum := by decide
  have hdescent : baseEnd_108508 < baseStart_108508 := by decide
  rcases family_descends (prefixWord ++ tailWord_108508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108537 : List Nat := [1, 2, 1, 3, 1, 4, 7]
def baseStart_108537 : Nat := 118140960795 + 108537 * 2 ^ 59
def prefixEnd_108537 : Nat := 4983230072969 + 3 ^ 40 * 108537 * 2
def baseEnd_108537 : Nat := 11008720947584608827329

theorem tailTrace_108537 : CollatzResearch.WordTrace tailWord_108537 prefixEnd_108537 11008720947584608827329 := by
  unfold tailWord_108537
  simp only [CollatzResearch.WordTrace]
  refine ⟨3958669607796460488931865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2639113071864306992621243 3958669607796460488931865)
  ·
    refine ⟨2969002205847345366698899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3958669607796460488931865 2969002205847345366698899)
    ·
      refine ⟨4453503308771018050048349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2969002205847345366698899 4453503308771018050048349)
      ·
        refine ⟨1670063740789131768768131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4453503308771018050048349 1670063740789131768768131)
        ·
          refine ⟨2505095611183697653152197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1670063740789131768768131 2505095611183697653152197)
          ·
            refine ⟨469705427096943309966037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2505095611183697653152197 469705427096943309966037)
            ·
              refine ⟨11008720947584608827329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 469705427096943309966037 11008720947584608827329)
              ·
                rfl

theorem cell19_108537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 7].length) (baseStart_108537 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_108537 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_108537 prefixEnd_108537 := by exact prefixLift 108537
  have htrace : WordTrace (prefixWord ++ tailWord_108537) baseStart_108537 baseEnd_108537 := by
    simpa [prefixWord, tailWord_108537, baseEnd_108537] using wordTrace_append hprefix tailTrace_108537
  have hstable : (prefixWord ++ tailWord_108537).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108537).length < 2 ^ (prefixWord ++ tailWord_108537).sum := by decide
  have hdescent : baseEnd_108537 < baseStart_108537 := by decide
  rcases family_descends (prefixWord ++ tailWord_108537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108573 : List Nat := [1, 4, 2, 2, 2, 1, 2, 5]
def baseStart_108573 : Nat := 118140960795 + 108573 * 2 ^ 59
def prefixEnd_108573 : Nat := 4983230072969 + 3 ^ 40 * 108573 * 2
def baseEnd_108573 : Nat := 33037117096716409681889

theorem tailTrace_108573 : CollatzResearch.WordTrace tailWord_108573 prefixEnd_108573 33037117096716409681889 := by
  unfold tailWord_108573
  simp only [CollatzResearch.WordTrace]
  refine ⟨3959982635666038637242373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2639988423777359091494915 3959982635666038637242373)
  ·
    refine ⟨742496744187382244482945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3959982635666038637242373 742496744187382244482945)
    ·
      refine ⟨556872558140536683362209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 742496744187382244482945 556872558140536683362209)
      ·
        refine ⟨417654418605402512521657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 556872558140536683362209 417654418605402512521657)
        ·
          refine ⟨313240813954051884391243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 417654418605402512521657 313240813954051884391243)
          ·
            refine ⟨469861220931077826586865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 313240813954051884391243 469861220931077826586865)
            ·
              refine ⟨352395915698308369940149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 469861220931077826586865 352395915698308369940149)
              ·
                refine ⟨33037117096716409681889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 352395915698308369940149 33037117096716409681889)
                ·
                  rfl

theorem cell19_108573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 5].length) (baseStart_108573 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_108573 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_108573 prefixEnd_108573 := by exact prefixLift 108573
  have htrace : WordTrace (prefixWord ++ tailWord_108573) baseStart_108573 baseEnd_108573 := by
    simpa [prefixWord, tailWord_108573, baseEnd_108573] using wordTrace_append hprefix tailTrace_108573
  have hstable : (prefixWord ++ tailWord_108573).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108573).length < 2 ^ (prefixWord ++ tailWord_108573).sum := by decide
  have hdescent : baseEnd_108573 < baseStart_108573 := by decide
  rcases family_descends (prefixWord ++ tailWord_108573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108575 : List Nat := [1, 1, 2, 4, 1, 2, 1, 7]
def baseStart_108575 : Nat := 118140960795 + 108575 * 2 ^ 59
def prefixEnd_108575 : Nat := 4983230072969 + 3 ^ 40 * 108575 * 2
def baseEnd_108575 : Nat := 33037725666380997637439

theorem tailTrace_108575 : CollatzResearch.WordTrace tailWord_108575 prefixEnd_108575 33037725666380997637439 := by
  unfold tailWord_108575
  simp only [CollatzResearch.WordTrace]
  refine ⟨3960055581658792978815179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2640037054439195319210119 3960055581658792978815179)
  ·
    refine ⟨5940083372488189468222769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3960055581658792978815179 5940083372488189468222769)
    ·
      refine ⟨4455062529366142101167077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5940083372488189468222769 4455062529366142101167077)
      ·
        refine ⟨835324224256151643968827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4455062529366142101167077 835324224256151643968827)
        ·
          refine ⟨1252986336384227465953241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 835324224256151643968827 1252986336384227465953241)
          ·
            refine ⟨939739752288170599464931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1252986336384227465953241 939739752288170599464931)
            ·
              refine ⟨1409609628432255899197397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 939739752288170599464931 1409609628432255899197397)
              ·
                refine ⟨33037725666380997637439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1409609628432255899197397 33037725666380997637439)
                ·
                  rfl

theorem cell19_108575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 7].length) (baseStart_108575 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_108575 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_108575 prefixEnd_108575 := by exact prefixLift 108575
  have htrace : WordTrace (prefixWord ++ tailWord_108575) baseStart_108575 baseEnd_108575 := by
    simpa [prefixWord, tailWord_108575, baseEnd_108575] using wordTrace_append hprefix tailTrace_108575
  have hstable : (prefixWord ++ tailWord_108575).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108575).length < 2 ^ (prefixWord ++ tailWord_108575).sum := by decide
  have hdescent : baseEnd_108575 < baseStart_108575 := by decide
  rcases family_descends (prefixWord ++ tailWord_108575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108594 : List Nat := [3, 2, 1, 1, 2, 10]
def baseStart_108594 : Nat := 118140960795 + 108594 * 2 ^ 59
def prefixEnd_108594 : Nat := 4983230072969 + 3 ^ 40 * 108594 * 2
def baseEnd_108594 : Nat := 3671500786466064801685

theorem tailTrace_108594 : CollatzResearch.WordTrace tailWord_108594 prefixEnd_108594 3671500786466064801685 := by
  unfold tailWord_108594
  simp only [CollatzResearch.WordTrace]
  refine ⟨990187142147489805939209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2640499045726639482504557 990187142147489805939209)
  ·
    refine ⟨742640356610617354454407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 990187142147489805939209 742640356610617354454407)
    ·
      refine ⟨1113960534915926031681611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 742640356610617354454407 1113960534915926031681611)
      ·
        refine ⟨1670940802373889047522417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1113960534915926031681611 1670940802373889047522417)
        ·
          refine ⟨1253205601780416785641813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1670940802373889047522417 1253205601780416785641813)
          ·
            refine ⟨3671500786466064801685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1253205601780416785641813 3671500786466064801685)
            ·
              rfl

theorem cell19_108594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 10].length) (baseStart_108594 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_108594 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_108594 prefixEnd_108594 := by exact prefixLift 108594
  have htrace : WordTrace (prefixWord ++ tailWord_108594) baseStart_108594 baseEnd_108594 := by
    simpa [prefixWord, tailWord_108594, baseEnd_108594] using wordTrace_append hprefix tailTrace_108594
  have hstable : (prefixWord ++ tailWord_108594).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108594).length < 2 ^ (prefixWord ++ tailWord_108594).sum := by decide
  have hdescent : baseEnd_108594 < baseStart_108594 := by decide
  rcases family_descends (prefixWord ++ tailWord_108594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108609 : List Nat := [1, 2, 5, 1, 2, 3, 1, 4]
def baseStart_108609 : Nat := 118140960795 + 108609 * 2 ^ 59
def prefixEnd_108609 : Nat := 4983230072969 + 3 ^ 40 * 108609 * 2
def baseEnd_108609 : Nat := 33048071350678992881791

theorem tailTrace_108609 : CollatzResearch.WordTrace tailWord_108609 prefixEnd_108609 33048071350678992881791 := by
  unfold tailWord_108609
  simp only [CollatzResearch.WordTrace]
  refine ⟨3961295663535616785552881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2640863775690411190368587 3961295663535616785552881)
  ·
    refine ⟨2970971747651712589164661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3961295663535616785552881 2970971747651712589164661)
    ·
      refine ⟨278528601342348055234187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2970971747651712589164661 278528601342348055234187)
      ·
        refine ⟨417792902013522082851281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278528601342348055234187 417792902013522082851281)
        ·
          refine ⟨313344676510141562138461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 417792902013522082851281 313344676510141562138461)
          ·
            refine ⟨117504253691303085801923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 313344676510141562138461 117504253691303085801923)
            ·
              refine ⟨176256380536954628702885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117504253691303085801923 176256380536954628702885)
              ·
                refine ⟨33048071350678992881791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 176256380536954628702885 33048071350678992881791)
                ·
                  rfl

theorem cell19_108609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 1, 4].length) (baseStart_108609 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_108609 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_108609 prefixEnd_108609 := by exact prefixLift 108609
  have htrace : WordTrace (prefixWord ++ tailWord_108609) baseStart_108609 baseEnd_108609 := by
    simpa [prefixWord, tailWord_108609, baseEnd_108609] using wordTrace_append hprefix tailTrace_108609
  have hstable : (prefixWord ++ tailWord_108609).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108609).length < 2 ^ (prefixWord ++ tailWord_108609).sum := by decide
  have hdescent : baseEnd_108609 < baseStart_108609 := by decide
  rcases family_descends (prefixWord ++ tailWord_108609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108702 : List Nat := [4, 3, 1, 1, 4, 1, 5]
def baseStart_108702 : Nat := 118140960795 + 108702 * 2 ^ 59
def prefixEnd_108702 : Nat := 4983230072969 + 3 ^ 40 * 108702 * 2
def baseEnd_108702 : Nat := 11025456613360777604957

theorem tailTrace_108702 : CollatzResearch.WordTrace tailWord_108702 prefixEnd_108702 11025456613360777604957 := by
  unfold tailWord_108702
  simp only [CollatzResearch.WordTrace]
  refine ⟨495585956524836708586045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2643125101465795779125573 495585956524836708586045)
  ·
    refine ⟨185844733696813765719767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 495585956524836708586045 185844733696813765719767)
    ·
      refine ⟨278767100545220648579651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185844733696813765719767 278767100545220648579651)
      ·
        refine ⟨418150650817830972869477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278767100545220648579651 418150650817830972869477)
        ·
          refine ⟨78403247028343307413027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 418150650817830972869477 78403247028343307413027)
          ·
            refine ⟨117604870542514961119541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78403247028343307413027 117604870542514961119541)
            ·
              refine ⟨11025456613360777604957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 117604870542514961119541 11025456613360777604957)
              ·
                rfl

theorem cell19_108702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 5].length) (baseStart_108702 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_108702 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_108702 prefixEnd_108702 := by exact prefixLift 108702
  have htrace : WordTrace (prefixWord ++ tailWord_108702) baseStart_108702 baseEnd_108702 := by
    simpa [prefixWord, tailWord_108702, baseEnd_108702] using wordTrace_append hprefix tailTrace_108702
  have hstable : (prefixWord ++ tailWord_108702).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108702).length < 2 ^ (prefixWord ++ tailWord_108702).sum := by decide
  have hdescent : baseEnd_108702 < baseStart_108702 := by decide
  rcases family_descends (prefixWord ++ tailWord_108702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108706 : List Nat := [3, 3, 1, 3, 1, 1, 7]
def baseStart_108706 : Nat := 118140960795 + 108706 * 2 ^ 59
def prefixEnd_108706 : Nat := 4983230072969 + 3 ^ 40 * 108706 * 2
def baseEnd_108706 : Nat := 11025862326470502908657

theorem tailTrace_108706 : CollatzResearch.WordTrace tailWord_108706 prefixEnd_108706 11025862326470502908657 := by
  unfold tailWord_108706
  simp only [CollatzResearch.WordTrace]
  refine ⟨991208386046050587958493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2643222362789468234555981 991208386046050587958493)
  ·
    refine ⟨371703144767268970484435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 991208386046050587958493 371703144767268970484435)
    ·
      refine ⟨557554717150903455726653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 371703144767268970484435 557554717150903455726653)
      ·
        refine ⟨209083018931588795897495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 557554717150903455726653 209083018931588795897495)
        ·
          refine ⟨313624528397383193846243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209083018931588795897495 313624528397383193846243)
          ·
            refine ⟨470436792596074790769365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 313624528397383193846243 470436792596074790769365)
            ·
              refine ⟨11025862326470502908657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 470436792596074790769365 11025862326470502908657)
              ·
                rfl

theorem cell19_108706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 7].length) (baseStart_108706 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_108706 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_108706 prefixEnd_108706 := by exact prefixLift 108706
  have htrace : WordTrace (prefixWord ++ tailWord_108706) baseStart_108706 baseEnd_108706 := by
    simpa [prefixWord, tailWord_108706, baseEnd_108706] using wordTrace_append hprefix tailTrace_108706
  have hstable : (prefixWord ++ tailWord_108706).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108706).length < 2 ^ (prefixWord ++ tailWord_108706).sum := by decide
  have hdescent : baseEnd_108706 < baseStart_108706 := by decide
  rcases family_descends (prefixWord ++ tailWord_108706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108727 : List Nat := [1, 1, 3, 1, 4, 2, 1, 6]
def baseStart_108727 : Nat := 118140960795 + 108727 * 2 ^ 59
def prefixEnd_108727 : Nat := 4983230072969 + 3 ^ 40 * 108727 * 2
def baseEnd_108727 : Nat := 33083976960889682259247

theorem tailTrace_108727 : CollatzResearch.WordTrace tailWord_108727 prefixEnd_108727 33083976960889682259247 := by
  unfold tailWord_108727
  simp only [CollatzResearch.WordTrace]
  refine ⟨3965599477108122938348435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2643732984738748625565623 3965599477108122938348435)
  ·
    refine ⟨5948399215662184407522653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3965599477108122938348435 5948399215662184407522653)
    ·
      refine ⟨2230649705873319152820995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5948399215662184407522653 2230649705873319152820995)
      ·
        refine ⟨3345974558809978729231493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2230649705873319152820995 3345974558809978729231493)
        ·
          refine ⟨627370229776871011730905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3345974558809978729231493 627370229776871011730905)
          ·
            refine ⟨470527672332653258798179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 627370229776871011730905 470527672332653258798179)
            ·
              refine ⟨705791508498979888197269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 470527672332653258798179 705791508498979888197269)
              ·
                refine ⟨33083976960889682259247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 705791508498979888197269 33083976960889682259247)
                ·
                  rfl

theorem cell19_108727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 6].length) (baseStart_108727 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_108727 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_108727 prefixEnd_108727 := by exact prefixLift 108727
  have htrace : WordTrace (prefixWord ++ tailWord_108727) baseStart_108727 baseEnd_108727 := by
    simpa [prefixWord, tailWord_108727, baseEnd_108727] using wordTrace_append hprefix tailTrace_108727
  have hstable : (prefixWord ++ tailWord_108727).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108727).length < 2 ^ (prefixWord ++ tailWord_108727).sum := by decide
  have hdescent : baseEnd_108727 < baseStart_108727 := by decide
  rcases family_descends (prefixWord ++ tailWord_108727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108746 : List Nat := [3, 1, 2, 1, 3, 1, 1, 7]
def baseStart_108746 : Nat := 118140960795 + 108746 * 2 ^ 59
def prefixEnd_108746 : Nat := 4983230072969 + 3 ^ 40 * 108746 * 2
def baseEnd_108746 : Nat := 33089758372703267836973

theorem tailTrace_108746 : CollatzResearch.WordTrace tailWord_108746 prefixEnd_108746 33089758372703267836973 := by
  unfold tailWord_108746
  simp only [CollatzResearch.WordTrace]
  refine ⟨991573116009822295822523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2644194976026192788860061 991573116009822295822523)
  ·
    refine ⟨1487359674014733443733785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 991573116009822295822523 1487359674014733443733785)
    ·
      refine ⟨1115519755511050082800339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1487359674014733443733785 1115519755511050082800339)
      ·
        refine ⟨1673279633266575124200509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1115519755511050082800339 1673279633266575124200509)
        ·
          refine ⟨627479862474965671575191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1673279633266575124200509 627479862474965671575191)
          ·
            refine ⟨941219793712448507362787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 627479862474965671575191 941219793712448507362787)
            ·
              refine ⟨1411829690568672761044181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 941219793712448507362787 1411829690568672761044181)
              ·
                refine ⟨33089758372703267836973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1411829690568672761044181 33089758372703267836973)
                ·
                  rfl

theorem cell19_108746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 7].length) (baseStart_108746 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_108746 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_108746 prefixEnd_108746 := by exact prefixLift 108746
  have htrace : WordTrace (prefixWord ++ tailWord_108746) baseStart_108746 baseEnd_108746 := by
    simpa [prefixWord, tailWord_108746, baseEnd_108746] using wordTrace_append hprefix tailTrace_108746
  have hstable : (prefixWord ++ tailWord_108746).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108746).length < 2 ^ (prefixWord ++ tailWord_108746).sum := by decide
  have hdescent : baseEnd_108746 < baseStart_108746 := by decide
  rcases family_descends (prefixWord ++ tailWord_108746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108801 : List Nat := [1, 2, 4, 1, 1, 2, 5, 3]
def baseStart_108801 : Nat := 118140960795 + 108801 * 2 ^ 59
def prefixEnd_108801 : Nat := 4983230072969 + 3 ^ 40 * 108801 * 2
def baseEnd_108801 : Nat := 33106494038479436614601

theorem tailTrace_108801 : CollatzResearch.WordTrace tailWord_108801 prefixEnd_108801 33106494038479436614601 := by
  unfold tailWord_108801
  simp only [CollatzResearch.WordTrace]
  refine ⟨3968298478840033576542257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2645532319226689051028171 3968298478840033576542257)
  ·
    refine ⟨2976223859130025182406693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3968298478840033576542257 2976223859130025182406693)
    ·
      refine ⟨558041973586879721701255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2976223859130025182406693 558041973586879721701255)
      ·
        refine ⟨837062960380319582551883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 558041973586879721701255 837062960380319582551883)
        ·
          refine ⟨1255594440570479373827825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 837062960380319582551883 1255594440570479373827825)
          ·
            refine ⟨941695830427859530370869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1255594440570479373827825 941695830427859530370869)
            ·
              refine ⟨88283984102611830972269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 941695830427859530370869 88283984102611830972269)
              ·
                refine ⟨33106494038479436614601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88283984102611830972269 33106494038479436614601)
                ·
                  rfl

theorem cell19_108801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 5, 3].length) (baseStart_108801 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_108801 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_108801 prefixEnd_108801 := by exact prefixLift 108801
  have htrace : WordTrace (prefixWord ++ tailWord_108801) baseStart_108801 baseEnd_108801 := by
    simpa [prefixWord, tailWord_108801, baseEnd_108801] using wordTrace_append hprefix tailTrace_108801
  have hstable : (prefixWord ++ tailWord_108801).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108801).length < 2 ^ (prefixWord ++ tailWord_108801).sum := by decide
  have hdescent : baseEnd_108801 < baseStart_108801 := by decide
  rcases family_descends (prefixWord ++ tailWord_108801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108858 : List Nat := [3, 1, 1, 1, 4, 2, 4, 3]
def baseStart_108858 : Nat := 118140960795 + 108858 * 2 ^ 59
def prefixEnd_108858 : Nat := 4983230072969 + 3 ^ 40 * 108858 * 2
def baseEnd_108858 : Nat := 33123838273920193347779

theorem tailTrace_108858 : CollatzResearch.WordTrace tailWord_108858 prefixEnd_108858 33123838273920193347779 := by
  unfold tailWord_108858
  simp only [CollatzResearch.WordTrace]
  refine ⟨992594359908383077841807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2646918293089021540911485 992594359908383077841807)
  ·
    refine ⟨1488891539862574616762711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 992594359908383077841807 1488891539862574616762711)
    ·
      refine ⟨2233337309793861925144067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1488891539862574616762711 2233337309793861925144067)
      ·
        refine ⟨3350005964690792887716101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2233337309793861925144067 3350005964690792887716101)
        ·
          refine ⟨628126118379523666446769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3350005964690792887716101 628126118379523666446769)
          ·
            refine ⟨471094588784642749835077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 628126118379523666446769 471094588784642749835077)
            ·
              refine ⟨88330235397120515594077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 471094588784642749835077 88330235397120515594077)
              ·
                refine ⟨33123838273920193347779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88330235397120515594077 33123838273920193347779)
                ·
                  rfl

theorem cell19_108858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 4, 3].length) (baseStart_108858 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_108858 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_108858 prefixEnd_108858 := by exact prefixLift 108858
  have htrace : WordTrace (prefixWord ++ tailWord_108858) baseStart_108858 baseEnd_108858 := by
    simpa [prefixWord, tailWord_108858, baseEnd_108858] using wordTrace_append hprefix tailTrace_108858
  have hstable : (prefixWord ++ tailWord_108858).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108858).length < 2 ^ (prefixWord ++ tailWord_108858).sum := by decide
  have hdescent : baseEnd_108858 < baseStart_108858 := by decide
  rcases family_descends (prefixWord ++ tailWord_108858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108860 : List Nat := [2, 2, 2, 2, 1, 2, 3, 5]
def baseStart_108860 : Nat := 118140960795 + 108860 * 2 ^ 59
def prefixEnd_108860 : Nat := 4983230072969 + 3 ^ 40 * 108860 * 2
def baseEnd_108860 : Nat := 33124446843584781303329

theorem tailTrace_108860 : CollatzResearch.WordTrace tailWord_108860 prefixEnd_108860 33124446843584781303329 := by
  unfold tailWord_108860
  simp only [CollatzResearch.WordTrace]
  refine ⟨1985225192813143326470017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2646966923750857768626689 1985225192813143326470017)
  ·
    refine ⟨1488918894609857494852513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1985225192813143326470017 1488918894609857494852513)
    ·
      refine ⟨1116689170957393121139385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1488918894609857494852513 1116689170957393121139385)
      ·
        refine ⟨837516878218044840854539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1116689170957393121139385 837516878218044840854539)
        ·
          refine ⟨1256275317327067261281809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 837516878218044840854539 1256275317327067261281809)
          ·
            refine ⟨942206487995300445961357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1256275317327067261281809 942206487995300445961357)
            ·
              refine ⟨353327432998237667235509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 942206487995300445961357 353327432998237667235509)
              ·
                refine ⟨33124446843584781303329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 353327432998237667235509 33124446843584781303329)
                ·
                  rfl

theorem cell19_108860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 5].length) (baseStart_108860 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_108860 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_108860 prefixEnd_108860 := by exact prefixLift 108860
  have htrace : WordTrace (prefixWord ++ tailWord_108860) baseStart_108860 baseEnd_108860 := by
    simpa [prefixWord, tailWord_108860, baseEnd_108860] using wordTrace_append hprefix tailTrace_108860
  have hstable : (prefixWord ++ tailWord_108860).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108860).length < 2 ^ (prefixWord ++ tailWord_108860).sum := by decide
  have hdescent : baseEnd_108860 < baseStart_108860 := by decide
  rcases family_descends (prefixWord ++ tailWord_108860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108896 : List Nat := [2, 1, 1, 3, 5, 1, 2, 4]
def baseStart_108896 : Nat := 118140960795 + 108896 * 2 ^ 59
def prefixEnd_108896 : Nat := 4983230072969 + 3 ^ 40 * 108896 * 2
def baseEnd_108896 : Nat := 33135401097547364503231

theorem tailTrace_108896 : CollatzResearch.WordTrace tailWord_108896 prefixEnd_108896 33135401097547364503231 := by
  unfold tailWord_108896
  simp only [CollatzResearch.WordTrace]
  refine ⟨1985881706747932400625271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2647842275663909867500361 1985881706747932400625271)
  ·
    refine ⟨2978822560121898600937907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1985881706747932400625271 2978822560121898600937907)
    ·
      refine ⟨4468233840182847901406861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2978822560121898600937907 4468233840182847901406861)
      ·
        refine ⟨1675587690068567963027573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4468233840182847901406861 1675587690068567963027573)
        ·
          refine ⟨157086345943928246533835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1675587690068567963027573 157086345943928246533835)
          ·
            refine ⟨235629518915892369800753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157086345943928246533835 235629518915892369800753)
            ·
              refine ⟨176722139186919277350565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 235629518915892369800753 176722139186919277350565)
              ·
                refine ⟨33135401097547364503231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 176722139186919277350565 33135401097547364503231)
                ·
                  rfl

theorem cell19_108896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 2, 4].length) (baseStart_108896 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_108896 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_108896 prefixEnd_108896 := by exact prefixLift 108896
  have htrace : WordTrace (prefixWord ++ tailWord_108896) baseStart_108896 baseEnd_108896 := by
    simpa [prefixWord, tailWord_108896, baseEnd_108896] using wordTrace_append hprefix tailTrace_108896
  have hstable : (prefixWord ++ tailWord_108896).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108896).length < 2 ^ (prefixWord ++ tailWord_108896).sum := by decide
  have hdescent : baseEnd_108896 < baseStart_108896 := by decide
  rcases family_descends (prefixWord ++ tailWord_108896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109027 : List Nat := [1, 1, 1, 6, 3, 2, 2, 3]
def baseStart_109027 : Nat := 118140960795 + 109027 * 2 ^ 59
def prefixEnd_109027 : Nat := 4983230072969 + 3 ^ 40 * 109027 * 2
def baseEnd_109027 : Nat := 33175262410577875591763

theorem tailTrace_109027 : CollatzResearch.WordTrace tailWord_109027 prefixEnd_109027 33175262410577875591763 := by
  unfold tailWord_109027
  simp only [CollatzResearch.WordTrace]
  refine ⟨3976541376021274174269335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2651027584014182782846223 3976541376021274174269335)
  ·
    refine ⟨5964812064031911261404003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3976541376021274174269335 5964812064031911261404003)
    ·
      refine ⟨8947218096047866892106005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5964812064031911261404003 8947218096047866892106005)
      ·
        refine ⟨419400848252243760567469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 8947218096047866892106005 419400848252243760567469)
        ·
          refine ⟨157275318094591410212801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 419400848252243760567469 157275318094591410212801)
          ·
            refine ⟨117956488570943557659601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157275318094591410212801 117956488570943557659601)
            ·
              refine ⟨88467366428207668244701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117956488570943557659601 88467366428207668244701)
              ·
                refine ⟨33175262410577875591763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88467366428207668244701 33175262410577875591763)
                ·
                  rfl

theorem cell19_109027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 2, 3].length) (baseStart_109027 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_109027 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_109027 prefixEnd_109027 := by exact prefixLift 109027
  have htrace : WordTrace (prefixWord ++ tailWord_109027) baseStart_109027 baseEnd_109027 := by
    simpa [prefixWord, tailWord_109027, baseEnd_109027] using wordTrace_append hprefix tailTrace_109027
  have hstable : (prefixWord ++ tailWord_109027).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109027).length < 2 ^ (prefixWord ++ tailWord_109027).sum := by decide
  have hdescent : baseEnd_109027 < baseStart_109027 := by decide
  rcases family_descends (prefixWord ++ tailWord_109027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109029 : List Nat := [1, 3, 1, 5, 2, 1, 1, 5]
def baseStart_109029 : Nat := 118140960795 + 109029 * 2 ^ 59
def prefixEnd_109029 : Nat := 4983230072969 + 3 ^ 40 * 109029 * 2
def baseEnd_109029 : Nat := 33175870980242463547313

theorem tailTrace_109029 : CollatzResearch.WordTrace tailWord_109029 prefixEnd_109029 33175870980242463547313 := by
  unfold tailWord_109029
  simp only [CollatzResearch.WordTrace]
  refine ⟨3976614322014028515842141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2651076214676019010561427 3976614322014028515842141)
  ·
    refine ⟨1491230370755260693440803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3976614322014028515842141 1491230370755260693440803)
    ·
      refine ⟨2236845556132891040161205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1491230370755260693440803 2236845556132891040161205)
      ·
        refine ⟨209704270887458535015113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2236845556132891040161205 209704270887458535015113)
        ·
          refine ⟨157278203165593901261335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 209704270887458535015113 157278203165593901261335)
          ·
            refine ⟨235917304748390851892003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157278203165593901261335 235917304748390851892003)
            ·
              refine ⟨353875957122586277838005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 235917304748390851892003 353875957122586277838005)
              ·
                refine ⟨33175870980242463547313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 353875957122586277838005 33175870980242463547313)
                ·
                  rfl

theorem cell19_109029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 5].length) (baseStart_109029 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_109029 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_109029 prefixEnd_109029 := by exact prefixLift 109029
  have htrace : WordTrace (prefixWord ++ tailWord_109029) baseStart_109029 baseEnd_109029 := by
    simpa [prefixWord, tailWord_109029, baseEnd_109029] using wordTrace_append hprefix tailTrace_109029
  have hstable : (prefixWord ++ tailWord_109029).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109029).length < 2 ^ (prefixWord ++ tailWord_109029).sum := by decide
  have hdescent : baseEnd_109029 < baseStart_109029 := by decide
  rcases family_descends (prefixWord ++ tailWord_109029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109031 : List Nat := [1, 1, 5, 2, 1, 1, 3, 5]
def baseStart_109031 : Nat := 118140960795 + 109031 * 2 ^ 59
def prefixEnd_109031 : Nat := 4983230072969 + 3 ^ 40 * 109031 * 2
def baseEnd_109031 : Nat := 33176479549907051502863

theorem tailTrace_109031 : CollatzResearch.WordTrace tailWord_109031 prefixEnd_109031 33176479549907051502863 := by
  unfold tailWord_109031
  simp only [CollatzResearch.WordTrace]
  refine ⟨3976687268006782857414947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2651124845337855238276631 3976687268006782857414947)
  ·
    refine ⟨5965030902010174286122421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3976687268006782857414947 5965030902010174286122421)
    ·
      refine ⟨559221647063453839323977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5965030902010174286122421 559221647063453839323977)
      ·
        refine ⟨419416235297590379492983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 559221647063453839323977 419416235297590379492983)
        ·
          refine ⟨629124352946385569239475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 419416235297590379492983 629124352946385569239475)
          ·
            refine ⟨943686529419578353859213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 629124352946385569239475 943686529419578353859213)
            ·
              refine ⟨353882448532341882697205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 943686529419578353859213 353882448532341882697205)
              ·
                refine ⟨33176479549907051502863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 353882448532341882697205 33176479549907051502863)
                ·
                  rfl

theorem cell19_109031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 5].length) (baseStart_109031 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_109031 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_109031 prefixEnd_109031 := by exact prefixLift 109031
  have htrace : WordTrace (prefixWord ++ tailWord_109031) baseStart_109031 baseEnd_109031 := by
    simpa [prefixWord, tailWord_109031, baseEnd_109031] using wordTrace_append hprefix tailTrace_109031
  have hstable : (prefixWord ++ tailWord_109031).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109031).length < 2 ^ (prefixWord ++ tailWord_109031).sum := by decide
  have hdescent : baseEnd_109031 < baseStart_109031 := by decide
  rcases family_descends (prefixWord ++ tailWord_109031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109071 : List Nat := [1, 1, 2, 1, 1, 1, 2, 10]
def baseStart_109071 : Nat := 118140960795 + 109071 * 2 ^ 59
def prefixEnd_109071 : Nat := 4983230072969 + 3 ^ 40 * 109071 * 2
def baseEnd_109071 : Nat := 33188650943198810613865

theorem tailTrace_109071 : CollatzResearch.WordTrace tailWord_109071 prefixEnd_109071 33188650943198810613865 := by
  unfold tailWord_109071
  simp only [CollatzResearch.WordTrace]
  refine ⟨3978146187861869688871067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2652097458574579792580711 3978146187861869688871067)
  ·
    refine ⟨5967219281792804533306601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3978146187861869688871067 5967219281792804533306601)
    ·
      refine ⟨4475414461344603399979951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5967219281792804533306601 4475414461344603399979951)
      ·
        refine ⟨6713121692016905099969927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4475414461344603399979951 6713121692016905099969927)
        ·
          refine ⟨10069682538025357649954891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6713121692016905099969927 10069682538025357649954891)
          ·
            refine ⟨15104523807038036474932337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10069682538025357649954891 15104523807038036474932337)
            ·
              refine ⟨11328392855278527356199253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15104523807038036474932337 11328392855278527356199253)
              ·
                refine ⟨33188650943198810613865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 11328392855278527356199253 33188650943198810613865)
                ·
                  rfl

theorem cell19_109071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 10].length) (baseStart_109071 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_109071 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_109071 prefixEnd_109071 := by exact prefixLift 109071
  have htrace : WordTrace (prefixWord ++ tailWord_109071) baseStart_109071 baseEnd_109071 := by
    simpa [prefixWord, tailWord_109071, baseEnd_109071] using wordTrace_append hprefix tailTrace_109071
  have hstable : (prefixWord ++ tailWord_109071).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109071).length < 2 ^ (prefixWord ++ tailWord_109071).sum := by decide
  have hdescent : baseEnd_109071 < baseStart_109071 := by decide
  rcases family_descends (prefixWord ++ tailWord_109071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109101 : List Nat := [1, 5, 4, 1, 2, 6]
def baseStart_109101 : Nat := 118140960795 + 109101 * 2 ^ 59
def prefixEnd_109101 : Nat := 4983230072969 + 3 ^ 40 * 109101 * 2
def baseEnd_109101 : Nat := 3688642165351958883013

theorem tailTrace_109101 : CollatzResearch.WordTrace tailWord_109101 prefixEnd_109101 3688642165351958883013 := by
  unfold tailWord_109101
  simp only [CollatzResearch.WordTrace]
  refine ⟨3979240377753184812463157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2652826918502123208308771 3979240377753184812463157)
  ·
    refine ⟨373053785414361076168421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3979240377753184812463157 373053785414361076168421)
    ·
      refine ⟨69947584765192701781579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 373053785414361076168421 69947584765192701781579)
      ·
        refine ⟨104921377147789052672369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69947584765192701781579 104921377147789052672369)
        ·
          refine ⟨78691032860841789504277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104921377147789052672369 78691032860841789504277)
          ·
            refine ⟨3688642165351958883013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 78691032860841789504277 3688642165351958883013)
            ·
              rfl

theorem cell19_109101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 6].length) (baseStart_109101 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_109101 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_109101 prefixEnd_109101 := by exact prefixLift 109101
  have htrace : WordTrace (prefixWord ++ tailWord_109101) baseStart_109101 baseEnd_109101 := by
    simpa [prefixWord, tailWord_109101, baseEnd_109101] using wordTrace_append hprefix tailTrace_109101
  have hstable : (prefixWord ++ tailWord_109101).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109101).length < 2 ^ (prefixWord ++ tailWord_109101).sum := by decide
  have hdescent : baseEnd_109101 < baseStart_109101 := by decide
  rcases family_descends (prefixWord ++ tailWord_109101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109335 : List Nat := [1, 1, 3, 4, 3, 1, 6]
def baseStart_109335 : Nat := 118140960795 + 109335 * 2 ^ 59
def prefixEnd_109335 : Nat := 4983230072969 + 3 ^ 40 * 109335 * 2
def baseEnd_109335 : Nat := 11089660712974806915493

theorem tailTrace_109335 : CollatzResearch.WordTrace tailWord_109335 prefixEnd_109335 11089660712974806915493 := by
  unfold tailWord_109335
  simp only [CollatzResearch.WordTrace]
  refine ⟨3987775058905442776481459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2658516705936961850987639 3987775058905442776481459)
  ·
    refine ⟨5981662588358164164722189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3987775058905442776481459 5981662588358164164722189)
    ·
      refine ⟨2243123470634311561770821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5981662588358164164722189 2243123470634311561770821)
      ·
        refine ⟨420585650743933417832029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2243123470634311561770821 420585650743933417832029)
        ·
          refine ⟨157719619028975031687011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 420585650743933417832029 157719619028975031687011)
          ·
            refine ⟨236579428543462547530517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157719619028975031687011 236579428543462547530517)
            ·
              refine ⟨11089660712974806915493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 236579428543462547530517 11089660712974806915493)
              ·
                rfl

theorem cell19_109335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 6].length) (baseStart_109335 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_109335 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_109335 prefixEnd_109335 := by exact prefixLift 109335
  have htrace : WordTrace (prefixWord ++ tailWord_109335) baseStart_109335 baseEnd_109335 := by
    simpa [prefixWord, tailWord_109335, baseEnd_109335] using wordTrace_append hprefix tailTrace_109335
  have hstable : (prefixWord ++ tailWord_109335).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109335).length < 2 ^ (prefixWord ++ tailWord_109335).sum := by decide
  have hdescent : baseEnd_109335 < baseStart_109335 := by decide
  rcases family_descends (prefixWord ++ tailWord_109335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109356 : List Nat := [2, 2, 1, 1, 1, 4, 2, 6]
def baseStart_109356 : Nat := 118140960795 + 109356 * 2 ^ 59
def prefixEnd_109356 : Nat := 4983230072969 + 3 ^ 40 * 109356 * 2
def baseEnd_109356 : Nat := 33275372120402594279755

theorem tailTrace_109356 : CollatzResearch.WordTrace tailWord_109356 prefixEnd_109356 33275372120402594279755 := by
  unfold tailWord_109356
  simp only [CollatzResearch.WordTrace]
  refine ⟨1994270495914681681497961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2659027327886242241997281 1994270495914681681497961)
  ·
    refine ⟨1495702871936011261123471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1994270495914681681497961 1495702871936011261123471)
    ·
      refine ⟨2243554307904016891685207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1495702871936011261123471 2243554307904016891685207)
      ·
        refine ⟨3365331461856025337527811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2243554307904016891685207 3365331461856025337527811)
        ·
          refine ⟨5047997192784038006291717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3365331461856025337527811 5047997192784038006291717)
          ·
            refine ⟨946499473647007126179697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5047997192784038006291717 946499473647007126179697)
            ·
              refine ⟨709874605235255344634773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 946499473647007126179697 709874605235255344634773)
              ·
                refine ⟨33275372120402594279755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 709874605235255344634773 33275372120402594279755)
                ·
                  rfl

theorem cell19_109356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 6].length) (baseStart_109356 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_109356 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_109356 prefixEnd_109356 := by exact prefixLift 109356
  have htrace : WordTrace (prefixWord ++ tailWord_109356) baseStart_109356 baseEnd_109356 := by
    simpa [prefixWord, tailWord_109356, baseEnd_109356] using wordTrace_append hprefix tailTrace_109356
  have hstable : (prefixWord ++ tailWord_109356).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109356).length < 2 ^ (prefixWord ++ tailWord_109356).sum := by decide
  have hdescent : baseEnd_109356 < baseStart_109356 := by decide
  rcases family_descends (prefixWord ++ tailWord_109356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109411 : List Nat := [1, 1, 1, 5, 3, 2, 2, 4]
def baseStart_109411 : Nat := 118140960795 + 109411 * 2 ^ 59
def prefixEnd_109411 : Nat := 4983230072969 + 3 ^ 40 * 109411 * 2
def baseEnd_109411 : Nat := 33292107786178763057383

theorem tailTrace_109411 : CollatzResearch.WordTrace tailWord_109411 prefixEnd_109411 33292107786178763057383 := by
  unfold tailWord_109411
  simp only [CollatzResearch.WordTrace]
  refine ⟨3990547006630107756248087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2660364671086738504165391 3990547006630107756248087)
  ·
    refine ⟨5985820509945161634372131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3990547006630107756248087 5985820509945161634372131)
    ·
      refine ⟨8978730764917742451558197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5985820509945161634372131 8978730764917742451558197)
      ·
        refine ⟨841756009211038354833581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8978730764917742451558197 841756009211038354833581)
        ·
          refine ⟨315658503454139383062593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 841756009211038354833581 315658503454139383062593)
          ·
            refine ⟨236743877590604537296945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 315658503454139383062593 236743877590604537296945)
            ·
              refine ⟨177557908192953402972709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 236743877590604537296945 177557908192953402972709)
              ·
                refine ⟨33292107786178763057383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 177557908192953402972709 33292107786178763057383)
                ·
                  rfl

theorem cell19_109411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 2, 4].length) (baseStart_109411 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_109411 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_109411 prefixEnd_109411 := by exact prefixLift 109411
  have htrace : WordTrace (prefixWord ++ tailWord_109411) baseStart_109411 baseEnd_109411 := by
    simpa [prefixWord, tailWord_109411, baseEnd_109411] using wordTrace_append hprefix tailTrace_109411
  have hstable : (prefixWord ++ tailWord_109411).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109411).length < 2 ^ (prefixWord ++ tailWord_109411).sum := by decide
  have hdescent : baseEnd_109411 < baseStart_109411 := by decide
  rcases family_descends (prefixWord ++ tailWord_109411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109413 : List Nat := [1, 3, 1, 3, 1, 1, 3, 6]
def baseStart_109413 : Nat := 118140960795 + 109413 * 2 ^ 59
def prefixEnd_109413 : Nat := 4983230072969 + 3 ^ 40 * 109413 * 2
def baseEnd_109413 : Nat := 33292716355843351012933

theorem tailTrace_109413 : CollatzResearch.WordTrace tailWord_109413 prefixEnd_109413 33292716355843351012933 := by
  unfold tailWord_109413
  simp only [CollatzResearch.WordTrace]
  refine ⟨3990619952622862097820893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2660413301748574731880595 3990619952622862097820893)
  ·
    refine ⟨1496482482233573286682835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3990619952622862097820893 1496482482233573286682835)
    ·
      refine ⟨2244723723350359930024253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1496482482233573286682835 2244723723350359930024253)
      ·
        refine ⟨841771396256384973759095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2244723723350359930024253 841771396256384973759095)
        ·
          refine ⟨1262657094384577460638643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 841771396256384973759095 1262657094384577460638643)
          ·
            refine ⟨1893985641576866190957965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1262657094384577460638643 1893985641576866190957965)
            ·
              refine ⟨710244615591324821609237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1893985641576866190957965 710244615591324821609237)
              ·
                refine ⟨33292716355843351012933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 710244615591324821609237 33292716355843351012933)
                ·
                  rfl

theorem cell19_109413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 6].length) (baseStart_109413 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_109413 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_109413 prefixEnd_109413 := by exact prefixLift 109413
  have htrace : WordTrace (prefixWord ++ tailWord_109413) baseStart_109413 baseEnd_109413 := by
    simpa [prefixWord, tailWord_109413, baseEnd_109413] using wordTrace_append hprefix tailTrace_109413
  have hstable : (prefixWord ++ tailWord_109413).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109413).length < 2 ^ (prefixWord ++ tailWord_109413).sum := by decide
  have hdescent : baseEnd_109413 < baseStart_109413 := by decide
  rcases family_descends (prefixWord ++ tailWord_109413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109462 : List Nat := [5, 3, 1, 1, 1, 3, 1, 4]
def baseStart_109462 : Nat := 118140960795 + 109462 * 2 ^ 59
def prefixEnd_109462 : Nat := 4983230072969 + 3 ^ 40 * 109462 * 2
def baseEnd_109462 : Nat := 33307626312625755923911

theorem tailTrace_109462 : CollatzResearch.WordTrace tailWord_109462 prefixEnd_109462 33307626312625755923911 := by
  unfold tailWord_109462
  simp only [CollatzResearch.WordTrace]
  refine ⟨249525445590333966647165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2661604752963562310903093 249525445590333966647165)
  ·
    refine ⟨93572042096375237492687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 249525445590333966647165 93572042096375237492687)
    ·
      refine ⟨140358063144562856239031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93572042096375237492687 140358063144562856239031)
      ·
        refine ⟨210537094716844284358547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140358063144562856239031 210537094716844284358547)
        ·
          refine ⟨315805642075266426537821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210537094716844284358547 315805642075266426537821)
          ·
            refine ⟨118427115778224909951683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 315805642075266426537821 118427115778224909951683)
            ·
              refine ⟨177640673667337364927525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118427115778224909951683 177640673667337364927525)
              ·
                refine ⟨33307626312625755923911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 177640673667337364927525 33307626312625755923911)
                ·
                  rfl

theorem cell19_109462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 1, 4].length) (baseStart_109462 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_109462 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_109462 prefixEnd_109462 := by exact prefixLift 109462
  have htrace : WordTrace (prefixWord ++ tailWord_109462) baseStart_109462 baseEnd_109462 := by
    simpa [prefixWord, tailWord_109462, baseEnd_109462] using wordTrace_append hprefix tailTrace_109462
  have hstable : (prefixWord ++ tailWord_109462).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109462).length < 2 ^ (prefixWord ++ tailWord_109462).sum := by decide
  have hdescent : baseEnd_109462 < baseStart_109462 := by decide
  rcases family_descends (prefixWord ++ tailWord_109462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109466 : List Nat := [3, 1, 1, 4, 3, 2, 1, 4]
def baseStart_109466 : Nat := 118140960795 + 109466 * 2 ^ 59
def prefixEnd_109466 : Nat := 4983230072969 + 3 ^ 40 * 109466 * 2
def baseEnd_109466 : Nat := 33308843451954931835011

theorem tailTrace_109466 : CollatzResearch.WordTrace tailWord_109466 prefixEnd_109466 33308843451954931835011 := by
  unfold tailWord_109466
  simp only [CollatzResearch.WordTrace]
  refine ⟨998138255357713037375063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2661702014287234766333501 998138255357713037375063)
  ·
    refine ⟨1497207383036569556062595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 998138255357713037375063 1497207383036569556062595)
    ·
      refine ⟨2245811074554854334093893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1497207383036569556062595 2245811074554854334093893)
      ·
        refine ⟨421089576479035187642605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2245811074554854334093893 421089576479035187642605)
        ·
          refine ⟨157908591179638195365977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 421089576479035187642605 157908591179638195365977)
          ·
            refine ⟨118431443384728646524483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157908591179638195365977 118431443384728646524483)
            ·
              refine ⟨177647165077092969786725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118431443384728646524483 177647165077092969786725)
              ·
                refine ⟨33308843451954931835011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 177647165077092969786725 33308843451954931835011)
                ·
                  rfl

theorem cell19_109466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 1, 4].length) (baseStart_109466 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_109466 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_109466 prefixEnd_109466 := by exact prefixLift 109466
  have htrace : WordTrace (prefixWord ++ tailWord_109466) baseStart_109466 baseEnd_109466 := by
    simpa [prefixWord, tailWord_109466, baseEnd_109466] using wordTrace_append hprefix tailTrace_109466
  have hstable : (prefixWord ++ tailWord_109466).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109466).length < 2 ^ (prefixWord ++ tailWord_109466).sum := by decide
  have hdescent : baseEnd_109466 < baseStart_109466 := by decide
  rcases family_descends (prefixWord ++ tailWord_109466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109544 : List Nat := [2, 1, 4, 1, 1, 1, 6, 3]
def baseStart_109544 : Nat := 118140960795 + 109544 * 2 ^ 59
def prefixEnd_109544 : Nat := 4983230072969 + 3 ^ 40 * 109544 * 2
def baseEnd_109544 : Nat := 33332577668873862101465

theorem tailTrace_109544 : CollatzResearch.WordTrace tailWord_109544 prefixEnd_109544 33332577668873862101465 := by
  unfold tailWord_109544
  simp only [CollatzResearch.WordTrace]
  refine ⟨1997698957574135735419843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2663598610098847647226457 1997698957574135735419843)
  ·
    refine ⟨2996548436361203603129765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1997698957574135735419843 2996548436361203603129765)
    ·
      refine ⟨561852831817725675586831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2996548436361203603129765 561852831817725675586831)
      ·
        refine ⟨842779247726588513380247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 561852831817725675586831 842779247726588513380247)
        ·
          refine ⟨1264168871589882770070371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 842779247726588513380247 1264168871589882770070371)
          ·
            refine ⟨1896253307384824155105557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1264168871589882770070371 1896253307384824155105557)
            ·
              refine ⟨88886873783663632270573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1896253307384824155105557 88886873783663632270573)
              ·
                refine ⟨33332577668873862101465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88886873783663632270573 33332577668873862101465)
                ·
                  rfl

theorem cell19_109544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 6, 3].length) (baseStart_109544 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_109544 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_109544 prefixEnd_109544 := by exact prefixLift 109544
  have htrace : WordTrace (prefixWord ++ tailWord_109544) baseStart_109544 baseEnd_109544 := by
    simpa [prefixWord, tailWord_109544, baseEnd_109544] using wordTrace_append hprefix tailTrace_109544
  have hstable : (prefixWord ++ tailWord_109544).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109544).length < 2 ^ (prefixWord ++ tailWord_109544).sum := by decide
  have hdescent : baseEnd_109544 < baseStart_109544 := by decide
  rcases family_descends (prefixWord ++ tailWord_109544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109582 : List Nat := [4, 1, 1, 2, 2, 3, 2, 4]
def baseStart_109582 : Nat := 118140960795 + 109582 * 2 ^ 59
def prefixEnd_109582 : Nat := 4983230072969 + 3 ^ 40 * 109582 * 2
def baseEnd_109582 : Nat := 33344140492501033256917

theorem tailTrace_109582 : CollatzResearch.WordTrace tailWord_109582 prefixEnd_109582 33344140492501033256917 := by
  unfold tailWord_109582
  simp only [CollatzResearch.WordTrace]
  refine ⟨499597986126325495090375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2664522592673735973815333 499597986126325495090375)
  ·
    refine ⟨749396979189488242635563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 499597986126325495090375 749396979189488242635563)
    ·
      refine ⟨1124095468784232363953345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 749396979189488242635563 1124095468784232363953345)
      ·
        refine ⟨843071601588174272965009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1124095468784232363953345 843071601588174272965009)
        ·
          refine ⟨632303701191130704723757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 843071601588174272965009 632303701191130704723757)
          ·
            refine ⟨237113887946674014271409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 632303701191130704723757 237113887946674014271409)
            ·
              refine ⟨177835415960005510703557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 237113887946674014271409 177835415960005510703557)
              ·
                refine ⟨33344140492501033256917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 177835415960005510703557 33344140492501033256917)
                ·
                  rfl

theorem cell19_109582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 2, 4].length) (baseStart_109582 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_109582 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_109582 prefixEnd_109582 := by exact prefixLift 109582
  have htrace : WordTrace (prefixWord ++ tailWord_109582) baseStart_109582 baseEnd_109582 := by
    simpa [prefixWord, tailWord_109582, baseEnd_109582] using wordTrace_append hprefix tailTrace_109582
  have hstable : (prefixWord ++ tailWord_109582).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109582).length < 2 ^ (prefixWord ++ tailWord_109582).sum := by decide
  have hdescent : baseEnd_109582 < baseStart_109582 := by decide
  rcases family_descends (prefixWord ++ tailWord_109582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109603 : List Nat := [1, 1, 1, 4, 3, 2, 2, 5]
def baseStart_109603 : Nat := 118140960795 + 109603 * 2 ^ 59
def prefixEnd_109603 : Nat := 4983230072969 + 3 ^ 40 * 109603 * 2
def baseEnd_109603 : Nat := 33350530473979206790193

theorem tailTrace_109603 : CollatzResearch.WordTrace tailWord_109603 prefixEnd_109603 33350530473979206790193 := by
  unfold tailWord_109603
  simp only [CollatzResearch.WordTrace]
  refine ⟨3997549821934524547237463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2665033214623016364824975 3997549821934524547237463)
  ·
    refine ⟨5996324732901786820856195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3997549821934524547237463 5996324732901786820856195)
    ·
      refine ⟨8994487099352680231284293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5996324732901786820856195 8994487099352680231284293)
      ·
        refine ⟨1686466331128627543365805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8994487099352680231284293 1686466331128627543365805)
        ·
          refine ⟨632424874173235328762177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1686466331128627543365805 632424874173235328762177)
          ·
            refine ⟨474318655629926496571633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 632424874173235328762177 474318655629926496571633)
            ·
              refine ⟨355738991722444872428725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 474318655629926496571633 355738991722444872428725)
              ·
                refine ⟨33350530473979206790193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 355738991722444872428725 33350530473979206790193)
                ·
                  rfl

theorem cell19_109603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 5].length) (baseStart_109603 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_109603 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_109603 prefixEnd_109603 := by exact prefixLift 109603
  have htrace : WordTrace (prefixWord ++ tailWord_109603) baseStart_109603 baseEnd_109603 := by
    simpa [prefixWord, tailWord_109603, baseEnd_109603] using wordTrace_append hprefix tailTrace_109603
  have hstable : (prefixWord ++ tailWord_109603).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109603).length < 2 ^ (prefixWord ++ tailWord_109603).sum := by decide
  have hdescent : baseEnd_109603 < baseStart_109603 := by decide
  rcases family_descends (prefixWord ++ tailWord_109603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109620 : List Nat := [2, 5, 1, 2, 1, 8]
def baseStart_109620 : Nat := 118140960795 + 109620 * 2 ^ 59
def prefixEnd_109620 : Nat := 4983230072969 + 3 ^ 40 * 109620 * 2
def baseEnd_109620 : Nat := 3706189257347578268041

theorem tailTrace_109620 : CollatzResearch.WordTrace tailWord_109620 prefixEnd_109620 3706189257347578268041 := by
  unfold tailWord_109620
  simp only [CollatzResearch.WordTrace]
  refine ⟨1999084931436468225303157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2665446575248624300404209 1999084931436468225303157)
  ·
    refine ⟨187414212322168896122171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1999084931436468225303157 187414212322168896122171)
    ·
      refine ⟨281121318483253344183257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187414212322168896122171 281121318483253344183257)
      ·
        refine ⟨210840988862440008137443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 281121318483253344183257 210840988862440008137443)
        ·
          refine ⟨316261483293660012206165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210840988862440008137443 316261483293660012206165)
          ·
            refine ⟨3706189257347578268041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 316261483293660012206165 3706189257347578268041)
            ·
              rfl

theorem cell19_109620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 8].length) (baseStart_109620 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_109620 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_109620 prefixEnd_109620 := by exact prefixLift 109620
  have htrace : WordTrace (prefixWord ++ tailWord_109620) baseStart_109620 baseEnd_109620 := by
    simpa [prefixWord, tailWord_109620, baseEnd_109620] using wordTrace_append hprefix tailTrace_109620
  have hstable : (prefixWord ++ tailWord_109620).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109620).length < 2 ^ (prefixWord ++ tailWord_109620).sum := by decide
  have hdescent : baseEnd_109620 < baseStart_109620 := by decide
  rcases family_descends (prefixWord ++ tailWord_109620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109639 : List Nat := [1, 1, 4, 1, 3, 4, 1, 4]
def baseStart_109639 : Nat := 118140960795 + 109639 * 2 ^ 59
def prefixEnd_109639 : Nat := 4983230072969 + 3 ^ 40 * 109639 * 2
def baseEnd_109639 : Nat := 33361484727941789990095

theorem tailTrace_109639 : CollatzResearch.WordTrace tailWord_109639 prefixEnd_109639 33361484727941789990095 := by
  unfold tailWord_109639
  simp only [CollatzResearch.WordTrace]
  refine ⟨3998862849804102695547971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2665908566536068463698647 3998862849804102695547971)
  ·
    refine ⟨5998294274706154043321957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3998862849804102695547971 5998294274706154043321957)
    ·
      refine ⟨1124680176507403883122867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5998294274706154043321957 1124680176507403883122867)
      ·
        refine ⟨1687020264761105824684301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1124680176507403883122867 1687020264761105824684301)
        ·
          refine ⟨632632599285414684256613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1687020264761105824684301 632632599285414684256613)
          ·
            refine ⟨118618612366015253298115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 632632599285414684256613 118618612366015253298115)
            ·
              refine ⟨177927918549022879947173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118618612366015253298115 177927918549022879947173)
              ·
                refine ⟨33361484727941789990095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 177927918549022879947173 33361484727941789990095)
                ·
                  rfl

theorem cell19_109639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 1, 4].length) (baseStart_109639 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_109639 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_109639 prefixEnd_109639 := by exact prefixLift 109639
  have htrace : WordTrace (prefixWord ++ tailWord_109639) baseStart_109639 baseEnd_109639 := by
    simpa [prefixWord, tailWord_109639, baseEnd_109639] using wordTrace_append hprefix tailTrace_109639
  have hstable : (prefixWord ++ tailWord_109639).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109639).length < 2 ^ (prefixWord ++ tailWord_109639).sum := by decide
  have hdescent : baseEnd_109639 < baseStart_109639 := by decide
  rcases family_descends (prefixWord ++ tailWord_109639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109795 : List Nat := [1, 1, 1, 16]
def baseStart_109795 : Nat := 118140960795 + 109795 * 2 ^ 59
def prefixEnd_109795 : Nat := 4983230072969 + 3 ^ 40 * 109795 * 2
def baseEnd_109795 : Nat := 412456211873822845963

theorem tailTrace_109795 : CollatzResearch.WordTrace tailWord_109795 prefixEnd_109795 412456211873822845963 := by
  unfold tailWord_109795
  simp only [CollatzResearch.WordTrace]
  refine ⟨4004552637238941338226839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2669701758159294225484559 4004552637238941338226839)
  ·
    refine ⟨6006828955858412007340259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4004552637238941338226839 6006828955858412007340259)
    ·
      refine ⟨9010243433787618011010389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6006828955858412007340259 9010243433787618011010389)
      ·
        refine ⟨412456211873822845963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 16 9010243433787618011010389 412456211873822845963)
        ·
          rfl

theorem cell19_109795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 16].length) (baseStart_109795 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_109795 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_109795 prefixEnd_109795 := by exact prefixLift 109795
  have htrace : WordTrace (prefixWord ++ tailWord_109795) baseStart_109795 baseEnd_109795 := by
    simpa [prefixWord, tailWord_109795, baseEnd_109795] using wordTrace_append hprefix tailTrace_109795
  have hstable : (prefixWord ++ tailWord_109795).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109795).length < 2 ^ (prefixWord ++ tailWord_109795).sum := by decide
  have hdescent : baseEnd_109795 < baseStart_109795 := by decide
  rcases family_descends (prefixWord ++ tailWord_109795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109850 : List Nat := [3, 1, 1, 3, 3, 2, 6]
def baseStart_109850 : Nat := 118140960795 + 109850 * 2 ^ 59
def prefixEnd_109850 : Nat := 4983230072969 + 3 ^ 40 * 109850 * 2
def baseEnd_109850 : Nat := 11141896275851939766877

theorem tailTrace_109850 : CollatzResearch.WordTrace tailWord_109850 prefixEnd_109850 11141896275851939766877 := by
  unfold tailWord_109850
  simp only [CollatzResearch.WordTrace]
  refine ⟨1001639663009921432869751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2671039101359790487652669 1001639663009921432869751)
  ·
    refine ⟨1502459494514882149304627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1001639663009921432869751 1502459494514882149304627)
    ·
      refine ⟨2253689241772323223956941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1502459494514882149304627 2253689241772323223956941)
      ·
        refine ⟨845133465664621208983853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2253689241772323223956941 845133465664621208983853)
        ·
          refine ⟨316925049624232953368945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 845133465664621208983853 316925049624232953368945)
          ·
            refine ⟨237693787218174715026709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 316925049624232953368945 237693787218174715026709)
            ·
              refine ⟨11141896275851939766877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 237693787218174715026709 11141896275851939766877)
              ·
                rfl

theorem cell19_109850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 6].length) (baseStart_109850 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_109850 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_109850 prefixEnd_109850 := by exact prefixLift 109850
  have htrace : WordTrace (prefixWord ++ tailWord_109850) baseStart_109850 baseEnd_109850 := by
    simpa [prefixWord, tailWord_109850, baseEnd_109850] using wordTrace_append hprefix tailTrace_109850
  have hstable : (prefixWord ++ tailWord_109850).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109850).length < 2 ^ (prefixWord ++ tailWord_109850).sum := by decide
  have hdescent : baseEnd_109850 < baseStart_109850 := by decide
  rcases family_descends (prefixWord ++ tailWord_109850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109871 : List Nat := [1, 1, 2, 1, 2, 1, 3, 8]
def baseStart_109871 : Nat := 118140960795 + 109871 * 2 ^ 59
def prefixEnd_109871 : Nat := 4983230072969 + 3 ^ 40 * 109871 * 2
def baseEnd_109871 : Nat := 33432078809033992833907

theorem tailTrace_109871 : CollatzResearch.WordTrace tailWord_109871 prefixEnd_109871 33432078809033992833907 := by
  unfold tailWord_109871
  simp only [CollatzResearch.WordTrace]
  refine ⟨4007324584963606317993467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2671549723309070878662311 4007324584963606317993467)
  ·
    refine ⟨6010986877445409476990201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4007324584963606317993467 6010986877445409476990201)
    ·
      refine ⟨4508240158084057107742651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6010986877445409476990201 4508240158084057107742651)
      ·
        refine ⟨6762360237126085661613977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4508240158084057107742651 6762360237126085661613977)
        ·
          refine ⟨5071770177844564246210483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6762360237126085661613977 5071770177844564246210483)
          ·
            refine ⟨7607655266766846369315725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5071770177844564246210483 7607655266766846369315725)
            ·
              refine ⟨2852870725037567388493397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7607655266766846369315725 2852870725037567388493397)
              ·
                refine ⟨33432078809033992833907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2852870725037567388493397 33432078809033992833907)
                ·
                  rfl

theorem cell19_109871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 8].length) (baseStart_109871 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_109871 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_109871 prefixEnd_109871 := by exact prefixLift 109871
  have htrace : WordTrace (prefixWord ++ tailWord_109871) baseStart_109871 baseEnd_109871 := by
    simpa [prefixWord, tailWord_109871, baseEnd_109871] using wordTrace_append hprefix tailTrace_109871
  have hstable : (prefixWord ++ tailWord_109871).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109871).length < 2 ^ (prefixWord ++ tailWord_109871).sum := by decide
  have hdescent : baseEnd_109871 < baseStart_109871 := by decide
  rcases family_descends (prefixWord ++ tailWord_109871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109901 : List Nat := [1, 6, 1, 3, 2, 1, 5]
def baseStart_109901 : Nat := 118140960795 + 109901 * 2 ^ 59
def prefixEnd_109901 : Nat := 4983230072969 + 3 ^ 40 * 109901 * 2
def baseEnd_109901 : Nat := 11147069118000937389053

theorem tailTrace_109901 : CollatzResearch.WordTrace tailWord_109901 prefixEnd_109901 11147069118000937389053 := by
  unfold tailWord_109901
  simp only [CollatzResearch.WordTrace]
  refine ⟨4008418774854921441585557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2672279183236614294390371 4008418774854921441585557)
  ·
    refine ⟨187894630071324442574323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 4008418774854921441585557 187894630071324442574323)
    ·
      refine ⟨281841945106986663861485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187894630071324442574323 281841945106986663861485)
      ·
        refine ⟨105690729415119998948057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 281841945106986663861485 105690729415119998948057)
        ·
          refine ⟨79268047061339999211043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105690729415119998948057 79268047061339999211043)
          ·
            refine ⟨118902070592009998816565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79268047061339999211043 118902070592009998816565)
            ·
              refine ⟨11147069118000937389053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 118902070592009998816565 11147069118000937389053)
              ·
                rfl

theorem cell19_109901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 5].length) (baseStart_109901 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_109901 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_109901 prefixEnd_109901 := by exact prefixLift 109901
  have htrace : WordTrace (prefixWord ++ tailWord_109901) baseStart_109901 baseEnd_109901 := by
    simpa [prefixWord, tailWord_109901, baseEnd_109901] using wordTrace_append hprefix tailTrace_109901
  have hstable : (prefixWord ++ tailWord_109901).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109901).length < 2 ^ (prefixWord ++ tailWord_109901).sum := by decide
  have hdescent : baseEnd_109901 < baseStart_109901 := by decide
  rcases family_descends (prefixWord ++ tailWord_109901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109947 : List Nat := [1, 1, 1, 1, 1, 6, 1, 7]
def baseStart_109947 : Nat := 118140960795 + 109947 * 2 ^ 59
def prefixEnd_109947 : Nat := 4983230072969 + 3 ^ 40 * 109947 * 2
def baseEnd_109947 : Nat := 33455204456288335144811

theorem tailTrace_109947 : CollatzResearch.WordTrace tailWord_109947 prefixEnd_109947 33455204456288335144811 := by
  unfold tailWord_109947
  simp only [CollatzResearch.WordTrace]
  refine ⟨4010096532688271297760095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2673397688458847531840063 4010096532688271297760095)
  ·
    refine ⟨6015144799032406946640143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4010096532688271297760095 6015144799032406946640143)
    ·
      refine ⟨9022717198548610419960215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6015144799032406946640143 9022717198548610419960215)
      ·
        refine ⟨13534075797822915629940323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9022717198548610419960215 13534075797822915629940323)
        ·
          refine ⟨20301113696734373444910485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13534075797822915629940323 20301113696734373444910485)
          ·
            refine ⟨951614704534423755230179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 20301113696734373444910485 951614704534423755230179)
            ·
              refine ⟨1427422056801635632845269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 951614704534423755230179 1427422056801635632845269)
              ·
                refine ⟨33455204456288335144811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1427422056801635632845269 33455204456288335144811)
                ·
                  rfl

theorem cell19_109947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 7].length) (baseStart_109947 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_109947 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_109947 prefixEnd_109947 := by exact prefixLift 109947
  have htrace : WordTrace (prefixWord ++ tailWord_109947) baseStart_109947 baseEnd_109947 := by
    simpa [prefixWord, tailWord_109947, baseEnd_109947] using wordTrace_append hprefix tailTrace_109947
  have hstable : (prefixWord ++ tailWord_109947).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109947).length < 2 ^ (prefixWord ++ tailWord_109947).sum := by decide
  have hdescent : baseEnd_109947 < baseStart_109947 := by decide
  rcases family_descends (prefixWord ++ tailWord_109947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109981 : List Nat := [1, 4, 2, 1, 3, 3, 1, 4]
def baseStart_109981 : Nat := 118140960795 + 109981 * 2 ^ 59
def prefixEnd_109981 : Nat := 4983230072969 + 3 ^ 40 * 109981 * 2
def baseEnd_109981 : Nat := 33465550140586330389163

theorem tailTrace_109981 : CollatzResearch.WordTrace tailWord_109981 prefixEnd_109981 33465550140586330389163 := by
  unfold tailWord_109981
  simp only [CollatzResearch.WordTrace]
  refine ⟨4011336614565095104497797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2674224409710063402998531 4011336614565095104497797)
  ·
    refine ⟨752125615230955332093337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4011336614565095104497797 752125615230955332093337)
    ·
      refine ⟨564094211423216499070003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 752125615230955332093337 564094211423216499070003)
      ·
        refine ⟨846141317134824748605005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 564094211423216499070003 846141317134824748605005)
        ·
          refine ⟨317302993925559280726877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 846141317134824748605005 317302993925559280726877)
          ·
            refine ⟨118988622722084730272579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 317302993925559280726877 118988622722084730272579)
            ·
              refine ⟨178482934083127095408869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118988622722084730272579 178482934083127095408869)
              ·
                refine ⟨33465550140586330389163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 178482934083127095408869 33465550140586330389163)
                ·
                  rfl

theorem cell19_109981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 1, 4].length) (baseStart_109981 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_109981 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_109981 prefixEnd_109981 := by exact prefixLift 109981
  have htrace : WordTrace (prefixWord ++ tailWord_109981) baseStart_109981 baseEnd_109981 := by
    simpa [prefixWord, tailWord_109981, baseEnd_109981] using wordTrace_append hprefix tailTrace_109981
  have hstable : (prefixWord ++ tailWord_109981).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109981).length < 2 ^ (prefixWord ++ tailWord_109981).sum := by decide
  have hdescent : baseEnd_109981 < baseStart_109981 := by decide
  rcases family_descends (prefixWord ++ tailWord_109981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109983 : List Nat := [1, 1, 2, 5, 1, 2, 3, 4]
def baseStart_109983 : Nat := 118140960795 + 109983 * 2 ^ 59
def prefixEnd_109983 : Nat := 4983230072969 + 3 ^ 40 * 109983 * 2
def baseEnd_109983 : Nat := 33466158710250918344713

theorem tailTrace_109983 : CollatzResearch.WordTrace tailWord_109983 prefixEnd_109983 33466158710250918344713 := by
  unfold tailWord_109983
  simp only [CollatzResearch.WordTrace]
  refine ⟨4011409560557849446070603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2674273040371899630713735 4011409560557849446070603)
  ·
    refine ⟨6017114340836774169105905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4011409560557849446070603 6017114340836774169105905)
    ·
      refine ⟨4512835755627580626829429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6017114340836774169105905 4512835755627580626829429)
      ·
        refine ⟨423078352090085683765259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4512835755627580626829429 423078352090085683765259)
        ·
          refine ⟨634617528135128525647889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 423078352090085683765259 634617528135128525647889)
          ·
            refine ⟨475963146101346394235917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 634617528135128525647889 475963146101346394235917)
            ·
              refine ⟨178486179788004897838469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 475963146101346394235917 178486179788004897838469)
              ·
                refine ⟨33466158710250918344713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 178486179788004897838469 33466158710250918344713)
                ·
                  rfl

theorem cell19_109983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 3, 4].length) (baseStart_109983 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_109983 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_109983 prefixEnd_109983 := by exact prefixLift 109983
  have htrace : WordTrace (prefixWord ++ tailWord_109983) baseStart_109983 baseEnd_109983 := by
    simpa [prefixWord, tailWord_109983, baseEnd_109983] using wordTrace_append hprefix tailTrace_109983
  have hstable : (prefixWord ++ tailWord_109983).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109983).length < 2 ^ (prefixWord ++ tailWord_109983).sum := by decide
  have hdescent : baseEnd_109983 < baseStart_109983 := by decide
  rcases family_descends (prefixWord ++ tailWord_109983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110023 : List Nat := [1, 1, 4, 1, 1, 3, 8]
def baseStart_110023 : Nat := 118140960795 + 110023 * 2 ^ 59
def prefixEnd_110023 : Nat := 4983230072969 + 3 ^ 40 * 110023 * 2
def baseEnd_110023 : Nat := 11159443367847559151905

theorem tailTrace_110023 : CollatzResearch.WordTrace tailWord_110023 prefixEnd_110023 11159443367847559151905 := by
  unfold tailWord_110023
  simp only [CollatzResearch.WordTrace]
  refine ⟨4012868480412936277526723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2675245653608624185017815 4012868480412936277526723)
  ·
    refine ⟨6019302720619404416290085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4012868480412936277526723 6019302720619404416290085)
    ·
      refine ⟨1128619260116138328054391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6019302720619404416290085 1128619260116138328054391)
      ·
        refine ⟨1692928890174207492081587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1128619260116138328054391 1692928890174207492081587)
        ·
          refine ⟨2539393335261311238122381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1692928890174207492081587 2539393335261311238122381)
          ·
            refine ⟨952272500722991714295893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2539393335261311238122381 952272500722991714295893)
            ·
              refine ⟨11159443367847559151905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 952272500722991714295893 11159443367847559151905)
              ·
                rfl

theorem cell19_110023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 8].length) (baseStart_110023 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_110023 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_110023 prefixEnd_110023 := by exact prefixLift 110023
  have htrace : WordTrace (prefixWord ++ tailWord_110023) baseStart_110023 baseEnd_110023 := by
    simpa [prefixWord, tailWord_110023, baseEnd_110023] using wordTrace_append hprefix tailTrace_110023
  have hstable : (prefixWord ++ tailWord_110023).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110023).length < 2 ^ (prefixWord ++ tailWord_110023).sum := by decide
  have hdescent : baseEnd_110023 < baseStart_110023 := by decide
  rcases family_descends (prefixWord ++ tailWord_110023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110099 : List Nat := [1, 1, 1, 2, 1, 6, 1, 6]
def baseStart_110099 : Nat := 118140960795 + 110099 * 2 ^ 59
def prefixEnd_110099 : Nat := 4983230072969 + 3 ^ 40 * 110099 * 2
def baseEnd_110099 : Nat := 33501455750797019766619

theorem tailTrace_110099 : CollatzResearch.WordTrace tailWord_110099 prefixEnd_110099 33501455750797019766619 := by
  unfold tailWord_110099
  simp only [CollatzResearch.WordTrace]
  refine ⟨4015640428137601257293351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2677093618758400838195567 4015640428137601257293351)
  ·
    refine ⟨6023460642206401885940027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4015640428137601257293351 6023460642206401885940027)
    ·
      refine ⟨9035190963309602828910041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6023460642206401885940027 9035190963309602828910041)
      ·
        refine ⟨6776393222482202121682531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9035190963309602828910041 6776393222482202121682531)
        ·
          refine ⟨10164589833723303182523797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6776393222482202121682531 10164589833723303182523797)
          ·
            refine ⟨476465148455779836680803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 10164589833723303182523797 476465148455779836680803)
            ·
              refine ⟨714697722683669755021205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 476465148455779836680803 714697722683669755021205)
              ·
                refine ⟨33501455750797019766619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 714697722683669755021205 33501455750797019766619)
                ·
                  rfl

theorem cell19_110099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 6].length) (baseStart_110099 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_110099 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_110099 prefixEnd_110099 := by exact prefixLift 110099
  have htrace : WordTrace (prefixWord ++ tailWord_110099) baseStart_110099 baseEnd_110099 := by
    simpa [prefixWord, tailWord_110099, baseEnd_110099] using wordTrace_append hprefix tailTrace_110099
  have hstable : (prefixWord ++ tailWord_110099).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110099).length < 2 ^ (prefixWord ++ tailWord_110099).sum := by decide
  have hdescent : baseEnd_110099 < baseStart_110099 := by decide
  rcases family_descends (prefixWord ++ tailWord_110099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110137 : List Nat := [1, 2, 1, 5, 1, 9]
def baseStart_110137 : Nat := 118140960795 + 110137 * 2 ^ 59
def prefixEnd_110137 : Nat := 4983230072969 + 3 ^ 40 * 110137 * 2
def baseEnd_110137 : Nat := 3723668730491576769119

theorem tailTrace_110137 : CollatzResearch.WordTrace tailWord_110137 prefixEnd_110137 3723668730491576769119 := by
  unfold tailWord_110137
  simp only [CollatzResearch.WordTrace]
  refine ⟨4017026401999933747176665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2678017601333289164784443 4017026401999933747176665)
  ·
    refine ⟨3012769801499950310382499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4017026401999933747176665 3012769801499950310382499)
    ·
      refine ⟨4519154702249925465573749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3012769801499950310382499 4519154702249925465573749)
      ·
        refine ⟨423670753335930512397539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4519154702249925465573749 423670753335930512397539)
        ·
          refine ⟨635506130003895768596309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 423670753335930512397539 635506130003895768596309)
          ·
            refine ⟨3723668730491576769119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 635506130003895768596309 3723668730491576769119)
            ·
              rfl

theorem cell19_110137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 9].length) (baseStart_110137 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_110137 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_110137 prefixEnd_110137 := by exact prefixLift 110137
  have htrace : WordTrace (prefixWord ++ tailWord_110137) baseStart_110137 baseEnd_110137 := by
    simpa [prefixWord, tailWord_110137, baseEnd_110137] using wordTrace_append hprefix tailTrace_110137
  have hstable : (prefixWord ++ tailWord_110137).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110137).length < 2 ^ (prefixWord ++ tailWord_110137).sum := by decide
  have hdescent : baseEnd_110137 < baseStart_110137 := by decide
  rcases family_descends (prefixWord ++ tailWord_110137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110213 : List Nat := [1, 3, 1, 1, 4, 1, 2, 6]
def baseStart_110213 : Nat := 118140960795 + 110213 * 2 ^ 59
def prefixEnd_110213 : Nat := 4983230072969 + 3 ^ 40 * 110213 * 2
def baseEnd_110213 : Nat := 33536144221678533232975

theorem tailTrace_110213 : CollatzResearch.WordTrace tailWord_110213 prefixEnd_110213 33536144221678533232975 := by
  unfold tailWord_110213
  simp only [CollatzResearch.WordTrace]
  refine ⟨4019798349724598726943293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2679865566483065817962195 4019798349724598726943293)
  ·
    refine ⟨1507424381146724522603735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4019798349724598726943293 1507424381146724522603735)
    ·
      refine ⟨2261136571720086783905603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1507424381146724522603735 2261136571720086783905603)
      ·
        refine ⟨3391704857580130175858405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2261136571720086783905603 3391704857580130175858405)
        ·
          refine ⟨635944660796274407973451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3391704857580130175858405 635944660796274407973451)
          ·
            refine ⟨953916991194411611960177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 635944660796274407973451 953916991194411611960177)
            ·
              refine ⟨715437743395808708970133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 953916991194411611960177 715437743395808708970133)
              ·
                refine ⟨33536144221678533232975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 715437743395808708970133 33536144221678533232975)
                ·
                  rfl

theorem cell19_110213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 6].length) (baseStart_110213 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_110213 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_110213 prefixEnd_110213 := by exact prefixLift 110213
  have htrace : WordTrace (prefixWord ++ tailWord_110213) baseStart_110213 baseEnd_110213 := by
    simpa [prefixWord, tailWord_110213, baseEnd_110213] using wordTrace_append hprefix tailTrace_110213
  have hstable : (prefixWord ++ tailWord_110213).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110213).length < 2 ^ (prefixWord ++ tailWord_110213).sum := by decide
  have hdescent : baseEnd_110213 < baseStart_110213 := by decide
  rcases family_descends (prefixWord ++ tailWord_110213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110226 : List Nat := [3, 2, 3, 1, 3, 2, 2, 3]
def baseStart_110226 : Nat := 118140960795 + 110226 * 2 ^ 59
def prefixEnd_110226 : Nat := 4983230072969 + 3 ^ 40 * 110226 * 2
def baseEnd_110226 : Nat := 33540099924498354944051

theorem tailTrace_110226 : CollatzResearch.WordTrace tailWord_110226 prefixEnd_110226 33540099924498354944051 := by
  unfold tailWord_110226
  simp only [CollatzResearch.WordTrace]
  refine ⟨1005068124669375486791633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2680181665785001298111021 1005068124669375486791633)
  ·
    refine ⟨753801093502031615093725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1005068124669375486791633 753801093502031615093725)
    ·
      refine ⟨282675410063261855660147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 753801093502031615093725 282675410063261855660147)
      ·
        refine ⟨424013115094892783490221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282675410063261855660147 424013115094892783490221)
        ·
          refine ⟨159004918160584793808833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 424013115094892783490221 159004918160584793808833)
          ·
            refine ⟨119253688620438595356625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159004918160584793808833 119253688620438595356625)
            ·
              refine ⟨89440266465328946517469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119253688620438595356625 89440266465328946517469)
              ·
                refine ⟨33540099924498354944051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89440266465328946517469 33540099924498354944051)
                ·
                  rfl

theorem cell19_110226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 2, 3].length) (baseStart_110226 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_110226 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_110226 prefixEnd_110226 := by exact prefixLift 110226
  have htrace : WordTrace (prefixWord ++ tailWord_110226) baseStart_110226 baseEnd_110226 := by
    simpa [prefixWord, tailWord_110226, baseEnd_110226] using wordTrace_append hprefix tailTrace_110226
  have hstable : (prefixWord ++ tailWord_110226).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110226).length < 2 ^ (prefixWord ++ tailWord_110226).sum := by decide
  have hdescent : baseEnd_110226 < baseStart_110226 := by decide
  rcases family_descends (prefixWord ++ tailWord_110226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110228 : List Nat := [2, 4, 2, 2, 2, 1, 1, 5]
def baseStart_110228 : Nat := 118140960795 + 110228 * 2 ^ 59
def prefixEnd_110228 : Nat := 4983230072969 + 3 ^ 40 * 110228 * 2
def baseEnd_110228 : Nat := 33540708494162942899601

theorem tailTrace_110228 : CollatzResearch.WordTrace tailWord_110228 prefixEnd_110228 33540708494162942899601 := by
  unfold tailWord_110228
  simp only [CollatzResearch.WordTrace]
  refine ⟨2010172722335128144369669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2680230296446837525826225 2010172722335128144369669)
  ·
    refine ⟨376907385437836527069313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2010172722335128144369669 376907385437836527069313)
    ·
      refine ⟨282680539078377395301985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 376907385437836527069313 282680539078377395301985)
      ·
        refine ⟨212010404308783046476489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 282680539078377395301985 212010404308783046476489)
        ·
          refine ⟨159007803231587284857367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212010404308783046476489 159007803231587284857367)
          ·
            refine ⟨238511704847380927286051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159007803231587284857367 238511704847380927286051)
            ·
              refine ⟨357767557271071390929077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 238511704847380927286051 357767557271071390929077)
              ·
                refine ⟨33540708494162942899601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 357767557271071390929077 33540708494162942899601)
                ·
                  rfl

theorem cell19_110228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 5].length) (baseStart_110228 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_110228 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_110228 prefixEnd_110228 := by exact prefixLift 110228
  have htrace : WordTrace (prefixWord ++ tailWord_110228) baseStart_110228 baseEnd_110228 := by
    simpa [prefixWord, tailWord_110228, baseEnd_110228] using wordTrace_append hprefix tailTrace_110228
  have hstable : (prefixWord ++ tailWord_110228).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110228).length < 2 ^ (prefixWord ++ tailWord_110228).sum := by decide
  have hdescent : baseEnd_110228 < baseStart_110228 := by decide
  rcases family_descends (prefixWord ++ tailWord_110228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110268 : List Nat := [2, 2, 2, 3, 1, 3, 2, 4]
def baseStart_110268 : Nat := 118140960795 + 110268 * 2 ^ 59
def prefixEnd_110268 : Nat := 4983230072969 + 3 ^ 40 * 110268 * 2
def baseEnd_110268 : Nat := 33552879887454702010603

theorem tailTrace_110268 : CollatzResearch.WordTrace tailWord_110268 prefixEnd_110268 33552879887454702010603 := by
  unfold tailWord_110268
  simp only [CollatzResearch.WordTrace]
  refine ⟨2010902182262671560097729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2681202909683562080130305 2010902182262671560097729)
  ·
    refine ⟨1508176636697003670073297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2010902182262671560097729 1508176636697003670073297)
    ·
      refine ⟨1131132477522752752554973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1508176636697003670073297 1131132477522752752554973)
      ·
        refine ⟨424174679071032282208115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1131132477522752752554973 424174679071032282208115)
        ·
          refine ⟨636262018606548423312173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 424174679071032282208115 636262018606548423312173)
          ·
            refine ⟨238598256977455658742065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 636262018606548423312173 238598256977455658742065)
            ·
              refine ⟨178948692733091744056549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 238598256977455658742065 178948692733091744056549)
              ·
                refine ⟨33552879887454702010603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 178948692733091744056549 33552879887454702010603)
                ·
                  rfl

theorem cell19_110268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 2, 4].length) (baseStart_110268 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_110268 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_110268 prefixEnd_110268 := by exact prefixLift 110268
  have htrace : WordTrace (prefixWord ++ tailWord_110268) baseStart_110268 baseEnd_110268 := by
    simpa [prefixWord, tailWord_110268, baseEnd_110268] using wordTrace_append hprefix tailTrace_110268
  have hstable : (prefixWord ++ tailWord_110268).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110268).length < 2 ^ (prefixWord ++ tailWord_110268).sum := by decide
  have hdescent : baseEnd_110268 < baseStart_110268 := by decide
  rcases family_descends (prefixWord ++ tailWord_110268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110285 : List Nat := [1, 6, 2, 1, 1, 1, 2, 5]
def baseStart_110285 : Nat := 118140960795 + 110285 * 2 ^ 59
def prefixEnd_110285 : Nat := 4983230072969 + 3 ^ 40 * 110285 * 2
def baseEnd_110285 : Nat := 33558052729603699632779

theorem tailTrace_110285 : CollatzResearch.WordTrace tailWord_110285 prefixEnd_110285 33558052729603699632779 := by
  unfold tailWord_110285
  simp only [CollatzResearch.WordTrace]
  refine ⟨4022424405463755023564309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2681616270309170015709539 4022424405463755023564309)
  ·
    refine ⟨188551144006113516729577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 4022424405463755023564309 188551144006113516729577)
    ·
      refine ⟨141413358004585137547183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188551144006113516729577 141413358004585137547183)
      ·
        refine ⟨212120037006877706320775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141413358004585137547183 212120037006877706320775)
        ·
          refine ⟨318180055510316559481163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212120037006877706320775 318180055510316559481163)
          ·
            refine ⟨477270083265474839221745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 318180055510316559481163 477270083265474839221745)
            ·
              refine ⟨357952562449106129416309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 477270083265474839221745 357952562449106129416309)
              ·
                refine ⟨33558052729603699632779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 357952562449106129416309 33558052729603699632779)
                ·
                  rfl

theorem cell19_110285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 5].length) (baseStart_110285 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_110285 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_110285 prefixEnd_110285 := by exact prefixLift 110285
  have htrace : WordTrace (prefixWord ++ tailWord_110285) baseStart_110285 baseEnd_110285 := by
    simpa [prefixWord, tailWord_110285, baseEnd_110285] using wordTrace_append hprefix tailTrace_110285
  have hstable : (prefixWord ++ tailWord_110285).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110285).length < 2 ^ (prefixWord ++ tailWord_110285).sum := by decide
  have hdescent : baseEnd_110285 < baseStart_110285 := by decide
  rcases family_descends (prefixWord ++ tailWord_110285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110289 : List Nat := [1, 2, 2, 1, 2, 4, 2, 5]
def baseStart_110289 : Nat := 118140960795 + 110289 * 2 ^ 59
def prefixEnd_110289 : Nat := 4983230072969 + 3 ^ 40 * 110289 * 2
def baseEnd_110289 : Nat := 33559269868932875543879

theorem tailTrace_110289 : CollatzResearch.WordTrace tailWord_110289 prefixEnd_110289 33559269868932875543879 := by
  unfold tailWord_110289
  simp only [CollatzResearch.WordTrace]
  refine ⟨4022570297449263706709921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2681713531632842471139947 4022570297449263706709921)
  ·
    refine ⟨3016927723086947780032441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4022570297449263706709921 3016927723086947780032441)
    ·
      refine ⟨2262695792315210835024331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3016927723086947780032441 2262695792315210835024331)
      ·
        refine ⟨3394043688472816252536497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2262695792315210835024331 3394043688472816252536497)
        ·
          refine ⟨2545532766354612189402373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3394043688472816252536497 2545532766354612189402373)
          ·
            refine ⟨477287393691489785512945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2545532766354612189402373 477287393691489785512945)
            ·
              refine ⟨357965545268617339134709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 477287393691489785512945 357965545268617339134709)
              ·
                refine ⟨33559269868932875543879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 357965545268617339134709 33559269868932875543879)
                ·
                  rfl

theorem cell19_110289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 5].length) (baseStart_110289 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_110289 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_110289 prefixEnd_110289 := by exact prefixLift 110289
  have htrace : WordTrace (prefixWord ++ tailWord_110289) baseStart_110289 baseEnd_110289 := by
    simpa [prefixWord, tailWord_110289, baseEnd_110289] using wordTrace_append hprefix tailTrace_110289
  have hstable : (prefixWord ++ tailWord_110289).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110289).length < 2 ^ (prefixWord ++ tailWord_110289).sum := by decide
  have hdescent : baseEnd_110289 < baseStart_110289 := by decide
  rcases family_descends (prefixWord ++ tailWord_110289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110327 : List Nat := [1, 1, 3, 1, 1, 1, 7, 4]
def baseStart_110327 : Nat := 118140960795 + 110327 * 2 ^ 59
def prefixEnd_110327 : Nat := 4983230072969 + 3 ^ 40 * 110327 * 2
def baseEnd_110327 : Nat := 33570832692560046699331

theorem tailTrace_110327 : CollatzResearch.WordTrace tailWord_110327 prefixEnd_110327 33570832692560046699331 := by
  unfold tailWord_110327
  simp only [CollatzResearch.WordTrace]
  refine ⟨4023956271311596196593235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2682637514207730797728823 4023956271311596196593235)
  ·
    refine ⟨6035934406967394294889853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4023956271311596196593235 6035934406967394294889853)
    ·
      refine ⟨2263475402612772860583695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6035934406967394294889853 2263475402612772860583695)
      ·
        refine ⟨3395213103919159290875543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2263475402612772860583695 3395213103919159290875543)
        ·
          refine ⟨5092819655878738936313315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3395213103919159290875543 5092819655878738936313315)
          ·
            refine ⟨7639229483818108404469973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5092819655878738936313315 7639229483818108404469973)
            ·
              refine ⟨179044441026986915729765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 7639229483818108404469973 179044441026986915729765)
              ·
                refine ⟨33570832692560046699331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 179044441026986915729765 33570832692560046699331)
                ·
                  rfl

theorem cell19_110327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 7, 4].length) (baseStart_110327 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_110327 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_110327 prefixEnd_110327 := by exact prefixLift 110327
  have htrace : WordTrace (prefixWord ++ tailWord_110327) baseStart_110327 baseEnd_110327 := by
    simpa [prefixWord, tailWord_110327, baseEnd_110327] using wordTrace_append hprefix tailTrace_110327
  have hstable : (prefixWord ++ tailWord_110327).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110327).length < 2 ^ (prefixWord ++ tailWord_110327).sum := by decide
  have hdescent : baseEnd_110327 < baseStart_110327 := by decide
  rcases family_descends (prefixWord ++ tailWord_110327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110344 : List Nat := [2, 1, 3, 2, 2, 1, 5, 3]
def baseStart_110344 : Nat := 118140960795 + 110344 * 2 ^ 59
def prefixEnd_110344 : Nat := 4983230072969 + 3 ^ 40 * 110344 * 2
def baseEnd_110344 : Nat := 33576005534709044321507

theorem tailTrace_110344 : CollatzResearch.WordTrace tailWord_110344 prefixEnd_110344 33576005534709044321507 := by
  unfold tailWord_110344
  simp only [CollatzResearch.WordTrace]
  refine ⟨2012288156125004049981043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2683050874833338733308057 2012288156125004049981043)
  ·
    refine ⟨3018432234187506074971565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2012288156125004049981043 3018432234187506074971565)
    ·
      refine ⟨1131912087820314778114337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3018432234187506074971565 1131912087820314778114337)
      ·
        refine ⟨848934065865236083585753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1131912087820314778114337 848934065865236083585753)
        ·
          refine ⟨636700549398927062689315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 848934065865236083585753 636700549398927062689315)
          ·
            refine ⟨955050824098390594033973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 636700549398927062689315 955050824098390594033973)
            ·
              refine ⟨89536014759224118190685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 955050824098390594033973 89536014759224118190685)
              ·
                refine ⟨33576005534709044321507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89536014759224118190685 33576005534709044321507)
                ·
                  rfl

theorem cell19_110344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 5, 3].length) (baseStart_110344 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_110344 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_110344 prefixEnd_110344 := by exact prefixLift 110344
  have htrace : WordTrace (prefixWord ++ tailWord_110344) baseStart_110344 baseEnd_110344 := by
    simpa [prefixWord, tailWord_110344, baseEnd_110344] using wordTrace_append hprefix tailTrace_110344
  have hstable : (prefixWord ++ tailWord_110344).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110344).length < 2 ^ (prefixWord ++ tailWord_110344).sum := by decide
  have hdescent : baseEnd_110344 < baseStart_110344 := by decide
  rcases family_descends (prefixWord ++ tailWord_110344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110399 : List Nat := [1, 1, 2, 2, 6, 2, 2, 3]
def baseStart_110399 : Nat := 118140960795 + 110399 * 2 ^ 59
def prefixEnd_110399 : Nat := 4983230072969 + 3 ^ 40 * 110399 * 2
def baseEnd_110399 : Nat := 33592741200485213099135

theorem tailTrace_110399 : CollatzResearch.WordTrace tailWord_110399 prefixEnd_110399 33592741200485213099135 := by
  unfold tailWord_110399
  simp only [CollatzResearch.WordTrace]
  refine ⟨4026582327050752493214251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2684388218033834995476167 4026582327050752493214251)
  ·
    refine ⟨6039873490576128739821377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4026582327050752493214251 6039873490576128739821377)
    ·
      refine ⟨4529905117932096554866033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6039873490576128739821377 4529905117932096554866033)
      ·
        refine ⟨3397428838449072416149525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4529905117932096554866033 3397428838449072416149525)
        ·
          refine ⟨159254476802300269507009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 3397428838449072416149525 159254476802300269507009)
          ·
            refine ⟨119440857601725202130257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159254476802300269507009 119440857601725202130257)
            ·
              refine ⟨89580643201293901597693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119440857601725202130257 89580643201293901597693)
              ·
                refine ⟨33592741200485213099135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89580643201293901597693 33592741200485213099135)
                ·
                  rfl

theorem cell19_110399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 2, 3].length) (baseStart_110399 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_110399 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_110399 prefixEnd_110399 := by exact prefixLift 110399
  have htrace : WordTrace (prefixWord ++ tailWord_110399) baseStart_110399 baseEnd_110399 := by
    simpa [prefixWord, tailWord_110399, baseEnd_110399] using wordTrace_append hprefix tailTrace_110399
  have hstable : (prefixWord ++ tailWord_110399).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110399).length < 2 ^ (prefixWord ++ tailWord_110399).sum := by decide
  have hdescent : baseEnd_110399 < baseStart_110399 := by decide
  rcases family_descends (prefixWord ++ tailWord_110399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110403 : List Nat := [1, 1, 1, 3, 1, 6, 1, 5]
def baseStart_110403 : Nat := 118140960795 + 110403 * 2 ^ 59
def prefixEnd_110403 : Nat := 4983230072969 + 3 ^ 40 * 110403 * 2
def baseEnd_110403 : Nat := 33593958339814389010235

theorem tailTrace_110403 : CollatzResearch.WordTrace tailWord_110403 prefixEnd_110403 33593958339814389010235 := by
  unfold tailWord_110403
  simp only [CollatzResearch.WordTrace]
  refine ⟨4026728219036261176359863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2684485479357507450906575 4026728219036261176359863)
  ·
    refine ⟨6040092328554391764539795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4026728219036261176359863 6040092328554391764539795)
    ·
      refine ⟨9060138492831587646809693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6040092328554391764539795 9060138492831587646809693)
      ·
        refine ⟨3397551934811845367553635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9060138492831587646809693 3397551934811845367553635)
        ·
          refine ⟨5096327902217768051330453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3397551934811845367553635 5096327902217768051330453)
          ·
            refine ⟨238890370416457877406115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 5096327902217768051330453 238890370416457877406115)
            ·
              refine ⟨358335555624686816109173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 238890370416457877406115 358335555624686816109173)
              ·
                refine ⟨33593958339814389010235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 358335555624686816109173 33593958339814389010235)
                ·
                  rfl

theorem cell19_110403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 5].length) (baseStart_110403 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_110403 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_110403 prefixEnd_110403 := by exact prefixLift 110403
  have htrace : WordTrace (prefixWord ++ tailWord_110403) baseStart_110403 baseEnd_110403 := by
    simpa [prefixWord, tailWord_110403, baseEnd_110403] using wordTrace_append hprefix tailTrace_110403
  have hstable : (prefixWord ++ tailWord_110403).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110403).length < 2 ^ (prefixWord ++ tailWord_110403).sum := by decide
  have hdescent : baseEnd_110403 < baseStart_110403 := by decide
  rcases family_descends (prefixWord ++ tailWord_110403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110420 : List Nat := [2, 4, 1, 1, 3, 3, 5]
def baseStart_110420 : Nat := 118140960795 + 110420 * 2 ^ 59
def prefixEnd_110420 : Nat := 4983230072969 + 3 ^ 40 * 110420 * 2
def baseEnd_110420 : Nat := 11199710393987795544137

theorem tailTrace_110420 : CollatzResearch.WordTrace tailWord_110420 prefixEnd_110420 11199710393987795544137 := by
  unfold tailWord_110420
  simp only [CollatzResearch.WordTrace]
  refine ⟨2013674129987336539864357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2684898839983115386485809 2013674129987336539864357)
  ·
    refine ⟨377563899372625601224567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2013674129987336539864357 377563899372625601224567)
    ·
      refine ⟨566345849058938401836851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377563899372625601224567 566345849058938401836851)
      ·
        refine ⟨849518773588407602755277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 566345849058938401836851 849518773588407602755277)
        ·
          refine ⟨318569540095652851033229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 849518773588407602755277 318569540095652851033229)
          ·
            refine ⟨119463577535869819137461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 318569540095652851033229 119463577535869819137461)
            ·
              refine ⟨11199710393987795544137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 119463577535869819137461 11199710393987795544137)
              ·
                rfl

theorem cell19_110420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 5].length) (baseStart_110420 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_110420 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_110420 prefixEnd_110420 := by exact prefixLift 110420
  have htrace : WordTrace (prefixWord ++ tailWord_110420) baseStart_110420 baseEnd_110420 := by
    simpa [prefixWord, tailWord_110420, baseEnd_110420] using wordTrace_append hprefix tailTrace_110420
  have hstable : (prefixWord ++ tailWord_110420).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110420).length < 2 ^ (prefixWord ++ tailWord_110420).sum := by decide
  have hdescent : baseEnd_110420 < baseStart_110420 := by decide
  rcases family_descends (prefixWord ++ tailWord_110420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110536 : List Nat := [2, 1, 3, 1, 4, 2, 6]
def baseStart_110536 : Nat := 118140960795 + 110536 * 2 ^ 59
def prefixEnd_110536 : Nat := 4983230072969 + 3 ^ 40 * 110536 * 2
def baseEnd_110536 : Nat := 11211476074169829351439

theorem tailTrace_110536 : CollatzResearch.WordTrace tailWord_110536 prefixEnd_110536 11211476074169829351439 := by
  unfold tailWord_110536
  simp only [CollatzResearch.WordTrace]
  refine ⟨2015789563777212445475731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2687719418369616593967641 2015789563777212445475731)
  ·
    refine ⟨3023684345665818668213597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2015789563777212445475731 3023684345665818668213597)
    ·
      refine ⟨1133881629624682000580099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3023684345665818668213597 1133881629624682000580099)
      ·
        refine ⟨1700822444437023000870149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1133881629624682000580099 1700822444437023000870149)
        ·
          refine ⟨318904208331941812663153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1700822444437023000870149 318904208331941812663153)
          ·
            refine ⟨239178156248956359497365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 318904208331941812663153 239178156248956359497365)
            ·
              refine ⟨11211476074169829351439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 239178156248956359497365 11211476074169829351439)
              ·
                rfl

theorem cell19_110536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 6].length) (baseStart_110536 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_110536 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_110536 prefixEnd_110536 := by exact prefixLift 110536
  have htrace : WordTrace (prefixWord ++ tailWord_110536) baseStart_110536 baseEnd_110536 := by
    simpa [prefixWord, tailWord_110536, baseEnd_110536] using wordTrace_append hprefix tailTrace_110536
  have hstable : (prefixWord ++ tailWord_110536).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110536).length < 2 ^ (prefixWord ++ tailWord_110536).sum := by decide
  have hdescent : baseEnd_110536 < baseStart_110536 := by decide
  rcases family_descends (prefixWord ++ tailWord_110536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110802 : List Nat := [3, 2, 2, 2, 1, 2, 2, 5]
def baseStart_110802 : Nat := 118140960795 + 110802 * 2 ^ 59
def prefixEnd_110802 : Nat := 4983230072969 + 3 ^ 40 * 110802 * 2
def baseEnd_110802 : Nat := 33715367987899686142481

theorem tailTrace_110802 : CollatzResearch.WordTrace tailWord_110802 prefixEnd_110802 33715367987899686142481 := by
  unfold tailWord_110802
  simp only [CollatzResearch.WordTrace]
  refine ⟨1010320236147688080033665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2694187296393834880089773 1010320236147688080033665)
  ·
    refine ⟨757740177110766060025249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1010320236147688080033665 757740177110766060025249)
    ·
      refine ⟨568305132833074545018937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 757740177110766060025249 568305132833074545018937)
      ·
        refine ⟨426228849624805908764203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 568305132833074545018937 426228849624805908764203)
        ·
          refine ⟨639343274437208863146305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 426228849624805908764203 639343274437208863146305)
          ·
            refine ⟨479507455827906647359729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 639343274437208863146305 479507455827906647359729)
            ·
              refine ⟨359630591870929985519797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 479507455827906647359729 359630591870929985519797)
              ·
                refine ⟨33715367987899686142481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 359630591870929985519797 33715367987899686142481)
                ·
                  rfl

theorem cell19_110802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 5].length) (baseStart_110802 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_110802 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_110802 prefixEnd_110802 := by exact prefixLift 110802
  have htrace : WordTrace (prefixWord ++ tailWord_110802) baseStart_110802 baseEnd_110802 := by
    simpa [prefixWord, tailWord_110802, baseEnd_110802] using wordTrace_append hprefix tailTrace_110802
  have hstable : (prefixWord ++ tailWord_110802).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110802).length < 2 ^ (prefixWord ++ tailWord_110802).sum := by decide
  have hdescent : baseEnd_110802 < baseStart_110802 := by decide
  rcases family_descends (prefixWord ++ tailWord_110802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110819 : List Nat := [1, 1, 1, 8, 2, 6]
def baseStart_110819 : Nat := 118140960795 + 110819 * 2 ^ 59
def prefixEnd_110819 : Nat := 4983230072969 + 3 ^ 40 * 110819 * 2
def baseEnd_110819 : Nat := 3746726758894298196073

theorem tailTrace_110819 : CollatzResearch.WordTrace tailWord_110819 prefixEnd_110819 3746726758894298196073 := by
  unfold tailWord_110819
  simp only [CollatzResearch.WordTrace]
  refine ⟨4041900985529164223503511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2694600657019442815669007 4041900985529164223503511)
  ·
    refine ⟨6062851478293746335255267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4041900985529164223503511 6062851478293746335255267)
    ·
      refine ⟨9094277217440619502882901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6062851478293746335255267 9094277217440619502882901)
      ·
        refine ⟨106573561141882259799409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 9094277217440619502882901 106573561141882259799409)
        ·
          refine ⟨79930170856411694849557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106573561141882259799409 79930170856411694849557)
          ·
            refine ⟨3746726758894298196073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 79930170856411694849557 3746726758894298196073)
            ·
              rfl

theorem cell19_110819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 6].length) (baseStart_110819 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_110819 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_110819 prefixEnd_110819 := by exact prefixLift 110819
  have htrace : WordTrace (prefixWord ++ tailWord_110819) baseStart_110819 baseEnd_110819 := by
    simpa [prefixWord, tailWord_110819, baseEnd_110819] using wordTrace_append hprefix tailTrace_110819
  have hstable : (prefixWord ++ tailWord_110819).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110819).length < 2 ^ (prefixWord ++ tailWord_110819).sum := by decide
  have hdescent : baseEnd_110819 < baseStart_110819 := by decide
  rcases family_descends (prefixWord ++ tailWord_110819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110855 : List Nat := [1, 1, 4, 5, 1, 1, 3, 3]
def baseStart_110855 : Nat := 118140960795 + 110855 * 2 ^ 59
def prefixEnd_110855 : Nat := 4983230072969 + 3 ^ 40 * 110855 * 2
def baseEnd_110855 : Nat := 33731495084011266964559

theorem tailTrace_110855 : CollatzResearch.WordTrace tailWord_110855 prefixEnd_110855 33731495084011266964559 := by
  unfold tailWord_110855
  simp only [CollatzResearch.WordTrace]
  refine ⟨4043214013398742371814019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2695476008932494914542679 4043214013398742371814019)
  ·
    refine ⟨6064821020098113557721029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4043214013398742371814019 6064821020098113557721029)
    ·
      refine ⟨1137153941268396292072693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6064821020098113557721029 1137153941268396292072693)
      ·
        refine ⟨106608181993912152381815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1137153941268396292072693 106608181993912152381815)
        ·
          refine ⟨159912272990868228572723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106608181993912152381815 159912272990868228572723)
          ·
            refine ⟨239868409486302342859085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159912272990868228572723 239868409486302342859085)
            ·
              refine ⟨89950653557363378572157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 239868409486302342859085 89950653557363378572157)
              ·
                refine ⟨33731495084011266964559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89950653557363378572157 33731495084011266964559)
                ·
                  rfl

theorem cell19_110855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 3, 3].length) (baseStart_110855 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_110855 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_110855 prefixEnd_110855 := by exact prefixLift 110855
  have htrace : WordTrace (prefixWord ++ tailWord_110855) baseStart_110855 baseEnd_110855 := by
    simpa [prefixWord, tailWord_110855, baseEnd_110855] using wordTrace_append hprefix tailTrace_110855
  have hstable : (prefixWord ++ tailWord_110855).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110855).length < 2 ^ (prefixWord ++ tailWord_110855).sum := by decide
  have hdescent : baseEnd_110855 < baseStart_110855 := by decide
  rcases family_descends (prefixWord ++ tailWord_110855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110859 : List Nat := [1, 1, 1, 1, 5, 2, 5, 3]
def baseStart_110859 : Nat := 118140960795 + 110859 * 2 ^ 59
def prefixEnd_110859 : Nat := 4983230072969 + 3 ^ 40 * 110859 * 2
def baseEnd_110859 : Nat := 33732712223340442875659

theorem tailTrace_110859 : CollatzResearch.WordTrace tailWord_110859 prefixEnd_110859 33732712223340442875659 := by
  unfold tailWord_110859
  simp only [CollatzResearch.WordTrace]
  refine ⟨4043359905384251054959631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2695573270256167369973087 4043359905384251054959631)
  ·
    refine ⟨6065039858076376582439447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4043359905384251054959631 6065039858076376582439447)
    ·
      refine ⟨9097559787114564873659171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6065039858076376582439447 9097559787114564873659171)
      ·
        refine ⟨13646339680671847310488757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9097559787114564873659171 13646339680671847310488757)
        ·
          refine ⟨1279344345062985685358321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13646339680671847310488757 1279344345062985685358321)
          ·
            refine ⟨959508258797239264018741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1279344345062985685358321 959508258797239264018741)
            ·
              refine ⟨89953899262241181001757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 959508258797239264018741 89953899262241181001757)
              ·
                refine ⟨33732712223340442875659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89953899262241181001757 33732712223340442875659)
                ·
                  rfl

theorem cell19_110859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 5, 3].length) (baseStart_110859 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_110859 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_110859 prefixEnd_110859 := by exact prefixLift 110859
  have htrace : WordTrace (prefixWord ++ tailWord_110859) baseStart_110859 baseEnd_110859 := by
    simpa [prefixWord, tailWord_110859, baseEnd_110859] using wordTrace_append hprefix tailTrace_110859
  have hstable : (prefixWord ++ tailWord_110859).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110859).length < 2 ^ (prefixWord ++ tailWord_110859).sum := by decide
  have hdescent : baseEnd_110859 < baseStart_110859 := by decide
  rcases family_descends (prefixWord ++ tailWord_110859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110899 : List Nat := [1, 1, 1, 2, 5, 1, 2, 6]
def baseStart_110899 : Nat := 118140960795 + 110899 * 2 ^ 59
def prefixEnd_110899 : Nat := 4983230072969 + 3 ^ 40 * 110899 * 2
def baseEnd_110899 : Nat := 33744883616632201986661

theorem tailTrace_110899 : CollatzResearch.WordTrace tailWord_110899 prefixEnd_110899 33744883616632201986661 := by
  unfold tailWord_110899
  simp only [CollatzResearch.WordTrace]
  refine ⟨4044818825239337886415751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2696545883492891924277167 4044818825239337886415751)
  ·
    refine ⟨6067228237859006829623627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4044818825239337886415751 6067228237859006829623627)
    ·
      refine ⟨9100842356788510244435441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6067228237859006829623627 9100842356788510244435441)
      ·
        refine ⟨6825631767591382683326581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9100842356788510244435441 6825631767591382683326581)
        ·
          refine ⟨639902978211692126561867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6825631767591382683326581 639902978211692126561867)
          ·
            refine ⟨959854467317538189842801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 639902978211692126561867 959854467317538189842801)
            ·
              refine ⟨719890850488153642382101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 959854467317538189842801 719890850488153642382101)
              ·
                refine ⟨33744883616632201986661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 719890850488153642382101 33744883616632201986661)
                ·
                  rfl

theorem cell19_110899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 6].length) (baseStart_110899 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_110899 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_110899 prefixEnd_110899 := by exact prefixLift 110899
  have htrace : WordTrace (prefixWord ++ tailWord_110899) baseStart_110899 baseEnd_110899 := by
    simpa [prefixWord, tailWord_110899, baseEnd_110899] using wordTrace_append hprefix tailTrace_110899
  have hstable : (prefixWord ++ tailWord_110899).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110899).length < 2 ^ (prefixWord ++ tailWord_110899).sum := by decide
  have hdescent : baseEnd_110899 < baseStart_110899 := by decide
  rcases family_descends (prefixWord ++ tailWord_110899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110933 : List Nat := [1, 3, 2, 2, 5, 1, 5]
def baseStart_110933 : Nat := 118140960795 + 110933 * 2 ^ 59
def prefixEnd_110933 : Nat := 4983230072969 + 3 ^ 40 * 110933 * 2
def baseEnd_110933 : Nat := 11251743100310065743671

theorem tailTrace_110933 : CollatzResearch.WordTrace tailWord_110933 prefixEnd_110933 11251743100310065743671 := by
  unfold tailWord_110933
  simp only [CollatzResearch.WordTrace]
  refine ⟨4046058907116161693153453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2697372604744107795435635 4046058907116161693153453)
  ·
    refine ⟨1517272090168560634932545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4046058907116161693153453 1517272090168560634932545)
    ·
      refine ⟨1137954067626420476199409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1517272090168560634932545 1137954067626420476199409)
      ·
        refine ⟨853465550719815357149557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1137954067626420476199409 853465550719815357149557)
        ·
          refine ⟨80012395379982689732771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 853465550719815357149557 80012395379982689732771)
          ·
            refine ⟨120018593069974034599157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80012395379982689732771 120018593069974034599157)
            ·
              refine ⟨11251743100310065743671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 120018593069974034599157 11251743100310065743671)
              ·
                rfl

theorem cell19_110933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 5].length) (baseStart_110933 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_110933 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_110933 prefixEnd_110933 := by exact prefixLift 110933
  have htrace : WordTrace (prefixWord ++ tailWord_110933) baseStart_110933 baseEnd_110933 := by
    simpa [prefixWord, tailWord_110933, baseEnd_110933] using wordTrace_append hprefix tailTrace_110933
  have hstable : (prefixWord ++ tailWord_110933).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110933).length < 2 ^ (prefixWord ++ tailWord_110933).sum := by decide
  have hdescent : baseEnd_110933 < baseStart_110933 := by decide
  rcases family_descends (prefixWord ++ tailWord_110933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110954 : List Nat := [3, 1, 3, 3, 1, 1, 1, 6]
def baseStart_110954 : Nat := 118140960795 + 110954 * 2 ^ 59
def prefixEnd_110954 : Nat := 4983230072969 + 3 ^ 40 * 110954 * 2
def baseEnd_110954 : Nat := 33761619282408370764289

theorem tailTrace_110954 : CollatzResearch.WordTrace tailWord_110954 prefixEnd_110954 33761619282408370764289 := by
  unfold tailWord_110954
  simp only [CollatzResearch.WordTrace]
  refine ⟨1011706210010020569916979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2697883226693388186445277 1011706210010020569916979)
  ·
    refine ⟨1517559315015030854875469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1011706210010020569916979 1517559315015030854875469)
    ·
      refine ⟨569084743130636570578301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1517559315015030854875469 569084743130636570578301)
      ·
        refine ⟨213406778673988713966863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 569084743130636570578301 213406778673988713966863)
        ·
          refine ⟨320110168010983070950295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213406778673988713966863 320110168010983070950295)
          ·
            refine ⟨480165252016474606425443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 320110168010983070950295 480165252016474606425443)
            ·
              refine ⟨720247878024711909638165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 480165252016474606425443 720247878024711909638165)
              ·
                refine ⟨33761619282408370764289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 720247878024711909638165 33761619282408370764289)
                ·
                  rfl

theorem cell19_110954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 6].length) (baseStart_110954 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_110954 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_110954 prefixEnd_110954 := by exact prefixLift 110954
  have htrace : WordTrace (prefixWord ++ tailWord_110954) baseStart_110954 baseEnd_110954 := by
    simpa [prefixWord, tailWord_110954, baseEnd_110954] using wordTrace_append hprefix tailTrace_110954
  have hstable : (prefixWord ++ tailWord_110954).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110954).length < 2 ^ (prefixWord ++ tailWord_110954).sum := by decide
  have hdescent : baseEnd_110954 < baseStart_110954 := by decide
  rcases family_descends (prefixWord ++ tailWord_110954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110994 : List Nat := [3, 2, 3, 11]
def baseStart_110994 : Nat := 118140960795 + 110994 * 2 ^ 59
def prefixEnd_110994 : Nat := 4983230072969 + 3 ^ 40 * 110994 * 2
def baseEnd_110994 : Nat := 416960378712347282411

theorem tailTrace_110994 : CollatzResearch.WordTrace tailWord_110994 prefixEnd_110994 416960378712347282411 := by
  unfold tailWord_110994
  simp only [CollatzResearch.WordTrace]
  refine ⟨1012070939973792277781009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2698855839930112740749357 1012070939973792277781009)
  ·
    refine ⟨759053204980344208335757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1012070939973792277781009 759053204980344208335757)
    ·
      refine ⟨284644951867629078125909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 759053204980344208335757 284644951867629078125909)
      ·
        refine ⟨416960378712347282411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 11 284644951867629078125909 416960378712347282411)
        ·
          rfl

theorem cell19_110994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 11].length) (baseStart_110994 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_110994 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_110994 prefixEnd_110994 := by exact prefixLift 110994
  have htrace : WordTrace (prefixWord ++ tailWord_110994) baseStart_110994 baseEnd_110994 := by
    simpa [prefixWord, tailWord_110994, baseEnd_110994] using wordTrace_append hprefix tailTrace_110994
  have hstable : (prefixWord ++ tailWord_110994).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110994).length < 2 ^ (prefixWord ++ tailWord_110994).sum := by decide
  have hdescent : baseEnd_110994 < baseStart_110994 := by decide
  rcases family_descends (prefixWord ++ tailWord_110994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111011 : List Nat := [1, 1, 1, 4, 1, 6, 1, 4]
def baseStart_111011 : Nat := 118140960795 + 111011 * 2 ^ 59
def prefixEnd_111011 : Nat := 4983230072969 + 3 ^ 40 * 111011 * 2
def baseEnd_111011 : Nat := 33778963517849127497467

theorem tailTrace_111011 : CollatzResearch.WordTrace tailWord_111011 prefixEnd_111011 33778963517849127497467 := by
  unfold tailWord_111011
  simp only [CollatzResearch.WordTrace]
  refine ⟨4048903800833581014492887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2699269200555720676328591 4048903800833581014492887)
  ·
    refine ⟨6073355701250371521739331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4048903800833581014492887 6073355701250371521739331)
    ·
      refine ⟨9110033551875557282608997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6073355701250371521739331 9110033551875557282608997)
      ·
        refine ⟨1708131290976666990489187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9110033551875557282608997 1708131290976666990489187)
        ·
          refine ⟨2562196936465000485733781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1708131290976666990489187 2562196936465000485733781)
          ·
            refine ⟨120102981396796897768771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 2562196936465000485733781 120102981396796897768771)
            ·
              refine ⟨180154472095195346653157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120102981396796897768771 180154472095195346653157)
              ·
                refine ⟨33778963517849127497467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 180154472095195346653157 33778963517849127497467)
                ·
                  rfl

theorem cell19_111011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 1, 4].length) (baseStart_111011 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_111011 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_111011 prefixEnd_111011 := by exact prefixLift 111011
  have htrace : WordTrace (prefixWord ++ tailWord_111011) baseStart_111011 baseEnd_111011 := by
    simpa [prefixWord, tailWord_111011, baseEnd_111011] using wordTrace_append hprefix tailTrace_111011
  have hstable : (prefixWord ++ tailWord_111011).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111011).length < 2 ^ (prefixWord ++ tailWord_111011).sum := by decide
  have hdescent : baseEnd_111011 < baseStart_111011 := by decide
  rcases family_descends (prefixWord ++ tailWord_111011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111085 : List Nat := [1, 5, 1, 3, 1, 1, 4, 3]
def baseStart_111085 : Nat := 118140960795 + 111085 * 2 ^ 59
def prefixEnd_111085 : Nat := 4983230072969 + 3 ^ 40 * 111085 * 2
def baseEnd_111085 : Nat := 33801480595438881852821

theorem tailTrace_111085 : CollatzResearch.WordTrace tailWord_111085 prefixEnd_111085 33801480595438881852821 := by
  unfold tailWord_111085
  simp only [CollatzResearch.WordTrace]
  refine ⟨4051602802565491652686709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2701068535043661101791139 4051602802565491652686709)
  ·
    refine ⟨379837762740514842439379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4051602802565491652686709 379837762740514842439379)
    ·
      refine ⟨569756644110772263659069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379837762740514842439379 569756644110772263659069)
      ·
        refine ⟨213658741541539598872151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 569756644110772263659069 213658741541539598872151)
        ·
          refine ⟨320488112312309398308227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213658741541539598872151 320488112312309398308227)
          ·
            refine ⟨480732168468464097462341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 320488112312309398308227 480732168468464097462341)
            ·
              refine ⟨90137281587837018274189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 480732168468464097462341 90137281587837018274189)
              ·
                refine ⟨33801480595438881852821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90137281587837018274189 33801480595438881852821)
                ·
                  rfl

theorem cell19_111085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 4, 3].length) (baseStart_111085 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_111085 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_111085 prefixEnd_111085 := by exact prefixLift 111085
  have htrace : WordTrace (prefixWord ++ tailWord_111085) baseStart_111085 baseEnd_111085 := by
    simpa [prefixWord, tailWord_111085, baseEnd_111085] using wordTrace_append hprefix tailTrace_111085
  have hstable : (prefixWord ++ tailWord_111085).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111085).length < 2 ^ (prefixWord ++ tailWord_111085).sum := by decide
  have hdescent : baseEnd_111085 < baseStart_111085 := by decide
  rcases family_descends (prefixWord ++ tailWord_111085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111089 : List Nat := [1, 2, 2, 2, 3, 1, 3, 5]
def baseStart_111089 : Nat := 118140960795 + 111089 * 2 ^ 59
def prefixEnd_111089 : Nat := 4983230072969 + 3 ^ 40 * 111089 * 2
def baseEnd_111089 : Nat := 33802697734768057763921

theorem tailTrace_111089 : CollatzResearch.WordTrace tailWord_111089 prefixEnd_111089 33802697734768057763921 := by
  unfold tailWord_111089
  simp only [CollatzResearch.WordTrace]
  refine ⟨4051748694551000335832321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2701165796367333557221547 4051748694551000335832321)
  ·
    refine ⟨3038811520913250251874241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4051748694551000335832321 3038811520913250251874241)
    ·
      refine ⟨2279108640684937688905681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3038811520913250251874241 2279108640684937688905681)
      ·
        refine ⟨1709331480513703266679261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2279108640684937688905681 1709331480513703266679261)
        ·
          refine ⟨640999305192638725004723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1709331480513703266679261 640999305192638725004723)
          ·
            refine ⟨961498957788958087507085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 640999305192638725004723 961498957788958087507085)
            ·
              refine ⟨360562109170859282815157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 961498957788958087507085 360562109170859282815157)
              ·
                refine ⟨33802697734768057763921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 360562109170859282815157 33802697734768057763921)
                ·
                  rfl

theorem cell19_111089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 5].length) (baseStart_111089 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_111089 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_111089 prefixEnd_111089 := by exact prefixLift 111089
  have htrace : WordTrace (prefixWord ++ tailWord_111089) baseStart_111089 baseEnd_111089 := by
    simpa [prefixWord, tailWord_111089, baseEnd_111089] using wordTrace_append hprefix tailTrace_111089
  have hstable : (prefixWord ++ tailWord_111089).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111089).length < 2 ^ (prefixWord ++ tailWord_111089).sum := by decide
  have hdescent : baseEnd_111089 < baseStart_111089 := by decide
  rcases family_descends (prefixWord ++ tailWord_111089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111144 : List Nat := [2, 1, 5, 2, 1, 1, 2, 5]
def baseStart_111144 : Nat := 118140960795 + 111144 * 2 ^ 59
def prefixEnd_111144 : Nat := 4983230072969 + 3 ^ 40 * 111144 * 2
def baseEnd_111144 : Nat := 33819433400544226541549

theorem tailTrace_111144 : CollatzResearch.WordTrace tailWord_111144 prefixEnd_111144 33819433400544226541549 := by
  unfold tailWord_111144
  simp only [CollatzResearch.WordTrace]
  refine ⟨2026877354675872364542243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2702503139567829819389657 2026877354675872364542243)
  ·
    refine ⟨3040316032013808546813365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2026877354675872364542243 3040316032013808546813365)
    ·
      refine ⟨285029628001294551263753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3040316032013808546813365 285029628001294551263753)
      ·
        refine ⟨213772221000970913447815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 285029628001294551263753 213772221000970913447815)
        ·
          refine ⟨320658331501456370171723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213772221000970913447815 320658331501456370171723)
          ·
            refine ⟨480987497252184555257585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 320658331501456370171723 480987497252184555257585)
            ·
              refine ⟨360740622939138416443189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 480987497252184555257585 360740622939138416443189)
              ·
                refine ⟨33819433400544226541549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 360740622939138416443189 33819433400544226541549)
                ·
                  rfl

theorem cell19_111144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 5].length) (baseStart_111144 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_111144 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_111144 prefixEnd_111144 := by exact prefixLift 111144
  have htrace : WordTrace (prefixWord ++ tailWord_111144) baseStart_111144 baseEnd_111144 := by
    simpa [prefixWord, tailWord_111144, baseEnd_111144] using wordTrace_append hprefix tailTrace_111144
  have hstable : (prefixWord ++ tailWord_111144).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111144).length < 2 ^ (prefixWord ++ tailWord_111144).sum := by decide
  have hdescent : baseEnd_111144 < baseStart_111144 := by decide
  rcases family_descends (prefixWord ++ tailWord_111144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111165 : List Nat := [1, 4, 1, 3, 2, 8]
def baseStart_111165 : Nat := 118140960795 + 111165 * 2 ^ 59
def prefixEnd_111165 : Nat := 4983230072969 + 3 ^ 40 * 111165 * 2
def baseEnd_111165 : Nat := 3758424820224711119425

theorem tailTrace_111165 : CollatzResearch.WordTrace tailWord_111165 prefixEnd_111165 3758424820224711119425 := by
  unfold tailWord_111165
  simp only [CollatzResearch.WordTrace]
  refine ⟨4054520642275665315598949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2703013761517110210399299 4054520642275665315598949)
  ·
    refine ⟨760222620426687246674803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4054520642275665315598949 760222620426687246674803)
    ·
      refine ⟨1140333930640030870012205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 760222620426687246674803 1140333930640030870012205)
      ·
        refine ⟨427625223990011576254577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1140333930640030870012205 427625223990011576254577)
        ·
          refine ⟨320718917992508682190933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 427625223990011576254577 320718917992508682190933)
          ·
            refine ⟨3758424820224711119425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 320718917992508682190933 3758424820224711119425)
            ·
              rfl

theorem cell19_111165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 8].length) (baseStart_111165 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_111165 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_111165 prefixEnd_111165 := by exact prefixLift 111165
  have htrace : WordTrace (prefixWord ++ tailWord_111165) baseStart_111165 baseEnd_111165 := by
    simpa [prefixWord, tailWord_111165, baseEnd_111165] using wordTrace_append hprefix tailTrace_111165
  have hstable : (prefixWord ++ tailWord_111165).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111165).length < 2 ^ (prefixWord ++ tailWord_111165).sum := by decide
  have hdescent : baseEnd_111165 < baseStart_111165 := by decide
  rcases family_descends (prefixWord ++ tailWord_111165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111201 : List Nat := [1, 2, 3, 1, 1, 5, 3, 3]
def baseStart_111201 : Nat := 118140960795 + 111201 * 2 ^ 59
def prefixEnd_111201 : Nat := 4983230072969 + 3 ^ 40 * 111201 * 2
def baseEnd_111201 : Nat := 33836777635984983274727

theorem tailTrace_111201 : CollatzResearch.WordTrace tailWord_111201 prefixEnd_111201 33836777635984983274727 := by
  unfold tailWord_111201
  simp only [CollatzResearch.WordTrace]
  refine ⟨4055833670145243463909457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2703889113430162309272971 4055833670145243463909457)
  ·
    refine ⟨3041875252608932597932093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4055833670145243463909457 3041875252608932597932093)
    ·
      refine ⟨1140703219728349724224535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3041875252608932597932093 1140703219728349724224535)
      ·
        refine ⟨1711054829592524586336803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1140703219728349724224535 1711054829592524586336803)
        ·
          refine ⟨2566582244388786879505205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1711054829592524586336803 2566582244388786879505205)
          ·
            refine ⟨240617085411448769953613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2566582244388786879505205 240617085411448769953613)
            ·
              refine ⟨90231407029293288732605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 240617085411448769953613 90231407029293288732605)
              ·
                refine ⟨33836777635984983274727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90231407029293288732605 33836777635984983274727)
                ·
                  rfl

theorem cell19_111201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 3, 3].length) (baseStart_111201 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_111201 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_111201 prefixEnd_111201 := by exact prefixLift 111201
  have htrace : WordTrace (prefixWord ++ tailWord_111201) baseStart_111201 baseEnd_111201 := by
    simpa [prefixWord, tailWord_111201, baseEnd_111201] using wordTrace_append hprefix tailTrace_111201
  have hstable : (prefixWord ++ tailWord_111201).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111201).length < 2 ^ (prefixWord ++ tailWord_111201).sum := by decide
  have hdescent : baseEnd_111201 < baseStart_111201 := by decide
  rcases family_descends (prefixWord ++ tailWord_111201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111277 : List Nat := [1, 5, 2, 1, 1, 4, 5]
def baseStart_111277 : Nat := 118140960795 + 111277 * 2 ^ 59
def prefixEnd_111277 : Nat := 4983230072969 + 3 ^ 40 * 111277 * 2
def baseEnd_111277 : Nat := 11286634427746441861877

theorem tailTrace_111277 : CollatzResearch.WordTrace tailWord_111277 prefixEnd_111277 11286634427746441861877 := by
  unfold tailWord_111277
  simp only [CollatzResearch.WordTrace]
  refine ⟨4058605617869908443676085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2705737078579938962450723 4058605617869908443676085)
  ·
    refine ⟨380494276675303916594633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4058605617869908443676085 380494276675303916594633)
    ·
      refine ⟨285370707506477937445975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 380494276675303916594633 285370707506477937445975)
      ·
        refine ⟨428056061259716906168963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285370707506477937445975 428056061259716906168963)
        ·
          refine ⟨642084091889575359253445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 428056061259716906168963 642084091889575359253445)
          ·
            refine ⟨120390767229295379860021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 642084091889575359253445 120390767229295379860021)
            ·
              refine ⟨11286634427746441861877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 120390767229295379860021 11286634427746441861877)
              ·
                rfl

theorem cell19_111277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 5].length) (baseStart_111277 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_111277 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_111277 prefixEnd_111277 := by exact prefixLift 111277
  have htrace : WordTrace (prefixWord ++ tailWord_111277) baseStart_111277 baseEnd_111277 := by
    simpa [prefixWord, tailWord_111277, baseEnd_111277] using wordTrace_append hprefix tailTrace_111277
  have hstable : (prefixWord ++ tailWord_111277).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111277).length < 2 ^ (prefixWord ++ tailWord_111277).sum := by decide
  have hdescent : baseEnd_111277 < baseStart_111277 := by decide
  rcases family_descends (prefixWord ++ tailWord_111277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111279 : List Nat := [1, 1, 2, 1, 2, 7, 5]
def baseStart_111279 : Nat := 118140960795 + 111279 * 2 ^ 59
def prefixEnd_111279 : Nat := 4983230072969 + 3 ^ 40 * 111279 * 2
def baseEnd_111279 : Nat := 11286837284301304513727

theorem tailTrace_111279 : CollatzResearch.WordTrace tailWord_111279 prefixEnd_111279 11286837284301304513727 := by
  unfold tailWord_111279
  simp only [CollatzResearch.WordTrace]
  refine ⟨4058678563862662785248891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2705785709241775190165927 4058678563862662785248891)
  ·
    refine ⟨6088017845793994177873337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4058678563862662785248891 6088017845793994177873337)
    ·
      refine ⟨4566013384345495633405003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6088017845793994177873337 4566013384345495633405003)
      ·
        refine ⟨6849020076518243450107505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4566013384345495633405003 6849020076518243450107505)
        ·
          refine ⟨5136765057388682587580629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6849020076518243450107505 5136765057388682587580629)
          ·
            refine ⟨120392931032547248146421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 5136765057388682587580629 120392931032547248146421)
            ·
              refine ⟨11286837284301304513727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 120392931032547248146421 11286837284301304513727)
              ·
                rfl

theorem cell19_111279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 5].length) (baseStart_111279 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_111279 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_111279 prefixEnd_111279 := by exact prefixLift 111279
  have htrace : WordTrace (prefixWord ++ tailWord_111279) baseStart_111279 baseEnd_111279 := by
    simpa [prefixWord, tailWord_111279, baseEnd_111279] using wordTrace_append hprefix tailTrace_111279
  have hstable : (prefixWord ++ tailWord_111279).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111279).length < 2 ^ (prefixWord ++ tailWord_111279).sum := by decide
  have hdescent : baseEnd_111279 < baseStart_111279 := by decide
  rcases family_descends (prefixWord ++ tailWord_111279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111336 : List Nat := [2, 1, 4, 1, 4, 7]
def baseStart_111336 : Nat := 118140960795 + 111336 * 2 ^ 59
def prefixEnd_111336 : Nat := 4983230072969 + 3 ^ 40 * 111336 * 2
def baseEnd_111336 : Nat := 3764206232038296697151

theorem tailTrace_111336 : CollatzResearch.WordTrace tailWord_111336 prefixEnd_111336 3764206232038296697151 := by
  unfold tailWord_111336
  simp only [CollatzResearch.WordTrace]
  refine ⟨2030378762328080760036931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2707171683104107680049241 2030378762328080760036931)
  ·
    refine ⟨3045568143492121140055397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2030378762328080760036931 3045568143492121140055397)
    ·
      refine ⟨571044026904772713760387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3045568143492121140055397 571044026904772713760387)
      ·
        refine ⟨856566040357159070640581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 571044026904772713760387 856566040357159070640581)
        ·
          refine ⟨160606132566967325745109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 856566040357159070640581 160606132566967325745109)
          ·
            refine ⟨3764206232038296697151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 160606132566967325745109 3764206232038296697151)
            ·
              rfl

theorem cell19_111336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 7].length) (baseStart_111336 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_111336 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_111336 prefixEnd_111336 := by exact prefixLift 111336
  have htrace : WordTrace (prefixWord ++ tailWord_111336) baseStart_111336 baseEnd_111336 := by
    simpa [prefixWord, tailWord_111336, baseEnd_111336] using wordTrace_append hprefix tailTrace_111336
  have hstable : (prefixWord ++ tailWord_111336).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111336).length < 2 ^ (prefixWord ++ tailWord_111336).sum := by decide
  have hdescent : baseEnd_111336 < baseStart_111336 := by decide
  rcases family_descends (prefixWord ++ tailWord_111336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111425 : List Nat := [1, 2, 5, 3, 1, 2, 2, 3]
def baseStart_111425 : Nat := 118140960795 + 111425 * 2 ^ 59
def prefixEnd_111425 : Nat := 4983230072969 + 3 ^ 40 * 111425 * 2
def baseEnd_111425 : Nat := 33904937438418834296339

theorem tailTrace_111425 : CollatzResearch.WordTrace tailWord_111425 prefixEnd_111425 33904937438418834296339 := by
  unfold tailWord_111425
  simp only [CollatzResearch.WordTrace]
  refine ⟨4064003621333729720063729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2709335747555819813375819 4064003621333729720063729)
  ·
    refine ⟨3048002716000297290047797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4064003621333729720063729 3048002716000297290047797)
    ·
      refine ⟨285750254625027870941981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3048002716000297290047797 285750254625027870941981)
      ·
        refine ⟨107156345484385451603243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 285750254625027870941981 107156345484385451603243)
        ·
          refine ⟨160734518226578177404865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107156345484385451603243 160734518226578177404865)
          ·
            refine ⟨120550888669933633053649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160734518226578177404865 120550888669933633053649)
            ·
              refine ⟨90413166502450224790237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120550888669933633053649 90413166502450224790237)
              ·
                refine ⟨33904937438418834296339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90413166502450224790237 33904937438418834296339)
                ·
                  rfl

theorem cell19_111425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 2, 3].length) (baseStart_111425 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_111425 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_111425 prefixEnd_111425 := by exact prefixLift 111425
  have htrace : WordTrace (prefixWord ++ tailWord_111425) baseStart_111425 baseEnd_111425 := by
    simpa [prefixWord, tailWord_111425, baseEnd_111425] using wordTrace_append hprefix tailTrace_111425
  have hstable : (prefixWord ++ tailWord_111425).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111425).length < 2 ^ (prefixWord ++ tailWord_111425).sum := by decide
  have hdescent : baseEnd_111425 < baseStart_111425 := by decide
  rcases family_descends (prefixWord ++ tailWord_111425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan19Incremental
