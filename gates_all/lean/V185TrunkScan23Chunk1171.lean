import V185TrunkScan23Chunk1170

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6937328 : List Nat := [2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 5]
def baseStart_6937328 : Nat := 118140960795 + 6937328 * 2 ^ 59
def prefixEnd_6937328 : Nat := 4983230072969 + 3 ^ 40 * 6937328 * 2
def baseEnd_6937328 : Nat := 3562183721894138905995815

theorem tailTrace_6937328 : CollatzResearch.WordTrace tailWord_6937328 prefixEnd_6937328 3562183721894138905995815 := by
  unfold tailWord_6937328
  simp only [CollatzResearch.WordTrace]
  refine ⟨126512569505626466070330319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168683426007501954760440425 126512569505626466070330319)
  ·
    refine ⟨189768854258439699105495479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126512569505626466070330319 189768854258439699105495479)
    ·
      refine ⟨284653281387659548658243219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189768854258439699105495479 284653281387659548658243219)
      ·
        refine ⟨426979922081489322987364829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284653281387659548658243219 426979922081489322987364829)
        ·
          refine ⟨160117470780558496120261811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 426979922081489322987364829 160117470780558496120261811)
          ·
            refine ⟨240176206170837744180392717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160117470780558496120261811 240176206170837744180392717)
            ·
              refine ⟨90066077314064154067647269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 240176206170837744180392717 90066077314064154067647269)
              ·
                refine ⟨16887389496387028887683863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90066077314064154067647269 16887389496387028887683863)
                ·
                  refine ⟨25331084244580543331525795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16887389496387028887683863 25331084244580543331525795)
                  ·
                    refine ⟨37996626366870814997288693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25331084244580543331525795 37996626366870814997288693)
                    ·
                      refine ⟨3562183721894138905995815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37996626366870814997288693 3562183721894138905995815)
                      ·
                        rfl

theorem cell23_6937328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 5].length) (baseStart_6937328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6937328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6937328 prefixEnd_6937328 := by exact prefixLift 6937328
  have htrace : WordTrace (prefixWord ++ tailWord_6937328) baseStart_6937328 baseEnd_6937328 := by
    simpa [prefixWord, tailWord_6937328, baseEnd_6937328] using wordTrace_append hprefix tailTrace_6937328
  have hstable : (prefixWord ++ tailWord_6937328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6937328).length < 2 ^ (prefixWord ++ tailWord_6937328).sum := by decide
  have hdescent : baseEnd_6937328 < baseStart_6937328 := by decide
  rcases family_descends (prefixWord ++ tailWord_6937328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6937338 : List Nat := [3, 1, 1, 1, 1, 3, 4, 1, 1, 1, 6]
def baseStart_6937338 : Nat := 118140960795 + 6937338 * 2 ^ 59
def prefixEnd_6937338 : Nat := 4983230072969 + 3 ^ 40 * 6937338 * 2
def baseEnd_6937338 : Nat := 3562188856700683866870769

theorem tailTrace_6937338 : CollatzResearch.WordTrace tailWord_6937338 prefixEnd_6937338 3562188856700683866870769 := by
  unfold tailWord_6937338
  simp only [CollatzResearch.WordTrace]
  refine ⟨63256375935304175962131167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168683669160811135899016445 63256375935304175962131167)
  ·
    refine ⟨94884563902956263943196751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63256375935304175962131167 94884563902956263943196751)
    ·
      refine ⟨142326845854434395914795127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94884563902956263943196751 142326845854434395914795127)
      ·
        refine ⟨213490268781651593872192691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142326845854434395914795127 213490268781651593872192691)
        ·
          refine ⟨320235403172477390808289037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213490268781651593872192691 320235403172477390808289037)
          ·
            refine ⟨120088276189679021553108389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 320235403172477390808289037 120088276189679021553108389)
            ·
              refine ⟨22516551785564816541207823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 120088276189679021553108389 22516551785564816541207823)
              ·
                refine ⟨33774827678347224811811735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22516551785564816541207823 33774827678347224811811735)
                ·
                  refine ⟨50662241517520837217717603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33774827678347224811811735 50662241517520837217717603)
                  ·
                    refine ⟨75993362276281255826576405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50662241517520837217717603 75993362276281255826576405)
                    ·
                      refine ⟨3562188856700683866870769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75993362276281255826576405 3562188856700683866870769)
                      ·
                        rfl

theorem cell23_6937338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 1, 1, 1, 6].length) (baseStart_6937338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6937338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6937338 prefixEnd_6937338 := by exact prefixLift 6937338
  have htrace : WordTrace (prefixWord ++ tailWord_6937338) baseStart_6937338 baseEnd_6937338 := by
    simpa [prefixWord, tailWord_6937338, baseEnd_6937338] using wordTrace_append hprefix tailTrace_6937338
  have hstable : (prefixWord ++ tailWord_6937338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6937338).length < 2 ^ (prefixWord ++ tailWord_6937338).sum := by decide
  have hdescent : baseEnd_6937338 < baseStart_6937338 := by decide
  rcases family_descends (prefixWord ++ tailWord_6937338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6937342 : List Nat := [4, 2, 2, 1, 2, 2, 1, 1, 3, 1, 4]
def baseStart_6937342 : Nat := 118140960795 + 6937342 * 2 ^ 59
def prefixEnd_6937342 : Nat := 4983230072969 + 3 ^ 40 * 6937342 * 2
def baseEnd_6937342 : Nat := 3562190910623301851220751

theorem tailTrace_6937342 : CollatzResearch.WordTrace tailWord_6937342 prefixEnd_6937342 3562190910623301851220751 := by
  unfold tailWord_6937342
  simp only [CollatzResearch.WordTrace]
  refine ⟨31628206204150276566458785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168683766422134808354446853 31628206204150276566458785)
  ·
    refine ⟨23721154653112707424844089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31628206204150276566458785 23721154653112707424844089)
    ·
      refine ⟨17790865989834530568633067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23721154653112707424844089 17790865989834530568633067)
      ·
        refine ⟨26686298984751795852949601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17790865989834530568633067 26686298984751795852949601)
        ·
          refine ⟨20014724238563846889712201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26686298984751795852949601 20014724238563846889712201)
          ·
            refine ⟨15011043178922885167284151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20014724238563846889712201 15011043178922885167284151)
            ·
              refine ⟨22516564768384327750926227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15011043178922885167284151 22516564768384327750926227)
              ·
                refine ⟨33774847152576491626389341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22516564768384327750926227 33774847152576491626389341)
                ·
                  refine ⟨12665567682216184359896003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33774847152576491626389341 12665567682216184359896003)
                  ·
                    refine ⟨18998351523324276539844005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12665567682216184359896003 18998351523324276539844005)
                    ·
                      refine ⟨3562190910623301851220751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18998351523324276539844005 3562190910623301851220751)
                      ·
                        rfl

theorem cell23_6937342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_6937342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6937342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6937342 prefixEnd_6937342 := by exact prefixLift 6937342
  have htrace : WordTrace (prefixWord ++ tailWord_6937342) baseStart_6937342 baseEnd_6937342 := by
    simpa [prefixWord, tailWord_6937342, baseEnd_6937342] using wordTrace_append hprefix tailTrace_6937342
  have hstable : (prefixWord ++ tailWord_6937342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6937342).length < 2 ^ (prefixWord ++ tailWord_6937342).sum := by decide
  have hdescent : baseEnd_6937342 < baseStart_6937342 := by decide
  rcases family_descends (prefixWord ++ tailWord_6937342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6937348 : List Nat := [2, 3, 2, 2, 1, 1, 1, 11]
def baseStart_6937348 : Nat := 118140960795 + 6937348 * 2 ^ 59
def prefixEnd_6937348 : Nat := 4983230072969 + 3 ^ 40 * 6937348 * 2
def baseEnd_6937348 : Nat := 131933110796564030657249

theorem tailTrace_6937348 : CollatzResearch.WordTrace tailWord_6937348 prefixEnd_6937348 131933110796564030657249 := by
  unfold tailWord_6937348
  simp only [CollatzResearch.WordTrace]
  refine ⟨126512934235590237778194349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168683912314120317037592465 126512934235590237778194349)
  ·
    refine ⟨47442350338346339166822881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126512934235590237778194349 47442350338346339166822881)
    ·
      refine ⟨35581762753759754375117161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47442350338346339166822881 35581762753759754375117161)
      ·
        refine ⟨26686322065319815781337871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35581762753759754375117161 26686322065319815781337871)
        ·
          refine ⟨40029483097979723672006807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26686322065319815781337871 40029483097979723672006807)
          ·
            refine ⟨60044224646969585508010211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40029483097979723672006807 60044224646969585508010211)
            ·
              refine ⟨90066336970454378262015317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60044224646969585508010211 90066336970454378262015317)
              ·
                refine ⟨131933110796564030657249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 90066336970454378262015317 131933110796564030657249)
                ·
                  rfl

theorem cell23_6937348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 11].length) (baseStart_6937348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6937348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6937348 prefixEnd_6937348 := by exact prefixLift 6937348
  have htrace : WordTrace (prefixWord ++ tailWord_6937348) baseStart_6937348 baseEnd_6937348 := by
    simpa [prefixWord, tailWord_6937348, baseEnd_6937348] using wordTrace_append hprefix tailTrace_6937348
  have hstable : (prefixWord ++ tailWord_6937348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6937348).length < 2 ^ (prefixWord ++ tailWord_6937348).sum := by decide
  have hdescent : baseEnd_6937348 < baseStart_6937348 := by decide
  rcases family_descends (prefixWord ++ tailWord_6937348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6937359 : List Nat := [1, 1, 2, 1, 1, 1, 6, 5, 1, 2, 2]
def baseStart_6937359 : Nat := 118140960795 + 6937359 * 2 ^ 59
def prefixEnd_6937359 : Nat := 4983230072969 + 3 ^ 40 * 6937359 * 2
def baseEnd_6937359 : Nat := 3562199639794428284708173

theorem tailTrace_6937359 : CollatzResearch.WordTrace tailWord_6937359 prefixEnd_6937359 3562199639794428284708173 := by
  unfold tailWord_6937359
  simp only [CollatzResearch.WordTrace]
  refine ⟨253026269674140624435039131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168684179782760416290026087 253026269674140624435039131)
  ·
    refine ⟨379539404511210936652558697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253026269674140624435039131 379539404511210936652558697)
    ·
      refine ⟨284654553383408202489419023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 379539404511210936652558697 284654553383408202489419023)
      ·
        refine ⟨426981830075112303734128535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284654553383408202489419023 426981830075112303734128535)
        ·
          refine ⟨640472745112668455601192803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 426981830075112303734128535 640472745112668455601192803)
          ·
            refine ⟨960709117669002683401789205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 640472745112668455601192803 960709117669002683401789205)
            ·
              refine ⟨45033239890734500784458869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 960709117669002683401789205 45033239890734500784458869)
              ·
                refine ⟨4221866239756359448543019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45033239890734500784458869 4221866239756359448543019)
                ·
                  refine ⟨6332799359634539172814529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4221866239756359448543019 6332799359634539172814529)
                  ·
                    refine ⟨4749599519725904379610897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6332799359634539172814529 4749599519725904379610897)
                    ·
                      refine ⟨3562199639794428284708173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4749599519725904379610897 3562199639794428284708173)
                      ·
                        rfl

theorem cell23_6937359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 5, 1, 2, 2].length) (baseStart_6937359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6937359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6937359 prefixEnd_6937359 := by exact prefixLift 6937359
  have htrace : WordTrace (prefixWord ++ tailWord_6937359) baseStart_6937359 baseEnd_6937359 := by
    simpa [prefixWord, tailWord_6937359, baseEnd_6937359] using wordTrace_append hprefix tailTrace_6937359
  have hstable : (prefixWord ++ tailWord_6937359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6937359).length < 2 ^ (prefixWord ++ tailWord_6937359).sum := by decide
  have hdescent : baseEnd_6937359 < baseStart_6937359 := by decide
  rcases family_descends (prefixWord ++ tailWord_6937359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6937376 : List Nat := [2, 1, 1, 5, 1, 3, 1, 4, 1, 2, 2]
def baseStart_6937376 : Nat := 118140960795 + 6937376 * 2 ^ 59
def prefixEnd_6937376 : Nat := 4983230072969 + 3 ^ 40 * 6937376 * 2
def baseEnd_6937376 : Nat := 3562208368965554718195595

theorem tailTrace_6937376 : CollatzResearch.WordTrace tailWord_6937376 prefixEnd_6937376 3562208368965554718195595 := by
  unfold tailWord_6937376
  simp only [CollatzResearch.WordTrace]
  refine ⟨126513444857539518169203991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168684593143386024225605321 126513444857539518169203991)
  ·
    refine ⟨189770167286309277253805987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126513444857539518169203991 189770167286309277253805987)
    ·
      refine ⟨284655250929463915880708981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189770167286309277253805987 284655250929463915880708981)
      ·
        refine ⟨26686429774637242113816467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 284655250929463915880708981 26686429774637242113816467)
        ·
          refine ⟨40029644661955863170724701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26686429774637242113816467 40029644661955863170724701)
          ·
            refine ⟨15011116748233448689021763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40029644661955863170724701 15011116748233448689021763)
            ·
              refine ⟨22516675122350173033532645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15011116748233448689021763 22516675122350173033532645)
              ·
                refine ⟨4221876585440657443787371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22516675122350173033532645 4221876585440657443787371)
                ·
                  refine ⟨6332814878160986165681057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4221876585440657443787371 6332814878160986165681057)
                  ·
                    refine ⟨4749611158620739624260793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6332814878160986165681057 4749611158620739624260793)
                    ·
                      refine ⟨3562208368965554718195595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4749611158620739624260793 3562208368965554718195595)
                      ·
                        rfl

theorem cell23_6937376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 4, 1, 2, 2].length) (baseStart_6937376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6937376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6937376 prefixEnd_6937376 := by exact prefixLift 6937376
  have htrace : WordTrace (prefixWord ++ tailWord_6937376) baseStart_6937376 baseEnd_6937376 := by
    simpa [prefixWord, tailWord_6937376, baseEnd_6937376] using wordTrace_append hprefix tailTrace_6937376
  have hstable : (prefixWord ++ tailWord_6937376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6937376).length < 2 ^ (prefixWord ++ tailWord_6937376).sum := by decide
  have hdescent : baseEnd_6937376 < baseStart_6937376 := by decide
  rcases family_descends (prefixWord ++ tailWord_6937376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6937445 : List Nat := [1, 3, 1, 3, 1, 1, 4, 1, 2, 2, 4]
def baseStart_6937445 : Nat := 118140960795 + 6937445 * 2 ^ 59
def prefixEnd_6937445 : Nat := 4983230072969 + 3 ^ 40 * 6937445 * 2
def baseEnd_6937445 : Nat := 3562243799130714948232777

theorem tailTrace_6937445 : CollatzResearch.WordTrace tailWord_6937445 prefixEnd_6937445 3562243799130714948232777 := by
  unfold tailWord_6937445
  simp only [CollatzResearch.WordTrace]
  refine ⟨253029406351829061122669789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168686270901219374081779859 253029406351829061122669789)
  ·
    refine ⟨94886027381935897921001171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 253029406351829061122669789 94886027381935897921001171)
    ·
      refine ⟨142329041072903846881501757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94886027381935897921001171 142329041072903846881501757)
      ·
        refine ⟨53373390402338942580563159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142329041072903846881501757 53373390402338942580563159)
        ·
          refine ⟨80060085603508413870844739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53373390402338942580563159 80060085603508413870844739)
          ·
            refine ⟨120090128405262620806267109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80060085603508413870844739 120090128405262620806267109)
            ·
              refine ⟨22516899075986741401175083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 120090128405262620806267109 22516899075986741401175083)
              ·
                refine ⟨33775348613980112101762625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22516899075986741401175083 33775348613980112101762625)
                ·
                  refine ⟨25331511460485084076321969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33775348613980112101762625 25331511460485084076321969)
                  ·
                    refine ⟨18998633595363813057241477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25331511460485084076321969 18998633595363813057241477)
                    ·
                      refine ⟨3562243799130714948232777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18998633595363813057241477 3562243799130714948232777)
                      ·
                        rfl

theorem cell23_6937445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 1, 2, 2, 4].length) (baseStart_6937445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6937445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6937445 prefixEnd_6937445 := by exact prefixLift 6937445
  have htrace : WordTrace (prefixWord ++ tailWord_6937445) baseStart_6937445 baseEnd_6937445 := by
    simpa [prefixWord, tailWord_6937445, baseEnd_6937445] using wordTrace_append hprefix tailTrace_6937445
  have hstable : (prefixWord ++ tailWord_6937445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6937445).length < 2 ^ (prefixWord ++ tailWord_6937445).sum := by decide
  have hdescent : baseEnd_6937445 < baseStart_6937445 := by decide
  rcases family_descends (prefixWord ++ tailWord_6937445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6937495 : List Nat := [1, 1, 3, 3, 1, 2, 3, 1, 1, 2, 5]
def baseStart_6937495 : Nat := 118140960795 + 6937495 * 2 ^ 59
def prefixEnd_6937495 : Nat := 4983230072969 + 3 ^ 40 * 6937495 * 2
def baseEnd_6937495 : Nat := 3562269473163439752607547

theorem tailTrace_6937495 : CollatzResearch.WordTrace tailWord_6937495 prefixEnd_6937495 3562269473163439752607547 := by
  unfold tailWord_6937495
  simp only [CollatzResearch.WordTrace]
  refine ⟨253031230001647919661989939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168687486667765279774659959 253031230001647919661989939)
  ·
    refine ⟨379546845002471879492984909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253031230001647919661989939 379546845002471879492984909)
    ·
      refine ⟨142330066875926954809869341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 379546845002471879492984909 142330066875926954809869341)
      ·
        refine ⟨53373775078472608053701003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142330066875926954809869341 53373775078472608053701003)
        ·
          refine ⟨80060662617708912080551505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53373775078472608053701003 80060662617708912080551505)
          ·
            refine ⟨60045496963281684060413629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80060662617708912080551505 60045496963281684060413629)
            ·
              refine ⟨22517061361230631522655111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60045496963281684060413629 22517061361230631522655111)
              ·
                refine ⟨33775592041845947283982667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22517061361230631522655111 33775592041845947283982667)
                ·
                  refine ⟨50663388062768920925974001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33775592041845947283982667 50663388062768920925974001)
                  ·
                    refine ⟨37997541047076690694480501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50663388062768920925974001 37997541047076690694480501)
                    ·
                      refine ⟨3562269473163439752607547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37997541047076690694480501 3562269473163439752607547)
                      ·
                        rfl

theorem cell23_6937495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 1, 1, 2, 5].length) (baseStart_6937495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6937495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6937495 prefixEnd_6937495 := by exact prefixLift 6937495
  have htrace : WordTrace (prefixWord ++ tailWord_6937495) baseStart_6937495 baseEnd_6937495 := by
    simpa [prefixWord, tailWord_6937495, baseEnd_6937495] using wordTrace_append hprefix tailTrace_6937495
  have hstable : (prefixWord ++ tailWord_6937495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6937495).length < 2 ^ (prefixWord ++ tailWord_6937495).sum := by decide
  have hdescent : baseEnd_6937495 < baseStart_6937495 := by decide
  rcases family_descends (prefixWord ++ tailWord_6937495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6937500 : List Nat := [2, 2, 3, 3, 2, 2, 2, 1, 2, 2, 2]
def baseStart_6937500 : Nat := 118140960795 + 6937500 * 2 ^ 59
def prefixEnd_6937500 : Nat := 4983230072969 + 3 ^ 40 * 6937500 * 2
def baseEnd_6937500 : Nat := 3562272040566712233045025

theorem tailTrace_6937500 : CollatzResearch.WordTrace tailWord_6937500 prefixEnd_6937500 3562272040566712233045025 := by
  unfold tailWord_6937500
  simp only [CollatzResearch.WordTrace]
  refine ⟨126515706183314902757960977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168687608244419870343947969 126515706183314902757960977)
  ·
    refine ⟨94886779637486177068470733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126515706183314902757960977 94886779637486177068470733)
    ·
      refine ⟨35582542364057316400676525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94886779637486177068470733 35582542364057316400676525)
      ·
        refine ⟨13343453386521493650253697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35582542364057316400676525 13343453386521493650253697)
        ·
          refine ⟨10007590039891120237690273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13343453386521493650253697 10007590039891120237690273)
          ·
            refine ⟨7505692529918340178267705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10007590039891120237690273 7505692529918340178267705)
            ·
              refine ⟨5629269397438755133700779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7505692529918340178267705 5629269397438755133700779)
              ·
                refine ⟨8443904096158132700551169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5629269397438755133700779 8443904096158132700551169)
                ·
                  refine ⟨6332928072118599525413377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8443904096158132700551169 6332928072118599525413377)
                  ·
                    refine ⟨4749696054088949644060033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6332928072118599525413377 4749696054088949644060033)
                    ·
                      refine ⟨3562272040566712233045025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4749696054088949644060033 3562272040566712233045025)
                      ·
                        rfl

theorem cell23_6937500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 2, 1, 2, 2, 2].length) (baseStart_6937500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6937500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6937500 prefixEnd_6937500 := by exact prefixLift 6937500
  have htrace : WordTrace (prefixWord ++ tailWord_6937500) baseStart_6937500 baseEnd_6937500 := by
    simpa [prefixWord, tailWord_6937500, baseEnd_6937500] using wordTrace_append hprefix tailTrace_6937500
  have hstable : (prefixWord ++ tailWord_6937500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6937500).length < 2 ^ (prefixWord ++ tailWord_6937500).sum := by decide
  have hdescent : baseEnd_6937500 < baseStart_6937500 := by decide
  rcases family_descends (prefixWord ++ tailWord_6937500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6937522 : List Nat := [3, 2, 1, 1, 1, 1, 1, 1, 6, 4, 2]
def baseStart_6937522 : Nat := 118140960795 + 6937522 * 2 ^ 59
def prefixEnd_6937522 : Nat := 4983230072969 + 3 ^ 40 * 6937522 * 2
def baseEnd_6937522 : Nat := 3562283337141111146969923

theorem tailTrace_6937522 : CollatzResearch.WordTrace tailWord_6937522 prefixEnd_6937522 3562283337141111146969923 := by
  unfold tailWord_6937522
  simp only [CollatzResearch.WordTrace]
  refine ⟨63258053693137525818305705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168688143181700068848815213 63258053693137525818305705)
  ·
    refine ⟨47443540269853144363729279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63258053693137525818305705 47443540269853144363729279)
    ·
      refine ⟨71165310404779716545593919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47443540269853144363729279 71165310404779716545593919)
      ·
        refine ⟨106747965607169574818390879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71165310404779716545593919 106747965607169574818390879)
        ·
          refine ⟨160121948410754362227586319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106747965607169574818390879 160121948410754362227586319)
          ·
            refine ⟨240182922616131543341379479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160121948410754362227586319 240182922616131543341379479)
            ·
              refine ⟨360274383924197315012069219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 240182922616131543341379479 360274383924197315012069219)
              ·
                refine ⟨540411575886295972518103829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 360274383924197315012069219 540411575886295972518103829)
                ·
                  refine ⟨25331792619670123711786117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 540411575886295972518103829 25331792619670123711786117)
                  ·
                    refine ⟨4749711116188148195959897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25331792619670123711786117 4749711116188148195959897)
                    ·
                      refine ⟨3562283337141111146969923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4749711116188148195959897 3562283337141111146969923)
                      ·
                        rfl

theorem cell23_6937522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 6, 4, 2].length) (baseStart_6937522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6937522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6937522 prefixEnd_6937522 := by exact prefixLift 6937522
  have htrace : WordTrace (prefixWord ++ tailWord_6937522) baseStart_6937522 baseEnd_6937522 := by
    simpa [prefixWord, tailWord_6937522, baseEnd_6937522] using wordTrace_append hprefix tailTrace_6937522
  have hstable : (prefixWord ++ tailWord_6937522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6937522).length < 2 ^ (prefixWord ++ tailWord_6937522).sum := by decide
  have hdescent : baseEnd_6937522 < baseStart_6937522 := by decide
  rcases family_descends (prefixWord ++ tailWord_6937522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6937540 : List Nat := [2, 3, 3, 3, 2, 1, 2, 2, 5]
def baseStart_6937540 : Nat := 118140960795 + 6937540 * 2 ^ 59
def prefixEnd_6937540 : Nat := 4983230072969 + 3 ^ 40 * 6937540 * 2
def baseEnd_6937540 : Nat := 395810286643654675171649

theorem tailTrace_6937540 : CollatzResearch.WordTrace tailWord_6937540 prefixEnd_6937540 395810286643654675171649 := by
  unfold tailWord_6937540
  simp only [CollatzResearch.WordTrace]
  refine ⟨126516435643242446173689037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168688580857656594898252049 126516435643242446173689037)
  ·
    refine ⟨47443663366215917315133389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126516435643242446173689037 47443663366215917315133389)
    ·
      refine ⟨17791373762330968993175021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47443663366215917315133389 17791373762330968993175021)
      ·
        refine ⟨6671765160874113372440633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17791373762330968993175021 6671765160874113372440633)
        ·
          refine ⟨5003823870655585029330475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6671765160874113372440633 5003823870655585029330475)
          ·
            refine ⟨7505735805983377543995713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5003823870655585029330475 7505735805983377543995713)
            ·
              refine ⟨5629301854487533157996785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7505735805983377543995713 5629301854487533157996785)
              ·
                refine ⟨4221976390865649868497589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5629301854487533157996785 4221976390865649868497589)
                ·
                  refine ⟨395810286643654675171649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4221976390865649868497589 395810286643654675171649)
                  ·
                    rfl

theorem cell23_6937540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 2, 2, 5].length) (baseStart_6937540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6937540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6937540 prefixEnd_6937540 := by exact prefixLift 6937540
  have htrace : WordTrace (prefixWord ++ tailWord_6937540) baseStart_6937540 baseEnd_6937540 := by
    simpa [prefixWord, tailWord_6937540, baseEnd_6937540] using wordTrace_append hprefix tailTrace_6937540
  have hstable : (prefixWord ++ tailWord_6937540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6937540).length < 2 ^ (prefixWord ++ tailWord_6937540).sum := by decide
  have hdescent : baseEnd_6937540 < baseStart_6937540 := by decide
  rcases family_descends (prefixWord ++ tailWord_6937540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6937562 : List Nat := [3, 1, 1, 2, 4, 1, 2, 3, 6]
def baseStart_6937562 : Nat := 118140960795 + 6937562 * 2 ^ 59
def prefixEnd_6937562 : Nat := 4983230072969 + 3 ^ 40 * 6937562 * 2
def baseEnd_6937562 : Nat := 395811541818587887829971

theorem tailTrace_6937562 : CollatzResearch.WordTrace tailWord_6937562 prefixEnd_6937562 395811541818587887829971 := by
  unfold tailWord_6937562
  simp only [CollatzResearch.WordTrace]
  refine ⟨63258418423101297526169735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168689115794936793403119293 63258418423101297526169735)
  ·
    refine ⟨94887627634651946289254603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63258418423101297526169735 94887627634651946289254603)
    ·
      refine ⟨142331441451977919433881905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94887627634651946289254603 142331441451977919433881905)
      ·
        refine ⟨106748581088983439575411429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142331441451977919433881905 106748581088983439575411429)
        ·
          refine ⟨20015358954184394920389643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 106748581088983439575411429 20015358954184394920389643)
          ·
            refine ⟨30023038431276592380584465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20015358954184394920389643 30023038431276592380584465)
            ·
              refine ⟨22517278823457444285438349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30023038431276592380584465 22517278823457444285438349)
              ·
                refine ⟨8443979558796541607039381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22517278823457444285438349 8443979558796541607039381)
                ·
                  refine ⟨395811541818587887829971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8443979558796541607039381 395811541818587887829971)
                  ·
                    rfl

theorem cell23_6937562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 3, 6].length) (baseStart_6937562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6937562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6937562 prefixEnd_6937562 := by exact prefixLift 6937562
  have htrace : WordTrace (prefixWord ++ tailWord_6937562) baseStart_6937562 baseEnd_6937562 := by
    simpa [prefixWord, tailWord_6937562, baseEnd_6937562] using wordTrace_append hprefix tailTrace_6937562
  have hstable : (prefixWord ++ tailWord_6937562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6937562).length < 2 ^ (prefixWord ++ tailWord_6937562).sum := by decide
  have hdescent : baseEnd_6937562 < baseStart_6937562 := by decide
  rcases family_descends (prefixWord ++ tailWord_6937562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6937573 : List Nat := [1, 3, 1, 6, 2, 1, 1, 1, 2, 1, 4]
def baseStart_6937573 : Nat := 118140960795 + 6937573 * 2 ^ 59
def prefixEnd_6937573 : Nat := 4983230072969 + 3 ^ 40 * 6937573 * 2
def baseEnd_6937573 : Nat := 3562309524654490447432189

theorem tailTrace_6937573 : CollatzResearch.WordTrace tailWord_6937573 prefixEnd_6937573 3562309524654490447432189 := by
  unfold tailWord_6937573
  simp only [CollatzResearch.WordTrace]
  refine ⟨253034074895365338983329373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168689383263576892655552915 253034074895365338983329373)
  ·
    refine ⟨94887778085762002118748515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 253034074895365338983329373 94887778085762002118748515)
    ·
      refine ⟨142331667128643003178122773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94887778085762002118748515 142331667128643003178122773)
      ·
        refine ⟨6671796896655140773974505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 142331667128643003178122773 6671796896655140773974505)
        ·
          refine ⟨5003847672491355580480879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6671796896655140773974505 5003847672491355580480879)
          ·
            refine ⟨7505771508737033370721319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5003847672491355580480879 7505771508737033370721319)
            ·
              refine ⟨11258657263105550056081979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7505771508737033370721319 11258657263105550056081979)
              ·
                refine ⟨16887985894658325084122969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11258657263105550056081979 16887985894658325084122969)
                ·
                  refine ⟨12665989420993743813092227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16887985894658325084122969 12665989420993743813092227)
                  ·
                    refine ⟨18998984131490615719638341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12665989420993743813092227 18998984131490615719638341)
                    ·
                      refine ⟨3562309524654490447432189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18998984131490615719638341 3562309524654490447432189)
                      ·
                        rfl

theorem cell23_6937573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_6937573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6937573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6937573 prefixEnd_6937573 := by exact prefixLift 6937573
  have htrace : WordTrace (prefixWord ++ tailWord_6937573) baseStart_6937573 baseEnd_6937573 := by
    simpa [prefixWord, tailWord_6937573, baseEnd_6937573] using wordTrace_append hprefix tailTrace_6937573
  have hstable : (prefixWord ++ tailWord_6937573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6937573).length < 2 ^ (prefixWord ++ tailWord_6937573).sum := by decide
  have hdescent : baseEnd_6937573 < baseStart_6937573 := by decide
  rcases family_descends (prefixWord ++ tailWord_6937573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6937649 : List Nat := [1, 2, 2, 3, 1, 2, 1, 5, 1, 2, 3]
def baseStart_6937649 : Nat := 118140960795 + 6937649 * 2 ^ 59
def prefixEnd_6937649 : Nat := 4983230072969 + 3 ^ 40 * 6937649 * 2
def baseEnd_6937649 : Nat := 3562348549184232150081839

theorem tailTrace_6937649 : CollatzResearch.WordTrace tailWord_6937649 prefixEnd_6937649 3562348549184232150081839 := by
  unfold tailWord_6937649
  simp only [CollatzResearch.WordTrace]
  refine ⟨253036846843090003963096001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168691231228726669308730667 253036846843090003963096001)
  ·
    refine ⟨189777635132317502972322001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253036846843090003963096001 189777635132317502972322001)
    ·
      refine ⟨142333226349238127229241501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189777635132317502972322001 142333226349238127229241501)
      ·
        refine ⟨53374959880964297710965563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142333226349238127229241501 53374959880964297710965563)
        ·
          refine ⟨80062439821446446566448345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53374959880964297710965563 80062439821446446566448345)
          ·
            refine ⟨60046829866084834924836259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80062439821446446566448345 60046829866084834924836259)
            ·
              refine ⟨90070244799127252387254389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60046829866084834924836259 90070244799127252387254389)
              ·
                refine ⟨8444085449918179911305099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 90070244799127252387254389 8444085449918179911305099)
                ·
                  refine ⟨12666128174877269866957649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8444085449918179911305099 12666128174877269866957649)
                  ·
                    refine ⟨9499596131157952400218237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12666128174877269866957649 9499596131157952400218237)
                    ·
                      refine ⟨3562348549184232150081839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9499596131157952400218237 3562348549184232150081839)
                      ·
                        rfl

theorem cell23_6937649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 5, 1, 2, 3].length) (baseStart_6937649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6937649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6937649 prefixEnd_6937649 := by exact prefixLift 6937649
  have htrace : WordTrace (prefixWord ++ tailWord_6937649) baseStart_6937649 baseEnd_6937649 := by
    simpa [prefixWord, tailWord_6937649, baseEnd_6937649] using wordTrace_append hprefix tailTrace_6937649
  have hstable : (prefixWord ++ tailWord_6937649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6937649).length < 2 ^ (prefixWord ++ tailWord_6937649).sum := by decide
  have hdescent : baseEnd_6937649 < baseStart_6937649 := by decide
  rcases family_descends (prefixWord ++ tailWord_6937649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6937712 : List Nat := [2, 1, 1, 1, 5, 1, 2, 2, 2, 6]
def baseStart_6937712 : Nat := 118140960795 + 6937712 * 2 ^ 59
def prefixEnd_6937712 : Nat := 4983230072969 + 3 ^ 40 * 6937712 * 2
def baseEnd_6937712 : Nat := 1187460299488488467864683

theorem tailTrace_6937712 : CollatzResearch.WordTrace tailWord_6937712 prefixEnd_6937712 1187460299488488467864683 := by
  unfold tailWord_6937712
  simp only [CollatzResearch.WordTrace]
  refine ⟨126519572320930882861319695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168692763094574510481759593 126519572320930882861319695)
  ·
    refine ⟨189779358481396324291979543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126519572320930882861319695 189779358481396324291979543)
    ·
      refine ⟨284669037722094486437969315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189779358481396324291979543 284669037722094486437969315)
      ·
        refine ⟨427003556583141729656953973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284669037722094486437969315 427003556583141729656953973)
        ·
          refine ⟨40031583429669537155339435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 427003556583141729656953973 40031583429669537155339435)
          ·
            refine ⟨60047375144504305733009153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40031583429669537155339435 60047375144504305733009153)
            ·
              refine ⟨45035531358378229299756865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60047375144504305733009153 45035531358378229299756865)
              ·
                refine ⟨33776648518783671974817649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45035531358378229299756865 33776648518783671974817649)
                ·
                  refine ⟨25332486389087753981113237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33776648518783671974817649 25332486389087753981113237)
                  ·
                    refine ⟨1187460299488488467864683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25332486389087753981113237 1187460299488488467864683)
                    ·
                      rfl

theorem cell23_6937712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 2, 2, 6].length) (baseStart_6937712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6937712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6937712 prefixEnd_6937712 := by exact prefixLift 6937712
  have htrace : WordTrace (prefixWord ++ tailWord_6937712) baseStart_6937712 baseEnd_6937712 := by
    simpa [prefixWord, tailWord_6937712, baseEnd_6937712] using wordTrace_append hprefix tailTrace_6937712
  have hstable : (prefixWord ++ tailWord_6937712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6937712).length < 2 ^ (prefixWord ++ tailWord_6937712).sum := by decide
  have hdescent : baseEnd_6937712 < baseStart_6937712 := by decide
  rcases family_descends (prefixWord ++ tailWord_6937712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6937719 : List Nat := [1, 1, 3, 1, 1, 4, 1, 2, 3, 4, 2]
def baseStart_6937719 : Nat := 118140960795 + 6937719 * 2 ^ 59
def prefixEnd_6937719 : Nat := 4983230072969 + 3 ^ 40 * 6937719 * 2
def baseEnd_6937719 : Nat := 3562384492830046876206517

theorem tailTrace_6937719 : CollatzResearch.WordTrace tailWord_6937719 prefixEnd_6937719 3562384492830046876206517 := by
  unfold tailWord_6937719
  simp only [CollatzResearch.WordTrace]
  refine ⟨253039399952836405918144211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168692933301890937278762807 253039399952836405918144211)
  ·
    refine ⟨379559099929254608877216317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253039399952836405918144211 379559099929254608877216317)
    ·
      refine ⟨142334662473470478328956119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 379559099929254608877216317 142334662473470478328956119)
      ·
        refine ⟨213501993710205717493434179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142334662473470478328956119 213501993710205717493434179)
        ·
          refine ⟨320252990565308576240151269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213501993710205717493434179 320252990565308576240151269)
          ·
            refine ⟨60047435730995358045028363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 320252990565308576240151269 60047435730995358045028363)
            ·
              refine ⟨90071153596493037067542545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60047435730995358045028363 90071153596493037067542545)
              ·
                refine ⟨67553365197369777800656909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90071153596493037067542545 67553365197369777800656909)
                ·
                  refine ⟨25332511949013666675246341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67553365197369777800656909 25332511949013666675246341)
                  ·
                    refine ⟨4749845990440062501608689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25332511949013666675246341 4749845990440062501608689)
                    ·
                      refine ⟨3562384492830046876206517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4749845990440062501608689 3562384492830046876206517)
                      ·
                        rfl

theorem cell23_6937719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 2, 3, 4, 2].length) (baseStart_6937719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6937719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6937719 prefixEnd_6937719 := by exact prefixLift 6937719
  have htrace : WordTrace (prefixWord ++ tailWord_6937719) baseStart_6937719 baseEnd_6937719 := by
    simpa [prefixWord, tailWord_6937719, baseEnd_6937719] using wordTrace_append hprefix tailTrace_6937719
  have hstable : (prefixWord ++ tailWord_6937719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6937719).length < 2 ^ (prefixWord ++ tailWord_6937719).sum := by decide
  have hdescent : baseEnd_6937719 < baseStart_6937719 := by decide
  rcases family_descends (prefixWord ++ tailWord_6937719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6937729 : List Nat := [1, 2, 4, 2, 2, 2, 1, 1, 2, 6]
def baseStart_6937729 : Nat := 118140960795 + 6937729 * 2 ^ 59
def prefixEnd_6937729 : Nat := 4983230072969 + 3 ^ 40 * 6937729 * 2
def baseEnd_6937729 : Nat := 1187463209212197279027157

theorem tailTrace_6937729 : CollatzResearch.WordTrace tailWord_6937729 prefixEnd_6937729 1187463209212197279027157 := by
  unfold tailWord_6937729
  simp only [CollatzResearch.WordTrace]
  refine ⟨253039764682800177626008241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168693176455200118417338827 253039764682800177626008241)
  ·
    refine ⟨189779823512100133219506181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253039764682800177626008241 189779823512100133219506181)
    ·
      refine ⟨35583716908518774978657409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 189779823512100133219506181 35583716908518774978657409)
      ·
        refine ⟨26687787681389081233993057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35583716908518774978657409 26687787681389081233993057)
        ·
          refine ⟨20015840761041810925494793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26687787681389081233993057 20015840761041810925494793)
          ·
            refine ⟨15011880570781358194121095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20015840761041810925494793 15011880570781358194121095)
            ·
              refine ⟨22517820856172037291181643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15011880570781358194121095 22517820856172037291181643)
              ·
                refine ⟨33776731284258055936772465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22517820856172037291181643 33776731284258055936772465)
                ·
                  refine ⟨25332548463193541952579349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33776731284258055936772465 25332548463193541952579349)
                  ·
                    refine ⟨1187463209212197279027157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25332548463193541952579349 1187463209212197279027157)
                    ·
                      rfl

theorem cell23_6937729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 1, 2, 6].length) (baseStart_6937729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6937729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6937729 prefixEnd_6937729 := by exact prefixLift 6937729
  have htrace : WordTrace (prefixWord ++ tailWord_6937729) baseStart_6937729 baseEnd_6937729 := by
    simpa [prefixWord, tailWord_6937729, baseEnd_6937729] using wordTrace_append hprefix tailTrace_6937729
  have hstable : (prefixWord ++ tailWord_6937729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6937729).length < 2 ^ (prefixWord ++ tailWord_6937729).sum := by decide
  have hdescent : baseEnd_6937729 < baseStart_6937729 := by decide
  rcases family_descends (prefixWord ++ tailWord_6937729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6937770 : List Nat := [3, 1, 5, 1, 1, 2, 1, 1, 4, 2, 2]
def baseStart_6937770 : Nat := 118140960795 + 6937770 * 2 ^ 59
def prefixEnd_6937770 : Nat := 4983230072969 + 3 ^ 40 * 6937770 * 2
def baseEnd_6937770 : Nat := 3562410680343426176668783

theorem tailTrace_6937770 : CollatzResearch.WordTrace tailWord_6937770 prefixEnd_6937770 3562410680343426176668783 := by
  unfold tailWord_6937770
  simp only [CollatzResearch.WordTrace]
  refine ⟨63260315018912910407062691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168694173383767761085500509 63260315018912910407062691)
  ·
    refine ⟨94890472528369365610594037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63260315018912910407062691 94890472528369365610594037)
    ·
      refine ⟨8895981799534628025993191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 94890472528369365610594037 8895981799534628025993191)
      ·
        refine ⟨13343972699301942038989787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8895981799534628025993191 13343972699301942038989787)
        ·
          refine ⟨20015959048952913058484681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13343972699301942038989787 20015959048952913058484681)
          ·
            refine ⟨15011969286714684793863511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20015959048952913058484681 15011969286714684793863511)
            ·
              refine ⟨22517953930072027190795267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15011969286714684793863511 22517953930072027190795267)
              ·
                refine ⟨33776930895108040786192901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22517953930072027190795267 33776930895108040786192901)
                ·
                  refine ⟨6333174542832757647411169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33776930895108040786192901 6333174542832757647411169)
                  ·
                    refine ⟨4749880907124568235558377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6333174542832757647411169 4749880907124568235558377)
                    ·
                      refine ⟨3562410680343426176668783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4749880907124568235558377 3562410680343426176668783)
                      ·
                        rfl

theorem cell23_6937770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 1, 4, 2, 2].length) (baseStart_6937770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6937770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6937770 prefixEnd_6937770 := by exact prefixLift 6937770
  have htrace : WordTrace (prefixWord ++ tailWord_6937770) baseStart_6937770 baseEnd_6937770 := by
    simpa [prefixWord, tailWord_6937770, baseEnd_6937770] using wordTrace_append hprefix tailTrace_6937770
  have hstable : (prefixWord ++ tailWord_6937770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6937770).length < 2 ^ (prefixWord ++ tailWord_6937770).sum := by decide
  have hdescent : baseEnd_6937770 < baseStart_6937770 := by decide
  rcases family_descends (prefixWord ++ tailWord_6937770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6937779 : List Nat := [1, 1, 1, 2, 3, 2, 2, 1, 1, 7, 2]
def baseStart_6937779 : Nat := 118140960795 + 6937779 * 2 ^ 59
def prefixEnd_6937779 : Nat := 4983230072969 + 3 ^ 40 * 6937779 * 2
def baseEnd_6937779 : Nat := 3562415301669316641456241

theorem tailTrace_6937779 : CollatzResearch.WordTrace tailWord_6937779 prefixEnd_6937779 3562415301669316641456241 := by
  unfold tailWord_6937779
  simp only [CollatzResearch.WordTrace]
  refine ⟨253041588332619036165328391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168694392221746024110218927 253041588332619036165328391)
  ·
    refine ⟨379562382498928554247992587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253041588332619036165328391 379562382498928554247992587)
    ·
      refine ⟨569343573748392831371988881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379562382498928554247992587 569343573748392831371988881)
      ·
        refine ⟨427007680311294623528991661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 569343573748392831371988881 427007680311294623528991661)
        ·
          refine ⟨160127880116735483823371873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 427007680311294623528991661 160127880116735483823371873)
          ·
            refine ⟨120095910087551612867528905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160127880116735483823371873 120095910087551612867528905)
            ·
              refine ⟨90071932565663709650646679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120095910087551612867528905 90071932565663709650646679)
              ·
                refine ⟨135107898848495564475970019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90071932565663709650646679 135107898848495564475970019)
                ·
                  refine ⟨202661848272743346713955029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 135107898848495564475970019 202661848272743346713955029)
                  ·
                    refine ⟨4749887068892422188608321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 202661848272743346713955029 4749887068892422188608321)
                    ·
                      refine ⟨3562415301669316641456241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4749887068892422188608321 3562415301669316641456241)
                      ·
                        rfl

theorem cell23_6937779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 7, 2].length) (baseStart_6937779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6937779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6937779 prefixEnd_6937779 := by exact prefixLift 6937779
  have htrace : WordTrace (prefixWord ++ tailWord_6937779) baseStart_6937779 baseEnd_6937779 := by
    simpa [prefixWord, tailWord_6937779, baseEnd_6937779] using wordTrace_append hprefix tailTrace_6937779
  have hstable : (prefixWord ++ tailWord_6937779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6937779).length < 2 ^ (prefixWord ++ tailWord_6937779).sum := by decide
  have hdescent : baseEnd_6937779 < baseStart_6937779 := by decide
  rcases family_descends (prefixWord ++ tailWord_6937779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6937809 : List Nat := [1, 2, 2, 1, 2, 2, 1, 5, 2, 1, 4]
def baseStart_6937809 : Nat := 118140960795 + 6937809 * 2 ^ 59
def prefixEnd_6937809 : Nat := 4983230072969 + 3 ^ 40 * 6937809 * 2
def baseEnd_6937809 : Nat := 3562430706088951524081103

theorem tailTrace_6937809 : CollatzResearch.WordTrace tailWord_6937809 prefixEnd_6937809 3562430706088951524081103 := by
  unfold tailWord_6937809
  simp only [CollatzResearch.WordTrace]
  refine ⟨253042682522510351288920481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168695121681673567525946987 253042682522510351288920481)
  ·
    refine ⟨189782011891882763466690361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253042682522510351288920481 189782011891882763466690361)
    ·
      refine ⟨142336508918912072600017771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189782011891882763466690361 142336508918912072600017771)
      ·
        refine ⟨213504763378368108900026657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142336508918912072600017771 213504763378368108900026657)
        ·
          refine ⟨160128572533776081675019993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213504763378368108900026657 160128572533776081675019993)
          ·
            refine ⟨120096429400332061256264995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160128572533776081675019993 120096429400332061256264995)
            ·
              refine ⟨180144644100498091884397493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120096429400332061256264995 180144644100498091884397493)
              ·
                refine ⟨16888560384421696114162265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 180144644100498091884397493 16888560384421696114162265)
                ·
                  refine ⟨12666420288316272085621699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16888560384421696114162265 12666420288316272085621699)
                  ·
                    refine ⟨18999630432474408128432549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12666420288316272085621699 18999630432474408128432549)
                    ·
                      refine ⟨3562430706088951524081103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18999630432474408128432549 3562430706088951524081103)
                      ·
                        rfl

theorem cell23_6937809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 5, 2, 1, 4].length) (baseStart_6937809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6937809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6937809 prefixEnd_6937809 := by exact prefixLift 6937809
  have htrace : WordTrace (prefixWord ++ tailWord_6937809) baseStart_6937809 baseEnd_6937809 := by
    simpa [prefixWord, tailWord_6937809, baseEnd_6937809] using wordTrace_append hprefix tailTrace_6937809
  have hstable : (prefixWord ++ tailWord_6937809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6937809).length < 2 ^ (prefixWord ++ tailWord_6937809).sum := by decide
  have hdescent : baseEnd_6937809 < baseStart_6937809 := by decide
  rcases family_descends (prefixWord ++ tailWord_6937809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6937836 : List Nat := [2, 2, 1, 1, 2, 4, 3, 1, 3, 4]
def baseStart_6937836 : Nat := 118140960795 + 6937836 * 2 ^ 59
def prefixEnd_6937836 : Nat := 4983230072969 + 3 ^ 40 * 6937836 * 2
def baseEnd_6937836 : Nat := 1187481523355540972814493

theorem tailTrace_6937836 : CollatzResearch.WordTrace tailWord_6937836 prefixEnd_6937836 1187481523355540972814493 := by
  unfold tailWord_6937836
  simp only [CollatzResearch.WordTrace]
  refine ⟨126521833646706267450076681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168695778195608356600102241 126521833646706267450076681)
  ·
    refine ⟨94891375235029700587557511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126521833646706267450076681 94891375235029700587557511)
    ·
      refine ⟨142337062852544550881336267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94891375235029700587557511 142337062852544550881336267)
      ·
        refine ⟨213505594278816826322004401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142337062852544550881336267 213505594278816826322004401)
        ·
          refine ⟨160129195709112619741503301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213505594278816826322004401 160129195709112619741503301)
          ·
            refine ⟨30024224195458616201531869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 160129195709112619741503301 30024224195458616201531869)
            ·
              refine ⟨11259084073296981075574451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30024224195458616201531869 11259084073296981075574451)
              ·
                refine ⟨16888626109945471613361677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11259084073296981075574451 16888626109945471613361677)
                ·
                  refine ⟨6333234791229551855010629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16888626109945471613361677 6333234791229551855010629)
                  ·
                    refine ⟨1187481523355540972814493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6333234791229551855010629 1187481523355540972814493)
                    ·
                      rfl

theorem cell23_6937836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 4].length) (baseStart_6937836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6937836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6937836 prefixEnd_6937836 := by exact prefixLift 6937836
  have htrace : WordTrace (prefixWord ++ tailWord_6937836) baseStart_6937836 baseEnd_6937836 := by
    simpa [prefixWord, tailWord_6937836, baseEnd_6937836] using wordTrace_append hprefix tailTrace_6937836
  have hstable : (prefixWord ++ tailWord_6937836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6937836).length < 2 ^ (prefixWord ++ tailWord_6937836).sum := by decide
  have hdescent : baseEnd_6937836 < baseStart_6937836 := by decide
  rcases family_descends (prefixWord ++ tailWord_6937836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6937846 : List Nat := [5, 1, 1, 1, 1, 1, 1, 1, 6, 2, 3]
def baseStart_6937846 : Nat := 118140960795 + 6937846 * 2 ^ 59
def prefixEnd_6937846 : Nat := 4983230072969 + 3 ^ 40 * 6937846 * 2
def baseEnd_6937846 : Nat := 3562449704873167879318433

theorem tailTrace_6937846 : CollatzResearch.WordTrace tailWord_6937846 prefixEnd_6937846 3562449704873167879318433 := by
  unfold tailWord_6937846
  simp only [CollatzResearch.WordTrace]
  refine ⟨15815252001461019163001087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 168696021348917537738678261 15815252001461019163001087)
  ·
    refine ⟨23722878002191528744501631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15815252001461019163001087 23722878002191528744501631)
    ·
      refine ⟨35584317003287293116752447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23722878002191528744501631 35584317003287293116752447)
      ·
        refine ⟨53376475504930939675128671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35584317003287293116752447 53376475504930939675128671)
        ·
          refine ⟨80064713257396409512693007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53376475504930939675128671 80064713257396409512693007)
          ·
            refine ⟨120097069886094614269039511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80064713257396409512693007 120097069886094614269039511)
            ·
              refine ⟨180145604829141921403559267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120097069886094614269039511 180145604829141921403559267)
              ·
                refine ⟨270218407243712882105338901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 180145604829141921403559267 270218407243712882105338901)
                ·
                  refine ⟨12666487839549041348687761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 270218407243712882105338901 12666487839549041348687761)
                  ·
                    refine ⟨9499865879661781011515821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12666487839549041348687761 9499865879661781011515821)
                    ·
                      refine ⟨3562449704873167879318433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9499865879661781011515821 3562449704873167879318433)
                      ·
                        rfl

theorem cell23_6937846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 6, 2, 3].length) (baseStart_6937846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6937846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6937846 prefixEnd_6937846 := by exact prefixLift 6937846
  have htrace : WordTrace (prefixWord ++ tailWord_6937846) baseStart_6937846 baseEnd_6937846 := by
    simpa [prefixWord, tailWord_6937846, baseEnd_6937846] using wordTrace_append hprefix tailTrace_6937846
  have hstable : (prefixWord ++ tailWord_6937846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6937846).length < 2 ^ (prefixWord ++ tailWord_6937846).sum := by decide
  have hdescent : baseEnd_6937846 < baseStart_6937846 := by decide
  rcases family_descends (prefixWord ++ tailWord_6937846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6937849 : List Nat := [1, 2, 1, 3, 1, 1, 5, 3, 6]
def baseStart_6937849 : Nat := 118140960795 + 6937849 * 2 ^ 59
def prefixEnd_6937849 : Nat := 4983230072969 + 3 ^ 40 * 6937849 * 2
def baseEnd_6937849 : Nat := 395827916146125707508991

theorem tailTrace_6937849 : CollatzResearch.WordTrace tailWord_6937849 prefixEnd_6937849 395827916146125707508991 := by
  unfold tailWord_6937849
  simp only [CollatzResearch.WordTrace]
  refine ⟨253044141442365438120376601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168696094294910292080251067 253044141442365438120376601)
  ·
    refine ⟨189783106081774078590282451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253044141442365438120376601 189783106081774078590282451)
    ·
      refine ⟨284674659122661117885423677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189783106081774078590282451 284674659122661117885423677)
      ·
        refine ⟨106752997170997919207033879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 284674659122661117885423677 106752997170997919207033879)
        ·
          refine ⟨160129495756496878810550819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106752997170997919207033879 160129495756496878810550819)
          ·
            refine ⟨240194243634745318215826229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160129495756496878810550819 240194243634745318215826229)
            ·
              refine ⟨22518210340757373582733709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 240194243634745318215826229 22518210340757373582733709)
              ·
                refine ⟨8444328877784015093525141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22518210340757373582733709 8444328877784015093525141)
                ·
                  refine ⟨395827916146125707508991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8444328877784015093525141 395827916146125707508991)
                  ·
                    rfl

theorem cell23_6937849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 3, 6].length) (baseStart_6937849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6937849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6937849 prefixEnd_6937849 := by exact prefixLift 6937849
  have htrace : WordTrace (prefixWord ++ tailWord_6937849) baseStart_6937849 baseEnd_6937849 := by
    simpa [prefixWord, tailWord_6937849, baseEnd_6937849] using wordTrace_append hprefix tailTrace_6937849
  have hstable : (prefixWord ++ tailWord_6937849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6937849).length < 2 ^ (prefixWord ++ tailWord_6937849).sum := by decide
  have hdescent : baseEnd_6937849 < baseStart_6937849 := by decide
  rcases family_descends (prefixWord ++ tailWord_6937849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6937887 : List Nat := [1, 1, 2, 4, 4, 2, 2, 2, 1, 4]
def baseStart_6937887 : Nat := 118140960795 + 6937887 * 2 ^ 59
def prefixEnd_6937887 : Nat := 4983230072969 + 3 ^ 40 * 6937887 * 2
def baseEnd_6937887 : Nat := 1187490252526667406301915

theorem tailTrace_6937887 : CollatzResearch.WordTrace tailWord_6937887 prefixEnd_6937887 1187490252526667406301915 := by
  unfold tailWord_6937887
  simp only [CollatzResearch.WordTrace]
  refine ⟨253045527416227770610259915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168697018277485180406839943 253045527416227770610259915)
  ·
    refine ⟨379568291124341655915389873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253045527416227770610259915 379568291124341655915389873)
    ·
      refine ⟨284676218343256241936542405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 379568291124341655915389873 284676218343256241936542405)
      ·
        refine ⟨53376790939360545363101701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 284676218343256241936542405 53376790939360545363101701)
        ·
          refine ⟨10008148301130102255581569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53376790939360545363101701 10008148301130102255581569)
          ·
            refine ⟨7506111225847576691686177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10008148301130102255581569 7506111225847576691686177)
            ·
              refine ⟨5629583419385682518764633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7506111225847576691686177 5629583419385682518764633)
              ·
                refine ⟨4222187564539261889073475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5629583419385682518764633 4222187564539261889073475)
                ·
                  refine ⟨6333281346808892833610213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4222187564539261889073475 6333281346808892833610213)
                  ·
                    refine ⟨1187490252526667406301915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6333281346808892833610213 1187490252526667406301915)
                    ·
                      rfl

theorem cell23_6937887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 2, 2, 1, 4].length) (baseStart_6937887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6937887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6937887 prefixEnd_6937887 := by exact prefixLift 6937887
  have htrace : WordTrace (prefixWord ++ tailWord_6937887) baseStart_6937887 baseEnd_6937887 := by
    simpa [prefixWord, tailWord_6937887, baseEnd_6937887] using wordTrace_append hprefix tailTrace_6937887
  have hstable : (prefixWord ++ tailWord_6937887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6937887).length < 2 ^ (prefixWord ++ tailWord_6937887).sum := by decide
  have hdescent : baseEnd_6937887 < baseStart_6937887 := by decide
  rcases family_descends (prefixWord ++ tailWord_6937887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6937896 : List Nat := [2, 1, 5, 1, 2, 1, 1, 2, 3, 5]
def baseStart_6937896 : Nat := 118140960795 + 6937896 * 2 ^ 59
def prefixEnd_6937896 : Nat := 4983230072969 + 3 ^ 40 * 6937896 * 2
def baseEnd_6937896 : Nat := 1187491792968630894564401

theorem tailTrace_6937896 : CollatzResearch.WordTrace tailWord_6937896 prefixEnd_6937896 1187491792968630894564401 := by
  unfold tailWord_6937896
  simp only [CollatzResearch.WordTrace]
  refine ⟨126522927836597582573668771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168697237115463443431558361 126522927836597582573668771)
  ·
    refine ⟨189784391754896373860503157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126522927836597582573668771 189784391754896373860503157)
    ·
      refine ⟨17792286727021535049422171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 189784391754896373860503157 17792286727021535049422171)
      ·
        refine ⟨26688430090532302574133257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17792286727021535049422171 26688430090532302574133257)
        ·
          refine ⟨20016322567899226930599943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26688430090532302574133257 20016322567899226930599943)
          ·
            refine ⟨30024483851848840395899915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20016322567899226930599943 30024483851848840395899915)
            ·
              refine ⟨45036725777773260593849873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30024483851848840395899915 45036725777773260593849873)
              ·
                refine ⟨33777544333329945445387405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45036725777773260593849873 33777544333329945445387405)
                ·
                  refine ⟨12666579124998729542020277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33777544333329945445387405 12666579124998729542020277)
                  ·
                    refine ⟨1187491792968630894564401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12666579124998729542020277 1187491792968630894564401)
                    ·
                      rfl

theorem cell23_6937896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 2, 3, 5].length) (baseStart_6937896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6937896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6937896 prefixEnd_6937896 := by exact prefixLift 6937896
  have htrace : WordTrace (prefixWord ++ tailWord_6937896) baseStart_6937896 baseEnd_6937896 := by
    simpa [prefixWord, tailWord_6937896, baseEnd_6937896] using wordTrace_append hprefix tailTrace_6937896
  have hstable : (prefixWord ++ tailWord_6937896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6937896).length < 2 ^ (prefixWord ++ tailWord_6937896).sum := by decide
  have hdescent : baseEnd_6937896 < baseStart_6937896 := by decide
  rcases family_descends (prefixWord ++ tailWord_6937896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6937916 : List Nat := [2, 2, 2, 2, 1, 3, 2, 1, 3, 1, 4]
def baseStart_6937916 : Nat := 118140960795 + 6937916 * 2 ^ 59
def prefixEnd_6937916 : Nat := 4983230072969 + 3 ^ 40 * 6937916 * 2
def baseEnd_6937916 : Nat := 3562485648518982605443111

theorem tailTrace_6937916 : CollatzResearch.WordTrace tailWord_6937916 prefixEnd_6937916 3562485648518982605443111 := by
  unfold tailWord_6937916
  simp only [CollatzResearch.WordTrace]
  refine ⟨126523292566561354281532801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168697723422081805708710401 126523292566561354281532801)
  ·
    refine ⟨94892469424921015711149601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126523292566561354281532801 94892469424921015711149601)
    ·
      refine ⟨71169352068690761783362201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94892469424921015711149601 71169352068690761783362201)
      ·
        refine ⟨53377014051518071337521651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71169352068690761783362201 53377014051518071337521651)
        ·
          refine ⟨80065521077277107006282477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53377014051518071337521651 80065521077277107006282477)
          ·
            refine ⟨30024570403978915127355929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80065521077277107006282477 30024570403978915127355929)
            ·
              refine ⟨22518427802984186345516947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30024570403978915127355929 22518427802984186345516947)
              ·
                refine ⟨33777641704476279518275421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22518427802984186345516947 33777641704476279518275421)
                ·
                  refine ⟨12666615639178604819353283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33777641704476279518275421 12666615639178604819353283)
                  ·
                    refine ⟨18999923458767907229029925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12666615639178604819353283 18999923458767907229029925)
                    ·
                      refine ⟨3562485648518982605443111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18999923458767907229029925 3562485648518982605443111)
                      ·
                        rfl

theorem cell23_6937916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 1, 3, 1, 4].length) (baseStart_6937916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6937916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6937916 prefixEnd_6937916 := by exact prefixLift 6937916
  have htrace : WordTrace (prefixWord ++ tailWord_6937916) baseStart_6937916 baseEnd_6937916 := by
    simpa [prefixWord, tailWord_6937916, baseEnd_6937916] using wordTrace_append hprefix tailTrace_6937916
  have hstable : (prefixWord ++ tailWord_6937916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6937916).length < 2 ^ (prefixWord ++ tailWord_6937916).sum := by decide
  have hdescent : baseEnd_6937916 < baseStart_6937916 := by decide
  rcases family_descends (prefixWord ++ tailWord_6937916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6937943 : List Nat := [1, 1, 3, 2, 3, 2, 3, 2, 2, 4]
def baseStart_6937943 : Nat := 118140960795 + 6937943 * 2 ^ 59
def prefixEnd_6937943 : Nat := 4983230072969 + 3 ^ 40 * 6937943 * 2
def baseEnd_6937943 : Nat := 1187499837498884666601829

theorem tailTrace_6937943 : CollatzResearch.WordTrace tailWord_6937943 prefixEnd_6937943 1187499837498884666601829 := by
  unfold tailWord_6937943
  simp only [CollatzResearch.WordTrace]
  refine ⟨253047569904024892174298483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168698379936016594782865655 253047569904024892174298483)
  ·
    refine ⟨379571354856037338261447725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253047569904024892174298483 379571354856037338261447725)
    ·
      refine ⟨142339258071014001848042897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 379571354856037338261447725 142339258071014001848042897)
      ·
        refine ⟨106754443553260501386032173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142339258071014001848042897 106754443553260501386032173)
        ·
          refine ⟨40032916332472688019762065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106754443553260501386032173 40032916332472688019762065)
          ·
            refine ⟨30024687249354516014821549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40032916332472688019762065 30024687249354516014821549)
            ·
              refine ⟨11259257718507943505558081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30024687249354516014821549 11259257718507943505558081)
              ·
                refine ⟨8444443288880957629168561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11259257718507943505558081 8444443288880957629168561)
                ·
                  refine ⟨6333332466660718221876421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8444443288880957629168561 6333332466660718221876421)
                  ·
                    refine ⟨1187499837498884666601829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6333332466660718221876421 1187499837498884666601829)
                    ·
                      rfl

theorem cell23_6937943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 3, 2, 2, 4].length) (baseStart_6937943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6937943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6937943 prefixEnd_6937943 := by exact prefixLift 6937943
  have htrace : WordTrace (prefixWord ++ tailWord_6937943) baseStart_6937943 baseEnd_6937943 := by
    simpa [prefixWord, tailWord_6937943, baseEnd_6937943] using wordTrace_append hprefix tailTrace_6937943
  have hstable : (prefixWord ++ tailWord_6937943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6937943).length < 2 ^ (prefixWord ++ tailWord_6937943).sum := by decide
  have hdescent : baseEnd_6937943 < baseStart_6937943 := by decide
  rcases family_descends (prefixWord ++ tailWord_6937943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6937960 : List Nat := [2, 1, 4, 2, 4, 1, 1, 1, 1, 6]
def baseStart_6937960 : Nat := 118140960795 + 6937960 * 2 ^ 59
def prefixEnd_6937960 : Nat := 4983230072969 + 3 ^ 40 * 6937960 * 2
def baseEnd_6937960 : Nat := 1187502747222593477764303

theorem tailTrace_6937960 : CollatzResearch.WordTrace tailWord_6937960 prefixEnd_6937960 1187502747222593477764303 := by
  unfold tailWord_6937960
  simp only [CollatzResearch.WordTrace]
  refine ⟨126524094972481652038833667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168698793296642202718444889 126524094972481652038833667)
  ·
    refine ⟨189786142458722478058250501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126524094972481652038833667 189786142458722478058250501)
    ·
      refine ⟨35584901711010464635921969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 189786142458722478058250501 35584901711010464635921969)
      ·
        refine ⟨26688676283257848476941477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35584901711010464635921969 26688676283257848476941477)
        ·
          refine ⟨5004126803110846589426527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26688676283257848476941477 5004126803110846589426527)
          ·
            refine ⟨7506190204666269884139791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5004126803110846589426527 7506190204666269884139791)
            ·
              refine ⟨11259285306999404826209687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7506190204666269884139791 11259285306999404826209687)
              ·
                refine ⟨16888927960499107239314531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11259285306999404826209687 16888927960499107239314531)
                ·
                  refine ⟨25333391940748660858971797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16888927960499107239314531 25333391940748660858971797)
                  ·
                    refine ⟨1187502747222593477764303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25333391940748660858971797 1187502747222593477764303)
                    ·
                      rfl

theorem cell23_6937960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 1, 1, 1, 6].length) (baseStart_6937960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6937960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6937960 prefixEnd_6937960 := by exact prefixLift 6937960
  have htrace : WordTrace (prefixWord ++ tailWord_6937960) baseStart_6937960 baseEnd_6937960 := by
    simpa [prefixWord, tailWord_6937960, baseEnd_6937960] using wordTrace_append hprefix tailTrace_6937960
  have hstable : (prefixWord ++ tailWord_6937960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6937960).length < 2 ^ (prefixWord ++ tailWord_6937960).sum := by decide
  have hdescent : baseEnd_6937960 < baseStart_6937960 := by decide
  rcases family_descends (prefixWord ++ tailWord_6937960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6937969 : List Nat := [1, 2, 2, 2, 1, 2, 2, 2, 2, 7]
def baseStart_6937969 : Nat := 118140960795 + 6937969 * 2 ^ 59
def prefixEnd_6937969 : Nat := 4983230072969 + 3 ^ 40 * 6937969 * 2
def baseEnd_6937969 : Nat := 1187504287664556966026789

theorem tailTrace_6937969 : CollatzResearch.WordTrace tailWord_6937969 prefixEnd_6937969 1187504287664556966026789 := by
  unfold tailWord_6937969
  simp only [CollatzResearch.WordTrace]
  refine ⟨253048518201930698614744961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168699012134620465743163307 253048518201930698614744961)
  ·
    refine ⟨189786388651448023961058721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253048518201930698614744961 189786388651448023961058721)
    ·
      refine ⟨142339791488586017970794041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189786388651448023961058721 142339791488586017970794041)
      ·
        refine ⟨106754843616439513478095531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142339791488586017970794041 106754843616439513478095531)
        ·
          refine ⟨160132265424659270217143297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106754843616439513478095531 160132265424659270217143297)
          ·
            refine ⟨120099199068494452662857473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160132265424659270217143297 120099199068494452662857473)
            ·
              refine ⟨90074399301370839497143105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120099199068494452662857473 90074399301370839497143105)
              ·
                refine ⟨67555799476028129622857329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90074399301370839497143105 67555799476028129622857329)
                ·
                  refine ⟨50666849607021097217142997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67555799476028129622857329 50666849607021097217142997)
                  ·
                    refine ⟨1187504287664556966026789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50666849607021097217142997 1187504287664556966026789)
                    ·
                      rfl

theorem cell23_6937969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 2, 7].length) (baseStart_6937969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6937969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6937969 prefixEnd_6937969 := by exact prefixLift 6937969
  have htrace : WordTrace (prefixWord ++ tailWord_6937969) baseStart_6937969 baseEnd_6937969 := by
    simpa [prefixWord, tailWord_6937969, baseEnd_6937969] using wordTrace_append hprefix tailTrace_6937969
  have hstable : (prefixWord ++ tailWord_6937969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6937969).length < 2 ^ (prefixWord ++ tailWord_6937969).sum := by decide
  have hdescent : baseEnd_6937969 < baseStart_6937969 := by decide
  rcases family_descends (prefixWord ++ tailWord_6937969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6937976 : List Nat := [2, 1, 2, 1, 1, 1, 1, 1, 4, 7, 2]
def baseStart_6937976 : Nat := 118140960795 + 6937976 * 2 ^ 59
def prefixEnd_6937976 : Nat := 4983230072969 + 3 ^ 40 * 6937976 * 2
def baseEnd_6937976 : Nat := 3562516457358252370692835

theorem tailTrace_6937976 : CollatzResearch.WordTrace tailWord_6937976 prefixEnd_6937976 3562516457358252370692835 := by
  unfold tailWord_6937976
  simp only [CollatzResearch.WordTrace]
  refine ⟨126524386756452669405124891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168699182341936892540166521 126524386756452669405124891)
  ·
    refine ⟨189786580134679004107687337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126524386756452669405124891 189786580134679004107687337)
    ·
      refine ⟨142339935101009253080765503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189786580134679004107687337 142339935101009253080765503)
      ·
        refine ⟨213509902651513879621148255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142339935101009253080765503 213509902651513879621148255)
        ·
          refine ⟨320264853977270819431722383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213509902651513879621148255 320264853977270819431722383)
          ·
            refine ⟨480397280965906229147583575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 320264853977270819431722383 480397280965906229147583575)
            ·
              refine ⟨720595921448859343721375363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 480397280965906229147583575 720595921448859343721375363)
              ·
                refine ⟨1080893882173289015582063045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 720595921448859343721375363 1080893882173289015582063045)
                ·
                  refine ⟨202667602907491690421636821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1080893882173289015582063045 202667602907491690421636821)
                  ·
                    refine ⟨4750021943144336494257113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 202667602907491690421636821 4750021943144336494257113)
                    ·
                      refine ⟨3562516457358252370692835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4750021943144336494257113 3562516457358252370692835)
                      ·
                        rfl

theorem cell23_6937976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 4, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 4, 7, 2].length) (baseStart_6937976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6937976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6937976 prefixEnd_6937976 := by exact prefixLift 6937976
  have htrace : WordTrace (prefixWord ++ tailWord_6937976) baseStart_6937976 baseEnd_6937976 := by
    simpa [prefixWord, tailWord_6937976, baseEnd_6937976] using wordTrace_append hprefix tailTrace_6937976
  have hstable : (prefixWord ++ tailWord_6937976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6937976).length < 2 ^ (prefixWord ++ tailWord_6937976).sum := by decide
  have hdescent : baseEnd_6937976 < baseStart_6937976 := by decide
  rcases family_descends (prefixWord ++ tailWord_6937976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6937979 : List Nat := [1, 1, 1, 1, 1, 6, 1, 1, 1, 4, 5]
def baseStart_6937979 : Nat := 118140960795 + 6937979 * 2 ^ 59
def prefixEnd_6937979 : Nat := 4983230072969 + 3 ^ 40 * 6937979 * 2
def baseEnd_6937979 : Nat := 3562517997800215858955321

theorem tailTrace_6937979 : CollatzResearch.WordTrace tailWord_6937979 prefixEnd_6937979 3562517997800215858955321 := by
  unfold tailWord_6937979
  simp only [CollatzResearch.WordTrace]
  refine ⟨253048882931894470322608991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168699255287929646881739327 253048882931894470322608991)
  ·
    refine ⟨379573324397841705483913487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253048882931894470322608991 379573324397841705483913487)
    ·
      refine ⟨569359986596762558225870231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379573324397841705483913487 569359986596762558225870231)
      ·
        refine ⟨854039979895143837338805347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 569359986596762558225870231 854039979895143837338805347)
        ·
          refine ⟨1281059969842715756008208021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 854039979895143837338805347 1281059969842715756008208021)
          ·
            refine ⟨60049686086377301062884751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1281059969842715756008208021 60049686086377301062884751)
            ·
              refine ⟨90074529129565951594327127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60049686086377301062884751 90074529129565951594327127)
              ·
                refine ⟨135111793694348927391490691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90074529129565951594327127 135111793694348927391490691)
                ·
                  refine ⟨202667690541523391087236037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 135111793694348927391490691 202667690541523391087236037)
                  ·
                    refine ⟨38000191976535635828856757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 202667690541523391087236037 38000191976535635828856757)
                    ·
                      refine ⟨3562517997800215858955321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38000191976535635828856757 3562517997800215858955321)
                      ·
                        rfl

theorem cell23_6937979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 4, 5].length) (baseStart_6937979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6937979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6937979 prefixEnd_6937979 := by exact prefixLift 6937979
  have htrace : WordTrace (prefixWord ++ tailWord_6937979) baseStart_6937979 baseEnd_6937979 := by
    simpa [prefixWord, tailWord_6937979, baseEnd_6937979] using wordTrace_append hprefix tailTrace_6937979
  have hstable : (prefixWord ++ tailWord_6937979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6937979).length < 2 ^ (prefixWord ++ tailWord_6937979).sum := by decide
  have hdescent : baseEnd_6937979 < baseStart_6937979 := by decide
  rcases family_descends (prefixWord ++ tailWord_6937979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6938044 : List Nat := [2, 2, 2, 4, 2, 1, 3, 1, 1, 3, 2]
def baseStart_6938044 : Nat := 118140960795 + 6938044 * 2 ^ 59
def prefixEnd_6938044 : Nat := 4983230072969 + 3 ^ 40 * 6938044 * 2
def baseEnd_6938044 : Nat := 3562551374042758104642523

theorem tailTrace_6938044 : CollatzResearch.WordTrace tailWord_6938044 prefixEnd_6938044 3562551374042758104642523 := by
  unfold tailWord_6938044
  simp only [CollatzResearch.WordTrace]
  refine ⟨126525626838329493211862593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168700835784439324282483457 126525626838329493211862593)
  ·
    refine ⟨94894220128747119908896945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126525626838329493211862593 94894220128747119908896945)
    ·
      refine ⟨71170665096560339931672709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94894220128747119908896945 71170665096560339931672709)
      ·
        refine ⟨13344499705605063737188633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71170665096560339931672709 13344499705605063737188633)
        ·
          refine ⟨10008374779203797802891475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13344499705605063737188633 10008374779203797802891475)
          ·
            refine ⟨15012562168805696704337213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10008374779203797802891475 15012562168805696704337213)
            ·
              refine ⟨5629710813302136264126455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15012562168805696704337213 5629710813302136264126455)
              ·
                refine ⟨8444566219953204396189683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5629710813302136264126455 8444566219953204396189683)
                ·
                  refine ⟨12666849329929806594284525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8444566219953204396189683 12666849329929806594284525)
                  ·
                    refine ⟨4750068498723677472856697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12666849329929806594284525 4750068498723677472856697)
                    ·
                      refine ⟨3562551374042758104642523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4750068498723677472856697 3562551374042758104642523)
                      ·
                        rfl

theorem cell23_6938044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 3, 1, 1, 3, 2].length) (baseStart_6938044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6938044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6938044 prefixEnd_6938044 := by exact prefixLift 6938044
  have htrace : WordTrace (prefixWord ++ tailWord_6938044) baseStart_6938044 baseEnd_6938044 := by
    simpa [prefixWord, tailWord_6938044, baseEnd_6938044] using wordTrace_append hprefix tailTrace_6938044
  have hstable : (prefixWord ++ tailWord_6938044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6938044).length < 2 ^ (prefixWord ++ tailWord_6938044).sum := by decide
  have hdescent : baseEnd_6938044 < baseStart_6938044 := by decide
  rcases family_descends (prefixWord ++ tailWord_6938044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6938070 : List Nat := [5, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4]
def baseStart_6938070 : Nat := 118140960795 + 6938070 * 2 ^ 59
def prefixEnd_6938070 : Nat := 4983230072969 + 3 ^ 40 * 6938070 * 2
def baseEnd_6938070 : Nat := 3562564724539775002917403

theorem tailTrace_6938070 : CollatzResearch.WordTrace tailWord_6938070 prefixEnd_6938070 3562564724539775002917403 := by
  unfold tailWord_6938070
  simp only [CollatzResearch.WordTrace]
  refine ⟨15815762623410299554010729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 168701467983043195242781109 15815762623410299554010729)
  ·
    refine ⟨11861821967557724665508047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15815762623410299554010729 11861821967557724665508047)
    ·
      refine ⟨17792732951336586998262071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11861821967557724665508047 17792732951336586998262071)
      ·
        refine ⟨26689099427004880497393107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17792732951336586998262071 26689099427004880497393107)
        ·
          refine ⟨40033649140507320746089661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26689099427004880497393107 40033649140507320746089661)
          ·
            refine ⟨15012618427690245279783623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40033649140507320746089661 15012618427690245279783623)
            ·
              refine ⟨22518927641535367919675435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15012618427690245279783623 22518927641535367919675435)
              ·
                refine ⟨33778391462303051879513153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22518927641535367919675435 33778391462303051879513153)
                ·
                  refine ⟨25333793596727288909634865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33778391462303051879513153 25333793596727288909634865)
                  ·
                    refine ⟨19000345197545466682226149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25333793596727288909634865 19000345197545466682226149)
                    ·
                      refine ⟨3562564724539775002917403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19000345197545466682226149 3562564724539775002917403)
                      ·
                        rfl

theorem cell23_6938070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_6938070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6938070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6938070 prefixEnd_6938070 := by exact prefixLift 6938070
  have htrace : WordTrace (prefixWord ++ tailWord_6938070) baseStart_6938070 baseEnd_6938070 := by
    simpa [prefixWord, tailWord_6938070, baseEnd_6938070] using wordTrace_append hprefix tailTrace_6938070
  have hstable : (prefixWord ++ tailWord_6938070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6938070).length < 2 ^ (prefixWord ++ tailWord_6938070).sum := by decide
  have hdescent : baseEnd_6938070 < baseStart_6938070 := by decide
  rcases family_descends (prefixWord ++ tailWord_6938070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6938073 : List Nat := [1, 2, 1, 2, 4, 3, 1, 1, 2, 3, 3]
def baseStart_6938073 : Nat := 118140960795 + 6938073 * 2 ^ 59
def prefixEnd_6938073 : Nat := 4983230072969 + 3 ^ 40 * 6938073 * 2
def baseEnd_6938073 : Nat := 3562566264981738491179889

theorem tailTrace_6938073 : CollatzResearch.WordTrace tailWord_6938073 prefixEnd_6938073 3562566264981738491179889 := by
  unfold tailWord_6938073
  simp only [CollatzResearch.WordTrace]
  refine ⟨253052311393553924376530873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168701540929035949584353915 253052311393553924376530873)
  ·
    refine ⟨189789233545165443282398155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253052311393553924376530873 189789233545165443282398155)
    ·
      refine ⟨284683850317748164923597233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189789233545165443282398155 284683850317748164923597233)
      ·
        refine ⟨213512887738311123692697925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 284683850317748164923597233 213512887738311123692697925)
        ·
          refine ⟨40033666450933335692380861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 213512887738311123692697925 40033666450933335692380861)
          ·
            refine ⟨15012624919100000884642823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40033666450933335692380861 15012624919100000884642823)
            ·
              refine ⟨22518937378650001326964235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15012624919100000884642823 22518937378650001326964235)
              ·
                refine ⟨33778406067975001990446353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22518937378650001326964235 33778406067975001990446353)
                ·
                  refine ⟨25333804550981251492834765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33778406067975001990446353 25333804550981251492834765)
                  ·
                    refine ⟨9500176706617969309813037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25333804550981251492834765 9500176706617969309813037)
                    ·
                      refine ⟨3562566264981738491179889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9500176706617969309813037 3562566264981738491179889)
                      ·
                        rfl

theorem cell23_6938073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 1, 2, 3, 3].length) (baseStart_6938073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6938073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6938073 prefixEnd_6938073 := by exact prefixLift 6938073
  have htrace : WordTrace (prefixWord ++ tailWord_6938073) baseStart_6938073 baseEnd_6938073 := by
    simpa [prefixWord, tailWord_6938073, baseEnd_6938073] using wordTrace_append hprefix tailTrace_6938073
  have hstable : (prefixWord ++ tailWord_6938073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6938073).length < 2 ^ (prefixWord ++ tailWord_6938073).sum := by decide
  have hdescent : baseEnd_6938073 < baseStart_6938073 := by decide
  rcases family_descends (prefixWord ++ tailWord_6938073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6938133 : List Nat := [1, 3, 2, 1, 3, 2, 1, 2, 1, 4, 3]
def baseStart_6938133 : Nat := 118140960795 + 6938133 * 2 ^ 59
def prefixEnd_6938133 : Nat := 4983230072969 + 3 ^ 40 * 6938133 * 2
def baseEnd_6938133 : Nat := 3562597073821008256429613

theorem tailTrace_6938133 : CollatzResearch.WordTrace tailWord_6938133 prefixEnd_6938133 3562597073821008256429613 := by
  unfold tailWord_6938133
  simp only [CollatzResearch.WordTrace]
  refine ⟨253054499773336554623715053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168702999848891036415810035 253054499773336554623715053)
  ·
    refine ⟨94895437415001207983893145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 253054499773336554623715053 94895437415001207983893145)
    ·
      refine ⟨71171578061250905987919859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94895437415001207983893145 71171578061250905987919859)
      ·
        refine ⟨106757367091876358981879789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71171578061250905987919859 106757367091876358981879789)
        ·
          refine ⟨40034012659453634618204921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106757367091876358981879789 40034012659453634618204921)
          ·
            refine ⟨30025509494590225963653691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40034012659453634618204921 30025509494590225963653691)
            ·
              refine ⟨45038264241885338945480537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30025509494590225963653691 45038264241885338945480537)
              ·
                refine ⟨33778698181414004209110403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45038264241885338945480537 33778698181414004209110403)
                ·
                  refine ⟨50668047272121006313665605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33778698181414004209110403 50668047272121006313665605)
                  ·
                    refine ⟨9500258863522688683812301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50668047272121006313665605 9500258863522688683812301)
                    ·
                      refine ⟨3562597073821008256429613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9500258863522688683812301 3562597073821008256429613)
                      ·
                        rfl

theorem cell23_6938133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 2, 1, 4, 3].length) (baseStart_6938133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6938133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6938133 prefixEnd_6938133 := by exact prefixLift 6938133
  have htrace : WordTrace (prefixWord ++ tailWord_6938133) baseStart_6938133 baseEnd_6938133 := by
    simpa [prefixWord, tailWord_6938133, baseEnd_6938133] using wordTrace_append hprefix tailTrace_6938133
  have hstable : (prefixWord ++ tailWord_6938133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6938133).length < 2 ^ (prefixWord ++ tailWord_6938133).sum := by decide
  have hdescent : baseEnd_6938133 < baseStart_6938133 := by decide
  rcases family_descends (prefixWord ++ tailWord_6938133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6938176 : List Nat := [2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 7]
def baseStart_6938176 : Nat := 118140960795 + 6938176 * 2 ^ 59
def prefixEnd_6938176 : Nat := 4983230072969 + 3 ^ 40 * 6938176 * 2
def baseEnd_6938176 : Nat := 3562619153489151588191915

theorem tailTrace_6938176 : CollatzResearch.WordTrace tailWord_6938176 prefixEnd_6938176 3562619153489151588191915 := by
  unfold tailWord_6938176
  simp only [CollatzResearch.WordTrace]
  refine ⟨126528034056090386483765191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168704045408120515311686921 126528034056090386483765191)
  ·
    refine ⟨189792051084135579725647787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126528034056090386483765191 189792051084135579725647787)
    ·
      refine ⟨284688076626203369588471681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189792051084135579725647787 284688076626203369588471681)
      ·
        refine ⟨213516057469652527191353761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 284688076626203369588471681 213516057469652527191353761)
        ·
          refine ⟨160137043102239395393515321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213516057469652527191353761 160137043102239395393515321)
          ·
            refine ⟨120102782326679546545136491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160137043102239395393515321 120102782326679546545136491)
            ·
              refine ⟨180154173490019319817704737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120102782326679546545136491 180154173490019319817704737)
              ·
                refine ⟨135115630117514489863278553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 180154173490019319817704737 135115630117514489863278553)
                ·
                  refine ⟨101336722588135867397458915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 135115630117514489863278553 101336722588135867397458915)
                  ·
                    refine ⟨152005083882203801096188373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 101336722588135867397458915 152005083882203801096188373)
                    ·
                      refine ⟨3562619153489151588191915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 152005083882203801096188373 3562619153489151588191915)
                      ·
                        rfl

theorem cell23_6938176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 7].length) (baseStart_6938176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6938176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6938176 prefixEnd_6938176 := by exact prefixLift 6938176
  have htrace : WordTrace (prefixWord ++ tailWord_6938176) baseStart_6938176 baseEnd_6938176 := by
    simpa [prefixWord, tailWord_6938176, baseEnd_6938176] using wordTrace_append hprefix tailTrace_6938176
  have hstable : (prefixWord ++ tailWord_6938176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6938176).length < 2 ^ (prefixWord ++ tailWord_6938176).sum := by decide
  have hdescent : baseEnd_6938176 < baseStart_6938176 := by decide
  rcases family_descends (prefixWord ++ tailWord_6938176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6938190 : List Nat := [4, 1, 1, 1, 1, 2, 1, 1, 6, 3, 2]
def baseStart_6938190 : Nat := 118140960795 + 6938190 * 2 ^ 59
def prefixEnd_6938190 : Nat := 4983230072969 + 3 ^ 40 * 6938190 * 2
def baseEnd_6938190 : Nat := 3562626342218314533416851

theorem tailTrace_6938190 : CollatzResearch.WordTrace tailWord_6938190 prefixEnd_6938190 3562626342218314533416851 := by
  unfold tailWord_6938190
  simp only [CollatzResearch.WordTrace]
  refine ⟨31632072341766256669817503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168704385822753368905693349 31632072341766256669817503)
  ·
    refine ⟨47448108512649385004726255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31632072341766256669817503 47448108512649385004726255)
    ·
      refine ⟨71172162768974077507089383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47448108512649385004726255 71172162768974077507089383)
      ·
        refine ⟨106758244153461116260634075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71172162768974077507089383 106758244153461116260634075)
        ·
          refine ⟨160137366230191674390951113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106758244153461116260634075 160137366230191674390951113)
          ·
            refine ⟨120103024672643755793213335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160137366230191674390951113 120103024672643755793213335)
            ·
              refine ⟨180154537008965633689820003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120103024672643755793213335 180154537008965633689820003)
              ·
                refine ⟨270231805513448450534730005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 180154537008965633689820003 270231805513448450534730005)
                ·
                  refine ⟨12667115883442896118815469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 270231805513448450534730005 12667115883442896118815469)
                  ·
                    refine ⟨4750168456291086044555801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12667115883442896118815469 4750168456291086044555801)
                    ·
                      refine ⟨3562626342218314533416851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4750168456291086044555801 3562626342218314533416851)
                      ·
                        rfl

theorem cell23_6938190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 6, 3, 2].length) (baseStart_6938190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6938190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6938190 prefixEnd_6938190 := by exact prefixLift 6938190
  have htrace : WordTrace (prefixWord ++ tailWord_6938190) baseStart_6938190 baseEnd_6938190 := by
    simpa [prefixWord, tailWord_6938190, baseEnd_6938190] using wordTrace_append hprefix tailTrace_6938190
  have hstable : (prefixWord ++ tailWord_6938190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6938190).length < 2 ^ (prefixWord ++ tailWord_6938190).sum := by decide
  have hdescent : baseEnd_6938190 < baseStart_6938190 := by decide
  rcases family_descends (prefixWord ++ tailWord_6938190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6938213 : List Nat := [1, 3, 1, 3, 3, 1, 1, 1, 3, 6]
def baseStart_6938213 : Nat := 118140960795 + 6938213 * 2 ^ 59
def prefixEnd_6938213 : Nat := 4983230072969 + 3 ^ 40 * 6938213 * 2
def baseEnd_6938213 : Nat := 1187546050757789314476415

theorem tailTrace_6938213 : CollatzResearch.WordTrace tailWord_6938213 prefixEnd_6938213 1187546050757789314476415 := by
  unfold tailWord_6938213
  simp only [CollatzResearch.WordTrace]
  refine ⟨253057417613046728286627293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168704945075364485524418195 253057417613046728286627293)
  ·
    refine ⟨94896531604892523107485235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 253057417613046728286627293 94896531604892523107485235)
    ·
      refine ⟨142344797407338784661227853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94896531604892523107485235 142344797407338784661227853)
      ·
        refine ⟨53379299027752044247960445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142344797407338784661227853 53379299027752044247960445)
        ·
          refine ⟨20017237135407016592985167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53379299027752044247960445 20017237135407016592985167)
          ·
            refine ⟨30025855703110524889477751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20017237135407016592985167 30025855703110524889477751)
            ·
              refine ⟨45038783554665787334216627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30025855703110524889477751 45038783554665787334216627)
              ·
                refine ⟨67558175331998681001324941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45038783554665787334216627 67558175331998681001324941)
                ·
                  refine ⟨25334315749499505375496853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67558175331998681001324941 25334315749499505375496853)
                  ·
                    refine ⟨1187546050757789314476415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25334315749499505375496853 1187546050757789314476415)
                    ·
                      rfl

theorem cell23_6938213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 1, 3, 6].length) (baseStart_6938213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6938213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6938213 prefixEnd_6938213 := by exact prefixLift 6938213
  have htrace : WordTrace (prefixWord ++ tailWord_6938213) baseStart_6938213 baseEnd_6938213 := by
    simpa [prefixWord, tailWord_6938213, baseEnd_6938213] using wordTrace_append hprefix tailTrace_6938213
  have hstable : (prefixWord ++ tailWord_6938213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6938213).length < 2 ^ (prefixWord ++ tailWord_6938213).sum := by decide
  have hdescent : baseEnd_6938213 < baseStart_6938213 := by decide
  rcases family_descends (prefixWord ++ tailWord_6938213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6938233 : List Nat := [1, 2, 1, 3, 3, 1, 1, 2, 3, 2, 4]
def baseStart_6938233 : Nat := 118140960795 + 6938233 * 2 ^ 59
def prefixEnd_6938233 : Nat := 4983230072969 + 3 ^ 40 * 6938233 * 2
def baseEnd_6938233 : Nat := 3562648421886457865179153

theorem tailTrace_6938233 : CollatzResearch.WordTrace tailWord_6938233 prefixEnd_6938233 3562648421886457865179153 := by
  unfold tailWord_6938233
  simp only [CollatzResearch.WordTrace]
  refine ⟨253058147072974271702355353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168705431381982847801570235 253058147072974271702355353)
  ·
    refine ⟨189793610304730703776766515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253058147072974271702355353 189793610304730703776766515)
    ·
      refine ⟨284690415457096055665149773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189793610304730703776766515 284690415457096055665149773)
      ·
        refine ⟨106758905796411020874431165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 284690415457096055665149773 106758905796411020874431165)
        ·
          refine ⟨40034589673654132827911687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106758905796411020874431165 40034589673654132827911687)
          ·
            refine ⟨60051884510481199241867531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40034589673654132827911687 60051884510481199241867531)
            ·
              refine ⟨90077826765721798862801297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60051884510481199241867531 90077826765721798862801297)
              ·
                refine ⟨67558370074291349147100973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90077826765721798862801297 67558370074291349147100973)
                ·
                  refine ⟨25334388777859255930162865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67558370074291349147100973 25334388777859255930162865)
                  ·
                    refine ⟨19000791583394441947622149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25334388777859255930162865 19000791583394441947622149)
                    ·
                      refine ⟨3562648421886457865179153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19000791583394441947622149 3562648421886457865179153)
                      ·
                        rfl

theorem cell23_6938233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 2, 3, 2, 4].length) (baseStart_6938233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6938233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6938233 prefixEnd_6938233 := by exact prefixLift 6938233
  have htrace : WordTrace (prefixWord ++ tailWord_6938233) baseStart_6938233 baseEnd_6938233 := by
    simpa [prefixWord, tailWord_6938233, baseEnd_6938233] using wordTrace_append hprefix tailTrace_6938233
  have hstable : (prefixWord ++ tailWord_6938233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6938233).length < 2 ^ (prefixWord ++ tailWord_6938233).sum := by decide
  have hdescent : baseEnd_6938233 < baseStart_6938233 := by decide
  rcases family_descends (prefixWord ++ tailWord_6938233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6938250 : List Nat := [3, 1, 2, 3, 2, 1, 1, 3, 1, 2, 4]
def baseStart_6938250 : Nat := 118140960795 + 6938250 * 2 ^ 59
def prefixEnd_6938250 : Nat := 4983230072969 + 3 ^ 40 * 6938250 * 2
def baseEnd_6938250 : Nat := 3562657151057584298666575

theorem tailTrace_6938250 : CollatzResearch.WordTrace tailWord_6938250 prefixEnd_6938250 3562657151057584298666575 := by
  unfold tailWord_6938250
  simp only [CollatzResearch.WordTrace]
  refine ⟨63264691778478170901431051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168705844742608455737149469 63264691778478170901431051)
  ·
    refine ⟨94897037667717256352146577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63264691778478170901431051 94897037667717256352146577)
    ·
      refine ⟨71172778250787942264109933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94897037667717256352146577 71172778250787942264109933)
      ·
        refine ⟨26689791844045478349041225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71172778250787942264109933 26689791844045478349041225)
        ·
          refine ⟨20017343883034108761780919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26689791844045478349041225 20017343883034108761780919)
          ·
            refine ⟨30026015824551163142671379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20017343883034108761780919 30026015824551163142671379)
            ·
              refine ⟨45039023736826744714007069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30026015824551163142671379 45039023736826744714007069)
              ·
                refine ⟨16889633901310029267752651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45039023736826744714007069 16889633901310029267752651)
                ·
                  refine ⟨25334450851965043901628977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16889633901310029267752651 25334450851965043901628977)
                  ·
                    refine ⟨19000838138973782926221733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25334450851965043901628977 19000838138973782926221733)
                    ·
                      refine ⟨3562657151057584298666575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19000838138973782926221733 3562657151057584298666575)
                      ·
                        rfl

theorem cell23_6938250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_6938250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6938250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6938250 prefixEnd_6938250 := by exact prefixLift 6938250
  have htrace : WordTrace (prefixWord ++ tailWord_6938250) baseStart_6938250 baseEnd_6938250 := by
    simpa [prefixWord, tailWord_6938250, baseEnd_6938250] using wordTrace_append hprefix tailTrace_6938250
  have hstable : (prefixWord ++ tailWord_6938250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6938250).length < 2 ^ (prefixWord ++ tailWord_6938250).sum := by decide
  have hdescent : baseEnd_6938250 < baseStart_6938250 := by decide
  rcases family_descends (prefixWord ++ tailWord_6938250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6938254 : List Nat := [4, 1, 1, 3, 1, 3, 1, 2, 3, 2, 2]
def baseStart_6938254 : Nat := 118140960795 + 6938254 * 2 ^ 59
def prefixEnd_6938254 : Nat := 4983230072969 + 3 ^ 40 * 6938254 * 2
def baseEnd_6938254 : Nat := 3562659204980202283016557

theorem tailTrace_6938254 : CollatzResearch.WordTrace tailWord_6938254 prefixEnd_6938254 3562659204980202283016557 := by
  unfold tailWord_6938254
  simp only [CollatzResearch.WordTrace]
  refine ⟨31632364125737274036108727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168705942003932128192579877 31632364125737274036108727)
  ·
    refine ⟨47448546188605911054163091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31632364125737274036108727 47448546188605911054163091)
    ·
      refine ⟨71172819282908866581244637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47448546188605911054163091 71172819282908866581244637)
      ·
        refine ⟨26689807231090824967966739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71172819282908866581244637 26689807231090824967966739)
        ·
          refine ⟨40034710846636237451950109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26689807231090824967966739 40034710846636237451950109)
          ·
            refine ⟨15013016567488589044481291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40034710846636237451950109 15013016567488589044481291)
            ·
              refine ⟨22519524851232883566721937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15013016567488589044481291 22519524851232883566721937)
              ·
                refine ⟨16889643638424662675041453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22519524851232883566721937 16889643638424662675041453)
                ·
                  refine ⟨6333616364409248503140545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16889643638424662675041453 6333616364409248503140545)
                  ·
                    refine ⟨4750212273306936377355409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6333616364409248503140545 4750212273306936377355409)
                    ·
                      refine ⟨3562659204980202283016557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4750212273306936377355409 3562659204980202283016557)
                      ·
                        rfl

theorem cell23_6938254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 2, 3, 2, 2].length) (baseStart_6938254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6938254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6938254 prefixEnd_6938254 := by exact prefixLift 6938254
  have htrace : WordTrace (prefixWord ++ tailWord_6938254) baseStart_6938254 baseEnd_6938254 := by
    simpa [prefixWord, tailWord_6938254, baseEnd_6938254] using wordTrace_append hprefix tailTrace_6938254
  have hstable : (prefixWord ++ tailWord_6938254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6938254).length < 2 ^ (prefixWord ++ tailWord_6938254).sum := by decide
  have hdescent : baseEnd_6938254 < baseStart_6938254 := by decide
  rcases family_descends (prefixWord ++ tailWord_6938254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6938271 : List Nat := [1, 1, 2, 7, 1, 2, 2, 1, 1, 1, 4]
def baseStart_6938271 : Nat := 118140960795 + 6938271 * 2 ^ 59
def prefixEnd_6938271 : Nat := 4983230072969 + 3 ^ 40 * 6938271 * 2
def baseEnd_6938271 : Nat := 3562667934151328716503979

theorem tailTrace_6938271 : CollatzResearch.WordTrace tailWord_6938271 prefixEnd_6938271 3562667934151328716503979 := by
  unfold tailWord_6938271
  simp only [CollatzResearch.WordTrace]
  refine ⟨253059533046836604192238667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168706355364557736128159111 253059533046836604192238667)
  ·
    refine ⟨379589299570254906288358001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253059533046836604192238667 379589299570254906288358001)
    ·
      refine ⟨284691974677691179716268501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 379589299570254906288358001 284691974677691179716268501)
      ·
        refine ⟨6672468156508387024600043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 284691974677691179716268501 6672468156508387024600043)
        ·
          refine ⟨10008702234762580536900065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6672468156508387024600043 10008702234762580536900065)
          ·
            refine ⟨7506526676071935402675049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10008702234762580536900065 7506526676071935402675049)
            ·
              refine ⟨5629895007053951552006287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7506526676071935402675049 5629895007053951552006287)
              ·
                refine ⟨8444842510580927328009431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5629895007053951552006287 8444842510580927328009431)
                ·
                  refine ⟨12667263765871390992014147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8444842510580927328009431 12667263765871390992014147)
                  ·
                    refine ⟨19000895648807086488021221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12667263765871390992014147 19000895648807086488021221)
                    ·
                      refine ⟨3562667934151328716503979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19000895648807086488021221 3562667934151328716503979)
                      ·
                        rfl

theorem cell23_6938271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_6938271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6938271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6938271 prefixEnd_6938271 := by exact prefixLift 6938271
  have htrace : WordTrace (prefixWord ++ tailWord_6938271) baseStart_6938271 baseEnd_6938271 := by
    simpa [prefixWord, tailWord_6938271, baseEnd_6938271] using wordTrace_append hprefix tailTrace_6938271
  have hstable : (prefixWord ++ tailWord_6938271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6938271).length < 2 ^ (prefixWord ++ tailWord_6938271).sum := by decide
  have hdescent : baseEnd_6938271 < baseStart_6938271 := by decide
  rcases family_descends (prefixWord ++ tailWord_6938271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6938303 : List Nat := [1, 1, 2, 2, 2, 3, 1, 3, 2, 6]
def baseStart_6938303 : Nat := 118140960795 + 6938303 * 2 ^ 59
def prefixEnd_6938303 : Nat := 4983230072969 + 3 ^ 40 * 6938303 * 2
def baseEnd_6938303 : Nat := 1187561455177424197101277

theorem tailTrace_6938303 : CollatzResearch.WordTrace tailWord_6938303 prefixEnd_6938303 1187561455177424197101277 := by
  unfold tailWord_6938303
  simp only [CollatzResearch.WordTrace]
  refine ⟨253060700182720673657403563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168707133455147115771602375 253060700182720673657403563)
  ·
    refine ⟨379591050274081010486105345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253060700182720673657403563 379591050274081010486105345)
    ·
      refine ⟨284693287705560757864579009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 379591050274081010486105345 284693287705560757864579009)
      ·
        refine ⟨213519965779170568398434257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 284693287705560757864579009 213519965779170568398434257)
        ·
          refine ⟨160139974334377926298825693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213519965779170568398434257 160139974334377926298825693)
          ·
            refine ⟨60052490375391722362059635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 160139974334377926298825693 60052490375391722362059635)
            ·
              refine ⟨90078735563087583543089453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60052490375391722362059635 90078735563087583543089453)
              ·
                refine ⟨33779525836157843828658545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90078735563087583543089453 33779525836157843828658545)
                ·
                  refine ⟨25334644377118382871493909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33779525836157843828658545 25334644377118382871493909)
                  ·
                    refine ⟨1187561455177424197101277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25334644377118382871493909 1187561455177424197101277)
                    ·
                      rfl

theorem cell23_6938303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 3, 2, 6].length) (baseStart_6938303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6938303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6938303 prefixEnd_6938303 := by exact prefixLift 6938303
  have htrace : WordTrace (prefixWord ++ tailWord_6938303) baseStart_6938303 baseEnd_6938303 := by
    simpa [prefixWord, tailWord_6938303, baseEnd_6938303] using wordTrace_append hprefix tailTrace_6938303
  have hstable : (prefixWord ++ tailWord_6938303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6938303).length < 2 ^ (prefixWord ++ tailWord_6938303).sum := by decide
  have hdescent : baseEnd_6938303 < baseStart_6938303 := by decide
  rcases family_descends (prefixWord ++ tailWord_6938303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6938304 : List Nat := [2, 1, 1, 2, 4, 1, 5, 1, 2, 1, 3]
def baseStart_6938304 : Nat := 118140960795 + 6938304 * 2 ^ 59
def prefixEnd_6938304 : Nat := 4983230072969 + 3 ^ 40 * 6938304 * 2
def baseEnd_6938304 : Nat := 3562684879012927087391327

theorem tailTrace_6938304 : CollatzResearch.WordTrace tailWord_6938304 prefixEnd_6938304 3562684879012927087391327 := by
  unfold tailWord_6938304
  simp only [CollatzResearch.WordTrace]
  refine ⟨126530368327858525414094983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168707157770478033885459977 126530368327858525414094983)
  ·
    refine ⟨189795552491787788121142475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126530368327858525414094983 189795552491787788121142475)
    ·
      refine ⟨284693328737681682181713713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189795552491787788121142475 284693328737681682181713713)
      ·
        refine ⟨213519996553261261636285285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 284693328737681682181713713 213519996553261261636285285)
        ·
          refine ⟨40034999353736486556803491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 213519996553261261636285285 40034999353736486556803491)
          ·
            refine ⟨60052499030604729835205237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40034999353736486556803491 60052499030604729835205237)
            ·
              refine ⟨5629921784119193422050491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60052499030604729835205237 5629921784119193422050491)
              ·
                refine ⟨8444882676178790133075737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5629921784119193422050491 8444882676178790133075737)
                ·
                  refine ⟨6333662007134092599806803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8444882676178790133075737 6333662007134092599806803)
                  ·
                    refine ⟨9500493010701138899710205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6333662007134092599806803 9500493010701138899710205)
                    ·
                      refine ⟨3562684879012927087391327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9500493010701138899710205 3562684879012927087391327)
                      ·
                        rfl

theorem cell23_6938304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 5, 1, 2, 1, 3].length) (baseStart_6938304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6938304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6938304 prefixEnd_6938304 := by exact prefixLift 6938304
  have htrace : WordTrace (prefixWord ++ tailWord_6938304) baseStart_6938304 baseEnd_6938304 := by
    simpa [prefixWord, tailWord_6938304, baseEnd_6938304] using wordTrace_append hprefix tailTrace_6938304
  have hstable : (prefixWord ++ tailWord_6938304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6938304).length < 2 ^ (prefixWord ++ tailWord_6938304).sum := by decide
  have hdescent : baseEnd_6938304 < baseStart_6938304 := by decide
  rcases family_descends (prefixWord ++ tailWord_6938304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6938317 : List Nat := [1, 6, 2, 1, 1, 1, 1, 1, 2, 2, 5]
def baseStart_6938317 : Nat := 118140960795 + 6938317 * 2 ^ 59
def prefixEnd_6938317 : Nat := 4983230072969 + 3 ^ 40 * 6938317 * 2
def baseEnd_6938317 : Nat := 3562691554261435536528767

theorem tailTrace_6938317 : CollatzResearch.WordTrace tailWord_6938317 prefixEnd_6938317 3562691554261435536528767 := by
  unfold tailWord_6938317
  simp only [CollatzResearch.WordTrace]
  refine ⟨253061210804669954048413205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168707473869779969365608803 253061210804669954048413205)
  ·
    refine ⟨11862244256468904096019369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 253061210804669954048413205 11862244256468904096019369)
    ·
      refine ⟨8896683192351678072014527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11862244256468904096019369 8896683192351678072014527)
      ·
        refine ⟨13345024788527517108021791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8896683192351678072014527 13345024788527517108021791)
        ·
          refine ⟨20017537182791275662032687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13345024788527517108021791 20017537182791275662032687)
          ·
            refine ⟨30026305774186913493049031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20017537182791275662032687 30026305774186913493049031)
            ·
              refine ⟨45039458661280370239573547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30026305774186913493049031 45039458661280370239573547)
              ·
                refine ⟨67559187991920555359360321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45039458661280370239573547 67559187991920555359360321)
                ·
                  refine ⟨50669390993940416519520241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67559187991920555359360321 50669390993940416519520241)
                  ·
                    refine ⟨38002043245455312389640181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50669390993940416519520241 38002043245455312389640181)
                    ·
                      refine ⟨3562691554261435536528767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38002043245455312389640181 3562691554261435536528767)
                      ·
                        rfl

theorem cell23_6938317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_6938317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6938317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6938317 prefixEnd_6938317 := by exact prefixLift 6938317
  have htrace : WordTrace (prefixWord ++ tailWord_6938317) baseStart_6938317 baseEnd_6938317 := by
    simpa [prefixWord, tailWord_6938317, baseEnd_6938317] using wordTrace_append hprefix tailTrace_6938317
  have hstable : (prefixWord ++ tailWord_6938317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6938317).length < 2 ^ (prefixWord ++ tailWord_6938317).sum := by decide
  have hdescent : baseEnd_6938317 < baseStart_6938317 := by decide
  rcases family_descends (prefixWord ++ tailWord_6938317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6938327 : List Nat := [1, 1, 3, 2, 1, 3, 1, 1, 6, 2, 2]
def baseStart_6938327 : Nat := 118140960795 + 6938327 * 2 ^ 59
def prefixEnd_6938327 : Nat := 4983230072969 + 3 ^ 40 * 6938327 * 2
def baseEnd_6938327 : Nat := 3562696689067980497403721

theorem tailTrace_6938327 : CollatzResearch.WordTrace tailWord_6938327 prefixEnd_6938327 3562696689067980497403721 := by
  unfold tailWord_6938327
  simp only [CollatzResearch.WordTrace]
  refine ⟨253061575534633725756277235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168707717023089150504184823 253061575534633725756277235)
  ·
    refine ⟨379592363301950588634415853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253061575534633725756277235 379592363301950588634415853)
    ·
      refine ⟨142347136238231470737905945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 379592363301950588634415853 142347136238231470737905945)
      ·
        refine ⟨106760352178673603053429459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142347136238231470737905945 106760352178673603053429459)
        ·
          refine ⟨160140528268010404580144189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106760352178673603053429459 160140528268010404580144189)
          ·
            refine ⟨60052698100503901717554071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 160140528268010404580144189 60052698100503901717554071)
            ·
              refine ⟨90079047150755852576331107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60052698100503901717554071 90079047150755852576331107)
              ·
                refine ⟨135118570726133778864496661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90079047150755852576331107 135118570726133778864496661)
                ·
                  refine ⟨6333683002787520884273281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 135118570726133778864496661 6333683002787520884273281)
                  ·
                    refine ⟨4750262252090640663204961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6333683002787520884273281 4750262252090640663204961)
                    ·
                      refine ⟨3562696689067980497403721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4750262252090640663204961 3562696689067980497403721)
                      ·
                        rfl

theorem cell23_6938327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 6, 2, 2].length) (baseStart_6938327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6938327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6938327 prefixEnd_6938327 := by exact prefixLift 6938327
  have htrace : WordTrace (prefixWord ++ tailWord_6938327) baseStart_6938327 baseEnd_6938327 := by
    simpa [prefixWord, tailWord_6938327, baseEnd_6938327] using wordTrace_append hprefix tailTrace_6938327
  have hstable : (prefixWord ++ tailWord_6938327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6938327).length < 2 ^ (prefixWord ++ tailWord_6938327).sum := by decide
  have hdescent : baseEnd_6938327 < baseStart_6938327 := by decide
  rcases family_descends (prefixWord ++ tailWord_6938327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6938330 : List Nat := [3, 1, 1, 2, 2, 4, 1, 1, 2, 1, 5]
def baseStart_6938330 : Nat := 118140960795 + 6938330 * 2 ^ 59
def prefixEnd_6938330 : Nat := 4983230072969 + 3 ^ 40 * 6938330 * 2
def baseEnd_6938330 : Nat := 3562698229509943985666207

theorem tailTrace_6938330 : CollatzResearch.WordTrace tailWord_6938330 prefixEnd_6938330 3562698229509943985666207 := by
  unfold tailWord_6938330
  simp only [CollatzResearch.WordTrace]
  refine ⟨63265421238405714317159111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168707789969081904845757629 63265421238405714317159111)
  ·
    refine ⟨94898131857608571475738667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63265421238405714317159111 94898131857608571475738667)
    ·
      refine ⟨142347197786412857213608001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94898131857608571475738667 142347197786412857213608001)
      ·
        refine ⟨106760398339809642910206001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142347197786412857213608001 106760398339809642910206001)
        ·
          refine ⟨80070298754857232182654501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106760398339809642910206001 80070298754857232182654501)
          ·
            refine ⟨15013181016535731034247719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80070298754857232182654501 15013181016535731034247719)
            ·
              refine ⟨22519771524803596551371579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15013181016535731034247719 22519771524803596551371579)
              ·
                refine ⟨33779657287205394827057369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22519771524803596551371579 33779657287205394827057369)
                ·
                  refine ⟨25334742965404046120293027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33779657287205394827057369 25334742965404046120293027)
                  ·
                    refine ⟨38002114448106069180439541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25334742965404046120293027 38002114448106069180439541)
                    ·
                      refine ⟨3562698229509943985666207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38002114448106069180439541 3562698229509943985666207)
                      ·
                        rfl

theorem cell23_6938330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 1, 2, 1, 5].length) (baseStart_6938330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6938330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6938330 prefixEnd_6938330 := by exact prefixLift 6938330
  have htrace : WordTrace (prefixWord ++ tailWord_6938330) baseStart_6938330 baseEnd_6938330 := by
    simpa [prefixWord, tailWord_6938330, baseEnd_6938330] using wordTrace_append hprefix tailTrace_6938330
  have hstable : (prefixWord ++ tailWord_6938330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6938330).length < 2 ^ (prefixWord ++ tailWord_6938330).sum := by decide
  have hdescent : baseEnd_6938330 < baseStart_6938330 := by decide
  rcases family_descends (prefixWord ++ tailWord_6938330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6938344 : List Nat := [2, 1, 4, 1, 3, 1, 2, 1, 4, 2, 2]
def baseStart_6938344 : Nat := 118140960795 + 6938344 * 2 ^ 59
def prefixEnd_6938344 : Nat := 4983230072969 + 3 ^ 40 * 6938344 * 2
def baseEnd_6938344 : Nat := 3562705418239106930891143

theorem tailTrace_6938344 : CollatzResearch.WordTrace tailWord_6938344 prefixEnd_6938344 3562705418239106930891143 := by
  unfold tailWord_6938344
  simp only [CollatzResearch.WordTrace]
  refine ⟨126531097787786068829823043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168708130383714758439764057 126531097787786068829823043)
  ·
    refine ⟨189796646681679103244734565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126531097787786068829823043 189796646681679103244734565)
    ·
      refine ⟨35586871252814831858387731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 189796646681679103244734565 35586871252814831858387731)
      ·
        refine ⟨53380306879222247787581597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35586871252814831858387731 53380306879222247787581597)
        ·
          refine ⟨20017615079708342920343099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53380306879222247787581597 20017615079708342920343099)
          ·
            refine ⟨30026422619562514380514649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20017615079708342920343099 30026422619562514380514649)
            ·
              refine ⟨22519816964671885785385987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30026422619562514380514649 22519816964671885785385987)
              ·
                refine ⟨33779725447007828678078981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22519816964671885785385987 33779725447007828678078981)
                ·
                  refine ⟨6333698521313967877139809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33779725447007828678078981 6333698521313967877139809)
                  ·
                    refine ⟨4750273890985475907854857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6333698521313967877139809 4750273890985475907854857)
                    ·
                      refine ⟨3562705418239106930891143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4750273890985475907854857 3562705418239106930891143)
                      ·
                        rfl

theorem cell23_6938344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 1, 4, 2, 2].length) (baseStart_6938344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6938344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6938344 prefixEnd_6938344 := by exact prefixLift 6938344
  have htrace : WordTrace (prefixWord ++ tailWord_6938344) baseStart_6938344 baseEnd_6938344 := by
    simpa [prefixWord, tailWord_6938344, baseEnd_6938344] using wordTrace_append hprefix tailTrace_6938344
  have hstable : (prefixWord ++ tailWord_6938344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6938344).length < 2 ^ (prefixWord ++ tailWord_6938344).sum := by decide
  have hdescent : baseEnd_6938344 < baseStart_6938344 := by decide
  rcases family_descends (prefixWord ++ tailWord_6938344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6938363 : List Nat := [1, 1, 1, 1, 1, 3, 1, 6, 1, 7]
def baseStart_6938363 : Nat := 118140960795 + 6938363 * 2 ^ 59
def prefixEnd_6938363 : Nat := 4983230072969 + 3 ^ 40 * 6938363 * 2
def baseEnd_6938363 : Nat := 1187571724790514118851185

theorem tailTrace_6938363 : CollatzResearch.WordTrace tailWord_6938363 prefixEnd_6938363 1187571724790514118851185 := by
  unfold tailWord_6938363
  simp only [CollatzResearch.WordTrace]
  refine ⟨253062888562503303904587743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168708592375002202603058495 253062888562503303904587743)
  ·
    refine ⟨379594332843754955856881615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253062888562503303904587743 379594332843754955856881615)
    ·
      refine ⟨569391499265632433785322423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379594332843754955856881615 569391499265632433785322423)
      ·
        refine ⟨854087248898448650677983635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 569391499265632433785322423 854087248898448650677983635)
        ·
          refine ⟨1281130873347672976016975453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 854087248898448650677983635 1281130873347672976016975453)
          ·
            refine ⟨480424077505377366006365795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1281130873347672976016975453 480424077505377366006365795)
            ·
              refine ⟨720636116258066049009548693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 480424077505377366006365795 720636116258066049009548693)
              ·
                refine ⟨33779817949596846047322595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 720636116258066049009548693 33779817949596846047322595)
                ·
                  refine ⟨50669726924395269070983893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33779817949596846047322595 50669726924395269070983893)
                  ·
                    refine ⟨1187571724790514118851185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50669726924395269070983893 1187571724790514118851185)
                    ·
                      rfl

theorem cell23_6938363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6, 1, 7].length) (baseStart_6938363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6938363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6938363 prefixEnd_6938363 := by exact prefixLift 6938363
  have htrace : WordTrace (prefixWord ++ tailWord_6938363) baseStart_6938363 baseEnd_6938363 := by
    simpa [prefixWord, tailWord_6938363, baseEnd_6938363] using wordTrace_append hprefix tailTrace_6938363
  have hstable : (prefixWord ++ tailWord_6938363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6938363).length < 2 ^ (prefixWord ++ tailWord_6938363).sum := by decide
  have hdescent : baseEnd_6938363 < baseStart_6938363 := by decide
  rcases family_descends (prefixWord ++ tailWord_6938363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6938380 : List Nat := [2, 2, 1, 2, 2, 1, 3, 3, 2, 5]
def baseStart_6938380 : Nat := 118140960795 + 6938380 * 2 ^ 59
def prefixEnd_6938380 : Nat := 4983230072969 + 3 ^ 40 * 6938380 * 2
def baseEnd_6938380 : Nat := 1187574634514222930013659

theorem tailTrace_6938380 : CollatzResearch.WordTrace tailWord_6938380 prefixEnd_6938380 1187574634514222930013659 := by
  unfold tailWord_6938380
  simp only [CollatzResearch.WordTrace]
  refine ⟨126531754301720857903978297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168709005735627810538637729 126531754301720857903978297)
  ·
    refine ⟨94898815726290643427983723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126531754301720857903978297 94898815726290643427983723)
    ·
      refine ⟨142348223589435965141975585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94898815726290643427983723 142348223589435965141975585)
      ·
        refine ⟨106761167692076973856481689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142348223589435965141975585 106761167692076973856481689)
        ·
          refine ⟨80070875769057730392361267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106761167692076973856481689 80070875769057730392361267)
          ·
            refine ⟨120106313653586595588541901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80070875769057730392361267 120106313653586595588541901)
            ·
              refine ⟨45039867620094973345703213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120106313653586595588541901 45039867620094973345703213)
              ·
                refine ⟨16889950357535615004638705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45039867620094973345703213 16889950357535615004638705)
                ·
                  refine ⟨12667462768151711253479029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16889950357535615004638705 12667462768151711253479029)
                  ·
                    refine ⟨1187574634514222930013659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12667462768151711253479029 1187574634514222930013659)
                    ·
                      rfl

theorem cell23_6938380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 3, 2, 5].length) (baseStart_6938380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6938380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6938380 prefixEnd_6938380 := by exact prefixLift 6938380
  have htrace : WordTrace (prefixWord ++ tailWord_6938380) baseStart_6938380 baseEnd_6938380 := by
    simpa [prefixWord, tailWord_6938380, baseEnd_6938380] using wordTrace_append hprefix tailTrace_6938380
  have hstable : (prefixWord ++ tailWord_6938380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6938380).length < 2 ^ (prefixWord ++ tailWord_6938380).sum := by decide
  have hdescent : baseEnd_6938380 < baseStart_6938380 := by decide
  rcases family_descends (prefixWord ++ tailWord_6938380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6938393 : List Nat := [1, 2, 1, 2, 1, 1, 1, 2, 4, 8]
def baseStart_6938393 : Nat := 118140960795 + 6938393 * 2 ^ 59
def prefixEnd_6938393 : Nat := 4983230072969 + 3 ^ 40 * 6938393 * 2
def baseEnd_6938393 : Nat := 1187576859597059079726139

theorem tailTrace_6938393 : CollatzResearch.WordTrace tailWord_6938393 prefixEnd_6938393 1187576859597059079726139 := by
  unfold tailWord_6938393
  simp only [CollatzResearch.WordTrace]
  refine ⟨253063982752394619028179833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168709321834929746018786555 253063982752394619028179833)
  ·
    refine ⟨189797987064295964271134875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253063982752394619028179833 189797987064295964271134875)
    ·
      refine ⟨284696980596443946406702313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189797987064295964271134875 284696980596443946406702313)
      ·
        refine ⟨213522735447332959805026735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 284696980596443946406702313 213522735447332959805026735)
        ·
          refine ⟨320284103170999439707540103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213522735447332959805026735 320284103170999439707540103)
          ·
            refine ⟨480426154756499159561310155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 320284103170999439707540103 480426154756499159561310155)
            ·
              refine ⟨720639232134748739341965233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 480426154756499159561310155 720639232134748739341965233)
              ·
                refine ⟨540479424101061554506473925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 720639232134748739341965233 540479424101061554506473925)
                ·
                  refine ⟨101339892018949041469963861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 540479424101061554506473925 101339892018949041469963861)
                  ·
                    refine ⟨1187576859597059079726139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 101339892018949041469963861 1187576859597059079726139)
                    ·
                      rfl

theorem cell23_6938393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 8].length) (baseStart_6938393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6938393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6938393 prefixEnd_6938393 := by exact prefixLift 6938393
  have htrace : WordTrace (prefixWord ++ tailWord_6938393) baseStart_6938393 baseEnd_6938393 := by
    simpa [prefixWord, tailWord_6938393, baseEnd_6938393] using wordTrace_append hprefix tailTrace_6938393
  have hstable : (prefixWord ++ tailWord_6938393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6938393).length < 2 ^ (prefixWord ++ tailWord_6938393).sum := by decide
  have hdescent : baseEnd_6938393 < baseStart_6938393 := by decide
  rcases family_descends (prefixWord ++ tailWord_6938393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6938417 : List Nat := [1, 2, 2, 3, 2, 2, 1, 1, 1, 6, 2]
def baseStart_6938417 : Nat := 118140960795 + 6938417 * 2 ^ 59
def prefixEnd_6938417 : Nat := 4983230072969 + 3 ^ 40 * 6938417 * 2
def baseEnd_6938417 : Nat := 3562742902326885145278307

theorem tailTrace_6938417 : CollatzResearch.WordTrace tailWord_6938417 prefixEnd_6938417 3562742902326885145278307 := by
  unfold tailWord_6938417
  simp only [CollatzResearch.WordTrace]
  refine ⟨253064858104307671127053505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168709905402871780751369003 253064858104307671127053505)
  ·
    refine ⟨189798643578230753345290129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253064858104307671127053505 189798643578230753345290129)
    ·
      refine ⟨142348982683673065008967597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189798643578230753345290129 142348982683673065008967597)
      ·
        refine ⟨53380868506377399378362849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142348982683673065008967597 53380868506377399378362849)
        ·
          refine ⟨40035651379783049533772137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53380868506377399378362849 40035651379783049533772137)
          ·
            refine ⟨30026738534837287150329103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40035651379783049533772137 30026738534837287150329103)
            ·
              refine ⟨45040107802255930725493655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30026738534837287150329103 45040107802255930725493655)
              ·
                refine ⟨67560161703383896088240483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45040107802255930725493655 67560161703383896088240483)
                ·
                  refine ⟨101340242555075844132360725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67560161703383896088240483 101340242555075844132360725)
                  ·
                    refine ⟨4750323869769180193704409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 101340242555075844132360725 4750323869769180193704409)
                    ·
                      refine ⟨3562742902326885145278307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4750323869769180193704409 3562742902326885145278307)
                      ·
                        rfl

theorem cell23_6938417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 1, 1, 6, 2].length) (baseStart_6938417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6938417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6938417 prefixEnd_6938417 := by exact prefixLift 6938417
  have htrace : WordTrace (prefixWord ++ tailWord_6938417) baseStart_6938417 baseEnd_6938417 := by
    simpa [prefixWord, tailWord_6938417, baseEnd_6938417] using wordTrace_append hprefix tailTrace_6938417
  have hstable : (prefixWord ++ tailWord_6938417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6938417).length < 2 ^ (prefixWord ++ tailWord_6938417).sum := by decide
  have hdescent : baseEnd_6938417 < baseStart_6938417 := by decide
  rcases family_descends (prefixWord ++ tailWord_6938417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6938517 : List Nat := [1, 3, 2, 1, 1, 3, 1, 3, 4, 4]
def baseStart_6938517 : Nat := 118140960795 + 6938517 * 2 ^ 59
def prefixEnd_6938517 : Nat := 4983230072969 + 3 ^ 40 * 6938517 * 2
def baseEnd_6938517 : Nat := 1187598083464111584675949

theorem tailTrace_6938517 : CollatzResearch.WordTrace tailWord_6938517 prefixEnd_6938517 1187598083464111584675949 := by
  unfold tailWord_6938517
  simp only [CollatzResearch.WordTrace]
  refine ⟨253068505403945388205693805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168712336935963592137129203 253068505403945388205693805)
  ·
    refine ⟨94900689526479520577135177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 253068505403945388205693805 94900689526479520577135177)
    ·
      refine ⟨71175517144859640432851383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94900689526479520577135177 71175517144859640432851383)
      ·
        refine ⟨106763275717289460649277075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71175517144859640432851383 106763275717289460649277075)
        ·
          refine ⟨160144913575934190973915613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106763275717289460649277075 160144913575934190973915613)
          ·
            refine ⟨60054342590975321615218355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 160144913575934190973915613 60054342590975321615218355)
            ·
              refine ⟨90081513886462982422827533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60054342590975321615218355 90081513886462982422827533)
              ·
                refine ⟨33780567707423618408560325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90081513886462982422827533 33780567707423618408560325)
                ·
                  refine ⟨6333856445141928451605061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33780567707423618408560325 6333856445141928451605061)
                  ·
                    refine ⟨1187598083464111584675949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6333856445141928451605061 1187598083464111584675949)
                    ·
                      rfl

theorem cell23_6938517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 3, 4, 4].length) (baseStart_6938517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6938517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6938517 prefixEnd_6938517 := by exact prefixLift 6938517
  have htrace : WordTrace (prefixWord ++ tailWord_6938517) baseStart_6938517 baseEnd_6938517 := by
    simpa [prefixWord, tailWord_6938517, baseEnd_6938517] using wordTrace_append hprefix tailTrace_6938517
  have hstable : (prefixWord ++ tailWord_6938517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6938517).length < 2 ^ (prefixWord ++ tailWord_6938517).sum := by decide
  have hdescent : baseEnd_6938517 < baseStart_6938517 := by decide
  rcases family_descends (prefixWord ++ tailWord_6938517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6938584 : List Nat := [2, 1, 2, 2, 2, 2, 1, 1, 5, 3, 2]
def baseStart_6938584 : Nat := 118140960795 + 6938584 * 2 ^ 59
def prefixEnd_6938584 : Nat := 4983230072969 + 3 ^ 40 * 6938584 * 2
def baseEnd_6938584 : Nat := 3562828653596185991890039

theorem tailTrace_6938584 : CollatzResearch.WordTrace tailWord_6938584 prefixEnd_6938584 3562828653596185991890039 := by
  unfold tailWord_6938584
  simp only [CollatzResearch.WordTrace]
  refine ⟨126535474547351329324191403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168713966063135105765588537 126535474547351329324191403)
  ·
    refine ⟨189803211821026993986287105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126535474547351329324191403 189803211821026993986287105)
    ·
      refine ⟨142352408865770245489715329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189803211821026993986287105 142352408865770245489715329)
      ·
        refine ⟨106764306649327684117286497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142352408865770245489715329 106764306649327684117286497)
        ·
          refine ⟨80073229986995763087964873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106764306649327684117286497 80073229986995763087964873)
          ·
            refine ⟨60054922490246822315973655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80073229986995763087964873 60054922490246822315973655)
            ·
              refine ⟨90082383735370233473960483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60054922490246822315973655 90082383735370233473960483)
              ·
                refine ⟨135123575603055350210940725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90082383735370233473960483 135123575603055350210940725)
                ·
                  refine ⟨12667835212786439082275693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 135123575603055350210940725 12667835212786439082275693)
                  ·
                    refine ⟨4750438204794914655853385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12667835212786439082275693 4750438204794914655853385)
                    ·
                      refine ⟨3562828653596185991890039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4750438204794914655853385 3562828653596185991890039)
                      ·
                        rfl

theorem cell23_6938584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 5, 3, 2].length) (baseStart_6938584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6938584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6938584 prefixEnd_6938584 := by exact prefixLift 6938584
  have htrace : WordTrace (prefixWord ++ tailWord_6938584) baseStart_6938584 baseEnd_6938584 := by
    simpa [prefixWord, tailWord_6938584, baseEnd_6938584] using wordTrace_append hprefix tailTrace_6938584
  have hstable : (prefixWord ++ tailWord_6938584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6938584).length < 2 ^ (prefixWord ++ tailWord_6938584).sum := by decide
  have hdescent : baseEnd_6938584 < baseStart_6938584 := by decide
  rcases family_descends (prefixWord ++ tailWord_6938584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6938591 : List Nat := [1, 1, 2, 3, 4, 1, 2, 3, 2, 1, 3]
def baseStart_6938591 : Nat := 118140960795 + 6938591 * 2 ^ 59
def prefixEnd_6938591 : Nat := 4983230072969 + 3 ^ 40 * 6938591 * 2
def baseEnd_6938591 : Nat := 3562832247960767464502507

theorem tailTrace_6938591 : CollatzResearch.WordTrace tailWord_6938591 prefixEnd_6938591 3562832247960767464502507 := by
  unfold tailWord_6938591
  simp only [CollatzResearch.WordTrace]
  refine ⟨253071204405677298843887627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168714136270451532562591751 253071204405677298843887627)
  ·
    refine ⟨379606806608515948265831441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253071204405677298843887627 379606806608515948265831441)
    ·
      refine ⟨284705104956386961199373581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 379606806608515948265831441 284705104956386961199373581)
      ·
        refine ⟨106764414358645110449765093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 284705104956386961199373581 106764414358645110449765093)
        ·
          refine ⟨20018327692245958209330955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 106764414358645110449765093 20018327692245958209330955)
          ·
            refine ⟨30027491538368937313996433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20018327692245958209330955 30027491538368937313996433)
            ·
              refine ⟨22520618653776702985497325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30027491538368937313996433 22520618653776702985497325)
              ·
                refine ⟨8445231995166263619561497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22520618653776702985497325 8445231995166263619561497)
                ·
                  refine ⟨6333923996374697714671123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8445231995166263619561497 6333923996374697714671123)
                  ·
                    refine ⟨9500885994562046572006685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6333923996374697714671123 9500885994562046572006685)
                    ·
                      refine ⟨3562832247960767464502507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9500885994562046572006685 3562832247960767464502507)
                      ·
                        rfl

theorem cell23_6938591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 3, 2, 1, 3].length) (baseStart_6938591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6938591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6938591 prefixEnd_6938591 := by exact prefixLift 6938591
  have htrace : WordTrace (prefixWord ++ tailWord_6938591) baseStart_6938591 baseEnd_6938591 := by
    simpa [prefixWord, tailWord_6938591, baseEnd_6938591] using wordTrace_append hprefix tailTrace_6938591
  have hstable : (prefixWord ++ tailWord_6938591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6938591).length < 2 ^ (prefixWord ++ tailWord_6938591).sum := by decide
  have hdescent : baseEnd_6938591 < baseStart_6938591 := by decide
  rcases family_descends (prefixWord ++ tailWord_6938591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6938684 : List Nat := [2, 2, 2, 2, 2, 1, 3, 2, 2, 5]
def baseStart_6938684 : Nat := 118140960795 + 6938684 * 2 ^ 59
def prefixEnd_6938684 : Nat := 4983230072969 + 3 ^ 40 * 6938684 * 2
def baseEnd_6938684 : Nat := 1187626667220545200213193

theorem tailTrace_6938684 : CollatzResearch.WordTrace tailWord_6938684 prefixEnd_6938684 1187626667220545200213193 := by
  unfold tailWord_6938684
  simp only [CollatzResearch.WordTrace]
  refine ⟨126537298197170187863511553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168716397596226917151348737 126537298197170187863511553)
  ·
    refine ⟨94902973647877640897633665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126537298197170187863511553 94902973647877640897633665)
    ·
      refine ⟨71177230235908230673225249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94902973647877640897633665 71177230235908230673225249)
      ·
        refine ⟨53382922676931173004918937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71177230235908230673225249 53382922676931173004918937)
        ·
          refine ⟨40037192007698379753689203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53382922676931173004918937 40037192007698379753689203)
          ·
            refine ⟨60055788011547569630533805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40037192007698379753689203 60055788011547569630533805)
            ·
              refine ⟨22520920504330338611450177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60055788011547569630533805 22520920504330338611450177)
              ·
                refine ⟨16890690378247753958587633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22520920504330338611450177 16890690378247753958587633)
                ·
                  refine ⟨12668017783685815468940725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16890690378247753958587633 12668017783685815468940725)
                  ·
                    refine ⟨1187626667220545200213193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12668017783685815468940725 1187626667220545200213193)
                    ·
                      rfl

theorem cell23_6938684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 2, 2, 5].length) (baseStart_6938684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6938684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6938684 prefixEnd_6938684 := by exact prefixLift 6938684
  have htrace : WordTrace (prefixWord ++ tailWord_6938684) baseStart_6938684 baseEnd_6938684 := by
    simpa [prefixWord, tailWord_6938684, baseEnd_6938684] using wordTrace_append hprefix tailTrace_6938684
  have hstable : (prefixWord ++ tailWord_6938684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6938684).length < 2 ^ (prefixWord ++ tailWord_6938684).sum := by decide
  have hdescent : baseEnd_6938684 < baseStart_6938684 := by decide
  rcases family_descends (prefixWord ++ tailWord_6938684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6938714 : List Nat := [3, 1, 1, 2, 1, 1, 4, 1, 5, 4]
def baseStart_6938714 : Nat := 118140960795 + 6938714 * 2 ^ 59
def prefixEnd_6938714 : Nat := 4983230072969 + 3 ^ 40 * 6938714 * 2
def baseEnd_6938714 : Nat := 1187631802027090161088147

theorem tailTrace_6938714 : CollatzResearch.WordTrace tailWord_6938714 prefixEnd_6938714 1187631802027090161088147 := by
  unfold tailWord_6938714
  simp only [CollatzResearch.WordTrace]
  refine ⟨63268922646057922712653799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168717127056154460567076797 63268922646057922712653799)
  ·
    refine ⟨94903383969086884068980699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63268922646057922712653799 94903383969086884068980699)
    ·
      refine ⟨142355075953630326103471049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94903383969086884068980699 142355075953630326103471049)
      ·
        refine ⟨106766306965222744577603287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142355075953630326103471049 106766306965222744577603287)
        ·
          refine ⟨160149460447834116866404931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106766306965222744577603287 160149460447834116866404931)
          ·
            refine ⟨240224190671751175299607397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160149460447834116866404931 240224190671751175299607397)
            ·
              refine ⟨45042035750953345368676387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 240224190671751175299607397 45042035750953345368676387)
              ·
                refine ⟨67563053626430018053014581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45042035750953345368676387 67563053626430018053014581)
                ·
                  refine ⟨6334036277477814192470117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67563053626430018053014581 6334036277477814192470117)
                  ·
                    refine ⟨1187631802027090161088147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6334036277477814192470117 1187631802027090161088147)
                    ·
                      rfl

theorem cell23_6938714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 1, 5, 4].length) (baseStart_6938714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6938714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6938714 prefixEnd_6938714 := by exact prefixLift 6938714
  have htrace : WordTrace (prefixWord ++ tailWord_6938714) baseStart_6938714 baseEnd_6938714 := by
    simpa [prefixWord, tailWord_6938714, baseEnd_6938714] using wordTrace_append hprefix tailTrace_6938714
  have hstable : (prefixWord ++ tailWord_6938714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6938714).length < 2 ^ (prefixWord ++ tailWord_6938714).sum := by decide
  have hdescent : baseEnd_6938714 < baseStart_6938714 := by decide
  rcases family_descends (prefixWord ++ tailWord_6938714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6938724 : List Nat := [2, 3, 1, 1, 2, 1, 2, 3, 1, 4, 3]
def baseStart_6938724 : Nat := 118140960795 + 6938724 * 2 ^ 59
def prefixEnd_6938724 : Nat := 4983230072969 + 3 ^ 40 * 6938724 * 2
def baseEnd_6938724 : Nat := 3562900540887815444139395

theorem tailTrace_6938724 : CollatzResearch.WordTrace tailWord_6938724 prefixEnd_6938724 3562900540887815444139395 := by
  unfold tailWord_6938724
  simp only [CollatzResearch.WordTrace]
  refine ⟨126538027657097731279239613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168717370209463641705652817 126538027657097731279239613)
  ·
    refine ⟨47451760371411649229714855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126538027657097731279239613 47451760371411649229714855)
    ·
      refine ⟨71177640557117473844572283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47451760371411649229714855 71177640557117473844572283)
      ·
        refine ⟨106766460835676210766858425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71177640557117473844572283 106766460835676210766858425)
        ·
          refine ⟨80074845626757158075143819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106766460835676210766858425 80074845626757158075143819)
          ·
            refine ⟨120112268440135737112715729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80074845626757158075143819 120112268440135737112715729)
            ·
              refine ⟨90084201330101802834536797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120112268440135737112715729 90084201330101802834536797)
              ·
                refine ⟨33781575498788176062951299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90084201330101802834536797 33781575498788176062951299)
                ·
                  refine ⟨50672363248182264094426949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33781575498788176062951299 50672363248182264094426949)
                  ·
                    refine ⟨9501068109034174517705053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50672363248182264094426949 9501068109034174517705053)
                    ·
                      refine ⟨3562900540887815444139395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9501068109034174517705053 3562900540887815444139395)
                      ·
                        rfl

theorem cell23_6938724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 3, 1, 4, 3].length) (baseStart_6938724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6938724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6938724 prefixEnd_6938724 := by exact prefixLift 6938724
  have htrace : WordTrace (prefixWord ++ tailWord_6938724) baseStart_6938724 baseEnd_6938724 := by
    simpa [prefixWord, tailWord_6938724, baseEnd_6938724] using wordTrace_append hprefix tailTrace_6938724
  have hstable : (prefixWord ++ tailWord_6938724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6938724).length < 2 ^ (prefixWord ++ tailWord_6938724).sum := by decide
  have hdescent : baseEnd_6938724 < baseStart_6938724 := by decide
  rcases family_descends (prefixWord ++ tailWord_6938724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6938734 : List Nat := [4, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6]
def baseStart_6938734 : Nat := 118140960795 + 6938734 * 2 ^ 59
def prefixEnd_6938734 : Nat := 4983230072969 + 3 ^ 40 * 6938734 * 2
def baseEnd_6938734 : Nat := 3562905675694360405014349

theorem tailTrace_6938734 : CollatzResearch.WordTrace tailWord_6938734 prefixEnd_6938734 3562905675694360405014349 := by
  unfold tailWord_6938734
  simp only [CollatzResearch.WordTrace]
  refine ⟨31634552505519904283292907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168717613362772822844228837 31634552505519904283292907)
  ·
    refine ⟨47451828758279856424939361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31634552505519904283292907 47451828758279856424939361)
    ·
      refine ⟨35588871568709892318704521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47451828758279856424939361 35588871568709892318704521)
      ·
        refine ⟨26691653676532419239028391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35588871568709892318704521 26691653676532419239028391)
        ·
          refine ⟨40037480514798628858542587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26691653676532419239028391 40037480514798628858542587)
          ·
            refine ⟨60056220772197943287813881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40037480514798628858542587 60056220772197943287813881)
            ·
              refine ⟨45042165579148457465860411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60056220772197943287813881 45042165579148457465860411)
              ·
                refine ⟨67563248368722686198790617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45042165579148457465860411 67563248368722686198790617)
                ·
                  refine ⟨50672436276542014649092963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67563248368722686198790617 50672436276542014649092963)
                  ·
                    refine ⟨76008654414813021973639445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50672436276542014649092963 76008654414813021973639445)
                    ·
                      refine ⟨3562905675694360405014349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76008654414813021973639445 3562905675694360405014349)
                      ·
                        rfl

theorem cell23_6938734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_6938734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6938734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6938734 prefixEnd_6938734 := by exact prefixLift 6938734
  have htrace : WordTrace (prefixWord ++ tailWord_6938734) baseStart_6938734 baseEnd_6938734 := by
    simpa [prefixWord, tailWord_6938734, baseEnd_6938734] using wordTrace_append hprefix tailTrace_6938734
  have hstable : (prefixWord ++ tailWord_6938734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6938734).length < 2 ^ (prefixWord ++ tailWord_6938734).sum := by decide
  have hdescent : baseEnd_6938734 < baseStart_6938734 := by decide
  rcases family_descends (prefixWord ++ tailWord_6938734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6938748 : List Nat := [2, 2, 2, 1, 1, 5, 1, 4, 1, 4]
def baseStart_6938748 : Nat := 118140960795 + 6938748 * 2 ^ 59
def prefixEnd_6938748 : Nat := 4983230072969 + 3 ^ 40 * 6938748 * 2
def baseEnd_6938748 : Nat := 1187637621474507783413095

theorem tailTrace_6938748 : CollatzResearch.WordTrace tailWord_6938748 prefixEnd_6938748 1187637621474507783413095 := by
  unfold tailWord_6938748
  simp only [CollatzResearch.WordTrace]
  refine ⟨126538465333054257328676449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168717953777405676438235265 126538465333054257328676449)
  ·
    refine ⟨94903848999790692996507337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126538465333054257328676449 94903848999790692996507337)
    ·
      refine ⟨71177886749843019747380503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94903848999790692996507337 71177886749843019747380503)
      ·
        refine ⟨106766830124764529621070755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71177886749843019747380503 106766830124764529621070755)
        ·
          refine ⟨160150245187146794431606133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106766830124764529621070755 160150245187146794431606133)
          ·
            refine ⟨15014085486295011977963075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 160150245187146794431606133 15014085486295011977963075)
            ·
              refine ⟨22521128229442517966944613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15014085486295011977963075 22521128229442517966944613)
              ·
                refine ⟨4222711543020472118802115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22521128229442517966944613 4222711543020472118802115)
                ·
                  refine ⟨6334067314530708178203173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4222711543020472118802115 6334067314530708178203173)
                  ·
                    refine ⟨1187637621474507783413095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6334067314530708178203173 1187637621474507783413095)
                    ·
                      rfl

theorem cell23_6938748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 4, 1, 4].length) (baseStart_6938748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6938748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6938748 prefixEnd_6938748 := by exact prefixLift 6938748
  have htrace : WordTrace (prefixWord ++ tailWord_6938748) baseStart_6938748 baseEnd_6938748 := by
    simpa [prefixWord, tailWord_6938748, baseEnd_6938748] using wordTrace_append hprefix tailTrace_6938748
  have hstable : (prefixWord ++ tailWord_6938748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6938748).length < 2 ^ (prefixWord ++ tailWord_6938748).sum := by decide
  have hdescent : baseEnd_6938748 < baseStart_6938748 := by decide
  rcases family_descends (prefixWord ++ tailWord_6938748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6938772 : List Nat := [2, 4, 2, 3, 2, 1, 1, 1, 2, 1, 4]
def baseStart_6938772 : Nat := 118140960795 + 6938772 * 2 ^ 59
def prefixEnd_6938772 : Nat := 4983230072969 + 3 ^ 40 * 6938772 * 2
def baseEnd_6938772 : Nat := 3562925187959231256339175

theorem tailTrace_6938772 : CollatzResearch.WordTrace tailWord_6938772 prefixEnd_6938772 3562925187959231256339175 := by
  unfold tailWord_6938772
  simp only [CollatzResearch.WordTrace]
  refine ⟨126538903009010783378113285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168718537345347711170817713 126538903009010783378113285)
  ·
    refine ⟨23726044314189521883396241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126538903009010783378113285 23726044314189521883396241)
    ·
      refine ⟨17794533235642141412547181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23726044314189521883396241 17794533235642141412547181)
      ·
        refine ⟨6672949963365803029705193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17794533235642141412547181 6672949963365803029705193)
        ·
          refine ⟨5004712472524352272278895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6672949963365803029705193 5004712472524352272278895)
          ·
            refine ⟨7507068708786528408418343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5004712472524352272278895 7507068708786528408418343)
            ·
              refine ⟨11260603063179792612627515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7507068708786528408418343 11260603063179792612627515)
              ·
                refine ⟨16890904594769688918941273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11260603063179792612627515 16890904594769688918941273)
                ·
                  refine ⟨12668178446077266689205955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16890904594769688918941273 12668178446077266689205955)
                  ·
                    refine ⟨19002267669115900033808933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12668178446077266689205955 19002267669115900033808933)
                    ·
                      refine ⟨3562925187959231256339175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19002267669115900033808933 3562925187959231256339175)
                      ·
                        rfl

theorem cell23_6938772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_6938772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6938772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6938772 prefixEnd_6938772 := by exact prefixLift 6938772
  have htrace : WordTrace (prefixWord ++ tailWord_6938772) baseStart_6938772 baseEnd_6938772 := by
    simpa [prefixWord, tailWord_6938772, baseEnd_6938772] using wordTrace_append hprefix tailTrace_6938772
  have hstable : (prefixWord ++ tailWord_6938772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6938772).length < 2 ^ (prefixWord ++ tailWord_6938772).sum := by decide
  have hdescent : baseEnd_6938772 < baseStart_6938772 := by decide
  rcases family_descends (prefixWord ++ tailWord_6938772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6938775 : List Nat := [1, 1, 3, 3, 5, 1, 1, 1, 2, 2, 3]
def baseStart_6938775 : Nat := 118140960795 + 6938775 * 2 ^ 59
def prefixEnd_6938775 : Nat := 4983230072969 + 3 ^ 40 * 6938775 * 2
def baseEnd_6938775 : Nat := 3562926728401194744601661

theorem tailTrace_6938775 : CollatzResearch.WordTrace tailWord_6938775 prefixEnd_6938775 3562926728401194744601661 := by
  unfold tailWord_6938775
  simp only [CollatzResearch.WordTrace]
  refine ⟨253077915437010698268585779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168718610291340465512390519 253077915437010698268585779)
  ·
    refine ⟨379616873155516047402878669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253077915437010698268585779 379616873155516047402878669)
    ·
      refine ⟨142356327433318517776079501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 379616873155516047402878669 142356327433318517776079501)
      ·
        refine ⟨53383622787494444166029813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142356327433318517776079501 53383622787494444166029813)
        ·
          refine ⟨5004714636327604140565295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 53383622787494444166029813 5004714636327604140565295)
          ·
            refine ⟨7507071954491406210847943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5004714636327604140565295 7507071954491406210847943)
            ·
              refine ⟨11260607931737109316271915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7507071954491406210847943 11260607931737109316271915)
              ·
                refine ⟨16890911897605663974407873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11260607931737109316271915 16890911897605663974407873)
                ·
                  refine ⟨12668183923204247980805905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16890911897605663974407873 12668183923204247980805905)
                  ·
                    refine ⟨9501137942403185985604429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12668183923204247980805905 9501137942403185985604429)
                    ·
                      refine ⟨3562926728401194744601661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9501137942403185985604429 3562926728401194744601661)
                      ·
                        rfl

theorem cell23_6938775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 1, 1, 2, 2, 3].length) (baseStart_6938775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6938775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6938775 prefixEnd_6938775 := by exact prefixLift 6938775
  have htrace : WordTrace (prefixWord ++ tailWord_6938775) baseStart_6938775 baseEnd_6938775 := by
    simpa [prefixWord, tailWord_6938775, baseEnd_6938775] using wordTrace_append hprefix tailTrace_6938775
  have hstable : (prefixWord ++ tailWord_6938775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6938775).length < 2 ^ (prefixWord ++ tailWord_6938775).sum := by decide
  have hdescent : baseEnd_6938775 < baseStart_6938775 := by decide
  rcases family_descends (prefixWord ++ tailWord_6938775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6938782 : List Nat := [4, 3, 1, 1, 3, 1, 2, 3, 1, 4]
def baseStart_6938782 : Nat := 118140960795 + 6938782 * 2 ^ 59
def prefixEnd_6938782 : Nat := 4983230072969 + 3 ^ 40 * 6938782 * 2
def baseEnd_6938782 : Nat := 1187643440921925405738043

theorem tailTrace_6938782 : CollatzResearch.WordTrace tailWord_6938782 prefixEnd_6938782 1187643440921925405738043 := by
  unfold tailWord_6938782
  simp only [CollatzResearch.WordTrace]
  refine ⟨31634771343498167308011325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168718780498656892309393733 31634771343498167308011325)
  ·
    refine ⟨11863039253811812740504247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31634771343498167308011325 11863039253811812740504247)
    ·
      refine ⟨17794558880717719110756371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11863039253811812740504247 17794558880717719110756371)
      ·
        refine ⟨26691838321076578666134557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17794558880717719110756371 26691838321076578666134557)
        ·
          refine ⟨10009439370403716999800459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26691838321076578666134557 10009439370403716999800459)
          ·
            refine ⟨15014159055605575499700689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10009439370403716999800459 15014159055605575499700689)
            ·
              refine ⟨11260619291704181624775517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15014159055605575499700689 11260619291704181624775517)
              ·
                refine ⟨4222732234389068109290819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11260619291704181624775517 4222732234389068109290819)
                ·
                  refine ⟨6334098351583602163936229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4222732234389068109290819 6334098351583602163936229)
                  ·
                    refine ⟨1187643440921925405738043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6334098351583602163936229 1187643440921925405738043)
                    ·
                      rfl

theorem cell23_6938782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 2, 3, 1, 4].length) (baseStart_6938782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6938782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6938782 prefixEnd_6938782 := by exact prefixLift 6938782
  have htrace : WordTrace (prefixWord ++ tailWord_6938782) baseStart_6938782 baseEnd_6938782 := by
    simpa [prefixWord, tailWord_6938782, baseEnd_6938782] using wordTrace_append hprefix tailTrace_6938782
  have hstable : (prefixWord ++ tailWord_6938782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6938782).length < 2 ^ (prefixWord ++ tailWord_6938782).sum := by decide
  have hdescent : baseEnd_6938782 < baseStart_6938782 := by decide
  rcases family_descends (prefixWord ++ tailWord_6938782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6938821 : List Nat := [1, 3, 1, 1, 1, 1, 4, 5, 2, 4]
def baseStart_6938821 : Nat := 118140960795 + 6938821 * 2 ^ 59
def prefixEnd_6938821 : Nat := 4983230072969 + 3 ^ 40 * 6938821 * 2
def baseEnd_6938821 : Nat := 1187650116170433854875483

theorem tailTrace_6938821 : CollatzResearch.WordTrace tailWord_6938821 prefixEnd_6938821 1187650116170433854875483 := by
  unfold tailWord_6938821
  simp only [CollatzResearch.WordTrace]
  refine ⟨253079593194844048124760317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168719728796562698749840211 253079593194844048124760317)
  ·
    refine ⟨94904847448066518046785119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 253079593194844048124760317 94904847448066518046785119)
    ·
      refine ⟨142357271172099777070177679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94904847448066518046785119 142357271172099777070177679)
      ·
        refine ⟨213535906758149665605266519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142357271172099777070177679 213535906758149665605266519)
        ·
          refine ⟨320303860137224498407899779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213535906758149665605266519 320303860137224498407899779)
          ·
            refine ⟨480455790205836747611849669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 320303860137224498407899779 480455790205836747611849669)
            ·
              refine ⟨90085460663594390177221813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 480455790205836747611849669 90085460663594390177221813)
              ·
                refine ⟨8445511937211974079114545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 90085460663594390177221813 8445511937211974079114545)
                ·
                  refine ⟨6334133952908980559335909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8445511937211974079114545 6334133952908980559335909)
                  ·
                    refine ⟨1187650116170433854875483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6334133952908980559335909 1187650116170433854875483)
                    ·
                      rfl

theorem cell23_6938821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 5, 2, 4].length) (baseStart_6938821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6938821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6938821 prefixEnd_6938821 := by exact prefixLift 6938821
  have htrace : WordTrace (prefixWord ++ tailWord_6938821) baseStart_6938821 baseEnd_6938821 := by
    simpa [prefixWord, tailWord_6938821, baseEnd_6938821] using wordTrace_append hprefix tailTrace_6938821
  have hstable : (prefixWord ++ tailWord_6938821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6938821).length < 2 ^ (prefixWord ++ tailWord_6938821).sum := by decide
  have hdescent : baseEnd_6938821 < baseStart_6938821 := by decide
  rcases family_descends (prefixWord ++ tailWord_6938821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6938878 : List Nat := [4, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3]
def baseStart_6938878 : Nat := 118140960795 + 6938878 * 2 ^ 59
def prefixEnd_6938878 : Nat := 4983230072969 + 3 ^ 40 * 6938878 * 2
def baseEnd_6938878 : Nat := 3562979616908607841613687

theorem tailTrace_6938878 : CollatzResearch.WordTrace tailWord_6938878 prefixEnd_6938878 3562979616908607841613687 := by
  unfold tailWord_6938878
  simp only [CollatzResearch.WordTrace]
  refine ⟨31635209019454693357448161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168721114770425031239723525 31635209019454693357448161)
  ·
    refine ⟨23726406764591020018086121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31635209019454693357448161 23726406764591020018086121)
    ·
      refine ⟨17794805073443265013564591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23726406764591020018086121 17794805073443265013564591)
      ·
        refine ⟨26692207610164897520346887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17794805073443265013564591 26692207610164897520346887)
        ·
          refine ⟨40038311415247346280520331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26692207610164897520346887 40038311415247346280520331)
          ·
            refine ⟨60057467122871019420780497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40038311415247346280520331 60057467122871019420780497)
            ·
              refine ⟨45043100342153264565585373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60057467122871019420780497 45043100342153264565585373)
              ·
                refine ⟨16891162628307474212094515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45043100342153264565585373 16891162628307474212094515)
                ·
                  refine ⟨25336743942461211318141773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16891162628307474212094515 25336743942461211318141773)
                  ·
                    refine ⟨9501278978422954244303165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25336743942461211318141773 9501278978422954244303165)
                    ·
                      refine ⟨3562979616908607841613687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9501278978422954244303165 3562979616908607841613687)
                      ·
                        rfl

theorem cell23_6938878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3].length) (baseStart_6938878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6938878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6938878 prefixEnd_6938878 := by exact prefixLift 6938878
  have htrace : WordTrace (prefixWord ++ tailWord_6938878) baseStart_6938878 baseEnd_6938878 := by
    simpa [prefixWord, tailWord_6938878, baseEnd_6938878] using wordTrace_append hprefix tailTrace_6938878
  have hstable : (prefixWord ++ tailWord_6938878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6938878).length < 2 ^ (prefixWord ++ tailWord_6938878).sum := by decide
  have hdescent : baseEnd_6938878 < baseStart_6938878 := by decide
  rcases family_descends (prefixWord ++ tailWord_6938878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6938882 : List Nat := [3, 4, 1, 1, 2, 3, 1, 2, 1, 2, 3]
def baseStart_6938882 : Nat := 118140960795 + 6938882 * 2 ^ 59
def prefixEnd_6938882 : Nat := 4983230072969 + 3 ^ 40 * 6938882 * 2
def baseEnd_6938882 : Nat := 3562981670831225825963669

theorem tailTrace_6938882 : CollatzResearch.WordTrace tailWord_6938882 prefixEnd_6938882 3562981670831225825963669 := by
  unfold tailWord_6938882
  simp only [CollatzResearch.WordTrace]
  refine ⟨63270454511905763885682725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168721212031748703695153933 63270454511905763885682725)
  ·
    refine ⟨11863210220982330728565511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63270454511905763885682725 11863210220982330728565511)
    ·
      refine ⟨17794815331473496092848267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11863210220982330728565511 17794815331473496092848267)
      ·
        refine ⟨26692222997210244139272401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17794815331473496092848267 26692222997210244139272401)
        ·
          refine ⟨20019167247907683104454301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26692222997210244139272401 20019167247907683104454301)
          ·
            refine ⟨7507187717965381164170363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20019167247907683104454301 7507187717965381164170363)
            ·
              refine ⟨11260781576948071746255545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7507187717965381164170363 11260781576948071746255545)
              ·
                refine ⟨8445586182711053809691659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11260781576948071746255545 8445586182711053809691659)
                ·
                  refine ⟨12668379274066580714537489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8445586182711053809691659 12668379274066580714537489)
                  ·
                    refine ⟨9501284455549935535903117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12668379274066580714537489 9501284455549935535903117)
                    ·
                      refine ⟨3562981670831225825963669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9501284455549935535903117 3562981670831225825963669)
                      ·
                        rfl

theorem cell23_6938882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 1, 2, 1, 2, 3].length) (baseStart_6938882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6938882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6938882 prefixEnd_6938882 := by exact prefixLift 6938882
  have htrace : WordTrace (prefixWord ++ tailWord_6938882) baseStart_6938882 baseEnd_6938882 := by
    simpa [prefixWord, tailWord_6938882, baseEnd_6938882] using wordTrace_append hprefix tailTrace_6938882
  have hstable : (prefixWord ++ tailWord_6938882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6938882).length < 2 ^ (prefixWord ++ tailWord_6938882).sum := by decide
  have hdescent : baseEnd_6938882 < baseStart_6938882 := by decide
  rcases family_descends (prefixWord ++ tailWord_6938882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6938931 : List Nat := [1, 1, 1, 2, 5, 1, 3, 1, 2, 2, 4]
def baseStart_6938931 : Nat := 118140960795 + 6938931 * 2 ^ 59
def prefixEnd_6938931 : Nat := 4983230072969 + 3 ^ 40 * 6938931 * 2
def baseEnd_6938931 : Nat := 3563006831383296134250943

theorem tailTrace_6938931 : CollatzResearch.WordTrace tailWord_6938931 prefixEnd_6938931 3563006831383296134250943 := by
  unfold tailWord_6938931
  simp only [CollatzResearch.WordTrace]
  refine ⟨253083605224445536911264647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168722403482963691274176431 253083605224445536911264647)
  ·
    refine ⟨379625407836668305366896971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253083605224445536911264647 379625407836668305366896971)
    ·
      refine ⟨569438111755002458050345457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379625407836668305366896971 569438111755002458050345457)
      ·
        refine ⟨427078583816251843537759093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 569438111755002458050345457 427078583816251843537759093)
        ·
          refine ⟨40038617232773610331664915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 427078583816251843537759093 40038617232773610331664915)
          ·
            refine ⟨60057925849160415497497373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40038617232773610331664915 60057925849160415497497373)
            ·
              refine ⟨22521722193435155811561515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60057925849160415497497373 22521722193435155811561515)
              ·
                refine ⟨33782583290152733717342273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22521722193435155811561515 33782583290152733717342273)
                ·
                  refine ⟨25336937467614550288006705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33782583290152733717342273 25336937467614550288006705)
                  ·
                    refine ⟨19002703100710912716005029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25336937467614550288006705 19002703100710912716005029)
                    ·
                      refine ⟨3563006831383296134250943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19002703100710912716005029 3563006831383296134250943)
                      ·
                        rfl

theorem cell23_6938931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 1, 2, 2, 4].length) (baseStart_6938931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6938931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6938931 prefixEnd_6938931 := by exact prefixLift 6938931
  have htrace : WordTrace (prefixWord ++ tailWord_6938931) baseStart_6938931 baseEnd_6938931 := by
    simpa [prefixWord, tailWord_6938931, baseEnd_6938931] using wordTrace_append hprefix tailTrace_6938931
  have hstable : (prefixWord ++ tailWord_6938931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6938931).length < 2 ^ (prefixWord ++ tailWord_6938931).sum := by decide
  have hdescent : baseEnd_6938931 < baseStart_6938931 := by decide
  rcases family_descends (prefixWord ++ tailWord_6938931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6938951 : List Nat := [1, 1, 4, 1, 2, 2, 1, 2, 1, 5, 3]
def baseStart_6938951 : Nat := 118140960795 + 6938951 * 2 ^ 59
def prefixEnd_6938951 : Nat := 4983230072969 + 3 ^ 40 * 6938951 * 2
def baseEnd_6938951 : Nat := 3563017100996386056000851

theorem tailTrace_6938951 : CollatzResearch.WordTrace tailWord_6938951 prefixEnd_6938951 3563017100996386056000851 := by
  unfold tailWord_6938951
  simp only [CollatzResearch.WordTrace]
  refine ⟨253084334684373080326992707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168722889789582053551328471 253084334684373080326992707)
  ·
    refine ⟨379626502026559620490489061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253084334684373080326992707 379626502026559620490489061)
    ·
      refine ⟨71179969129979928841966699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 379626502026559620490489061 71179969129979928841966699)
      ·
        refine ⟨106769953694969893262950049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71179969129979928841966699 106769953694969893262950049)
        ·
          refine ⟨80077465271227419947212537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106769953694969893262950049 80077465271227419947212537)
          ·
            refine ⟨60058098953420564960409403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80077465271227419947212537 60058098953420564960409403)
            ·
              refine ⟨90087148430130847440614105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60058098953420564960409403 90087148430130847440614105)
              ·
                refine ⟨67565361322598135580460579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90087148430130847440614105 67565361322598135580460579)
                ·
                  refine ⟨101348041983897203370690869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67565361322598135580460579 101348041983897203370690869)
                  ·
                    refine ⟨9501378935990362816002269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 101348041983897203370690869 9501378935990362816002269)
                    ·
                      refine ⟨3563017100996386056000851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9501378935990362816002269 3563017100996386056000851)
                      ·
                        rfl

theorem cell23_6938951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 2, 1, 5, 3].length) (baseStart_6938951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6938951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6938951 prefixEnd_6938951 := by exact prefixLift 6938951
  have htrace : WordTrace (prefixWord ++ tailWord_6938951) baseStart_6938951 baseEnd_6938951 := by
    simpa [prefixWord, tailWord_6938951, baseEnd_6938951] using wordTrace_append hprefix tailTrace_6938951
  have hstable : (prefixWord ++ tailWord_6938951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6938951).length < 2 ^ (prefixWord ++ tailWord_6938951).sum := by decide
  have hdescent : baseEnd_6938951 < baseStart_6938951 := by decide
  rcases family_descends (prefixWord ++ tailWord_6938951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6938991 : List Nat := [1, 1, 2, 1, 3, 1, 2, 1, 6, 1, 4]
def baseStart_6938991 : Nat := 118140960795 + 6938991 * 2 ^ 59
def prefixEnd_6938991 : Nat := 4983230072969 + 3 ^ 40 * 6938991 * 2
def baseEnd_6938991 : Nat := 3563037640222565899500667

theorem tailTrace_6938991 : CollatzResearch.WordTrace tailWord_6938991 prefixEnd_6938991 3563037640222565899500667 := by
  unfold tailWord_6938991
  simp only [CollatzResearch.WordTrace]
  refine ⟨253085793604228167158448827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168723862402818778105632551 253085793604228167158448827)
  ·
    refine ⟨379628690406342250737673241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253085793604228167158448827 379628690406342250737673241)
    ·
      refine ⟨284721517804756688053254931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 379628690406342250737673241 284721517804756688053254931)
      ·
        refine ⟨427082276707135032079882397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284721517804756688053254931 427082276707135032079882397)
        ·
          refine ⟨160155853765175637029955899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 427082276707135032079882397 160155853765175637029955899)
          ·
            refine ⟨240233780647763455544933849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160155853765175637029955899 240233780647763455544933849)
            ·
              refine ⟨180175335485822591658700387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 240233780647763455544933849 180175335485822591658700387)
              ·
                refine ⟨270263003228733887488050581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 180175335485822591658700387 270263003228733887488050581)
                ·
                  refine ⟨12668578276346900976002371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 270263003228733887488050581 12668578276346900976002371)
                  ·
                    refine ⟨19002867414520351464003557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12668578276346900976002371 19002867414520351464003557)
                    ·
                      refine ⟨3563037640222565899500667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19002867414520351464003557 3563037640222565899500667)
                      ·
                        rfl

theorem cell23_6938991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 6, 1, 4].length) (baseStart_6938991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6938991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6938991 prefixEnd_6938991 := by exact prefixLift 6938991
  have htrace : WordTrace (prefixWord ++ tailWord_6938991) baseStart_6938991 baseEnd_6938991 := by
    simpa [prefixWord, tailWord_6938991, baseEnd_6938991] using wordTrace_append hprefix tailTrace_6938991
  have hstable : (prefixWord ++ tailWord_6938991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6938991).length < 2 ^ (prefixWord ++ tailWord_6938991).sum := by decide
  have hdescent : baseEnd_6938991 < baseStart_6938991 := by decide
  rcases family_descends (prefixWord ++ tailWord_6938991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6939031 : List Nat := [1, 1, 3, 3, 1, 1, 4, 1, 8]
def baseStart_6939031 : Nat := 118140960795 + 6939031 * 2 ^ 59
def prefixEnd_6939031 : Nat := 4983230072969 + 3 ^ 40 * 6939031 * 2
def baseEnd_6939031 : Nat := 395895353272082860333387

theorem tailTrace_6939031 : CollatzResearch.WordTrace tailWord_6939031 prefixEnd_6939031 395895353272082860333387 := by
  unfold tailWord_6939031
  simp only [CollatzResearch.WordTrace]
  refine ⟨253087252524083253989904947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168724835016055502659936631 253087252524083253989904947)
  ·
    refine ⟨379630878786124880984857421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253087252524083253989904947 379630878786124880984857421)
    ·
      refine ⟨142361579544796830369321533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 379630878786124880984857421 142361579544796830369321533)
      ·
        refine ⟨53385592329298811388495575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142361579544796830369321533 53385592329298811388495575)
        ·
          refine ⟨80078388493948217082743363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53385592329298811388495575 80078388493948217082743363)
          ·
            refine ⟨120117582740922325624115045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80078388493948217082743363 120117582740922325624115045)
            ·
              refine ⟨22522046763922936054521571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 120117582740922325624115045 22522046763922936054521571)
              ·
                refine ⟨33783070145884404081782357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22522046763922936054521571 33783070145884404081782357)
                ·
                  refine ⟨395895353272082860333387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33783070145884404081782357 395895353272082860333387)
                  ·
                    rfl

theorem cell23_6939031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 1, 8].length) (baseStart_6939031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6939031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6939031 prefixEnd_6939031 := by exact prefixLift 6939031
  have htrace : WordTrace (prefixWord ++ tailWord_6939031) baseStart_6939031 baseEnd_6939031 := by
    simpa [prefixWord, tailWord_6939031, baseEnd_6939031] using wordTrace_append hprefix tailTrace_6939031
  have hstable : (prefixWord ++ tailWord_6939031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6939031).length < 2 ^ (prefixWord ++ tailWord_6939031).sum := by decide
  have hdescent : baseEnd_6939031 < baseStart_6939031 := by decide
  rcases family_descends (prefixWord ++ tailWord_6939031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6939098 : List Nat := [3, 1, 1, 2, 3, 1, 1, 1, 5, 1, 4]
def baseStart_6939098 : Nat := 118140960795 + 6939098 * 2 ^ 59
def prefixEnd_6939098 : Nat := 4983230072969 + 3 ^ 40 * 6939098 * 2
def baseEnd_6939098 : Nat := 3563092582652596980862675

theorem tailTrace_6939098 : CollatzResearch.WordTrace tailWord_6939098 prefixEnd_6939098 3563092582652596980862675 := by
  unfold tailWord_6939098
  simp only [CollatzResearch.WordTrace]
  refine ⟨63272424053710131108148487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168726464143227016288395965 63272424053710131108148487)
  ·
    refine ⟨94908636080565196662222731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63272424053710131108148487 94908636080565196662222731)
    ·
      refine ⟨142362954120847794993334097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94908636080565196662222731 142362954120847794993334097)
      ·
        refine ⟨106772215590635846245000573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142362954120847794993334097 106772215590635846245000573)
        ·
          refine ⟨40039580846488442341875215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106772215590635846245000573 40039580846488442341875215)
          ·
            refine ⟨60059371269732663512812823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40039580846488442341875215 60059371269732663512812823)
            ·
              refine ⟨90089056904598995269219235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60059371269732663512812823 90089056904598995269219235)
              ·
                refine ⟨135133585356898492903828853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90089056904598995269219235 135133585356898492903828853)
                ·
                  refine ⟨12668773627209233709733955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 135133585356898492903828853 12668773627209233709733955)
                  ·
                    refine ⟨19003160440813850564600933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12668773627209233709733955 19003160440813850564600933)
                    ·
                      refine ⟨3563092582652596980862675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19003160440813850564600933 3563092582652596980862675)
                      ·
                        rfl

theorem cell23_6939098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 5, 1, 4].length) (baseStart_6939098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6939098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6939098 prefixEnd_6939098 := by exact prefixLift 6939098
  have htrace : WordTrace (prefixWord ++ tailWord_6939098) baseStart_6939098 baseEnd_6939098 := by
    simpa [prefixWord, tailWord_6939098, baseEnd_6939098] using wordTrace_append hprefix tailTrace_6939098
  have hstable : (prefixWord ++ tailWord_6939098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6939098).length < 2 ^ (prefixWord ++ tailWord_6939098).sum := by decide
  have hdescent : baseEnd_6939098 < baseStart_6939098 := by decide
  rcases family_descends (prefixWord ++ tailWord_6939098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6939108 : List Nat := [2, 3, 1, 1, 1, 1, 1, 1, 8, 4]
def baseStart_6939108 : Nat := 118140960795 + 6939108 * 2 ^ 59
def prefixEnd_6939108 : Nat := 4983230072969 + 3 ^ 40 * 6939108 * 2
def baseEnd_6939108 : Nat := 1187699239153047313912543

theorem tailTrace_6939108 : CollatzResearch.WordTrace tailWord_6939108 prefixEnd_6939108 1187699239153047313912543 := by
  unfold tailWord_6939108
  simp only [CollatzResearch.WordTrace]
  refine ⟨126545030472402148070228989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168726707296536197426971985 126545030472402148070228989)
  ·
    refine ⟨47454386427150805526335871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126545030472402148070228989 47454386427150805526335871)
    ·
      refine ⟨71181579640726208289503807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47454386427150805526335871 71181579640726208289503807)
      ·
        refine ⟨106772369461089312434255711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71181579640726208289503807 106772369461089312434255711)
        ·
          refine ⟨160158554191633968651383567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106772369461089312434255711 160158554191633968651383567)
          ·
            refine ⟨240237831287450952977075351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160158554191633968651383567 240237831287450952977075351)
            ·
              refine ⟨360356746931176429465613027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 240237831287450952977075351 360356746931176429465613027)
              ·
                refine ⟨540535120396764644198419541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 360356746931176429465613027 540535120396764644198419541)
                ·
                  refine ⟨6334395942149585674200229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 540535120396764644198419541 6334395942149585674200229)
                  ·
                    refine ⟨1187699239153047313912543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6334395942149585674200229 1187699239153047313912543)
                    ·
                      rfl

theorem cell23_6939108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 8, 4].length) (baseStart_6939108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6939108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6939108 prefixEnd_6939108 := by exact prefixLift 6939108
  have htrace : WordTrace (prefixWord ++ tailWord_6939108) baseStart_6939108 baseEnd_6939108 := by
    simpa [prefixWord, tailWord_6939108, baseEnd_6939108] using wordTrace_append hprefix tailTrace_6939108
  have hstable : (prefixWord ++ tailWord_6939108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6939108).length < 2 ^ (prefixWord ++ tailWord_6939108).sum := by decide
  have hdescent : baseEnd_6939108 < baseStart_6939108 := by decide
  rcases family_descends (prefixWord ++ tailWord_6939108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6939128 : List Nat := [2, 1, 2, 1, 1, 4, 1, 4, 1, 2, 4]
def baseStart_6939128 : Nat := 118140960795 + 6939128 * 2 ^ 59
def prefixEnd_6939128 : Nat := 4983230072969 + 3 ^ 40 * 6939128 * 2
def baseEnd_6939128 : Nat := 3563107987072231863487537

theorem tailTrace_6939128 : CollatzResearch.WordTrace tailWord_6939128 prefixEnd_6939128 3563107987072231863487537 := by
  unfold tailWord_6939128
  simp only [CollatzResearch.WordTrace]
  refine ⟨126545395202365919778093019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168727193603154559704124025 126545395202365919778093019)
  ·
    refine ⟨189818092803548879667139529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126545395202365919778093019 189818092803548879667139529)
    ·
      refine ⟨142363569602661659750354647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189818092803548879667139529 142363569602661659750354647)
      ·
        refine ⟨213545354403992489625531971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142363569602661659750354647 213545354403992489625531971)
        ·
          refine ⟨320318031605988734438297957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213545354403992489625531971 320318031605988734438297957)
          ·
            refine ⟨60059630926122887707180867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 320318031605988734438297957 60059630926122887707180867)
            ·
              refine ⟨90089446389184331560771301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60059630926122887707180867 90089446389184331560771301)
              ·
                refine ⟨16891771197972062167644619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90089446389184331560771301 16891771197972062167644619)
                ·
                  refine ⟨25337656796958093251466929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16891771197972062167644619 25337656796958093251466929)
                  ·
                    refine ⟨19003242597718569938600197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25337656796958093251466929 19003242597718569938600197)
                    ·
                      refine ⟨3563107987072231863487537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19003242597718569938600197 3563107987072231863487537)
                      ·
                        rfl

theorem cell23_6939128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 4, 1, 2, 4].length) (baseStart_6939128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6939128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6939128 prefixEnd_6939128 := by exact prefixLift 6939128
  have htrace : WordTrace (prefixWord ++ tailWord_6939128) baseStart_6939128 baseEnd_6939128 := by
    simpa [prefixWord, tailWord_6939128, baseEnd_6939128] using wordTrace_append hprefix tailTrace_6939128
  have hstable : (prefixWord ++ tailWord_6939128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6939128).length < 2 ^ (prefixWord ++ tailWord_6939128).sum := by decide
  have hdescent : baseEnd_6939128 < baseStart_6939128 := by decide
  rcases family_descends (prefixWord ++ tailWord_6939128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6939135 : List Nat := [1, 1, 2, 2, 1, 2, 5, 3, 1, 2, 3]
def baseStart_6939135 : Nat := 118140960795 + 6939135 * 2 ^ 59
def prefixEnd_6939135 : Nat := 4983230072969 + 3 ^ 40 * 6939135 * 2
def baseEnd_6939135 : Nat := 3563111581436813336100005

theorem tailTrace_6939135 : CollatzResearch.WordTrace tailWord_6939135 prefixEnd_6939135 3563111581436813336100005 := by
  unfold tailWord_6939135
  simp only [CollatzResearch.WordTrace]
  refine ⟨253091045715706479751690859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168727363810470986501127239 253091045715706479751690859)
  ·
    refine ⟨379636568573559719627536289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253091045715706479751690859 379636568573559719627536289)
    ·
      refine ⟨284727426430169789720652217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 379636568573559719627536289 284727426430169789720652217)
      ·
        refine ⟨213545569822627342290489163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 284727426430169789720652217 213545569822627342290489163)
        ·
          refine ⟨320318354733941013435733745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213545569822627342290489163 320318354733941013435733745)
          ·
            refine ⟨240238766050455760076800309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 320318354733941013435733745 240238766050455760076800309)
            ·
              refine ⟨22522384317230227507200029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 240238766050455760076800309 22522384317230227507200029)
              ·
                refine ⟨8445894118961335315200011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22522384317230227507200029 8445894118961335315200011)
                ·
                  refine ⟨12668841178442002972800017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8445894118961335315200011 12668841178442002972800017)
                  ·
                    refine ⟨9501630883831502229600013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12668841178442002972800017 9501630883831502229600013)
                    ·
                      refine ⟨3563111581436813336100005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9501630883831502229600013 3563111581436813336100005)
                      ·
                        rfl

theorem cell23_6939135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 3, 1, 2, 3].length) (baseStart_6939135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6939135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6939135 prefixEnd_6939135 := by exact prefixLift 6939135
  have htrace : WordTrace (prefixWord ++ tailWord_6939135) baseStart_6939135 baseEnd_6939135 := by
    simpa [prefixWord, tailWord_6939135, baseEnd_6939135] using wordTrace_append hprefix tailTrace_6939135
  have hstable : (prefixWord ++ tailWord_6939135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6939135).length < 2 ^ (prefixWord ++ tailWord_6939135).sum := by decide
  have hdescent : baseEnd_6939135 < baseStart_6939135 := by decide
  rcases family_descends (prefixWord ++ tailWord_6939135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6939159 : List Nat := [1, 1, 3, 6, 2, 1, 1, 1, 1, 6]
def baseStart_6939159 : Nat := 118140960795 + 6939159 * 2 ^ 59
def prefixEnd_6939159 : Nat := 4983230072969 + 3 ^ 40 * 6939159 * 2
def baseEnd_6939159 : Nat := 1187707968324173747399965

theorem tailTrace_6939159 : CollatzResearch.WordTrace tailWord_6939159 prefixEnd_6939159 1187707968324173747399965 := by
  unfold tailWord_6939159
  simp only [CollatzResearch.WordTrace]
  refine ⟨253091921067619531850564531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168727947378413021233709687 253091921067619531850564531)
  ·
    refine ⟨379637881601429297775846797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253091921067619531850564531 379637881601429297775846797)
    ·
      refine ⟨142364205600535986665942549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 379637881601429297775846797 142364205600535986665942549)
      ·
        refine ⟨6673322137525124374966057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 142364205600535986665942549 6673322137525124374966057)
        ·
          refine ⟨5004991603143843281224543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6673322137525124374966057 5004991603143843281224543)
          ·
            refine ⟨7507487404715764921836815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5004991603143843281224543 7507487404715764921836815)
            ·
              refine ⟨11261231107073647382755223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7507487404715764921836815 11261231107073647382755223)
              ·
                refine ⟨16891846660610471074132835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11261231107073647382755223 16891846660610471074132835)
                ·
                  refine ⟨25337769990915706611199253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16891846660610471074132835 25337769990915706611199253)
                  ·
                    refine ⟨1187707968324173747399965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25337769990915706611199253 1187707968324173747399965)
                    ·
                      rfl

theorem cell23_6939159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 1, 1, 1, 6].length) (baseStart_6939159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6939159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6939159 prefixEnd_6939159 := by exact prefixLift 6939159
  have htrace : WordTrace (prefixWord ++ tailWord_6939159) baseStart_6939159 baseEnd_6939159 := by
    simpa [prefixWord, tailWord_6939159, baseEnd_6939159] using wordTrace_append hprefix tailTrace_6939159
  have hstable : (prefixWord ++ tailWord_6939159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6939159).length < 2 ^ (prefixWord ++ tailWord_6939159).sum := by decide
  have hdescent : baseEnd_6939159 < baseStart_6939159 := by decide
  rcases family_descends (prefixWord ++ tailWord_6939159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6939192 : List Nat := [2, 1, 2, 1, 4, 1, 1, 5, 1, 3, 2]
def baseStart_6939192 : Nat := 118140960795 + 6939192 * 2 ^ 59
def prefixEnd_6939192 : Nat := 4983230072969 + 3 ^ 40 * 6939192 * 2
def baseEnd_6939192 : Nat := 3563140849834119613087243

theorem tailTrace_6939192 : CollatzResearch.WordTrace tailWord_6939192 prefixEnd_6939192 3563140849834119613087243 := by
  unfold tailWord_6939192
  simp only [CollatzResearch.WordTrace]
  refine ⟨126546562338249989243257915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168728749784333318991010553 126546562338249989243257915)
  ·
    refine ⟨189819843507374983864886873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126546562338249989243257915 189819843507374983864886873)
    ·
      refine ⟨142364882630531237898665155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189819843507374983864886873 142364882630531237898665155)
      ·
        refine ⟨213547323945796856847997733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142364882630531237898665155 213547323945796856847997733)
        ·
          refine ⟨40040123239836910658999575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 213547323945796856847997733 40040123239836910658999575)
          ·
            refine ⟨60060184859755365988499363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40040123239836910658999575 60060184859755365988499363)
            ·
              refine ⟨90090277289633048982749045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60060184859755365988499363 90090277289633048982749045)
              ·
                refine ⟨8445963495903098342132723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 90090277289633048982749045 8445963495903098342132723)
                ·
                  refine ⟨12668945243854647513199085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8445963495903098342132723 12668945243854647513199085)
                  ·
                    refine ⟨4750854466445492817449657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12668945243854647513199085 4750854466445492817449657)
                    ·
                      refine ⟨3563140849834119613087243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4750854466445492817449657 3563140849834119613087243)
                      ·
                        rfl

theorem cell23_6939192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 5, 1, 3, 2].length) (baseStart_6939192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6939192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6939192 prefixEnd_6939192 := by exact prefixLift 6939192
  have htrace : WordTrace (prefixWord ++ tailWord_6939192) baseStart_6939192 baseEnd_6939192 := by
    simpa [prefixWord, tailWord_6939192, baseEnd_6939192] using wordTrace_append hprefix tailTrace_6939192
  have hstable : (prefixWord ++ tailWord_6939192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6939192).length < 2 ^ (prefixWord ++ tailWord_6939192).sum := by decide
  have hdescent : baseEnd_6939192 < baseStart_6939192 := by decide
  rcases family_descends (prefixWord ++ tailWord_6939192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6939266 : List Nat := [3, 4, 3, 1, 1, 1, 1, 1, 2, 6]
def baseStart_6939266 : Nat := 118140960795 + 6939266 * 2 ^ 59
def prefixEnd_6939266 : Nat := 4983230072969 + 3 ^ 40 * 6939266 * 2
def baseEnd_6939266 : Nat := 1187726282467517441187301

theorem tailTrace_6939266 : CollatzResearch.WordTrace tailWord_6939266 prefixEnd_6939266 1187726282467517441187301 := by
  unfold tailWord_6939266
  simp only [CollatzResearch.WordTrace]
  refine ⟨63273955919557972281177413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168730549118821259416473101 63273955919557972281177413)
  ·
    refine ⟨11863866734917119802720765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63273955919557972281177413 11863866734917119802720765)
    ·
      refine ⟨4448950025593919926020287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11863866734917119802720765 4448950025593919926020287)
      ·
        refine ⟨6673425038390879889030431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4448950025593919926020287 6673425038390879889030431)
        ·
          refine ⟨10010137557586319833545647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6673425038390879889030431 10010137557586319833545647)
          ·
            refine ⟨15015206336379479750318471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10010137557586319833545647 15015206336379479750318471)
            ·
              refine ⟨22522809504569219625477707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15015206336379479750318471 22522809504569219625477707)
              ·
                refine ⟨33784214256853829438216561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22522809504569219625477707 33784214256853829438216561)
                ·
                  refine ⟨25338160692640372078662421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33784214256853829438216561 25338160692640372078662421)
                  ·
                    refine ⟨1187726282467517441187301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25338160692640372078662421 1187726282467517441187301)
                    ·
                      rfl

theorem cell23_6939266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_6939266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6939266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6939266 prefixEnd_6939266 := by exact prefixLift 6939266
  have htrace : WordTrace (prefixWord ++ tailWord_6939266) baseStart_6939266 baseEnd_6939266 := by
    simpa [prefixWord, tailWord_6939266, baseEnd_6939266] using wordTrace_append hprefix tailTrace_6939266
  have hstable : (prefixWord ++ tailWord_6939266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6939266).length < 2 ^ (prefixWord ++ tailWord_6939266).sum := by decide
  have hdescent : baseEnd_6939266 < baseStart_6939266 := by decide
  rcases family_descends (prefixWord ++ tailWord_6939266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6939292 : List Nat := [2, 2, 3, 2, 2, 1, 3, 1, 2, 5]
def baseStart_6939292 : Nat := 118140960795 + 6939292 * 2 ^ 59
def prefixEnd_6939292 : Nat := 4983230072969 + 3 ^ 40 * 6939292 * 2
def baseEnd_6939292 : Nat := 1187730732633189740612261

theorem tailTrace_6939292 : CollatzResearch.WordTrace tailWord_6939292 prefixEnd_6939292 1187730732633189740612261 := by
  unfold tailWord_6939292
  simp only [CollatzResearch.WordTrace]
  refine ⟨126548385988068847782578065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168731181317425130376770753 126548385988068847782578065)
  ·
    refine ⟨94911289491051635836933549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126548385988068847782578065 94911289491051635836933549)
    ·
      refine ⟨35591733559144363438850081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94911289491051635836933549 35591733559144363438850081)
      ·
        refine ⟨26693800169358272579137561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35591733559144363438850081 26693800169358272579137561)
        ·
          refine ⟨20020350127018704434353171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26693800169358272579137561 20020350127018704434353171)
          ·
            refine ⟨30030525190528056651529757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20020350127018704434353171 30030525190528056651529757)
            ·
              refine ⟨11261446946448021244323659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30030525190528056651529757 11261446946448021244323659)
              ·
                refine ⟨16892170419672031866485489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11261446946448021244323659 16892170419672031866485489)
                ·
                  refine ⟨12669127814754023899864117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16892170419672031866485489 12669127814754023899864117)
                  ·
                    refine ⟨1187730732633189740612261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12669127814754023899864117 1187730732633189740612261)
                    ·
                      rfl

theorem cell23_6939292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 3, 1, 2, 5].length) (baseStart_6939292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6939292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6939292 prefixEnd_6939292 := by exact prefixLift 6939292
  have htrace : WordTrace (prefixWord ++ tailWord_6939292) baseStart_6939292 baseEnd_6939292 := by
    simpa [prefixWord, tailWord_6939292, baseEnd_6939292] using wordTrace_append hprefix tailTrace_6939292
  have hstable : (prefixWord ++ tailWord_6939292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6939292).length < 2 ^ (prefixWord ++ tailWord_6939292).sum := by decide
  have hdescent : baseEnd_6939292 < baseStart_6939292 := by decide
  rcases family_descends (prefixWord ++ tailWord_6939292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6939322 : List Nat := [3, 1, 1, 1, 2, 3, 4, 1, 3, 4]
def baseStart_6939322 : Nat := 118140960795 + 6939322 * 2 ^ 59
def prefixEnd_6939322 : Nat := 4983230072969 + 3 ^ 40 * 6939322 * 2
def baseEnd_6939322 : Nat := 1187735867439734701487215

theorem tailTrace_6939322 : CollatzResearch.WordTrace tailWord_6939322 prefixEnd_6939322 1187735867439734701487215 := by
  unfold tailWord_6939322
  simp only [CollatzResearch.WordTrace]
  refine ⟨63274466541507252672187055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168731910777352673792498813 63274466541507252672187055)
  ·
    refine ⟨94911699812260879008280583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63274466541507252672187055 94911699812260879008280583)
    ·
      refine ⟨142367549718391318512420875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94911699812260879008280583 142367549718391318512420875)
      ·
        refine ⟨213551324577586977768631313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142367549718391318512420875 213551324577586977768631313)
        ·
          refine ⟨160163493433190233326473485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213551324577586977768631313 160163493433190233326473485)
          ·
            refine ⟨60061310037446337497427557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 160163493433190233326473485 60061310037446337497427557)
            ·
              refine ⟨11261495632021188280767667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60061310037446337497427557 11261495632021188280767667)
              ·
                refine ⟨16892243448031782421151501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11261495632021188280767667 16892243448031782421151501)
                ·
                  refine ⟨6334591293011918407931813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16892243448031782421151501 6334591293011918407931813)
                  ·
                    refine ⟨1187735867439734701487215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6334591293011918407931813 1187735867439734701487215)
                    ·
                      rfl

theorem cell23_6939322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 4, 1, 3, 4].length) (baseStart_6939322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6939322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6939322 prefixEnd_6939322 := by exact prefixLift 6939322
  have htrace : WordTrace (prefixWord ++ tailWord_6939322) baseStart_6939322 baseEnd_6939322 := by
    simpa [prefixWord, tailWord_6939322, baseEnd_6939322] using wordTrace_append hprefix tailTrace_6939322
  have hstable : (prefixWord ++ tailWord_6939322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6939322).length < 2 ^ (prefixWord ++ tailWord_6939322).sum := by decide
  have hdescent : baseEnd_6939322 < baseStart_6939322 := by decide
  rcases family_descends (prefixWord ++ tailWord_6939322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6939332 : List Nat := [2, 3, 3, 1, 1, 2, 1, 2, 1, 4, 3]
def baseStart_6939332 : Nat := 118140960795 + 6939332 * 2 ^ 59
def prefixEnd_6939332 : Nat := 4983230072969 + 3 ^ 40 * 6939332 * 2
def baseEnd_6939332 : Nat := 3563212737125749065336599

theorem tailTrace_6939332 : CollatzResearch.WordTrace tailWord_6939332 prefixEnd_6939332 3563212737125749065336599 := by
  unfold tailWord_6939332
  simp only [CollatzResearch.WordTrace]
  refine ⟨126549115447996391198306125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168732153930661854931074833 126549115447996391198306125)
  ·
    refine ⟨47455918292998646699364797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126549115447996391198306125 47455918292998646699364797)
    ·
      refine ⟨17795969359874492512261799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47455918292998646699364797 17795969359874492512261799)
      ·
        refine ⟨26693954039811738768392699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17795969359874492512261799 26693954039811738768392699)
        ·
          refine ⟨40040931059717608152589049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26693954039811738768392699 40040931059717608152589049)
          ·
            refine ⟨30030698294788206114441787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40040931059717608152589049 30030698294788206114441787)
            ·
              refine ⟨45046047442182309171662681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30030698294788206114441787 45046047442182309171662681)
              ·
                refine ⟨33784535581636731878747011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45046047442182309171662681 33784535581636731878747011)
                ·
                  refine ⟨50676803372455097818120517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33784535581636731878747011 50676803372455097818120517)
                  ·
                    refine ⟨9501900632335330840897597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50676803372455097818120517 9501900632335330840897597)
                    ·
                      refine ⟨3563212737125749065336599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9501900632335330840897597 3563212737125749065336599)
                      ·
                        rfl

theorem cell23_6939332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 2, 1, 4, 3].length) (baseStart_6939332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6939332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6939332 prefixEnd_6939332 := by exact prefixLift 6939332
  have htrace : WordTrace (prefixWord ++ tailWord_6939332) baseStart_6939332 baseEnd_6939332 := by
    simpa [prefixWord, tailWord_6939332, baseEnd_6939332] using wordTrace_append hprefix tailTrace_6939332
  have hstable : (prefixWord ++ tailWord_6939332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6939332).length < 2 ^ (prefixWord ++ tailWord_6939332).sum := by decide
  have hdescent : baseEnd_6939332 < baseStart_6939332 := by decide
  rcases family_descends (prefixWord ++ tailWord_6939332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6939345 : List Nat := [1, 2, 2, 1, 2, 3, 1, 1, 2, 5, 3]
def baseStart_6939345 : Nat := 118140960795 + 6939345 * 2 ^ 59
def prefixEnd_6939345 : Nat := 4983230072969 + 3 ^ 40 * 6939345 * 2
def baseEnd_6939345 : Nat := 3563219412374257514474039

theorem tailTrace_6939345 : CollatzResearch.WordTrace tailWord_6939345 prefixEnd_6939345 3563219412374257514474039 := by
  unfold tailWord_6939345
  simp only [CollatzResearch.WordTrace]
  refine ⟨253098705044945685616835489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168732470029963790411223659 253098705044945685616835489)
  ·
    refine ⟨189824028783709264212626617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253098705044945685616835489 189824028783709264212626617)
    ·
      refine ⟨142368021587781948159469963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189824028783709264212626617 142368021587781948159469963)
      ·
        refine ⟨213552032381672922239204945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142368021587781948159469963 213552032381672922239204945)
        ·
          refine ⟨160164024286254691679403709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213552032381672922239204945 160164024286254691679403709)
          ·
            refine ⟨60061509107345509379776391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 160164024286254691679403709 60061509107345509379776391)
            ·
              refine ⟨90092263661018264069664587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60061509107345509379776391 90092263661018264069664587)
              ·
                refine ⟨135138395491527396104496881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90092263661018264069664587 135138395491527396104496881)
                ·
                  refine ⟨101353796618645547078372661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 135138395491527396104496881 101353796618645547078372661)
                  ·
                    refine ⟨9501918432998020038597437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 101353796618645547078372661 9501918432998020038597437)
                    ·
                      refine ⟨3563219412374257514474039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9501918432998020038597437 3563219412374257514474039)
                      ·
                        rfl

theorem cell23_6939345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 2, 5, 3].length) (baseStart_6939345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6939345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6939345 prefixEnd_6939345 := by exact prefixLift 6939345
  have htrace : WordTrace (prefixWord ++ tailWord_6939345) baseStart_6939345 baseEnd_6939345 := by
    simpa [prefixWord, tailWord_6939345, baseEnd_6939345] using wordTrace_append hprefix tailTrace_6939345
  have hstable : (prefixWord ++ tailWord_6939345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6939345).length < 2 ^ (prefixWord ++ tailWord_6939345).sum := by decide
  have hdescent : baseEnd_6939345 < baseStart_6939345 := by decide
  rcases family_descends (prefixWord ++ tailWord_6939345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6939382 : List Nat := [5, 1, 1, 1, 1, 2, 2, 2, 3, 5]
def baseStart_6939382 : Nat := 118140960795 + 6939382 * 2 ^ 59
def prefixEnd_6939382 : Nat := 4983230072969 + 3 ^ 40 * 6939382 * 2
def baseEnd_6939382 : Nat := 1187746137052824623237123

theorem tailTrace_6939382 : CollatzResearch.WordTrace tailWord_6939382 prefixEnd_6939382 1187746137052824623237123 := by
  unfold tailWord_6939382
  simp only [CollatzResearch.WordTrace]
  refine ⟨15818753409113227558495775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 168733369697207760623954933 15818753409113227558495775)
  ·
    refine ⟨23728130113669841337743663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15818753409113227558495775 23728130113669841337743663)
    ·
      refine ⟨35592195170504762006615495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23728130113669841337743663 35592195170504762006615495)
      ·
        refine ⟨53388292755757143009923243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35592195170504762006615495 53388292755757143009923243)
        ·
          refine ⟨80082439133635714514884865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53388292755757143009923243 80082439133635714514884865)
          ·
            refine ⟨60061829350226785886163649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80082439133635714514884865 60061829350226785886163649)
            ·
              refine ⟨45046372012670089414622737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60061829350226785886163649 45046372012670089414622737)
              ·
                refine ⟨33784779009502567060967053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45046372012670089414622737 33784779009502567060967053)
                ·
                  refine ⟨12669292128563462647862645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33784779009502567060967053 12669292128563462647862645)
                  ·
                    refine ⟨1187746137052824623237123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12669292128563462647862645 1187746137052824623237123)
                    ·
                      rfl

theorem cell23_6939382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 2, 3, 5].length) (baseStart_6939382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6939382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6939382 prefixEnd_6939382 := by exact prefixLift 6939382
  have htrace : WordTrace (prefixWord ++ tailWord_6939382) baseStart_6939382 baseEnd_6939382 := by
    simpa [prefixWord, tailWord_6939382, baseEnd_6939382] using wordTrace_append hprefix tailTrace_6939382
  have hstable : (prefixWord ++ tailWord_6939382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6939382).length < 2 ^ (prefixWord ++ tailWord_6939382).sum := by decide
  have hdescent : baseEnd_6939382 < baseStart_6939382 := by decide
  rcases family_descends (prefixWord ++ tailWord_6939382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6939395 : List Nat := [1, 1, 1, 3, 2, 2, 1, 5, 1, 6]
def baseStart_6939395 : Nat := 118140960795 + 6939395 * 2 ^ 59
def prefixEnd_6939395 : Nat := 4983230072969 + 3 ^ 40 * 6939395 * 2
def baseEnd_6939395 : Nat := 1187748362135660772949603

theorem tailTrace_6939395 : CollatzResearch.WordTrace tailWord_6939395 prefixEnd_6939395 1187748362135660772949603 := by
  unfold tailWord_6939395
  simp only [CollatzResearch.WordTrace]
  refine ⟨253100528694764544156155639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168733685796509696104103759 253100528694764544156155639)
  ·
    refine ⟨379650793042146816234233459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253100528694764544156155639 379650793042146816234233459)
    ·
      refine ⟨569476189563220224351350189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379650793042146816234233459 569476189563220224351350189)
      ·
        refine ⟨213553571086207584131756321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 569476189563220224351350189 213553571086207584131756321)
        ·
          refine ⟨160165178314655688098817241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213553571086207584131756321 160165178314655688098817241)
          ·
            refine ⟨120123883735991766074112931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160165178314655688098817241 120123883735991766074112931)
            ·
              refine ⟨180185825603987649111169397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120123883735991766074112931 180185825603987649111169397)
              ·
                refine ⟨16892421150373842104172131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 180185825603987649111169397 16892421150373842104172131)
                ·
                  refine ⟨25338631725560763156258197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16892421150373842104172131 25338631725560763156258197)
                  ·
                    refine ⟨1187748362135660772949603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25338631725560763156258197 1187748362135660772949603)
                    ·
                      rfl

theorem cell23_6939395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 5, 1, 6].length) (baseStart_6939395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6939395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6939395 prefixEnd_6939395 := by exact prefixLift 6939395
  have htrace : WordTrace (prefixWord ++ tailWord_6939395) baseStart_6939395 baseEnd_6939395 := by
    simpa [prefixWord, tailWord_6939395, baseEnd_6939395] using wordTrace_append hprefix tailTrace_6939395
  have hstable : (prefixWord ++ tailWord_6939395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6939395).length < 2 ^ (prefixWord ++ tailWord_6939395).sum := by decide
  have hdescent : baseEnd_6939395 < baseStart_6939395 := by decide
  rcases family_descends (prefixWord ++ tailWord_6939395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6939399 : List Nat := [1, 1, 4, 4, 1, 1, 3, 2, 1, 5]
def baseStart_6939399 : Nat := 118140960795 + 6939399 * 2 ^ 59
def prefixEnd_6939399 : Nat := 4983230072969 + 3 ^ 40 * 6939399 * 2
def baseEnd_6939399 : Nat := 1187749046776533434399597

theorem tailTrace_6939399 : CollatzResearch.WordTrace tailWord_6939399 prefixEnd_6939399 1187749046776533434399597 := by
  unfold tailWord_6939399
  simp only [CollatzResearch.WordTrace]
  refine ⟨253100674586750052839301251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168733783057833368559534167 253100674586750052839301251)
  ·
    refine ⟨379651011880125079258951877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253100674586750052839301251 379651011880125079258951877)
    ·
      refine ⟨71184564727523452361053477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 379651011880125079258951877 71184564727523452361053477)
      ·
        refine ⟨13347105886410647317697527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71184564727523452361053477 13347105886410647317697527)
        ·
          refine ⟨20020658829615970976546291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13347105886410647317697527 20020658829615970976546291)
          ·
            refine ⟨30030988244423956464819437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20020658829615970976546291 30030988244423956464819437)
            ·
              refine ⟨11261620591658983674307289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30030988244423956464819437 11261620591658983674307289)
              ·
                refine ⟨8446215443744237755730467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11261620591658983674307289 8446215443744237755730467)
                ·
                  refine ⟨12669323165616356633595701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8446215443744237755730467 12669323165616356633595701)
                  ·
                    refine ⟨1187749046776533434399597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12669323165616356633595701 1187749046776533434399597)
                    ·
                      rfl

theorem cell23_6939399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 3, 2, 1, 5].length) (baseStart_6939399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6939399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6939399 prefixEnd_6939399 := by exact prefixLift 6939399
  have htrace : WordTrace (prefixWord ++ tailWord_6939399) baseStart_6939399 baseEnd_6939399 := by
    simpa [prefixWord, tailWord_6939399, baseEnd_6939399] using wordTrace_append hprefix tailTrace_6939399
  have hstable : (prefixWord ++ tailWord_6939399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6939399).length < 2 ^ (prefixWord ++ tailWord_6939399).sum := by decide
  have hdescent : baseEnd_6939399 < baseStart_6939399 := by decide
  rcases family_descends (prefixWord ++ tailWord_6939399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6939402 : List Nat := [3, 1, 2, 2, 1, 2, 3, 1, 3, 1, 4]
def baseStart_6939402 : Nat := 118140960795 + 6939402 * 2 ^ 59
def prefixEnd_6939402 : Nat := 4983230072969 + 3 ^ 40 * 6939402 * 2
def baseEnd_6939402 : Nat := 3563248680771563791461277

theorem tailTrace_6939402 : CollatzResearch.WordTrace tailWord_6939402 prefixEnd_6939402 3563248680771563791461277 := by
  unfold tailWord_6939402
  simp only [CollatzResearch.WordTrace]
  refine ⟨63275196001434796087915115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168733856003826122901106973 63275196001434796087915115)
  ·
    refine ⟨94912794002152194131872673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63275196001434796087915115 94912794002152194131872673)
    ·
      refine ⟨71184595501614145598904505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94912794002152194131872673 71184595501614145598904505)
      ·
        refine ⟨53388446626210609199178379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71184595501614145598904505 53388446626210609199178379)
        ·
          refine ⟨80082669939315913798767569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53388446626210609199178379 80082669939315913798767569)
          ·
            refine ⟨60062002454486935349075677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80082669939315913798767569 60062002454486935349075677)
            ·
              refine ⟨22523250920432600755903379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60062002454486935349075677 22523250920432600755903379)
              ·
                refine ⟨33784876380648901133855069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22523250920432600755903379 33784876380648901133855069)
                ·
                  refine ⟨12669328642743337925195651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33784876380648901133855069 12669328642743337925195651)
                  ·
                    refine ⟨19003992964115006887793477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12669328642743337925195651 19003992964115006887793477)
                    ·
                      refine ⟨3563248680771563791461277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19003992964115006887793477 3563248680771563791461277)
                      ·
                        rfl

theorem cell23_6939402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 1, 3, 1, 4].length) (baseStart_6939402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6939402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6939402 prefixEnd_6939402 := by exact prefixLift 6939402
  have htrace : WordTrace (prefixWord ++ tailWord_6939402) baseStart_6939402 baseEnd_6939402 := by
    simpa [prefixWord, tailWord_6939402, baseEnd_6939402] using wordTrace_append hprefix tailTrace_6939402
  have hstable : (prefixWord ++ tailWord_6939402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6939402).length < 2 ^ (prefixWord ++ tailWord_6939402).sum := by decide
  have hdescent : baseEnd_6939402 < baseStart_6939402 := by decide
  rcases family_descends (prefixWord ++ tailWord_6939402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6939429 : List Nat := [1, 3, 1, 2, 3, 1, 4, 2, 2, 4]
def baseStart_6939429 : Nat := 118140960795 + 6939429 * 2 ^ 59
def prefixEnd_6939429 : Nat := 4983230072969 + 3 ^ 40 * 6939429 * 2
def baseEnd_6939429 : Nat := 1187754181583078395274551

theorem tailTrace_6939429 : CollatzResearch.WordTrace tailWord_6939429 prefixEnd_6939429 1187754181583078395274551 := by
  unfold tailWord_6939429
  simp only [CollatzResearch.WordTrace]
  refine ⟨253101768776641367962893341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168734512517760911975262227 253101768776641367962893341)
  ·
    refine ⟨94913163291240512986085003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 253101768776641367962893341 94913163291240512986085003)
    ·
      refine ⟨142369744936860769479127505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94913163291240512986085003 142369744936860769479127505)
      ·
        refine ⟨106777308702645577109345629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142369744936860769479127505 106777308702645577109345629)
        ·
          refine ⟨40041490763492091416004611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106777308702645577109345629 40041490763492091416004611)
          ·
            refine ⟨60062236145238137124006917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40041490763492091416004611 60062236145238137124006917)
            ·
              refine ⟨11261669277232150710751297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60062236145238137124006917 11261669277232150710751297)
              ·
                refine ⟨8446251957924113033063473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11261669277232150710751297 8446251957924113033063473)
                ·
                  refine ⟨6334688968443084774797605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8446251957924113033063473 6334688968443084774797605)
                  ·
                    refine ⟨1187754181583078395274551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6334688968443084774797605 1187754181583078395274551)
                    ·
                      rfl

theorem cell23_6939429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 4, 2, 2, 4].length) (baseStart_6939429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6939429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6939429 prefixEnd_6939429 := by exact prefixLift 6939429
  have htrace : WordTrace (prefixWord ++ tailWord_6939429) baseStart_6939429 baseEnd_6939429 := by
    simpa [prefixWord, tailWord_6939429, baseEnd_6939429] using wordTrace_append hprefix tailTrace_6939429
  have hstable : (prefixWord ++ tailWord_6939429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6939429).length < 2 ^ (prefixWord ++ tailWord_6939429).sum := by decide
  have hdescent : baseEnd_6939429 < baseStart_6939429 := by decide
  rcases family_descends (prefixWord ++ tailWord_6939429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6939432 : List Nat := [2, 1, 5, 1, 1, 1, 1, 2, 3, 2, 4]
def baseStart_6939432 : Nat := 118140960795 + 6939432 * 2 ^ 59
def prefixEnd_6939432 : Nat := 4983230072969 + 3 ^ 40 * 6939432 * 2
def baseEnd_6939432 : Nat := 3563264085191198674086139

theorem tailTrace_6939432 : CollatzResearch.WordTrace tailWord_6939432 prefixEnd_6939432 3563264085191198674086139 := by
  unfold tailWord_6939432
  simp only [CollatzResearch.WordTrace]
  refine ⟨126550939097815249737626275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168734585463753666316835033 126550939097815249737626275)
  ·
    refine ⟨189826408646722874606439413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126550939097815249737626275 189826408646722874606439413)
    ·
      refine ⟨17796225810630269494353695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 189826408646722874606439413 17796225810630269494353695)
      ·
        refine ⟨26694338715945404241530543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17796225810630269494353695 26694338715945404241530543)
        ·
          refine ⟨40041508073918106362295815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26694338715945404241530543 40041508073918106362295815)
          ·
            refine ⟨60062262110877159543443723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40041508073918106362295815 60062262110877159543443723)
            ·
              refine ⟨90093393166315739315165585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60062262110877159543443723 90093393166315739315165585)
              ·
                refine ⟨67570044874736804486374189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90093393166315739315165585 67570044874736804486374189)
                ·
                  refine ⟨25338766828026301682390321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67570044874736804486374189 25338766828026301682390321)
                  ·
                    refine ⟨19004075121019726261792741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25338766828026301682390321 19004075121019726261792741)
                    ·
                      refine ⟨3563264085191198674086139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19004075121019726261792741 3563264085191198674086139)
                      ·
                        rfl

theorem cell23_6939432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_6939432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6939432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6939432 prefixEnd_6939432 := by exact prefixLift 6939432
  have htrace : WordTrace (prefixWord ++ tailWord_6939432) baseStart_6939432 baseEnd_6939432 := by
    simpa [prefixWord, tailWord_6939432, baseEnd_6939432] using wordTrace_append hprefix tailTrace_6939432
  have hstable : (prefixWord ++ tailWord_6939432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6939432).length < 2 ^ (prefixWord ++ tailWord_6939432).sum := by decide
  have hdescent : baseEnd_6939432 < baseStart_6939432 := by decide
  rcases family_descends (prefixWord ++ tailWord_6939432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6939446 : List Nat := [5, 1, 2, 2, 2, 1, 2, 1, 1, 6]
def baseStart_6939446 : Nat := 118140960795 + 6939446 * 2 ^ 59
def prefixEnd_6939446 : Nat := 4983230072969 + 3 ^ 40 * 6939446 * 2
def baseEnd_6939446 : Nat := 1187757091306787206437025

theorem tailTrace_6939446 : CollatzResearch.WordTrace tailWord_6939446 prefixEnd_6939446 1187757091306787206437025 := by
  unfold tailWord_6939446
  simp only [CollatzResearch.WordTrace]
  refine ⟨15818899301098736241641387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 168734925878386519910841461 15818899301098736241641387)
  ·
    refine ⟨23728348951648104362462081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15818899301098736241641387 23728348951648104362462081)
    ·
      refine ⟨17796261713736078271846561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23728348951648104362462081 17796261713736078271846561)
      ·
        refine ⟨13347196285302058703884921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17796261713736078271846561 13347196285302058703884921)
        ·
          refine ⟨10010397213976544027913691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13347196285302058703884921 10010397213976544027913691)
          ·
            refine ⟨15015595820964816041870537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10010397213976544027913691 15015595820964816041870537)
            ·
              refine ⟨11261696865723612031402903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15015595820964816041870537 11261696865723612031402903)
              ·
                refine ⟨16892545298585418047104355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11261696865723612031402903 16892545298585418047104355)
                ·
                  refine ⟨25338817947878127070656533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16892545298585418047104355 25338817947878127070656533)
                  ·
                    refine ⟨1187757091306787206437025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25338817947878127070656533 1187757091306787206437025)
                    ·
                      rfl

theorem cell23_6939446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 2, 1, 1, 6].length) (baseStart_6939446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6939446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6939446 prefixEnd_6939446 := by exact prefixLift 6939446
  have htrace : WordTrace (prefixWord ++ tailWord_6939446) baseStart_6939446 baseEnd_6939446 := by
    simpa [prefixWord, tailWord_6939446, baseEnd_6939446] using wordTrace_append hprefix tailTrace_6939446
  have hstable : (prefixWord ++ tailWord_6939446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6939446).length < 2 ^ (prefixWord ++ tailWord_6939446).sum := by decide
  have hdescent : baseEnd_6939446 < baseStart_6939446 := by decide
  rcases family_descends (prefixWord ++ tailWord_6939446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6939453 : List Nat := [1, 4, 1, 4, 2, 1, 1, 2, 3, 2, 2]
def baseStart_6939453 : Nat := 118140960795 + 6939453 * 2 ^ 59
def prefixEnd_6939453 : Nat := 4983230072969 + 3 ^ 40 * 6939453 * 2
def baseEnd_6939453 : Nat := 3563274868284943091923543

theorem tailTrace_6939453 : CollatzResearch.WordTrace tailWord_6939453 prefixEnd_6939453 3563274868284943091923543 := by
  unfold tailWord_6939453
  simp only [CollatzResearch.WordTrace]
  refine ⟨253102644128554420061767013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168735096085702946707844675 253102644128554420061767013)
  ·
    refine ⟨47456745774103953761581315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 253102644128554420061767013 47456745774103953761581315)
    ·
      refine ⟨71185118661155930642371973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47456745774103953761581315 71185118661155930642371973)
      ·
        refine ⟨13347209748966736995444745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71185118661155930642371973 13347209748966736995444745)
        ·
          refine ⟨10010407311725052746583559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13347209748966736995444745 10010407311725052746583559)
          ·
            refine ⟨15015610967587579119875339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10010407311725052746583559 15015610967587579119875339)
            ·
              refine ⟨22523416451381368679813009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15015610967587579119875339 22523416451381368679813009)
              ·
                refine ⟨16892562338536026509859757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22523416451381368679813009 16892562338536026509859757)
                ·
                  refine ⟨6334710876951009941197409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16892562338536026509859757 6334710876951009941197409)
                  ·
                    refine ⟨4751033157713257455898057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6334710876951009941197409 4751033157713257455898057)
                    ·
                      refine ⟨3563274868284943091923543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4751033157713257455898057 3563274868284943091923543)
                      ·
                        rfl

theorem cell23_6939453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 2, 3, 2, 2].length) (baseStart_6939453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6939453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6939453 prefixEnd_6939453 := by exact prefixLift 6939453
  have htrace : WordTrace (prefixWord ++ tailWord_6939453) baseStart_6939453 baseEnd_6939453 := by
    simpa [prefixWord, tailWord_6939453, baseEnd_6939453] using wordTrace_append hprefix tailTrace_6939453
  have hstable : (prefixWord ++ tailWord_6939453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6939453).length < 2 ^ (prefixWord ++ tailWord_6939453).sum := by decide
  have hdescent : baseEnd_6939453 < baseStart_6939453 := by decide
  rcases family_descends (prefixWord ++ tailWord_6939453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6939473 : List Nat := [1, 2, 2, 1, 6, 2, 2, 1, 1, 2, 3]
def baseStart_6939473 : Nat := 118140960795 + 6939473 * 2 ^ 59
def prefixEnd_6939473 : Nat := 4983230072969 + 3 ^ 40 * 6939473 * 2
def baseEnd_6939473 : Nat := 3563285137898033013673451

theorem tailTrace_6939473 : CollatzResearch.WordTrace tailWord_6939473 prefixEnd_6939473 3563285137898033013673451 := by
  unfold tailWord_6939473
  simp only [CollatzResearch.WordTrace]
  refine ⟨253103373588481963477495073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168735582392321308984996715 253103373588481963477495073)
  ·
    refine ⟨189827530191361472608121305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253103373588481963477495073 189827530191361472608121305)
    ·
      refine ⟨142370647643521104456090979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189827530191361472608121305 142370647643521104456090979)
      ·
        refine ⟨213555971465281656684136469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142370647643521104456090979 213555971465281656684136469)
        ·
          refine ⟨10010436162435077657068897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 213555971465281656684136469 10010436162435077657068897)
          ·
            refine ⟨7507827121826308242801673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10010436162435077657068897 7507827121826308242801673)
            ·
              refine ⟨5630870341369731182101255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7507827121826308242801673 5630870341369731182101255)
              ·
                refine ⟨8446305512054596773151883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5630870341369731182101255 8446305512054596773151883)
                ·
                  refine ⟨12669458268081895159727825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8446305512054596773151883 12669458268081895159727825)
                  ·
                    refine ⟨9502093701061421369795869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12669458268081895159727825 9502093701061421369795869)
                    ·
                      refine ⟨3563285137898033013673451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9502093701061421369795869 3563285137898033013673451)
                      ·
                        rfl

theorem cell23_6939473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 2, 1, 1, 2, 3].length) (baseStart_6939473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6939473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6939473 prefixEnd_6939473 := by exact prefixLift 6939473
  have htrace : WordTrace (prefixWord ++ tailWord_6939473) baseStart_6939473 baseEnd_6939473 := by
    simpa [prefixWord, tailWord_6939473, baseEnd_6939473] using wordTrace_append hprefix tailTrace_6939473
  have hstable : (prefixWord ++ tailWord_6939473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6939473).length < 2 ^ (prefixWord ++ tailWord_6939473).sum := by decide
  have hdescent : baseEnd_6939473 < baseStart_6939473 := by decide
  rcases family_descends (prefixWord ++ tailWord_6939473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6939599 : List Nat := [1, 1, 2, 1, 1, 6, 2, 2, 2, 1, 4]
def baseStart_6939599 : Nat := 118140960795 + 6939599 * 2 ^ 59
def prefixEnd_6939599 : Nat := 4983230072969 + 3 ^ 40 * 6939599 * 2
def baseEnd_6939599 : Nat := 3563349836460499520697871

theorem tailTrace_6939599 : CollatzResearch.WordTrace tailWord_6939599 prefixEnd_6939599 3563349836460499520697871 := by
  unfold tailWord_6939599
  simp only [CollatzResearch.WordTrace]
  refine ⟨253107969186025486996581851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168738646124016991331054567 253107969186025486996581851)
  ·
    refine ⟨379661953779038230494872777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253107969186025486996581851 379661953779038230494872777)
    ·
      refine ⟨284746465334278672871154583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 379661953779038230494872777 284746465334278672871154583)
      ·
        refine ⟨427119698001418009306731875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284746465334278672871154583 427119698001418009306731875)
        ·
          refine ⟨640679547002127013960097813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 427119698001418009306731875 640679547002127013960097813)
          ·
            refine ⟨30031853765724703779379585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 640679547002127013960097813 30031853765724703779379585)
            ·
              refine ⟨22523890324293527834534689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30031853765724703779379585 22523890324293527834534689)
              ·
                refine ⟨16892917743220145875901017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22523890324293527834534689 16892917743220145875901017)
                ·
                  refine ⟨12669688307415109406925763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16892917743220145875901017 12669688307415109406925763)
                  ·
                    refine ⟨19004532461122664110388645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12669688307415109406925763 19004532461122664110388645)
                    ·
                      refine ⟨3563349836460499520697871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19004532461122664110388645 3563349836460499520697871)
                      ·
                        rfl

theorem cell23_6939599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 2, 2, 1, 4].length) (baseStart_6939599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6939599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6939599 prefixEnd_6939599 := by exact prefixLift 6939599
  have htrace : WordTrace (prefixWord ++ tailWord_6939599) baseStart_6939599 baseEnd_6939599 := by
    simpa [prefixWord, tailWord_6939599, baseEnd_6939599] using wordTrace_append hprefix tailTrace_6939599
  have hstable : (prefixWord ++ tailWord_6939599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6939599).length < 2 ^ (prefixWord ++ tailWord_6939599).sum := by decide
  have hdescent : baseEnd_6939599 < baseStart_6939599 := by decide
  rcases family_descends (prefixWord ++ tailWord_6939599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6939606 : List Nat := [5, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5]
def baseStart_6939606 : Nat := 118140960795 + 6939606 * 2 ^ 59
def prefixEnd_6939606 : Nat := 4983230072969 + 3 ^ 40 * 6939606 * 2
def baseEnd_6939606 : Nat := 3563353430825080993310339

theorem tailTrace_6939606 : CollatzResearch.WordTrace tailWord_6939606 prefixEnd_6939606 3563353430825080993310339 := by
  unfold tailWord_6939606
  simp only [CollatzResearch.WordTrace]
  refine ⟨15819264031062507949505417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 168738816331333418128057781 15819264031062507949505417)
  ·
    refine ⟨11864448023296880962129063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15819264031062507949505417 11864448023296880962129063)
    ·
      refine ⟨17796672034945321443193595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11864448023296880962129063 17796672034945321443193595)
      ·
        refine ⟨26695008052417982164790393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17796672034945321443193595 26695008052417982164790393)
        ·
          refine ⟨20021256039313486623592795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26695008052417982164790393 20021256039313486623592795)
          ·
            refine ⟨30031884058970229935389193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20021256039313486623592795 30031884058970229935389193)
            ·
              refine ⟨22523913044227672451541895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30031884058970229935389193 22523913044227672451541895)
              ·
                refine ⟨33785869566341508677312843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22523913044227672451541895 33785869566341508677312843)
                ·
                  refine ⟨50678804349512263015969265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33785869566341508677312843 50678804349512263015969265)
                  ·
                    refine ⟨38009103262134197261976949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50678804349512263015969265 38009103262134197261976949)
                    ·
                      refine ⟨3563353430825080993310339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38009103262134197261976949 3563353430825080993310339)
                      ·
                        rfl

theorem cell23_6939606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_6939606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6939606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6939606 prefixEnd_6939606 := by exact prefixLift 6939606
  have htrace : WordTrace (prefixWord ++ tailWord_6939606) baseStart_6939606 baseEnd_6939606 := by
    simpa [prefixWord, tailWord_6939606, baseEnd_6939606] using wordTrace_append hprefix tailTrace_6939606
  have hstable : (prefixWord ++ tailWord_6939606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6939606).length < 2 ^ (prefixWord ++ tailWord_6939606).sum := by decide
  have hdescent : baseEnd_6939606 < baseStart_6939606 := by decide
  rcases family_descends (prefixWord ++ tailWord_6939606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6939619 : List Nat := [1, 1, 1, 6, 1, 1, 2, 2, 1, 4, 3]
def baseStart_6939619 : Nat := 118140960795 + 6939619 * 2 ^ 59
def prefixEnd_6939619 : Nat := 4983230072969 + 3 ^ 40 * 6939619 * 2
def baseEnd_6939619 : Nat := 3563360106073589442447779

theorem tailTrace_6939619 : CollatzResearch.WordTrace tailWord_6939619 prefixEnd_6939619 3563360106073589442447779 := by
  unfold tailWord_6939619
  simp only [CollatzResearch.WordTrace]
  refine ⟨253108698645953030412309911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168739132430635353608206607 253108698645953030412309911)
  ·
    refine ⟨379663047968929545618464867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253108698645953030412309911 379663047968929545618464867)
    ·
      refine ⟨569494571953394318427697301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379663047968929545618464867 569494571953394318427697301)
      ·
        refine ⟨26695058060315358676298311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 569494571953394318427697301 26695058060315358676298311)
        ·
          refine ⟨40042587090473038014447467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26695058060315358676298311 40042587090473038014447467)
          ·
            refine ⟨60063880635709557021671201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40042587090473038014447467 60063880635709557021671201)
            ·
              refine ⟨45047910476782167766253401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60063880635709557021671201 45047910476782167766253401)
              ·
                refine ⟨33785932857586625824690051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45047910476782167766253401 33785932857586625824690051)
                ·
                  refine ⟨50678899286379938737035077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33785932857586625824690051 50678899286379938737035077)
                  ·
                    refine ⟨9502293616196238513194077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50678899286379938737035077 9502293616196238513194077)
                    ·
                      refine ⟨3563360106073589442447779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9502293616196238513194077 3563360106073589442447779)
                      ·
                        rfl

theorem cell23_6939619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 2, 1, 4, 3].length) (baseStart_6939619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6939619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6939619 prefixEnd_6939619 := by exact prefixLift 6939619
  have htrace : WordTrace (prefixWord ++ tailWord_6939619) baseStart_6939619 baseEnd_6939619 := by
    simpa [prefixWord, tailWord_6939619, baseEnd_6939619] using wordTrace_append hprefix tailTrace_6939619
  have hstable : (prefixWord ++ tailWord_6939619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6939619).length < 2 ^ (prefixWord ++ tailWord_6939619).sum := by decide
  have hdescent : baseEnd_6939619 < baseStart_6939619 := by decide
  rcases family_descends (prefixWord ++ tailWord_6939619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6939626 : List Nat := [3, 1, 3, 1, 2, 3, 1, 2, 3, 4]
def baseStart_6939626 : Nat := 118140960795 + 6939626 * 2 ^ 59
def prefixEnd_6939626 : Nat := 4983230072969 + 3 ^ 40 * 6939626 * 2
def baseEnd_6939626 : Nat := 1187787900146056971686749

theorem tailTrace_6939626 : CollatzResearch.WordTrace tailWord_6939626 prefixEnd_6939626 1187787900146056971686749 := by
  unfold tailWord_6939626
  simp only [CollatzResearch.WordTrace]
  refine ⟨63277238489231917651953683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168739302637951780405209821 63277238489231917651953683)
  ·
    refine ⟨94915857733847876477930525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63277238489231917651953683 94915857733847876477930525)
    ·
      refine ⟨35593446650192953679223947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94915857733847876477930525 35593446650192953679223947)
      ·
        refine ⟨53390169975289430518835921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35593446650192953679223947 53390169975289430518835921)
        ·
          refine ⟨40042627481467072889126941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53390169975289430518835921 40042627481467072889126941)
          ·
            refine ⟨15015985305550152333422603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40042627481467072889126941 15015985305550152333422603)
            ·
              refine ⟨22523977958325228500133905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15015985305550152333422603 22523977958325228500133905)
              ·
                refine ⟨16892983468743921375100429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22523977958325228500133905 16892983468743921375100429)
                ·
                  refine ⟨6334868800778970515662661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16892983468743921375100429 6334868800778970515662661)
                  ·
                    refine ⟨1187787900146056971686749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6334868800778970515662661 1187787900146056971686749)
                    ·
                      rfl

theorem cell23_6939626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 2, 3, 4].length) (baseStart_6939626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6939626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6939626 prefixEnd_6939626 := by exact prefixLift 6939626
  have htrace : WordTrace (prefixWord ++ tailWord_6939626) baseStart_6939626 baseEnd_6939626 := by
    simpa [prefixWord, tailWord_6939626, baseEnd_6939626] using wordTrace_append hprefix tailTrace_6939626
  have hstable : (prefixWord ++ tailWord_6939626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6939626).length < 2 ^ (prefixWord ++ tailWord_6939626).sum := by decide
  have hdescent : baseEnd_6939626 < baseStart_6939626 := by decide
  rcases family_descends (prefixWord ++ tailWord_6939626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6939642 : List Nat := [3, 1, 1, 1, 1, 2, 1, 2, 3, 2, 6]
def baseStart_6939642 : Nat := 118140960795 + 6939642 * 2 ^ 59
def prefixEnd_6939642 : Nat := 4983230072969 + 3 ^ 40 * 6939642 * 2
def baseEnd_6939642 : Nat := 3563371916128642852460173

theorem tailTrace_6939642 : CollatzResearch.WordTrace tailWord_6939642 prefixEnd_6939642 3563371916128642852460173 := by
  unfold tailWord_6939642
  simp only [CollatzResearch.WordTrace]
  refine ⟨63277384381217426335099295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168739691683246470226931453 63277384381217426335099295)
  ·
    refine ⟨94916076571826139502648943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63277384381217426335099295 94916076571826139502648943)
    ·
      refine ⟨142374114857739209253973415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94916076571826139502648943 142374114857739209253973415)
      ·
        refine ⟨213561172286608813880960123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142374114857739209253973415 213561172286608813880960123)
        ·
          refine ⟨320341758429913220821440185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213561172286608813880960123 320341758429913220821440185)
          ·
            refine ⟨240256318822434915616080139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 320341758429913220821440185 240256318822434915616080139)
            ·
              refine ⟨360384478233652373424120209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 240256318822434915616080139 360384478233652373424120209)
              ·
                refine ⟨270288358675239280068090157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 360384478233652373424120209 270288358675239280068090157)
                ·
                  refine ⟨101358134503214730025533809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 270288358675239280068090157 101358134503214730025533809)
                  ·
                    refine ⟨76018600877411047519150357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 101358134503214730025533809 76018600877411047519150357)
                    ·
                      refine ⟨3563371916128642852460173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76018600877411047519150357 3563371916128642852460173)
                      ·
                        rfl

theorem cell23_6939642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 3, 2, 6].length) (baseStart_6939642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6939642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6939642 prefixEnd_6939642 := by exact prefixLift 6939642
  have htrace : WordTrace (prefixWord ++ tailWord_6939642) baseStart_6939642 baseEnd_6939642 := by
    simpa [prefixWord, tailWord_6939642, baseEnd_6939642] using wordTrace_append hprefix tailTrace_6939642
  have hstable : (prefixWord ++ tailWord_6939642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6939642).length < 2 ^ (prefixWord ++ tailWord_6939642).sum := by decide
  have hdescent : baseEnd_6939642 < baseStart_6939642 := by decide
  rcases family_descends (prefixWord ++ tailWord_6939642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6939656 : List Nat := [2, 1, 3, 2, 1, 5, 1, 2, 6]
def baseStart_6939656 : Nat := 118140960795 + 6939656 * 2 ^ 59
def prefixEnd_6939656 : Nat := 4983230072969 + 3 ^ 40 * 6939656 * 2
def baseEnd_6939656 : Nat := 395931011650867310853901

theorem tailTrace_6939656 : CollatzResearch.WordTrace tailWord_6939656 prefixEnd_6939656 395931011650867310853901 := by
  unfold tailWord_6939656
  simp only [CollatzResearch.WordTrace]
  refine ⟨126555024073409492865703411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168740032097879323820937881 126555024073409492865703411)
  ·
    refine ⟨189832536110114239298555117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126555024073409492865703411 189832536110114239298555117)
    ·
      refine ⟨71187201041292839736958169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189832536110114239298555117 71187201041292839736958169)
      ·
        refine ⟨53390400780969629802718627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71187201041292839736958169 53390400780969629802718627)
        ·
          refine ⟨80085601171454444704077941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53390400780969629802718627 80085601171454444704077941)
          ·
            refine ⟨7508025109823854191007307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 80085601171454444704077941 7508025109823854191007307)
            ·
              refine ⟨11262037664735781286510961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7508025109823854191007307 11262037664735781286510961)
              ·
                refine ⟨8446528248551835964883221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11262037664735781286510961 8446528248551835964883221)
                ·
                  refine ⟨395931011650867310853901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8446528248551835964883221 395931011650867310853901)
                  ·
                    rfl

theorem cell23_6939656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 1, 2, 6].length) (baseStart_6939656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6939656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6939656 prefixEnd_6939656 := by exact prefixLift 6939656
  have htrace : WordTrace (prefixWord ++ tailWord_6939656) baseStart_6939656 baseEnd_6939656 := by
    simpa [prefixWord, tailWord_6939656, baseEnd_6939656] using wordTrace_append hprefix tailTrace_6939656
  have hstable : (prefixWord ++ tailWord_6939656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6939656).length < 2 ^ (prefixWord ++ tailWord_6939656).sum := by decide
  have hdescent : baseEnd_6939656 < baseStart_6939656 := by decide
  rcases family_descends (prefixWord ++ tailWord_6939656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6939706 : List Nat := [3, 1, 1, 1, 3, 1, 4, 3, 1, 1, 4]
def baseStart_6939706 : Nat := 118140960795 + 6939706 * 2 ^ 59
def prefixEnd_6939706 : Nat := 4983230072969 + 3 ^ 40 * 6939706 * 2
def baseEnd_6939706 : Nat := 3563404778890530602059879

theorem tailTrace_6939706 : CollatzResearch.WordTrace tailWord_6939706 prefixEnd_6939706 3563404778890530602059879 := by
  unfold tailWord_6939706
  simp only [CollatzResearch.WordTrace]
  refine ⟨63277967949159461067681743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168741247864425229513817981 63277967949159461067681743)
  ·
    refine ⟨94916951923739191601522615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63277967949159461067681743 94916951923739191601522615)
    ·
      refine ⟨142375427885608787402283923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94916951923739191601522615 142375427885608787402283923)
      ·
        refine ⟨213563141828413181103425885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142375427885608787402283923 213563141828413181103425885)
        ·
          refine ⟨80086178185654942913784707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 213563141828413181103425885 80086178185654942913784707)
          ·
            refine ⟨120129267278482414370677061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80086178185654942913784707 120129267278482414370677061)
            ·
              refine ⟨22524237614715452694501949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 120129267278482414370677061 22524237614715452694501949)
              ·
                refine ⟨8446589105518294760438231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22524237614715452694501949 8446589105518294760438231)
                ·
                  refine ⟨12669883658277442140657347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8446589105518294760438231 12669883658277442140657347)
                  ·
                    refine ⟨19004825487416163210986021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12669883658277442140657347 19004825487416163210986021)
                    ·
                      refine ⟨3563404778890530602059879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19004825487416163210986021 3563404778890530602059879)
                      ·
                        rfl

theorem cell23_6939706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 3, 1, 1, 4].length) (baseStart_6939706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6939706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6939706 prefixEnd_6939706 := by exact prefixLift 6939706
  have htrace : WordTrace (prefixWord ++ tailWord_6939706) baseStart_6939706 baseEnd_6939706 := by
    simpa [prefixWord, tailWord_6939706, baseEnd_6939706] using wordTrace_append hprefix tailTrace_6939706
  have hstable : (prefixWord ++ tailWord_6939706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6939706).length < 2 ^ (prefixWord ++ tailWord_6939706).sum := by decide
  have hdescent : baseEnd_6939706 < baseStart_6939706 := by decide
  rcases family_descends (prefixWord ++ tailWord_6939706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6939710 : List Nat := [4, 2, 1, 3, 1, 2, 1, 2, 2, 3, 2]
def baseStart_6939710 : Nat := 118140960795 + 6939710 * 2 ^ 59
def prefixEnd_6939710 : Nat := 4983230072969 + 3 ^ 40 * 6939710 * 2
def baseEnd_6939710 : Nat := 3563406832813148586409861

theorem tailTrace_6939710 : CollatzResearch.WordTrace tailWord_6939710 prefixEnd_6939710 3563406832813148586409861 := by
  unfold tailWord_6939710
  simp only [CollatzResearch.WordTrace]
  refine ⟨31639002211077919119234073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168741345125748901969248389 31639002211077919119234073)
  ·
    refine ⟨23729251658308439339425555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31639002211077919119234073 23729251658308439339425555)
    ·
      refine ⟨35593877487462659009138333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23729251658308439339425555 35593877487462659009138333)
      ·
        refine ⟨13347704057798497128426875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35593877487462659009138333 13347704057798497128426875)
        ·
          refine ⟨20021556086697745692640313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13347704057798497128426875 20021556086697745692640313)
          ·
            refine ⟨15016167065023309269480235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20021556086697745692640313 15016167065023309269480235)
            ·
              refine ⟨22524250597534963904220353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15016167065023309269480235 22524250597534963904220353)
              ·
                refine ⟨16893187948151222928165265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22524250597534963904220353 16893187948151222928165265)
                ·
                  refine ⟨12669890961113417196123949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16893187948151222928165265 12669890961113417196123949)
                  ·
                    refine ⟨4751209110417531448546481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12669890961113417196123949 4751209110417531448546481)
                    ·
                      refine ⟨3563406832813148586409861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4751209110417531448546481 3563406832813148586409861)
                      ·
                        rfl

theorem cell23_6939710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 2, 2, 3, 2].length) (baseStart_6939710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6939710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6939710 prefixEnd_6939710 := by exact prefixLift 6939710
  have htrace : WordTrace (prefixWord ++ tailWord_6939710) baseStart_6939710 baseEnd_6939710 := by
    simpa [prefixWord, tailWord_6939710, baseEnd_6939710] using wordTrace_append hprefix tailTrace_6939710
  have hstable : (prefixWord ++ tailWord_6939710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6939710).length < 2 ^ (prefixWord ++ tailWord_6939710).sum := by decide
  have hdescent : baseEnd_6939710 < baseStart_6939710 := by decide
  rcases family_descends (prefixWord ++ tailWord_6939710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6939719 : List Nat := [1, 1, 4, 1, 3, 2, 1, 2, 1, 1, 6]
def baseStart_6939719 : Nat := 118140960795 + 6939719 * 2 ^ 59
def prefixEnd_6939719 : Nat := 4983230072969 + 3 ^ 40 * 6939719 * 2
def baseEnd_6939719 : Nat := 3563411454139039051197319

theorem tailTrace_6939719 : CollatzResearch.WordTrace tailWord_6939719 prefixEnd_6939719 3563411454139039051197319 := by
  unfold tailWord_6939719
  simp only [CollatzResearch.WordTrace]
  refine ⟨253112345945590747490950211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168741563963727164993966807 253112345945590747490950211)
  ·
    refine ⟨379668518918386121236425317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253112345945590747490950211 379668518918386121236425317)
    ·
      refine ⟨71187847297197397731829747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 379668518918386121236425317 71187847297197397731829747)
      ·
        refine ⟨106781770945796096597744621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71187847297197397731829747 106781770945796096597744621)
        ·
          refine ⟨40043164104673536224154233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106781770945796096597744621 40043164104673536224154233)
          ·
            refine ⟨30032373078505152168115675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40043164104673536224154233 30032373078505152168115675)
            ·
              refine ⟨45048559617757728252173513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30032373078505152168115675 45048559617757728252173513)
              ·
                refine ⟨33786419713318296189130135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45048559617757728252173513 33786419713318296189130135)
                ·
                  refine ⟨50679629569977444283695203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33786419713318296189130135 50679629569977444283695203)
                  ·
                    refine ⟨76019444354966166425542805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50679629569977444283695203 76019444354966166425542805)
                    ·
                      refine ⟨3563411454139039051197319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76019444354966166425542805 3563411454139039051197319)
                      ·
                        rfl

theorem cell23_6939719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 2, 1, 1, 6].length) (baseStart_6939719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6939719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6939719 prefixEnd_6939719 := by exact prefixLift 6939719
  have htrace : WordTrace (prefixWord ++ tailWord_6939719) baseStart_6939719 baseEnd_6939719 := by
    simpa [prefixWord, tailWord_6939719, baseEnd_6939719] using wordTrace_append hprefix tailTrace_6939719
  have hstable : (prefixWord ++ tailWord_6939719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6939719).length < 2 ^ (prefixWord ++ tailWord_6939719).sum := by decide
  have hdescent : baseEnd_6939719 < baseStart_6939719 := by decide
  rcases family_descends (prefixWord ++ tailWord_6939719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6939726 : List Nat := [4, 1, 1, 1, 1, 3, 2, 2, 3, 2, 3]
def baseStart_6939726 : Nat := 118140960795 + 6939726 * 2 ^ 59
def prefixEnd_6939726 : Nat := 4983230072969 + 3 ^ 40 * 6939726 * 2
def baseEnd_6939726 : Nat := 3563415048503620523809787

theorem tailTrace_6939726 : CollatzResearch.WordTrace tailWord_6939726 prefixEnd_6939726 3563415048503620523809787 := by
  unfold tailWord_6939726
  simp only [CollatzResearch.WordTrace]
  refine ⟨31639075157070673460806879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168741734171043591790970021 31639075157070673460806879)
  ·
    refine ⟨47458612735606010191210319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31639075157070673460806879 47458612735606010191210319)
    ·
      refine ⟨71187919103409015286815479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47458612735606010191210319 71187919103409015286815479)
      ·
        refine ⟨106781878655113522930223219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71187919103409015286815479 106781878655113522930223219)
        ·
          refine ⟨160172817982670284395334829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106781878655113522930223219 160172817982670284395334829)
          ·
            refine ⟨60064806743501356648250561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 160172817982670284395334829 60064806743501356648250561)
            ·
              refine ⟨45048605057626017486187921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60064806743501356648250561 45048605057626017486187921)
              ·
                refine ⟨33786453793219513114640941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45048605057626017486187921 33786453793219513114640941)
                ·
                  refine ⟨12669920172457317417990353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33786453793219513114640941 12669920172457317417990353)
                  ·
                    refine ⟨9502440129342988063492765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12669920172457317417990353 9502440129342988063492765)
                    ·
                      refine ⟨3563415048503620523809787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9502440129342988063492765 3563415048503620523809787)
                      ·
                        rfl

theorem cell23_6939726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 2, 3, 2, 3].length) (baseStart_6939726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6939726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6939726 prefixEnd_6939726 := by exact prefixLift 6939726
  have htrace : WordTrace (prefixWord ++ tailWord_6939726) baseStart_6939726 baseEnd_6939726 := by
    simpa [prefixWord, tailWord_6939726, baseEnd_6939726] using wordTrace_append hprefix tailTrace_6939726
  have hstable : (prefixWord ++ tailWord_6939726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6939726).length < 2 ^ (prefixWord ++ tailWord_6939726).sum := by decide
  have hdescent : baseEnd_6939726 < baseStart_6939726 := by decide
  rcases family_descends (prefixWord ++ tailWord_6939726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6939746 : List Nat := [3, 3, 2, 2, 1, 1, 2, 9]
def baseStart_6939746 : Nat := 118140960795 + 6939746 * 2 ^ 59
def prefixEnd_6939746 : Nat := 4983230072969 + 3 ^ 40 * 6939746 * 2
def baseEnd_6939746 : Nat := 131978715485804090576285

theorem tailTrace_6939746 : CollatzResearch.WordTrace tailWord_6939746 prefixEnd_6939746 131978715485804090576285 := by
  unfold tailWord_6939746
  simp only [CollatzResearch.WordTrace]
  refine ⟨63278332679123232775545773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168742220477661954068122061 63278332679123232775545773)
  ·
    refine ⟨23729374754671212290829665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63278332679123232775545773 23729374754671212290829665)
    ·
      refine ⟨17797031066003409218122249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23729374754671212290829665 17797031066003409218122249)
      ·
        refine ⟨13347773299502556913591687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17797031066003409218122249 13347773299502556913591687)
        ·
          refine ⟨20021659949253835370387531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13347773299502556913591687 20021659949253835370387531)
          ·
            refine ⟨30032489923880753055581297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20021659949253835370387531 30032489923880753055581297)
            ·
              refine ⟨22524367442910564791685973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30032489923880753055581297 22524367442910564791685973)
              ·
                refine ⟨131978715485804090576285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22524367442910564791685973 131978715485804090576285)
                ·
                  rfl

theorem cell23_6939746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 9].length) (baseStart_6939746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6939746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6939746 prefixEnd_6939746 := by exact prefixLift 6939746
  have htrace : WordTrace (prefixWord ++ tailWord_6939746) baseStart_6939746 baseEnd_6939746 := by
    simpa [prefixWord, tailWord_6939746, baseEnd_6939746] using wordTrace_append hprefix tailTrace_6939746
  have hstable : (prefixWord ++ tailWord_6939746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6939746).length < 2 ^ (prefixWord ++ tailWord_6939746).sum := by decide
  have hdescent : baseEnd_6939746 < baseStart_6939746 := by decide
  rcases family_descends (prefixWord ++ tailWord_6939746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6939756 : List Nat := [2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 3]
def baseStart_6939756 : Nat := 118140960795 + 6939756 * 2 ^ 59
def prefixEnd_6939756 : Nat := 4983230072969 + 3 ^ 40 * 6939756 * 2
def baseEnd_6939756 : Nat := 3563430452923255406434649

theorem tailTrace_6939756 : CollatzResearch.WordTrace tailWord_6939756 prefixEnd_6939756 3563430452923255406434649 := by
  unfold tailWord_6939756
  simp only [CollatzResearch.WordTrace]
  refine ⟨126556847723228351405023561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168742463630971135206698081 126556847723228351405023561)
  ·
    refine ⟨94917635792421263553767671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126556847723228351405023561 94917635792421263553767671)
    ·
      refine ⟨142376453688631895330651507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94917635792421263553767671 142376453688631895330651507)
      ·
        refine ⟨213564680532947842995977261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142376453688631895330651507 213564680532947842995977261)
        ·
          refine ⟨80086755199855441123491473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 213564680532947842995977261 80086755199855441123491473)
          ·
            refine ⟨60065066399891580842618605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80086755199855441123491473 60065066399891580842618605)
            ·
              refine ⟨22524399899959342815981977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60065066399891580842618605 22524399899959342815981977)
              ·
                refine ⟨16893299924969507111986483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22524399899959342815981977 16893299924969507111986483)
                ·
                  refine ⟨25339949887454260667979725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16893299924969507111986483 25339949887454260667979725)
                  ·
                    refine ⟨9502481207795347750492397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25339949887454260667979725 9502481207795347750492397)
                    ·
                      refine ⟨3563430452923255406434649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9502481207795347750492397 3563430452923255406434649)
                      ·
                        rfl

theorem cell23_6939756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 3].length) (baseStart_6939756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6939756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6939756 prefixEnd_6939756 := by exact prefixLift 6939756
  have htrace : WordTrace (prefixWord ++ tailWord_6939756) baseStart_6939756 baseEnd_6939756 := by
    simpa [prefixWord, tailWord_6939756, baseEnd_6939756] using wordTrace_append hprefix tailTrace_6939756
  have hstable : (prefixWord ++ tailWord_6939756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6939756).length < 2 ^ (prefixWord ++ tailWord_6939756).sum := by decide
  have hdescent : baseEnd_6939756 < baseStart_6939756 := by decide
  rcases family_descends (prefixWord ++ tailWord_6939756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6939779 : List Nat := [1, 1, 1, 3, 3, 2, 1, 1, 1, 5, 4]
def baseStart_6939779 : Nat := 118140960795 + 6939779 * 2 ^ 59
def prefixEnd_6939779 : Nat := 4983230072969 + 3 ^ 40 * 6939779 * 2
def baseEnd_6939779 : Nat := 3563442262978308816447043

theorem tailTrace_6939779 : CollatzResearch.WordTrace tailWord_6939779 prefixEnd_6939779 3563442262978308816447043 := by
  unfold tailWord_6939779
  simp only [CollatzResearch.WordTrace]
  refine ⟨253114534325373377738134391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168743022883582251825422927 253114534325373377738134391)
  ·
    refine ⟨379671801488060066607201587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253114534325373377738134391 379671801488060066607201587)
    ·
      refine ⟨569507702232090099910802381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379671801488060066607201587 569507702232090099910802381)
      ·
        refine ⟨213565388337033787466550893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 569507702232090099910802381 213565388337033787466550893)
        ·
          refine ⟨80087020626387670299956585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 213565388337033787466550893 80087020626387670299956585)
          ·
            refine ⟨60065265469790752724967439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80087020626387670299956585 60065265469790752724967439)
            ·
              refine ⟨90097898204686129087451159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60065265469790752724967439 90097898204686129087451159)
              ·
                refine ⟨135146847307029193631176739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90097898204686129087451159 135146847307029193631176739)
                ·
                  refine ⟨202720270960543790446765109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 135146847307029193631176739 202720270960543790446765109)
                  ·
                    refine ⟨19005025402550980354384229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 202720270960543790446765109 19005025402550980354384229)
                    ·
                      refine ⟨3563442262978308816447043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19005025402550980354384229 3563442262978308816447043)
                      ·
                        rfl

theorem cell23_6939779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 5, 4].length) (baseStart_6939779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6939779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6939779 prefixEnd_6939779 := by exact prefixLift 6939779
  have htrace : WordTrace (prefixWord ++ tailWord_6939779) baseStart_6939779 baseEnd_6939779 := by
    simpa [prefixWord, tailWord_6939779, baseEnd_6939779] using wordTrace_append hprefix tailTrace_6939779
  have hstable : (prefixWord ++ tailWord_6939779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6939779).length < 2 ^ (prefixWord ++ tailWord_6939779).sum := by decide
  have hdescent : baseEnd_6939779 < baseStart_6939779 := by decide
  rcases family_descends (prefixWord ++ tailWord_6939779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6939790 : List Nat := [4, 1, 1, 3, 2, 1, 2, 3, 2, 1, 3]
def baseStart_6939790 : Nat := 118140960795 + 6939790 * 2 ^ 59
def prefixEnd_6939790 : Nat := 4983230072969 + 3 ^ 40 * 6939790 * 2
def baseEnd_6939790 : Nat := 3563447911265508273409493

theorem tailTrace_6939790 : CollatzResearch.WordTrace tailWord_6939790 prefixEnd_6939790 3563447911265508273409493 := by
  unfold tailWord_6939790
  simp only [CollatzResearch.WordTrace]
  refine ⟨31639366941041690827098103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168743290352222351077856549 31639366941041690827098103)
  ·
    refine ⟨47459050411562536240647155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31639366941041690827098103 47459050411562536240647155)
    ·
      refine ⟨71188575617343804360970733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47459050411562536240647155 71188575617343804360970733)
      ·
        refine ⟨26695715856503926635364025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71188575617343804360970733 26695715856503926635364025)
        ·
          refine ⟨20021786892377944976523019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26695715856503926635364025 20021786892377944976523019)
          ·
            refine ⟨30032680338566917464784529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20021786892377944976523019 30032680338566917464784529)
            ·
              refine ⟨22524510253925188098588397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30032680338566917464784529 22524510253925188098588397)
              ·
                refine ⟨8446691345221945536970649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22524510253925188098588397 8446691345221945536970649)
                ·
                  refine ⟨6335018508916459152727987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8446691345221945536970649 6335018508916459152727987)
                  ·
                    refine ⟨9502527763374688729091981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6335018508916459152727987 9502527763374688729091981)
                    ·
                      refine ⟨3563447911265508273409493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9502527763374688729091981 3563447911265508273409493)
                      ·
                        rfl

theorem cell23_6939790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 3, 2, 1, 3].length) (baseStart_6939790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6939790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6939790 prefixEnd_6939790 := by exact prefixLift 6939790
  have htrace : WordTrace (prefixWord ++ tailWord_6939790) baseStart_6939790 baseEnd_6939790 := by
    simpa [prefixWord, tailWord_6939790, baseEnd_6939790] using wordTrace_append hprefix tailTrace_6939790
  have hstable : (prefixWord ++ tailWord_6939790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6939790).length < 2 ^ (prefixWord ++ tailWord_6939790).sum := by decide
  have hdescent : baseEnd_6939790 < baseStart_6939790 := by decide
  rcases family_descends (prefixWord ++ tailWord_6939790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6939813 : List Nat := [1, 3, 1, 2, 1, 4, 2, 2, 1, 4, 2]
def baseStart_6939813 : Nat := 118140960795 + 6939813 * 2 ^ 59
def prefixEnd_6939813 : Nat := 4983230072969 + 3 ^ 40 * 6939813 * 2
def baseEnd_6939813 : Nat := 3563459721320561683421887

theorem tailTrace_6939813 : CollatzResearch.WordTrace tailWord_6939813 prefixEnd_6939813 3563459721320561683421887 := by
  unfold tailWord_6939813
  simp only [CollatzResearch.WordTrace]
  refine ⟨253115774407250201544872093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168743849604833467696581395 253115774407250201544872093)
  ·
    refine ⟨94918415402718825579327035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 253115774407250201544872093 94918415402718825579327035)
    ·
      refine ⟨142377623104078238368990553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94918415402718825579327035 142377623104078238368990553)
      ·
        refine ⟨106783217328058678776742915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142377623104078238368990553 106783217328058678776742915)
        ·
          refine ⟨160174825992088018165114373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106783217328058678776742915 160174825992088018165114373)
          ·
            refine ⟨30032779873516503405958945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 160174825992088018165114373 30032779873516503405958945)
            ·
              refine ⟨22524584905137377554469209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30032779873516503405958945 22524584905137377554469209)
              ·
                refine ⟨16893438678853033165851907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22524584905137377554469209 16893438678853033165851907)
                ·
                  refine ⟨25340158018279549748777861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16893438678853033165851907 25340158018279549748777861)
                  ·
                    refine ⟨4751279628427415577895849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25340158018279549748777861 4751279628427415577895849)
                    ·
                      refine ⟨3563459721320561683421887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4751279628427415577895849 3563459721320561683421887)
                      ·
                        rfl

theorem cell23_6939813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 2, 1, 4, 2].length) (baseStart_6939813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6939813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6939813 prefixEnd_6939813 := by exact prefixLift 6939813
  have htrace : WordTrace (prefixWord ++ tailWord_6939813) baseStart_6939813 baseEnd_6939813 := by
    simpa [prefixWord, tailWord_6939813, baseEnd_6939813] using wordTrace_append hprefix tailTrace_6939813
  have hstable : (prefixWord ++ tailWord_6939813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6939813).length < 2 ^ (prefixWord ++ tailWord_6939813).sum := by decide
  have hdescent : baseEnd_6939813 < baseStart_6939813 := by decide
  rcases family_descends (prefixWord ++ tailWord_6939813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6939826 : List Nat := [3, 2, 1, 1, 1, 4, 1, 2, 2, 2, 4]
def baseStart_6939826 : Nat := 118140960795 + 6939826 * 2 ^ 59
def prefixEnd_6939826 : Nat := 4983230072969 + 3 ^ 40 * 6939826 * 2
def baseEnd_6939826 : Nat := 3563466396569070132559327

theorem tailTrace_6939826 : CollatzResearch.WordTrace tailWord_6939826 prefixEnd_6939826 3563466396569070132559327 := by
  unfold tailWord_6939826
  simp only [CollatzResearch.WordTrace]
  refine ⟨63279062139050776191273833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168744165704135403176730221 63279062139050776191273833)
  ·
    refine ⟨47459296604288082143455375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63279062139050776191273833 47459296604288082143455375)
    ·
      refine ⟨71188944906432123215183063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47459296604288082143455375 71188944906432123215183063)
      ·
        refine ⟨106783417359648184822774595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71188944906432123215183063 106783417359648184822774595)
        ·
          refine ⟨160175126039472277234161893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106783417359648184822774595 160175126039472277234161893)
          ·
            refine ⟨30032836132401051981405355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 160175126039472277234161893 30032836132401051981405355)
            ·
              refine ⟨45049254198601577972108033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30032836132401051981405355 45049254198601577972108033)
              ·
                refine ⟨33786940648951183479081025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45049254198601577972108033 33786940648951183479081025)
                ·
                  refine ⟨25340205486713387609310769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33786940648951183479081025 25340205486713387609310769)
                  ·
                    refine ⟨19005154115035040706983077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25340205486713387609310769 19005154115035040706983077)
                    ·
                      refine ⟨3563466396569070132559327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19005154115035040706983077 3563466396569070132559327)
                      ·
                        rfl

theorem cell23_6939826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 2, 2, 2, 4].length) (baseStart_6939826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6939826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6939826 prefixEnd_6939826 := by exact prefixLift 6939826
  have htrace : WordTrace (prefixWord ++ tailWord_6939826) baseStart_6939826 baseEnd_6939826 := by
    simpa [prefixWord, tailWord_6939826, baseEnd_6939826] using wordTrace_append hprefix tailTrace_6939826
  have hstable : (prefixWord ++ tailWord_6939826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6939826).length < 2 ^ (prefixWord ++ tailWord_6939826).sum := by decide
  have hdescent : baseEnd_6939826 < baseStart_6939826 := by decide
  rcases family_descends (prefixWord ++ tailWord_6939826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6939836 : List Nat := [2, 2, 2, 3, 2, 1, 1, 3, 7]
def baseStart_6939836 : Nat := 118140960795 + 6939836 * 2 ^ 59
def prefixEnd_6939836 : Nat := 4983230072969 + 3 ^ 40 * 6939836 * 2
def baseEnd_6939836 : Nat := 395941281263957232603809

theorem tailTrace_6939836 : CollatzResearch.WordTrace tailWord_6939836 prefixEnd_6939836 395941281263957232603809 := by
  unfold tailWord_6939836
  simp only [CollatzResearch.WordTrace]
  refine ⟨126558306643083438236479681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168744408857444584315306241 126558306643083438236479681)
  ·
    refine ⟨94918729982312578677359761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126558306643083438236479681 94918729982312578677359761)
    ·
      refine ⟨71189047486734434008019821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94918729982312578677359761 71189047486734434008019821)
      ·
        refine ⟨26695892807525412753007433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71189047486734434008019821 26695892807525412753007433)
        ·
          refine ⟨20021919605644059564755575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26695892807525412753007433 20021919605644059564755575)
          ·
            refine ⟨30032879408466089347133363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20021919605644059564755575 30032879408466089347133363)
            ·
              refine ⟨45049319112699134020700045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30032879408466089347133363 45049319112699134020700045)
              ·
                refine ⟨16893494667262175257762517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45049319112699134020700045 16893494667262175257762517)
                ·
                  refine ⟨395941281263957232603809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16893494667262175257762517 395941281263957232603809)
                  ·
                    rfl

theorem cell23_6939836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 3, 7].length) (baseStart_6939836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6939836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6939836 prefixEnd_6939836 := by exact prefixLift 6939836
  have htrace : WordTrace (prefixWord ++ tailWord_6939836) baseStart_6939836 baseEnd_6939836 := by
    simpa [prefixWord, tailWord_6939836, baseEnd_6939836] using wordTrace_append hprefix tailTrace_6939836
  have hstable : (prefixWord ++ tailWord_6939836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6939836).length < 2 ^ (prefixWord ++ tailWord_6939836).sum := by decide
  have hdescent : baseEnd_6939836 < baseStart_6939836 := by decide
  rcases family_descends (prefixWord ++ tailWord_6939836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6939859 : List Nat := [1, 1, 1, 2, 1, 1, 1, 6, 1, 1, 7]
def baseStart_6939859 : Nat := 118140960795 + 6939859 * 2 ^ 59
def prefixEnd_6939859 : Nat := 4983230072969 + 3 ^ 40 * 6939859 * 2
def baseEnd_6939859 : Nat := 3563483341430668503446675

theorem tailTrace_6939859 : CollatzResearch.WordTrace tailWord_6939859 prefixEnd_6939859 3563483341430668503446675 := by
  unfold tailWord_6939859
  simp only [CollatzResearch.WordTrace]
  refine ⟨253117452165083551401046631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168744968110055700934031087 253117452165083551401046631)
  ·
    refine ⟨379676178247625327101569947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253117452165083551401046631 379676178247625327101569947)
    ·
      refine ⟨569514267371437990652354921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379676178247625327101569947 569514267371437990652354921)
      ·
        refine ⟨427135700528578492989266191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 569514267371437990652354921 427135700528578492989266191)
        ·
          refine ⟨640703550792867739483899287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 427135700528578492989266191 640703550792867739483899287)
          ·
            refine ⟨961055326189301609225848931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 640703550792867739483899287 961055326189301609225848931)
            ·
              refine ⟨1441582989283952413838773397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 961055326189301609225848931 1441582989283952413838773397)
              ·
                refine ⟨67574202622685269398692503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1441582989283952413838773397 67574202622685269398692503)
                ·
                  refine ⟨101361303934027904098038755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67574202622685269398692503 101361303934027904098038755)
                  ·
                    refine ⟨152041955901041856147058133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 101361303934027904098038755 152041955901041856147058133)
                    ·
                      refine ⟨3563483341430668503446675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 152041955901041856147058133 3563483341430668503446675)
                      ·
                        rfl

theorem cell23_6939859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 6, 1, 1, 7].length) (baseStart_6939859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6939859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6939859 prefixEnd_6939859 := by exact prefixLift 6939859
  have htrace : WordTrace (prefixWord ++ tailWord_6939859) baseStart_6939859 baseEnd_6939859 := by
    simpa [prefixWord, tailWord_6939859, baseEnd_6939859] using wordTrace_append hprefix tailTrace_6939859
  have hstable : (prefixWord ++ tailWord_6939859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6939859).length < 2 ^ (prefixWord ++ tailWord_6939859).sum := by decide
  have hdescent : baseEnd_6939859 < baseStart_6939859 := by decide
  rcases family_descends (prefixWord ++ tailWord_6939859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6939866 : List Nat := [3, 1, 1, 2, 2, 1, 1, 5, 2, 5]
def baseStart_6939866 : Nat := 118140960795 + 6939866 * 2 ^ 59
def prefixEnd_6939866 : Nat := 4983230072969 + 3 ^ 40 * 6939866 * 2
def baseEnd_6939866 : Nat := 1187828978598416658686381

theorem tailTrace_6939866 : CollatzResearch.WordTrace tailWord_6939866 prefixEnd_6939866 1187828978598416658686381 := by
  unfold tailWord_6939866
  simp only [CollatzResearch.WordTrace]
  refine ⟨63279426869014547899137863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168745138317372127731034301 63279426869014547899137863)
  ·
    refine ⟨94919140303521821848706795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63279426869014547899137863 94919140303521821848706795)
    ·
      refine ⟨142378710455282732773060193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94919140303521821848706795 142378710455282732773060193)
      ·
        refine ⟨106784032841462049579795145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142378710455282732773060193 106784032841462049579795145)
        ·
          refine ⟨80088024631096537184846359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106784032841462049579795145 80088024631096537184846359)
          ·
            refine ⟨120132036946644805777269539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80088024631096537184846359 120132036946644805777269539)
            ·
              refine ⟨180198055419967208665904309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120132036946644805777269539 180198055419967208665904309)
              ·
                refine ⟨16893567695621925812428529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 180198055419967208665904309 16893567695621925812428529)
                ·
                  refine ⟨12670175771716444359321397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16893567695621925812428529 12670175771716444359321397)
                  ·
                    refine ⟨1187828978598416658686381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12670175771716444359321397 1187828978598416658686381)
                    ·
                      rfl

theorem cell23_6939866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 5, 2, 5].length) (baseStart_6939866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6939866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6939866 prefixEnd_6939866 := by exact prefixLift 6939866
  have htrace : WordTrace (prefixWord ++ tailWord_6939866) baseStart_6939866 baseEnd_6939866 := by
    simpa [prefixWord, tailWord_6939866, baseEnd_6939866] using wordTrace_append hprefix tailTrace_6939866
  have hstable : (prefixWord ++ tailWord_6939866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6939866).length < 2 ^ (prefixWord ++ tailWord_6939866).sum := by decide
  have hdescent : baseEnd_6939866 < baseStart_6939866 := by decide
  rcases family_descends (prefixWord ++ tailWord_6939866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6939974 : List Nat := [6, 1, 1, 3, 1, 1, 1, 1, 1, 4, 3]
def baseStart_6939974 : Nat := 118140960795 + 6939974 * 2 ^ 59
def prefixEnd_6939974 : Nat := 4983230072969 + 3 ^ 40 * 6939974 * 2
def baseEnd_6939974 : Nat := 3563542391705935553508647

theorem tailTrace_6939974 : CollatzResearch.WordTrace tailWord_6939974 prefixEnd_6939974 3563542391705935553508647 := by
  unfold tailWord_6939974
  simp only [CollatzResearch.WordTrace]
  refine ⟨7910051454989591438796343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 168747764373111284027655317 7910051454989591438796343)
  ·
    refine ⟨11865077182484387158194515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7910051454989591438796343 11865077182484387158194515)
    ·
      refine ⟨17797615773726580737291773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11865077182484387158194515 17797615773726580737291773)
      ·
        refine ⟨6674105915147467776484415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17797615773726580737291773 6674105915147467776484415)
        ·
          refine ⟨10011158872721201664726623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6674105915147467776484415 10011158872721201664726623)
          ·
            refine ⟨15016738309081802497089935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10011158872721201664726623 15016738309081802497089935)
            ·
              refine ⟨22525107463622703745634903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15016738309081802497089935 22525107463622703745634903)
              ·
                refine ⟨33787661195434055618452355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22525107463622703745634903 33787661195434055618452355)
                ·
                  refine ⟨50681491793151083427678533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33787661195434055618452355 50681491793151083427678533)
                  ·
                    refine ⟨9502779711215828142689725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50681491793151083427678533 9502779711215828142689725)
                    ·
                      refine ⟨3563542391705935553508647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9502779711215828142689725 3563542391705935553508647)
                      ·
                        rfl

theorem cell23_6939974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_6939974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6939974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6939974 prefixEnd_6939974 := by exact prefixLift 6939974
  have htrace : WordTrace (prefixWord ++ tailWord_6939974) baseStart_6939974 baseEnd_6939974 := by
    simpa [prefixWord, tailWord_6939974, baseEnd_6939974] using wordTrace_append hprefix tailTrace_6939974
  have hstable : (prefixWord ++ tailWord_6939974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6939974).length < 2 ^ (prefixWord ++ tailWord_6939974).sum := by decide
  have hdescent : baseEnd_6939974 < baseStart_6939974 := by decide
  rcases family_descends (prefixWord ++ tailWord_6939974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6939980 : List Nat := [2, 2, 1, 3, 2, 3, 1, 1, 1, 5, 2]
def baseStart_6939980 : Nat := 118140960795 + 6939980 * 2 ^ 59
def prefixEnd_6939980 : Nat := 4983230072969 + 3 ^ 40 * 6939980 * 2
def baseEnd_6939980 : Nat := 3563545472589862530033619

theorem tailTrace_6939980 : CollatzResearch.WordTrace tailWord_6939980 prefixEnd_6939980 3563545472589862530033619 := by
  unfold tailWord_6939980
  simp only [CollatzResearch.WordTrace]
  refine ⟨126560932698822594533100697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168747910265096792710800929 126560932698822594533100697)
  ·
    refine ⟨94920699524116945899825523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126560932698822594533100697 94920699524116945899825523)
    ·
      refine ⟨142381049286175418849738285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94920699524116945899825523 142381049286175418849738285)
      ·
        refine ⟨53392893482315782068651857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142381049286175418849738285 53392893482315782068651857)
        ·
          refine ⟨40044670111736836551488893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53392893482315782068651857 40044670111736836551488893)
          ·
            refine ⟨15016751291901313706808335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40044670111736836551488893 15016751291901313706808335)
            ·
              refine ⟨22525126937851970560212503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15016751291901313706808335 22525126937851970560212503)
              ·
                refine ⟨33787690406777955840318755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22525126937851970560212503 33787690406777955840318755)
                ·
                  refine ⟨50681535610166933760478133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33787690406777955840318755 50681535610166933760478133)
                  ·
                    refine ⟨4751393963453150040044825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50681535610166933760478133 4751393963453150040044825)
                    ·
                      refine ⟨3563545472589862530033619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4751393963453150040044825 3563545472589862530033619)
                      ·
                        rfl

theorem cell23_6939980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 1, 1, 5, 2].length) (baseStart_6939980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6939980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6939980 prefixEnd_6939980 := by exact prefixLift 6939980
  have htrace : WordTrace (prefixWord ++ tailWord_6939980) baseStart_6939980 baseEnd_6939980 := by
    simpa [prefixWord, tailWord_6939980, baseEnd_6939980] using wordTrace_append hprefix tailTrace_6939980
  have hstable : (prefixWord ++ tailWord_6939980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6939980).length < 2 ^ (prefixWord ++ tailWord_6939980).sum := by decide
  have hdescent : baseEnd_6939980 < baseStart_6939980 := by decide
  rcases family_descends (prefixWord ++ tailWord_6939980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6939981 : List Nat := [1, 6, 1, 3, 1, 1, 2, 3, 1, 4]
def baseStart_6939981 : Nat := 118140960795 + 6939981 * 2 ^ 59
def prefixEnd_6939981 : Nat := 4983230072969 + 3 ^ 40 * 6939981 * 2
def baseEnd_6939981 : Nat := 1187848662023505675373705

theorem tailTrace_6939981 : CollatzResearch.WordTrace tailWord_6939981 prefixEnd_6939981 1187848662023505675373705 := by
  unfold tailWord_6939981
  simp only [CollatzResearch.WordTrace]
  refine ⟨253121901870641566236987797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168747934580427710824658531 253121901870641566236987797)
  ·
    refine ⟨11865089150186323417358803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 253121901870641566236987797 11865089150186323417358803)
    ·
      refine ⟨17797633725279485126038205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11865089150186323417358803 17797633725279485126038205)
      ·
        refine ⟨6674112646979806922264327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17797633725279485126038205 6674112646979806922264327)
        ·
          refine ⟨10011168970469710383396491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6674112646979806922264327 10011168970469710383396491)
          ·
            refine ⟨15016753455704565575094737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10011168970469710383396491 15016753455704565575094737)
            ·
              refine ⟨11262565091778424181321053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15016753455704565575094737 11262565091778424181321053)
              ·
                refine ⟨4223461909416909067995395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11262565091778424181321053 4223461909416909067995395)
                ·
                  refine ⟨6335192864125363601993093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4223461909416909067995395 6335192864125363601993093)
                  ·
                    refine ⟨1187848662023505675373705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6335192864125363601993093 1187848662023505675373705)
                    ·
                      rfl

theorem cell23_6939981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 2, 3, 1, 4].length) (baseStart_6939981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6939981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6939981 prefixEnd_6939981 := by exact prefixLift 6939981
  have htrace : WordTrace (prefixWord ++ tailWord_6939981) baseStart_6939981 baseEnd_6939981 := by
    simpa [prefixWord, tailWord_6939981, baseEnd_6939981] using wordTrace_append hprefix tailTrace_6939981
  have hstable : (prefixWord ++ tailWord_6939981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6939981).length < 2 ^ (prefixWord ++ tailWord_6939981).sum := by decide
  have hdescent : baseEnd_6939981 < baseStart_6939981 := by decide
  rcases family_descends (prefixWord ++ tailWord_6939981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6939987 : List Nat := [1, 1, 1, 2, 1, 1, 8, 3, 1, 1, 3]
def baseStart_6939987 : Nat := 118140960795 + 6939987 * 2 ^ 59
def prefixEnd_6939987 : Nat := 4983230072969 + 3 ^ 40 * 6939987 * 2
def baseEnd_6939987 : Nat := 3563549066954444002646087

theorem tailTrace_6939987 : CollatzResearch.WordTrace tailWord_6939987 prefixEnd_6939987 3563549066954444002646087 := by
  unfold tailWord_6939987
  simp only [CollatzResearch.WordTrace]
  refine ⟨253122120708619829261706215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168748080472413219507804143 253122120708619829261706215)
  ·
    refine ⟨379683181062929743892559323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253122120708619829261706215 379683181062929743892559323)
    ·
      refine ⟨569524771594394615838838985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379683181062929743892559323 569524771594394615838838985)
      ·
        refine ⟨427143578695795961879129239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 569524771594394615838838985 427143578695795961879129239)
        ·
          refine ⟨640715368043693942818693859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 427143578695795961879129239 640715368043693942818693859)
          ·
            refine ⟨961073052065540914228040789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 640715368043693942818693859 961073052065540914228040789)
            ·
              refine ⟨11262574828893057588609853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 961073052065540914228040789 11262574828893057588609853)
              ·
                refine ⟨4223465560834896595728695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11262574828893057588609853 4223465560834896595728695)
                ·
                  refine ⟨6335198341252344893593043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4223465560834896595728695 6335198341252344893593043)
                  ·
                    refine ⟨9502797511878517340389565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6335198341252344893593043 9502797511878517340389565)
                    ·
                      refine ⟨3563549066954444002646087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9502797511878517340389565 3563549066954444002646087)
                      ·
                        rfl

theorem cell23_6939987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 8, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 8, 3, 1, 1, 3].length) (baseStart_6939987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6939987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6939987 prefixEnd_6939987 := by exact prefixLift 6939987
  have htrace : WordTrace (prefixWord ++ tailWord_6939987) baseStart_6939987 baseEnd_6939987 := by
    simpa [prefixWord, tailWord_6939987, baseEnd_6939987] using wordTrace_append hprefix tailTrace_6939987
  have hstable : (prefixWord ++ tailWord_6939987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6939987).length < 2 ^ (prefixWord ++ tailWord_6939987).sum := by decide
  have hdescent : baseEnd_6939987 < baseStart_6939987 := by decide
  rcases family_descends (prefixWord ++ tailWord_6939987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6940013 : List Nat := [1, 5, 1, 1, 1, 3, 1, 1, 3, 1, 5]
def baseStart_6940013 : Nat := 118140960795 + 6940013 * 2 ^ 59
def prefixEnd_6940013 : Nat := 4983230072969 + 3 ^ 40 * 6940013 * 2
def baseEnd_6940013 : Nat := 3563562417451460900920967

theorem tailTrace_6940013 : CollatzResearch.WordTrace tailWord_6940013 prefixEnd_6940013 3563562417451460900920967 := by
  unfold tailWord_6940013
  simp only [CollatzResearch.WordTrace]
  refine ⟨253123069006525635702152693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168748712671017090468101795 253123069006525635702152693)
  ·
    refine ⟨23730287719361778347076815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 253123069006525635702152693 23730287719361778347076815)
    ·
      refine ⟨35595431579042667520615223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23730287719361778347076815 35595431579042667520615223)
      ·
        refine ⟨53393147368564001280922835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35595431579042667520615223 53393147368564001280922835)
        ·
          refine ⟨80089721052846001921384253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53393147368564001280922835 80089721052846001921384253)
          ·
            refine ⟨30033645394817250720519095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80089721052846001921384253 30033645394817250720519095)
            ·
              refine ⟨45050468092225876080778643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30033645394817250720519095 45050468092225876080778643)
              ·
                refine ⟨67575702138338814121167965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45050468092225876080778643 67575702138338814121167965)
                ·
                  refine ⟨25340888301877055295437987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67575702138338814121167965 25340888301877055295437987)
                  ·
                    refine ⟨38011332452815582943156981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25340888301877055295437987 38011332452815582943156981)
                    ·
                      refine ⟨3563562417451460900920967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38011332452815582943156981 3563562417451460900920967)
                      ·
                        rfl

theorem cell23_6940013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 1, 3, 1, 5].length) (baseStart_6940013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6940013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6940013 prefixEnd_6940013 := by exact prefixLift 6940013
  have htrace : WordTrace (prefixWord ++ tailWord_6940013) baseStart_6940013 baseEnd_6940013 := by
    simpa [prefixWord, tailWord_6940013, baseEnd_6940013] using wordTrace_append hprefix tailTrace_6940013
  have hstable : (prefixWord ++ tailWord_6940013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6940013).length < 2 ^ (prefixWord ++ tailWord_6940013).sum := by decide
  have hdescent : baseEnd_6940013 < baseStart_6940013 := by decide
  rcases family_descends (prefixWord ++ tailWord_6940013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6940016 : List Nat := [2, 1, 1, 1, 4, 2, 2, 10]
def baseStart_6940016 : Nat := 118140960795 + 6940016 * 2 ^ 59
def prefixEnd_6940016 : Nat := 4983230072969 + 3 ^ 40 * 6940016 * 2
def baseEnd_6940016 : Nat := 131983850292349051451239

theorem tailTrace_6940016 : CollatzResearch.WordTrace tailWord_6940016 prefixEnd_6940016 131983850292349051451239 := by
  unfold tailWord_6940016
  simp only [CollatzResearch.WordTrace]
  refine ⟨126561589212757383607255951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168748785617009844809674601 126561589212757383607255951)
  ·
    refine ⟨189842383819136075410883927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126561589212757383607255951 189842383819136075410883927)
    ·
      refine ⟨284763575728704113116325891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189842383819136075410883927 284763575728704113116325891)
      ·
        refine ⟨427145363593056169674488837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284763575728704113116325891 427145363593056169674488837)
        ·
          refine ⟨80089755673698031813966657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 427145363593056169674488837 80089755673698031813966657)
          ·
            refine ⟨60067316755273523860474993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80089755673698031813966657 60067316755273523860474993)
            ·
              refine ⟨45050487566455142895356245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60067316755273523860474993 45050487566455142895356245)
              ·
                refine ⟨131983850292349051451239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 45050487566455142895356245 131983850292349051451239)
                ·
                  rfl

theorem cell23_6940016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 10].length) (baseStart_6940016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6940016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6940016 prefixEnd_6940016 := by exact prefixLift 6940016
  have htrace : WordTrace (prefixWord ++ tailWord_6940016) baseStart_6940016 baseEnd_6940016 := by
    simpa [prefixWord, tailWord_6940016, baseEnd_6940016] using wordTrace_append hprefix tailTrace_6940016
  have hstable : (prefixWord ++ tailWord_6940016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6940016).length < 2 ^ (prefixWord ++ tailWord_6940016).sum := by decide
  have hdescent : baseEnd_6940016 < baseStart_6940016 := by decide
  rcases family_descends (prefixWord ++ tailWord_6940016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6940026 : List Nat := [3, 1, 1, 1, 1, 1, 2, 2, 2, 2, 7]
def baseStart_6940026 : Nat := 118140960795 + 6940026 * 2 ^ 59
def prefixEnd_6940026 : Nat := 4983230072969 + 3 ^ 40 * 6940026 * 2
def baseEnd_6940026 : Nat := 3563569092699969350058407

theorem tailTrace_6940026 : CollatzResearch.WordTrace tailWord_6940026 prefixEnd_6940026 3563569092699969350058407 := by
  unfold tailWord_6940026
  simp only [CollatzResearch.WordTrace]
  refine ⟨63280885788869634730593983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168749028770319025948250621 63280885788869634730593983)
  ·
    refine ⟨94921328683304452095890975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63280885788869634730593983 94921328683304452095890975)
    ·
      refine ⟨142381993024956678143836463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94921328683304452095890975 142381993024956678143836463)
      ·
        refine ⟨213572989537435017215754695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142381993024956678143836463 213572989537435017215754695)
        ·
          refine ⟨320359484306152525823632043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213572989537435017215754695 320359484306152525823632043)
          ·
            refine ⟨480539226459228788735448065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 320359484306152525823632043 480539226459228788735448065)
            ·
              refine ⟨360404419844421591551586049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 480539226459228788735448065 360404419844421591551586049)
              ·
                refine ⟨270303314883316193663689537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 360404419844421591551586049 270303314883316193663689537)
                ·
                  refine ⟨202727486162487145247767153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 270303314883316193663689537 202727486162487145247767153)
                  ·
                    refine ⟨152045614621865358935825365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 202727486162487145247767153 152045614621865358935825365)
                    ·
                      refine ⟨3563569092699969350058407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 152045614621865358935825365 3563569092699969350058407)
                      ·
                        rfl

theorem cell23_6940026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 2, 2, 7].length) (baseStart_6940026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6940026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6940026 prefixEnd_6940026 := by exact prefixLift 6940026
  have htrace : WordTrace (prefixWord ++ tailWord_6940026) baseStart_6940026 baseEnd_6940026 := by
    simpa [prefixWord, tailWord_6940026, baseEnd_6940026] using wordTrace_append hprefix tailTrace_6940026
  have hstable : (prefixWord ++ tailWord_6940026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6940026).length < 2 ^ (prefixWord ++ tailWord_6940026).sum := by decide
  have hdescent : baseEnd_6940026 < baseStart_6940026 := by decide
  rcases family_descends (prefixWord ++ tailWord_6940026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6940043 : List Nat := [1, 1, 1, 1, 4, 3, 2, 1, 3, 3, 3]
def baseStart_6940043 : Nat := 118140960795 + 6940043 * 2 ^ 59
def prefixEnd_6940043 : Nat := 4983230072969 + 3 ^ 40 * 6940043 * 2
def baseEnd_6940043 : Nat := 3563577821871095783545829

theorem tailTrace_6940043 : CollatzResearch.WordTrace tailWord_6940043 prefixEnd_6940043 3563577821871095783545829 := by
  unfold tailWord_6940043
  simp only [CollatzResearch.WordTrace]
  refine ⟨253124163196416950825744783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168749442130944633883829855 253124163196416950825744783)
  ·
    refine ⟨379686244794625426238617175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253124163196416950825744783 379686244794625426238617175)
    ·
      refine ⟨569529367191938139357925763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379686244794625426238617175 569529367191938139357925763)
      ·
        refine ⟨854294050787907209036888645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 569529367191938139357925763 854294050787907209036888645)
        ·
          refine ⟨160180134522732601694416621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 854294050787907209036888645 160180134522732601694416621)
          ·
            refine ⟨60067550446024725635406233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 160180134522732601694416621 60067550446024725635406233)
            ·
              refine ⟨45050662834518544226554675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60067550446024725635406233 45050662834518544226554675)
              ·
                refine ⟨67575994251777816339832013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45050662834518544226554675 67575994251777816339832013)
                ·
                  refine ⟨25340997844416681127437005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67575994251777816339832013 25340997844416681127437005)
                  ·
                    refine ⟨9502874191656255422788877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25340997844416681127437005 9502874191656255422788877)
                    ·
                      refine ⟨3563577821871095783545829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9502874191656255422788877 3563577821871095783545829)
                      ·
                        rfl

theorem cell23_6940043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 1, 3, 3, 3].length) (baseStart_6940043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6940043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6940043 prefixEnd_6940043 := by exact prefixLift 6940043
  have htrace : WordTrace (prefixWord ++ tailWord_6940043) baseStart_6940043 baseEnd_6940043 := by
    simpa [prefixWord, tailWord_6940043, baseEnd_6940043] using wordTrace_append hprefix tailTrace_6940043
  have hstable : (prefixWord ++ tailWord_6940043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6940043).length < 2 ^ (prefixWord ++ tailWord_6940043).sum := by decide
  have hdescent : baseEnd_6940043 < baseStart_6940043 := by decide
  rcases family_descends (prefixWord ++ tailWord_6940043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6940098 : List Nat := [3, 5, 2, 1, 1, 2, 1, 1, 1, 1, 5]
def baseStart_6940098 : Nat := 118140960795 + 6940098 * 2 ^ 59
def prefixEnd_6940098 : Nat := 4983230072969 + 3 ^ 40 * 6940098 * 2
def baseEnd_6940098 : Nat := 3563606063307093068358077

theorem tailTrace_6940098 : CollatzResearch.WordTrace tailWord_6940098 prefixEnd_6940098 3563606063307093068358077 := by
  unfold tailWord_6940098
  simp only [CollatzResearch.WordTrace]
  refine ⟨63281542302804423804749237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168750779474145130145997965 63281542302804423804749237)
  ·
    refine ⟨5932644590887914731695241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 63281542302804423804749237 5932644590887914731695241)
    ·
      refine ⟨4449483443165936048771431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5932644590887914731695241 4449483443165936048771431)
      ·
        refine ⟨6674225164748904073157147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4449483443165936048771431 6674225164748904073157147)
        ·
          refine ⟨10011337747123356109735721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6674225164748904073157147 10011337747123356109735721)
          ·
            refine ⟨7508503310342517082301791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10011337747123356109735721 7508503310342517082301791)
            ·
              refine ⟨11262754965513775623452687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7508503310342517082301791 11262754965513775623452687)
              ·
                refine ⟨16894132448270663435179031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11262754965513775623452687 16894132448270663435179031)
                ·
                  refine ⟨25341198672405995152768547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16894132448270663435179031 25341198672405995152768547)
                  ·
                    refine ⟨38011798008608992729152821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25341198672405995152768547 38011798008608992729152821)
                    ·
                      refine ⟨3563606063307093068358077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38011798008608992729152821 3563606063307093068358077)
                      ·
                        rfl

theorem cell23_6940098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_6940098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6940098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6940098 prefixEnd_6940098 := by exact prefixLift 6940098
  have htrace : WordTrace (prefixWord ++ tailWord_6940098) baseStart_6940098 baseEnd_6940098 := by
    simpa [prefixWord, tailWord_6940098, baseEnd_6940098] using wordTrace_append hprefix tailTrace_6940098
  have hstable : (prefixWord ++ tailWord_6940098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6940098).length < 2 ^ (prefixWord ++ tailWord_6940098).sum := by decide
  have hdescent : baseEnd_6940098 < baseStart_6940098 := by decide
  rcases family_descends (prefixWord ++ tailWord_6940098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6940103 : List Nat := [1, 1, 4, 1, 1, 3, 1, 3, 2, 1, 5]
def baseStart_6940103 : Nat := 118140960795 + 6940103 * 2 ^ 59
def prefixEnd_6940103 : Nat := 4983230072969 + 3 ^ 40 * 6940103 * 2
def baseEnd_6940103 : Nat := 3563608630710365548795553

theorem tailTrace_6940103 : CollatzResearch.WordTrace tailWord_6940103 prefixEnd_6940103 3563608630710365548795553 := by
  unfold tailWord_6940103
  simp only [CollatzResearch.WordTrace]
  refine ⟨253126351576199581072928963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168750901050799720715285975 253126351576199581072928963)
  ·
    refine ⟨379689527364299371609393445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253126351576199581072928963 379689527364299371609393445)
    ·
      refine ⟨71191786380806132176761271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 379689527364299371609393445 71191786380806132176761271)
      ·
        refine ⟨106787679571209198265141907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71191786380806132176761271 106787679571209198265141907)
        ·
          refine ⟨160181519356813797397712861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106787679571209198265141907 160181519356813797397712861)
          ·
            refine ⟨60068069758805174024142323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 160181519356813797397712861 60068069758805174024142323)
            ·
              refine ⟨90102104638207761036213485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60068069758805174024142323 90102104638207761036213485)
              ·
                refine ⟨33788289239327910388580057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90102104638207761036213485 33788289239327910388580057)
                ·
                  refine ⟨25341216929495932791435043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33788289239327910388580057 25341216929495932791435043)
                  ·
                    refine ⟨38011825394243899187152565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25341216929495932791435043 38011825394243899187152565)
                    ·
                      refine ⟨3563608630710365548795553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38011825394243899187152565 3563608630710365548795553)
                      ·
                        rfl

theorem cell23_6940103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 3, 2, 1, 5].length) (baseStart_6940103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6940103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6940103 prefixEnd_6940103 := by exact prefixLift 6940103
  have htrace : WordTrace (prefixWord ++ tailWord_6940103) baseStart_6940103 baseEnd_6940103 := by
    simpa [prefixWord, tailWord_6940103, baseEnd_6940103] using wordTrace_append hprefix tailTrace_6940103
  have hstable : (prefixWord ++ tailWord_6940103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6940103).length < 2 ^ (prefixWord ++ tailWord_6940103).sum := by decide
  have hdescent : baseEnd_6940103 < baseStart_6940103 := by decide
  rcases family_descends (prefixWord ++ tailWord_6940103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6940104 : List Nat := [2, 1, 3, 1, 3, 1, 5, 1, 1, 3, 2]
def baseStart_6940104 : Nat := 118140960795 + 6940104 * 2 ^ 59
def prefixEnd_6940104 : Nat := 4983230072969 + 3 ^ 40 * 6940104 * 2
def baseEnd_6940104 : Nat := 3563609144191020044883049

theorem tailTrace_6940104 : CollatzResearch.WordTrace tailWord_6940104 prefixEnd_6940104 3563609144191020044883049 := by
  unfold tailWord_6940104
  simp only [CollatzResearch.WordTrace]
  refine ⟨126563194024597979121857683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168750925366130638829143577 126563194024597979121857683)
  ·
    refine ⟨189844791036896968682786525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126563194024597979121857683 189844791036896968682786525)
    ·
      refine ⟨71191796638836363256044947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189844791036896968682786525 71191796638836363256044947)
      ·
        refine ⟨106787694958254544884067421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71191796638836363256044947 106787694958254544884067421)
        ·
          refine ⟨40045385609345454331525283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106787694958254544884067421 40045385609345454331525283)
          ·
            refine ⟨60068078414018181497287925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40045385609345454331525283 60068078414018181497287925)
            ·
              refine ⟨5631382351314204515370743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60068078414018181497287925 5631382351314204515370743)
              ·
                refine ⟨8447073526971306773056115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5631382351314204515370743 8447073526971306773056115)
                ·
                  refine ⟨12670610290456960159584173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8447073526971306773056115 12670610290456960159584173)
                  ·
                    refine ⟨4751478858921360059844065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12670610290456960159584173 4751478858921360059844065)
                    ·
                      refine ⟨3563609144191020044883049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4751478858921360059844065 3563609144191020044883049)
                      ·
                        rfl

theorem cell23_6940104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 5, 1, 1, 3, 2].length) (baseStart_6940104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6940104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6940104 prefixEnd_6940104 := by exact prefixLift 6940104
  have htrace : WordTrace (prefixWord ++ tailWord_6940104) baseStart_6940104 baseEnd_6940104 := by
    simpa [prefixWord, tailWord_6940104, baseEnd_6940104] using wordTrace_append hprefix tailTrace_6940104
  have hstable : (prefixWord ++ tailWord_6940104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6940104).length < 2 ^ (prefixWord ++ tailWord_6940104).sum := by decide
  have hdescent : baseEnd_6940104 < baseStart_6940104 := by decide
  rcases family_descends (prefixWord ++ tailWord_6940104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6940157 : List Nat := [1, 4, 1, 1, 1, 5, 2, 3, 5]
def baseStart_6940157 : Nat := 118140960795 + 6940157 * 2 ^ 59
def prefixEnd_6940157 : Nat := 4983230072969 + 3 ^ 40 * 6940157 * 2
def baseEnd_6940157 : Nat := 395959595407300926391145

theorem tailTrace_6940157 : CollatzResearch.WordTrace tailWord_6940157 prefixEnd_6940157 395959595407300926391145 := by
  unfold tailWord_6940157
  simp only [CollatzResearch.WordTrace]
  refine ⟨253128321118003948295394725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168752214078669298863596483 253128321118003948295394725)
  ·
    refine ⟨47461560209625740305386511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 253128321118003948295394725 47461560209625740305386511)
    ·
      refine ⟨71192340314438610458079767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47461560209625740305386511 71192340314438610458079767)
      ·
        refine ⟨106788510471657915687119651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71192340314438610458079767 106788510471657915687119651)
        ·
          refine ⟨160182765707486873530679477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106788510471657915687119651 160182765707486873530679477)
          ·
            refine ⟨15017134285076894393501201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 160182765707486873530679477 15017134285076894393501201)
            ·
              refine ⟨11262850713807670795125901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15017134285076894393501201 11262850713807670795125901)
              ·
                refine ⟨4223569017677876548172213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11262850713807670795125901 4223569017677876548172213)
                ·
                  refine ⟨395959595407300926391145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4223569017677876548172213 395959595407300926391145)
                  ·
                    rfl

theorem cell23_6940157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 2, 3, 5].length) (baseStart_6940157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6940157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6940157 prefixEnd_6940157 := by exact prefixLift 6940157
  have htrace : WordTrace (prefixWord ++ tailWord_6940157) baseStart_6940157 baseEnd_6940157 := by
    simpa [prefixWord, tailWord_6940157, baseEnd_6940157] using wordTrace_append hprefix tailTrace_6940157
  have hstable : (prefixWord ++ tailWord_6940157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6940157).length < 2 ^ (prefixWord ++ tailWord_6940157).sum := by decide
  have hdescent : baseEnd_6940157 < baseStart_6940157 := by decide
  rcases family_descends (prefixWord ++ tailWord_6940157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6940163 : List Nat := [1, 1, 1, 3, 2, 1, 2, 4, 1, 2, 5]
def baseStart_6940163 : Nat := 118140960795 + 6940163 * 2 ^ 59
def prefixEnd_6940163 : Nat := 4983230072969 + 3 ^ 40 * 6940163 * 2
def baseEnd_6940163 : Nat := 3563639439549635314045277

theorem tailTrace_6940163 : CollatzResearch.WordTrace tailWord_6940163 prefixEnd_6940163 3563639439549635314045277 := by
  unfold tailWord_6940163
  simp only [CollatzResearch.WordTrace]
  refine ⟨253128539955982211320113143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168752359970654807546742095 253128539955982211320113143)
  ·
    refine ⟨379692809933973316980169715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253128539955982211320113143 379692809933973316980169715)
    ·
      refine ⟨569539214900959975470254573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379692809933973316980169715 569539214900959975470254573)
      ·
        refine ⟨213577205587859990801345465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 569539214900959975470254573 213577205587859990801345465)
        ·
          refine ⟨160182904190894993101009099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213577205587859990801345465 160182904190894993101009099)
          ·
            refine ⟨240274356286342489651513649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160182904190894993101009099 240274356286342489651513649)
            ·
              refine ⟨180205767214756867238635237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 240274356286342489651513649 180205767214756867238635237)
              ·
                refine ⟨33788581352766912607244107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 180205767214756867238635237 33788581352766912607244107)
                ·
                  refine ⟨50682872029150368910866161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33788581352766912607244107 50682872029150368910866161)
                  ·
                    refine ⟨38012154021862776683149621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50682872029150368910866161 38012154021862776683149621)
                    ·
                      refine ⟨3563639439549635314045277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38012154021862776683149621 3563639439549635314045277)
                      ·
                        rfl

theorem cell23_6940163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 4, 1, 2, 5].length) (baseStart_6940163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6940163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6940163 prefixEnd_6940163 := by exact prefixLift 6940163
  have htrace : WordTrace (prefixWord ++ tailWord_6940163) baseStart_6940163 baseEnd_6940163 := by
    simpa [prefixWord, tailWord_6940163, baseEnd_6940163] using wordTrace_append hprefix tailTrace_6940163
  have hstable : (prefixWord ++ tailWord_6940163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6940163).length < 2 ^ (prefixWord ++ tailWord_6940163).sum := by decide
  have hdescent : baseEnd_6940163 < baseStart_6940163 := by decide
  rcases family_descends (prefixWord ++ tailWord_6940163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6940233 : List Nat := [1, 2, 1, 1, 2, 2, 1, 3, 1, 1, 8]
def baseStart_6940233 : Nat := 118140960795 + 6940233 * 2 ^ 59
def prefixEnd_6940233 : Nat := 4983230072969 + 3 ^ 40 * 6940233 * 2
def baseEnd_6940233 : Nat := 3563675383195450040169955

theorem tailTrace_6940233 : CollatzResearch.WordTrace tailWord_6940233 prefixEnd_6940233 3563675383195450040169955 := by
  unfold tailWord_6940233
  simp only [CollatzResearch.WordTrace]
  refine ⟨253131093065728613275161353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168754062043819075516774235 253131093065728613275161353)
  ·
    refine ⟨189848319799296459956371015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253131093065728613275161353 189848319799296459956371015)
    ·
      refine ⟨284772479698944689934556523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189848319799296459956371015 284772479698944689934556523)
      ·
        refine ⟨427158719548417034901834785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284772479698944689934556523 427158719548417034901834785)
        ·
          refine ⟨320369039661312776176376089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 427158719548417034901834785 320369039661312776176376089)
          ·
            refine ⟨240276779745984582132282067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 320369039661312776176376089 240276779745984582132282067)
            ·
              refine ⟨360415169618976873198423101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 240276779745984582132282067 360415169618976873198423101)
              ·
                refine ⟨135155688607116327449408663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 360415169618976873198423101 135155688607116327449408663)
                ·
                  refine ⟨202733532910674491174112995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 135155688607116327449408663 202733532910674491174112995)
                  ·
                    refine ⟨304100299366011736761169493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 202733532910674491174112995 304100299366011736761169493)
                    ·
                      refine ⟨3563675383195450040169955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 304100299366011736761169493 3563675383195450040169955)
                      ·
                        rfl

theorem cell23_6940233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 1, 8].length) (baseStart_6940233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6940233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6940233 prefixEnd_6940233 := by exact prefixLift 6940233
  have htrace : WordTrace (prefixWord ++ tailWord_6940233) baseStart_6940233 baseEnd_6940233 := by
    simpa [prefixWord, tailWord_6940233, baseEnd_6940233] using wordTrace_append hprefix tailTrace_6940233
  have hstable : (prefixWord ++ tailWord_6940233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6940233).length < 2 ^ (prefixWord ++ tailWord_6940233).sum := by decide
  have hdescent : baseEnd_6940233 < baseStart_6940233 := by decide
  rcases family_descends (prefixWord ++ tailWord_6940233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6940247 : List Nat := [1, 1, 3, 2, 2, 3, 4, 1, 6]
def baseStart_6940247 : Nat := 118140960795 + 6940247 * 2 ^ 59
def prefixEnd_6940247 : Nat := 4983230072969 + 3 ^ 40 * 6940247 * 2
def baseEnd_6940247 : Nat := 395964730213845887266099

theorem tailTrace_6940247 : CollatzResearch.WordTrace tailWord_6940247 prefixEnd_6940247 395964730213845887266099 := by
  unfold tailWord_6940247
  simp only [CollatzResearch.WordTrace]
  refine ⟨253131603687677893666170995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168754402458451929110780663 253131603687677893666170995)
  ·
    refine ⟨379697405531516840499256493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253131603687677893666170995 379697405531516840499256493)
    ·
      refine ⟨142386527074318815187221185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 379697405531516840499256493 142386527074318815187221185)
      ·
        refine ⟨106789895305739111390415889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142386527074318815187221185 106789895305739111390415889)
        ·
          refine ⟨80092421479304333542811917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106789895305739111390415889 80092421479304333542811917)
          ·
            refine ⟨30034658054739125078554469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80092421479304333542811917 30034658054739125078554469)
            ·
              refine ⟨5631498385263585952228963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30034658054739125078554469 5631498385263585952228963)
              ·
                refine ⟨8447247577895378928343445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5631498385263585952228963 8447247577895378928343445)
                ·
                  refine ⟨395964730213845887266099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8447247577895378928343445 395964730213845887266099)
                  ·
                    rfl

theorem cell23_6940247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 4, 1, 6].length) (baseStart_6940247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6940247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6940247 prefixEnd_6940247 := by exact prefixLift 6940247
  have htrace : WordTrace (prefixWord ++ tailWord_6940247) baseStart_6940247 baseEnd_6940247 := by
    simpa [prefixWord, tailWord_6940247, baseEnd_6940247] using wordTrace_append hprefix tailTrace_6940247
  have hstable : (prefixWord ++ tailWord_6940247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6940247).length < 2 ^ (prefixWord ++ tailWord_6940247).sum := by decide
  have hdescent : baseEnd_6940247 < baseStart_6940247 := by decide
  rcases family_descends (prefixWord ++ tailWord_6940247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6940257 : List Nat := [1, 2, 3, 1, 1, 3, 2, 1, 5, 1, 3]
def baseStart_6940257 : Nat := 118140960795 + 6940257 * 2 ^ 59
def prefixEnd_6940257 : Nat := 4983230072969 + 3 ^ 40 * 6940257 * 2
def baseEnd_6940257 : Nat := 3563687706731157946269845

theorem tailTrace_6940257 : CollatzResearch.WordTrace tailWord_6940257 prefixEnd_6940257 3563687706731157946269845 := by
  unfold tailWord_6940257
  simp only [CollatzResearch.WordTrace]
  refine ⟨253131968417641665374035025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168754645611761110249356683 253131968417641665374035025)
  ·
    refine ⟨189848976313231249030526269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253131968417641665374035025 189848976313231249030526269)
    ·
      refine ⟨71193366117461718386447351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189848976313231249030526269 71193366117461718386447351)
      ·
        refine ⟨106790049176192577579671027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71193366117461718386447351 106790049176192577579671027)
        ·
          refine ⟨160185073764288866369506541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106790049176192577579671027 160185073764288866369506541)
          ·
            refine ⟨60069402661608324888564953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 160185073764288866369506541 60069402661608324888564953)
            ·
              refine ⟨45052051996206243666423715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60069402661608324888564953 45052051996206243666423715)
              ·
                refine ⟨67578077994309365499635573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45052051996206243666423715 67578077994309365499635573)
                ·
                  refine ⟨6335444811966503015590835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67578077994309365499635573 6335444811966503015590835)
                  ·
                    refine ⟨9503167217949754523386253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6335444811966503015590835 9503167217949754523386253)
                    ·
                      refine ⟨3563687706731157946269845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9503167217949754523386253 3563687706731157946269845)
                      ·
                        rfl

theorem cell23_6940257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 1, 5, 1, 3].length) (baseStart_6940257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6940257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6940257 prefixEnd_6940257 := by exact prefixLift 6940257
  have htrace : WordTrace (prefixWord ++ tailWord_6940257) baseStart_6940257 baseEnd_6940257 := by
    simpa [prefixWord, tailWord_6940257, baseEnd_6940257] using wordTrace_append hprefix tailTrace_6940257
  have hstable : (prefixWord ++ tailWord_6940257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6940257).length < 2 ^ (prefixWord ++ tailWord_6940257).sum := by decide
  have hdescent : baseEnd_6940257 < baseStart_6940257 := by decide
  rcases family_descends (prefixWord ++ tailWord_6940257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6940280 : List Nat := [2, 1, 2, 1, 1, 1, 2, 1, 7, 1, 4]
def baseStart_6940280 : Nat := 118140960795 + 6940280 * 2 ^ 59
def prefixEnd_6940280 : Nat := 4983230072969 + 3 ^ 40 * 6940280 * 2
def baseEnd_6940280 : Nat := 3563699516786211356282239

theorem tailTrace_6940280 : CollatzResearch.WordTrace tailWord_6940280 prefixEnd_6940280 3563699516786211356282239 := by
  unfold tailWord_6940280
  simp only [CollatzResearch.WordTrace]
  refine ⟨126566403648279170151061147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168755204864372226868081529 126566403648279170151061147)
  ·
    refine ⟨189849605472418755226591721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126566403648279170151061147 189849605472418755226591721)
    ·
      refine ⟨142387204104314066419943791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189849605472418755226591721 142387204104314066419943791)
      ·
        refine ⟨213580806156471099629915687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142387204104314066419943791 213580806156471099629915687)
        ·
          refine ⟨320371209234706649444873531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213580806156471099629915687 320371209234706649444873531)
          ·
            refine ⟨480556813852059974167310297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 320371209234706649444873531 480556813852059974167310297)
            ·
              refine ⟨360417610389044980625482723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 480556813852059974167310297 360417610389044980625482723)
              ·
                refine ⟨540626415583567470938224085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 360417610389044980625482723 540626415583567470938224085)
                ·
                  refine ⟨12670931615239862600114627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 540626415583567470938224085 12670931615239862600114627)
                  ·
                    refine ⟨19006397422859793900171941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12670931615239862600114627 19006397422859793900171941)
                    ·
                      refine ⟨3563699516786211356282239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19006397422859793900171941 3563699516786211356282239)
                      ·
                        rfl

theorem cell23_6940280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 7, 1, 4].length) (baseStart_6940280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6940280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6940280 prefixEnd_6940280 := by exact prefixLift 6940280
  have htrace : WordTrace (prefixWord ++ tailWord_6940280) baseStart_6940280 baseEnd_6940280 := by
    simpa [prefixWord, tailWord_6940280, baseEnd_6940280] using wordTrace_append hprefix tailTrace_6940280
  have hstable : (prefixWord ++ tailWord_6940280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6940280).length < 2 ^ (prefixWord ++ tailWord_6940280).sum := by decide
  have hdescent : baseEnd_6940280 < baseStart_6940280 := by decide
  rcases family_descends (prefixWord ++ tailWord_6940280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6940300 : List Nat := [2, 2, 1, 2, 1, 1, 4, 1, 3, 1, 5]
def baseStart_6940300 : Nat := 118140960795 + 6940300 * 2 ^ 59
def prefixEnd_6940300 : Nat := 4983230072969 + 3 ^ 40 * 6940300 * 2
def baseEnd_6940300 : Nat := 3563709786399301278032147

theorem tailTrace_6940300 : CollatzResearch.WordTrace tailWord_6940300 prefixEnd_6940300 3563709786399301278032147 := by
  unfold tailWord_6940300
  simp only [CollatzResearch.WordTrace]
  refine ⟨126566768378242941858925177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168755691170990589145233569 126566768378242941858925177)
  ·
    refine ⟨94925076283682206394193883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126566768378242941858925177 94925076283682206394193883)
    ·
      refine ⟨142387614425523309591290825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94925076283682206394193883 142387614425523309591290825)
      ·
        refine ⟨106790710819142482193468119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142387614425523309591290825 106790710819142482193468119)
        ·
          refine ⟨160186066228713723290202179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106790710819142482193468119 160186066228713723290202179)
          ·
            refine ⟨240279099343070584935303269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160186066228713723290202179 240279099343070584935303269)
            ·
              refine ⟨45052331126825734675369363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 240279099343070584935303269 45052331126825734675369363)
              ·
                refine ⟨67578496690238602013054045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45052331126825734675369363 67578496690238602013054045)
                ·
                  refine ⟨25341936258839475754895267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67578496690238602013054045 25341936258839475754895267)
                  ·
                    refine ⟨38012904388259213632342901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25341936258839475754895267 38012904388259213632342901)
                    ·
                      refine ⟨3563709786399301278032147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38012904388259213632342901 3563709786399301278032147)
                      ·
                        rfl

theorem cell23_6940300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 3, 1, 5].length) (baseStart_6940300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6940300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6940300 prefixEnd_6940300 := by exact prefixLift 6940300
  have htrace : WordTrace (prefixWord ++ tailWord_6940300) baseStart_6940300 baseEnd_6940300 := by
    simpa [prefixWord, tailWord_6940300, baseEnd_6940300] using wordTrace_append hprefix tailTrace_6940300
  have hstable : (prefixWord ++ tailWord_6940300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6940300).length < 2 ^ (prefixWord ++ tailWord_6940300).sum := by decide
  have hdescent : baseEnd_6940300 < baseStart_6940300 := by decide
  rcases family_descends (prefixWord ++ tailWord_6940300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6940318 : List Nat := [4, 3, 1, 1, 1, 4, 1, 1, 2, 3, 2]
def baseStart_6940318 : Nat := 118140960795 + 6940318 * 2 ^ 59
def prefixEnd_6940318 : Nat := 4983230072969 + 3 ^ 40 * 6940318 * 2
def baseEnd_6940318 : Nat := 3563719029051082207607065

theorem tailTrace_6940318 : CollatzResearch.WordTrace tailWord_6940318 prefixEnd_6940318 3563719029051082207607065 := by
  unfold tailWord_6940318
  simp only [CollatzResearch.WordTrace]
  refine ⟨31641774158802584099000701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168756128846947115194670405 31641774158802584099000701)
  ·
    refine ⟨11865665309550969037125263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31641774158802584099000701 11865665309550969037125263)
    ·
      refine ⟨17798497964326453555687895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11865665309550969037125263 17798497964326453555687895)
      ·
        refine ⟨26697746946489680333531843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17798497964326453555687895 26697746946489680333531843)
        ·
          refine ⟨40046620419734520500297765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26697746946489680333531843 40046620419734520500297765)
          ·
            refine ⟨7508741328700222593805831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40046620419734520500297765 7508741328700222593805831)
            ·
              refine ⟨11263111993050333890708747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7508741328700222593805831 11263111993050333890708747)
              ·
                refine ⟨16894667989575500836063121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11263111993050333890708747 16894667989575500836063121)
                ·
                  refine ⟨12671000992181625627047341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16894667989575500836063121 12671000992181625627047341)
                  ·
                    refine ⟨4751625372068109610142753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12671000992181625627047341 4751625372068109610142753)
                    ·
                      refine ⟨3563719029051082207607065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4751625372068109610142753 3563719029051082207607065)
                      ·
                        rfl

theorem cell23_6940318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 1, 1, 2, 3, 2].length) (baseStart_6940318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6940318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6940318 prefixEnd_6940318 := by exact prefixLift 6940318
  have htrace : WordTrace (prefixWord ++ tailWord_6940318) baseStart_6940318 baseEnd_6940318 := by
    simpa [prefixWord, tailWord_6940318, baseEnd_6940318] using wordTrace_append hprefix tailTrace_6940318
  have hstable : (prefixWord ++ tailWord_6940318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6940318).length < 2 ^ (prefixWord ++ tailWord_6940318).sum := by decide
  have hdescent : baseEnd_6940318 < baseStart_6940318 := by decide
  rcases family_descends (prefixWord ++ tailWord_6940318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6940328 : List Nat := [2, 1, 7, 1, 1, 1, 1, 3, 1, 5]
def baseStart_6940328 : Nat := 118140960795 + 6940328 * 2 ^ 59
def prefixEnd_6940328 : Nat := 4983230072969 + 3 ^ 40 * 6940328 * 2
def baseEnd_6940328 : Nat := 1187908054619209056160673

theorem tailTrace_6940328 : CollatzResearch.WordTrace tailWord_6940328 prefixEnd_6940328 1187908054619209056160673 := by
  unfold tailWord_6940328
  simp only [CollatzResearch.WordTrace]
  refine ⟨126567279000192222249934819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168756372000256296333246425 126567279000192222249934819)
  ·
    refine ⟨189850918500288333374902229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126567279000192222249934819 189850918500288333374902229)
    ·
      refine ⟨4449630902350507813474271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 189850918500288333374902229 4449630902350507813474271)
      ·
        refine ⟨6674446353525761720211407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4449630902350507813474271 6674446353525761720211407)
        ·
          refine ⟨10011669530288642580317111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6674446353525761720211407 10011669530288642580317111)
          ·
            refine ⟨15017504295432963870475667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10011669530288642580317111 15017504295432963870475667)
            ·
              refine ⟨22526256443149445805713501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15017504295432963870475667 22526256443149445805713501)
              ·
                refine ⟨8447346166181042177142563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22526256443149445805713501 8447346166181042177142563)
                ·
                  refine ⟨12671019249271563265713845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8447346166181042177142563 12671019249271563265713845)
                  ·
                    refine ⟨1187908054619209056160673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12671019249271563265713845 1187908054619209056160673)
                    ·
                      rfl

theorem cell23_6940328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_6940328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6940328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6940328 prefixEnd_6940328 := by exact prefixLift 6940328
  have htrace : WordTrace (prefixWord ++ tailWord_6940328) baseStart_6940328 baseEnd_6940328 := by
    simpa [prefixWord, tailWord_6940328, baseEnd_6940328] using wordTrace_append hprefix tailTrace_6940328
  have hstable : (prefixWord ++ tailWord_6940328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6940328).length < 2 ^ (prefixWord ++ tailWord_6940328).sum := by decide
  have hdescent : baseEnd_6940328 < baseStart_6940328 := by decide
  rcases family_descends (prefixWord ++ tailWord_6940328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6940348 : List Nat := [2, 2, 2, 3, 1, 2, 2, 4, 1, 2, 2]
def baseStart_6940348 : Nat := 118140960795 + 6940348 * 2 ^ 59
def prefixEnd_6940348 : Nat := 4983230072969 + 3 ^ 40 * 6940348 * 2
def baseEnd_6940348 : Nat := 3563734433470717090231927

theorem tailTrace_6940348 : CollatzResearch.WordTrace tailWord_6940348 prefixEnd_6940348 3563734433470717090231927 := by
  unfold tailWord_6940348
  simp only [CollatzResearch.WordTrace]
  refine ⟨126567643730155993957798849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168756858306874658610398465 126567643730155993957798849)
  ·
    refine ⟨94925732797616995468349137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126567643730155993957798849 94925732797616995468349137)
    ·
      refine ⟨71194299598212746601261853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94925732797616995468349137 71194299598212746601261853)
      ·
        refine ⟨26697862349329779975473195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71194299598212746601261853 26697862349329779975473195)
        ·
          refine ⟨40046793523994669963209793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26697862349329779975473195 40046793523994669963209793)
          ·
            refine ⟨30035095142996002472407345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40046793523994669963209793 30035095142996002472407345)
            ·
              refine ⟨22526321357247001854305509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30035095142996002472407345 22526321357247001854305509)
              ·
                refine ⟨4223685254483812847682283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22526321357247001854305509 4223685254483812847682283)
                ·
                  refine ⟨6335527881725719271523425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4223685254483812847682283 6335527881725719271523425)
                  ·
                    refine ⟨4751645911294289453642569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6335527881725719271523425 4751645911294289453642569)
                    ·
                      refine ⟨3563734433470717090231927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4751645911294289453642569 3563734433470717090231927)
                      ·
                        rfl

theorem cell23_6940348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 4, 1, 2, 2].length) (baseStart_6940348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6940348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6940348 prefixEnd_6940348 := by exact prefixLift 6940348
  have htrace : WordTrace (prefixWord ++ tailWord_6940348) baseStart_6940348 baseEnd_6940348 := by
    simpa [prefixWord, tailWord_6940348, baseEnd_6940348] using wordTrace_append hprefix tailTrace_6940348
  have hstable : (prefixWord ++ tailWord_6940348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6940348).length < 2 ^ (prefixWord ++ tailWord_6940348).sum := by decide
  have hdescent : baseEnd_6940348 < baseStart_6940348 := by decide
  rcases family_descends (prefixWord ++ tailWord_6940348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6940358 : List Nat := [6, 1, 2, 1, 1, 3, 1, 1, 1, 6]
def baseStart_6940358 : Nat := 118140960795 + 6940358 * 2 ^ 59
def prefixEnd_6940358 : Nat := 4983230072969 + 3 ^ 40 * 6940358 * 2
def baseEnd_6940358 : Nat := 1187913189425754017035627

theorem tailTrace_6940358 : CollatzResearch.WordTrace tailWord_6940358 prefixEnd_6940358 1187913189425754017035627 := by
  unfold tailWord_6940358
  simp only [CollatzResearch.WordTrace]
  refine ⟨7910489130946117488233179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 168757101460183839748974485 7910489130946117488233179)
  ·
    refine ⟨11865733696419176232349769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7910489130946117488233179 11865733696419176232349769)
    ·
      refine ⟨8899300272314382174262327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11865733696419176232349769 8899300272314382174262327)
      ·
        refine ⟨13348950408471573261393491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8899300272314382174262327 13348950408471573261393491)
        ·
          refine ⟨20023425612707359892090237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13348950408471573261393491 20023425612707359892090237)
          ·
            refine ⟨7508784604765259959533839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20023425612707359892090237 7508784604765259959533839)
            ·
              refine ⟨11263176907147889939300759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7508784604765259959533839 11263176907147889939300759)
              ·
                refine ⟨16894765360721834908951139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11263176907147889939300759 16894765360721834908951139)
                ·
                  refine ⟨25342148041082752363426709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16894765360721834908951139 25342148041082752363426709)
                  ·
                    refine ⟨1187913189425754017035627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25342148041082752363426709 1187913189425754017035627)
                    ·
                      rfl

theorem cell23_6940358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_6940358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6940358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6940358 prefixEnd_6940358 := by exact prefixLift 6940358
  have htrace : WordTrace (prefixWord ++ tailWord_6940358) baseStart_6940358 baseEnd_6940358 := by
    simpa [prefixWord, tailWord_6940358, baseEnd_6940358] using wordTrace_append hprefix tailTrace_6940358
  have hstable : (prefixWord ++ tailWord_6940358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6940358).length < 2 ^ (prefixWord ++ tailWord_6940358).sum := by decide
  have hdescent : baseEnd_6940358 < baseStart_6940358 := by decide
  rcases family_descends (prefixWord ++ tailWord_6940358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6940400 : List Nat := [2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 6]
def baseStart_6940400 : Nat := 118140960795 + 6940400 * 2 ^ 59
def prefixEnd_6940400 : Nat := 4983230072969 + 3 ^ 40 * 6940400 * 2
def baseEnd_6940400 : Nat := 3563761134464750886781687

theorem tailTrace_6940400 : CollatzResearch.WordTrace tailWord_6940400 prefixEnd_6940400 3563761134464750886781687 := by
  unfold tailWord_6940400
  simp only [CollatzResearch.WordTrace]
  refine ⟨126568592028061800398245327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168758122704082400530993769 126568592028061800398245327)
  ·
    refine ⟨189852888042092700597367991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126568592028061800398245327 189852888042092700597367991)
    ·
      refine ⟨284779332063139050896051987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189852888042092700597367991 284779332063139050896051987)
      ·
        refine ⟨427168998094708576344077981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284779332063139050896051987 427168998094708576344077981)
        ·
          refine ⟨160188374285515716129029243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 427168998094708576344077981 160188374285515716129029243)
          ·
            refine ⟨240282561428273574193543865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160188374285515716129029243 240282561428273574193543865)
            ·
              refine ⟨180211921071205180645157899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 240282561428273574193543865 180211921071205180645157899)
              ·
                refine ⟨270317881606807770967736849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 180211921071205180645157899 270317881606807770967736849)
                ·
                  refine ⟨202738411205105828225802637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 270317881606807770967736849 202738411205105828225802637)
                  ·
                    refine ⟨76026904201914685584675989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 202738411205105828225802637 76026904201914685584675989)
                    ·
                      refine ⟨3563761134464750886781687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76026904201914685584675989 3563761134464750886781687)
                      ·
                        rfl

theorem cell23_6940400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 6].length) (baseStart_6940400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6940400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6940400 prefixEnd_6940400 := by exact prefixLift 6940400
  have htrace : WordTrace (prefixWord ++ tailWord_6940400) baseStart_6940400 baseEnd_6940400 := by
    simpa [prefixWord, tailWord_6940400, baseEnd_6940400] using wordTrace_append hprefix tailTrace_6940400
  have hstable : (prefixWord ++ tailWord_6940400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6940400).length < 2 ^ (prefixWord ++ tailWord_6940400).sum := by decide
  have hdescent : baseEnd_6940400 < baseStart_6940400 := by decide
  rcases family_descends (prefixWord ++ tailWord_6940400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6940417 : List Nat := [1, 2, 4, 1, 1, 1, 2, 3, 2, 2, 4]
def baseStart_6940417 : Nat := 118140960795 + 6940417 * 2 ^ 59
def prefixEnd_6940417 : Nat := 4983230072969 + 3 ^ 40 * 6940417 * 2
def baseEnd_6940417 : Nat := 3563769863635877320269109

theorem tailTrace_6940417 : CollatzResearch.WordTrace tailWord_6940417 prefixEnd_6940417 3563769863635877320269109 := by
  unfold tailWord_6940417
  simp only [CollatzResearch.WordTrace]
  refine ⟨253137804097062012699859505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168758536064708008466573003 253137804097062012699859505)
  ·
    refine ⟨189853353072796509524894629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253137804097062012699859505 189853353072796509524894629)
    ·
      refine ⟨35597503701149345535917743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 189853353072796509524894629 35597503701149345535917743)
      ·
        refine ⟨53396255551724018303876615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35597503701149345535917743 53396255551724018303876615)
        ·
          refine ⟨80094383327586027455814923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53396255551724018303876615 80094383327586027455814923)
          ·
            refine ⟨120141574991379041183722385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80094383327586027455814923 120141574991379041183722385)
            ·
              refine ⟨90106181243534280887791789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120141574991379041183722385 90106181243534280887791789)
              ·
                refine ⟨33789817966325355332921921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90106181243534280887791789 33789817966325355332921921)
                ·
                  refine ⟨25342363474744016499691441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33789817966325355332921921 25342363474744016499691441)
                  ·
                    refine ⟨19006772606058012374768581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25342363474744016499691441 19006772606058012374768581)
                    ·
                      refine ⟨3563769863635877320269109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19006772606058012374768581 3563769863635877320269109)
                      ·
                        rfl

theorem cell23_6940417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 3, 2, 2, 4].length) (baseStart_6940417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6940417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6940417 prefixEnd_6940417 := by exact prefixLift 6940417
  have htrace : WordTrace (prefixWord ++ tailWord_6940417) baseStart_6940417 baseEnd_6940417 := by
    simpa [prefixWord, tailWord_6940417, baseEnd_6940417] using wordTrace_append hprefix tailTrace_6940417
  have hstable : (prefixWord ++ tailWord_6940417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6940417).length < 2 ^ (prefixWord ++ tailWord_6940417).sum := by decide
  have hdescent : baseEnd_6940417 < baseStart_6940417 := by decide
  rcases family_descends (prefixWord ++ tailWord_6940417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6940444 : List Nat := [2, 2, 3, 1, 1, 2, 2, 5, 5]
def baseStart_6940444 : Nat := 118140960795 + 6940444 * 2 ^ 59
def prefixEnd_6940444 : Nat := 4983230072969 + 3 ^ 40 * 6940444 * 2
def baseEnd_6940444 : Nat := 395975969734838746070165

theorem tailTrace_6940444 : CollatzResearch.WordTrace tailWord_6940444 prefixEnd_6940444 395975969734838746070165 := by
  unfold tailWord_6940444
  simp only [CollatzResearch.WordTrace]
  refine ⟨126569394433982098155546193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168759192578642797540728257 126569394433982098155546193)
  ·
    refine ⟨94927045825486573616659645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126569394433982098155546193 94927045825486573616659645)
    ·
      refine ⟨35597642184557465106247367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94927045825486573616659645 35597642184557465106247367)
      ·
        refine ⟨53396463276836197659371051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35597642184557465106247367 53396463276836197659371051)
        ·
          refine ⟨80094694915254296489056577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53396463276836197659371051 80094694915254296489056577)
          ·
            refine ⟨60071021186440722366792433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80094694915254296489056577 60071021186440722366792433)
            ·
              refine ⟨45053265889830541775094325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60071021186440722366792433 45053265889830541775094325)
              ·
                refine ⟨4223743677171613291415093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45053265889830541775094325 4223743677171613291415093)
                ·
                  refine ⟨395975969734838746070165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4223743677171613291415093 395975969734838746070165)
                  ·
                    rfl

theorem cell23_6940444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 5, 5].length) (baseStart_6940444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6940444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6940444 prefixEnd_6940444 := by exact prefixLift 6940444
  have htrace : WordTrace (prefixWord ++ tailWord_6940444) baseStart_6940444 baseEnd_6940444 := by
    simpa [prefixWord, tailWord_6940444, baseEnd_6940444] using wordTrace_append hprefix tailTrace_6940444
  have hstable : (prefixWord ++ tailWord_6940444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6940444).length < 2 ^ (prefixWord ++ tailWord_6940444).sum := by decide
  have hdescent : baseEnd_6940444 < baseStart_6940444 := by decide
  rcases family_descends (prefixWord ++ tailWord_6940444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6940537 : List Nat := [1, 2, 1, 3, 2, 2, 1, 2, 1, 2, 6]
def baseStart_6940537 : Nat := 118140960795 + 6940537 * 2 ^ 59
def prefixEnd_6940537 : Nat := 4983230072969 + 3 ^ 40 * 6940537 * 2
def baseEnd_6940537 : Nat := 3563831481314416850768557

theorem tailTrace_6940537 : CollatzResearch.WordTrace tailWord_6940537 prefixEnd_6940537 3563831481314416850768557 := by
  unfold tailWord_6940537
  simp only [CollatzResearch.WordTrace]
  refine ⟨253142180856627273194227865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168761453904418182129485243 253142180856627273194227865)
  ·
    refine ⟨189856635642470454895670899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253142180856627273194227865 189856635642470454895670899)
    ·
      refine ⟨284784953463705682343506349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189856635642470454895670899 284784953463705682343506349)
      ·
        refine ⟨106794357548889630878814881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 284784953463705682343506349 106794357548889630878814881)
        ·
          refine ⟨80095768161667223159111161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106794357548889630878814881 80095768161667223159111161)
          ·
            refine ⟨60071826121250417369333371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80095768161667223159111161 60071826121250417369333371)
            ·
              refine ⟨90107739181875626054000057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60071826121250417369333371 90107739181875626054000057)
              ·
                refine ⟨67580804386406719540500043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90107739181875626054000057 67580804386406719540500043)
                ·
                  refine ⟨101371206579610079310750065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67580804386406719540500043 101371206579610079310750065)
                  ·
                    refine ⟨76028404934707559483062549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 101371206579610079310750065 76028404934707559483062549)
                    ·
                      refine ⟨3563831481314416850768557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76028404934707559483062549 3563831481314416850768557)
                      ·
                        rfl

theorem cell23_6940537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 2, 1, 2, 6].length) (baseStart_6940537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6940537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6940537 prefixEnd_6940537 := by exact prefixLift 6940537
  have htrace : WordTrace (prefixWord ++ tailWord_6940537) baseStart_6940537 baseEnd_6940537 := by
    simpa [prefixWord, tailWord_6940537, baseEnd_6940537] using wordTrace_append hprefix tailTrace_6940537
  have hstable : (prefixWord ++ tailWord_6940537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6940537).length < 2 ^ (prefixWord ++ tailWord_6940537).sum := by decide
  have hdescent : baseEnd_6940537 < baseStart_6940537 := by decide
  rcases family_descends (prefixWord ++ tailWord_6940537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6940607 : List Nat := [1, 1, 2, 2, 2, 1, 3, 11]
def baseStart_6940607 : Nat := 118140960795 + 6940607 * 2 ^ 59
def prefixEnd_6940607 : Nat := 4983230072969 + 3 ^ 40 * 6940607 * 2
def baseEnd_6940607 : Nat := 131995089813341910255305

theorem tailTrace_6940607 : CollatzResearch.WordTrace tailWord_6940607 prefixEnd_6940607 131995089813341910255305 := by
  unfold tailWord_6940607
  simp only [CollatzResearch.WordTrace]
  refine ⟨253144733966373675149276075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168763155977582450099517383 253144733966373675149276075)
  ·
    refine ⟨379717100949560512723914113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253144733966373675149276075 379717100949560512723914113)
    ·
      refine ⟨284787825712170384542935585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 379717100949560512723914113 284787825712170384542935585)
      ·
        refine ⟨213590869284127788407201689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 284787825712170384542935585 213590869284127788407201689)
        ·
          refine ⟨160193151963095841305401267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213590869284127788407201689 160193151963095841305401267)
          ·
            refine ⟨240289727944643761958101901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160193151963095841305401267 240289727944643761958101901)
            ·
              refine ⟨90108647979241410734288213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 240289727944643761958101901 90108647979241410734288213)
              ·
                refine ⟨131995089813341910255305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 90108647979241410734288213 131995089813341910255305)
                ·
                  rfl

theorem cell23_6940607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 11].length) (baseStart_6940607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6940607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6940607 prefixEnd_6940607 := by exact prefixLift 6940607
  have htrace : WordTrace (prefixWord ++ tailWord_6940607) baseStart_6940607 baseEnd_6940607 := by
    simpa [prefixWord, tailWord_6940607, baseEnd_6940607] using wordTrace_append hprefix tailTrace_6940607
  have hstable : (prefixWord ++ tailWord_6940607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6940607).length < 2 ^ (prefixWord ++ tailWord_6940607).sum := by decide
  have hdescent : baseEnd_6940607 < baseStart_6940607 := by decide
  rcases family_descends (prefixWord ++ tailWord_6940607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6940627 : List Nat := [1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 8]
def baseStart_6940627 : Nat := 118140960795 + 6940627 * 2 ^ 59
def prefixEnd_6940627 : Nat := 4983230072969 + 3 ^ 40 * 6940627 * 2
def baseEnd_6940627 : Nat := 3563877694573321498643143

theorem tailTrace_6940627 : CollatzResearch.WordTrace tailWord_6940627 prefixEnd_6940627 3563877694573321498643143 := by
  unfold tailWord_6940627
  simp only [CollatzResearch.WordTrace]
  refine ⟨253145463426301218565004135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168763642284200812376669423 253145463426301218565004135)
  ·
    refine ⟨379718195139451827847506203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253145463426301218565004135 379718195139451827847506203)
    ·
      refine ⟨569577292709177741771259305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379718195139451827847506203 569577292709177741771259305)
      ·
        refine ⟨427182969531883306328444479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 569577292709177741771259305 427182969531883306328444479)
        ·
          refine ⟨640774454297824959492666719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 427182969531883306328444479 640774454297824959492666719)
          ·
            refine ⟨961161681446737439239000079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 640774454297824959492666719 961161681446737439239000079)
            ·
              refine ⟨1441742522170106158858500119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 961161681446737439239000079 1441742522170106158858500119)
              ·
                refine ⟨2162613783255159238287750179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1441742522170106158858500119 2162613783255159238287750179)
                ·
                  refine ⟨3243920674882738857431625269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2162613783255159238287750179 3243920674882738857431625269)
                  ·
                    refine ⟨304117563270256767884214869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3243920674882738857431625269 304117563270256767884214869)
                    ·
                      refine ⟨3563877694573321498643143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 304117563270256767884214869 3563877694573321498643143)
                      ·
                        rfl

theorem cell23_6940627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 8].length) (baseStart_6940627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6940627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6940627 prefixEnd_6940627 := by exact prefixLift 6940627
  have htrace : WordTrace (prefixWord ++ tailWord_6940627) baseStart_6940627 baseEnd_6940627 := by
    simpa [prefixWord, tailWord_6940627, baseEnd_6940627] using wordTrace_append hprefix tailTrace_6940627
  have hstable : (prefixWord ++ tailWord_6940627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6940627).length < 2 ^ (prefixWord ++ tailWord_6940627).sum := by decide
  have hdescent : baseEnd_6940627 < baseStart_6940627 := by decide
  rcases family_descends (prefixWord ++ tailWord_6940627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6940628 : List Nat := [2, 4, 1, 2, 1, 1, 4, 2, 2, 4]
def baseStart_6940628 : Nat := 118140960795 + 6940628 * 2 ^ 59
def prefixEnd_6940628 : Nat := 4983230072969 + 3 ^ 40 * 6940628 * 2
def baseEnd_6940628 : Nat := 1187959402684658664910213

theorem tailTrace_6940628 : CollatzResearch.WordTrace tailWord_6940628 prefixEnd_6940628 1187959402684658664910213 := by
  unfold tailWord_6940628
  simp only [CollatzResearch.WordTrace]
  refine ⟨126572749949648797867895269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168763666599531730490527025 126572749949648797867895269)
  ·
    refine ⟨23732390615559149600230363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126572749949648797867895269 23732390615559149600230363)
    ·
      refine ⟨35598585923338724400345545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23732390615559149600230363 35598585923338724400345545)
      ·
        refine ⟨26698939442504043300259159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35598585923338724400345545 26698939442504043300259159)
        ·
          refine ⟨40048409163756064950388739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26698939442504043300259159 40048409163756064950388739)
          ·
            refine ⟨60072613745634097425583109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40048409163756064950388739 60072613745634097425583109)
            ·
              refine ⟨11263615077306393267296833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60072613745634097425583109 11263615077306393267296833)
              ·
                refine ⟨8447711307979794950472625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11263615077306393267296833 8447711307979794950472625)
                ·
                  refine ⟨6335783480984846212854469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8447711307979794950472625 6335783480984846212854469)
                  ·
                    refine ⟨1187959402684658664910213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6335783480984846212854469 1187959402684658664910213)
                    ·
                      rfl

theorem cell23_6940628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4, 2, 2, 4].length) (baseStart_6940628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6940628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6940628 prefixEnd_6940628 := by exact prefixLift 6940628
  have htrace : WordTrace (prefixWord ++ tailWord_6940628) baseStart_6940628 baseEnd_6940628 := by
    simpa [prefixWord, tailWord_6940628, baseEnd_6940628] using wordTrace_append hprefix tailTrace_6940628
  have hstable : (prefixWord ++ tailWord_6940628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6940628).length < 2 ^ (prefixWord ++ tailWord_6940628).sum := by decide
  have hdescent : baseEnd_6940628 < baseStart_6940628 := by decide
  rcases family_descends (prefixWord ++ tailWord_6940628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6940684 : List Nat := [2, 2, 1, 2, 3, 1, 1, 1, 4, 6]
def baseStart_6940684 : Nat := 118140960795 + 6940684 * 2 ^ 59
def prefixEnd_6940684 : Nat := 4983230072969 + 3 ^ 40 * 6940684 * 2
def baseEnd_6940684 : Nat := 1187968987656875925210127

theorem tailTrace_6940684 : CollatzResearch.WordTrace tailWord_6940684 prefixEnd_6940684 1187968987656875925210127 := by
  unfold tailWord_6940684
  simp only [CollatzResearch.WordTrace]
  refine ⟨126573771193547358649914553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168765028258063144866552737 126573771193547358649914553)
  ·
    refine ⟨94930328395160518987435915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126573771193547358649914553 94930328395160518987435915)
    ·
      refine ⟨142395492592740778481153873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94930328395160518987435915 142395492592740778481153873)
      ·
        refine ⟨106796619444555583860865405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142395492592740778481153873 106796619444555583860865405)
        ·
          refine ⟨40048732291708343947824527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106796619444555583860865405 40048732291708343947824527)
          ·
            refine ⟨60073098437562515921736791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40048732291708343947824527 60073098437562515921736791)
            ·
              refine ⟨90109647656343773882605187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60073098437562515921736791 90109647656343773882605187)
              ·
                refine ⟨135164471484515660823907781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90109647656343773882605187 135164471484515660823907781)
                ·
                  refine ⟨25343338403346686404482709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 135164471484515660823907781 25343338403346686404482709)
                  ·
                    refine ⟨1187968987656875925210127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25343338403346686404482709 1187968987656875925210127)
                    ·
                      rfl

theorem cell23_6940684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 4, 6].length) (baseStart_6940684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6940684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6940684 prefixEnd_6940684 := by exact prefixLift 6940684
  have htrace : WordTrace (prefixWord ++ tailWord_6940684) baseStart_6940684 baseEnd_6940684 := by
    simpa [prefixWord, tailWord_6940684, baseEnd_6940684] using wordTrace_append hprefix tailTrace_6940684
  have hstable : (prefixWord ++ tailWord_6940684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6940684).length < 2 ^ (prefixWord ++ tailWord_6940684).sum := by decide
  have hdescent : baseEnd_6940684 < baseStart_6940684 := by decide
  rcases family_descends (prefixWord ++ tailWord_6940684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6940691 : List Nat := [1, 1, 1, 2, 1, 4, 2, 2, 3, 4, 2]
def baseStart_6940691 : Nat := 118140960795 + 6940691 * 2 ^ 59
def prefixEnd_6940691 : Nat := 4983230072969 + 3 ^ 40 * 6940691 * 2
def baseEnd_6940691 : Nat := 3563910557335209248242849

theorem tailTrace_6940691 : CollatzResearch.WordTrace tailWord_6940691 prefixEnd_6940691 3563910557335209248242849 := by
  unfold tailWord_6940691
  simp only [CollatzResearch.WordTrace]
  refine ⟨253147797698069357495333927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168765198465379571663555951 253147797698069357495333927)
  ·
    refine ⟨379721696547104036243000891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253147797698069357495333927 379721696547104036243000891)
    ·
      refine ⟨569582544820656054364501337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379721696547104036243000891 569582544820656054364501337)
      ·
        refine ⟨427186908615492040773376003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 569582544820656054364501337 427186908615492040773376003)
        ·
          refine ⟨640780362923238061160064005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 427186908615492040773376003 640780362923238061160064005)
          ·
            refine ⟨120146318048107136467512001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 640780362923238061160064005 120146318048107136467512001)
            ·
              refine ⟨90109738536080352350634001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120146318048107136467512001 90109738536080352350634001)
              ·
                refine ⟨67582303902060264262975501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90109738536080352350634001 67582303902060264262975501)
                ·
                  refine ⟨25343363963272599098615813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67582303902060264262975501 25343363963272599098615813)
                  ·
                    refine ⟨4751880743113612330990465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25343363963272599098615813 4751880743113612330990465)
                    ·
                      refine ⟨3563910557335209248242849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4751880743113612330990465 3563910557335209248242849)
                      ·
                        rfl

theorem cell23_6940691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 2, 3, 4, 2].length) (baseStart_6940691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6940691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6940691 prefixEnd_6940691 := by exact prefixLift 6940691
  have htrace : WordTrace (prefixWord ++ tailWord_6940691) baseStart_6940691 baseEnd_6940691 := by
    simpa [prefixWord, tailWord_6940691, baseEnd_6940691] using wordTrace_append hprefix tailTrace_6940691
  have hstable : (prefixWord ++ tailWord_6940691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6940691).length < 2 ^ (prefixWord ++ tailWord_6940691).sum := by decide
  have hdescent : baseEnd_6940691 < baseStart_6940691 := by decide
  rcases family_descends (prefixWord ++ tailWord_6940691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6940701 : List Nat := [1, 4, 2, 2, 2, 1, 2, 1, 2, 6]
def baseStart_6940701 : Nat := 118140960795 + 6940701 * 2 ^ 59
def prefixEnd_6940701 : Nat := 4983230072969 + 3 ^ 40 * 6940701 * 2
def baseEnd_6940701 : Nat := 1187971897380584736372601

theorem tailTrace_6940701 : CollatzResearch.WordTrace tailWord_6940701 prefixEnd_6940701 1187971897380584736372601 := by
  unfold tailWord_6940701
  simp only [CollatzResearch.WordTrace]
  refine ⟨253148162428033129203197957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168765441618688752802131971 253148162428033129203197957)
  ·
    refine ⟨47465280455256211725599617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 253148162428033129203197957 47465280455256211725599617)
    ·
      refine ⟨35598960341442158794199713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47465280455256211725599617 35598960341442158794199713)
      ·
        refine ⟨26699220256081619095649785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35598960341442158794199713 26699220256081619095649785)
        ·
          refine ⟨20024415192061214321737339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26699220256081619095649785 20024415192061214321737339)
          ·
            refine ⟨30036622788091821482606009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20024415192061214321737339 30036622788091821482606009)
            ·
              refine ⟨22527467091068866111954507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30036622788091821482606009 22527467091068866111954507)
              ·
                refine ⟨33791200636603299167931761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22527467091068866111954507 33791200636603299167931761)
                ·
                  refine ⟨25343400477452474375948821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33791200636603299167931761 25343400477452474375948821)
                  ·
                    refine ⟨1187971897380584736372601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25343400477452474375948821 1187971897380584736372601)
                    ·
                      rfl

theorem cell23_6940701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 1, 2, 6].length) (baseStart_6940701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6940701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6940701 prefixEnd_6940701 := by exact prefixLift 6940701
  have htrace : WordTrace (prefixWord ++ tailWord_6940701) baseStart_6940701 baseEnd_6940701 := by
    simpa [prefixWord, tailWord_6940701, baseEnd_6940701] using wordTrace_append hprefix tailTrace_6940701
  have hstable : (prefixWord ++ tailWord_6940701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6940701).length < 2 ^ (prefixWord ++ tailWord_6940701).sum := by decide
  have hdescent : baseEnd_6940701 < baseStart_6940701 := by decide
  rcases family_descends (prefixWord ++ tailWord_6940701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6940742 : List Nat := [6, 1, 1, 1, 1, 1, 1, 3, 4, 2, 2]
def baseStart_6940742 : Nat := 118140960795 + 6940742 * 2 ^ 59
def prefixEnd_6940742 : Nat := 4983230072969 + 3 ^ 40 * 6940742 * 2
def baseEnd_6940742 : Nat := 3563936744848588548705115

theorem tailTrace_6940742 : CollatzResearch.WordTrace tailWord_6940742 prefixEnd_6940742 3563936744848588548705115 := by
  unfold tailWord_6940742
  simp only [CollatzResearch.WordTrace]
  refine ⟨7910926806902643537670015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 168766438547256395470293653 7910926806902643537670015)
  ·
    refine ⟨11866390210353965306505023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7910926806902643537670015 11866390210353965306505023)
    ·
      refine ⟨17799585315530947959757535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11866390210353965306505023 17799585315530947959757535)
      ·
        refine ⟨26699377973296421939636303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17799585315530947959757535 26699377973296421939636303)
        ·
          refine ⟨40049066959944632909454455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26699377973296421939636303 40049066959944632909454455)
          ·
            refine ⟨60073600439916949364181683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40049066959944632909454455 60073600439916949364181683)
            ·
              refine ⟨90110400659875424046272525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60073600439916949364181683 90110400659875424046272525)
              ·
                refine ⟨33791400247453284017352197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90110400659875424046272525 33791400247453284017352197)
                ·
                  refine ⟨6335887546397490753253537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33791400247453284017352197 6335887546397490753253537)
                  ·
                    refine ⟨4751915659798118064940153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6335887546397490753253537 4751915659798118064940153)
                    ·
                      refine ⟨3563936744848588548705115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4751915659798118064940153 3563936744848588548705115)
                      ·
                        rfl

theorem cell23_6940742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 3, 4, 2, 2].length) (baseStart_6940742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6940742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6940742 prefixEnd_6940742 := by exact prefixLift 6940742
  have htrace : WordTrace (prefixWord ++ tailWord_6940742) baseStart_6940742 baseEnd_6940742 := by
    simpa [prefixWord, tailWord_6940742, baseEnd_6940742] using wordTrace_append hprefix tailTrace_6940742
  have hstable : (prefixWord ++ tailWord_6940742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6940742).length < 2 ^ (prefixWord ++ tailWord_6940742).sum := by decide
  have hdescent : baseEnd_6940742 < baseStart_6940742 := by decide
  rcases family_descends (prefixWord ++ tailWord_6940742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6940744 : List Nat := [2, 1, 3, 1, 1, 1, 2, 2, 3, 7]
def baseStart_6940744 : Nat := 118140960795 + 6940744 * 2 ^ 59
def prefixEnd_6940744 : Nat := 4983230072969 + 3 ^ 40 * 6940744 * 2
def baseEnd_6940744 : Nat := 1187979257269965846960035

theorem tailTrace_6940744 : CollatzResearch.WordTrace tailWord_6940744 prefixEnd_6940744 1187979257269965846960035 := by
  unfold tailWord_6940744
  simp only [CollatzResearch.WordTrace]
  refine ⟨126574865383438673773506643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168766487177918231698008857 126574865383438673773506643)
  ·
    refine ⟨189862298075158010660259965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126574865383438673773506643 189862298075158010660259965)
    ·
      refine ⟨71198361778184253997597487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189862298075158010660259965 71198361778184253997597487)
      ·
        refine ⟨106797542667276380996396231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71198361778184253997597487 106797542667276380996396231)
        ·
          refine ⟨160196314000914571494594347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106797542667276380996396231 160196314000914571494594347)
          ·
            refine ⟨240294471001371857241891521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160196314000914571494594347 240294471001371857241891521)
            ·
              refine ⟨180220853251028892931418641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 240294471001371857241891521 180220853251028892931418641)
              ·
                refine ⟨135165639938271669698563981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 180220853251028892931418641 135165639938271669698563981)
                ·
                  refine ⟨50687114976851876136961493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 135165639938271669698563981 50687114976851876136961493)
                  ·
                    refine ⟨1187979257269965846960035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50687114976851876136961493 1187979257269965846960035)
                    ·
                      rfl

theorem cell23_6940744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 3, 7].length) (baseStart_6940744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6940744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6940744 prefixEnd_6940744 := by exact prefixLift 6940744
  have htrace : WordTrace (prefixWord ++ tailWord_6940744) baseStart_6940744 baseEnd_6940744 := by
    simpa [prefixWord, tailWord_6940744, baseEnd_6940744] using wordTrace_append hprefix tailTrace_6940744
  have hstable : (prefixWord ++ tailWord_6940744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6940744).length < 2 ^ (prefixWord ++ tailWord_6940744).sum := by decide
  have hdescent : baseEnd_6940744 < baseStart_6940744 := by decide
  rcases family_descends (prefixWord ++ tailWord_6940744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6940751 : List Nat := [1, 1, 2, 1, 1, 2, 2, 3, 1, 7, 2]
def baseStart_6940751 : Nat := 118140960795 + 6940751 * 2 ^ 59
def prefixEnd_6940751 : Nat := 4983230072969 + 3 ^ 40 * 6940751 * 2
def baseEnd_6940751 : Nat := 3563941366174479013492573

theorem tailTrace_6940751 : CollatzResearch.WordTrace tailWord_6940751 prefixEnd_6940751 3563941366174479013492573 := by
  unfold tailWord_6940751
  simp only [CollatzResearch.WordTrace]
  refine ⟨253149986077851987742518107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168766657385234658495012071 253149986077851987742518107)
  ·
    refine ⟨379724979116777981613777161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253149986077851987742518107 379724979116777981613777161)
    ·
      refine ⟨284793734337583486210332871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 379724979116777981613777161 284793734337583486210332871)
      ·
        refine ⟨427190601506375229315499307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284793734337583486210332871 427190601506375229315499307)
        ·
          refine ⟨640785902259562843973248961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 427190601506375229315499307 640785902259562843973248961)
          ·
            refine ⟨480589426694672132979936721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 640785902259562843973248961 480589426694672132979936721)
            ·
              refine ⟨360442070021004099734952541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 480589426694672132979936721 360442070021004099734952541)
              ·
                refine ⟨135165776257876537400607203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 360442070021004099734952541 135165776257876537400607203)
                ·
                  refine ⟨202748664386814806100910805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 135165776257876537400607203 202748664386814806100910805)
                  ·
                    refine ⟨4751921821565972017990097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 202748664386814806100910805 4751921821565972017990097)
                    ·
                      refine ⟨3563941366174479013492573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4751921821565972017990097 3563941366174479013492573)
                      ·
                        rfl

theorem cell23_6940751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 7, 2].length) (baseStart_6940751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6940751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6940751 prefixEnd_6940751 := by exact prefixLift 6940751
  have htrace : WordTrace (prefixWord ++ tailWord_6940751) baseStart_6940751 baseEnd_6940751 := by
    simpa [prefixWord, tailWord_6940751, baseEnd_6940751] using wordTrace_append hprefix tailTrace_6940751
  have hstable : (prefixWord ++ tailWord_6940751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6940751).length < 2 ^ (prefixWord ++ tailWord_6940751).sum := by decide
  have hdescent : baseEnd_6940751 < baseStart_6940751 := by decide
  rcases family_descends (prefixWord ++ tailWord_6940751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6940818 : List Nat := [3, 2, 3, 1, 1, 1, 2, 2, 1, 4, 3]
def baseStart_6940818 : Nat := 118140960795 + 6940818 * 2 ^ 59
def prefixEnd_6940818 : Nat := 4983230072969 + 3 ^ 40 * 6940818 * 2
def baseEnd_6940818 : Nat := 3563975769378330251354765

theorem tailTrace_6940818 : CollatzResearch.WordTrace tailWord_6940818 prefixEnd_6940818 3563975769378330251354765 := by
  unfold tailWord_6940818
  simp only [CollatzResearch.WordTrace]
  refine ⟨63288107442152314546301777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168768286512406172123471405 63288107442152314546301777)
  ·
    refine ⟨47466080581614235909726333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63288107442152314546301777 47466080581614235909726333)
    ·
      refine ⟨17799780218105338466147375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47466080581614235909726333 17799780218105338466147375)
      ·
        refine ⟨26699670327158007699221063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17799780218105338466147375 26699670327158007699221063)
        ·
          refine ⟨40049505490737011548831595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26699670327158007699221063 40049505490737011548831595)
          ·
            refine ⟨60074258236105517323247393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40049505490737011548831595 60074258236105517323247393)
            ·
              refine ⟨45055693677079137992435545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60074258236105517323247393 45055693677079137992435545)
              ·
                refine ⟨33791770257809353494326659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45055693677079137992435545 33791770257809353494326659)
                ·
                  refine ⟨50687655386714030241489989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33791770257809353494326659 50687655386714030241489989)
                  ·
                    refine ⟨9503935385008880670279373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50687655386714030241489989 9503935385008880670279373)
                    ·
                      refine ⟨3563975769378330251354765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9503935385008880670279373 3563975769378330251354765)
                      ·
                        rfl

theorem cell23_6940818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 2, 1, 4, 3].length) (baseStart_6940818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6940818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6940818 prefixEnd_6940818 := by exact prefixLift 6940818
  have htrace : WordTrace (prefixWord ++ tailWord_6940818) baseStart_6940818 baseEnd_6940818 := by
    simpa [prefixWord, tailWord_6940818, baseEnd_6940818] using wordTrace_append hprefix tailTrace_6940818
  have hstable : (prefixWord ++ tailWord_6940818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6940818).length < 2 ^ (prefixWord ++ tailWord_6940818).sum := by decide
  have hdescent : baseEnd_6940818 < baseStart_6940818 := by decide
  rcases family_descends (prefixWord ++ tailWord_6940818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6940821 : List Nat := [1, 3, 2, 1, 1, 1, 3, 5, 6]
def baseStart_6940821 : Nat := 118140960795 + 6940821 * 2 ^ 59
def prefixEnd_6940821 : Nat := 4983230072969 + 3 ^ 40 * 6940821 * 2
def baseEnd_6940821 : Nat := 395997478868921526624139

theorem tailTrace_6940821 : CollatzResearch.WordTrace tailWord_6940821 prefixEnd_6940821 395997478868921526624139 := by
  unfold tailWord_6940821
  simp only [CollatzResearch.WordTrace]
  refine ⟨253152539187598389697566317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168768359458398926465044211 253152539187598389697566317)
  ·
    refine ⟨94932202195349396136587369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 253152539187598389697566317 94932202195349396136587369)
    ·
      refine ⟨71199151646512047102440527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94932202195349396136587369 71199151646512047102440527)
      ·
        refine ⟨106798727469768070653660791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71199151646512047102440527 106798727469768070653660791)
        ·
          refine ⟨160198091204652105980491187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106798727469768070653660791 160198091204652105980491187)
          ·
            refine ⟨240297136806978158970736781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160198091204652105980491187 240297136806978158970736781)
            ·
              refine ⟨90111426302616809614026293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 240297136806978158970736781 90111426302616809614026293)
              ·
                refine ⟨8447946215870325901314965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 90111426302616809614026293 8447946215870325901314965)
                ·
                  refine ⟨395997478868921526624139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8447946215870325901314965 395997478868921526624139)
                  ·
                    rfl

theorem cell23_6940821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 5, 6].length) (baseStart_6940821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6940821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6940821 prefixEnd_6940821 := by exact prefixLift 6940821
  have htrace : WordTrace (prefixWord ++ tailWord_6940821) baseStart_6940821 baseEnd_6940821 := by
    simpa [prefixWord, tailWord_6940821, baseEnd_6940821] using wordTrace_append hprefix tailTrace_6940821
  have hstable : (prefixWord ++ tailWord_6940821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6940821).length < 2 ^ (prefixWord ++ tailWord_6940821).sum := by decide
  have hdescent : baseEnd_6940821 < baseStart_6940821 := by decide
  rcases family_descends (prefixWord ++ tailWord_6940821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6940908 : List Nat := [2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 5]
def baseStart_6940908 : Nat := 118140960795 + 6940908 * 2 ^ 59
def prefixEnd_6940908 : Nat := 4983230072969 + 3 ^ 40 * 6940908 * 2
def baseEnd_6940908 : Nat := 3564021982637234899229351

theorem tailTrace_6940908 : CollatzResearch.WordTrace tailWord_6940908 prefixEnd_6940908 3564021982637234899229351 := by
  unfold tailWord_6940908
  simp only [CollatzResearch.WordTrace]
  refine ⟨126577856169141601777991689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168770474892188802370655585 126577856169141601777991689)
  ·
    refine ⟨94933392126856201333493767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126577856169141601777991689 94933392126856201333493767)
    ·
      refine ⟨142400088190284302000240651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94933392126856201333493767 142400088190284302000240651)
      ·
        refine ⟨213600132285426453000360977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142400088190284302000240651 213600132285426453000360977)
        ·
          refine ⟨160200099214069839750270733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213600132285426453000360977 160200099214069839750270733)
          ·
            refine ⟨60075037205276189906351525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 160200099214069839750270733 60075037205276189906351525)
            ·
              refine ⟨11264069475989285607440911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60075037205276189906351525 11264069475989285607440911)
              ·
                refine ⟨16896104213983928411161367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11264069475989285607440911 16896104213983928411161367)
                ·
                  refine ⟨25344156320975892616742051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16896104213983928411161367 25344156320975892616742051)
                  ·
                    refine ⟨38016234481463838925113077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25344156320975892616742051 38016234481463838925113077)
                    ·
                      refine ⟨3564021982637234899229351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38016234481463838925113077 3564021982637234899229351)
                      ·
                        rfl

theorem cell23_6940908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 5].length) (baseStart_6940908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6940908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6940908 prefixEnd_6940908 := by exact prefixLift 6940908
  have htrace : WordTrace (prefixWord ++ tailWord_6940908) baseStart_6940908 baseEnd_6940908 := by
    simpa [prefixWord, tailWord_6940908, baseEnd_6940908] using wordTrace_append hprefix tailTrace_6940908
  have hstable : (prefixWord ++ tailWord_6940908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6940908).length < 2 ^ (prefixWord ++ tailWord_6940908).sum := by decide
  have hdescent : baseEnd_6940908 < baseStart_6940908 := by decide
  rcases family_descends (prefixWord ++ tailWord_6940908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6940911 : List Nat := [1, 1, 2, 1, 6, 1, 11]
def baseStart_6940911 : Nat := 118140960795 + 6940911 * 2 ^ 59
def prefixEnd_6940911 : Nat := 4983230072969 + 3 ^ 40 * 6940911 * 2
def baseEnd_6940911 : Nat := 44000290408385165277677

theorem tailTrace_6940911 : CollatzResearch.WordTrace tailWord_6940911 prefixEnd_6940911 44000290408385165277677 := by
  unfold tailWord_6940911
  simp only [CollatzResearch.WordTrace]
  refine ⟨253155821757272335068342587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168770547838181556712228391 253155821757272335068342587)
  ·
    refine ⟨379733732635908502602513881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253155821757272335068342587 379733732635908502602513881)
    ·
      refine ⟨284800299476931376951885411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 379733732635908502602513881 284800299476931376951885411)
      ·
        refine ⟨427200449215397065427828117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284800299476931376951885411 427200449215397065427828117)
        ·
          refine ⟨20025021056971737441929443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 427200449215397065427828117 20025021056971737441929443)
          ·
            refine ⟨30037531585457606162894165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20025021056971737441929443 30037531585457606162894165)
            ·
              refine ⟨44000290408385165277677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 30037531585457606162894165 44000290408385165277677)
              ·
                rfl

theorem cell23_6940911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 11].length) (baseStart_6940911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6940911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6940911 prefixEnd_6940911 := by exact prefixLift 6940911
  have htrace : WordTrace (prefixWord ++ tailWord_6940911) baseStart_6940911 baseEnd_6940911 := by
    simpa [prefixWord, tailWord_6940911, baseEnd_6940911] using wordTrace_append hprefix tailTrace_6940911
  have hstable : (prefixWord ++ tailWord_6940911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6940911).length < 2 ^ (prefixWord ++ tailWord_6940911).sum := by decide
  have hdescent : baseEnd_6940911 < baseStart_6940911 := by decide
  rcases family_descends (prefixWord ++ tailWord_6940911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6940918 : List Nat := [5, 1, 1, 1, 1, 1, 3, 2, 1, 1, 6]
def baseStart_6940918 : Nat := 118140960795 + 6940918 * 2 ^ 59
def prefixEnd_6940918 : Nat := 4983230072969 + 3 ^ 40 * 6940918 * 2
def baseEnd_6940918 : Nat := 3564027117443779860104305

theorem tailTrace_6940918 : CollatzResearch.WordTrace tailWord_6940918 prefixEnd_6940918 3564027117443779860104305 := by
  unfold tailWord_6940918
  simp only [CollatzResearch.WordTrace]
  refine ⟨15822254816765435953990463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 168770718045497983509231605 15822254816765435953990463)
  ·
    refine ⟨23733382225148153930985695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15822254816765435953990463 23733382225148153930985695)
    ·
      refine ⟨35600073337722230896478543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23733382225148153930985695 35600073337722230896478543)
      ·
        refine ⟨53400110006583346344717815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35600073337722230896478543 53400110006583346344717815)
        ·
          refine ⟨80100165009875019517076723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53400110006583346344717815 80100165009875019517076723)
          ·
            refine ⟨120150247514812529275615085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80100165009875019517076723 120150247514812529275615085)
            ·
              refine ⟨45056342818054698478355657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120150247514812529275615085 45056342818054698478355657)
              ·
                refine ⟨33792257113541023858766743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45056342818054698478355657 33792257113541023858766743)
                ·
                  refine ⟨50688385670311535788150115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33792257113541023858766743 50688385670311535788150115)
                  ·
                    refine ⟨76032578505467303682225173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50688385670311535788150115 76032578505467303682225173)
                    ·
                      refine ⟨3564027117443779860104305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76032578505467303682225173 3564027117443779860104305)
                      ·
                        rfl

theorem cell23_6940918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 2, 1, 1, 6].length) (baseStart_6940918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6940918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6940918 prefixEnd_6940918 := by exact prefixLift 6940918
  have htrace : WordTrace (prefixWord ++ tailWord_6940918) baseStart_6940918 baseEnd_6940918 := by
    simpa [prefixWord, tailWord_6940918, baseEnd_6940918] using wordTrace_append hprefix tailTrace_6940918
  have hstable : (prefixWord ++ tailWord_6940918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6940918).length < 2 ^ (prefixWord ++ tailWord_6940918).sum := by decide
  have hdescent : baseEnd_6940918 < baseStart_6940918 := by decide
  rcases family_descends (prefixWord ++ tailWord_6940918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6940922 : List Nat := [3, 1, 1, 1, 1, 5, 3, 1, 3, 2, 2]
def baseStart_6940922 : Nat := 118140960795 + 6940922 * 2 ^ 59
def prefixEnd_6940922 : Nat := 4983230072969 + 3 ^ 40 * 6940922 * 2
def baseEnd_6940922 : Nat := 3564029171366397844454287

theorem tailTrace_6940922 : CollatzResearch.WordTrace tailWord_6940922 prefixEnd_6940922 3564029171366397844454287 := by
  unfold tailWord_6940922
  simp only [CollatzResearch.WordTrace]
  refine ⟨63289055740058120986748255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168770815306821655964662013 63289055740058120986748255)
  ·
    refine ⟨94933583610087181480122383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63289055740058120986748255 94933583610087181480122383)
    ·
      refine ⟨142400375415130772220183575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94933583610087181480122383 142400375415130772220183575)
      ·
        refine ⟨213600563122696158330275363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142400375415130772220183575 213600563122696158330275363)
        ·
          refine ⟨320400844684044237495413045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213600563122696158330275363 320400844684044237495413045)
          ·
            refine ⟨30037579189129147265194973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 320400844684044237495413045 30037579189129147265194973)
            ·
              refine ⟨11264092195923430224448115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30037579189129147265194973 11264092195923430224448115)
              ·
                refine ⟨16896138293885145336672173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11264092195923430224448115 16896138293885145336672173)
                ·
                  refine ⟨6336051860206929501252065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16896138293885145336672173 6336051860206929501252065)
                  ·
                    refine ⟨4752038895155197125939049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6336051860206929501252065 4752038895155197125939049)
                    ·
                      refine ⟨3564029171366397844454287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4752038895155197125939049 3564029171366397844454287)
                      ·
                        rfl

theorem cell23_6940922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 3, 1, 3, 2, 2].length) (baseStart_6940922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6940922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6940922 prefixEnd_6940922 := by exact prefixLift 6940922
  have htrace : WordTrace (prefixWord ++ tailWord_6940922) baseStart_6940922 baseEnd_6940922 := by
    simpa [prefixWord, tailWord_6940922, baseEnd_6940922] using wordTrace_append hprefix tailTrace_6940922
  have hstable : (prefixWord ++ tailWord_6940922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6940922).length < 2 ^ (prefixWord ++ tailWord_6940922).sum := by decide
  have hdescent : baseEnd_6940922 < baseStart_6940922 := by decide
  rcases family_descends (prefixWord ++ tailWord_6940922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6940931 : List Nat := [1, 1, 1, 3, 2, 3, 1, 1, 2, 2, 6]
def baseStart_6940931 : Nat := 118140960795 + 6940931 * 2 ^ 59
def prefixEnd_6940931 : Nat := 4983230072969 + 3 ^ 40 * 6940931 * 2
def baseEnd_6940931 : Nat := 3564033792692288309241745

theorem tailTrace_6940931 : CollatzResearch.WordTrace tailWord_6940931 prefixEnd_6940931 3564033792692288309241745 := by
  unfold tailWord_6940931
  simp only [CollatzResearch.WordTrace]
  refine ⟨253156551217199878484070647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168771034144799918989380431 253156551217199878484070647)
  ·
    refine ⟨379734826825799817726105971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253156551217199878484070647 379734826825799817726105971)
    ·
      refine ⟨569602240238699726589158957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379734826825799817726105971 569602240238699726589158957)
      ·
        refine ⟨213600840089512397470934609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 569602240238699726589158957 213600840089512397470934609)
        ·
          refine ⟨160200630067134298103200957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213600840089512397470934609 160200630067134298103200957)
          ·
            refine ⟨60075236275175361788700359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 160200630067134298103200957 60075236275175361788700359)
            ·
              refine ⟨90112854412763042683050539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60075236275175361788700359 90112854412763042683050539)
              ·
                refine ⟨135169281619144564024575809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90112854412763042683050539 135169281619144564024575809)
                ·
                  refine ⟨101376961214358423018431857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 135169281619144564024575809 101376961214358423018431857)
                  ·
                    refine ⟨76032720910768817263823893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 101376961214358423018431857 76032720910768817263823893)
                    ·
                      refine ⟨3564033792692288309241745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76032720910768817263823893 3564033792692288309241745)
                      ·
                        rfl

theorem cell23_6940931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 2, 2, 6].length) (baseStart_6940931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6940931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6940931 prefixEnd_6940931 := by exact prefixLift 6940931
  have htrace : WordTrace (prefixWord ++ tailWord_6940931) baseStart_6940931 baseEnd_6940931 := by
    simpa [prefixWord, tailWord_6940931, baseEnd_6940931] using wordTrace_append hprefix tailTrace_6940931
  have hstable : (prefixWord ++ tailWord_6940931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6940931).length < 2 ^ (prefixWord ++ tailWord_6940931).sum := by decide
  have hdescent : baseEnd_6940931 < baseStart_6940931 := by decide
  rcases family_descends (prefixWord ++ tailWord_6940931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6940932 : List Nat := [2, 3, 2, 2, 3, 1, 1, 3, 2, 4]
def baseStart_6940932 : Nat := 118140960795 + 6940932 * 2 ^ 59
def prefixEnd_6940932 : Nat := 4983230072969 + 3 ^ 40 * 6940932 * 2
def baseEnd_6940932 : Nat := 1188011435390980935109747

theorem tailTrace_6940932 : CollatzResearch.WordTrace tailWord_6940932 prefixEnd_6940932 1188011435390980935109747 := by
  unfold tailWord_6940932
  simp only [CollatzResearch.WordTrace]
  refine ⟨126578293845098127827428525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168771058460130837103238033 126578293845098127827428525)
  ·
    refine ⟨47466860191911797935285697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126578293845098127827428525 47466860191911797935285697)
    ·
      refine ⟨35600145143933848451464273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47466860191911797935285697 35600145143933848451464273)
      ·
        refine ⟨26700108857950386338598205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35600145143933848451464273 26700108857950386338598205)
        ·
          refine ⟨10012540821731394876974327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26700108857950386338598205 10012540821731394876974327)
          ·
            refine ⟨15018811232597092315461491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10012540821731394876974327 15018811232597092315461491)
            ·
              refine ⟨22528216848895638473192237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15018811232597092315461491 22528216848895638473192237)
              ·
                refine ⟨8448081318335864427447089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22528216848895638473192237 8448081318335864427447089)
                ·
                  refine ⟨6336060988751898320585317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8448081318335864427447089 6336060988751898320585317)
                  ·
                    refine ⟨1188011435390980935109747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6336060988751898320585317 1188011435390980935109747)
                    ·
                      rfl

theorem cell23_6940932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 3, 2, 4].length) (baseStart_6940932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6940932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6940932 prefixEnd_6940932 := by exact prefixLift 6940932
  have htrace : WordTrace (prefixWord ++ tailWord_6940932) baseStart_6940932 baseEnd_6940932 := by
    simpa [prefixWord, tailWord_6940932, baseEnd_6940932] using wordTrace_append hprefix tailTrace_6940932
  have hstable : (prefixWord ++ tailWord_6940932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6940932).length < 2 ^ (prefixWord ++ tailWord_6940932).sum := by decide
  have hdescent : baseEnd_6940932 < baseStart_6940932 := by decide
  rcases family_descends (prefixWord ++ tailWord_6940932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6940967 : List Nat := [1, 1, 8, 1, 2, 1, 2, 2, 1, 1, 3]
def baseStart_6940967 : Nat := 118140960795 + 6940967 * 2 ^ 59
def prefixEnd_6940967 : Nat := 4983230072969 + 3 ^ 40 * 6940967 * 2
def baseEnd_6940967 : Nat := 3564052277995850168391581

theorem tailTrace_6940967 : CollatzResearch.WordTrace tailWord_6940967 prefixEnd_6940967 3564052277995850168391581 := by
  unfold tailWord_6940967
  simp only [CollatzResearch.WordTrace]
  refine ⟨253157864245069456632381155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168771909496712971088254103 253157864245069456632381155)
  ·
    refine ⟨379736796367604184948571733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253157864245069456632381155 379736796367604184948571733)
    ·
      refine ⟨4450040582432861542366075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 379736796367604184948571733 4450040582432861542366075)
      ·
        refine ⟨6675060873649292313549113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4450040582432861542366075 6675060873649292313549113)
        ·
          refine ⟨5006295655236969235161835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6675060873649292313549113 5006295655236969235161835)
          ·
            refine ⟨7509443482855453852742753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5006295655236969235161835 7509443482855453852742753)
            ·
              refine ⟨5632082612141590389557065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7509443482855453852742753 5632082612141590389557065)
              ·
                refine ⟨4224061959106192792167799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5632082612141590389557065 4224061959106192792167799)
                ·
                  refine ⟨6336092938659289188251699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4224061959106192792167799 6336092938659289188251699)
                  ·
                    refine ⟨9504139407988933782377549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6336092938659289188251699 9504139407988933782377549)
                    ·
                      refine ⟨3564052277995850168391581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9504139407988933782377549 3564052277995850168391581)
                      ·
                        rfl

theorem cell23_6940967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_6940967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6940967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6940967 prefixEnd_6940967 := by exact prefixLift 6940967
  have htrace : WordTrace (prefixWord ++ tailWord_6940967) baseStart_6940967 baseEnd_6940967 := by
    simpa [prefixWord, tailWord_6940967, baseEnd_6940967] using wordTrace_append hprefix tailTrace_6940967
  have hstable : (prefixWord ++ tailWord_6940967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6940967).length < 2 ^ (prefixWord ++ tailWord_6940967).sum := by decide
  have hdescent : baseEnd_6940967 < baseStart_6940967 := by decide
  rcases family_descends (prefixWord ++ tailWord_6940967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6940973 : List Nat := [1, 5, 3, 1, 2, 1, 1, 4, 1, 2, 2]
def baseStart_6940973 : Nat := 118140960795 + 6940973 * 2 ^ 59
def prefixEnd_6940973 : Nat := 4983230072969 + 3 ^ 40 * 6940973 * 2
def baseEnd_6940973 : Nat := 3564055358879777144916553

theorem tailTrace_6940973 : CollatzResearch.WordTrace tailWord_6940973 prefixEnd_6940973 3564055358879777144916553 := by
  unfold tailWord_6940973
  simp only [CollatzResearch.WordTrace]
  refine ⟨253158083083047719657099573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168772055388698479771399715 253158083083047719657099573)
  ·
    refine ⟨23733570289035723717853085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 253158083083047719657099573 23733570289035723717853085)
    ·
      refine ⟨8900088858388396394194907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23733570289035723717853085 8900088858388396394194907)
      ·
        refine ⟨13350133287582594591292361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8900088858388396394194907 13350133287582594591292361)
        ·
          refine ⟨10012599965686945943469271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13350133287582594591292361 10012599965686945943469271)
          ·
            refine ⟨15018899948530418915203907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10012599965686945943469271 15018899948530418915203907)
            ·
              refine ⟨22528349922795628372805861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15018899948530418915203907 22528349922795628372805861)
              ·
                refine ⟨4224065610524180319901099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22528349922795628372805861 4224065610524180319901099)
                ·
                  refine ⟨6336098415786270479851649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4224065610524180319901099 6336098415786270479851649)
                  ·
                    refine ⟨4752073811839702859888737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6336098415786270479851649 4752073811839702859888737)
                    ·
                      refine ⟨3564055358879777144916553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4752073811839702859888737 3564055358879777144916553)
                      ·
                        rfl

theorem cell23_6940973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 4, 1, 2, 2].length) (baseStart_6940973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6940973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6940973 prefixEnd_6940973 := by exact prefixLift 6940973
  have htrace : WordTrace (prefixWord ++ tailWord_6940973) baseStart_6940973 baseEnd_6940973 := by
    simpa [prefixWord, tailWord_6940973, baseEnd_6940973] using wordTrace_append hprefix tailTrace_6940973
  have hstable : (prefixWord ++ tailWord_6940973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6940973).length < 2 ^ (prefixWord ++ tailWord_6940973).sum := by decide
  have hdescent : baseEnd_6940973 < baseStart_6940973 := by decide
  rcases family_descends (prefixWord ++ tailWord_6940973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6940988 : List Nat := [2, 2, 2, 2, 1, 2, 3, 1, 2, 6]
def baseStart_6940988 : Nat := 118140960795 + 6940988 * 2 ^ 59
def prefixEnd_6940988 : Nat := 4983230072969 + 3 ^ 40 * 6940988 * 2
def baseEnd_6940988 : Nat := 1188021020363198195409661

theorem tailTrace_6940988 : CollatzResearch.WordTrace tailWord_6940988 prefixEnd_6940988 1188021020363198195409661 := by
  unfold tailWord_6940988
  simp only [CollatzResearch.WordTrace]
  refine ⟨126579315088996688609447809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168772420118662251479263745 126579315088996688609447809)
  ·
    refine ⟨94934486316747516457085857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126579315088996688609447809 94934486316747516457085857)
    ·
      refine ⟨71200864737560637342814393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94934486316747516457085857 71200864737560637342814393)
      ·
        refine ⟨53400648553170478007110795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71200864737560637342814393 53400648553170478007110795)
        ·
          refine ⟨80100972829755717010666193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53400648553170478007110795 80100972829755717010666193)
          ·
            refine ⟨60075729622316787757999645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80100972829755717010666193 60075729622316787757999645)
            ·
              refine ⟨22528398608368795409249867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60075729622316787757999645 22528398608368795409249867)
              ·
                refine ⟨33792597912553193113874801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22528398608368795409249867 33792597912553193113874801)
                ·
                  refine ⟨25344448434414894835406101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33792597912553193113874801 25344448434414894835406101)
                  ·
                    refine ⟨1188021020363198195409661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25344448434414894835406101 1188021020363198195409661)
                    ·
                      rfl

theorem cell23_6940988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 1, 2, 6].length) (baseStart_6940988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6940988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6940988 prefixEnd_6940988 := by exact prefixLift 6940988
  have htrace : WordTrace (prefixWord ++ tailWord_6940988) baseStart_6940988 baseEnd_6940988 := by
    simpa [prefixWord, tailWord_6940988, baseEnd_6940988] using wordTrace_append hprefix tailTrace_6940988
  have hstable : (prefixWord ++ tailWord_6940988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6940988).length < 2 ^ (prefixWord ++ tailWord_6940988).sum := by decide
  have hdescent : baseEnd_6940988 < baseStart_6940988 := by decide
  rcases family_descends (prefixWord ++ tailWord_6940988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6940995 : List Nat := [1, 1, 1, 3, 1, 3, 3, 3, 1, 4, 2]
def baseStart_6940995 : Nat := 118140960795 + 6940995 * 2 ^ 59
def prefixEnd_6940995 : Nat := 4983230072969 + 3 ^ 40 * 6940995 * 2
def baseEnd_6940995 : Nat := 3564066655454176058841451

theorem tailTrace_6940995 : CollatzResearch.WordTrace tailWord_6940995 prefixEnd_6940995 3564066655454176058841451 := by
  unfold tailWord_6940995
  simp only [CollatzResearch.WordTrace]
  refine ⟨253158885488968017414400439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168772590325978678276266959 253158885488968017414400439)
  ·
    refine ⟨379738328233452026121600659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253158885488968017414400439 379738328233452026121600659)
    ·
      refine ⟨569607492350178039182400989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379738328233452026121600659 569607492350178039182400989)
      ·
        refine ⟨213602809631316764693400371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 569607492350178039182400989 213602809631316764693400371)
        ·
          refine ⟨320404214446975147040100557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213602809631316764693400371 320404214446975147040100557)
          ·
            refine ⟨120151580417615680140037709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 320404214446975147040100557 120151580417615680140037709)
            ·
              refine ⟨45056842656605880052514141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120151580417615680140037709 45056842656605880052514141)
              ·
                refine ⟨16896315996227205019692803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45056842656605880052514141 16896315996227205019692803)
                ·
                  refine ⟨25344473994340807529539205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16896315996227205019692803 25344473994340807529539205)
                  ·
                    refine ⟨4752088873938901411788601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25344473994340807529539205 4752088873938901411788601)
                    ·
                      refine ⟨3564066655454176058841451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4752088873938901411788601 3564066655454176058841451)
                      ·
                        rfl

theorem cell23_6940995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 3, 1, 4, 2].length) (baseStart_6940995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6940995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6940995 prefixEnd_6940995 := by exact prefixLift 6940995
  have htrace : WordTrace (prefixWord ++ tailWord_6940995) baseStart_6940995 baseEnd_6940995 := by
    simpa [prefixWord, tailWord_6940995, baseEnd_6940995] using wordTrace_append hprefix tailTrace_6940995
  have hstable : (prefixWord ++ tailWord_6940995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6940995).length < 2 ^ (prefixWord ++ tailWord_6940995).sum := by decide
  have hdescent : baseEnd_6940995 < baseStart_6940995 := by decide
  rcases family_descends (prefixWord ++ tailWord_6940995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6941012 : List Nat := [2, 4, 1, 1, 2, 2, 2, 2, 1, 4, 2]
def baseStart_6941012 : Nat := 118140960795 + 6941012 * 2 ^ 59
def prefixEnd_6941012 : Nat := 4983230072969 + 3 ^ 40 * 6941012 * 2
def baseEnd_6941012 : Nat := 3564075384625302492328873

theorem tailTrace_6941012 : CollatzResearch.WordTrace tailWord_6941012 prefixEnd_6941012 3564075384625302492328873 := by
  unfold tailWord_6941012
  simp only [CollatzResearch.WordTrace]
  refine ⟨126579752764953214658884645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168773003686604286211846193 126579752764953214658884645)
  ·
    refine ⟨23733703643428727748540871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126579752764953214658884645 23733703643428727748540871)
    ·
      refine ⟨35600555465143091622811307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23733703643428727748540871 35600555465143091622811307)
      ·
        refine ⟨53400833197714637434216961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35600555465143091622811307 53400833197714637434216961)
        ·
          refine ⟨40050624898285978075662721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53400833197714637434216961 40050624898285978075662721)
          ·
            refine ⟨30037968673714483556747041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40050624898285978075662721 30037968673714483556747041)
            ·
              refine ⟨22528476505285862667560281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30037968673714483556747041 22528476505285862667560281)
              ·
                refine ⟨16896357378964397000670211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22528476505285862667560281 16896357378964397000670211)
                ·
                  refine ⟨25344536068446595501005317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16896357378964397000670211 25344536068446595501005317)
                  ·
                    refine ⟨4752100512833736656438497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25344536068446595501005317 4752100512833736656438497)
                    ·
                      refine ⟨3564075384625302492328873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4752100512833736656438497 3564075384625302492328873)
                      ·
                        rfl

theorem cell23_6941012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 2, 1, 4, 2].length) (baseStart_6941012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6941012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6941012 prefixEnd_6941012 := by exact prefixLift 6941012
  have htrace : WordTrace (prefixWord ++ tailWord_6941012) baseStart_6941012 baseEnd_6941012 := by
    simpa [prefixWord, tailWord_6941012, baseEnd_6941012] using wordTrace_append hprefix tailTrace_6941012
  have hstable : (prefixWord ++ tailWord_6941012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6941012).length < 2 ^ (prefixWord ++ tailWord_6941012).sum := by decide
  have hdescent : baseEnd_6941012 < baseStart_6941012 := by decide
  rcases family_descends (prefixWord ++ tailWord_6941012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6941029 : List Nat := [1, 3, 1, 3, 1, 3, 3, 2, 2, 2, 2]
def baseStart_6941029 : Nat := 118140960795 + 6941029 * 2 ^ 59
def prefixEnd_6941029 : Nat := 4983230072969 + 3 ^ 40 * 6941029 * 2
def baseEnd_6941029 : Nat := 3564084113796428925816295

theorem tailTrace_6941029 : CollatzResearch.WordTrace tailWord_6941029 prefixEnd_6941029 3564084113796428925816295 := by
  unfold tailWord_6941029
  simp only [CollatzResearch.WordTrace]
  refine ⟨253160125570844841221138141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168773417047229894147425427 253160125570844841221138141)
  ·
    refine ⟨94935047089066815457926803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 253160125570844841221138141 94935047089066815457926803)
    ·
      refine ⟨142402570633600223186890205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94935047089066815457926803 142402570633600223186890205)
      ·
        refine ⟨53400963987600083695083827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142402570633600223186890205 53400963987600083695083827)
        ·
          refine ⟨80101445981400125542625741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53400963987600083695083827 80101445981400125542625741)
          ·
            refine ⟨30038042243025047078484653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80101445981400125542625741 30038042243025047078484653)
            ·
              refine ⟨11264265841134392654431745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30038042243025047078484653 11264265841134392654431745)
              ·
                refine ⟨8448199380850794490823809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11264265841134392654431745 8448199380850794490823809)
                ·
                  refine ⟨6336149535638095868117857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8448199380850794490823809 6336149535638095868117857)
                  ·
                    refine ⟨4752112151728571901088393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6336149535638095868117857 4752112151728571901088393)
                    ·
                      refine ⟨3564084113796428925816295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4752112151728571901088393 3564084113796428925816295)
                      ·
                        rfl

theorem cell23_6941029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3, 2, 2, 2, 2].length) (baseStart_6941029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6941029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6941029 prefixEnd_6941029 := by exact prefixLift 6941029
  have htrace : WordTrace (prefixWord ++ tailWord_6941029) baseStart_6941029 baseEnd_6941029 := by
    simpa [prefixWord, tailWord_6941029, baseEnd_6941029] using wordTrace_append hprefix tailTrace_6941029
  have hstable : (prefixWord ++ tailWord_6941029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6941029).length < 2 ^ (prefixWord ++ tailWord_6941029).sum := by decide
  have hdescent : baseEnd_6941029 < baseStart_6941029 := by decide
  rcases family_descends (prefixWord ++ tailWord_6941029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6941086 : List Nat := [4, 3, 1, 2, 1, 2, 3, 2, 5]
def baseStart_6941086 : Nat := 118140960795 + 6941086 * 2 ^ 59
def prefixEnd_6941086 : Nat := 4983230072969 + 3 ^ 40 * 6941086 * 2
def baseEnd_6941086 : Nat := 396012598021526133644837

theorem tailTrace_6941086 : CollatzResearch.WordTrace tailWord_6941086 prefixEnd_6941086 396012598021526133644837 := by
  unfold tailWord_6941086
  simp only [CollatzResearch.WordTrace]
  refine ⟨31645275566454792494495389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168774803021092226637308741 31645275566454792494495389)
  ·
    refine ⟨11866978337420547185435771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31645275566454792494495389 11866978337420547185435771)
    ·
      refine ⟨17800467506130820778153657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11866978337420547185435771 17800467506130820778153657)
      ·
        refine ⟨13350350629598115583615243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17800467506130820778153657 13350350629598115583615243)
        ·
          refine ⟨20025525944397173375422865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13350350629598115583615243 20025525944397173375422865)
          ·
            refine ⟨15019144458297880031567149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20025525944397173375422865 15019144458297880031567149)
            ·
              refine ⟨5632179171861705011837681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15019144458297880031567149 5632179171861705011837681)
              ·
                refine ⟨4224134378896278758878261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5632179171861705011837681 4224134378896278758878261)
                ·
                  refine ⟨396012598021526133644837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4224134378896278758878261 396012598021526133644837)
                  ·
                    rfl

theorem cell23_6941086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 3, 2, 5].length) (baseStart_6941086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6941086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6941086 prefixEnd_6941086 := by exact prefixLift 6941086
  have htrace : WordTrace (prefixWord ++ tailWord_6941086) baseStart_6941086 baseEnd_6941086 := by
    simpa [prefixWord, tailWord_6941086, baseEnd_6941086] using wordTrace_append hprefix tailTrace_6941086
  have hstable : (prefixWord ++ tailWord_6941086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6941086).length < 2 ^ (prefixWord ++ tailWord_6941086).sum := by decide
  have hdescent : baseEnd_6941086 < baseStart_6941086 := by decide
  rcases family_descends (prefixWord ++ tailWord_6941086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6941152 : List Nat := [2, 1, 1, 3, 1, 1, 4, 3, 3, 1, 3]
def baseStart_6941152 : Nat := 118140960795 + 6941152 * 2 ^ 59
def prefixEnd_6941152 : Nat := 4983230072969 + 3 ^ 40 * 6941152 * 2
def baseEnd_6941152 : Nat := 3564147271916931944578229

theorem tailTrace_6941152 : CollatzResearch.WordTrace tailWord_6941152 prefixEnd_6941152 3564147271916931944578229 := by
  unfold tailWord_6941152
  simp only [CollatzResearch.WordTrace]
  refine ⟨126582305874699616613932855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168776407832932822151910473 126582305874699616613932855)
  ·
    refine ⟨189873458812049424920899283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126582305874699616613932855 189873458812049424920899283)
    ·
      refine ⟨284810188218074137381348925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189873458812049424920899283 284810188218074137381348925)
      ·
        refine ⟨106803820581777801518005847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 284810188218074137381348925 106803820581777801518005847)
        ·
          refine ⟨160205730872666702277008771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106803820581777801518005847 160205730872666702277008771)
          ·
            refine ⟨240308596309000053415513157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160205730872666702277008771 240308596309000053415513157)
            ·
              refine ⟨45057861807937510015408717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 240308596309000053415513157 45057861807937510015408717)
              ·
                refine ⟨16896698177976566255778269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45057861807937510015408717 16896698177976566255778269)
                ·
                  refine ⟨6336261816741212345916851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16896698177976566255778269 6336261816741212345916851)
                  ·
                    refine ⟨9504392725111818518875277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6336261816741212345916851 9504392725111818518875277)
                    ·
                      refine ⟨3564147271916931944578229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9504392725111818518875277 3564147271916931944578229)
                      ·
                        rfl

theorem cell23_6941152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 3, 3, 1, 3].length) (baseStart_6941152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6941152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6941152 prefixEnd_6941152 := by exact prefixLift 6941152
  have htrace : WordTrace (prefixWord ++ tailWord_6941152) baseStart_6941152 baseEnd_6941152 := by
    simpa [prefixWord, tailWord_6941152, baseEnd_6941152] using wordTrace_append hprefix tailTrace_6941152
  have hstable : (prefixWord ++ tailWord_6941152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6941152).length < 2 ^ (prefixWord ++ tailWord_6941152).sum := by decide
  have hdescent : baseEnd_6941152 < baseStart_6941152 := by decide
  rcases family_descends (prefixWord ++ tailWord_6941152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6941173 : List Nat := [1, 3, 5, 1, 3, 1, 1, 1, 2, 2, 3]
def baseStart_6941173 : Nat := 118140960795 + 6941173 * 2 ^ 59
def prefixEnd_6941173 : Nat := 4983230072969 + 3 ^ 40 * 6941173 * 2
def baseEnd_6941173 : Nat := 3564158055010676362415633

theorem tailTrace_6941173 : CollatzResearch.WordTrace tailWord_6941173 prefixEnd_6941173 3564158055010676362415633 := by
  unfold tailWord_6941173
  simp only [CollatzResearch.WordTrace]
  refine ⟨253165377682323153814380173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168776918454882102542920115 253165377682323153814380173)
  ·
    refine ⟨94937016630871182680392565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 253165377682323153814380173 94937016630871182680392565)
    ·
      refine ⟨8900345309144173376286803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 94937016630871182680392565 8900345309144173376286803)
      ·
        refine ⟨13350517963716260064430205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8900345309144173376286803 13350517963716260064430205)
        ·
          refine ⟨5006444236393597524161327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13350517963716260064430205 5006444236393597524161327)
          ·
            refine ⟨7509666354590396286241991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5006444236393597524161327 7509666354590396286241991)
            ·
              refine ⟨11264499531885594429362987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7509666354590396286241991 11264499531885594429362987)
              ·
                refine ⟨16896749297828391644044481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11264499531885594429362987 16896749297828391644044481)
                ·
                  refine ⟨12672561973371293733033361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16896749297828391644044481 12672561973371293733033361)
                  ·
                    refine ⟨9504421480028470299775021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12672561973371293733033361 9504421480028470299775021)
                    ·
                      refine ⟨3564158055010676362415633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9504421480028470299775021 3564158055010676362415633)
                      ·
                        rfl

theorem cell23_6941173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 1, 1, 2, 2, 3].length) (baseStart_6941173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6941173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6941173 prefixEnd_6941173 := by exact prefixLift 6941173
  have htrace : WordTrace (prefixWord ++ tailWord_6941173) baseStart_6941173 baseEnd_6941173 := by
    simpa [prefixWord, tailWord_6941173, baseEnd_6941173] using wordTrace_append hprefix tailTrace_6941173
  have hstable : (prefixWord ++ tailWord_6941173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6941173).length < 2 ^ (prefixWord ++ tailWord_6941173).sum := by decide
  have hdescent : baseEnd_6941173 < baseStart_6941173 := by decide
  rcases family_descends (prefixWord ++ tailWord_6941173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6941205 : List Nat := [1, 3, 2, 1, 3, 1, 2, 2, 1, 1, 6]
def baseStart_6941205 : Nat := 118140960795 + 6941205 * 2 ^ 59
def prefixEnd_6941205 : Nat := 4983230072969 + 3 ^ 40 * 6941205 * 2
def baseEnd_6941205 : Nat := 3564174486391620237215485

theorem tailTrace_6941205 : CollatzResearch.WordTrace tailWord_6941205 prefixEnd_6941205 3564174486391620237215485 := by
  unfold tailWord_6941205
  simp only [CollatzResearch.WordTrace]
  refine ⟨253166544818207223279545069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168777696545471482186363379 253166544818207223279545069)
  ·
    refine ⟨94937454306827708729829401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 253166544818207223279545069 94937454306827708729829401)
    ·
      refine ⟨71203090730120781547372051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94937454306827708729829401 71203090730120781547372051)
      ·
        refine ⟨106804636095181172321058077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71203090730120781547372051 106804636095181172321058077)
        ·
          refine ⟨40051738535692939620396779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106804636095181172321058077 40051738535692939620396779)
          ·
            refine ⟨60077607803539409430595169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40051738535692939620396779 60077607803539409430595169)
            ·
              refine ⟨45058205852654557072946377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60077607803539409430595169 45058205852654557072946377)
              ·
                refine ⟨33793654389490917804709783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45058205852654557072946377 33793654389490917804709783)
                ·
                  refine ⟨50690481584236376707064675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33793654389490917804709783 50690481584236376707064675)
                  ·
                    refine ⟨76035722376354565060597013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50690481584236376707064675 76035722376354565060597013)
                    ·
                      refine ⟨3564174486391620237215485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76035722376354565060597013 3564174486391620237215485)
                      ·
                        rfl

theorem cell23_6941205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 2, 1, 1, 6].length) (baseStart_6941205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6941205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6941205 prefixEnd_6941205 := by exact prefixLift 6941205
  have htrace : WordTrace (prefixWord ++ tailWord_6941205) baseStart_6941205 baseEnd_6941205 := by
    simpa [prefixWord, tailWord_6941205, baseEnd_6941205] using wordTrace_append hprefix tailTrace_6941205
  have hstable : (prefixWord ++ tailWord_6941205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6941205).length < 2 ^ (prefixWord ++ tailWord_6941205).sum := by decide
  have hdescent : baseEnd_6941205 < baseStart_6941205 := by decide
  rcases family_descends (prefixWord ++ tailWord_6941205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6941212 : List Nat := [2, 2, 3, 1, 2, 3, 1, 2, 1, 1, 5]
def baseStart_6941212 : Nat := 118140960795 + 6941212 * 2 ^ 59
def prefixEnd_6941212 : Nat := 4983230072969 + 3 ^ 40 * 6941212 * 2
def baseEnd_6941212 : Nat := 3564178080756201709827953

theorem tailTrace_6941212 : CollatzResearch.WordTrace tailWord_6941212 prefixEnd_6941212 3564178080756201709827953 := by
  unfold tailWord_6941212
  simp only [CollatzResearch.WordTrace]
  refine ⟨126583400064590931737524945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168777866752787908983366593 126583400064590931737524945)
  ·
    refine ⟨94937550048443198803143709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126583400064590931737524945 94937550048443198803143709)
    ·
      refine ⟨35601581268166199551178891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94937550048443198803143709 35601581268166199551178891)
      ·
        refine ⟨53402371902249299326768337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35601581268166199551178891 53402371902249299326768337)
        ·
          refine ⟨40051778926686974495076253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53402371902249299326768337 40051778926686974495076253)
          ·
            refine ⟨15019417097507615435653595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40051778926686974495076253 15019417097507615435653595)
            ·
              refine ⟨22529125646261423153480393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15019417097507615435653595 22529125646261423153480393)
              ·
                refine ⟨16896844234696067365110295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22529125646261423153480393 16896844234696067365110295)
                ·
                  refine ⟨25345266352044101047665443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16896844234696067365110295 25345266352044101047665443)
                  ·
                    refine ⟨38017899528066151571498165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25345266352044101047665443 38017899528066151571498165)
                    ·
                      refine ⟨3564178080756201709827953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38017899528066151571498165 3564178080756201709827953)
                      ·
                        rfl

theorem cell23_6941212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 2, 1, 1, 5].length) (baseStart_6941212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6941212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6941212 prefixEnd_6941212 := by exact prefixLift 6941212
  have htrace : WordTrace (prefixWord ++ tailWord_6941212) baseStart_6941212 baseEnd_6941212 := by
    simpa [prefixWord, tailWord_6941212, baseEnd_6941212] using wordTrace_append hprefix tailTrace_6941212
  have hstable : (prefixWord ++ tailWord_6941212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6941212).length < 2 ^ (prefixWord ++ tailWord_6941212).sum := by decide
  have hdescent : baseEnd_6941212 < baseStart_6941212 := by decide
  rcases family_descends (prefixWord ++ tailWord_6941212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6941226 : List Nat := [3, 1, 4, 1, 1, 2, 2, 2, 3, 2, 2]
def baseStart_6941226 : Nat := 118140960795 + 6941226 * 2 ^ 59
def prefixEnd_6941226 : Nat := 4983230072969 + 3 ^ 40 * 6941226 * 2
def baseEnd_6941226 : Nat := 3564185269485364655052889

theorem tailTrace_6941226 : CollatzResearch.WordTrace tailWord_6941226 prefixEnd_6941226 3564185269485364655052889 := by
  unfold tailWord_6941226
  simp only [CollatzResearch.WordTrace]
  refine ⟨63291827687782785966514883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168778207167420762577373021 63291827687782785966514883)
  ·
    refine ⟨94937741531674178949772325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63291827687782785966514883 94937741531674178949772325)
    ·
      refine ⟨17800826537188908553082311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94937741531674178949772325 17800826537188908553082311)
      ·
        refine ⟨26701239805783362829623467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17800826537188908553082311 26701239805783362829623467)
        ·
          refine ⟨40051859708675044244435201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26701239805783362829623467 40051859708675044244435201)
          ·
            refine ⟨30038894781506283183326401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40051859708675044244435201 30038894781506283183326401)
            ·
              refine ⟨22529171086129712387494801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30038894781506283183326401 22529171086129712387494801)
              ·
                refine ⟨16896878314597284290621101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22529171086129712387494801 16896878314597284290621101)
                ·
                  refine ⟨6336329367973981608982913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16896878314597284290621101 6336329367973981608982913)
                  ·
                    refine ⟨4752247025980486206737185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6336329367973981608982913 4752247025980486206737185)
                    ·
                      refine ⟨3564185269485364655052889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4752247025980486206737185 3564185269485364655052889)
                      ·
                        rfl

theorem cell23_6941226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 2, 3, 2, 2].length) (baseStart_6941226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6941226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6941226 prefixEnd_6941226 := by exact prefixLift 6941226
  have htrace : WordTrace (prefixWord ++ tailWord_6941226) baseStart_6941226 baseEnd_6941226 := by
    simpa [prefixWord, tailWord_6941226, baseEnd_6941226] using wordTrace_append hprefix tailTrace_6941226
  have hstable : (prefixWord ++ tailWord_6941226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6941226).length < 2 ^ (prefixWord ++ tailWord_6941226).sum := by decide
  have hdescent : baseEnd_6941226 < baseStart_6941226 := by decide
  rcases family_descends (prefixWord ++ tailWord_6941226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6941246 : List Nat := [4, 2, 1, 4, 1, 1, 2, 1, 1, 1, 5]
def baseStart_6941246 : Nat := 118140960795 + 6941246 * 2 ^ 59
def prefixEnd_6941246 : Nat := 4983230072969 + 3 ^ 40 * 6941246 * 2
def baseEnd_6941246 : Nat := 3564195539098454576802797

theorem tailTrace_6941246 : CollatzResearch.WordTrace tailWord_6941246 prefixEnd_6941246 3564195539098454576802797 := by
  unfold tailWord_6941246
  simp only [CollatzResearch.WordTrace]
  refine ⟨31646005026382335910223449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168778693474039124854525061 31646005026382335910223449)
  ·
    refine ⟨23734503769786751932667587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31646005026382335910223449 23734503769786751932667587)
    ·
      refine ⟨35601755654680127899001381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23734503769786751932667587 35601755654680127899001381)
      ·
        refine ⟨6675329185252523981062759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35601755654680127899001381 6675329185252523981062759)
        ·
          refine ⟨10012993777878785971594139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6675329185252523981062759 10012993777878785971594139)
          ·
            refine ⟨15019490666818178957391209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10012993777878785971594139 15019490666818178957391209)
            ·
              refine ⟨11264618000113634218043407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15019490666818178957391209 11264618000113634218043407)
              ·
                refine ⟨16896927000170451327065111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11264618000113634218043407 16896927000170451327065111)
                ·
                  refine ⟨25345390500255676990597667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16896927000170451327065111 25345390500255676990597667)
                  ·
                    refine ⟨38018085750383515485896501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25345390500255676990597667 38018085750383515485896501)
                    ·
                      refine ⟨3564195539098454576802797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38018085750383515485896501 3564195539098454576802797)
                      ·
                        rfl

theorem cell23_6941246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_6941246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6941246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6941246 prefixEnd_6941246 := by exact prefixLift 6941246
  have htrace : WordTrace (prefixWord ++ tailWord_6941246) baseStart_6941246 baseEnd_6941246 := by
    simpa [prefixWord, tailWord_6941246, baseEnd_6941246] using wordTrace_append hprefix tailTrace_6941246
  have hstable : (prefixWord ++ tailWord_6941246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6941246).length < 2 ^ (prefixWord ++ tailWord_6941246).sum := by decide
  have hdescent : baseEnd_6941246 < baseStart_6941246 := by decide
  rcases family_descends (prefixWord ++ tailWord_6941246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6941299 : List Nat := [1, 1, 1, 2, 2, 1, 1, 6, 4, 2, 2]
def baseStart_6941299 : Nat := 118140960795 + 6941299 * 2 ^ 59
def prefixEnd_6941299 : Nat := 4983230072969 + 3 ^ 40 * 6941299 * 2
def baseEnd_6941299 : Nat := 3564222753573142869440053

theorem tailTrace_6941299 : CollatzResearch.WordTrace tailWord_6941299 prefixEnd_6941299 3564222753573142869440053 := by
  unfold tailWord_6941299
  simp only [CollatzResearch.WordTrace]
  refine ⟨253169973279866677333466951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168779982186577784888977967 253169973279866677333466951)
  ·
    refine ⟨379754959919800016000200427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253169973279866677333466951 379754959919800016000200427)
    ·
      refine ⟨569632439879700024000300641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379754959919800016000200427 569632439879700024000300641)
      ·
        refine ⟨427224329909775018000225481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 569632439879700024000300641 427224329909775018000225481)
        ·
          refine ⟨320418247432331263500169111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 427224329909775018000225481 320418247432331263500169111)
          ·
            refine ⟨480627371148496895250253667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 320418247432331263500169111 480627371148496895250253667)
            ·
              refine ⟨720941056722745342875380501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 480627371148496895250253667 720941056722745342875380501)
              ·
                refine ⟨33794112033878687947283461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 720941056722745342875380501 33794112033878687947283461)
                ·
                  refine ⟨6336396006352253990115649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33794112033878687947283461 6336396006352253990115649)
                  ·
                    refine ⟨4752297004764190492586737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6336396006352253990115649 4752297004764190492586737)
                    ·
                      refine ⟨3564222753573142869440053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4752297004764190492586737 3564222753573142869440053)
                      ·
                        rfl

theorem cell23_6941299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 6, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 6, 4, 2, 2].length) (baseStart_6941299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6941299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6941299 prefixEnd_6941299 := by exact prefixLift 6941299
  have htrace : WordTrace (prefixWord ++ tailWord_6941299) baseStart_6941299 baseEnd_6941299 := by
    simpa [prefixWord, tailWord_6941299, baseEnd_6941299] using wordTrace_append hprefix tailTrace_6941299
  have hstable : (prefixWord ++ tailWord_6941299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6941299).length < 2 ^ (prefixWord ++ tailWord_6941299).sum := by decide
  have hdescent : baseEnd_6941299 < baseStart_6941299 := by decide
  rcases family_descends (prefixWord ++ tailWord_6941299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6941315 : List Nat := [1, 1, 1, 3, 3, 1, 2, 1, 1, 2, 7]
def baseStart_6941315 : Nat := 118140960795 + 6941315 * 2 ^ 59
def prefixEnd_6941315 : Nat := 4983230072969 + 3 ^ 40 * 6941315 * 2
def baseEnd_6941315 : Nat := 3564230969263614806839979

theorem tailTrace_6941315 : CollatzResearch.WordTrace tailWord_6941315 prefixEnd_6941315 3564230969263614806839979 := by
  unfold tailWord_6941315
  simp only [CollatzResearch.WordTrace]
  refine ⟨253170556847808712066049399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168780371231872474710699599 253170556847808712066049399)
  ·
    refine ⟨379755835271713068099074099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253170556847808712066049399 379755835271713068099074099)
    ·
      refine ⟨569633752907569602148611149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379755835271713068099074099 569633752907569602148611149)
      ·
        refine ⟨213612657340338600805729181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 569633752907569602148611149 213612657340338600805729181)
        ·
          refine ⟨80104746502626975302148443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 213612657340338600805729181 80104746502626975302148443)
          ·
            refine ⟨120157119753940462953222665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80104746502626975302148443 120157119753940462953222665)
            ·
              refine ⟨90117839815455347214916999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120157119753940462953222665 90117839815455347214916999)
              ·
                refine ⟨135176759723183020822375499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90117839815455347214916999 135176759723183020822375499)
                ·
                  refine ⟨202765139584774531233563249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 135176759723183020822375499 202765139584774531233563249)
                  ·
                    refine ⟨152073854688580898425172437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 202765139584774531233563249 152073854688580898425172437)
                    ·
                      refine ⟨3564230969263614806839979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 152073854688580898425172437 3564230969263614806839979)
                      ·
                        rfl

theorem cell23_6941315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 2, 7].length) (baseStart_6941315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6941315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6941315 prefixEnd_6941315 := by exact prefixLift 6941315
  have htrace : WordTrace (prefixWord ++ tailWord_6941315) baseStart_6941315 baseEnd_6941315 := by
    simpa [prefixWord, tailWord_6941315, baseEnd_6941315] using wordTrace_append hprefix tailTrace_6941315
  have hstable : (prefixWord ++ tailWord_6941315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6941315).length < 2 ^ (prefixWord ++ tailWord_6941315).sum := by decide
  have hdescent : baseEnd_6941315 < baseStart_6941315 := by decide
  rcases family_descends (prefixWord ++ tailWord_6941315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6941354 : List Nat := [3, 1, 5, 2, 2, 1, 2, 1, 1, 3, 2]
def baseStart_6941354 : Nat := 118140960795 + 6941354 * 2 ^ 59
def prefixEnd_6941354 : Nat := 4983230072969 + 3 ^ 40 * 6941354 * 2
def baseEnd_6941354 : Nat := 3564250995009140154252301

theorem tailTrace_6941354 : CollatzResearch.WordTrace tailWord_6941354 prefixEnd_6941354 3564250995009140154252301 := by
  unfold tailWord_6941354
  simp only [CollatzResearch.WordTrace]
  refine ⟨63292994823666855431679779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168781319529778281151146077 63292994823666855431679779)
  ·
    refine ⟨94939492235500283147519669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63292994823666855431679779 94939492235500283147519669)
    ·
      refine ⟨8900577397078151545079969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 94939492235500283147519669 8900577397078151545079969)
      ·
        refine ⟨6675433047808613658809977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8900577397078151545079969 6675433047808613658809977)
        ·
          refine ⟨5006574785856460244107483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6675433047808613658809977 5006574785856460244107483)
          ·
            refine ⟨7509862178784690366161225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5006574785856460244107483 7509862178784690366161225)
            ·
              refine ⟨5632396634088517774620919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7509862178784690366161225 5632396634088517774620919)
              ·
                refine ⟨8448594951132776661931379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5632396634088517774620919 8448594951132776661931379)
                ·
                  refine ⟨12672892426699164992897069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8448594951132776661931379 12672892426699164992897069)
                  ·
                    refine ⟨4752334660012186872336401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12672892426699164992897069 4752334660012186872336401)
                    ·
                      refine ⟨3564250995009140154252301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4752334660012186872336401 3564250995009140154252301)
                      ·
                        rfl

theorem cell23_6941354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_6941354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6941354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6941354 prefixEnd_6941354 := by exact prefixLift 6941354
  have htrace : WordTrace (prefixWord ++ tailWord_6941354) baseStart_6941354 baseEnd_6941354 := by
    simpa [prefixWord, tailWord_6941354, baseEnd_6941354] using wordTrace_append hprefix tailTrace_6941354
  have hstable : (prefixWord ++ tailWord_6941354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6941354).length < 2 ^ (prefixWord ++ tailWord_6941354).sum := by decide
  have hdescent : baseEnd_6941354 < baseStart_6941354 := by decide
  rcases family_descends (prefixWord ++ tailWord_6941354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6941399 : List Nat := [1, 1, 3, 2, 1, 4, 2, 2, 3, 4]
def baseStart_6941399 : Nat := 118140960795 + 6941399 * 2 ^ 59
def prefixEnd_6941399 : Nat := 4983230072969 + 3 ^ 40 * 6941399 * 2
def baseEnd_6941399 : Nat := 1188091367212864159396531

theorem tailTrace_6941399 : CollatzResearch.WordTrace tailWord_6941399 prefixEnd_6941399 1188091367212864159396531 := by
  unfold tailWord_6941399
  simp only [CollatzResearch.WordTrace]
  refine ⟨253173620579504394412107251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168782413719669596274738167 253173620579504394412107251)
  ·
    refine ⟨379760430869256591618160877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253173620579504394412107251 379760430869256591618160877)
    ·
      refine ⟨142410161575971221856810329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 379760430869256591618160877 142410161575971221856810329)
      ·
        refine ⟨106807621181978416392607747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142410161575971221856810329 106807621181978416392607747)
        ·
          refine ⟨160211431772967624588911621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106807621181978416392607747 160211431772967624588911621)
          ·
            refine ⟨30039643457431429610420929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 160211431772967624588911621 30039643457431429610420929)
            ·
              refine ⟨22529732593073572207815697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30039643457431429610420929 22529732593073572207815697)
              ·
                refine ⟨16897299444805179155861773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22529732593073572207815697 16897299444805179155861773)
                ·
                  refine ⟨6336487291801942183448165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16897299444805179155861773 6336487291801942183448165)
                  ·
                    refine ⟨1188091367212864159396531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6336487291801942183448165 1188091367212864159396531)
                    ·
                      rfl

theorem cell23_6941399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 2, 3, 4].length) (baseStart_6941399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6941399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6941399 prefixEnd_6941399 := by exact prefixLift 6941399
  have htrace : WordTrace (prefixWord ++ tailWord_6941399) baseStart_6941399 baseEnd_6941399 := by
    simpa [prefixWord, tailWord_6941399, baseEnd_6941399] using wordTrace_append hprefix tailTrace_6941399
  have hstable : (prefixWord ++ tailWord_6941399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6941399).length < 2 ^ (prefixWord ++ tailWord_6941399).sum := by decide
  have hdescent : baseEnd_6941399 < baseStart_6941399 := by decide
  rcases family_descends (prefixWord ++ tailWord_6941399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6941402 : List Nat := [3, 1, 1, 2, 2, 2, 1, 1, 2, 4, 4]
def baseStart_6941402 : Nat := 118140960795 + 6941402 * 2 ^ 59
def prefixEnd_6941402 : Nat := 4983230072969 + 3 ^ 40 * 6941402 * 2
def baseEnd_6941402 : Nat := 3564275642080555966452079

theorem tailTrace_6941402 : CollatzResearch.WordTrace tailWord_6941402 prefixEnd_6941402 3564275642080555966452079 := by
  unfold tailWord_6941402
  simp only [CollatzResearch.WordTrace]
  refine ⟨63293432499623381481116615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168782486665662350616310973 63293432499623381481116615)
  ·
    refine ⟨94940148749435072221674923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63293432499623381481116615 94940148749435072221674923)
    ·
      refine ⟨142410223124152608332512385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94940148749435072221674923 142410223124152608332512385)
      ·
        refine ⟨106807667343114456249384289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142410223124152608332512385 106807667343114456249384289)
        ·
          refine ⟨80105750507335842187038217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106807667343114456249384289 80105750507335842187038217)
          ·
            refine ⟨60079312880501881640278663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80105750507335842187038217 60079312880501881640278663)
            ·
              refine ⟨90118969320752822460417995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60079312880501881640278663 90118969320752822460417995)
              ·
                refine ⟨135178453981129233690626993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90118969320752822460417995 135178453981129233690626993)
                ·
                  refine ⟨101383840485846925267970245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 135178453981129233690626993 101383840485846925267970245)
                  ·
                    refine ⟨19009470091096298487744421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 101383840485846925267970245 19009470091096298487744421)
                    ·
                      refine ⟨3564275642080555966452079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19009470091096298487744421 3564275642080555966452079)
                      ·
                        rfl

theorem cell23_6941402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 2, 4, 4].length) (baseStart_6941402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6941402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6941402 prefixEnd_6941402 := by exact prefixLift 6941402
  have htrace : WordTrace (prefixWord ++ tailWord_6941402) baseStart_6941402 baseEnd_6941402 := by
    simpa [prefixWord, tailWord_6941402, baseEnd_6941402] using wordTrace_append hprefix tailTrace_6941402
  have hstable : (prefixWord ++ tailWord_6941402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6941402).length < 2 ^ (prefixWord ++ tailWord_6941402).sum := by decide
  have hdescent : baseEnd_6941402 < baseStart_6941402 := by decide
  rcases family_descends (prefixWord ++ tailWord_6941402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6941409 : List Nat := [1, 2, 3, 1, 4, 1, 2, 1, 1, 4, 3]
def baseStart_6941409 : Nat := 118140960795 + 6941409 * 2 ^ 59
def prefixEnd_6941409 : Nat := 4983230072969 + 3 ^ 40 * 6941409 * 2
def baseEnd_6941409 : Nat := 3564279236445137439064547

theorem tailTrace_6941409 : CollatzResearch.WordTrace tailWord_6941409 prefixEnd_6941409 3564279236445137439064547 := by
  unfold tailWord_6941409
  simp only [CollatzResearch.WordTrace]
  refine ⟨253173985309468166119971281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168782656872978777413314187 253173985309468166119971281)
  ·
    refine ⟨189880488982101124589978461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253173985309468166119971281 189880488982101124589978461)
    ·
      refine ⟨71205183368287921721241923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189880488982101124589978461 71205183368287921721241923)
      ·
        refine ⟨106807775052431882581862885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71205183368287921721241923 106807775052431882581862885)
        ·
          refine ⟨20026457822330977984099291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 106807775052431882581862885 20026457822330977984099291)
          ·
            refine ⟨30039686733496466976148937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20026457822330977984099291 30039686733496466976148937)
            ·
              refine ⟨22529765050122350232111703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30039686733496466976148937 22529765050122350232111703)
              ·
                refine ⟨33794647575183525348167555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22529765050122350232111703 33794647575183525348167555)
                ·
                  refine ⟨50691971362775288022251333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33794647575183525348167555 50691971362775288022251333)
                  ·
                    refine ⟨9504744630520366504172125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50691971362775288022251333 9504744630520366504172125)
                    ·
                      refine ⟨3564279236445137439064547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9504744630520366504172125 3564279236445137439064547)
                      ·
                        rfl

theorem cell23_6941409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 1, 1, 4, 3].length) (baseStart_6941409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6941409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6941409 prefixEnd_6941409 := by exact prefixLift 6941409
  have htrace : WordTrace (prefixWord ++ tailWord_6941409) baseStart_6941409 baseEnd_6941409 := by
    simpa [prefixWord, tailWord_6941409, baseEnd_6941409] using wordTrace_append hprefix tailTrace_6941409
  have hstable : (prefixWord ++ tailWord_6941409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6941409).length < 2 ^ (prefixWord ++ tailWord_6941409).sum := by decide
  have hdescent : baseEnd_6941409 < baseStart_6941409 := by decide
  rcases family_descends (prefixWord ++ tailWord_6941409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6941412 : List Nat := [2, 3, 1, 1, 1, 4, 1, 2, 8]
def baseStart_6941412 : Nat := 118140960795 + 6941412 * 2 ^ 59
def prefixEnd_6941412 : Nat := 4983230072969 + 3 ^ 40 * 6941412 * 2
def baseEnd_6941412 : Nat := 396031197431900103036337

theorem tailTrace_6941412 : CollatzResearch.WordTrace tailWord_6941412 prefixEnd_6941412 396031197431900103036337 := by
  unfold tailWord_6941412
  simp only [CollatzResearch.WordTrace]
  refine ⟨126587047364228648816165245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168782729818971531754886993 126587047364228648816165245)
  ·
    refine ⟨47470142761585743306061967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126587047364228648816165245 47470142761585743306061967)
    ·
      refine ⟨71205214142378614959092951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47470142761585743306061967 71205214142378614959092951)
      ·
        refine ⟨106807821213567922438639427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71205214142378614959092951 106807821213567922438639427)
        ·
          refine ⟨160211731820351883657959141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106807821213567922438639427 160211731820351883657959141)
          ·
            refine ⟨30039699716315978185867339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 160211731820351883657959141 30039699716315978185867339)
            ·
              refine ⟨45059549574473967278801009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30039699716315978185867339 45059549574473967278801009)
              ·
                refine ⟨33794662180855475459100757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45059549574473967278801009 33794662180855475459100757)
                ·
                  refine ⟨396031197431900103036337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33794662180855475459100757 396031197431900103036337)
                  ·
                    rfl

theorem cell23_6941412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 2, 8].length) (baseStart_6941412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6941412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6941412 prefixEnd_6941412 := by exact prefixLift 6941412
  have htrace : WordTrace (prefixWord ++ tailWord_6941412) baseStart_6941412 baseEnd_6941412 := by
    simpa [prefixWord, tailWord_6941412, baseEnd_6941412] using wordTrace_append hprefix tailTrace_6941412
  have hstable : (prefixWord ++ tailWord_6941412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6941412).length < 2 ^ (prefixWord ++ tailWord_6941412).sum := by decide
  have hdescent : baseEnd_6941412 < baseStart_6941412 := by decide
  rcases family_descends (prefixWord ++ tailWord_6941412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6941426 : List Nat := [3, 2, 1, 3, 1, 3, 1, 2, 2, 2, 3]
def baseStart_6941426 : Nat := 118140960795 + 6941426 * 2 ^ 59
def prefixEnd_6941426 : Nat := 4983230072969 + 3 ^ 40 * 6941426 * 2
def baseEnd_6941426 : Nat := 3564287965616263872551969

theorem tailTrace_6941426 : CollatzResearch.WordTrace tailWord_6941426 prefixEnd_6941426 3564287965616263872551969 := by
  unfold tailWord_6941426
  simp only [CollatzResearch.WordTrace]
  refine ⟨63293651337601644505835033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168783070233604385348893421 63293651337601644505835033)
  ·
    refine ⟨47470238503201233379376275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63293651337601644505835033 47470238503201233379376275)
    ·
      refine ⟨71205357754801850069064413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47470238503201233379376275 71205357754801850069064413)
      ·
        refine ⟨26702009158050693775899155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71205357754801850069064413 26702009158050693775899155)
        ·
          refine ⟨40053013737076040663848733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26702009158050693775899155 40053013737076040663848733)
          ·
            refine ⟨15019880151403515248943275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40053013737076040663848733 15019880151403515248943275)
            ·
              refine ⟨22529820227105272873414913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15019880151403515248943275 22529820227105272873414913)
              ·
                refine ⟨16897365170328954655061185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22529820227105272873414913 16897365170328954655061185)
                ·
                  refine ⟨12673023877746715991295889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16897365170328954655061185 12673023877746715991295889)
                  ·
                    refine ⟨9504767908310036993471917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12673023877746715991295889 9504767908310036993471917)
                    ·
                      refine ⟨3564287965616263872551969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9504767908310036993471917 3564287965616263872551969)
                      ·
                        rfl

theorem cell23_6941426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 2, 2, 2, 3].length) (baseStart_6941426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6941426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6941426 prefixEnd_6941426 := by exact prefixLift 6941426
  have htrace : WordTrace (prefixWord ++ tailWord_6941426) baseStart_6941426 baseEnd_6941426 := by
    simpa [prefixWord, tailWord_6941426, baseEnd_6941426] using wordTrace_append hprefix tailTrace_6941426
  have hstable : (prefixWord ++ tailWord_6941426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6941426).length < 2 ^ (prefixWord ++ tailWord_6941426).sum := by decide
  have hdescent : baseEnd_6941426 < baseStart_6941426 := by decide
  rcases family_descends (prefixWord ++ tailWord_6941426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6941449 : List Nat := [1, 2, 1, 1, 3, 2, 2, 1, 3, 5, 2]
def baseStart_6941449 : Nat := 118140960795 + 6941449 * 2 ^ 59
def prefixEnd_6941449 : Nat := 4983230072969 + 3 ^ 40 * 6941449 * 2
def baseEnd_6941449 : Nat := 3564299775671317282564363

theorem tailTrace_6941449 : CollatzResearch.WordTrace tailWord_6941449 prefixEnd_6941449 3564299775671317282564363 := by
  unfold tailWord_6941449
  simp only [CollatzResearch.WordTrace]
  refine ⟨253175444229323252951427401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168783629486215501967618267 253175444229323252951427401)
  ·
    refine ⟨189881583171992439713570551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253175444229323252951427401 189881583171992439713570551)
    ·
      refine ⟨284822374757988659570355827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189881583171992439713570551 284822374757988659570355827)
      ·
        refine ⟨427233562136982989355533741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284822374757988659570355827 427233562136982989355533741)
        ·
          refine ⟨160212585801368621008325153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 427233562136982989355533741 160212585801368621008325153)
          ·
            refine ⟨120159439351026465756243865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160212585801368621008325153 120159439351026465756243865)
            ·
              refine ⟨90119579513269849317182899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120159439351026465756243865 90119579513269849317182899)
              ·
                refine ⟨135179369269904773975774349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90119579513269849317182899 135179369269904773975774349)
                ·
                  refine ⟨50692263476214290240915381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 135179369269904773975774349 50692263476214290240915381)
                  ·
                    refine ⟨4752399700895089710085817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50692263476214290240915381 4752399700895089710085817)
                    ·
                      refine ⟨3564299775671317282564363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4752399700895089710085817 3564299775671317282564363)
                      ·
                        rfl

theorem cell23_6941449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 3, 5, 2].length) (baseStart_6941449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6941449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6941449 prefixEnd_6941449 := by exact prefixLift 6941449
  have htrace : WordTrace (prefixWord ++ tailWord_6941449) baseStart_6941449 baseEnd_6941449 := by
    simpa [prefixWord, tailWord_6941449, baseEnd_6941449] using wordTrace_append hprefix tailTrace_6941449
  have hstable : (prefixWord ++ tailWord_6941449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6941449).length < 2 ^ (prefixWord ++ tailWord_6941449).sum := by decide
  have hdescent : baseEnd_6941449 < baseStart_6941449 := by decide
  rcases family_descends (prefixWord ++ tailWord_6941449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6941473 : List Nat := [1, 2, 3, 2, 1, 2, 2, 5, 1, 1, 3]
def baseStart_6941473 : Nat := 118140960795 + 6941473 * 2 ^ 59
def prefixEnd_6941473 : Nat := 4983230072969 + 3 ^ 40 * 6941473 * 2
def baseEnd_6941473 : Nat := 3564312099207025188664253

theorem tailTrace_6941473 : CollatzResearch.WordTrace tailWord_6941473 prefixEnd_6941473 3564312099207025188664253 := by
  unfold tailWord_6941473
  simp only [CollatzResearch.WordTrace]
  refine ⟨253176319581236305050301073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168784213054157536700200715 253176319581236305050301073)
  ·
    refine ⟨189882239685927228787725805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253176319581236305050301073 189882239685927228787725805)
    ·
      refine ⟨71205839882222710795397177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189882239685927228787725805 71205839882222710795397177)
      ·
        refine ⟨53404379911667033096547883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71205839882222710795397177 53404379911667033096547883)
        ·
          refine ⟨80106569867500549644821825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53404379911667033096547883 80106569867500549644821825)
          ·
            refine ⟨60079927400625412233616369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80106569867500549644821825 60079927400625412233616369)
            ·
              refine ⟨45059945550469059175212277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60079927400625412233616369 45059945550469059175212277)
              ·
                refine ⟨4224369895356474297676151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45059945550469059175212277 4224369895356474297676151)
                ·
                  refine ⟨6336554843034711446514227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4224369895356474297676151 6336554843034711446514227)
                  ·
                    refine ⟨9504832264552067169771341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6336554843034711446514227 9504832264552067169771341)
                    ·
                      refine ⟨3564312099207025188664253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9504832264552067169771341 3564312099207025188664253)
                      ·
                        rfl

theorem cell23_6941473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 5, 1, 1, 3].length) (baseStart_6941473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6941473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6941473 prefixEnd_6941473 := by exact prefixLift 6941473
  have htrace : WordTrace (prefixWord ++ tailWord_6941473) baseStart_6941473 baseEnd_6941473 := by
    simpa [prefixWord, tailWord_6941473, baseEnd_6941473] using wordTrace_append hprefix tailTrace_6941473
  have hstable : (prefixWord ++ tailWord_6941473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6941473).length < 2 ^ (prefixWord ++ tailWord_6941473).sum := by decide
  have hdescent : baseEnd_6941473 < baseStart_6941473 := by decide
  rcases family_descends (prefixWord ++ tailWord_6941473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6941513 : List Nat := [1, 2, 1, 1, 2, 6, 1, 2, 3, 2, 2]
def baseStart_6941513 : Nat := 118140960795 + 6941513 * 2 ^ 59
def prefixEnd_6941513 : Nat := 4983230072969 + 3 ^ 40 * 6941513 * 2
def baseEnd_6941513 : Nat := 3564332638433205032164069

theorem tailTrace_6941513 : CollatzResearch.WordTrace tailWord_6941513 prefixEnd_6941513 3564332638433205032164069 := by
  unfold tailWord_6941513
  simp only [CollatzResearch.WordTrace]
  refine ⟨253177778501091391881757193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168785185667394261254504795 253177778501091391881757193)
  ·
    refine ⟨189883333875818543911317895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253177778501091391881757193 189883333875818543911317895)
    ·
      refine ⟨284825000813727815866976843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189883333875818543911317895 284825000813727815866976843)
      ·
        refine ⟨427237501220591723800465265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284825000813727815866976843 427237501220591723800465265)
        ·
          refine ⟨320428125915443792850348949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 427237501220591723800465265 320428125915443792850348949)
          ·
            refine ⟨15020068402286427789860107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 320428125915443792850348949 15020068402286427789860107)
            ·
              refine ⟨22530102603429641684790161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15020068402286427789860107 22530102603429641684790161)
              ·
                refine ⟨16897576952572231263592621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22530102603429641684790161 16897576952572231263592621)
                ·
                  refine ⟨6336591357214586723847233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16897576952572231263592621 6336591357214586723847233)
                  ·
                    refine ⟨4752443517910940042885425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6336591357214586723847233 4752443517910940042885425)
                    ·
                      refine ⟨3564332638433205032164069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4752443517910940042885425 3564332638433205032164069)
                      ·
                        rfl

theorem cell23_6941513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 2, 3, 2, 2].length) (baseStart_6941513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6941513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6941513 prefixEnd_6941513 := by exact prefixLift 6941513
  have htrace : WordTrace (prefixWord ++ tailWord_6941513) baseStart_6941513 baseEnd_6941513 := by
    simpa [prefixWord, tailWord_6941513, baseEnd_6941513] using wordTrace_append hprefix tailTrace_6941513
  have hstable : (prefixWord ++ tailWord_6941513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6941513).length < 2 ^ (prefixWord ++ tailWord_6941513).sum := by decide
  have hdescent : baseEnd_6941513 < baseStart_6941513 := by decide
  rcases family_descends (prefixWord ++ tailWord_6941513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6941516 : List Nat := [2, 2, 1, 3, 3, 1, 2, 1, 3, 2, 3]
def baseStart_6941516 : Nat := 118140960795 + 6941516 * 2 ^ 59
def prefixEnd_6941516 : Nat := 4983230072969 + 3 ^ 40 * 6941516 * 2
def baseEnd_6941516 : Nat := 3564334178875168520426555

theorem tailTrace_6941516 : CollatzResearch.WordTrace tailWord_6941516 prefixEnd_6941516 3564334178875168520426555 := by
  unfold tailWord_6941516
  simp only [CollatzResearch.WordTrace]
  refine ⟨126588943960040261697058201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168785258613387015596077601 126588943960040261697058201)
  ·
    refine ⟨94941707970030196272793651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126588943960040261697058201 94941707970030196272793651)
    ·
      refine ⟨142412561955045294409190477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94941707970030196272793651 142412561955045294409190477)
      ·
        refine ⟨53404710733141985403446429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142412561955045294409190477 53404710733141985403446429)
        ·
          refine ⟨20026766524928244526292411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53404710733141985403446429 20026766524928244526292411)
          ·
            refine ⟨30040149787392366789438617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20026766524928244526292411 30040149787392366789438617)
            ·
              refine ⟨22530112340544275092078963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30040149787392366789438617 22530112340544275092078963)
              ·
                refine ⟨33795168510816412638118445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22530112340544275092078963 33795168510816412638118445)
                ·
                  refine ⟨12673188191556154739294417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33795168510816412638118445 12673188191556154739294417)
                  ·
                    refine ⟨9504891143667116054470813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12673188191556154739294417 9504891143667116054470813)
                    ·
                      refine ⟨3564334178875168520426555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9504891143667116054470813 3564334178875168520426555)
                      ·
                        rfl

theorem cell23_6941516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 1, 3, 2, 3].length) (baseStart_6941516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6941516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6941516 prefixEnd_6941516 := by exact prefixLift 6941516
  have htrace : WordTrace (prefixWord ++ tailWord_6941516) baseStart_6941516 baseEnd_6941516 := by
    simpa [prefixWord, tailWord_6941516, baseEnd_6941516] using wordTrace_append hprefix tailTrace_6941516
  have hstable : (prefixWord ++ tailWord_6941516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6941516).length < 2 ^ (prefixWord ++ tailWord_6941516).sum := by decide
  have hdescent : baseEnd_6941516 < baseStart_6941516 := by decide
  rcases family_descends (prefixWord ++ tailWord_6941516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6941517 : List Nat := [1, 6, 1, 2, 2, 2, 1, 1, 2, 3, 2]
def baseStart_6941517 : Nat := 118140960795 + 6941517 * 2 ^ 59
def prefixEnd_6941517 : Nat := 4983230072969 + 3 ^ 40 * 6941517 * 2
def baseEnd_6941517 : Nat := 3564334692355823016514051

theorem tailTrace_6941517 : CollatzResearch.WordTrace tailWord_6941517 prefixEnd_6941517 3564334692355823016514051 := by
  unfold tailWord_6941517
  simp only [CollatzResearch.WordTrace]
  refine ⟨253177924393076900564902805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168785282928717933709935203 253177924393076900564902805)
  ·
    refine ⟨11867715205925479713979819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 253177924393076900564902805 11867715205925479713979819)
    ·
      refine ⟨17801572808888219570969729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11867715205925479713979819 17801572808888219570969729)
      ·
        refine ⟨13351179606666164678227297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17801572808888219570969729 13351179606666164678227297)
        ·
          refine ⟨10013384704999623508670473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13351179606666164678227297 10013384704999623508670473)
          ·
            refine ⟨7510038528749717631502855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10013384704999623508670473 7510038528749717631502855)
            ·
              refine ⟨11265057793124576447254283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7510038528749717631502855 11265057793124576447254283)
              ·
                refine ⟨16897586689686864670881425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11265057793124576447254283 16897586689686864670881425)
                ·
                  refine ⟨12673190017265148503161069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16897586689686864670881425 12673190017265148503161069)
                  ·
                    refine ⟨4752446256474430688685401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12673190017265148503161069 4752446256474430688685401)
                    ·
                      refine ⟨3564334692355823016514051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4752446256474430688685401 3564334692355823016514051)
                      ·
                        rfl

theorem cell23_6941517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 1, 1, 2, 3, 2].length) (baseStart_6941517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6941517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6941517 prefixEnd_6941517 := by exact prefixLift 6941517
  have htrace : WordTrace (prefixWord ++ tailWord_6941517) baseStart_6941517 baseEnd_6941517 := by
    simpa [prefixWord, tailWord_6941517, baseEnd_6941517] using wordTrace_append hprefix tailTrace_6941517
  have hstable : (prefixWord ++ tailWord_6941517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6941517).length < 2 ^ (prefixWord ++ tailWord_6941517).sum := by decide
  have hdescent : baseEnd_6941517 < baseStart_6941517 := by decide
  rcases family_descends (prefixWord ++ tailWord_6941517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6941530 : List Nat := [3, 1, 1, 2, 1, 4, 1, 5, 1, 2, 2]
def baseStart_6941530 : Nat := 118140960795 + 6941530 * 2 ^ 59
def prefixEnd_6941530 : Nat := 4983230072969 + 3 ^ 40 * 6941530 * 2
def baseEnd_6941530 : Nat := 3564341367604331465651491

theorem tailTrace_6941530 : CollatzResearch.WordTrace tailWord_6941530 prefixEnd_6941530 3564341367604331465651491 := by
  unfold tailWord_6941530
  simp only [CollatzResearch.WordTrace]
  refine ⟨63294599635507450946281511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168785599028019869190084029 63294599635507450946281511)
  ·
    refine ⟨94941899453261176419422267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63294599635507450946281511 94941899453261176419422267)
    ·
      refine ⟨142412849179891764629133401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94941899453261176419422267 142412849179891764629133401)
      ·
        refine ⟨106809636884918823471850051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142412849179891764629133401 106809636884918823471850051)
        ·
          refine ⟨160214455327378235207775077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106809636884918823471850051 160214455327378235207775077)
          ·
            refine ⟨30040210373883419101457827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 160214455327378235207775077 30040210373883419101457827)
            ·
              refine ⟨45060315560825128652186741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30040210373883419101457827 45060315560825128652186741)
              ·
                refine ⟨4224404583827355811142507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45060315560825128652186741 4224404583827355811142507)
                ·
                  refine ⟨6336606875741033716713761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4224404583827355811142507 6336606875741033716713761)
                  ·
                    refine ⟨4752455156805775287535321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6336606875741033716713761 4752455156805775287535321)
                    ·
                      refine ⟨3564341367604331465651491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4752455156805775287535321 3564341367604331465651491)
                      ·
                        rfl

theorem cell23_6941530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 5, 1, 2, 2].length) (baseStart_6941530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6941530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6941530 prefixEnd_6941530 := by exact prefixLift 6941530
  have htrace : WordTrace (prefixWord ++ tailWord_6941530) baseStart_6941530 baseEnd_6941530 := by
    simpa [prefixWord, tailWord_6941530, baseEnd_6941530] using wordTrace_append hprefix tailTrace_6941530
  have hstable : (prefixWord ++ tailWord_6941530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6941530).length < 2 ^ (prefixWord ++ tailWord_6941530).sum := by decide
  have hdescent : baseEnd_6941530 < baseStart_6941530 := by decide
  rcases family_descends (prefixWord ++ tailWord_6941530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6941573 : List Nat := [1, 3, 1, 1, 3, 3, 1, 4, 1, 3, 2]
def baseStart_6941573 : Nat := 118140960795 + 6941573 * 2 ^ 59
def prefixEnd_6941573 : Nat := 4983230072969 + 3 ^ 40 * 6941573 * 2
def baseEnd_6941573 : Nat := 3564363447272474797413793

theorem tailTrace_6941573 : CollatzResearch.WordTrace tailWord_6941573 prefixEnd_6941573 3564363447272474797413793 := by
  unfold tailWord_6941573
  simp only [CollatzResearch.WordTrace]
  refine ⟨253179966880874022128941373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168786644587249348085960915 253179966880874022128941373)
  ·
    refine ⟨94942487580327758298353015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 253179966880874022128941373 94942487580327758298353015)
    ·
      refine ⟨142413731370491637447529523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94942487580327758298353015 142413731370491637447529523)
      ·
        refine ⟨213620597055737456171294285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142413731370491637447529523 213620597055737456171294285)
        ·
          refine ⟨80107723895901546064235357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 213620597055737456171294285 80107723895901546064235357)
          ·
            refine ⟨30040396460963079774088259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80107723895901546064235357 30040396460963079774088259)
            ·
              refine ⟨45060594691444619661132389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30040396460963079774088259 45060594691444619661132389)
              ·
                refine ⟨8448861504645866186462323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45060594691444619661132389 8448861504645866186462323)
                ·
                  refine ⟨12673292256968799279693485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8448861504645866186462323 12673292256968799279693485)
                  ·
                    refine ⟨4752484596363299729885057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12673292256968799279693485 4752484596363299729885057)
                    ·
                      refine ⟨3564363447272474797413793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4752484596363299729885057 3564363447272474797413793)
                      ·
                        rfl

theorem cell23_6941573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 4, 1, 3, 2].length) (baseStart_6941573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6941573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6941573 prefixEnd_6941573 := by exact prefixLift 6941573
  have htrace : WordTrace (prefixWord ++ tailWord_6941573) baseStart_6941573 baseEnd_6941573 := by
    simpa [prefixWord, tailWord_6941573, baseEnd_6941573] using wordTrace_append hprefix tailTrace_6941573
  have hstable : (prefixWord ++ tailWord_6941573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6941573).length < 2 ^ (prefixWord ++ tailWord_6941573).sum := by decide
  have hdescent : baseEnd_6941573 < baseStart_6941573 := by decide
  rcases family_descends (prefixWord ++ tailWord_6941573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6941589 : List Nat := [1, 3, 2, 1, 1, 4, 1, 1, 1, 3, 5]
def baseStart_6941589 : Nat := 118140960795 + 6941589 * 2 ^ 59
def prefixEnd_6941589 : Nat := 4983230072969 + 3 ^ 40 * 6941589 * 2
def baseEnd_6941589 : Nat := 3564371662962946734813719

theorem tailTrace_6941589 : CollatzResearch.WordTrace tailWord_6941589 prefixEnd_6941589 3564371662962946734813719 := by
  unfold tailWord_6941589
  simp only [CollatzResearch.WordTrace]
  refine ⟨253180550448816056861523821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168787033632544037907682547 253180550448816056861523821)
  ·
    refine ⟨94942706418306021323071433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 253180550448816056861523821 94942706418306021323071433)
    ·
      refine ⟨71207029813729515992303575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94942706418306021323071433 71207029813729515992303575)
      ·
        refine ⟨106810544720594273988455363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71207029813729515992303575 106810544720594273988455363)
        ·
          refine ⟨160215817080891410982683045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106810544720594273988455363 160215817080891410982683045)
          ·
            refine ⟨30040465702667139559253071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 160215817080891410982683045 30040465702667139559253071)
            ·
              refine ⟨45060698554000709338879607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30040465702667139559253071 45060698554000709338879607)
              ·
                refine ⟨67591047831001064008319411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45060698554000709338879607 67591047831001064008319411)
                ·
                  refine ⟨101386571746501596012479117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67591047831001064008319411 101386571746501596012479117)
                  ·
                    refine ⟨38019964404938098504679669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 101386571746501596012479117 38019964404938098504679669)
                    ·
                      refine ⟨3564371662962946734813719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38019964404938098504679669 3564371662962946734813719)
                      ·
                        rfl

theorem cell23_6941589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 1, 1, 3, 5].length) (baseStart_6941589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6941589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6941589 prefixEnd_6941589 := by exact prefixLift 6941589
  have htrace : WordTrace (prefixWord ++ tailWord_6941589) baseStart_6941589 baseEnd_6941589 := by
    simpa [prefixWord, tailWord_6941589, baseEnd_6941589] using wordTrace_append hprefix tailTrace_6941589
  have hstable : (prefixWord ++ tailWord_6941589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6941589).length < 2 ^ (prefixWord ++ tailWord_6941589).sum := by decide
  have hdescent : baseEnd_6941589 < baseStart_6941589 := by decide
  rcases family_descends (prefixWord ++ tailWord_6941589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6941603 : List Nat := [1, 1, 1, 4, 1, 2, 4, 1, 4, 2, 2]
def baseStart_6941603 : Nat := 118140960795 + 6941603 * 2 ^ 59
def prefixEnd_6941603 : Nat := 4983230072969 + 3 ^ 40 * 6941603 * 2
def baseEnd_6941603 : Nat := 3564378851692109680038655

theorem tailTrace_6941603 : CollatzResearch.WordTrace tailWord_6941603 prefixEnd_6941603 3564378851692109680038655 := by
  unfold tailWord_6941603
  simp only [CollatzResearch.WordTrace]
  refine ⟨253181061070765337252533463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168787374047176891501688975 253181061070765337252533463)
  ·
    refine ⟨379771591606148005878800195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253181061070765337252533463 379771591606148005878800195)
    ·
      refine ⟨569657387409222008818200293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379771591606148005878800195 569657387409222008818200293)
      ·
        refine ⟨106810760139229126653412555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 569657387409222008818200293 106810760139229126653412555)
        ·
          refine ⟨160216140208843689980118833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106810760139229126653412555 160216140208843689980118833)
          ·
            refine ⟨120162105156632767485089125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160216140208843689980118833 120162105156632767485089125)
            ·
              refine ⟨22530394716868643903454211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 120162105156632767485089125 22530394716868643903454211)
              ·
                refine ⟨33795592075302965855181317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22530394716868643903454211 33795592075302965855181317)
                ·
                  refine ⟨6336673514119306097846497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33795592075302965855181317 6336673514119306097846497)
                  ·
                    refine ⟨4752505135589479573384873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6336673514119306097846497 4752505135589479573384873)
                    ·
                      refine ⟨3564378851692109680038655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4752505135589479573384873 3564378851692109680038655)
                      ·
                        rfl

theorem cell23_6941603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 1, 4, 2, 2].length) (baseStart_6941603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6941603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6941603 prefixEnd_6941603 := by exact prefixLift 6941603
  have htrace : WordTrace (prefixWord ++ tailWord_6941603) baseStart_6941603 baseEnd_6941603 := by
    simpa [prefixWord, tailWord_6941603, baseEnd_6941603] using wordTrace_append hprefix tailTrace_6941603
  have hstable : (prefixWord ++ tailWord_6941603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6941603).length < 2 ^ (prefixWord ++ tailWord_6941603).sum := by decide
  have hdescent : baseEnd_6941603 < baseStart_6941603 := by decide
  rcases family_descends (prefixWord ++ tailWord_6941603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6941639 : List Nat := [1, 1, 4, 1, 1, 2, 2, 3, 1, 7]
def baseStart_6941639 : Nat := 118140960795 + 6941639 * 2 ^ 59
def prefixEnd_6941639 : Nat := 4983230072969 + 3 ^ 40 * 6941639 * 2
def baseEnd_6941639 : Nat := 1188132445665223846396163

theorem tailTrace_6941639 : CollatzResearch.WordTrace tailWord_6941639 prefixEnd_6941639 1188132445665223846396163 := by
  unfold tailWord_6941639
  simp only [CollatzResearch.WordTrace]
  refine ⟨253182374098634915400843971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168788249399089943600562647 253182374098634915400843971)
  ·
    refine ⟨379773561147952373101265957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253182374098634915400843971 379773561147952373101265957)
    ·
      refine ⟨71207542715241069956487367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 379773561147952373101265957 71207542715241069956487367)
      ·
        refine ⟨106811314072861604934731051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71207542715241069956487367 106811314072861604934731051)
        ·
          refine ⟨160216971109292407402096577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106811314072861604934731051 160216971109292407402096577)
          ·
            refine ⟨120162728331969305551572433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160216971109292407402096577 120162728331969305551572433)
            ·
              refine ⟨90122046248976979163679325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120162728331969305551572433 90122046248976979163679325)
              ·
                refine ⟨33795767343366367186379747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90122046248976979163679325 33795767343366367186379747)
                ·
                  refine ⟨50693651015049550779569621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33795767343366367186379747 50693651015049550779569621)
                  ·
                    refine ⟨1188132445665223846396163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50693651015049550779569621 1188132445665223846396163)
                    ·
                      rfl

theorem cell23_6941639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 3, 1, 7].length) (baseStart_6941639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6941639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6941639 prefixEnd_6941639 := by exact prefixLift 6941639
  have htrace : WordTrace (prefixWord ++ tailWord_6941639) baseStart_6941639 baseEnd_6941639 := by
    simpa [prefixWord, tailWord_6941639, baseEnd_6941639] using wordTrace_append hprefix tailTrace_6941639
  have hstable : (prefixWord ++ tailWord_6941639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6941639).length < 2 ^ (prefixWord ++ tailWord_6941639).sum := by decide
  have hdescent : baseEnd_6941639 < baseStart_6941639 := by decide
  rcases family_descends (prefixWord ++ tailWord_6941639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6941649 : List Nat := [1, 2, 2, 1, 2, 1, 3, 1, 3, 2, 5]
def baseStart_6941649 : Nat := 118140960795 + 6941649 * 2 ^ 59
def prefixEnd_6941649 : Nat := 4983230072969 + 3 ^ 40 * 6941649 * 2
def baseEnd_6941649 : Nat := 3564402471802216500063443

theorem tailTrace_6941649 : CollatzResearch.WordTrace tailWord_6941649 prefixEnd_6941649 3564402471802216500063443 := by
  unfold tailWord_6941649
  simp only [CollatzResearch.WordTrace]
  refine ⟨253182738828598687108708001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168788492552399124739138667 253182738828598687108708001)
  ·
    refine ⟨189887054121449015331531001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253182738828598687108708001 189887054121449015331531001)
    ·
      refine ⟨142415290591086761498648251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189887054121449015331531001 142415290591086761498648251)
      ·
        refine ⟨213622935886630142247972377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142415290591086761498648251 213622935886630142247972377)
        ·
          refine ⟨160217201914972606685979283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213622935886630142247972377 160217201914972606685979283)
          ·
            refine ⟨240325802872458910028968925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160217201914972606685979283 240325802872458910028968925)
            ·
              refine ⟨90122176077172091260863347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 240325802872458910028968925 90122176077172091260863347)
              ·
                refine ⟨135183264115758136891295021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90122176077172091260863347 135183264115758136891295021)
                ·
                  refine ⟨50693724043409301334235633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 135183264115758136891295021 50693724043409301334235633)
                  ·
                    refine ⟨38020293032556976000676725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50693724043409301334235633 38020293032556976000676725)
                    ·
                      refine ⟨3564402471802216500063443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38020293032556976000676725 3564402471802216500063443)
                      ·
                        rfl

theorem cell23_6941649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 3, 2, 5].length) (baseStart_6941649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6941649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6941649 prefixEnd_6941649 := by exact prefixLift 6941649
  have htrace : WordTrace (prefixWord ++ tailWord_6941649) baseStart_6941649 baseEnd_6941649 := by
    simpa [prefixWord, tailWord_6941649, baseEnd_6941649] using wordTrace_append hprefix tailTrace_6941649
  have hstable : (prefixWord ++ tailWord_6941649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6941649).length < 2 ^ (prefixWord ++ tailWord_6941649).sum := by decide
  have hdescent : baseEnd_6941649 < baseStart_6941649 := by decide
  rcases family_descends (prefixWord ++ tailWord_6941649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6941654 : List Nat := [5, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2]
def baseStart_6941654 : Nat := 118140960795 + 6941654 * 2 ^ 59
def prefixEnd_6941654 : Nat := 4983230072969 + 3 ^ 40 * 6941654 * 2
def baseEnd_6941654 : Nat := 3564405039205488980500921

theorem tailTrace_6941654 : CollatzResearch.WordTrace tailWord_6941654 prefixEnd_6941654 3564405039205488980500921 := by
  unfold tailWord_6941654
  simp only [CollatzResearch.WordTrace]
  refine ⟨15823932574598785810165001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 168788614129053715308426677 15823932574598785810165001)
  ·
    refine ⟨11867949430949089357623751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15823932574598785810165001 11867949430949089357623751)
    ·
      refine ⟨17801924146423634036435627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11867949430949089357623751 17801924146423634036435627)
      ·
        refine ⟨26702886219635451054653441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17801924146423634036435627 26702886219635451054653441)
        ·
          refine ⟨20027164664726588290990081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26702886219635451054653441 20027164664726588290990081)
          ·
            refine ⟨15020373498544941218242561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20027164664726588290990081 15020373498544941218242561)
            ·
              refine ⟨11265280123908705913681921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15020373498544941218242561 11265280123908705913681921)
              ·
                refine ⟨8448960092931529435261441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11265280123908705913681921 8448960092931529435261441)
                ·
                  refine ⟨6336720069698647076446081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8448960092931529435261441 6336720069698647076446081)
                  ·
                    refine ⟨4752540052273985307334561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6336720069698647076446081 4752540052273985307334561)
                    ·
                      refine ⟨3564405039205488980500921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4752540052273985307334561 3564405039205488980500921)
                      ·
                        rfl

theorem cell23_6941654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2].length) (baseStart_6941654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6941654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6941654 prefixEnd_6941654 := by exact prefixLift 6941654
  have htrace : WordTrace (prefixWord ++ tailWord_6941654) baseStart_6941654 baseEnd_6941654 := by
    simpa [prefixWord, tailWord_6941654, baseEnd_6941654] using wordTrace_append hprefix tailTrace_6941654
  have hstable : (prefixWord ++ tailWord_6941654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6941654).length < 2 ^ (prefixWord ++ tailWord_6941654).sum := by decide
  have hdescent : baseEnd_6941654 < baseStart_6941654 := by decide
  rcases family_descends (prefixWord ++ tailWord_6941654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6941656 : List Nat := [2, 1, 2, 2, 2, 3, 2, 2, 2, 5]
def baseStart_6941656 : Nat := 118140960795 + 6941656 * 2 ^ 59
def prefixEnd_6941656 : Nat := 4983230072969 + 3 ^ 40 * 6941656 * 2
def baseEnd_6941656 : Nat := 1188135355388932657558637

theorem tailTrace_6941656 : CollatzResearch.WordTrace tailWord_6941656 prefixEnd_6941656 1188135355388932657558637 := by
  unfold tailWord_6941656
  simp only [CollatzResearch.WordTrace]
  refine ⟨126591497069786663652106411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168788662759715551536141881 126591497069786663652106411)
  ·
    refine ⟨189887245604679995478159617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126591497069786663652106411 189887245604679995478159617)
    ·
      refine ⟨142415434203509996608619713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189887245604679995478159617 142415434203509996608619713)
      ·
        refine ⟨106811575652632497456464785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142415434203509996608619713 106811575652632497456464785)
        ·
          refine ⟨80108681739474373092348589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106811575652632497456464785 80108681739474373092348589)
          ·
            refine ⟨30040755652302889909630721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80108681739474373092348589 30040755652302889909630721)
            ·
              refine ⟨22530566739227167432223041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30040755652302889909630721 22530566739227167432223041)
              ·
                refine ⟨16897925054420375574167281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22530566739227167432223041 16897925054420375574167281)
                ·
                  refine ⟨12673443790815281680625461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16897925054420375574167281 12673443790815281680625461)
                  ·
                    refine ⟨1188135355388932657558637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12673443790815281680625461 1188135355388932657558637)
                    ·
                      rfl

theorem cell23_6941656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 2, 2, 5].length) (baseStart_6941656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6941656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6941656 prefixEnd_6941656 := by exact prefixLift 6941656
  have htrace : WordTrace (prefixWord ++ tailWord_6941656) baseStart_6941656 baseEnd_6941656 := by
    simpa [prefixWord, tailWord_6941656, baseEnd_6941656] using wordTrace_append hprefix tailTrace_6941656
  have hstable : (prefixWord ++ tailWord_6941656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6941656).length < 2 ^ (prefixWord ++ tailWord_6941656).sum := by decide
  have hdescent : baseEnd_6941656 < baseStart_6941656 := by decide
  rcases family_descends (prefixWord ++ tailWord_6941656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6941706 : List Nat := [3, 1, 2, 2, 3, 1, 1, 1, 2, 1, 6]
def baseStart_6941706 : Nat := 118140960795 + 6941706 * 2 ^ 59
def prefixEnd_6941706 : Nat := 4983230072969 + 3 ^ 40 * 6941706 * 2
def baseEnd_6941706 : Nat := 3564431740199522777050681

theorem tailTrace_6941706 : CollatzResearch.WordTrace tailWord_6941706 prefixEnd_6941706 3564431740199522777050681 := by
  unfold tailWord_6941706
  simp only [CollatzResearch.WordTrace]
  refine ⟨63296204447348046460883243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168789878526261457229021981 63296204447348046460883243)
  ·
    refine ⟨94944306671022069691324865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63296204447348046460883243 94944306671022069691324865)
    ·
      refine ⟨71208230003266552268493649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94944306671022069691324865 71208230003266552268493649)
      ·
        refine ⟨53406172502449914201370237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71208230003266552268493649 53406172502449914201370237)
        ·
          refine ⟨20027314688418717825513839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53406172502449914201370237 20027314688418717825513839)
          ·
            refine ⟨30040972032628076738270759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20027314688418717825513839 30040972032628076738270759)
            ·
              refine ⟨45061458048942115107406139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30040972032628076738270759 45061458048942115107406139)
              ·
                refine ⟨67592187073413172661109209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45061458048942115107406139 67592187073413172661109209)
                ·
                  refine ⟨50694140305059879495831907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67592187073413172661109209 50694140305059879495831907)
                  ·
                    refine ⟨76041210457589819243747861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50694140305059879495831907 76041210457589819243747861)
                    ·
                      refine ⟨3564431740199522777050681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76041210457589819243747861 3564431740199522777050681)
                      ·
                        rfl

theorem cell23_6941706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 1, 2, 1, 6].length) (baseStart_6941706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6941706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6941706 prefixEnd_6941706 := by exact prefixLift 6941706
  have htrace : WordTrace (prefixWord ++ tailWord_6941706) baseStart_6941706 baseEnd_6941706 := by
    simpa [prefixWord, tailWord_6941706, baseEnd_6941706] using wordTrace_append hprefix tailTrace_6941706
  have hstable : (prefixWord ++ tailWord_6941706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6941706).length < 2 ^ (prefixWord ++ tailWord_6941706).sum := by decide
  have hdescent : baseEnd_6941706 < baseStart_6941706 := by decide
  rcases family_descends (prefixWord ++ tailWord_6941706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6941720 : List Nat := [2, 1, 2, 3, 2, 2, 2, 4, 1, 4]
def baseStart_6941720 : Nat := 118140960795 + 6941720 * 2 ^ 59
def prefixEnd_6941720 : Nat := 4983230072969 + 3 ^ 40 * 6941720 * 2
def baseEnd_6941720 : Nat := 1188146309642895240758539

theorem tailTrace_6941720 : CollatzResearch.WordTrace tailWord_6941720 prefixEnd_6941720 1188146309642895240758539 := by
  unfold tailWord_6941720
  simp only [CollatzResearch.WordTrace]
  refine ⟨126592664205670733117271307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168790218940894310823028409 126592664205670733117271307)
  ·
    refine ⟨189888996308506099675906961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126592664205670733117271307 189888996308506099675906961)
    ·
      refine ⟨142416747231379574756930221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189888996308506099675906961 142416747231379574756930221)
      ·
        refine ⟨53406280211767340533848833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142416747231379574756930221 53406280211767340533848833)
        ·
          refine ⟨40054710158825505400386625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53406280211767340533848833 40054710158825505400386625)
          ·
            refine ⟨30041032619119129050289969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40054710158825505400386625 30041032619119129050289969)
            ·
              refine ⟨22530774464339346787717477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30041032619119129050289969 22530774464339346787717477)
              ·
                refine ⟨4224520212063627522697027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22530774464339346787717477 4224520212063627522697027)
                ·
                  refine ⟨6336780318095441284045541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4224520212063627522697027 6336780318095441284045541)
                  ·
                    refine ⟨1188146309642895240758539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6336780318095441284045541 1188146309642895240758539)
                    ·
                      rfl

theorem cell23_6941720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 4, 1, 4].length) (baseStart_6941720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6941720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6941720 prefixEnd_6941720 := by exact prefixLift 6941720
  have htrace : WordTrace (prefixWord ++ tailWord_6941720) baseStart_6941720 baseEnd_6941720 := by
    simpa [prefixWord, tailWord_6941720, baseEnd_6941720] using wordTrace_append hprefix tailTrace_6941720
  have hstable : (prefixWord ++ tailWord_6941720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6941720).length < 2 ^ (prefixWord ++ tailWord_6941720).sum := by decide
  have hdescent : baseEnd_6941720 < baseStart_6941720 := by decide
  rcases family_descends (prefixWord ++ tailWord_6941720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6941733 : List Nat := [1, 3, 1, 2, 2, 2, 5, 1, 6]
def baseStart_6941733 : Nat := 118140960795 + 6941733 * 2 ^ 59
def prefixEnd_6941733 : Nat := 4983230072969 + 3 ^ 40 * 6941733 * 2
def baseEnd_6941733 : Nat := 396049511575243796823673

theorem tailTrace_6941733 : CollatzResearch.WordTrace tailWord_6941733 prefixEnd_6941733 396049511575243796823673 := by
  unfold tailWord_6941733
  simp only [CollatzResearch.WordTrace]
  refine ⟨253185802560294369454765853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168790535040196246303177235 253185802560294369454765853)
  ·
    refine ⟨94944675960110388545537195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 253185802560294369454765853 94944675960110388545537195)
    ·
      refine ⟨142417013940165582818305793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94944675960110388545537195 142417013940165582818305793)
      ·
        refine ⟨106812760455124187113729345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142417013940165582818305793 106812760455124187113729345)
        ·
          refine ⟨80109570341343140335297009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106812760455124187113729345 80109570341343140335297009)
          ·
            refine ⟨60082177756007355251472757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80109570341343140335297009 60082177756007355251472757)
            ·
              refine ⟨5632704164625689554825571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60082177756007355251472757 5632704164625689554825571)
              ·
                refine ⟨8449056246938534332238357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5632704164625689554825571 8449056246938534332238357)
                ·
                  refine ⟨396049511575243796823673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8449056246938534332238357 396049511575243796823673)
                  ·
                    rfl

theorem cell23_6941733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 5, 1, 6].length) (baseStart_6941733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6941733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6941733 prefixEnd_6941733 := by exact prefixLift 6941733
  have htrace : WordTrace (prefixWord ++ tailWord_6941733) baseStart_6941733 baseEnd_6941733 := by
    simpa [prefixWord, tailWord_6941733, baseEnd_6941733] using wordTrace_append hprefix tailTrace_6941733
  have hstable : (prefixWord ++ tailWord_6941733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6941733).length < 2 ^ (prefixWord ++ tailWord_6941733).sum := by decide
  have hdescent : baseEnd_6941733 < baseStart_6941733 := by decide
  rcases family_descends (prefixWord ++ tailWord_6941733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6941786 : List Nat := [3, 1, 1, 2, 1, 1, 2, 3, 3, 1, 5]
def baseStart_6941786 : Nat := 118140960795 + 6941786 * 2 ^ 59
def prefixEnd_6941786 : Nat := 4983230072969 + 3 ^ 40 * 6941786 * 2
def baseEnd_6941786 : Nat := 3564472818651882464050313

theorem tailTrace_6941786 : CollatzResearch.WordTrace tailWord_6941786 prefixEnd_6941786 3564472818651882464050313 := by
  unfold tailWord_6941786
  simp only [CollatzResearch.WordTrace]
  refine ⟨63296933907275589876611303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168791823752734906337630141 63296933907275589876611303)
  ·
    refine ⟨94945400860913384814916955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63296933907275589876611303 94945400860913384814916955)
    ·
      refine ⟨142418101291370077222375433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94945400860913384814916955 142418101291370077222375433)
      ·
        refine ⟨106813575968527557916781575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142418101291370077222375433 106813575968527557916781575)
        ·
          refine ⟨160220363952791336875172363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106813575968527557916781575 160220363952791336875172363)
          ·
            refine ⟨240330545929187005312758545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160220363952791336875172363 240330545929187005312758545)
            ·
              refine ⟨180247909446890253984568909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 240330545929187005312758545 180247909446890253984568909)
              ·
                refine ⟨67592966042583845244213341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 180247909446890253984568909 67592966042583845244213341)
                ·
                  refine ⟨25347362265968941966580003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67592966042583845244213341 25347362265968941966580003)
                  ·
                    refine ⟨38021043398953412949870005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25347362265968941966580003 38021043398953412949870005)
                    ·
                      refine ⟨3564472818651882464050313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38021043398953412949870005 3564472818651882464050313)
                      ·
                        rfl

theorem cell23_6941786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 3, 3, 1, 5].length) (baseStart_6941786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6941786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6941786 prefixEnd_6941786 := by exact prefixLift 6941786
  have htrace : WordTrace (prefixWord ++ tailWord_6941786) baseStart_6941786 baseEnd_6941786 := by
    simpa [prefixWord, tailWord_6941786, baseEnd_6941786] using wordTrace_append hprefix tailTrace_6941786
  have hstable : (prefixWord ++ tailWord_6941786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6941786).length < 2 ^ (prefixWord ++ tailWord_6941786).sum := by decide
  have hdescent : baseEnd_6941786 < baseStart_6941786 := by decide
  rcases family_descends (prefixWord ++ tailWord_6941786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6941817 : List Nat := [1, 2, 1, 3, 5, 1, 3, 1, 1, 1, 4]
def baseStart_6941817 : Nat := 118140960795 + 6941817 * 2 ^ 59
def prefixEnd_6941817 : Nat := 4983230072969 + 3 ^ 40 * 6941817 * 2
def baseEnd_6941817 : Nat := 3564488736552171842762671

theorem tailTrace_6941817 : CollatzResearch.WordTrace tailWord_6941817 prefixEnd_6941817 3564488736552171842762671 := by
  unfold tailWord_6941817
  simp only [CollatzResearch.WordTrace]
  refine ⟨253188866291990051800823705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168792577527993367867215803 253188866291990051800823705)
  ·
    refine ⟨189891649718992538850617779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253188866291990051800823705 189891649718992538850617779)
    ·
      refine ⟨284837474578488808275926669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189891649718992538850617779 284837474578488808275926669)
      ·
        refine ⟨106814052966933303103472501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 284837474578488808275926669 106814052966933303103472501)
        ·
          refine ⟨10013817465649997165950547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 106814052966933303103472501 10013817465649997165950547)
          ·
            refine ⟨15020726198474995748925821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10013817465649997165950547 15020726198474995748925821)
            ·
              refine ⟨5632772324428123405847183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15020726198474995748925821 5632772324428123405847183)
              ·
                refine ⟨8449158486642185108770775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5632772324428123405847183 8449158486642185108770775)
                ·
                  refine ⟨12673737729963277663156163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8449158486642185108770775 12673737729963277663156163)
                  ·
                    refine ⟨19010606594944916494734245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12673737729963277663156163 19010606594944916494734245)
                    ·
                      refine ⟨3564488736552171842762671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19010606594944916494734245 3564488736552171842762671)
                      ·
                        rfl

theorem cell23_6941817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 3, 1, 1, 1, 4].length) (baseStart_6941817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6941817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6941817 prefixEnd_6941817 := by exact prefixLift 6941817
  have htrace : WordTrace (prefixWord ++ tailWord_6941817) baseStart_6941817 baseEnd_6941817 := by
    simpa [prefixWord, tailWord_6941817, baseEnd_6941817] using wordTrace_append hprefix tailTrace_6941817
  have hstable : (prefixWord ++ tailWord_6941817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6941817).length < 2 ^ (prefixWord ++ tailWord_6941817).sum := by decide
  have hdescent : baseEnd_6941817 < baseStart_6941817 := by decide
  rcases family_descends (prefixWord ++ tailWord_6941817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6941834 : List Nat := [3, 1, 2, 3, 1, 1, 3, 4, 1, 2, 2]
def baseStart_6941834 : Nat := 118140960795 + 6941834 * 2 ^ 59
def prefixEnd_6941834 : Nat := 4983230072969 + 3 ^ 40 * 6941834 * 2
def baseEnd_6941834 : Nat := 3564497465723298276250093

theorem tailTrace_6941834 : CollatzResearch.WordTrace tailWord_6941834 prefixEnd_6941834 3564497465723298276250093 := by
  unfold tailWord_6941834
  simp only [CollatzResearch.WordTrace]
  refine ⟨63297371583232115926048139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168792990888618975802795037 63297371583232115926048139)
  ·
    refine ⟨94946057374848173889072209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63297371583232115926048139 94946057374848173889072209)
    ·
      refine ⟨71209543031136130416804157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94946057374848173889072209 71209543031136130416804157)
      ·
        refine ⟨26703578636676048906301559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71209543031136130416804157 26703578636676048906301559)
        ·
          refine ⟨40055367955014073359452339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26703578636676048906301559 40055367955014073359452339)
          ·
            refine ⟨60083051932521110039178509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40055367955014073359452339 60083051932521110039178509)
            ·
              refine ⟨22531144474695416264691941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60083051932521110039178509 22531144474695416264691941)
              ·
                refine ⟨4224589589005390549629739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22531144474695416264691941 4224589589005390549629739)
                ·
                  refine ⟨6336884383508085824444609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4224589589005390549629739 6336884383508085824444609)
                  ·
                    refine ⟨4752663287631064368333457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6336884383508085824444609 4752663287631064368333457)
                    ·
                      refine ⟨3564497465723298276250093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4752663287631064368333457 3564497465723298276250093)
                      ·
                        rfl

theorem cell23_6941834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 4, 1, 2, 2].length) (baseStart_6941834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6941834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6941834 prefixEnd_6941834 := by exact prefixLift 6941834
  have htrace : WordTrace (prefixWord ++ tailWord_6941834) baseStart_6941834 baseEnd_6941834 := by
    simpa [prefixWord, tailWord_6941834, baseEnd_6941834] using wordTrace_append hprefix tailTrace_6941834
  have hstable : (prefixWord ++ tailWord_6941834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6941834).length < 2 ^ (prefixWord ++ tailWord_6941834).sum := by decide
  have hdescent : baseEnd_6941834 < baseStart_6941834 := by decide
  rcases family_descends (prefixWord ++ tailWord_6941834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6941850 : List Nat := [3, 1, 1, 5, 1, 1, 1, 3, 1, 3, 3]
def baseStart_6941850 : Nat := 118140960795 + 6941850 * 2 ^ 59
def prefixEnd_6941850 : Nat := 4983230072969 + 3 ^ 40 * 6941850 * 2
def baseEnd_6941850 : Nat := 3564505681413770213650019

theorem tailTrace_6941850 : CollatzResearch.WordTrace tailWord_6941850 prefixEnd_6941850 3564505681413770213650019 := by
  unfold tailWord_6941850
  simp only [CollatzResearch.WordTrace]
  refine ⟨63297517475217624609193751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168793379933913665624516669 63297517475217624609193751)
  ·
    refine ⟨94946276212826436913790627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63297517475217624609193751 94946276212826436913790627)
    ·
      refine ⟨142419414319239655370685941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94946276212826436913790627 142419414319239655370685941)
      ·
        refine ⟨13351820092428717691001807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 142419414319239655370685941 13351820092428717691001807)
        ·
          refine ⟨20027730138643076536502711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13351820092428717691001807 20027730138643076536502711)
          ·
            refine ⟨30041595207964614804754067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20027730138643076536502711 30041595207964614804754067)
            ·
              refine ⟨45062392811946922207131101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30041595207964614804754067 45062392811946922207131101)
              ·
                refine ⟨16898397304480095827674163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45062392811946922207131101 16898397304480095827674163)
                ·
                  refine ⟨25347595956720143741511245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16898397304480095827674163 25347595956720143741511245)
                  ·
                    refine ⟨9505348483770053903066717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25347595956720143741511245 9505348483770053903066717)
                    ·
                      refine ⟨3564505681413770213650019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9505348483770053903066717 3564505681413770213650019)
                      ·
                        rfl

theorem cell23_6941850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_6941850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6941850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6941850 prefixEnd_6941850 := by exact prefixLift 6941850
  have htrace : WordTrace (prefixWord ++ tailWord_6941850) baseStart_6941850 baseEnd_6941850 := by
    simpa [prefixWord, tailWord_6941850, baseEnd_6941850] using wordTrace_append hprefix tailTrace_6941850
  have hstable : (prefixWord ++ tailWord_6941850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6941850).length < 2 ^ (prefixWord ++ tailWord_6941850).sum := by decide
  have hdescent : baseEnd_6941850 < baseStart_6941850 := by decide
  rcases family_descends (prefixWord ++ tailWord_6941850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6941878 : List Nat := [5, 1, 3, 2, 2, 1, 1, 2, 2, 4]
def baseStart_6941878 : Nat := 118140960795 + 6941878 * 2 ^ 59
def prefixEnd_6941878 : Nat := 4983230072969 + 3 ^ 40 * 6941878 * 2
def baseEnd_6941878 : Nat := 1188173352957365368033297

theorem tailTrace_6941878 : CollatzResearch.WordTrace tailWord_6941878 prefixEnd_6941878 1188173352957365368033297 := by
  unfold tailWord_6941878
  simp only [CollatzResearch.WordTrace]
  refine ⟨15824443196548066201174643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 168794060763179372812529525 15824443196548066201174643)
  ·
    refine ⟨23736664794822099301761965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15824443196548066201174643 23736664794822099301761965)
    ·
      refine ⟨8901249298058287238160737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23736664794822099301761965 8901249298058287238160737)
      ·
        refine ⟨6675936973543715428620553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8901249298058287238160737 6675936973543715428620553)
        ·
          refine ⟨5006952730157786571465415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6675936973543715428620553 5006952730157786571465415)
          ·
            refine ⟨7510429095236679857198123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5006952730157786571465415 7510429095236679857198123)
            ·
              refine ⟨11265643642855019785797185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7510429095236679857198123 11265643642855019785797185)
              ·
                refine ⟨8449232732141264839347889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11265643642855019785797185 8449232732141264839347889)
                ·
                  refine ⟨6336924549105948629510917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8449232732141264839347889 6336924549105948629510917)
                  ·
                    refine ⟨1188173352957365368033297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6336924549105948629510917 1188173352957365368033297)
                    ·
                      rfl

theorem cell23_6941878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_6941878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6941878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6941878 prefixEnd_6941878 := by exact prefixLift 6941878
  have htrace : WordTrace (prefixWord ++ tailWord_6941878) baseStart_6941878 baseEnd_6941878 := by
    simpa [prefixWord, tailWord_6941878, baseEnd_6941878] using wordTrace_append hprefix tailTrace_6941878
  have hstable : (prefixWord ++ tailWord_6941878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6941878).length < 2 ^ (prefixWord ++ tailWord_6941878).sum := by decide
  have hdescent : baseEnd_6941878 < baseStart_6941878 := by decide
  rcases family_descends (prefixWord ++ tailWord_6941878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6941884 : List Nat := [2, 2, 2, 3, 2, 3, 1, 2, 2, 1, 3]
def baseStart_6941884 : Nat := 118140960795 + 6941884 * 2 ^ 59
def prefixEnd_6941884 : Nat := 4983230072969 + 3 ^ 40 * 6941884 * 2
def baseEnd_6941884 : Nat := 3564523139756023080624863

theorem tailTrace_6941884 : CollatzResearch.WordTrace tailWord_6941884 prefixEnd_6941884 3564523139756023080624863 := by
  unfold tailWord_6941884
  simp only [CollatzResearch.WordTrace]
  refine ⟨126595654991373661121756353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168794206655164881495675137 126595654991373661121756353)
  ·
    refine ⟨94946741243530245841317265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126595654991373661121756353 94946741243530245841317265)
    ·
      refine ⟨71210055932647684380987949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94946741243530245841317265 71210055932647684380987949)
      ·
        refine ⟨26703770974742881642870481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71210055932647684380987949 26703770974742881642870481)
        ·
          refine ⟨20027828231057161232152861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26703770974742881642870481 20027828231057161232152861)
          ·
            refine ⟨7510435586646435462057323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20027828231057161232152861 7510435586646435462057323)
            ·
              refine ⟨11265653379969653193085985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7510435586646435462057323 11265653379969653193085985)
              ·
                refine ⟨8449240034977239894814489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11265653379969653193085985 8449240034977239894814489)
                ·
                  refine ⟨6336930026232929921110867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8449240034977239894814489 6336930026232929921110867)
                  ·
                    refine ⟨9505395039349394881666301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6336930026232929921110867 9505395039349394881666301)
                    ·
                      refine ⟨3564523139756023080624863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9505395039349394881666301 3564523139756023080624863)
                      ·
                        rfl

theorem cell23_6941884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 1, 2, 2, 1, 3].length) (baseStart_6941884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6941884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6941884 prefixEnd_6941884 := by exact prefixLift 6941884
  have htrace : WordTrace (prefixWord ++ tailWord_6941884) baseStart_6941884 baseEnd_6941884 := by
    simpa [prefixWord, tailWord_6941884, baseEnd_6941884] using wordTrace_append hprefix tailTrace_6941884
  have hstable : (prefixWord ++ tailWord_6941884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6941884).length < 2 ^ (prefixWord ++ tailWord_6941884).sum := by decide
  have hdescent : baseEnd_6941884 < baseStart_6941884 := by decide
  rcases family_descends (prefixWord ++ tailWord_6941884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6941901 : List Nat := [1, 6, 2, 2, 1, 2, 1, 1, 1, 3, 3]
def baseStart_6941901 : Nat := 118140960795 + 6941901 * 2 ^ 59
def prefixEnd_6941901 : Nat := 4983230072969 + 3 ^ 40 * 6941901 * 2
def baseEnd_6941901 : Nat := 3564531868927149514112285

theorem tailTrace_6941901 : CollatzResearch.WordTrace tailWord_6941901 prefixEnd_6941901 3564531868927149514112285 := by
  unfold tailWord_6941901
  simp only [CollatzResearch.WordTrace]
  refine ⟨253191930023685734146881557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168794620015790489431254371 253191930023685734146881557)
  ·
    refine ⟨11868371719860268788135073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 253191930023685734146881557 11868371719860268788135073)
    ·
      refine ⟨8901278789895201591101305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11868371719860268788135073 8901278789895201591101305)
      ·
        refine ⟨6675959092421401193325979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8901278789895201591101305 6675959092421401193325979)
        ·
          refine ⟨10013938638632101789988969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6675959092421401193325979 10013938638632101789988969)
          ·
            refine ⟨7510453978974076342491727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10013938638632101789988969 7510453978974076342491727)
            ·
              refine ⟨11265680968461114513737591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7510453978974076342491727 11265680968461114513737591)
              ·
                refine ⟨16898521452691671770606387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11265680968461114513737591 16898521452691671770606387)
                ·
                  refine ⟨25347782179037507655909581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16898521452691671770606387 25347782179037507655909581)
                  ·
                    refine ⟨9505418317139065370966093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25347782179037507655909581 9505418317139065370966093)
                    ·
                      refine ⟨3564531868927149514112285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9505418317139065370966093 3564531868927149514112285)
                      ·
                        rfl

theorem cell23_6941901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_6941901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6941901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6941901 prefixEnd_6941901 := by exact prefixLift 6941901
  have htrace : WordTrace (prefixWord ++ tailWord_6941901) baseStart_6941901 baseEnd_6941901 := by
    simpa [prefixWord, tailWord_6941901, baseEnd_6941901] using wordTrace_append hprefix tailTrace_6941901
  have hstable : (prefixWord ++ tailWord_6941901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6941901).length < 2 ^ (prefixWord ++ tailWord_6941901).sum := by decide
  have hdescent : baseEnd_6941901 < baseStart_6941901 := by decide
  rcases family_descends (prefixWord ++ tailWord_6941901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6941943 : List Nat := [1, 1, 3, 1, 1, 1, 2, 6, 2, 5]
def baseStart_6941943 : Nat := 118140960795 + 6941943 * 2 ^ 59
def prefixEnd_6941943 : Nat := 4983230072969 + 3 ^ 40 * 6941943 * 2
def baseEnd_6941943 : Nat := 1188184478371546116595697

theorem tailTrace_6941943 : CollatzResearch.WordTrace tailWord_6941943 prefixEnd_6941943 1188184478371546116595697 := by
  unfold tailWord_6941943
  simp only [CollatzResearch.WordTrace]
  refine ⟨253193461889533575319910483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168795641259689050213273655 253193461889533575319910483)
  ·
    refine ⟨379790192834300362979865725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253193461889533575319910483 379790192834300362979865725)
    ·
      refine ⟨142421322312862636117449647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 379790192834300362979865725 142421322312862636117449647)
      ·
        refine ⟨213631983469293954176174471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142421322312862636117449647 213631983469293954176174471)
        ·
          refine ⟨320447975203940931264261707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213631983469293954176174471 320447975203940931264261707)
          ·
            refine ⟨480671962805911396896392561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 320447975203940931264261707 480671962805911396896392561)
            ·
              refine ⟨360503972104433547672294421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 480671962805911396896392561 360503972104433547672294421)
              ·
                refine ⟨16898623692395322547138801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 360503972104433547672294421 16898623692395322547138801)
                ·
                  refine ⟨12673967769296491910354101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16898623692395322547138801 12673967769296491910354101)
                  ·
                    refine ⟨1188184478371546116595697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12673967769296491910354101 1188184478371546116595697)
                    ·
                      rfl

theorem cell23_6941943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 6, 2, 5].length) (baseStart_6941943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6941943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6941943 prefixEnd_6941943 := by exact prefixLift 6941943
  have htrace : WordTrace (prefixWord ++ tailWord_6941943) baseStart_6941943 baseEnd_6941943 := by
    simpa [prefixWord, tailWord_6941943, baseEnd_6941943] using wordTrace_append hprefix tailTrace_6941943
  have hstable : (prefixWord ++ tailWord_6941943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6941943).length < 2 ^ (prefixWord ++ tailWord_6941943).sum := by decide
  have hdescent : baseEnd_6941943 < baseStart_6941943 := by decide
  rcases family_descends (prefixWord ++ tailWord_6941943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6941953 : List Nat := [1, 2, 4, 1, 1, 3, 1, 1, 1, 1, 7]
def baseStart_6941953 : Nat := 118140960795 + 6941953 * 2 ^ 59
def prefixEnd_6941953 : Nat := 4983230072969 + 3 ^ 40 * 6941953 * 2
def baseEnd_6941953 : Nat := 3564558569921183310662045

theorem tailTrace_6941953 : CollatzResearch.WordTrace tailWord_6941953 prefixEnd_6941953 3564558569921183310662045 := by
  unfold tailWord_6941953
  simp only [CollatzResearch.WordTrace]
  refine ⟨253193826619497347027774513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168795884412998231351849675 253193826619497347027774513)
  ·
    refine ⟨189895369964623010270830885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253193826619497347027774513 189895369964623010270830885)
    ·
      refine ⟨35605381868366814425780791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 189895369964623010270830885 35605381868366814425780791)
      ·
        refine ⟨53408072802550221638671187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35605381868366814425780791 53408072802550221638671187)
        ·
          refine ⟨80112109203825332458006781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53408072802550221638671187 80112109203825332458006781)
          ·
            refine ⟨30042040951434499671752543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80112109203825332458006781 30042040951434499671752543)
            ·
              refine ⟨45063061427151749507628815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30042040951434499671752543 45063061427151749507628815)
              ·
                refine ⟨67594592140727624261443223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45063061427151749507628815 67594592140727624261443223)
                ·
                  refine ⟨101391888211091436392164835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67594592140727624261443223 101391888211091436392164835)
                  ·
                    refine ⟨152087832316637154588247253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 101391888211091436392164835 152087832316637154588247253)
                    ·
                      refine ⟨3564558569921183310662045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 152087832316637154588247253 3564558569921183310662045)
                      ·
                        rfl

theorem cell23_6941953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 1, 1, 1, 7].length) (baseStart_6941953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6941953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6941953 prefixEnd_6941953 := by exact prefixLift 6941953
  have htrace : WordTrace (prefixWord ++ tailWord_6941953) baseStart_6941953 baseEnd_6941953 := by
    simpa [prefixWord, tailWord_6941953, baseEnd_6941953] using wordTrace_append hprefix tailTrace_6941953
  have hstable : (prefixWord ++ tailWord_6941953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6941953).length < 2 ^ (prefixWord ++ tailWord_6941953).sum := by decide
  have hdescent : baseEnd_6941953 < baseStart_6941953 := by decide
  rcases family_descends (prefixWord ++ tailWord_6941953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6941980 : List Nat := [2, 2, 3, 1, 1, 1, 3, 3, 2, 1, 4]
def baseStart_6941980 : Nat := 118140960795 + 6941980 * 2 ^ 59
def prefixEnd_6941980 : Nat := 4983230072969 + 3 ^ 40 * 6941980 * 2
def baseEnd_6941980 : Nat := 3564572433898854705024421

theorem tailTrace_6941980 : CollatzResearch.WordTrace tailWord_6941980 prefixEnd_6941980 3564572433898854705024421 := by
  unfold tailWord_6941980
  simp only [CollatzResearch.WordTrace]
  refine ⟨126597405695199765319503697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168796540926933020426004929 126597405695199765319503697)
  ·
    refine ⟨94948054271399823989627773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126597405695199765319503697 94948054271399823989627773)
    ·
      refine ⟨35605520351774933996110415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94948054271399823989627773 35605520351774933996110415)
      ·
        refine ⟨53408280527662400994165623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35605520351774933996110415 53408280527662400994165623)
        ·
          refine ⟨80112420791493601491248435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53408280527662400994165623 80112420791493601491248435)
          ·
            refine ⟨120168631187240402236872653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80112420791493601491248435 120168631187240402236872653)
            ·
              refine ⟨45063236695215150838827245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120168631187240402236872653 45063236695215150838827245)
              ·
                refine ⟨16898713760705681564560217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45063236695215150838827245 16898713760705681564560217)
                ·
                  refine ⟨12674035320529261173420163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16898713760705681564560217 12674035320529261173420163)
                  ·
                    refine ⟨19011052980793891760130245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12674035320529261173420163 19011052980793891760130245)
                    ·
                      refine ⟨3564572433898854705024421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19011052980793891760130245 3564572433898854705024421)
                      ·
                        rfl

theorem cell23_6941980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 3, 2, 1, 4].length) (baseStart_6941980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6941980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6941980 prefixEnd_6941980 := by exact prefixLift 6941980
  have htrace : WordTrace (prefixWord ++ tailWord_6941980) baseStart_6941980 baseEnd_6941980 := by
    simpa [prefixWord, tailWord_6941980, baseEnd_6941980] using wordTrace_append hprefix tailTrace_6941980
  have hstable : (prefixWord ++ tailWord_6941980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6941980).length < 2 ^ (prefixWord ++ tailWord_6941980).sum := by decide
  have hdescent : baseEnd_6941980 < baseStart_6941980 := by decide
  rcases family_descends (prefixWord ++ tailWord_6941980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6942000 : List Nat := [2, 1, 1, 1, 2, 2, 3, 4, 2, 2, 3]
def baseStart_6942000 : Nat := 118140960795 + 6942000 * 2 ^ 59
def prefixEnd_6942000 : Nat := 4983230072969 + 3 ^ 40 * 6942000 * 2
def baseEnd_6942000 : Nat := 3564582703511944626774329

theorem tailTrace_6942000 : CollatzResearch.WordTrace tailWord_6942000 prefixEnd_6942000 3564582703511944626774329 := by
  unfold tailWord_6942000
  simp only [CollatzResearch.WordTrace]
  refine ⟨126597770425163537027367727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168797027233551382703156969 126597770425163537027367727)
  ·
    refine ⟨189896655637745305541051591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126597770425163537027367727 189896655637745305541051591)
    ·
      refine ⟨284844983456617958311577387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189896655637745305541051591 284844983456617958311577387)
      ·
        refine ⟨427267475184926937467366081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284844983456617958311577387 427267475184926937467366081)
        ·
          refine ⟨320450606388695203100524561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 427267475184926937467366081 320450606388695203100524561)
          ·
            refine ⟨240337954791521402325393421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 320450606388695203100524561 240337954791521402325393421)
            ·
              refine ⟨90126733046820525872022533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 240337954791521402325393421 90126733046820525872022533)
              ·
                refine ⟨16898762446278848601004225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90126733046820525872022533 16898762446278848601004225)
                ·
                  refine ⟨12674071834709136450753169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16898762446278848601004225 12674071834709136450753169)
                  ·
                    refine ⟨9505553876031852338064877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12674071834709136450753169 9505553876031852338064877)
                    ·
                      refine ⟨3564582703511944626774329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9505553876031852338064877 3564582703511944626774329)
                      ·
                        rfl

theorem cell23_6942000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 4, 2, 2, 3].length) (baseStart_6942000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6942000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6942000 prefixEnd_6942000 := by exact prefixLift 6942000
  have htrace : WordTrace (prefixWord ++ tailWord_6942000) baseStart_6942000 baseEnd_6942000 := by
    simpa [prefixWord, tailWord_6942000, baseEnd_6942000] using wordTrace_append hprefix tailTrace_6942000
  have hstable : (prefixWord ++ tailWord_6942000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6942000).length < 2 ^ (prefixWord ++ tailWord_6942000).sum := by decide
  have hdescent : baseEnd_6942000 < baseStart_6942000 := by decide
  rcases family_descends (prefixWord ++ tailWord_6942000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6942064 : List Nat := [2, 1, 1, 1, 4, 2, 1, 6, 1, 1, 3]
def baseStart_6942064 : Nat := 118140960795 + 6942064 * 2 ^ 59
def prefixEnd_6942064 : Nat := 4983230072969 + 3 ^ 40 * 6942064 * 2
def baseEnd_6942064 : Nat := 3564615566273832376374035

theorem tailTrace_6942064 : CollatzResearch.WordTrace tailWord_6942064 prefixEnd_6942064 3564615566273832376374035 := by
  unfold tailWord_6942064
  simp only [CollatzResearch.WordTrace]
  refine ⟨126598937561047606492532623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168798583414730141990043497 126598937561047606492532623)
  ·
    refine ⟨189898406341571409738798935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126598937561047606492532623 189898406341571409738798935)
    ·
      refine ⟨284847609512357114608198403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189898406341571409738798935 284847609512357114608198403)
      ·
        refine ⟨427271414268535671912297605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284847609512357114608198403 427271414268535671912297605)
        ·
          refine ⟨80113390175350438483555801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 427271414268535671912297605 80113390175350438483555801)
          ·
            refine ⟨60085042631512828862666851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80113390175350438483555801 60085042631512828862666851)
            ·
              refine ⟨90127563947269243294000277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60085042631512828862666851 90127563947269243294000277)
              ·
                refine ⟨4224729560028245779406263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 90127563947269243294000277 4224729560028245779406263)
                ·
                  refine ⟨6337094340042368669109395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4224729560028245779406263 6337094340042368669109395)
                  ·
                    refine ⟨9505641510063553003664093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6337094340042368669109395 9505641510063553003664093)
                    ·
                      refine ⟨3564615566273832376374035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9505641510063553003664093 3564615566273832376374035)
                      ·
                        rfl

theorem cell23_6942064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 6, 1, 1, 3].length) (baseStart_6942064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6942064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6942064 prefixEnd_6942064 := by exact prefixLift 6942064
  have htrace : WordTrace (prefixWord ++ tailWord_6942064) baseStart_6942064 baseEnd_6942064 := by
    simpa [prefixWord, tailWord_6942064, baseEnd_6942064] using wordTrace_append hprefix tailTrace_6942064
  have hstable : (prefixWord ++ tailWord_6942064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6942064).length < 2 ^ (prefixWord ++ tailWord_6942064).sum := by decide
  have hdescent : baseEnd_6942064 < baseStart_6942064 := by decide
  rcases family_descends (prefixWord ++ tailWord_6942064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6942087 : List Nat := [1, 1, 4, 2, 2, 2, 1, 4, 1, 1, 4]
def baseStart_6942087 : Nat := 118140960795 + 6942087 * 2 ^ 59
def prefixEnd_6942087 : Nat := 4983230072969 + 3 ^ 40 * 6942087 * 2
def baseEnd_6942087 : Nat := 3564627376328885786386429

theorem tailTrace_6942087 : CollatzResearch.WordTrace tailWord_6942087 prefixEnd_6942087 3564627376328885786386429 := by
  unfold tailWord_6942087
  simp only [CollatzResearch.WordTrace]
  refine ⟨253198714001011887913152515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168799142667341258608768343 253198714001011887913152515)
  ·
    refine ⟨379798071001517831869728773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253198714001011887913152515 379798071001517831869728773)
    ·
      refine ⟨71212138312784593475574145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 379798071001517831869728773 71212138312784593475574145)
      ·
        refine ⟨53409103734588445106680609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71212138312784593475574145 53409103734588445106680609)
        ·
          refine ⟨40056827800941333830010457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53409103734588445106680609 40056827800941333830010457)
          ·
            refine ⟨30042620850706000372507843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40056827800941333830010457 30042620850706000372507843)
            ·
              refine ⟨45063931276059000558761765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30042620850706000372507843 45063931276059000558761765)
              ·
                refine ⟨8449487114261062604767831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45063931276059000558761765 8449487114261062604767831)
                ·
                  refine ⟨12674230671391593907151747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8449487114261062604767831 12674230671391593907151747)
                  ·
                    refine ⟨19011346007087390860727621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12674230671391593907151747 19011346007087390860727621)
                    ·
                      refine ⟨3564627376328885786386429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19011346007087390860727621 3564627376328885786386429)
                      ·
                        rfl

theorem cell23_6942087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 4, 1, 1, 4].length) (baseStart_6942087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6942087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6942087 prefixEnd_6942087 := by exact prefixLift 6942087
  have htrace : WordTrace (prefixWord ++ tailWord_6942087) baseStart_6942087 baseEnd_6942087 := by
    simpa [prefixWord, tailWord_6942087, baseEnd_6942087] using wordTrace_append hprefix tailTrace_6942087
  have hstable : (prefixWord ++ tailWord_6942087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6942087).length < 2 ^ (prefixWord ++ tailWord_6942087).sum := by decide
  have hdescent : baseEnd_6942087 < baseStart_6942087 := by decide
  rcases family_descends (prefixWord ++ tailWord_6942087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6942180 : List Nat := [2, 3, 1, 1, 1, 1, 1, 4, 1, 3, 5]
def baseStart_6942180 : Nat := 118140960795 + 6942180 * 2 ^ 59
def prefixEnd_6942180 : Nat := 4983230072969 + 3 ^ 40 * 6942180 * 2
def baseEnd_6942180 : Nat := 3564675130029753922523501

theorem tailTrace_6942180 : CollatzResearch.WordTrace tailWord_6942180 prefixEnd_6942180 3564675130029753922523501 := by
  unfold tailWord_6942180
  simp only [CollatzResearch.WordTrace]
  refine ⟨126601052994837482398143997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168801403993116643197525329 126601052994837482398143997)
  ·
    refine ⟨47475394873064055899303999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126601052994837482398143997 47475394873064055899303999)
    ·
      refine ⟨71213092309596083848955999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47475394873064055899303999 71213092309596083848955999)
      ·
        refine ⟨106819638464394125773433999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71213092309596083848955999 106819638464394125773433999)
        ·
          refine ⟨160229457696591188660150999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106819638464394125773433999 160229457696591188660150999)
          ·
            refine ⟨240344186544886782990226499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160229457696591188660150999 240344186544886782990226499)
            ·
              refine ⟨360516279817330174485339749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 240344186544886782990226499 360516279817330174485339749)
              ·
                refine ⟨67596802465749407716001203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 360516279817330174485339749 67596802465749407716001203)
                ·
                  refine ⟨101395203698624111574001805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67596802465749407716001203 101395203698624111574001805)
                  ·
                    refine ⟨38023201386984041840250677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 101395203698624111574001805 38023201386984041840250677)
                    ·
                      refine ⟨3564675130029753922523501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38023201386984041840250677 3564675130029753922523501)
                      ·
                        rfl

theorem cell23_6942180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 4, 1, 3, 5].length) (baseStart_6942180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6942180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6942180 prefixEnd_6942180 := by exact prefixLift 6942180
  have htrace : WordTrace (prefixWord ++ tailWord_6942180) baseStart_6942180 baseEnd_6942180 := by
    simpa [prefixWord, tailWord_6942180, baseEnd_6942180] using wordTrace_append hprefix tailTrace_6942180
  have hstable : (prefixWord ++ tailWord_6942180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6942180).length < 2 ^ (prefixWord ++ tailWord_6942180).sum := by decide
  have hdescent : baseEnd_6942180 < baseStart_6942180 := by decide
  rcases family_descends (prefixWord ++ tailWord_6942180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6942200 : List Nat := [2, 1, 2, 1, 1, 5, 1, 1, 9]
def baseStart_6942200 : Nat := 118140960795 + 6942200 * 2 ^ 59
def prefixEnd_6942200 : Nat := 4983230072969 + 3 ^ 40 * 6942200 * 2
def baseEnd_6942200 : Nat := 396076155515871538252601

theorem tailTrace_6942200 : CollatzResearch.WordTrace tailWord_6942200 prefixEnd_6942200 396076155515871538252601 := by
  unfold tailWord_6942200
  simp only [CollatzResearch.WordTrace]
  refine ⟨126601417724801254106008027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168801890299735005474677369 126601417724801254106008027)
  ·
    refine ⟨189902126587201881159012041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126601417724801254106008027 189902126587201881159012041)
    ·
      refine ⟨142426594940401410869259031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189902126587201881159012041 142426594940401410869259031)
      ·
        refine ⟨213639892410602116303888547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142426594940401410869259031 213639892410602116303888547)
        ·
          refine ⟨320459838615903174455832821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213639892410602116303888547 320459838615903174455832821)
          ·
            refine ⟨30043109870240922605234327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 320459838615903174455832821 30043109870240922605234327)
            ·
              refine ⟨45064664805361383907851491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30043109870240922605234327 45064664805361383907851491)
              ·
                refine ⟨67596997208042075861777237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45064664805361383907851491 67596997208042075861777237)
                ·
                  refine ⟨396076155515871538252601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 67596997208042075861777237 396076155515871538252601)
                  ·
                    rfl

theorem cell23_6942200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 1, 9].length) (baseStart_6942200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6942200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6942200 prefixEnd_6942200 := by exact prefixLift 6942200
  have htrace : WordTrace (prefixWord ++ tailWord_6942200) baseStart_6942200 baseEnd_6942200 := by
    simpa [prefixWord, tailWord_6942200, baseEnd_6942200] using wordTrace_append hprefix tailTrace_6942200
  have hstable : (prefixWord ++ tailWord_6942200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6942200).length < 2 ^ (prefixWord ++ tailWord_6942200).sum := by decide
  have hdescent : baseEnd_6942200 < baseStart_6942200 := by decide
  rcases family_descends (prefixWord ++ tailWord_6942200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6942227 : List Nat := [1, 1, 1, 2, 1, 6, 1, 2, 2, 3, 3]
def baseStart_6942227 : Nat := 118140960795 + 6942227 * 2 ^ 59
def prefixEnd_6942227 : Nat := 4983230072969 + 3 ^ 40 * 6942227 * 2
def baseEnd_6942227 : Nat := 3564699263620515238635785

theorem tailTrace_6942227 : CollatzResearch.WordTrace tailWord_6942227 prefixEnd_6942227 3564699263620515238635785 := by
  unfold tailWord_6942227
  simp only [CollatzResearch.WordTrace]
  refine ⟨253203820220504691823248935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168802546813669794548832623 253203820220504691823248935)
  ·
    refine ⟨379805730330757037734873403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253203820220504691823248935 379805730330757037734873403)
    ·
      refine ⟨569708595496135556602310105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379805730330757037734873403 569708595496135556602310105)
      ·
        refine ⟨427281446622101667451732579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 569708595496135556602310105 427281446622101667451732579)
        ·
          refine ⟨640922169933152501177598869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 427281446622101667451732579 640922169933152501177598869)
          ·
            refine ⟨30043226715616523492699947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 640922169933152501177598869 30043226715616523492699947)
            ·
              refine ⟨45064840073424785239049921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30043226715616523492699947 45064840073424785239049921)
              ·
                refine ⟨33798630055068588929287441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45064840073424785239049921 33798630055068588929287441)
                ·
                  refine ⟨25348972541301441696965581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33798630055068588929287441 25348972541301441696965581)
                  ·
                    refine ⟨9505864702988040636362093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25348972541301441696965581 9505864702988040636362093)
                    ·
                      refine ⟨3564699263620515238635785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9505864702988040636362093 3564699263620515238635785)
                      ·
                        rfl

theorem cell23_6942227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 2, 2, 3, 3].length) (baseStart_6942227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6942227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6942227 prefixEnd_6942227 := by exact prefixLift 6942227
  have htrace : WordTrace (prefixWord ++ tailWord_6942227) baseStart_6942227 baseEnd_6942227 := by
    simpa [prefixWord, tailWord_6942227, baseEnd_6942227] using wordTrace_append hprefix tailTrace_6942227
  have hstable : (prefixWord ++ tailWord_6942227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6942227).length < 2 ^ (prefixWord ++ tailWord_6942227).sum := by decide
  have hdescent : baseEnd_6942227 < baseStart_6942227 := by decide
  rcases family_descends (prefixWord ++ tailWord_6942227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6942268 : List Nat := [2, 2, 2, 2, 5, 1, 1, 3, 5]
def baseStart_6942268 : Nat := 118140960795 + 6942268 * 2 ^ 59
def prefixEnd_6942268 : Nat := 4983230072969 + 3 ^ 40 * 6942268 * 2
def baseEnd_6942268 : Nat := 396080035147483286469233

theorem tailTrace_6942268 : CollatzResearch.WordTrace tailWord_6942268 prefixEnd_6942268 396080035147483286469233 := by
  unfold tailWord_6942268
  simp only [CollatzResearch.WordTrace]
  refine ⟨126602657806678077912745729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168803543742237437216994305 126602657806678077912745729)
  ·
    refine ⟨94951993355008558434559297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126602657806678077912745729 94951993355008558434559297)
    ·
      refine ⟨71213995016256418825919473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94951993355008558434559297 71213995016256418825919473)
      ·
        refine ⟨53410496262192314119439605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71213995016256418825919473 53410496262192314119439605)
        ·
          refine ⟨5007234024580529448697463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 53410496262192314119439605 5007234024580529448697463)
          ·
            refine ⟨7510851036870794173046195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5007234024580529448697463 7510851036870794173046195)
            ·
              refine ⟨11266276555306191259569293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7510851036870794173046195 11266276555306191259569293)
              ·
                refine ⟨4224853708239821722338485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11266276555306191259569293 4224853708239821722338485)
                ·
                  refine ⟨396080035147483286469233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4224853708239821722338485 396080035147483286469233)
                  ·
                    rfl

theorem cell23_6942268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 1, 3, 5].length) (baseStart_6942268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6942268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6942268 prefixEnd_6942268 := by exact prefixLift 6942268
  have htrace : WordTrace (prefixWord ++ tailWord_6942268) baseStart_6942268 baseEnd_6942268 := by
    simpa [prefixWord, tailWord_6942268, baseEnd_6942268] using wordTrace_append hprefix tailTrace_6942268
  have hstable : (prefixWord ++ tailWord_6942268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6942268).length < 2 ^ (prefixWord ++ tailWord_6942268).sum := by decide
  have hdescent : baseEnd_6942268 < baseStart_6942268 := by decide
  rcases family_descends (prefixWord ++ tailWord_6942268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6942284 : List Nat := [2, 2, 1, 3, 1, 4, 1, 2, 2, 1, 4]
def baseStart_6942284 : Nat := 118140960795 + 6942284 * 2 ^ 59
def prefixEnd_6942284 : Nat := 4983230072969 + 3 ^ 40 * 6942284 * 2
def baseEnd_6942284 : Nat := 3564728532017821515623023

theorem tailTrace_6942284 : CollatzResearch.WordTrace tailWord_6942284 prefixEnd_6942284 3564728532017821515623023 := by
  unfold tailWord_6942284
  simp only [CollatzResearch.WordTrace]
  refine ⟨126602949590649095279036953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168803932787532127038715937 126602949590649095279036953)
  ·
    refine ⟨94952212192986821459277715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126602949590649095279036953 94952212192986821459277715)
    ·
      refine ⟨142428318289480232188916573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94952212192986821459277715 142428318289480232188916573)
      ·
        refine ⟨53410619358555087070843715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142428318289480232188916573 53410619358555087070843715)
        ·
          refine ⟨80115929037832630606265573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53410619358555087070843715 80115929037832630606265573)
          ·
            refine ⟨15021736694593618238674795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80115929037832630606265573 15021736694593618238674795)
            ·
              refine ⟨22532605041890427358012193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15021736694593618238674795 22532605041890427358012193)
              ·
                refine ⟨16899453781417820518509145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22532605041890427358012193 16899453781417820518509145)
                ·
                  refine ⟨12674590336063365388881859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16899453781417820518509145 12674590336063365388881859)
                  ·
                    refine ⟨19011885504095048083322789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12674590336063365388881859 19011885504095048083322789)
                    ·
                      refine ⟨3564728532017821515623023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19011885504095048083322789 3564728532017821515623023)
                      ·
                        rfl

theorem cell23_6942284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 2, 2, 1, 4].length) (baseStart_6942284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6942284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6942284 prefixEnd_6942284 := by exact prefixLift 6942284
  have htrace : WordTrace (prefixWord ++ tailWord_6942284) baseStart_6942284 baseEnd_6942284 := by
    simpa [prefixWord, tailWord_6942284, baseEnd_6942284] using wordTrace_append hprefix tailTrace_6942284
  have hstable : (prefixWord ++ tailWord_6942284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6942284).length < 2 ^ (prefixWord ++ tailWord_6942284).sum := by decide
  have hdescent : baseEnd_6942284 < baseStart_6942284 := by decide
  rcases family_descends (prefixWord ++ tailWord_6942284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6942391 : List Nat := [1, 1, 3, 1, 5, 2, 1, 3, 1, 1, 4]
def baseStart_6942391 : Nat := 118140960795 + 6942391 * 2 ^ 59
def prefixEnd_6942391 : Nat := 4983230072969 + 3 ^ 40 * 6942391 * 2
def baseEnd_6942391 : Nat := 3564783474447852596985031

theorem tailTrace_6942391 : CollatzResearch.WordTrace tailWord_6942391 prefixEnd_6942391 3564783474447852596985031 := by
  unfold tailWord_6942391
  simp only [CollatzResearch.WordTrace]
  refine ⟨253209801791910547832219027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168806534527940365221479351 253209801791910547832219027)
  ·
    refine ⟨379814702687865821748328541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253209801791910547832219027 379814702687865821748328541)
    ·
      refine ⟨142430513507949683155623203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 379814702687865821748328541 142430513507949683155623203)
      ·
        refine ⟨213645770261924524733434805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142430513507949683155623203 213645770261924524733434805)
        ·
          refine ⟨20029290962055424193759513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 213645770261924524733434805 20029290962055424193759513)
          ·
            refine ⟨15021968221541568145319635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20029290962055424193759513 15021968221541568145319635)
            ·
              refine ⟨22532952332312352217979453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15021968221541568145319635 22532952332312352217979453)
              ·
                refine ⟨8449857124617132081742295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22532952332312352217979453 8449857124617132081742295)
                ·
                  refine ⟨12674785686925698122613443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8449857124617132081742295 12674785686925698122613443)
                  ·
                    refine ⟨19012178530388547183920165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12674785686925698122613443 19012178530388547183920165)
                    ·
                      refine ⟨3564783474447852596985031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19012178530388547183920165 3564783474447852596985031)
                      ·
                        rfl

theorem cell23_6942391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 3, 1, 1, 4].length) (baseStart_6942391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6942391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6942391 prefixEnd_6942391 := by exact prefixLift 6942391
  have htrace : WordTrace (prefixWord ++ tailWord_6942391) baseStart_6942391 baseEnd_6942391 := by
    simpa [prefixWord, tailWord_6942391, baseEnd_6942391] using wordTrace_append hprefix tailTrace_6942391
  have hstable : (prefixWord ++ tailWord_6942391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6942391).length < 2 ^ (prefixWord ++ tailWord_6942391).sum := by decide
  have hdescent : baseEnd_6942391 < baseStart_6942391 := by decide
  rcases family_descends (prefixWord ++ tailWord_6942391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6942397 : List Nat := [1, 4, 1, 2, 1, 2, 12]
def baseStart_6942397 : Nat := 118140960795 + 6942397 * 2 ^ 59
def prefixEnd_6942397 : Nat := 4983230072969 + 3 ^ 40 * 6942397 * 2
def baseEnd_6942397 : Nat := 44009710559651599672963

theorem tailTrace_6942397 : CollatzResearch.WordTrace tailWord_6942397 prefixEnd_6942397 44009710559651599672963 := by
  unfold tailWord_6942397
  simp only [CollatzResearch.WordTrace]
  refine ⟨253210020629888810856937445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168806680419925873904624963 253210020629888810856937445)
  ·
    refine ⟨47476878868104152035675771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 253210020629888810856937445 47476878868104152035675771)
    ·
      refine ⟨71215318302156228053513657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47476878868104152035675771 71215318302156228053513657)
      ·
        refine ⟨53411488726617171040135243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71215318302156228053513657 53411488726617171040135243)
        ·
          refine ⟨80117233089925756560202865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53411488726617171040135243 80117233089925756560202865)
          ·
            refine ⟨60087924817444317420152149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80117233089925756560202865 60087924817444317420152149)
            ·
              refine ⟨44009710559651599672963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 60087924817444317420152149 44009710559651599672963)
              ·
                rfl

theorem cell23_6942397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 12].length) (baseStart_6942397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6942397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6942397 prefixEnd_6942397 := by exact prefixLift 6942397
  have htrace : WordTrace (prefixWord ++ tailWord_6942397) baseStart_6942397 baseEnd_6942397 := by
    simpa [prefixWord, tailWord_6942397, baseEnd_6942397] using wordTrace_append hprefix tailTrace_6942397
  have hstable : (prefixWord ++ tailWord_6942397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6942397).length < 2 ^ (prefixWord ++ tailWord_6942397).sum := by decide
  have hdescent : baseEnd_6942397 < baseStart_6942397 := by decide
  rcases family_descends (prefixWord ++ tailWord_6942397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6942404 : List Nat := [2, 3, 3, 1, 1, 1, 2, 2, 1, 1, 6]
def baseStart_6942404 : Nat := 118140960795 + 6942404 * 2 ^ 59
def prefixEnd_6942404 : Nat := 4983230072969 + 3 ^ 40 * 6942404 * 2
def baseEnd_6942404 : Nat := 3564790149696361046122471

theorem tailTrace_6942404 : CollatzResearch.WordTrace tailWord_6942404 prefixEnd_6942404 3564790149696361046122471 := by
  unfold tailWord_6942404
  simp only [CollatzResearch.WordTrace]
  refine ⟨126605137970431725526221133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168806850627242300701628177 126605137970431725526221133)
  ·
    refine ⟨47476926738911897072332925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126605137970431725526221133 47476926738911897072332925)
    ·
      refine ⟨17803847527091961402124847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47476926738911897072332925 17803847527091961402124847)
      ·
        refine ⟨26705771290637942103187271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17803847527091961402124847 26705771290637942103187271)
        ·
          refine ⟨40058656935956913154780907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26705771290637942103187271 40058656935956913154780907)
          ·
            refine ⟨60087985403935369732171361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40058656935956913154780907 60087985403935369732171361)
            ·
              refine ⟨45065989052951527299128521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60087985403935369732171361 45065989052951527299128521)
              ·
                refine ⟨33799491789713645474346391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45065989052951527299128521 33799491789713645474346391)
                ·
                  refine ⟨50699237684570468211519587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33799491789713645474346391 50699237684570468211519587)
                  ·
                    refine ⟨76048856526855702317279381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50699237684570468211519587 76048856526855702317279381)
                    ·
                      refine ⟨3564790149696361046122471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76048856526855702317279381 3564790149696361046122471)
                      ·
                        rfl

theorem cell23_6942404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_6942404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6942404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6942404 prefixEnd_6942404 := by exact prefixLift 6942404
  have htrace : WordTrace (prefixWord ++ tailWord_6942404) baseStart_6942404 baseEnd_6942404 := by
    simpa [prefixWord, tailWord_6942404, baseEnd_6942404] using wordTrace_append hprefix tailTrace_6942404
  have hstable : (prefixWord ++ tailWord_6942404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6942404).length < 2 ^ (prefixWord ++ tailWord_6942404).sum := by decide
  have hdescent : baseEnd_6942404 < baseStart_6942404 := by decide
  rcases family_descends (prefixWord ++ tailWord_6942404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6942408 : List Nat := [2, 1, 3, 1, 2, 2, 4, 1, 3, 2, 2]
def baseStart_6942408 : Nat := 118140960795 + 6942408 * 2 ^ 59
def prefixEnd_6942408 : Nat := 4983230072969 + 3 ^ 40 * 6942408 * 2
def baseEnd_6942408 : Nat := 3564792203618979030472453

theorem tailTrace_6942408 : CollatzResearch.WordTrace tailWord_6942408 prefixEnd_6942408 3564792203618979030472453 := by
  unfold tailWord_6942408
  simp only [CollatzResearch.WordTrace]
  refine ⟨126605210916424479867793939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168806947888565973157058585 126605210916424479867793939)
  ·
    refine ⟨189907816374636719801690909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126605210916424479867793939 189907816374636719801690909)
    ·
      refine ⟨71215431140488769925634091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189907816374636719801690909 71215431140488769925634091)
      ·
        refine ⟨106823146710733154888451137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71215431140488769925634091 106823146710733154888451137)
        ·
          refine ⟨80117360033049866166338353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106823146710733154888451137 80117360033049866166338353)
          ·
            refine ⟨60088020024787399624753765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80117360033049866166338353 60088020024787399624753765)
            ·
              refine ⟨11266503754647637429641331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60088020024787399624753765 11266503754647637429641331)
              ·
                refine ⟨16899755631971456144461997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11266503754647637429641331 16899755631971456144461997)
                ·
                  refine ⟨6337408361989296054173249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16899755631971456144461997 6337408361989296054173249)
                  ·
                    refine ⟨4753056271491972040629937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6337408361989296054173249 4753056271491972040629937)
                    ·
                      refine ⟨3564792203618979030472453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4753056271491972040629937 3564792203618979030472453)
                      ·
                        rfl

theorem cell23_6942408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 4, 1, 3, 2, 2].length) (baseStart_6942408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6942408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6942408 prefixEnd_6942408 := by exact prefixLift 6942408
  have htrace : WordTrace (prefixWord ++ tailWord_6942408) baseStart_6942408 baseEnd_6942408 := by
    simpa [prefixWord, tailWord_6942408, baseEnd_6942408] using wordTrace_append hprefix tailTrace_6942408
  have hstable : (prefixWord ++ tailWord_6942408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6942408).length < 2 ^ (prefixWord ++ tailWord_6942408).sum := by decide
  have hdescent : baseEnd_6942408 < baseStart_6942408 := by decide
  rcases family_descends (prefixWord ++ tailWord_6942408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6942481 : List Nat := [1, 2, 2, 1, 1, 3, 1, 5, 1, 4, 2]
def baseStart_6942481 : Nat := 118140960795 + 6942481 * 2 ^ 59
def prefixEnd_6942481 : Nat := 4983230072969 + 3 ^ 40 * 6942481 * 2
def baseEnd_6942481 : Nat := 3564829687706757244859617

theorem tailTrace_6942481 : CollatzResearch.WordTrace tailWord_6942481 prefixEnd_6942481 3564829687706757244859617 := by
  unfold tailWord_6942481
  simp only [CollatzResearch.WordTrace]
  refine ⟨253213084361584493202995297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168808722907722995468663531 253213084361584493202995297)
  ·
    refine ⟨189909813271188369902246473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253213084361584493202995297 189909813271188369902246473)
    ·
      refine ⟨142432359953391277426684855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189909813271188369902246473 142432359953391277426684855)
      ·
        refine ⟨213648539930086916140027283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142432359953391277426684855 213648539930086916140027283)
        ·
          refine ⟨320472809895130374210040925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213648539930086916140027283 320472809895130374210040925)
          ·
            refine ⟨120177303710673890328765347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 320472809895130374210040925 120177303710673890328765347)
            ·
              refine ⟨180265955566010835493148021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120177303710673890328765347 180265955566010835493148021)
              ·
                refine ⟨16899933334313515827482627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 180265955566010835493148021 16899933334313515827482627)
                ·
                  refine ⟨25349900001470273741223941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16899933334313515827482627 25349900001470273741223941)
                  ·
                    refine ⟨4753106250275676326479489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25349900001470273741223941 4753106250275676326479489)
                    ·
                      refine ⟨3564829687706757244859617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4753106250275676326479489 3564829687706757244859617)
                      ·
                        rfl

theorem cell23_6942481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 4, 2].length) (baseStart_6942481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6942481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6942481 prefixEnd_6942481 := by exact prefixLift 6942481
  have htrace : WordTrace (prefixWord ++ tailWord_6942481) baseStart_6942481 baseEnd_6942481 := by
    simpa [prefixWord, tailWord_6942481, baseEnd_6942481] using wordTrace_append hprefix tailTrace_6942481
  have hstable : (prefixWord ++ tailWord_6942481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6942481).length < 2 ^ (prefixWord ++ tailWord_6942481).sum := by decide
  have hdescent : baseEnd_6942481 < baseStart_6942481 := by decide
  rcases family_descends (prefixWord ++ tailWord_6942481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6942485 : List Nat := [1, 3, 2, 1, 2, 5, 1, 2, 1, 3, 2]
def baseStart_6942485 : Nat := 118140960795 + 6942485 * 2 ^ 59
def prefixEnd_6942485 : Nat := 4983230072969 + 3 ^ 40 * 6942485 * 2
def baseEnd_6942485 : Nat := 3564831741629375229209599

theorem tailTrace_6942485 : CollatzResearch.WordTrace tailWord_6942485 prefixEnd_6942485 3564831741629375229209599 := by
  unfold tailWord_6942485
  simp only [CollatzResearch.WordTrace]
  refine ⟨253213230253570001886140909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168808820169046667924093939 253213230253570001886140909)
  ·
    refine ⟨94954961345088750707302841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 253213230253570001886140909 94954961345088750707302841)
    ·
      refine ⟨71216221008816563030477131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94954961345088750707302841 71216221008816563030477131)
      ·
        refine ⟨106824331513224844545715697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71216221008816563030477131 106824331513224844545715697)
        ·
          refine ⟨80118248634918633409286773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106824331513224844545715697 80118248634918633409286773)
          ·
            refine ⟨7511085809523621882120635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 80118248634918633409286773 7511085809523621882120635)
            ·
              refine ⟨11266628714285432823180953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7511085809523621882120635 11266628714285432823180953)
              ·
                refine ⟨8449971535714074617385715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11266628714285432823180953 8449971535714074617385715)
                ·
                  refine ⟨12674957303571111926078573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8449971535714074617385715 12674957303571111926078573)
                  ·
                    refine ⟨4753108988839166972279465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12674957303571111926078573 4753108988839166972279465)
                    ·
                      refine ⟨3564831741629375229209599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4753108988839166972279465 3564831741629375229209599)
                      ·
                        rfl

theorem cell23_6942485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 1, 2, 1, 3, 2].length) (baseStart_6942485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6942485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6942485 prefixEnd_6942485 := by exact prefixLift 6942485
  have htrace : WordTrace (prefixWord ++ tailWord_6942485) baseStart_6942485 baseEnd_6942485 := by
    simpa [prefixWord, tailWord_6942485, baseEnd_6942485] using wordTrace_append hprefix tailTrace_6942485
  have hstable : (prefixWord ++ tailWord_6942485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6942485).length < 2 ^ (prefixWord ++ tailWord_6942485).sum := by decide
  have hdescent : baseEnd_6942485 < baseStart_6942485 := by decide
  rcases family_descends (prefixWord ++ tailWord_6942485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6942498 : List Nat := [3, 3, 1, 1, 2, 1, 3, 2, 1, 4, 2]
def baseStart_6942498 : Nat := 118140960795 + 6942498 * 2 ^ 59
def prefixEnd_6942498 : Nat := 4983230072969 + 3 ^ 40 * 6942498 * 2
def baseEnd_6942498 : Nat := 3564838416877883678347039

theorem tailTrace_6942498 : CollatzResearch.WordTrace tailWord_6942498 prefixEnd_6942498 3564838416877883678347039 := by
  unfold tailWord_6942498
  simp only [CollatzResearch.WordTrace]
  refine ⟨63303426100630726276591037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168809136268348603404242765 63303426100630726276591037)
  ·
    refine ⟨23738784787736522353721639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63303426100630726276591037 23738784787736522353721639)
    ·
      refine ⟨35608177181604783530582459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23738784787736522353721639 35608177181604783530582459)
      ·
        refine ⟨53412265772407175295873689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35608177181604783530582459 53412265772407175295873689)
        ·
          refine ⟨40059199329305381471905267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53412265772407175295873689 40059199329305381471905267)
          ·
            refine ⟨60088798993958072207857901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40059199329305381471905267 60088798993958072207857901)
            ·
              refine ⟨22533299622734277077946713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60088798993958072207857901 22533299622734277077946713)
              ·
                refine ⟨16899974717050707808460035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22533299622734277077946713 16899974717050707808460035)
                ·
                  refine ⟨25349962075576061712690053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16899974717050707808460035 25349962075576061712690053)
                  ·
                    refine ⟨4753117889170511571129385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25349962075576061712690053 4753117889170511571129385)
                    ·
                      refine ⟨3564838416877883678347039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4753117889170511571129385 3564838416877883678347039)
                      ·
                        rfl

theorem cell23_6942498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 2, 1, 4, 2].length) (baseStart_6942498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6942498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6942498 prefixEnd_6942498 := by exact prefixLift 6942498
  have htrace : WordTrace (prefixWord ++ tailWord_6942498) baseStart_6942498 baseEnd_6942498 := by
    simpa [prefixWord, tailWord_6942498, baseEnd_6942498] using wordTrace_append hprefix tailTrace_6942498
  have hstable : (prefixWord ++ tailWord_6942498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6942498).length < 2 ^ (prefixWord ++ tailWord_6942498).sum := by decide
  have hdescent : baseEnd_6942498 < baseStart_6942498 := by decide
  rcases family_descends (prefixWord ++ tailWord_6942498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6942518 : List Nat := [5, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3]
def baseStart_6942518 : Nat := 118140960795 + 6942518 * 2 ^ 59
def prefixEnd_6942518 : Nat := 4983230072969 + 3 ^ 40 * 6942518 * 2
def baseEnd_6942518 : Nat := 3564848686490973600096947

theorem tailTrace_6942518 : CollatzResearch.WordTrace tailWord_6942518 prefixEnd_6942518 3564848686490973600096947 := by
  unfold tailWord_6942518
  simp only [CollatzResearch.WordTrace]
  refine ⟨15825902116403153032630763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 168809622574966965681394805 15825902116403153032630763)
  ·
    refine ⟨23738853174604729548946145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15825902116403153032630763 23738853174604729548946145)
    ·
      refine ⟨17804139880953547161709609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23738853174604729548946145 17804139880953547161709609)
      ·
        refine ⟨13353104910715160371282207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17804139880953547161709609 13353104910715160371282207)
        ·
          refine ⟨20029657366072740556923311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13353104910715160371282207 20029657366072740556923311)
          ·
            refine ⟨30044486049109110835384967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20029657366072740556923311 30044486049109110835384967)
            ·
              refine ⟨45066729073663666253077451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30044486049109110835384967 45066729073663666253077451)
              ·
                refine ⟨67600093610495499379616177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45066729073663666253077451 67600093610495499379616177)
                ·
                  refine ⟨50700070207871624534712133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67600093610495499379616177 50700070207871624534712133)
                  ·
                    refine ⟨9506263163975929600258525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50700070207871624534712133 9506263163975929600258525)
                    ·
                      refine ⟨3564848686490973600096947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9506263163975929600258525 3564848686490973600096947)
                      ·
                        rfl

theorem cell23_6942518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_6942518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6942518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6942518 prefixEnd_6942518 := by exact prefixLift 6942518
  have htrace : WordTrace (prefixWord ++ tailWord_6942518) baseStart_6942518 baseEnd_6942518 := by
    simpa [prefixWord, tailWord_6942518, baseEnd_6942518] using wordTrace_append hprefix tailTrace_6942518
  have hstable : (prefixWord ++ tailWord_6942518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6942518).length < 2 ^ (prefixWord ++ tailWord_6942518).sum := by decide
  have hdescent : baseEnd_6942518 < baseStart_6942518 := by decide
  rcases family_descends (prefixWord ++ tailWord_6942518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6942531 : List Nat := [1, 1, 1, 3, 1, 6, 1, 1, 2, 3, 3]
def baseStart_6942531 : Nat := 118140960795 + 6942531 * 2 ^ 59
def prefixEnd_6942531 : Nat := 4983230072969 + 3 ^ 40 * 6942531 * 2
def baseEnd_6942531 : Nat := 3564855361739482049234387

theorem tailTrace_6942531 : CollatzResearch.WordTrace tailWord_6942531 prefixEnd_6942531 3564855361739482049234387 := by
  unfold tailWord_6942531
  simp only [CollatzResearch.WordTrace]
  refine ⟨253214908011403351742315447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168809938674268901161543631 253214908011403351742315447)
  ·
    refine ⟨379822362017105027613473171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253214908011403351742315447 379822362017105027613473171)
    ·
      refine ⟨569733543025657541420209757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379822362017105027613473171 569733543025657541420209757)
      ·
        refine ⟨213650078634621578032578659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 569733543025657541420209757 213650078634621578032578659)
        ·
          refine ⟨320475117951932367048867989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213650078634621578032578659 320475117951932367048867989)
          ·
            refine ⟨15022271153996829705415687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 320475117951932367048867989 15022271153996829705415687)
            ·
              refine ⟨22533406730995244558123531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15022271153996829705415687 22533406730995244558123531)
              ·
                refine ⟨33800110096492866837185297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22533406730995244558123531 33800110096492866837185297)
                ·
                  refine ⟨25350082572369650127888973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33800110096492866837185297 25350082572369650127888973)
                  ·
                    refine ⟨9506280964638618797958365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25350082572369650127888973 9506280964638618797958365)
                    ·
                      refine ⟨3564855361739482049234387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9506280964638618797958365 3564855361739482049234387)
                      ·
                        rfl

theorem cell23_6942531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 1, 2, 3, 3].length) (baseStart_6942531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6942531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6942531 prefixEnd_6942531 := by exact prefixLift 6942531
  have htrace : WordTrace (prefixWord ++ tailWord_6942531) baseStart_6942531 baseEnd_6942531 := by
    simpa [prefixWord, tailWord_6942531, baseEnd_6942531] using wordTrace_append hprefix tailTrace_6942531
  have hstable : (prefixWord ++ tailWord_6942531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6942531).length < 2 ^ (prefixWord ++ tailWord_6942531).sum := by decide
  have hdescent : baseEnd_6942531 < baseStart_6942531 := by decide
  rcases family_descends (prefixWord ++ tailWord_6942531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6942551 : List Nat := [1, 1, 3, 2, 5, 1, 1, 1, 1, 7]
def baseStart_6942551 : Nat := 118140960795 + 6942551 * 2 ^ 59
def prefixEnd_6942551 : Nat := 4983230072969 + 3 ^ 40 * 6942551 * 2
def baseEnd_6942551 : Nat := 1188288543784190656994765

theorem tailTrace_6942551 : CollatzResearch.WordTrace tailWord_6942551 prefixEnd_6942551 1188288543784190656994765 := by
  unfold tailWord_6942551
  simp only [CollatzResearch.WordTrace]
  refine ⟨253215637471330895158043507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168810424980887263438695671 253215637471330895158043507)
  ·
    refine ⟨379823456206996342737065261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253215637471330895158043507 379823456206996342737065261)
    ·
      refine ⟨142433796077623628526399473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 379823456206996342737065261 142433796077623628526399473)
      ·
        refine ⟨106825347058217721394799605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142433796077623628526399473 106825347058217721394799605)
        ·
          refine ⟨10014876286707911380762463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 106825347058217721394799605 10014876286707911380762463)
          ·
            refine ⟨15022314430061867071143695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10014876286707911380762463 15022314430061867071143695)
            ·
              refine ⟨22533471645092800606715543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15022314430061867071143695 22533471645092800606715543)
              ·
                refine ⟨33800207467639200910073315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22533471645092800606715543 33800207467639200910073315)
                ·
                  refine ⟨50700311201458801365109973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33800207467639200910073315 50700311201458801365109973)
                  ·
                    refine ⟨1188288543784190656994765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50700311201458801365109973 1188288543784190656994765)
                    ·
                      rfl

theorem cell23_6942551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 1, 1, 7].length) (baseStart_6942551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6942551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6942551 prefixEnd_6942551 := by exact prefixLift 6942551
  have htrace : WordTrace (prefixWord ++ tailWord_6942551) baseStart_6942551 baseEnd_6942551 := by
    simpa [prefixWord, tailWord_6942551, baseEnd_6942551] using wordTrace_append hprefix tailTrace_6942551
  have hstable : (prefixWord ++ tailWord_6942551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6942551).length < 2 ^ (prefixWord ++ tailWord_6942551).sum := by decide
  have hdescent : baseEnd_6942551 < baseStart_6942551 := by decide
  rcases family_descends (prefixWord ++ tailWord_6942551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6942615 : List Nat := [1, 1, 3, 3, 1, 3, 3, 3, 1, 4]
def baseStart_6942615 : Nat := 118140960795 + 6942615 * 2 ^ 59
def prefixEnd_6942615 : Nat := 4983230072969 + 3 ^ 40 * 6942615 * 2
def baseEnd_6942615 : Nat := 1188299498038153240194667

theorem tailTrace_6942615 : CollatzResearch.WordTrace tailWord_6942615 prefixEnd_6942615 1188299498038153240194667 := by
  unfold tailWord_6942615
  simp only [CollatzResearch.WordTrace]
  refine ⟨253217971743099034088373299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168811981162066022725582199 253217971743099034088373299)
  ·
    refine ⟨379826957614648551132559949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253217971743099034088373299 379826957614648551132559949)
    ·
      refine ⟨142435109105493206674709981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 379826957614648551132559949 142435109105493206674709981)
      ·
        refine ⟨53413165914559952503016243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142435109105493206674709981 53413165914559952503016243)
        ·
          refine ⟨80119748871839928754524365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53413165914559952503016243 80119748871839928754524365)
          ·
            refine ⟨30044905826939973282946637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80119748871839928754524365 30044905826939973282946637)
            ·
              refine ⟨11266839685102489981104989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30044905826939973282946637 11266839685102489981104989)
              ·
                refine ⟨4225064881913433742914371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11266839685102489981104989 4225064881913433742914371)
                ·
                  refine ⟨6337597322870150614371557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4225064881913433742914371 6337597322870150614371557)
                  ·
                    refine ⟨1188299498038153240194667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6337597322870150614371557 1188299498038153240194667)
                    ·
                      rfl

theorem cell23_6942615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 3, 3, 1, 4].length) (baseStart_6942615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6942615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6942615 prefixEnd_6942615 := by exact prefixLift 6942615
  have htrace : WordTrace (prefixWord ++ tailWord_6942615) baseStart_6942615 baseEnd_6942615 := by
    simpa [prefixWord, tailWord_6942615, baseEnd_6942615] using wordTrace_append hprefix tailTrace_6942615
  have hstable : (prefixWord ++ tailWord_6942615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6942615).length < 2 ^ (prefixWord ++ tailWord_6942615).sum := by decide
  have hdescent : baseEnd_6942615 < baseStart_6942615 := by decide
  rcases family_descends (prefixWord ++ tailWord_6942615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6942622 : List Nat := [4, 3, 1, 3, 1, 1, 1, 2, 2, 1, 4]
def baseStart_6942622 : Nat := 118140960795 + 6942622 * 2 ^ 59
def prefixEnd_6942622 : Nat := 4983230072969 + 3 ^ 40 * 6942622 * 2
def baseEnd_6942622 : Nat := 3564902088479041193196469

theorem tailTrace_6942622 : CollatzResearch.WordTrace tailWord_6942622 prefixEnd_6942622 3564902088479041193196469 := by
  unfold tailWord_6942622
  simp only [CollatzResearch.WordTrace]
  refine ⟨31652278381759209285484765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168812151369382449522585413 31652278381759209285484765)
  ·
    refine ⟨11869604393159703482056787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31652278381759209285484765 11869604393159703482056787)
    ·
      refine ⟨17804406589739555223085181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11869604393159703482056787 17804406589739555223085181)
      ·
        refine ⟨6676652471152333208656943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17804406589739555223085181 6676652471152333208656943)
        ·
          refine ⟨10014978706728499812985415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6676652471152333208656943 10014978706728499812985415)
          ·
            refine ⟨15022468060092749719478123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10014978706728499812985415 15022468060092749719478123)
            ·
              refine ⟨22533702090139124579217185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15022468060092749719478123 22533702090139124579217185)
              ·
                refine ⟨16900276567604343434412889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22533702090139124579217185 16900276567604343434412889)
                ·
                  refine ⟨12675207425703257575809667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16900276567604343434412889 12675207425703257575809667)
                  ·
                    refine ⟨19012811138554886363714501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12675207425703257575809667 19012811138554886363714501)
                    ·
                      refine ⟨3564902088479041193196469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19012811138554886363714501 3564902088479041193196469)
                      ·
                        rfl

theorem cell23_6942622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_6942622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6942622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6942622 prefixEnd_6942622 := by exact prefixLift 6942622
  have htrace : WordTrace (prefixWord ++ tailWord_6942622) baseStart_6942622 baseEnd_6942622 := by
    simpa [prefixWord, tailWord_6942622, baseEnd_6942622] using wordTrace_append hprefix tailTrace_6942622
  have hstable : (prefixWord ++ tailWord_6942622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6942622).length < 2 ^ (prefixWord ++ tailWord_6942622).sum := by decide
  have hdescent : baseEnd_6942622 < baseStart_6942622 := by decide
  rcases family_descends (prefixWord ++ tailWord_6942622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6942625 : List Nat := [1, 2, 3, 4, 2, 1, 1, 2, 2, 2, 3]
def baseStart_6942625 : Nat := 118140960795 + 6942625 * 2 ^ 59
def prefixEnd_6942625 : Nat := 4983230072969 + 3 ^ 40 * 6942625 * 2
def baseEnd_6942625 : Nat := 3564903628921004681458955

theorem tailTrace_6942625 : CollatzResearch.WordTrace tailWord_6942625 prefixEnd_6942625 3564903628921004681458955 := by
  unfold tailWord_6942625
  simp only [CollatzResearch.WordTrace]
  refine ⟨253218336473062805796237329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168812224315375203864158219 253218336473062805796237329)
  ·
    refine ⟨189913752354797104347177997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253218336473062805796237329 189913752354797104347177997)
    ·
      refine ⟨71217657133048914130191749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189913752354797104347177997 71217657133048914130191749)
      ·
        refine ⟨13353310712446671399410953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71217657133048914130191749 13353310712446671399410953)
        ·
          refine ⟨10014983034335003549558215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13353310712446671399410953 10014983034335003549558215)
          ·
            refine ⟨15022474551502505324337323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10014983034335003549558215 15022474551502505324337323)
            ·
              refine ⟨22533711827253757986505985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15022474551502505324337323 22533711827253757986505985)
              ·
                refine ⟨16900283870440318489879489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22533711827253757986505985 16900283870440318489879489)
                ·
                  refine ⟨12675212902830238867409617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16900283870440318489879489 12675212902830238867409617)
                  ·
                    refine ⟨9506409677122679150557213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12675212902830238867409617 9506409677122679150557213)
                    ·
                      refine ⟨3564903628921004681458955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9506409677122679150557213 3564903628921004681458955)
                      ·
                        rfl

theorem cell23_6942625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_6942625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6942625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6942625 prefixEnd_6942625 := by exact prefixLift 6942625
  have htrace : WordTrace (prefixWord ++ tailWord_6942625) baseStart_6942625 baseEnd_6942625 := by
    simpa [prefixWord, tailWord_6942625, baseEnd_6942625] using wordTrace_append hprefix tailTrace_6942625
  have hstable : (prefixWord ++ tailWord_6942625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6942625).length < 2 ^ (prefixWord ++ tailWord_6942625).sum := by decide
  have hdescent : baseEnd_6942625 < baseStart_6942625 := by decide
  rcases family_descends (prefixWord ++ tailWord_6942625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6942645 : List Nat := [1, 3, 3, 2, 1, 4, 2, 1, 6]
def baseStart_6942645 : Nat := 118140960795 + 6942645 * 2 ^ 59
def prefixEnd_6942645 : Nat := 4983230072969 + 3 ^ 40 * 6942645 * 2
def baseEnd_6942645 : Nat := 396101544281566067023207

theorem tailTrace_6942645 : CollatzResearch.WordTrace tailWord_6942645 prefixEnd_6942645 396101544281566067023207 := by
  unfold tailWord_6942645
  simp only [CollatzResearch.WordTrace]
  refine ⟨253219065932990349211965389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168812710621993566141310259 253219065932990349211965389)
  ·
    refine ⟨94957149724871380954487021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 253219065932990349211965389 94957149724871380954487021)
    ·
      refine ⟨35608931146826767857932633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94957149724871380954487021 35608931146826767857932633)
      ·
        refine ⟨26706698360120075893449475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35608931146826767857932633 26706698360120075893449475)
        ·
          refine ⟨40060047540180113840174213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26706698360120075893449475 40060047540180113840174213)
          ·
            refine ⟨7511258913783771345032665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40060047540180113840174213 7511258913783771345032665)
            ·
              refine ⟨5633444185337828508774499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7511258913783771345032665 5633444185337828508774499)
              ·
                refine ⟨8450166278006742763161749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5633444185337828508774499 8450166278006742763161749)
                ·
                  refine ⟨396101544281566067023207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8450166278006742763161749 396101544281566067023207)
                  ·
                    rfl

theorem cell23_6942645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 2, 1, 6].length) (baseStart_6942645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6942645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6942645 prefixEnd_6942645 := by exact prefixLift 6942645
  have htrace : WordTrace (prefixWord ++ tailWord_6942645) baseStart_6942645 baseEnd_6942645 := by
    simpa [prefixWord, tailWord_6942645, baseEnd_6942645] using wordTrace_append hprefix tailTrace_6942645
  have hstable : (prefixWord ++ tailWord_6942645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6942645).length < 2 ^ (prefixWord ++ tailWord_6942645).sum := by decide
  have hdescent : baseEnd_6942645 < baseStart_6942645 := by decide
  rcases family_descends (prefixWord ++ tailWord_6942645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6942648 : List Nat := [2, 1, 2, 1, 2, 3, 1, 2, 4, 3, 2]
def baseStart_6942648 : Nat := 118140960795 + 6942648 * 2 ^ 59
def prefixEnd_6942648 : Nat := 4983230072969 + 3 ^ 40 * 6942648 * 2
def baseEnd_6942648 : Nat := 3564915438976058091471349

theorem tailTrace_6942648 : CollatzResearch.WordTrace tailWord_6942648 prefixEnd_6942648 3564915438976058091471349 := by
  unfold tailWord_6942648
  simp only [CollatzResearch.WordTrace]
  refine ⟨126609587675989740362162299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168812783567986320482883065 126609587675989740362162299)
  ·
    refine ⟨189914381513984610543243449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126609587675989740362162299 189914381513984610543243449)
    ·
      refine ⟨142435786135488457907432587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189914381513984610543243449 142435786135488457907432587)
      ·
        refine ⟨213653679203232686861148881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142435786135488457907432587 213653679203232686861148881)
        ·
          refine ⟨160240259402424515145861661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213653679203232686861148881 160240259402424515145861661)
          ·
            refine ⟨60090097275909193179698123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 160240259402424515145861661 60090097275909193179698123)
            ·
              refine ⟨90135145913863789769547185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60090097275909193179698123 90135145913863789769547185)
              ·
                refine ⟨67601359435397842327160389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90135145913863789769547185 67601359435397842327160389)
                ·
                  refine ⟨12675254894137095436342573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67601359435397842327160389 12675254894137095436342573)
                  ·
                    refine ⟨4753220585301410788628465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12675254894137095436342573 4753220585301410788628465)
                    ·
                      refine ⟨3564915438976058091471349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4753220585301410788628465 3564915438976058091471349)
                      ·
                        rfl

theorem cell23_6942648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 2, 4, 3, 2].length) (baseStart_6942648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6942648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6942648 prefixEnd_6942648 := by exact prefixLift 6942648
  have htrace : WordTrace (prefixWord ++ tailWord_6942648) baseStart_6942648 baseEnd_6942648 := by
    simpa [prefixWord, tailWord_6942648, baseEnd_6942648] using wordTrace_append hprefix tailTrace_6942648
  have hstable : (prefixWord ++ tailWord_6942648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6942648).length < 2 ^ (prefixWord ++ tailWord_6942648).sum := by decide
  have hdescent : baseEnd_6942648 < baseStart_6942648 := by decide
  rcases family_descends (prefixWord ++ tailWord_6942648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6942671 : List Nat := [1, 1, 2, 1, 1, 5, 3, 2, 1, 6]
def baseStart_6942671 : Nat := 118140960795 + 6942671 * 2 ^ 59
def prefixEnd_6942671 : Nat := 4983230072969 + 3 ^ 40 * 6942671 * 2
def baseEnd_6942671 : Nat := 1188309083010370500494581

theorem tailTrace_6942671 : CollatzResearch.WordTrace tailWord_6942671 prefixEnd_6942671 1188309083010370500494581 := by
  unfold tailWord_6942671
  simp only [CollatzResearch.WordTrace]
  refine ⟨253220014230896155652411867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168813342820597437101607911 253220014230896155652411867)
  ·
    refine ⟨379830021346344233478617801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253220014230896155652411867 379830021346344233478617801)
    ·
      refine ⟨284872516009758175108963351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 379830021346344233478617801 284872516009758175108963351)
      ·
        refine ⟨427308774014637262663445027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284872516009758175108963351 427308774014637262663445027)
        ·
          refine ⟨640963161021955893995167541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 427308774014637262663445027 640963161021955893995167541)
          ·
            refine ⟨60090296345808365062046957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 640963161021955893995167541 60090296345808365062046957)
            ·
              refine ⟨22533861129678136898267609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60090296345808365062046957 22533861129678136898267609)
              ·
                refine ⟨16900395847258602673700707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22533861129678136898267609 16900395847258602673700707)
                ·
                  refine ⟨25350593770887904010551061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16900395847258602673700707 25350593770887904010551061)
                  ·
                    refine ⟨1188309083010370500494581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25350593770887904010551061 1188309083010370500494581)
                    ·
                      rfl

theorem cell23_6942671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 2, 1, 6].length) (baseStart_6942671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6942671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6942671 prefixEnd_6942671 := by exact prefixLift 6942671
  have htrace : WordTrace (prefixWord ++ tailWord_6942671) baseStart_6942671 baseEnd_6942671 := by
    simpa [prefixWord, tailWord_6942671, baseEnd_6942671] using wordTrace_append hprefix tailTrace_6942671
  have hstable : (prefixWord ++ tailWord_6942671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6942671).length < 2 ^ (prefixWord ++ tailWord_6942671).sum := by decide
  have hdescent : baseEnd_6942671 < baseStart_6942671 := by decide
  rcases family_descends (prefixWord ++ tailWord_6942671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6942698 : List Nat := [3, 1, 3, 1, 2, 1, 1, 1, 5, 2, 3]
def baseStart_6942698 : Nat := 118140960795 + 6942698 * 2 ^ 59
def prefixEnd_6942698 : Nat := 4983230072969 + 3 ^ 40 * 6942698 * 2
def baseEnd_6942698 : Nat := 3564941113008782895846119

theorem tailTrace_6942698 : CollatzResearch.WordTrace tailWord_6942698 prefixEnd_6942698 3564941113008782895846119 := by
  unfold tailWord_6942698
  simp only [CollatzResearch.WordTrace]
  refine ⟨63305249750449584815911187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168813999334532226175763165 63305249750449584815911187)
  ·
    refine ⟨94957874625674377223866781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63305249750449584815911187 94957874625674377223866781)
    ·
      refine ⟨35609202984627891458950043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94957874625674377223866781 35609202984627891458950043)
      ·
        refine ⟨53413804476941837188425065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35609202984627891458950043 53413804476941837188425065)
        ·
          refine ⟨40060353357706377891318799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53413804476941837188425065 40060353357706377891318799)
          ·
            refine ⟨60090530036559566836978199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40060353357706377891318799 60090530036559566836978199)
            ·
              refine ⟨90135795054839350255467299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60090530036559566836978199 90135795054839350255467299)
              ·
                refine ⟨135203692582259025383200949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90135795054839350255467299 135203692582259025383200949)
                ·
                  refine ⟨12675346179586783629675089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 135203692582259025383200949 12675346179586783629675089)
                  ·
                    refine ⟨9506509634690087722256317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12675346179586783629675089 9506509634690087722256317)
                    ·
                      refine ⟨3564941113008782895846119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9506509634690087722256317 3564941113008782895846119)
                      ·
                        rfl

theorem cell23_6942698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 5, 2, 3].length) (baseStart_6942698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6942698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6942698 prefixEnd_6942698 := by exact prefixLift 6942698
  have htrace : WordTrace (prefixWord ++ tailWord_6942698) baseStart_6942698 baseEnd_6942698 := by
    simpa [prefixWord, tailWord_6942698, baseEnd_6942698] using wordTrace_append hprefix tailTrace_6942698
  have hstable : (prefixWord ++ tailWord_6942698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6942698).length < 2 ^ (prefixWord ++ tailWord_6942698).sum := by decide
  have hdescent : baseEnd_6942698 < baseStart_6942698 := by decide
  rcases family_descends (prefixWord ++ tailWord_6942698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6942726 : List Nat := [6, 2, 1, 2, 1, 1, 1, 3, 1, 5]
def baseStart_6942726 : Nat := 118140960795 + 6942726 * 2 ^ 59
def prefixEnd_6942726 : Nat := 4983230072969 + 3 ^ 40 * 6942726 * 2
def baseEnd_6942726 : Nat := 1188318496822369595431997

theorem tailTrace_6942726 : CollatzResearch.WordTrace tailWord_6942726 prefixEnd_6942726 1188318496822369595431997 := by
  unfold tailWord_6942726
  simp only [CollatzResearch.WordTrace]
  refine ⟨7913188132678028126427001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 168814680163797933363776021 7913188132678028126427001)
  ·
    refine ⟨5934891099508521094820251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7913188132678028126427001 5934891099508521094820251)
    ·
      refine ⟨8902336649262781642230377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5934891099508521094820251 8902336649262781642230377)
      ·
        refine ⟨6676752486947086231672783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8902336649262781642230377 6676752486947086231672783)
        ·
          refine ⟨10015128730420629347509175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6676752486947086231672783 10015128730420629347509175)
          ·
            refine ⟨15022693095630944021263763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10015128730420629347509175 15022693095630944021263763)
            ·
              refine ⟨22534039643446416031895645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15022693095630944021263763 22534039643446416031895645)
              ·
                refine ⟨8450264866292406011960867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22534039643446416031895645 8450264866292406011960867)
                ·
                  refine ⟨12675397299438609017941301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8450264866292406011960867 12675397299438609017941301)
                  ·
                    refine ⟨1188318496822369595431997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12675397299438609017941301 1188318496822369595431997)
                    ·
                      rfl

theorem cell23_6942726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_6942726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6942726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6942726 prefixEnd_6942726 := by exact prefixLift 6942726
  have htrace : WordTrace (prefixWord ++ tailWord_6942726) baseStart_6942726 baseEnd_6942726 := by
    simpa [prefixWord, tailWord_6942726, baseEnd_6942726] using wordTrace_append hprefix tailTrace_6942726
  have hstable : (prefixWord ++ tailWord_6942726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6942726).length < 2 ^ (prefixWord ++ tailWord_6942726).sum := by decide
  have hdescent : baseEnd_6942726 < baseStart_6942726 := by decide
  rcases family_descends (prefixWord ++ tailWord_6942726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6942728 : List Nat := [2, 1, 3, 2, 1, 2, 1, 4, 1, 3, 3]
def baseStart_6942728 : Nat := 118140960795 + 6942728 * 2 ^ 59
def prefixEnd_6942728 : Nat := 4983230072969 + 3 ^ 40 * 6942728 * 2
def baseEnd_6942728 : Nat := 3564956517428417778470981

theorem tailTrace_6942728 : CollatzResearch.WordTrace tailWord_6942728 prefixEnd_6942728 3564956517428417778470981 := by
  unfold tailWord_6942728
  simp only [CollatzResearch.WordTrace]
  refine ⟨126611046595844827193618419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168814728794459769591491225 126611046595844827193618419)
  ·
    refine ⟨189916569893767240790427629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126611046595844827193618419 189916569893767240790427629)
    ·
      refine ⟨71218713710162715296410361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189916569893767240790427629 71218713710162715296410361)
      ·
        refine ⟨53414035282622036472307771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71218713710162715296410361 53414035282622036472307771)
        ·
          refine ⟨80121052923933054708461657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53414035282622036472307771 80121052923933054708461657)
          ·
            refine ⟨60090789692949791031346243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80121052923933054708461657 60090789692949791031346243)
            ·
              refine ⟨90136184539424686547019365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60090789692949791031346243 90136184539424686547019365)
              ·
                refine ⟨16900534601142128727566131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90136184539424686547019365 16900534601142128727566131)
                ·
                  refine ⟨25350801901713193091349197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16900534601142128727566131 25350801901713193091349197)
                  ·
                    refine ⟨9506550713142447409255949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25350801901713193091349197 9506550713142447409255949)
                    ·
                      refine ⟨3564956517428417778470981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9506550713142447409255949 3564956517428417778470981)
                      ·
                        rfl

theorem cell23_6942728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 4, 1, 3, 3].length) (baseStart_6942728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6942728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6942728 prefixEnd_6942728 := by exact prefixLift 6942728
  have htrace : WordTrace (prefixWord ++ tailWord_6942728) baseStart_6942728 baseEnd_6942728 := by
    simpa [prefixWord, tailWord_6942728, baseEnd_6942728] using wordTrace_append hprefix tailTrace_6942728
  have hstable : (prefixWord ++ tailWord_6942728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6942728).length < 2 ^ (prefixWord ++ tailWord_6942728).sum := by decide
  have hdescent : baseEnd_6942728 < baseStart_6942728 := by decide
  rcases family_descends (prefixWord ++ tailWord_6942728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6942759 : List Nat := [1, 1, 7, 1, 3, 1, 1, 1, 1, 2, 4]
def baseStart_6942759 : Nat := 118140960795 + 6942759 * 2 ^ 59
def prefixEnd_6942759 : Nat := 4983230072969 + 3 ^ 40 * 6942759 * 2
def baseEnd_6942759 : Nat := 3564972435328707157183339

theorem tailTrace_6942759 : CollatzResearch.WordTrace tailWord_6942759 prefixEnd_6942759 3564972435328707157183339 := by
  unfold tailWord_6942759
  simp only [CollatzResearch.WordTrace]
  refine ⟨253223223854577346681615331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168815482569718231121076887 253223223854577346681615331)
  ·
    refine ⟨379834835781866020022422997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253223223854577346681615331 379834835781866020022422997)
    ·
      refine ⟨8902378963637484844275539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 379834835781866020022422997 8902378963637484844275539)
      ·
        refine ⟨13353568445456227266413309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8902378963637484844275539 13353568445456227266413309)
        ·
          refine ⟨5007588167046085224904991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13353568445456227266413309 5007588167046085224904991)
          ·
            refine ⟨7511382250569127837357487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5007588167046085224904991 7511382250569127837357487)
            ·
              refine ⟨11267073375853691756036231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7511382250569127837357487 11267073375853691756036231)
              ·
                refine ⟨16900610063780537634054347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11267073375853691756036231 16900610063780537634054347)
                ·
                  refine ⟨25350915095670806451081521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16900610063780537634054347 25350915095670806451081521)
                  ·
                    refine ⟨19013186321753104838311141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25350915095670806451081521 19013186321753104838311141)
                    ·
                      refine ⟨3564972435328707157183339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19013186321753104838311141 3564972435328707157183339)
                      ·
                        rfl

theorem cell23_6942759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 1, 1, 1, 2, 4].length) (baseStart_6942759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6942759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6942759 prefixEnd_6942759 := by exact prefixLift 6942759
  have htrace : WordTrace (prefixWord ++ tailWord_6942759) baseStart_6942759 baseEnd_6942759 := by
    simpa [prefixWord, tailWord_6942759, baseEnd_6942759] using wordTrace_append hprefix tailTrace_6942759
  have hstable : (prefixWord ++ tailWord_6942759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6942759).length < 2 ^ (prefixWord ++ tailWord_6942759).sum := by decide
  have hdescent : baseEnd_6942759 < baseStart_6942759 := by decide
  rcases family_descends (prefixWord ++ tailWord_6942759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6942762 : List Nat := [3, 1, 4, 1, 2, 3, 1, 1, 1, 3, 3]
def baseStart_6942762 : Nat := 118140960795 + 6942762 * 2 ^ 59
def prefixEnd_6942762 : Nat := 4983230072969 + 3 ^ 40 * 6942762 * 2
def baseEnd_6942762 : Nat := 3564973975770670645445825

theorem tailTrace_6942762 : CollatzResearch.WordTrace tailWord_6942762 prefixEnd_6942762 3564973975770670645445825 := by
  unfold tailWord_6942762
  simp only [CollatzResearch.WordTrace]
  refine ⟨63305833318391619548493635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168815555515710985462649693 63305833318391619548493635)
  ·
    refine ⟨94958749977587429322740453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63305833318391619548493635 94958749977587429322740453)
    ·
      refine ⟨17804765620797642998013835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94958749977587429322740453 17804765620797642998013835)
      ·
        refine ⟨26707148431196464497020753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17804765620797642998013835 26707148431196464497020753)
        ·
          refine ⟨20030361323397348372765565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26707148431196464497020753 20030361323397348372765565)
          ·
            refine ⟨7511385496274005639787087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20030361323397348372765565 7511385496274005639787087)
            ·
              refine ⟨11267078244411008459680631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7511385496274005639787087 11267078244411008459680631)
              ·
                refine ⟨16900617366616512689520947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11267078244411008459680631 16900617366616512689520947)
                ·
                  refine ⟨25350926049924769034281421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16900617366616512689520947 25350926049924769034281421)
                  ·
                    refine ⟨9506597268721788387855533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25350926049924769034281421 9506597268721788387855533)
                    ·
                      refine ⟨3564973975770670645445825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9506597268721788387855533 3564973975770670645445825)
                      ·
                        rfl

theorem cell23_6942762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 1, 1, 1, 3, 3].length) (baseStart_6942762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6942762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6942762 prefixEnd_6942762 := by exact prefixLift 6942762
  have htrace : WordTrace (prefixWord ++ tailWord_6942762) baseStart_6942762 baseEnd_6942762 := by
    simpa [prefixWord, tailWord_6942762, baseEnd_6942762] using wordTrace_append hprefix tailTrace_6942762
  have hstable : (prefixWord ++ tailWord_6942762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6942762).length < 2 ^ (prefixWord ++ tailWord_6942762).sum := by decide
  have hdescent : baseEnd_6942762 < baseStart_6942762 := by decide
  rcases family_descends (prefixWord ++ tailWord_6942762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6942801 : List Nat := [1, 2, 2, 1, 3, 1, 1, 1, 1, 1, 9]
def baseStart_6942801 : Nat := 118140960795 + 6942801 * 2 ^ 59
def prefixEnd_6942801 : Nat := 4983230072969 + 3 ^ 40 * 6942801 * 2
def baseEnd_6942801 : Nat := 3564994001516195992858145

theorem tailTrace_6942801 : CollatzResearch.WordTrace tailWord_6942801 prefixEnd_6942801 3564994001516195992858145 := by
  unfold tailWord_6942801
  simp only [CollatzResearch.WordTrace]
  refine ⟨253224755720425187854644257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168816503813616791903096171 253224755720425187854644257)
  ·
    refine ⟨189918566790318890890983193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253224755720425187854644257 189918566790318890890983193)
    ·
      refine ⟨142438925092739168168237395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189918566790318890890983193 142438925092739168168237395)
      ·
        refine ⟨213658387639108752252356093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142438925092739168168237395 213658387639108752252356093)
        ·
          refine ⟨80121895364665782094633535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 213658387639108752252356093 80121895364665782094633535)
          ·
            refine ⟨120182843046998673141950303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80121895364665782094633535 120182843046998673141950303)
            ·
              refine ⟨180274264570498009712925455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120182843046998673141950303 180274264570498009712925455)
              ·
                refine ⟨270411396855747014569388183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 180274264570498009712925455 270411396855747014569388183)
                ·
                  refine ⟨405617095283620521854082275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 270411396855747014569388183 405617095283620521854082275)
                  ·
                    refine ⟨608425642925430782781123413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 405617095283620521854082275 608425642925430782781123413)
                    ·
                      refine ⟨3564994001516195992858145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 608425642925430782781123413 3564994001516195992858145)
                      ·
                        rfl

theorem cell23_6942801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 1, 9].length) (baseStart_6942801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6942801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6942801 prefixEnd_6942801 := by exact prefixLift 6942801
  have htrace : WordTrace (prefixWord ++ tailWord_6942801) baseStart_6942801 baseEnd_6942801 := by
    simpa [prefixWord, tailWord_6942801, baseEnd_6942801] using wordTrace_append hprefix tailTrace_6942801
  have hstable : (prefixWord ++ tailWord_6942801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6942801).length < 2 ^ (prefixWord ++ tailWord_6942801).sum := by decide
  have hdescent : baseEnd_6942801 < baseStart_6942801 := by decide
  rcases family_descends (prefixWord ++ tailWord_6942801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6942808 : List Nat := [2, 1, 2, 2, 1, 4, 3, 1, 7]
def baseStart_6942808 : Nat := 118140960795 + 6942808 * 2 ^ 59
def prefixEnd_6942808 : Nat := 4983230072969 + 3 ^ 40 * 6942808 * 2
def baseEnd_6942808 : Nat := 396110843986753051718957

theorem tailTrace_6942808 : CollatzResearch.WordTrace tailWord_6942808 prefixEnd_6942808 396110843986753051718957 := by
  unfold tailWord_6942808
  simp only [CollatzResearch.WordTrace]
  refine ⟨126612505515699914025074539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168816674020933218700099385 126612505515699914025074539)
  ·
    refine ⟨189918758273549871037611809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126612505515699914025074539 189918758273549871037611809)
    ·
      refine ⟨142439068705162403278208857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189918758273549871037611809 142439068705162403278208857)
      ·
        refine ⟨106829301528871802458656643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142439068705162403278208857 106829301528871802458656643)
        ·
          refine ⟨160243952293307703687984965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106829301528871802458656643 160243952293307703687984965)
          ·
            refine ⟨30045741054995194441497181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 160243952293307703687984965 30045741054995194441497181)
            ·
              refine ⟨11267152895623197915561443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30045741054995194441497181 11267152895623197915561443)
              ·
                refine ⟨16900729343434796873342165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11267152895623197915561443 16900729343434796873342165)
                ·
                  refine ⟨396110843986753051718957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16900729343434796873342165 396110843986753051718957)
                  ·
                    rfl

theorem cell23_6942808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 3, 1, 7].length) (baseStart_6942808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6942808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6942808 prefixEnd_6942808 := by exact prefixLift 6942808
  have htrace : WordTrace (prefixWord ++ tailWord_6942808) baseStart_6942808 baseEnd_6942808 := by
    simpa [prefixWord, tailWord_6942808, baseEnd_6942808] using wordTrace_append hprefix tailTrace_6942808
  have hstable : (prefixWord ++ tailWord_6942808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6942808).length < 2 ^ (prefixWord ++ tailWord_6942808).sum := by decide
  have hdescent : baseEnd_6942808 < baseStart_6942808 := by decide
  rcases family_descends (prefixWord ++ tailWord_6942808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6942819 : List Nat := [1, 1, 1, 5, 1, 1, 6, 1, 2, 2, 2]
def baseStart_6942819 : Nat := 118140960795 + 6942819 * 2 ^ 59
def prefixEnd_6942819 : Nat := 4983230072969 + 3 ^ 40 * 6942819 * 2
def baseEnd_6942819 : Nat := 3565003244167976922433063

theorem tailTrace_6942819 : CollatzResearch.WordTrace tailWord_6942819 prefixEnd_6942819 3565003244167976922433063 := by
  unfold tailWord_6942819
  simp only [CollatzResearch.WordTrace]
  refine ⟨253225412234359976928799511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168816941489573317952533007 253225412234359976928799511)
  ·
    refine ⟨379838118351539965393199267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253225412234359976928799511 379838118351539965393199267)
    ·
      refine ⟨569757177527309948089798901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379838118351539965393199267 569757177527309948089798901)
      ·
        refine ⟨53414735393185307633418647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 569757177527309948089798901 53414735393185307633418647)
        ·
          refine ⟨80122103089777961450127971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53414735393185307633418647 80122103089777961450127971)
          ·
            refine ⟨120183154634666942175191957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80122103089777961450127971 120183154634666942175191957)
            ·
              refine ⟨5633585373500012914462123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 120183154634666942175191957 5633585373500012914462123)
              ·
                refine ⟨8450378060250019371693185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5633585373500012914462123 8450378060250019371693185)
                ·
                  refine ⟨6337783545187514528769889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8450378060250019371693185 6337783545187514528769889)
                  ·
                    refine ⟨4753337658890635896577417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6337783545187514528769889 4753337658890635896577417)
                    ·
                      refine ⟨3565003244167976922433063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4753337658890635896577417 3565003244167976922433063)
                      ·
                        rfl

theorem cell23_6942819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 6, 1, 2, 2, 2].length) (baseStart_6942819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6942819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6942819 prefixEnd_6942819 := by exact prefixLift 6942819
  have htrace : WordTrace (prefixWord ++ tailWord_6942819) baseStart_6942819 baseEnd_6942819 := by
    simpa [prefixWord, tailWord_6942819, baseEnd_6942819] using wordTrace_append hprefix tailTrace_6942819
  have hstable : (prefixWord ++ tailWord_6942819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6942819).length < 2 ^ (prefixWord ++ tailWord_6942819).sum := by decide
  have hdescent : baseEnd_6942819 < baseStart_6942819 := by decide
  rcases family_descends (prefixWord ++ tailWord_6942819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6942870 : List Nat := [5, 3, 2, 1, 1, 1, 2, 1, 1, 4, 2]
def baseStart_6942870 : Nat := 118140960795 + 6942870 * 2 ^ 59
def prefixEnd_6942870 : Nat := 4983230072969 + 3 ^ 40 * 6942870 * 2
def baseEnd_6942870 : Nat := 3565029431681356222895329

theorem tailTrace_6942870 : CollatzResearch.WordTrace tailWord_6942870 prefixEnd_6942870 3565029431681356222895329 := by
  unfold tailWord_6942870
  simp only [CollatzResearch.WordTrace]
  refine ⟨15826704522323450789931629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 168818181571450141759270709 15826704522323450789931629)
  ·
    refine ⟨5935014195871294046224361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15826704522323450789931629 5935014195871294046224361)
    ·
      refine ⟨4451260646903470534668271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5935014195871294046224361 4451260646903470534668271)
      ·
        refine ⟨6676890970355205802002407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4451260646903470534668271 6676890970355205802002407)
        ·
          refine ⟨10015336455532808703003611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6676890970355205802002407 10015336455532808703003611)
          ·
            refine ⟨15023004683299213054505417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10015336455532808703003611 15023004683299213054505417)
            ·
              refine ⟨11267253512474409790879063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15023004683299213054505417 11267253512474409790879063)
              ·
                refine ⟨16900880268711614686318595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11267253512474409790879063 16900880268711614686318595)
                ·
                  refine ⟨25351320403067422029477893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16900880268711614686318595 25351320403067422029477893)
                  ·
                    refine ⟨4753372575575141630527105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25351320403067422029477893 4753372575575141630527105)
                    ·
                      refine ⟨3565029431681356222895329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4753372575575141630527105 3565029431681356222895329)
                      ·
                        rfl

theorem cell23_6942870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_6942870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6942870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6942870 prefixEnd_6942870 := by exact prefixLift 6942870
  have htrace : WordTrace (prefixWord ++ tailWord_6942870) baseStart_6942870 baseEnd_6942870 := by
    simpa [prefixWord, tailWord_6942870, baseEnd_6942870] using wordTrace_append hprefix tailTrace_6942870
  have hstable : (prefixWord ++ tailWord_6942870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6942870).length < 2 ^ (prefixWord ++ tailWord_6942870).sum := by decide
  have hdescent : baseEnd_6942870 < baseStart_6942870 := by decide
  rcases family_descends (prefixWord ++ tailWord_6942870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6942885 : List Nat := [1, 3, 1, 2, 1, 3, 3, 2, 3, 4]
def baseStart_6942885 : Nat := 118140960795 + 6942885 * 2 ^ 59
def prefixEnd_6942885 : Nat := 4983230072969 + 3 ^ 40 * 6942885 * 2
def baseEnd_6942885 : Nat := 1188345711297057888069253

theorem tailTrace_6942885 : CollatzResearch.WordTrace tailWord_6942885 prefixEnd_6942885 1188345711297057888069253 := by
  unfold tailWord_6942885
  simp only [CollatzResearch.WordTrace]
  refine ⟨253227819452120870200702109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168818546301413913467134739 253227819452120870200702109)
  ·
    refine ⟨94960432294545326325263291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 253227819452120870200702109 94960432294545326325263291)
    ·
      refine ⟨142440648441817989487894937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94960432294545326325263291 142440648441817989487894937)
      ·
        refine ⟨106830486331363492115921203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142440648441817989487894937 106830486331363492115921203)
        ·
          refine ⟨160245729497045238173881805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106830486331363492115921203 160245729497045238173881805)
          ·
            refine ⟨60092148561391964315205677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 160245729497045238173881805 60092148561391964315205677)
            ·
              refine ⟨22534555710521986618202129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60092148561391964315205677 22534555710521986618202129)
              ·
                refine ⟨16900916782891489963651597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22534555710521986618202129 16900916782891489963651597)
                ·
                  refine ⟨6337843793584308736369349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16900916782891489963651597 6337843793584308736369349)
                  ·
                    refine ⟨1188345711297057888069253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6337843793584308736369349 1188345711297057888069253)
                    ·
                      rfl

theorem cell23_6942885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 2, 3, 4].length) (baseStart_6942885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6942885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6942885 prefixEnd_6942885 := by exact prefixLift 6942885
  have htrace : WordTrace (prefixWord ++ tailWord_6942885) baseStart_6942885 baseEnd_6942885 := by
    simpa [prefixWord, tailWord_6942885, baseEnd_6942885] using wordTrace_append hprefix tailTrace_6942885
  have hstable : (prefixWord ++ tailWord_6942885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6942885).length < 2 ^ (prefixWord ++ tailWord_6942885).sum := by decide
  have hdescent : baseEnd_6942885 < baseStart_6942885 := by decide
  rcases family_descends (prefixWord ++ tailWord_6942885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6942898 : List Nat := [3, 2, 1, 1, 1, 3, 2, 2, 8]
def baseStart_6942898 : Nat := 118140960795 + 6942898 * 2 ^ 59
def prefixEnd_6942898 : Nat := 4983230072969 + 3 ^ 40 * 6942898 * 2
def baseEnd_6942898 : Nat := 396115978793298012593911

theorem tailTrace_6942898 : CollatzResearch.WordTrace tailWord_6942898 prefixEnd_6942898 396115978793298012593911 := by
  unfold tailWord_6942898
  simp only [CollatzResearch.WordTrace]
  refine ⟨63307073400268443355231337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168818862400715848947283565 63307073400268443355231337)
  ·
    refine ⟨47480305050201332516423503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63307073400268443355231337 47480305050201332516423503)
    ·
      refine ⟨71220457575301998774635255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47480305050201332516423503 71220457575301998774635255)
      ·
        refine ⟨106830686362952998161952883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71220457575301998774635255 106830686362952998161952883)
        ·
          refine ⟨160246029544429497242929325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106830686362952998161952883 160246029544429497242929325)
          ·
            refine ⟨60092261079161061466098497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 160246029544429497242929325 60092261079161061466098497)
            ·
              refine ⟨45069195809370796099573873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60092261079161061466098497 45069195809370796099573873)
              ·
                refine ⟨33801896857028097074680405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45069195809370796099573873 33801896857028097074680405)
                ·
                  refine ⟨396115978793298012593911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33801896857028097074680405 396115978793298012593911)
                  ·
                    rfl

theorem cell23_6942898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 2, 8].length) (baseStart_6942898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6942898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6942898 prefixEnd_6942898 := by exact prefixLift 6942898
  have htrace : WordTrace (prefixWord ++ tailWord_6942898) baseStart_6942898 baseEnd_6942898 := by
    simpa [prefixWord, tailWord_6942898, baseEnd_6942898] using wordTrace_append hprefix tailTrace_6942898
  have hstable : (prefixWord ++ tailWord_6942898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6942898).length < 2 ^ (prefixWord ++ tailWord_6942898).sum := by decide
  have hdescent : baseEnd_6942898 < baseStart_6942898 := by decide
  rcases family_descends (prefixWord ++ tailWord_6942898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6942938 : List Nat := [3, 1, 1, 2, 2, 1, 2, 1, 2, 1, 7]
def baseStart_6942938 : Nat := 118140960795 + 6942938 * 2 ^ 59
def prefixEnd_6942938 : Nat := 4983230072969 + 3 ^ 40 * 6942938 * 2
def baseEnd_6942938 : Nat := 3565064348365861956845015

theorem tailTrace_6942938 : CollatzResearch.WordTrace tailWord_6942938 prefixEnd_6942938 3565064348365861956845015 := by
  unfold tailWord_6942938
  simp only [CollatzResearch.WordTrace]
  refine ⟨63307438130232215063095367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168819835013952573501587645 63307438130232215063095367)
  ·
    refine ⟨94961157195348322594643051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63307438130232215063095367 94961157195348322594643051)
    ·
      refine ⟨142441735793022483891964577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94961157195348322594643051 142441735793022483891964577)
      ·
        refine ⟨106831301844766862918973433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142441735793022483891964577 106831301844766862918973433)
        ·
          refine ⟨80123476383575147189230075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106831301844766862918973433 80123476383575147189230075)
          ·
            refine ⟨120185214575362720783845113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80123476383575147189230075 120185214575362720783845113)
            ·
              refine ⟨90138910931522040587883835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120185214575362720783845113 90138910931522040587883835)
              ·
                refine ⟨135208366397283060881825753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90138910931522040587883835 135208366397283060881825753)
                ·
                  refine ⟨101406274797962295661369315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 135208366397283060881825753 101406274797962295661369315)
                  ·
                    refine ⟨152109412196943443492053973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 101406274797962295661369315 152109412196943443492053973)
                    ·
                      refine ⟨3565064348365861956845015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 152109412196943443492053973 3565064348365861956845015)
                      ·
                        rfl

theorem cell23_6942938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 2, 1, 7].length) (baseStart_6942938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6942938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6942938 prefixEnd_6942938 := by exact prefixLift 6942938
  have htrace : WordTrace (prefixWord ++ tailWord_6942938) baseStart_6942938 baseEnd_6942938 := by
    simpa [prefixWord, tailWord_6942938, baseEnd_6942938] using wordTrace_append hprefix tailTrace_6942938
  have hstable : (prefixWord ++ tailWord_6942938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6942938).length < 2 ^ (prefixWord ++ tailWord_6942938).sum := by decide
  have hdescent : baseEnd_6942938 < baseStart_6942938 := by decide
  rcases family_descends (prefixWord ++ tailWord_6942938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6942952 : List Nat := [2, 1, 4, 1, 2, 2, 2, 1, 1, 5, 2]
def baseStart_6942952 : Nat := 118140960795 + 6942952 * 2 ^ 59
def prefixEnd_6942952 : Nat := 4983230072969 + 3 ^ 40 * 6942952 * 2
def baseEnd_6942952 : Nat := 3565071537095024902069951

theorem tailTrace_6942952 : CollatzResearch.WordTrace tailWord_6942952 prefixEnd_6942952 3565071537095024902069951 := by
  unfold tailWord_6942952
  simp only [CollatzResearch.WordTrace]
  refine ⟨126615131571439070321695555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168820175428585427095594073 126615131571439070321695555)
  ·
    refine ⟨189922697357158605482543333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126615131571439070321695555 189922697357158605482543333)
    ·
      refine ⟨35610505754467238527976875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 189922697357158605482543333 35610505754467238527976875)
      ·
        refine ⟨53415758631700857791965313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35610505754467238527976875 53415758631700857791965313)
        ·
          refine ⟨40061818973775643343973985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53415758631700857791965313 40061818973775643343973985)
          ·
            refine ⟨30046364230331732507980489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40061818973775643343973985 30046364230331732507980489)
            ·
              refine ⟨22534773172748799380985367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30046364230331732507980489 22534773172748799380985367)
              ·
                refine ⟨33802159759123199071478051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22534773172748799380985367 33802159759123199071478051)
                ·
                  refine ⟨50703239638684798607217077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33802159759123199071478051 50703239638684798607217077)
                  ·
                    refine ⟨4753428716126699869426601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50703239638684798607217077 4753428716126699869426601)
                    ·
                      refine ⟨3565071537095024902069951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4753428716126699869426601 3565071537095024902069951)
                      ·
                        rfl

theorem cell23_6942952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 1, 1, 5, 2].length) (baseStart_6942952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6942952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6942952 prefixEnd_6942952 := by exact prefixLift 6942952
  have htrace : WordTrace (prefixWord ++ tailWord_6942952) baseStart_6942952 baseEnd_6942952 := by
    simpa [prefixWord, tailWord_6942952, baseEnd_6942952] using wordTrace_append hprefix tailTrace_6942952
  have hstable : (prefixWord ++ tailWord_6942952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6942952).length < 2 ^ (prefixWord ++ tailWord_6942952).sum := by decide
  have hdescent : baseEnd_6942952 < baseStart_6942952 := by decide
  rcases family_descends (prefixWord ++ tailWord_6942952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6942962 : List Nat := [3, 2, 1, 3, 2, 1, 2, 3, 1, 5]
def baseStart_6942962 : Nat := 118140960795 + 6942962 * 2 ^ 59
def prefixEnd_6942962 : Nat := 4983230072969 + 3 ^ 40 * 6942962 * 2
def baseEnd_6942962 : Nat := 1188358890633856620981635

theorem tailTrace_6942962 : CollatzResearch.WordTrace tailWord_6942962 prefixEnd_6942962 1188358890633856620981635 := by
  unfold tailWord_6942962
  simp only [CollatzResearch.WordTrace]
  refine ⟨63307656968210478087813785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168820418581894608234170093 63307656968210478087813785)
  ·
    refine ⟨47480742726157858565860339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63307656968210478087813785 47480742726157858565860339)
    ·
      refine ⟨71221114089236787848790509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47480742726157858565860339 71221114089236787848790509)
      ·
        refine ⟨26707917783463795443296441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71221114089236787848790509 26707917783463795443296441)
        ·
          refine ⟨20030938337597846582472331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26707917783463795443296441 20030938337597846582472331)
          ·
            refine ⟨30046407506396769873708497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20030938337597846582472331 30046407506396769873708497)
            ·
              refine ⟨22534805629797577405281373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30046407506396769873708497 22534805629797577405281373)
              ·
                refine ⟨8450552111174091526980515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22534805629797577405281373 8450552111174091526980515)
                ·
                  refine ⟨12675828166761137290470773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8450552111174091526980515 12675828166761137290470773)
                  ·
                    refine ⟨1188358890633856620981635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12675828166761137290470773 1188358890633856620981635)
                    ·
                      rfl

theorem cell23_6942962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 3, 1, 5].length) (baseStart_6942962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6942962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6942962 prefixEnd_6942962 := by exact prefixLift 6942962
  have htrace : WordTrace (prefixWord ++ tailWord_6942962) baseStart_6942962 baseEnd_6942962 := by
    simpa [prefixWord, tailWord_6942962, baseEnd_6942962] using wordTrace_append hprefix tailTrace_6942962
  have hstable : (prefixWord ++ tailWord_6942962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6942962).length < 2 ^ (prefixWord ++ tailWord_6942962).sum := by decide
  have hdescent : baseEnd_6942962 < baseStart_6942962 := by decide
  rcases family_descends (prefixWord ++ tailWord_6942962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6942975 : List Nat := [1, 1, 2, 2, 1, 4, 1, 3, 4, 4]
def baseStart_6942975 : Nat := 118140960795 + 6942975 * 2 ^ 59
def prefixEnd_6942975 : Nat := 4983230072969 + 3 ^ 40 * 6942975 * 2
def baseEnd_6942975 : Nat := 1188361115716692770694115

theorem tailTrace_6942975 : CollatzResearch.WordTrace tailWord_6942975 prefixEnd_6942975 1188361115716692770694115 := by
  unfold tailWord_6942975
  simp only [CollatzResearch.WordTrace]
  refine ⟨253231102021794815571478379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168820734681196543714318919 253231102021794815571478379)
  ·
    refine ⟨379846653032692223357217569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253231102021794815571478379 379846653032692223357217569)
    ·
      refine ⟨284884989774519167517913177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 379846653032692223357217569 284884989774519167517913177)
      ·
        refine ⟨213663742330889375638434883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 284884989774519167517913177 213663742330889375638434883)
        ·
          refine ⟨320495613496334063457652325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213663742330889375638434883 320495613496334063457652325)
          ·
            refine ⟨60092927530562636898309811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 320495613496334063457652325 60092927530562636898309811)
            ·
              refine ⟨90139391295843955347464717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60092927530562636898309811 90139391295843955347464717)
              ·
                refine ⟨33802271735941483255299269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90139391295843955347464717 33802271735941483255299269)
                ·
                  refine ⟨6337925950489028110368613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33802271735941483255299269 6337925950489028110368613)
                  ·
                    refine ⟨1188361115716692770694115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6337925950489028110368613 1188361115716692770694115)
                    ·
                      rfl

theorem cell23_6942975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 3, 4, 4].length) (baseStart_6942975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6942975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6942975 prefixEnd_6942975 := by exact prefixLift 6942975
  have htrace : WordTrace (prefixWord ++ tailWord_6942975) baseStart_6942975 baseEnd_6942975 := by
    simpa [prefixWord, tailWord_6942975, baseEnd_6942975] using wordTrace_append hprefix tailTrace_6942975
  have hstable : (prefixWord ++ tailWord_6942975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6942975).length < 2 ^ (prefixWord ++ tailWord_6942975).sum := by decide
  have hdescent : baseEnd_6942975 < baseStart_6942975 := by decide
  rcases family_descends (prefixWord ++ tailWord_6942975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6942985 : List Nat := [1, 2, 1, 1, 3, 4, 2, 2, 1, 1, 5]
def baseStart_6942985 : Nat := 118140960795 + 6942985 * 2 ^ 59
def prefixEnd_6942985 : Nat := 4983230072969 + 3 ^ 40 * 6942985 * 2
def baseEnd_6942985 : Nat := 3565088481956623272957299

theorem tailTrace_6942985 : CollatzResearch.WordTrace tailWord_6942985 prefixEnd_6942985 3565088481956623272957299 := by
  unfold tailWord_6942985
  simp only [CollatzResearch.WordTrace]
  refine ⟨253231466751758587279342409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168820977834505724852894939 253231466751758587279342409)
  ·
    refine ⟨189923600063818940459506807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253231466751758587279342409 189923600063818940459506807)
    ·
      refine ⟨284885400095728410689260211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189923600063818940459506807 284885400095728410689260211)
      ·
        refine ⟨427328100143592616033890317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284885400095728410689260211 427328100143592616033890317)
        ·
          refine ⟨160248037553847231012708869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 427328100143592616033890317 160248037553847231012708869)
          ·
            refine ⟨30046507041346355814882913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 160248037553847231012708869 30046507041346355814882913)
            ·
              refine ⟨22534880281009766861162185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30046507041346355814882913 22534880281009766861162185)
              ·
                refine ⟨16901160210757325145871639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22534880281009766861162185 16901160210757325145871639)
                ·
                  refine ⟨25351740316135987718807459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16901160210757325145871639 25351740316135987718807459)
                  ·
                    refine ⟨38027610474203981578211189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25351740316135987718807459 38027610474203981578211189)
                    ·
                      refine ⟨3565088481956623272957299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38027610474203981578211189 3565088481956623272957299)
                      ·
                        rfl

theorem cell23_6942985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 2, 1, 1, 5].length) (baseStart_6942985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6942985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6942985 prefixEnd_6942985 := by exact prefixLift 6942985
  have htrace : WordTrace (prefixWord ++ tailWord_6942985) baseStart_6942985 baseEnd_6942985 := by
    simpa [prefixWord, tailWord_6942985, baseEnd_6942985] using wordTrace_append hprefix tailTrace_6942985
  have hstable : (prefixWord ++ tailWord_6942985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6942985).length < 2 ^ (prefixWord ++ tailWord_6942985).sum := by decide
  have hdescent : baseEnd_6942985 < baseStart_6942985 := by decide
  rcases family_descends (prefixWord ++ tailWord_6942985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6942999 : List Nat := [1, 1, 3, 4, 1, 4, 1, 2, 1, 1, 4]
def baseStart_6942999 : Nat := 118140960795 + 6942999 * 2 ^ 59
def prefixEnd_6942999 : Nat := 4983230072969 + 3 ^ 40 * 6942999 * 2
def baseEnd_6942999 : Nat := 3565095670685786218182235

theorem tailTrace_6942999 : CollatzResearch.WordTrace tailWord_6942999 prefixEnd_6942999 3565095670685786218182235 := by
  unfold tailWord_6942999
  simp only [CollatzResearch.WordTrace]
  refine ⟨253231977373707867670352051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168821318249138578446901367 253231977373707867670352051)
  ·
    refine ⟨379847966060561801505528077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253231977373707867670352051 379847966060561801505528077)
    ·
      refine ⟨142442987272710675564573029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 379847966060561801505528077 142442987272710675564573029)
      ·
        refine ⟨26708060113633251668357443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 142442987272710675564573029 26708060113633251668357443)
        ·
          refine ⟨40062090170449877502536165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26708060113633251668357443 40062090170449877502536165)
          ·
            refine ⟨7511641906959352031725531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40062090170449877502536165 7511641906959352031725531)
            ·
              refine ⟨11267462860439028047588297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7511641906959352031725531 11267462860439028047588297)
              ·
                refine ⟨8450597145329271035691223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11267462860439028047588297 8450597145329271035691223)
                ·
                  refine ⟨12675895717993906553536835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8450597145329271035691223 12675895717993906553536835)
                  ·
                    refine ⟨19013843576990859830305253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12675895717993906553536835 19013843576990859830305253)
                    ·
                      refine ⟨3565095670685786218182235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19013843576990859830305253 3565095670685786218182235)
                      ·
                        rfl

theorem cell23_6942999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 1, 2, 1, 1, 4].length) (baseStart_6942999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6942999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6942999 prefixEnd_6942999 := by exact prefixLift 6942999
  have htrace : WordTrace (prefixWord ++ tailWord_6942999) baseStart_6942999 baseEnd_6942999 := by
    simpa [prefixWord, tailWord_6942999, baseEnd_6942999] using wordTrace_append hprefix tailTrace_6942999
  have hstable : (prefixWord ++ tailWord_6942999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6942999).length < 2 ^ (prefixWord ++ tailWord_6942999).sum := by decide
  have hdescent : baseEnd_6942999 < baseStart_6942999 := by decide
  rcases family_descends (prefixWord ++ tailWord_6942999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6943012 : List Nat := [2, 3, 1, 3, 1, 3, 1, 2, 1, 2, 4]
def baseStart_6943012 : Nat := 118140960795 + 6943012 * 2 ^ 59
def prefixEnd_6943012 : Nat := 4983230072969 + 3 ^ 40 * 6943012 * 2
def baseEnd_6943012 : Nat := 3565102345934294667319675

theorem tailTrace_6943012 : CollatzResearch.WordTrace tailWord_6943012 prefixEnd_6943012 3565102345934294667319675 := by
  unfold tailWord_6943012
  simp only [CollatzResearch.WordTrace]
  refine ⟨126616225761330385445287645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168821634348440513927050193 126616225761330385445287645)
  ·
    refine ⟨47481084660498894541982867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126616225761330385445287645 47481084660498894541982867)
    ·
      refine ⟨71221626990748341812974301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47481084660498894541982867 71221626990748341812974301)
      ·
        refine ⟨26708110121530628179865363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71221626990748341812974301 26708110121530628179865363)
        ·
          refine ⟨40062165182295942269798045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26708110121530628179865363 40062165182295942269798045)
          ·
            refine ⟨15023311943360978351174267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40062165182295942269798045 15023311943360978351174267)
            ·
              refine ⟨22534967915041467526761401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15023311943360978351174267 22534967915041467526761401)
              ·
                refine ⟨16901225936281100645071051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22534967915041467526761401 16901225936281100645071051)
                ·
                  refine ⟨25351838904421650967606577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16901225936281100645071051 25351838904421650967606577)
                  ·
                    refine ⟨19013879178316238225704933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25351838904421650967606577 19013879178316238225704933)
                    ·
                      refine ⟨3565102345934294667319675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19013879178316238225704933 3565102345934294667319675)
                      ·
                        rfl

theorem cell23_6943012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_6943012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6943012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6943012 prefixEnd_6943012 := by exact prefixLift 6943012
  have htrace : WordTrace (prefixWord ++ tailWord_6943012) baseStart_6943012 baseEnd_6943012 := by
    simpa [prefixWord, tailWord_6943012, baseEnd_6943012] using wordTrace_append hprefix tailTrace_6943012
  have hstable : (prefixWord ++ tailWord_6943012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6943012).length < 2 ^ (prefixWord ++ tailWord_6943012).sum := by decide
  have hdescent : baseEnd_6943012 < baseStart_6943012 := by decide
  rcases family_descends (prefixWord ++ tailWord_6943012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6943016 : List Nat := [2, 1, 5, 1, 3, 1, 3, 1, 1, 1, 4]
def baseStart_6943016 : Nat := 118140960795 + 6943016 * 2 ^ 59
def prefixEnd_6943016 : Nat := 4983230072969 + 3 ^ 40 * 6943016 * 2
def baseEnd_6943016 : Nat := 3565104399856912651669657

theorem tailTrace_6943016 : CollatzResearch.WordTrace tailWord_6943016 prefixEnd_6943016 3565104399856912651669657 := by
  unfold tailWord_6943016
  simp only [CollatzResearch.WordTrace]
  refine ⟨126616298707323139786860451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168821731609764186382480601 126616298707323139786860451)
  ·
    refine ⟨189924448060984709680290677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126616298707323139786860451 189924448060984709680290677)
    ·
      refine ⟨17805417005717316532527251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 189924448060984709680290677 17805417005717316532527251)
      ·
        refine ⟨26708125508575974798790877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17805417005717316532527251 26708125508575974798790877)
        ·
          refine ⟨10015547065715990549546579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26708125508575974798790877 10015547065715990549546579)
          ·
            refine ⟨15023320598573985824319869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10015547065715990549546579 15023320598573985824319869)
            ·
              refine ⟨5633745224465244684119951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15023320598573985824319869 5633745224465244684119951)
              ·
                refine ⟨8450617836697867026179927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5633745224465244684119951 8450617836697867026179927)
                ·
                  refine ⟨12675926755046800539269891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8450617836697867026179927 12675926755046800539269891)
                  ·
                    refine ⟨19013890132570200808904837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12675926755046800539269891 19013890132570200808904837)
                    ·
                      refine ⟨3565104399856912651669657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19013890132570200808904837 3565104399856912651669657)
                      ·
                        rfl

theorem cell23_6943016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 3, 1, 1, 1, 4].length) (baseStart_6943016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6943016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6943016 prefixEnd_6943016 := by exact prefixLift 6943016
  have htrace : WordTrace (prefixWord ++ tailWord_6943016) baseStart_6943016 baseEnd_6943016 := by
    simpa [prefixWord, tailWord_6943016, baseEnd_6943016] using wordTrace_append hprefix tailTrace_6943016
  have hstable : (prefixWord ++ tailWord_6943016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6943016).length < 2 ^ (prefixWord ++ tailWord_6943016).sum := by decide
  have hdescent : baseEnd_6943016 < baseStart_6943016 := by decide
  rcases family_descends (prefixWord ++ tailWord_6943016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6943022 : List Nat := [4, 1, 3, 3, 1, 11]
def baseStart_6943022 : Nat := 118140960795 + 6943022 * 2 ^ 59
def prefixEnd_6943022 : Nat := 4983230072969 + 3 ^ 40 * 6943022 * 2
def baseEnd_6943022 : Nat := 14671224200579586947303

theorem tailTrace_6943022 : CollatzResearch.WordTrace tailWord_6943022 prefixEnd_6943022 14671224200579586947303 := by
  unfold tailWord_6943022
  simp only [CollatzResearch.WordTrace]
  refine ⟨31654102031578067824804915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168821877501749695065626213 31654102031578067824804915)
  ·
    refine ⟨47481153047367101737207373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31654102031578067824804915 47481153047367101737207373)
    ·
      refine ⟨17805432392762663151452765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47481153047367101737207373 17805432392762663151452765)
      ·
        refine ⟨6677037147285998681794787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17805432392762663151452765 6677037147285998681794787)
        ·
          refine ⟨10015555720928998022692181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6677037147285998681794787 10015555720928998022692181)
          ·
            refine ⟨14671224200579586947303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 10015555720928998022692181 14671224200579586947303)
            ·
              rfl

theorem cell23_6943022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 11].length) (baseStart_6943022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6943022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6943022 prefixEnd_6943022 := by exact prefixLift 6943022
  have htrace : WordTrace (prefixWord ++ tailWord_6943022) baseStart_6943022 baseEnd_6943022 := by
    simpa [prefixWord, tailWord_6943022, baseEnd_6943022] using wordTrace_append hprefix tailTrace_6943022
  have hstable : (prefixWord ++ tailWord_6943022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6943022).length < 2 ^ (prefixWord ++ tailWord_6943022).sum := by decide
  have hdescent : baseEnd_6943022 < baseStart_6943022 := by decide
  rcases family_descends (prefixWord ++ tailWord_6943022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6943032 : List Nat := [2, 1, 2, 1, 3, 1, 2, 3, 4, 1, 3]
def baseStart_6943032 : Nat := 118140960795 + 6943032 * 2 ^ 59
def prefixEnd_6943032 : Nat := 4983230072969 + 3 ^ 40 * 6943032 * 2
def baseEnd_6943032 : Nat := 3565112615547384589069583

theorem tailTrace_6943032 : CollatzResearch.WordTrace tailWord_6943032 prefixEnd_6943032 3565112615547384589069583 := by
  unfold tailWord_6943032
  simp only [CollatzResearch.WordTrace]
  refine ⟨126616590491294157153151675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168822120655058876204202233 126616590491294157153151675)
  ·
    refine ⟨189924885736941235729727513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126616590491294157153151675 189924885736941235729727513)
    ·
      refine ⟨142443664302705926797295635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189924885736941235729727513 142443664302705926797295635)
      ·
        refine ⟨213665496454058890195943453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142443664302705926797295635 213665496454058890195943453)
        ·
          refine ⟨80124561170272083823478795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 213665496454058890195943453 80124561170272083823478795)
          ·
            refine ⟨120186841755408125735218193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80124561170272083823478795 120186841755408125735218193)
            ·
              refine ⟨90140131316556094301413645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120186841755408125735218193 90140131316556094301413645)
              ·
                refine ⟨33802549243708535363030117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90140131316556094301413645 33802549243708535363030117)
                ·
                  refine ⟨6337977983195350380568147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33802549243708535363030117 6337977983195350380568147)
                  ·
                    refine ⟨9506966974793025570852221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6337977983195350380568147 9506966974793025570852221)
                    ·
                      refine ⟨3565112615547384589069583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9506966974793025570852221 3565112615547384589069583)
                      ·
                        rfl

theorem cell23_6943032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 3, 4, 1, 3].length) (baseStart_6943032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6943032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6943032 prefixEnd_6943032 := by exact prefixLift 6943032
  have htrace : WordTrace (prefixWord ++ tailWord_6943032) baseStart_6943032 baseEnd_6943032 := by
    simpa [prefixWord, tailWord_6943032, baseEnd_6943032] using wordTrace_append hprefix tailTrace_6943032
  have hstable : (prefixWord ++ tailWord_6943032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6943032).length < 2 ^ (prefixWord ++ tailWord_6943032).sum := by decide
  have hdescent : baseEnd_6943032 < baseStart_6943032 := by decide
  rcases family_descends (prefixWord ++ tailWord_6943032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6943033 : List Nat := [1, 2, 1, 6, 1, 2, 1, 4, 1, 2, 2]
def baseStart_6943033 : Nat := 118140960795 + 6943033 * 2 ^ 59
def prefixEnd_6943033 : Nat := 4983230072969 + 3 ^ 40 * 6943033 * 2
def baseEnd_6943033 : Nat := 3565113129028039085157079

theorem tailTrace_6943033 : CollatzResearch.WordTrace tailWord_6943033 prefixEnd_6943033 3565113129028039085157079 := by
  unfold tailWord_6943033
  simp only [CollatzResearch.WordTrace]
  refine ⟨253233217455584691477089753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168822144970389794318059835 253233217455584691477089753)
  ·
    refine ⟨189924913091688518607817315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253233217455584691477089753 189924913091688518607817315)
    ·
      refine ⟨284887369637532777911725973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189924913091688518607817315 284887369637532777911725973)
      ·
        refine ⟨13354095451759348964612155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 284887369637532777911725973 13354095451759348964612155)
        ·
          refine ⟨20031143177639023446918233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13354095451759348964612155 20031143177639023446918233)
          ·
            refine ⟨15023357383229267585188675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20031143177639023446918233 15023357383229267585188675)
            ·
              refine ⟨22535036074843901377783013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15023357383229267585188675 22535036074843901377783013)
              ·
                refine ⟨4225319264033231508334315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22535036074843901377783013 4225319264033231508334315)
                ·
                  refine ⟨6337978896049847262501473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4225319264033231508334315 6337978896049847262501473)
                  ·
                    refine ⟨4753484172037385446876105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6337978896049847262501473 4753484172037385446876105)
                    ·
                      refine ⟨3565113129028039085157079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4753484172037385446876105 3565113129028039085157079)
                      ·
                        rfl

theorem cell23_6943033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 4, 1, 2, 2].length) (baseStart_6943033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6943033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6943033 prefixEnd_6943033 := by exact prefixLift 6943033
  have htrace : WordTrace (prefixWord ++ tailWord_6943033) baseStart_6943033 baseEnd_6943033 := by
    simpa [prefixWord, tailWord_6943033, baseEnd_6943033] using wordTrace_append hprefix tailTrace_6943033
  have hstable : (prefixWord ++ tailWord_6943033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6943033).length < 2 ^ (prefixWord ++ tailWord_6943033).sum := by decide
  have hdescent : baseEnd_6943033 < baseStart_6943033 := by decide
  rcases family_descends (prefixWord ++ tailWord_6943033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6943075 : List Nat := [1, 1, 1, 5, 2, 1, 2, 1, 1, 3, 5]
def baseStart_6943075 : Nat := 118140960795 + 6943075 * 2 ^ 59
def prefixEnd_6943075 : Nat := 4983230072969 + 3 ^ 40 * 6943075 * 2
def baseEnd_6943075 : Nat := 3565134695215527920831885

theorem tailTrace_6943075 : CollatzResearch.WordTrace tailWord_6943075 prefixEnd_6943075 3565134695215527920831885 := by
  unfold tailWord_6943075
  simp only [CollatzResearch.WordTrace]
  refine ⟨253234749321432532650118679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168823166214288355100079119 253234749321432532650118679)
  ·
    refine ⟨379852123982148798975178019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253234749321432532650118679 379852123982148798975178019)
    ·
      refine ⟨569778185973223198462767029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379852123982148798975178019 569778185973223198462767029)
      ·
        refine ⟨53416704934989674855884409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 569778185973223198462767029 53416704934989674855884409)
        ·
          refine ⟨40062528701242256141913307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53416704934989674855884409 40062528701242256141913307)
          ·
            refine ⟨60093793051863384212869961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40062528701242256141913307 60093793051863384212869961)
            ·
              refine ⟨45070344788897538159652471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60093793051863384212869961 45070344788897538159652471)
              ·
                refine ⟨67605517183346307239478707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45070344788897538159652471 67605517183346307239478707)
                ·
                  refine ⟨101408275775019460859218061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67605517183346307239478707 101408275775019460859218061)
                  ·
                    refine ⟨38028103415632297822206773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 101408275775019460859218061 38028103415632297822206773)
                    ·
                      refine ⟨3565134695215527920831885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38028103415632297822206773 3565134695215527920831885)
                      ·
                        rfl

theorem cell23_6943075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 1, 1, 3, 5].length) (baseStart_6943075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6943075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6943075 prefixEnd_6943075 := by exact prefixLift 6943075
  have htrace : WordTrace (prefixWord ++ tailWord_6943075) baseStart_6943075 baseEnd_6943075 := by
    simpa [prefixWord, tailWord_6943075, baseEnd_6943075] using wordTrace_append hprefix tailTrace_6943075
  have hstable : (prefixWord ++ tailWord_6943075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6943075).length < 2 ^ (prefixWord ++ tailWord_6943075).sum := by decide
  have hdescent : baseEnd_6943075 < baseStart_6943075 := by decide
  rcases family_descends (prefixWord ++ tailWord_6943075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6943082 : List Nat := [3, 1, 3, 3, 1, 1, 1, 2, 2, 6]
def baseStart_6943082 : Nat := 118140960795 + 6943082 * 2 ^ 59
def prefixEnd_6943082 : Nat := 4983230072969 + 3 ^ 40 * 6943082 * 2
def baseEnd_6943082 : Nat := 1188379429860036464481451

theorem tailTrace_6943082 : CollatzResearch.WordTrace tailWord_6943082 prefixEnd_6943082 1188379429860036464481451 := by
  unfold tailWord_6943082
  simp only [CollatzResearch.WordTrace]
  refine ⟨63308751158101793211405875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168823336421604781897082333 63308751158101793211405875)
  ·
    refine ⟨94963126737152689817108813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63308751158101793211405875 94963126737152689817108813)
    ·
      refine ⟨35611172526432258681415805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94963126737152689817108813 35611172526432258681415805)
      ·
        refine ⟨13354189697412097005530927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35611172526432258681415805 13354189697412097005530927)
        ·
          refine ⟨20031284546118145508296391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13354189697412097005530927 20031284546118145508296391)
          ·
            refine ⟨30046926819177218262444587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20031284546118145508296391 30046926819177218262444587)
            ·
              refine ⟨45070390228765827393666881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30046926819177218262444587 45070390228765827393666881)
              ·
                refine ⟨33802792671574370545250161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45070390228765827393666881 33802792671574370545250161)
                ·
                  refine ⟨25352094503680777908937621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33802792671574370545250161 25352094503680777908937621)
                  ·
                    refine ⟨1188379429860036464481451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25352094503680777908937621 1188379429860036464481451)
                    ·
                      rfl

theorem cell23_6943082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 2, 2, 6].length) (baseStart_6943082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6943082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6943082 prefixEnd_6943082 := by exact prefixLift 6943082
  have htrace : WordTrace (prefixWord ++ tailWord_6943082) baseStart_6943082 baseEnd_6943082 := by
    simpa [prefixWord, tailWord_6943082, baseEnd_6943082] using wordTrace_append hprefix tailTrace_6943082
  have hstable : (prefixWord ++ tailWord_6943082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6943082).length < 2 ^ (prefixWord ++ tailWord_6943082).sum := by decide
  have hdescent : baseEnd_6943082 < baseStart_6943082 := by decide
  rcases family_descends (prefixWord ++ tailWord_6943082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6943157 : List Nat := [1, 3, 3, 2, 4, 1, 2, 1, 2, 2, 2]
def baseStart_6943157 : Nat := 118140960795 + 6943157 * 2 ^ 59
def prefixEnd_6943157 : Nat := 4983230072969 + 3 ^ 40 * 6943157 * 2
def baseEnd_6943157 : Nat := 3565176800629196600006509

theorem tailTrace_6943157 : CollatzResearch.WordTrace tailWord_6943157 prefixEnd_6943157 3565176800629196600006509 := by
  unfold tailWord_6943157
  simp only [CollatzResearch.WordTrace]
  refine ⟨253237740107135460654603725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168825160071423640436402483 253237740107135460654603725)
  ·
    refine ⟨94964152540175797745476397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 253237740107135460654603725 94964152540175797745476397)
    ·
      refine ⟨35611557202565924154553649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94964152540175797745476397 35611557202565924154553649)
      ·
        refine ⟨26708667901924443115915237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35611557202565924154553649 26708667901924443115915237)
        ·
          refine ⟨5007875231610833084234107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26708667901924443115915237 5007875231610833084234107)
          ·
            refine ⟨7511812847416249626351161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5007875231610833084234107 7511812847416249626351161)
            ·
              refine ⟨5633859635562187219763371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7511812847416249626351161 5633859635562187219763371)
              ·
                refine ⟨8450789453343280829645057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5633859635562187219763371 8450789453343280829645057)
                ·
                  refine ⟨6338092090007460622233793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8450789453343280829645057 6338092090007460622233793)
                  ·
                    refine ⟨4753569067505595466675345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6338092090007460622233793 4753569067505595466675345)
                    ·
                      refine ⟨3565176800629196600006509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4753569067505595466675345 3565176800629196600006509)
                      ·
                        rfl

theorem cell23_6943157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 2, 1, 2, 2, 2].length) (baseStart_6943157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6943157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6943157 prefixEnd_6943157 := by exact prefixLift 6943157
  have htrace : WordTrace (prefixWord ++ tailWord_6943157) baseStart_6943157 baseEnd_6943157 := by
    simpa [prefixWord, tailWord_6943157, baseEnd_6943157] using wordTrace_append hprefix tailTrace_6943157
  have hstable : (prefixWord ++ tailWord_6943157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6943157).length < 2 ^ (prefixWord ++ tailWord_6943157).sum := by decide
  have hdescent : baseEnd_6943157 < baseStart_6943157 := by decide
  rcases family_descends (prefixWord ++ tailWord_6943157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6943185 : List Nat := [1, 2, 2, 1, 2, 1, 1, 3, 10]
def baseStart_6943185 : Nat := 118140960795 + 6943185 * 2 ^ 59
def prefixEnd_6943185 : Nat := 4983230072969 + 3 ^ 40 * 6943185 * 2
def baseEnd_6943185 : Nat := 396132353120835832272931

theorem tailTrace_6943185 : CollatzResearch.WordTrace tailWord_6943185 prefixEnd_6943185 396132353120835832272931 := by
  unfold tailWord_6943185
  simp only [CollatzResearch.WordTrace]
  refine ⟨253238761351034021436623009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168825840900689347624415339 253238761351034021436623009)
  ·
    refine ⟨189929071013275516077467257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253238761351034021436623009 189929071013275516077467257)
    ·
      refine ⟨142446803259956637058100443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189929071013275516077467257 142446803259956637058100443)
      ·
        refine ⟨213670204889934955587150665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142446803259956637058100443 213670204889934955587150665)
        ·
          refine ⟨160252653667451216690362999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213670204889934955587150665 160252653667451216690362999)
          ·
            refine ⟨240378980501176825035544499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160252653667451216690362999 240378980501176825035544499)
            ·
              refine ⟨360568470751765237553316749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 240378980501176825035544499 360568470751765237553316749)
              ·
                refine ⟨135213176531911964082493781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 360568470751765237553316749 135213176531911964082493781)
                ·
                  refine ⟨396132353120835832272931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 135213176531911964082493781 396132353120835832272931)
                  ·
                    rfl

theorem cell23_6943185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 10].length) (baseStart_6943185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6943185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6943185 prefixEnd_6943185 := by exact prefixLift 6943185
  have htrace : WordTrace (prefixWord ++ tailWord_6943185) baseStart_6943185 baseEnd_6943185 := by
    simpa [prefixWord, tailWord_6943185, baseEnd_6943185] using wordTrace_append hprefix tailTrace_6943185
  have hstable : (prefixWord ++ tailWord_6943185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6943185).length < 2 ^ (prefixWord ++ tailWord_6943185).sum := by decide
  have hdescent : baseEnd_6943185 < baseStart_6943185 := by decide
  rcases family_descends (prefixWord ++ tailWord_6943185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6943199 : List Nat := [1, 1, 2, 3, 3, 2, 2, 2, 2, 2, 3]
def baseStart_6943199 : Nat := 118140960795 + 6943199 * 2 ^ 59
def prefixEnd_6943199 : Nat := 4983230072969 + 3 ^ 40 * 6943199 * 2
def baseEnd_6943199 : Nat := 3565198366816685435681315

theorem tailTrace_6943199 : CollatzResearch.WordTrace tailWord_6943199 prefixEnd_6943199 3565198366816685435681315 := by
  unfold tailWord_6943199
  simp only [CollatzResearch.WordTrace]
  refine ⟨253239271972983301827632651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168826181315322201218421767 253239271972983301827632651)
  ·
    refine ⟨379858907959474952741448977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253239271972983301827632651 379858907959474952741448977)
    ·
      refine ⟨284894180969606214556086733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 379858907959474952741448977 284894180969606214556086733)
      ·
        refine ⟨106835317863602330458532525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 284894180969606214556086733 106835317863602330458532525)
        ·
          refine ⟨40063244198850873921949697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106835317863602330458532525 40063244198850873921949697)
          ·
            refine ⟨30047433149138155441462273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40063244198850873921949697 30047433149138155441462273)
            ·
              refine ⟨22535574861853616581096705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30047433149138155441462273 22535574861853616581096705)
              ·
                refine ⟨16901681146390212435822529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22535574861853616581096705 16901681146390212435822529)
                ·
                  refine ⟨12676260859792659326866897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16901681146390212435822529 12676260859792659326866897)
                  ·
                    refine ⟨9507195644844494495150173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12676260859792659326866897 9507195644844494495150173)
                    ·
                      refine ⟨3565198366816685435681315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9507195644844494495150173 3565198366816685435681315)
                      ·
                        rfl

theorem cell23_6943199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 2, 2, 2, 3].length) (baseStart_6943199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6943199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6943199 prefixEnd_6943199 := by exact prefixLift 6943199
  have htrace : WordTrace (prefixWord ++ tailWord_6943199) baseStart_6943199 baseEnd_6943199 := by
    simpa [prefixWord, tailWord_6943199, baseEnd_6943199] using wordTrace_append hprefix tailTrace_6943199
  have hstable : (prefixWord ++ tailWord_6943199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6943199).length < 2 ^ (prefixWord ++ tailWord_6943199).sum := by decide
  have hdescent : baseEnd_6943199 < baseStart_6943199 := by decide
  rcases family_descends (prefixWord ++ tailWord_6943199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6943306 : List Nat := [3, 1, 2, 1, 1, 4, 2, 3, 1, 2, 3]
def baseStart_6943306 : Nat := 118140960795 + 6943306 * 2 ^ 59
def prefixEnd_6943306 : Nat := 4983230072969 + 3 ^ 40 * 6943306 * 2
def baseEnd_6943306 : Nat := 3565253309246716517043323

theorem tailTrace_6943306 : CollatzResearch.WordTrace tailWord_6943306 prefixEnd_6943306 3565253309246716517043323 := by
  unfold tailWord_6943306
  simp only [CollatzResearch.WordTrace]
  refine ⟨63310793645898914775444443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168828783055730439401185181 63310793645898914775444443)
  ·
    refine ⟨94966190468848372163166665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63310793645898914775444443 94966190468848372163166665)
    ·
      refine ⟨71224642851636279122374999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94966190468848372163166665 71224642851636279122374999)
      ·
        refine ⟨106836964277454418683562499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71224642851636279122374999 106836964277454418683562499)
        ·
          refine ⟨160255446416181628025343749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106836964277454418683562499 160255446416181628025343749)
          ·
            refine ⟨30047896203034055254751953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 160255446416181628025343749 30047896203034055254751953)
            ·
              refine ⟨22535922152275541441063965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30047896203034055254751953 22535922152275541441063965)
              ·
                refine ⟨8450970807103328040398987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22535922152275541441063965 8450970807103328040398987)
                ·
                  refine ⟨12676456210654992060598481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8450970807103328040398987 12676456210654992060598481)
                  ·
                    refine ⟨9507342157991244045448861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12676456210654992060598481 9507342157991244045448861)
                    ·
                      refine ⟨3565253309246716517043323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9507342157991244045448861 3565253309246716517043323)
                      ·
                        rfl

theorem cell23_6943306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 3, 1, 2, 3].length) (baseStart_6943306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6943306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6943306 prefixEnd_6943306 := by exact prefixLift 6943306
  have htrace : WordTrace (prefixWord ++ tailWord_6943306) baseStart_6943306 baseEnd_6943306 := by
    simpa [prefixWord, tailWord_6943306, baseEnd_6943306] using wordTrace_append hprefix tailTrace_6943306
  have hstable : (prefixWord ++ tailWord_6943306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6943306).length < 2 ^ (prefixWord ++ tailWord_6943306).sum := by decide
  have hdescent : baseEnd_6943306 < baseStart_6943306 := by decide
  rcases family_descends (prefixWord ++ tailWord_6943306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6943309 : List Nat := [1, 6, 1, 1, 2, 1, 11]
def baseStart_6943309 : Nat := 118140960795 + 6943309 * 2 ^ 59
def prefixEnd_6943309 : Nat := 4983230072969 + 3 ^ 40 * 6943309 * 2
def baseEnd_6943309 : Nat := 44015491971465185250689

theorem tailTrace_6943309 : CollatzResearch.WordTrace tailWord_6943309 prefixEnd_6943309 44015491971465185250689 := by
  unfold tailWord_6943309
  simp only [CollatzResearch.WordTrace]
  refine ⟨253243284002584790614136981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168828856001723193742757987 253243284002584790614136981)
  ·
    refine ⟨11870778937621162060037671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 253243284002584790614136981 11870778937621162060037671)
    ·
      refine ⟨17806168406431743090056507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11870778937621162060037671 17806168406431743090056507)
      ·
        refine ⟨26709252609647614635084761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17806168406431743090056507 26709252609647614635084761)
        ·
          refine ⟨20031939457235710976313571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26709252609647614635084761 20031939457235710976313571)
          ·
            refine ⟨30047909185853566464470357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20031939457235710976313571 30047909185853566464470357)
            ·
              refine ⟨44015491971465185250689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 30047909185853566464470357 44015491971465185250689)
              ·
                rfl

theorem cell23_6943309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 11].length) (baseStart_6943309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6943309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6943309 prefixEnd_6943309 := by exact prefixLift 6943309
  have htrace : WordTrace (prefixWord ++ tailWord_6943309) baseStart_6943309 baseEnd_6943309 := by
    simpa [prefixWord, tailWord_6943309, baseEnd_6943309] using wordTrace_append hprefix tailTrace_6943309
  have hstable : (prefixWord ++ tailWord_6943309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6943309).length < 2 ^ (prefixWord ++ tailWord_6943309).sum := by decide
  have hdescent : baseEnd_6943309 < baseStart_6943309 := by decide
  rcases family_descends (prefixWord ++ tailWord_6943309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6943330 : List Nat := [3, 3, 2, 3, 1, 1, 1, 3, 2, 4]
def baseStart_6943330 : Nat := 118140960795 + 6943330 * 2 ^ 59
def prefixEnd_6943330 : Nat := 4983230072969 + 3 ^ 40 * 6943330 * 2
def baseEnd_6943330 : Nat := 1188421877594141474381071

theorem tailTrace_6943330 : CollatzResearch.WordTrace tailWord_6943330 prefixEnd_6943330 1188421877594141474381071 := by
  unfold tailWord_6943330
  simp only [CollatzResearch.WordTrace]
  refine ⟨63311012483877177800162861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168829366623672474133767629 63311012483877177800162861)
  ·
    refine ⟨23741629681453941675061073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63311012483877177800162861 23741629681453941675061073)
    ·
      refine ⟨17806222261090456256295805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23741629681453941675061073 17806222261090456256295805)
      ·
        refine ⟨6677333347908921096110927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17806222261090456256295805 6677333347908921096110927)
        ·
          refine ⟨10016000021863381644166391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6677333347908921096110927 10016000021863381644166391)
          ·
            refine ⟨15024000032795072466249587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10016000021863381644166391 15024000032795072466249587)
            ·
              refine ⟨22536000049192608699374381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15024000032795072466249587 22536000049192608699374381)
              ·
                refine ⟨8451000018447228262265393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22536000049192608699374381 8451000018447228262265393)
                ·
                  refine ⟨6338250013835421196699045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8451000018447228262265393 6338250013835421196699045)
                  ·
                    refine ⟨1188421877594141474381071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6338250013835421196699045 1188421877594141474381071)
                    ·
                      rfl

theorem cell23_6943330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 3, 2, 4].length) (baseStart_6943330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6943330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6943330 prefixEnd_6943330 := by exact prefixLift 6943330
  have htrace : WordTrace (prefixWord ++ tailWord_6943330) baseStart_6943330 baseEnd_6943330 := by
    simpa [prefixWord, tailWord_6943330, baseEnd_6943330] using wordTrace_append hprefix tailTrace_6943330
  have hstable : (prefixWord ++ tailWord_6943330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6943330).length < 2 ^ (prefixWord ++ tailWord_6943330).sum := by decide
  have hdescent : baseEnd_6943330 < baseStart_6943330 := by decide
  rcases family_descends (prefixWord ++ tailWord_6943330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6943352 : List Nat := [2, 1, 2, 1, 1, 1, 2, 4, 1, 8]
def baseStart_6943352 : Nat := 118140960795 + 6943352 * 2 ^ 59
def prefixEnd_6943352 : Nat := 4983230072969 + 3 ^ 40 * 6943352 * 2
def baseEnd_6943352 : Nat := 1188425643118941112356037

theorem tailTrace_6943352 : CollatzResearch.WordTrace tailWord_6943352 prefixEnd_6943352 1188425643118941112356037 := by
  unfold tailWord_6943352
  simp only [CollatzResearch.WordTrace]
  refine ⟨126622426170714504478976155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168829901560952672638634873 126622426170714504478976155)
  ·
    refine ⟨189933639256071756718464233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126622426170714504478976155 189933639256071756718464233)
    ·
      refine ⟨142450229442053817538848175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189933639256071756718464233 142450229442053817538848175)
      ·
        refine ⟨213675344163080726308272263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142450229442053817538848175 213675344163080726308272263)
        ·
          refine ⟨320513016244621089462408395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213675344163080726308272263 320513016244621089462408395)
          ·
            refine ⟨480769524366931634193612593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 320513016244621089462408395 480769524366931634193612593)
            ·
              refine ⟨360577143275198725645209445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 480769524366931634193612593 360577143275198725645209445)
              ·
                refine ⟨67608214364099761058476771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 360577143275198725645209445 67608214364099761058476771)
                ·
                  refine ⟨101412321546149641587715157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67608214364099761058476771 101412321546149641587715157)
                  ·
                    refine ⟨1188425643118941112356037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 101412321546149641587715157 1188425643118941112356037)
                    ·
                      rfl

theorem cell23_6943352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 1, 8].length) (baseStart_6943352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6943352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6943352 prefixEnd_6943352 := by exact prefixLift 6943352
  have htrace : WordTrace (prefixWord ++ tailWord_6943352) baseStart_6943352 baseEnd_6943352 := by
    simpa [prefixWord, tailWord_6943352, baseEnd_6943352] using wordTrace_append hprefix tailTrace_6943352
  have hstable : (prefixWord ++ tailWord_6943352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6943352).length < 2 ^ (prefixWord ++ tailWord_6943352).sum := by decide
  have hdescent : baseEnd_6943352 < baseStart_6943352 := by decide
  rcases family_descends (prefixWord ++ tailWord_6943352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6943370 : List Nat := [3, 1, 2, 3, 3, 1, 2, 2, 2, 1, 3]
def baseStart_6943370 : Nat := 118140960795 + 6943370 * 2 ^ 59
def prefixEnd_6943370 : Nat := 4983230072969 + 3 ^ 40 * 6943370 * 2
def baseEnd_6943370 : Nat := 3565286172008604266643029

theorem tailTrace_6943370 : CollatzResearch.WordTrace tailWord_6943370 prefixEnd_6943370 3565286172008604266643029 := by
  unfold tailWord_6943370
  simp only [CollatzResearch.WordTrace]
  refine ⟨63311377213840949508026891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168830339236909198688071709 63311377213840949508026891)
  ·
    refine ⟨94967065820761424262040337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63311377213840949508026891 94967065820761424262040337)
    ·
      refine ⟨71225299365571068196530253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94967065820761424262040337 71225299365571068196530253)
      ·
        refine ⟨26709487262089150573698845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71225299365571068196530253 26709487262089150573698845)
        ·
          refine ⟨10016057723283431465137067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26709487262089150573698845 10016057723283431465137067)
          ·
            refine ⟨15024086584925147197705601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10016057723283431465137067 15024086584925147197705601)
            ·
              refine ⟨11268064938693860398279201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15024086584925147197705601 11268064938693860398279201)
              ·
                refine ⟨8451048704020395298709401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11268064938693860398279201 8451048704020395298709401)
                ·
                  refine ⟨6338286528015296474032051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8451048704020395298709401 6338286528015296474032051)
                  ·
                    refine ⟨9507429792022944711048077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6338286528015296474032051 9507429792022944711048077)
                    ·
                      refine ⟨3565286172008604266643029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9507429792022944711048077 3565286172008604266643029)
                      ·
                        rfl

theorem cell23_6943370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 2, 2, 2, 1, 3].length) (baseStart_6943370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6943370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6943370 prefixEnd_6943370 := by exact prefixLift 6943370
  have htrace : WordTrace (prefixWord ++ tailWord_6943370) baseStart_6943370 baseEnd_6943370 := by
    simpa [prefixWord, tailWord_6943370, baseEnd_6943370] using wordTrace_append hprefix tailTrace_6943370
  have hstable : (prefixWord ++ tailWord_6943370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6943370).length < 2 ^ (prefixWord ++ tailWord_6943370).sum := by decide
  have hdescent : baseEnd_6943370 < baseStart_6943370 := by decide
  rcases family_descends (prefixWord ++ tailWord_6943370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6943389 : List Nat := [1, 4, 2, 1, 1, 1, 3, 1, 1, 4, 4]
def baseStart_6943389 : Nat := 118140960795 + 6943389 * 2 ^ 59
def prefixEnd_6943389 : Nat := 4983230072969 + 3 ^ 40 * 6943389 * 2
def baseEnd_6943389 : Nat := 3565295928141039692305441

theorem tailTrace_6943389 : CollatzResearch.WordTrace tailWord_6943389 prefixEnd_6943389 3565295928141039692305441 := by
  unfold tailWord_6943389
  simp only [CollatzResearch.WordTrace]
  refine ⟨253246201842294964277049221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168830801228196642851366147 253246201842294964277049221)
  ·
    refine ⟨47483662845430305801946729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 253246201842294964277049221 47483662845430305801946729)
    ·
      refine ⟨35612747134072729351460047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47483662845430305801946729 35612747134072729351460047)
      ·
        refine ⟨53419120701109094027190071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35612747134072729351460047 53419120701109094027190071)
        ·
          refine ⟨80128681051663641040785107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53419120701109094027190071 80128681051663641040785107)
          ·
            refine ⟨120193021577495461561177661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80128681051663641040785107 120193021577495461561177661)
            ·
              refine ⟨45072383091560798085441623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120193021577495461561177661 45072383091560798085441623)
              ·
                refine ⟨67608574637341197128162435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45072383091560798085441623 67608574637341197128162435)
                ·
                  refine ⟨101412861956011795692243653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67608574637341197128162435 101412861956011795692243653)
                  ·
                    refine ⟨19014911616752211692295685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 101412861956011795692243653 19014911616752211692295685)
                    ·
                      refine ⟨3565295928141039692305441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19014911616752211692295685 3565295928141039692305441)
                      ·
                        rfl

theorem cell23_6943389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 1, 1, 4, 4].length) (baseStart_6943389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6943389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6943389 prefixEnd_6943389 := by exact prefixLift 6943389
  have htrace : WordTrace (prefixWord ++ tailWord_6943389) baseStart_6943389 baseEnd_6943389 := by
    simpa [prefixWord, tailWord_6943389, baseEnd_6943389] using wordTrace_append hprefix tailTrace_6943389
  have hstable : (prefixWord ++ tailWord_6943389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6943389).length < 2 ^ (prefixWord ++ tailWord_6943389).sum := by decide
  have hdescent : baseEnd_6943389 < baseStart_6943389 := by decide
  rcases family_descends (prefixWord ++ tailWord_6943389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
