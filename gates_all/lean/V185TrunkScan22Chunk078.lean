import V185TrunkScan22Chunk077

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_701505 : List Nat := [1, 2, 5, 1, 3, 1, 2, 3, 4]
def baseStart_701505 : Nat := 118140960795 + 701505 * 2 ^ 59
def prefixEnd_701505 : Nat := 4983230072969 + 3 ^ 40 * 701505 * 2
def baseEnd_701505 : Nat := 80046499229418464924743

theorem tailTrace_701505 : CollatzResearch.WordTrace tailWord_701505 prefixEnd_701505 80046499229418464924743 := by
  unfold tailWord_701505
  simp only [CollatzResearch.WordTrace]
  refine ⟨25585989323574667360745969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17057326215716444907163979 25585989323574667360745969)
  ·
    refine ⟨19189491992681000520559477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25585989323574667360745969 19189491992681000520559477)
    ·
      refine ⟨1799014874313843798802451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19189491992681000520559477 1799014874313843798802451)
      ·
        refine ⟨2698522311470765698203677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1799014874313843798802451 2698522311470765698203677)
        ·
          refine ⟨1011945866801537136826379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2698522311470765698203677 1011945866801537136826379)
          ·
            refine ⟨1517918800202305705239569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1011945866801537136826379 1517918800202305705239569)
            ·
              refine ⟨1138439100151729278929677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1517918800202305705239569 1138439100151729278929677)
              ·
                refine ⟨426914662556898479598629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1138439100151729278929677 426914662556898479598629)
                ·
                  refine ⟨80046499229418464924743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 426914662556898479598629 80046499229418464924743)
                  ·
                    rfl

theorem cell22_701505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 2, 3, 4].length) (baseStart_701505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_701505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_701505 prefixEnd_701505 := by exact prefixLift 701505
  have htrace : WordTrace (prefixWord ++ tailWord_701505) baseStart_701505 baseEnd_701505 := by
    simpa [prefixWord, tailWord_701505, baseEnd_701505] using wordTrace_append hprefix tailTrace_701505
  have hstable : (prefixWord ++ tailWord_701505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701505).length < 2 ^ (prefixWord ++ tailWord_701505).sum := by decide
  have hdescent : baseEnd_701505 < baseStart_701505 := by decide
  rcases family_descends (prefixWord ++ tailWord_701505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701529 : List Nat := [1, 2, 1, 2, 2, 1, 2, 3, 2, 6]
def baseStart_701529 : Nat := 118140960795 + 701529 * 2 ^ 59
def prefixEnd_701529 : Nat := 4983230072969 + 3 ^ 40 * 701529 * 2
def baseEnd_701529 : Nat := 240147713378727332174155

theorem tailTrace_701529 : CollatzResearch.WordTrace tailWord_701529 prefixEnd_701529 240147713378727332174155 := by
  unfold tailWord_701529
  simp only [CollatzResearch.WordTrace]
  refine ⟨25586864675487719459619641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17057909783658479639746427 25586864675487719459619641)
  ·
    refine ⟨19190148506615789594714731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25586864675487719459619641 19190148506615789594714731)
    ·
      refine ⟨28785222759923684392072097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19190148506615789594714731 28785222759923684392072097)
      ·
        refine ⟨21588917069942763294054073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28785222759923684392072097 21588917069942763294054073)
        ·
          refine ⟨16191687802457072470540555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21588917069942763294054073 16191687802457072470540555)
          ·
            refine ⟨24287531703685608705810833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16191687802457072470540555 24287531703685608705810833)
            ·
              refine ⟨18215648777764206529358125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24287531703685608705810833 18215648777764206529358125)
              ·
                refine ⟨6830868291661577448509297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18215648777764206529358125 6830868291661577448509297)
                ·
                  refine ⟨5123151218746183086381973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6830868291661577448509297 5123151218746183086381973)
                  ·
                    refine ⟨240147713378727332174155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5123151218746183086381973 240147713378727332174155)
                    ·
                      rfl

theorem cell22_701529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 3, 2, 6].length) (baseStart_701529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_701529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_701529 prefixEnd_701529 := by exact prefixLift 701529
  have htrace : WordTrace (prefixWord ++ tailWord_701529) baseStart_701529 baseEnd_701529 := by
    simpa [prefixWord, tailWord_701529, baseEnd_701529] using wordTrace_append hprefix tailTrace_701529
  have hstable : (prefixWord ++ tailWord_701529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701529).length < 2 ^ (prefixWord ++ tailWord_701529).sum := by decide
  have hdescent : baseEnd_701529 < baseStart_701529 := by decide
  rcases family_descends (prefixWord ++ tailWord_701529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701623 : List Nat := [1, 1, 3, 1, 4, 1, 2, 5, 4]
def baseStart_701623 : Nat := 118140960795 + 701623 * 2 ^ 59
def prefixEnd_701623 : Nat := 4983230072969 + 3 ^ 40 * 701623 * 2
def baseEnd_701623 : Nat := 80059963833247473441289

theorem tailTrace_701623 : CollatzResearch.WordTrace tailWord_701623 prefixEnd_701623 80059963833247473441289 := by
  unfold tailWord_701623
  simp only [CollatzResearch.WordTrace]
  refine ⟨25590293137147173513541523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17060195424764782342361015 25590293137147173513541523)
  ·
    refine ⟨38385439705720760270312285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25590293137147173513541523 38385439705720760270312285)
    ·
      refine ⟨14394539889645285101367107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38385439705720760270312285 14394539889645285101367107)
      ·
        refine ⟨21591809834467927652050661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14394539889645285101367107 21591809834467927652050661)
        ·
          refine ⟨4048464343962736434759499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21591809834467927652050661 4048464343962736434759499)
          ·
            refine ⟨6072696515944104652139249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4048464343962736434759499 6072696515944104652139249)
            ·
              refine ⟨4554522386958078489104437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6072696515944104652139249 4554522386958078489104437)
              ·
                refine ⟨426986473777319858353541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4554522386958078489104437 426986473777319858353541)
                ·
                  refine ⟨80059963833247473441289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 426986473777319858353541 80059963833247473441289)
                  ·
                    rfl

theorem cell22_701623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 5, 4].length) (baseStart_701623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_701623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_701623 prefixEnd_701623 := by exact prefixLift 701623
  have htrace : WordTrace (prefixWord ++ tailWord_701623) baseStart_701623 baseEnd_701623 := by
    simpa [prefixWord, tailWord_701623, baseEnd_701623] using wordTrace_append hprefix tailTrace_701623
  have hstable : (prefixWord ++ tailWord_701623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701623).length < 2 ^ (prefixWord ++ tailWord_701623).sum := by decide
  have hdescent : baseEnd_701623 < baseStart_701623 := by decide
  rcases family_descends (prefixWord ++ tailWord_701623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701625 : List Nat := [1, 2, 1, 4, 1, 4, 3, 1, 1, 4]
def baseStart_701625 : Nat := 118140960795 + 701625 * 2 ^ 59
def prefixEnd_701625 : Nat := 4983230072969 + 3 ^ 40 * 701625 * 2
def baseEnd_701625 : Nat := 240180576140615081773861

theorem tailTrace_701625 : CollatzResearch.WordTrace tailWord_701625 prefixEnd_701625 240180576140615081773861 := by
  unfold tailWord_701625
  simp only [CollatzResearch.WordTrace]
  refine ⟨25590366083139927855114329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17060244055426618570076219 25590366083139927855114329)
  ·
    refine ⟨19192774562354945891335747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25590366083139927855114329 19192774562354945891335747)
    ·
      refine ⟨28789161843532418837003621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19192774562354945891335747 28789161843532418837003621)
      ·
        refine ⟨5397967845662328531938179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28789161843532418837003621 5397967845662328531938179)
        ·
          refine ⟨8096951768493492797907269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5397967845662328531938179 8096951768493492797907269)
          ·
            refine ⟨1518178456592529899607613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8096951768493492797907269 1518178456592529899607613)
            ·
              refine ⟨569316921222198712352855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1518178456592529899607613 569316921222198712352855)
              ·
                refine ⟨853975381833298068529283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 569316921222198712352855 853975381833298068529283)
                ·
                  refine ⟨1280963072749947102793925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 853975381833298068529283 1280963072749947102793925)
                  ·
                    refine ⟨240180576140615081773861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1280963072749947102793925 240180576140615081773861)
                    ·
                      rfl

theorem cell22_701625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 3, 1, 1, 4].length) (baseStart_701625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_701625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_701625 prefixEnd_701625 := by exact prefixLift 701625
  have htrace : WordTrace (prefixWord ++ tailWord_701625) baseStart_701625 baseEnd_701625 := by
    simpa [prefixWord, tailWord_701625, baseEnd_701625] using wordTrace_append hprefix tailTrace_701625
  have hstable : (prefixWord ++ tailWord_701625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701625).length < 2 ^ (prefixWord ++ tailWord_701625).sum := by decide
  have hdescent : baseEnd_701625 < baseStart_701625 := by decide
  rcases family_descends (prefixWord ++ tailWord_701625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701640 : List Nat := [2, 1, 3, 1, 2, 1, 6, 2, 4]
def baseStart_701640 : Nat := 118140960795 + 701640 * 2 ^ 59
def prefixEnd_701640 : Nat := 4983230072969 + 3 ^ 40 * 701640 * 2
def baseEnd_701640 : Nat := 80061903649053347549605

theorem tailTrace_701640 : CollatzResearch.WordTrace tailWord_701640 prefixEnd_701640 80061903649053347549605 := by
  unfold tailWord_701640
  simp only [CollatzResearch.WordTrace]
  refine ⟨12795456589042792708455187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17060608785390390277940249 12795456589042792708455187)
  ·
    refine ⟨19193184883564189062682781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12795456589042792708455187 19193184883564189062682781)
    ·
      refine ⟨7197444331336570898506043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19193184883564189062682781 7197444331336570898506043)
      ·
        refine ⟨10796166497004856347759065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7197444331336570898506043 10796166497004856347759065)
        ·
          refine ⟨8097124872753642260819299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10796166497004856347759065 8097124872753642260819299)
          ·
            refine ⟨12145687309130463391228949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8097124872753642260819299 12145687309130463391228949)
            ·
              refine ⟨569329092615490471463857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 12145687309130463391228949 569329092615490471463857)
              ·
                refine ⟨426996819461617853597893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 569329092615490471463857 426996819461617853597893)
                ·
                  refine ⟨80061903649053347549605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 426996819461617853597893 80061903649053347549605)
                  ·
                    rfl

theorem cell22_701640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 6, 2, 4].length) (baseStart_701640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_701640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_701640 prefixEnd_701640 := by exact prefixLift 701640
  have htrace : WordTrace (prefixWord ++ tailWord_701640) baseStart_701640 baseEnd_701640 := by
    simpa [prefixWord, tailWord_701640, baseEnd_701640] using wordTrace_append hprefix tailTrace_701640
  have hstable : (prefixWord ++ tailWord_701640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701640).length < 2 ^ (prefixWord ++ tailWord_701640).sum := by decide
  have hdescent : baseEnd_701640 < baseStart_701640 := by decide
  rcases family_descends (prefixWord ++ tailWord_701640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701700 : List Nat := [2, 3, 2, 2, 2, 1, 1, 3, 3, 3]
def baseStart_701700 : Nat := 118140960795 + 701700 * 2 ^ 59
def prefixEnd_701700 : Nat := 4983230072969 + 3 ^ 40 * 701700 * 2
def baseEnd_701700 : Nat := 240206250173339886148631

theorem tailTrace_701700 : CollatzResearch.WordTrace tailWord_701700 prefixEnd_701700 240206250173339886148631 := by
  unfold tailWord_701700
  simp only [CollatzResearch.WordTrace]
  refine ⟨12796550778934107832047277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17062067705245477109396369 12796550778934107832047277)
  ·
    refine ⟨4798706542100290437017729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12796550778934107832047277 4798706542100290437017729)
    ·
      refine ⟨3599029906575217827763297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4798706542100290437017729 3599029906575217827763297)
      ·
        refine ⟨2699272429931413370822473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3599029906575217827763297 2699272429931413370822473)
        ·
          refine ⟨2024454322448560028116855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2699272429931413370822473 2024454322448560028116855)
          ·
            refine ⟨3036681483672840042175283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2024454322448560028116855 3036681483672840042175283)
            ·
              refine ⟨4555022225509260063262925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3036681483672840042175283 4555022225509260063262925)
              ·
                refine ⟨1708133334565972523723597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4555022225509260063262925 1708133334565972523723597)
                ·
                  refine ⟨640550000462239696396349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1708133334565972523723597 640550000462239696396349)
                  ·
                    refine ⟨240206250173339886148631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 640550000462239696396349 240206250173339886148631)
                    ·
                      rfl

theorem cell22_701700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 3, 3, 3].length) (baseStart_701700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_701700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_701700 prefixEnd_701700 := by exact prefixLift 701700
  have htrace : WordTrace (prefixWord ++ tailWord_701700) baseStart_701700 baseEnd_701700 := by
    simpa [prefixWord, tailWord_701700, baseEnd_701700] using wordTrace_append hprefix tailTrace_701700
  have hstable : (prefixWord ++ tailWord_701700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701700).length < 2 ^ (prefixWord ++ tailWord_701700).sum := by decide
  have hdescent : baseEnd_701700 < baseStart_701700 := by decide
  rcases family_descends (prefixWord ++ tailWord_701700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701764 : List Nat := [2, 3, 4, 1, 1, 3, 2, 1, 5]
def baseStart_701764 : Nat := 118140960795 + 701764 * 2 ^ 59
def prefixEnd_701764 : Nat := 4983230072969 + 3 ^ 40 * 701764 * 2
def baseEnd_701764 : Nat := 80076052893755017516145

theorem tailTrace_701764 : CollatzResearch.WordTrace tailWord_701764 prefixEnd_701764 80076052893755017516145 := by
  unfold tailWord_701764
  simp only [CollatzResearch.WordTrace]
  refine ⟨12797717914818177297212173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17063623886424236396282897 12797717914818177297212173)
  ·
    refine ⟨4799144218056816486454565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12797717914818177297212173 4799144218056816486454565)
    ·
      refine ⟨899839540885653091210231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4799144218056816486454565 899839540885653091210231)
      ·
        refine ⟨1349759311328479636815347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 899839540885653091210231 1349759311328479636815347)
        ·
          refine ⟨2024638966992719455223021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1349759311328479636815347 2024638966992719455223021)
          ·
            refine ⟨759239612622269795708633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2024638966992719455223021 759239612622269795708633)
            ·
              refine ⟨569429709466702346781475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 759239612622269795708633 569429709466702346781475)
              ·
                refine ⟨854144564200053520172213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 569429709466702346781475 854144564200053520172213)
                ·
                  refine ⟨80076052893755017516145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 854144564200053520172213 80076052893755017516145)
                  ·
                    rfl

theorem cell22_701764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 2, 1, 5].length) (baseStart_701764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_701764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_701764 prefixEnd_701764 := by exact prefixLift 701764
  have htrace : WordTrace (prefixWord ++ tailWord_701764) baseStart_701764 baseEnd_701764 := by
    simpa [prefixWord, tailWord_701764, baseEnd_701764] using wordTrace_append hprefix tailTrace_701764
  have hstable : (prefixWord ++ tailWord_701764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701764).length < 2 ^ (prefixWord ++ tailWord_701764).sum := by decide
  have hdescent : baseEnd_701764 < baseStart_701764 := by decide
  rcases family_descends (prefixWord ++ tailWord_701764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701805 : List Nat := [1, 5, 1, 1, 1, 3, 2, 2, 2, 4]
def baseStart_701805 : Nat := 118140960795 + 701805 * 2 ^ 59
def prefixEnd_701805 : Nat := 4983230072969 + 3 ^ 40 * 701805 * 2
def baseEnd_701805 : Nat := 240242193819154612273309

theorem tailTrace_701805 : CollatzResearch.WordTrace tailWord_701805 prefixEnd_701805 240242193819154612273309 := by
  unfold tailWord_701805
  simp only [CollatzResearch.WordTrace]
  refine ⟨25596931222487818596666869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17064620814991879064444579 25596931222487818596666869)
  ·
    refine ⟨2399712302108232993437519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25596931222487818596666869 2399712302108232993437519)
    ·
      refine ⟨3599568453162349490156279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2399712302108232993437519 3599568453162349490156279)
      ·
        refine ⟨5399352679743524235234419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3599568453162349490156279 5399352679743524235234419)
        ·
          refine ⟨8099029019615286352851629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5399352679743524235234419 8099029019615286352851629)
          ·
            refine ⟨3037135882355732382319361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8099029019615286352851629 3037135882355732382319361)
            ·
              refine ⟨2277851911766799286739521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3037135882355732382319361 2277851911766799286739521)
              ·
                refine ⟨1708388933825099465054641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2277851911766799286739521 1708388933825099465054641)
                ·
                  refine ⟨1281291700368824598790981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1708388933825099465054641 1281291700368824598790981)
                  ·
                    refine ⟨240242193819154612273309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1281291700368824598790981 240242193819154612273309)
                    ·
                      rfl

theorem cell22_701805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 2, 2, 4].length) (baseStart_701805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_701805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_701805 prefixEnd_701805 := by exact prefixLift 701805
  have htrace : WordTrace (prefixWord ++ tailWord_701805) baseStart_701805 baseEnd_701805 := by
    simpa [prefixWord, tailWord_701805, baseEnd_701805] using wordTrace_append hprefix tailTrace_701805
  have hstable : (prefixWord ++ tailWord_701805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701805).length < 2 ^ (prefixWord ++ tailWord_701805).sum := by decide
  have hdescent : baseEnd_701805 < baseStart_701805 := by decide
  rcases family_descends (prefixWord ++ tailWord_701805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701835 : List Nat := [1, 1, 1, 1, 4, 3, 3, 2, 3, 3]
def baseStart_701835 : Nat := 118140960795 + 701835 * 2 ^ 59
def prefixEnd_701835 : Nat := 4983230072969 + 3 ^ 40 * 701835 * 2
def baseEnd_701835 : Nat := 240252463432244534023217

theorem tailTrace_701835 : CollatzResearch.WordTrace tailWord_701835 prefixEnd_701835 240252463432244534023217 := by
  unfold tailWord_701835
  simp only [CollatzResearch.WordTrace]
  refine ⟨25598025412379133720258959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17065350274919422480172639 25598025412379133720258959)
  ·
    refine ⟨38397038118568700580388439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25598025412379133720258959 38397038118568700580388439)
    ·
      refine ⟨57595557177853050870582659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38397038118568700580388439 57595557177853050870582659)
      ·
        refine ⟨86393335766779576305873989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57595557177853050870582659 86393335766779576305873989)
        ·
          refine ⟨16198750456271170557351373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 86393335766779576305873989 16198750456271170557351373)
          ·
            refine ⟨6074531421101688959006765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16198750456271170557351373 6074531421101688959006765)
            ·
              refine ⟨2277949282913133359627537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6074531421101688959006765 2277949282913133359627537)
              ·
                refine ⟨1708461962184850019720653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2277949282913133359627537 1708461962184850019720653)
                ·
                  refine ⟨640673235819318757395245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1708461962184850019720653 640673235819318757395245)
                  ·
                    refine ⟨240252463432244534023217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 640673235819318757395245 240252463432244534023217)
                    ·
                      rfl

theorem cell22_701835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 2, 3, 3].length) (baseStart_701835 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_701835 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_701835 prefixEnd_701835 := by exact prefixLift 701835
  have htrace : WordTrace (prefixWord ++ tailWord_701835) baseStart_701835 baseEnd_701835 := by
    simpa [prefixWord, tailWord_701835, baseEnd_701835] using wordTrace_append hprefix tailTrace_701835
  have hstable : (prefixWord ++ tailWord_701835).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701835).length < 2 ^ (prefixWord ++ tailWord_701835).sum := by decide
  have hdescent : baseEnd_701835 < baseStart_701835 := by decide
  rcases family_descends (prefixWord ++ tailWord_701835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701869 : List Nat := [1, 5, 2, 2, 1, 2, 2, 1, 3, 3]
def baseStart_701869 : Nat := 118140960795 + 701869 * 2 ^ 59
def prefixEnd_701869 : Nat := 4983230072969 + 3 ^ 40 * 701869 * 2
def baseEnd_701869 : Nat := 240264102327079778673113

theorem tailTrace_701869 : CollatzResearch.WordTrace tailWord_701869 prefixEnd_701869 240264102327079778673113 := by
  unfold tailWord_701869
  simp only [CollatzResearch.WordTrace]
  refine ⟨25599265494255957526996661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17066176996170638351331107 25599265494255957526996661)
  ·
    refine ⟨2399931140086496018155937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25599265494255957526996661 2399931140086496018155937)
    ·
      refine ⟨1799948355064872013616953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2399931140086496018155937 1799948355064872013616953)
      ·
        refine ⟨1349961266298654010212715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1799948355064872013616953 1349961266298654010212715)
        ·
          refine ⟨2024941899447981015319073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1349961266298654010212715 2024941899447981015319073)
          ·
            refine ⟨1518706424585985761489305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2024941899447981015319073 1518706424585985761489305)
            ·
              refine ⟨1139029818439489321116979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1518706424585985761489305 1139029818439489321116979)
              ·
                refine ⟨1708544727659233981675469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1139029818439489321116979 1708544727659233981675469)
                ·
                  refine ⟨640704272872212743128301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1708544727659233981675469 640704272872212743128301)
                  ·
                    refine ⟨240264102327079778673113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 640704272872212743128301 240264102327079778673113)
                    ·
                      rfl

theorem cell22_701869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 2, 1, 3, 3].length) (baseStart_701869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_701869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_701869 prefixEnd_701869 := by exact prefixLift 701869
  have htrace : WordTrace (prefixWord ++ tailWord_701869) baseStart_701869 baseEnd_701869 := by
    simpa [prefixWord, tailWord_701869, baseEnd_701869] using wordTrace_append hprefix tailTrace_701869
  have hstable : (prefixWord ++ tailWord_701869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701869).length < 2 ^ (prefixWord ++ tailWord_701869).sum := by decide
  have hdescent : baseEnd_701869 < baseStart_701869 := by decide
  rcases family_descends (prefixWord ++ tailWord_701869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701927 : List Nat := [1, 1, 5, 2, 1, 4, 1, 1, 6]
def baseStart_701927 : Nat := 118140960795 + 701927 * 2 ^ 59
def prefixEnd_701927 : Nat := 4983230072969 + 3 ^ 40 * 701927 * 2
def baseEnd_701927 : Nat := 80094652304128986907645

theorem tailTrace_701927 : CollatzResearch.WordTrace tailWord_701927 prefixEnd_701927 80094652304128986907645 := by
  unfold tailWord_701927
  simp only [CollatzResearch.WordTrace]
  refine ⟨25601380928045833432608035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17067587285363888955072023 25601380928045833432608035)
  ·
    refine ⟨38402071392068750148912053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25601380928045833432608035 38402071392068750148912053)
    ·
      refine ⟨3600194193006445326460505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38402071392068750148912053 3600194193006445326460505)
      ·
        refine ⟨2700145644754833994845379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3600194193006445326460505 2700145644754833994845379)
        ·
          refine ⟨4050218467132250992268069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2700145644754833994845379 4050218467132250992268069)
          ·
            refine ⟨759415962587297061050263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4050218467132250992268069 759415962587297061050263)
            ·
              refine ⟨1139123943880945591575395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 759415962587297061050263 1139123943880945591575395)
              ·
                refine ⟨1708685915821418387363093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1139123943880945591575395 1708685915821418387363093)
                ·
                  refine ⟨80094652304128986907645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1708685915821418387363093 80094652304128986907645)
                  ·
                    rfl

theorem cell22_701927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 1, 1, 6].length) (baseStart_701927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_701927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_701927 prefixEnd_701927 := by exact prefixLift 701927
  have htrace : WordTrace (prefixWord ++ tailWord_701927) baseStart_701927 baseEnd_701927 := by
    simpa [prefixWord, tailWord_701927, baseEnd_701927] using wordTrace_append hprefix tailTrace_701927
  have hstable : (prefixWord ++ tailWord_701927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701927).length < 2 ^ (prefixWord ++ tailWord_701927).sum := by decide
  have hdescent : baseEnd_701927 < baseStart_701927 := by decide
  rcases family_descends (prefixWord ++ tailWord_701927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701972 : List Nat := [2, 4, 3, 1, 2, 10]
def baseStart_701972 : Nat := 118140960795 + 701972 * 2 ^ 59
def prefixEnd_701972 : Nat := 4983230072969 + 3 ^ 40 * 701972 * 2
def baseEnd_701972 : Nat := 2966658781876812880837

theorem tailTrace_701972 : CollatzResearch.WordTrace tailWord_701972 prefixEnd_701972 2966658781876812880837 := by
  unfold tailWord_701972
  simp only [CollatzResearch.WordTrace]
  refine ⟨12801511106441403058998085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17068681475255204078664113 12801511106441403058998085)
  ·
    refine ⟨2400283332457763073562141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12801511106441403058998085 2400283332457763073562141)
    ·
      refine ⟨900106249671661152585803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2400283332457763073562141 900106249671661152585803)
      ·
        refine ⟨1350159374507491728878705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 900106249671661152585803 1350159374507491728878705)
        ·
          refine ⟨1012619530880618796659029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1350159374507491728878705 1012619530880618796659029)
          ·
            refine ⟨2966658781876812880837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1012619530880618796659029 2966658781876812880837)
            ·
              rfl

theorem cell22_701972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 10].length) (baseStart_701972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_701972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_701972 prefixEnd_701972 := by exact prefixLift 701972
  have htrace : WordTrace (prefixWord ++ tailWord_701972) baseStart_701972 baseEnd_701972 := by
    simpa [prefixWord, tailWord_701972, baseEnd_701972] using wordTrace_append hprefix tailTrace_701972
  have hstable : (prefixWord ++ tailWord_701972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701972).length < 2 ^ (prefixWord ++ tailWord_701972).sum := by decide
  have hdescent : baseEnd_701972 < baseStart_701972 := by decide
  rcases family_descends (prefixWord ++ tailWord_701972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701985 : List Nat := [1, 2, 3, 2, 2, 2, 1, 1, 2, 6]
def baseStart_701985 : Nat := 118140960795 + 701985 * 2 ^ 59
def prefixEnd_701985 : Nat := 4983230072969 + 3 ^ 40 * 701985 * 2
def baseEnd_701985 : Nat := 240303811497694142772757

theorem tailTrace_701985 : CollatzResearch.WordTrace tailWord_701985 prefixEnd_701985 240303811497694142772757 := by
  unfold tailWord_701985
  simp only [CollatzResearch.WordTrace]
  refine ⟨25603496361835709338219409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17068997574557139558812939 25603496361835709338219409)
  ·
    refine ⟨19202622271376782003664557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25603496361835709338219409 19202622271376782003664557)
    ·
      refine ⟨7200983351766293251374209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19202622271376782003664557 7200983351766293251374209)
      ·
        refine ⟨5400737513824719938530657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7200983351766293251374209 5400737513824719938530657)
        ·
          refine ⟨4050553135368539953897993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5400737513824719938530657 4050553135368539953897993)
          ·
            refine ⟨3037914851526404965423495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4050553135368539953897993 3037914851526404965423495)
            ·
              refine ⟨4556872277289607448135243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3037914851526404965423495 4556872277289607448135243)
              ·
                refine ⟨6835308415934411172202865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4556872277289607448135243 6835308415934411172202865)
                ·
                  refine ⟨5126481311950808379152149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6835308415934411172202865 5126481311950808379152149)
                  ·
                    refine ⟨240303811497694142772757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5126481311950808379152149 240303811497694142772757)
                    ·
                      rfl

theorem cell22_701985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 1, 2, 6].length) (baseStart_701985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_701985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_701985 prefixEnd_701985 := by exact prefixLift 701985
  have htrace : WordTrace (prefixWord ++ tailWord_701985) baseStart_701985 baseEnd_701985 := by
    simpa [prefixWord, tailWord_701985, baseEnd_701985] using wordTrace_append hprefix tailTrace_701985
  have hstable : (prefixWord ++ tailWord_701985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701985).length < 2 ^ (prefixWord ++ tailWord_701985).sum := by decide
  have hdescent : baseEnd_701985 < baseStart_701985 := by decide
  rcases family_descends (prefixWord ++ tailWord_701985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702034 : List Nat := [3, 2, 2, 1, 2, 4, 1, 2, 5]
def baseStart_702034 : Nat := 118140960795 + 702034 * 2 ^ 59
def prefixEnd_702034 : Nat := 4983230072969 + 3 ^ 40 * 702034 * 2
def baseEnd_702034 : Nat := 80106861733024782765869

theorem tailTrace_702034 : CollatzResearch.WordTrace tailWord_702034 prefixEnd_702034 80106861733024782765869 := by
  unfold tailWord_702034
  simp only [CollatzResearch.WordTrace]
  refine ⟨6401320884664547676688289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17070189025772127137835437 6401320884664547676688289)
  ·
    refine ⟨4800990663498410757516217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6401320884664547676688289 4800990663498410757516217)
    ·
      refine ⟨3600742997623808068137163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4800990663498410757516217 3600742997623808068137163)
      ·
        refine ⟨5401114496435712102205745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3600742997623808068137163 5401114496435712102205745)
        ·
          refine ⟨4050835872326784076654309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5401114496435712102205745 4050835872326784076654309)
          ·
            refine ⟨759531726061272014372683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4050835872326784076654309 759531726061272014372683)
            ·
              refine ⟨1139297589091908021559025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 759531726061272014372683 1139297589091908021559025)
              ·
                refine ⟨854473191818931016169269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1139297589091908021559025 854473191818931016169269)
                ·
                  refine ⟨80106861733024782765869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 854473191818931016169269 80106861733024782765869)
                  ·
                    rfl

theorem cell22_702034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 1, 2, 5].length) (baseStart_702034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_702034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_702034 prefixEnd_702034 := by exact prefixLift 702034
  have htrace : WordTrace (prefixWord ++ tailWord_702034) baseStart_702034 baseEnd_702034 := by
    simpa [prefixWord, tailWord_702034, baseEnd_702034] using wordTrace_append hprefix tailTrace_702034
  have hstable : (prefixWord ++ tailWord_702034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702034).length < 2 ^ (prefixWord ++ tailWord_702034).sum := by decide
  have hdescent : baseEnd_702034 < baseStart_702034 := by decide
  rcases family_descends (prefixWord ++ tailWord_702034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702064 : List Nat := [2, 1, 1, 1, 6, 2, 2, 2, 1, 4]
def baseStart_702064 : Nat := 118140960795 + 702064 * 2 ^ 59
def prefixEnd_702064 : Nat := 4983230072969 + 3 ^ 40 * 702064 * 2
def baseEnd_702064 : Nat := 240330854812164270047515

theorem tailTrace_702064 : CollatzResearch.WordTrace tailWord_702064 prefixEnd_702064 240330854812164270047515 := by
  unfold tailWord_702064
  simp only [CollatzResearch.WordTrace]
  refine ⟨12803188864274752915172623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17070918485699670553563497 12803188864274752915172623)
  ·
    refine ⟨19204783296412129372758935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12803188864274752915172623 19204783296412129372758935)
    ·
      refine ⟨28807174944618194059138403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19204783296412129372758935 28807174944618194059138403)
      ·
        refine ⟨43210762416927291088707605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28807174944618194059138403 43210762416927291088707605)
        ·
          refine ⟨2025504488293466769783169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 43210762416927291088707605 2025504488293466769783169)
          ·
            refine ⟨1519128366220100077337377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2025504488293466769783169 1519128366220100077337377)
            ·
              refine ⟨1139346274665075058003033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1519128366220100077337377 1139346274665075058003033)
              ·
                refine ⟨854509705998806293502275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1139346274665075058003033 854509705998806293502275)
                ·
                  refine ⟨1281764558998209440253413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 854509705998806293502275 1281764558998209440253413)
                  ·
                    refine ⟨240330854812164270047515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1281764558998209440253413 240330854812164270047515)
                    ·
                      rfl

theorem cell22_702064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 2, 2, 1, 4].length) (baseStart_702064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_702064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_702064 prefixEnd_702064 := by exact prefixLift 702064
  have htrace : WordTrace (prefixWord ++ tailWord_702064) baseStart_702064 baseEnd_702064 := by
    simpa [prefixWord, tailWord_702064, baseEnd_702064] using wordTrace_append hprefix tailTrace_702064
  have hstable : (prefixWord ++ tailWord_702064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702064).length < 2 ^ (prefixWord ++ tailWord_702064).sum := by decide
  have hdescent : baseEnd_702064 < baseStart_702064 := by decide
  rcases family_descends (prefixWord ++ tailWord_702064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702075 : List Nat := [1, 1, 1, 1, 1, 4, 3, 3, 1, 6]
def baseStart_702075 : Nat := 118140960795 + 702075 * 2 ^ 59
def prefixEnd_702075 : Nat := 4983230072969 + 3 ^ 40 * 702075 * 2
def baseEnd_702075 : Nat := 240334620336963908022481

theorem tailTrace_702075 : CollatzResearch.WordTrace tailWord_702075 prefixEnd_702075 240334620336963908022481 := by
  unfold tailWord_702075
  simp only [CollatzResearch.WordTrace]
  refine ⟨25606778931509654708995679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17071185954339769805997119 25606778931509654708995679)
  ·
    refine ⟨38410168397264482063493519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25606778931509654708995679 38410168397264482063493519)
    ·
      refine ⟨57615252595896723095240279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38410168397264482063493519 57615252595896723095240279)
      ·
        refine ⟨86422878893845084642860419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57615252595896723095240279 86422878893845084642860419)
        ·
          refine ⟨129634318340767626964290629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86422878893845084642860419 129634318340767626964290629)
          ·
            refine ⟨24306434688893930055804493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 129634318340767626964290629 24306434688893930055804493)
            ·
              refine ⟨9114913008335223770926685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24306434688893930055804493 9114913008335223770926685)
              ·
                refine ⟨3418092378125708914097507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9114913008335223770926685 3418092378125708914097507)
                ·
                  refine ⟨5127138567188563371146261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3418092378125708914097507 5127138567188563371146261)
                  ·
                    refine ⟨240334620336963908022481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5127138567188563371146261 240334620336963908022481)
                    ·
                      rfl

theorem cell22_702075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 3, 1, 6].length) (baseStart_702075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_702075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_702075 prefixEnd_702075 := by exact prefixLift 702075
  have htrace : WordTrace (prefixWord ++ tailWord_702075) baseStart_702075 baseEnd_702075 := by
    simpa [prefixWord, tailWord_702075, baseEnd_702075] using wordTrace_append hprefix tailTrace_702075
  have hstable : (prefixWord ++ tailWord_702075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702075).length < 2 ^ (prefixWord ++ tailWord_702075).sum := by decide
  have hdescent : baseEnd_702075 < baseStart_702075 := by decide
  rcases family_descends (prefixWord ++ tailWord_702075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702092 : List Nat := [2, 2, 1, 2, 1, 1, 5, 2, 2, 4]
def baseStart_702092 : Nat := 118140960795 + 702092 * 2 ^ 59
def prefixEnd_702092 : Nat := 4983230072969 + 3 ^ 40 * 702092 * 2
def baseEnd_702092 : Nat := 240340439784381530347429

theorem tailTrace_702092 : CollatzResearch.WordTrace tailWord_702092 prefixEnd_702092 240340439784381530347429 := by
  unfold tailWord_702092
  simp only [CollatzResearch.WordTrace]
  refine ⟨12803699486224033306182265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17071599314965377741576353 12803699486224033306182265)
  ·
    refine ⟨9602774614668024979636699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12803699486224033306182265 9602774614668024979636699)
    ·
      refine ⟨14404161922002037469455049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9602774614668024979636699 14404161922002037469455049)
      ·
        refine ⟨10803121441501528102091287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14404161922002037469455049 10803121441501528102091287)
        ·
          refine ⟨16204682162252292153136931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10803121441501528102091287 16204682162252292153136931)
          ·
            refine ⟨24307023243378438229705397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16204682162252292153136931 24307023243378438229705397)
            ·
              refine ⟨2278783429066728584034881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24307023243378438229705397 2278783429066728584034881)
              ·
                refine ⟨1709087571800046438026161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2278783429066728584034881 1709087571800046438026161)
                ·
                  refine ⟨1281815678850034828519621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1709087571800046438026161 1281815678850034828519621)
                  ·
                    refine ⟨240340439784381530347429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1281815678850034828519621 240340439784381530347429)
                    ·
                      rfl

theorem cell22_702092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 2, 2, 4].length) (baseStart_702092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_702092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_702092 prefixEnd_702092 := by exact prefixLift 702092
  have htrace : WordTrace (prefixWord ++ tailWord_702092) baseStart_702092 baseEnd_702092 := by
    simpa [prefixWord, tailWord_702092, baseEnd_702092] using wordTrace_append hprefix tailTrace_702092
  have hstable : (prefixWord ++ tailWord_702092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702092).length < 2 ^ (prefixWord ++ tailWord_702092).sum := by decide
  have hdescent : baseEnd_702092 < baseStart_702092 := by decide
  rcases family_descends (prefixWord ++ tailWord_702092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702094 : List Nat := [4, 1, 1, 3, 1, 2, 2, 1, 4, 3]
def baseStart_702094 : Nat := 118140960795 + 702094 * 2 ^ 59
def prefixEnd_702094 : Nat := 4983230072969 + 3 ^ 40 * 702094 * 2
def baseEnd_702094 : Nat := 240341124425254191797423

theorem tailTrace_702094 : CollatzResearch.WordTrace tailWord_702094 prefixEnd_702094 240341124425254191797423 := by
  unfold tailWord_702094
  simp only [CollatzResearch.WordTrace]
  refine ⟨3200933989805102619242167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17071647945627213969291557 3200933989805102619242167)
  ·
    refine ⟨4801400984707653928863251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3200933989805102619242167 4801400984707653928863251)
    ·
      refine ⟨7202101477061480893294877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4801400984707653928863251 7202101477061480893294877)
      ·
        refine ⟨2700788053898055334985579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7202101477061480893294877 2700788053898055334985579)
        ·
          refine ⟨4051182080847083002478369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2700788053898055334985579 4051182080847083002478369)
          ·
            refine ⟨3038386560635312251858777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4051182080847083002478369 3038386560635312251858777)
            ·
              refine ⟨2278789920476484188894083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3038386560635312251858777 2278789920476484188894083)
              ·
                refine ⟨3418184880714726283341125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2278789920476484188894083 3418184880714726283341125)
                ·
                  refine ⟨640909665134011178126461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3418184880714726283341125 640909665134011178126461)
                  ·
                    refine ⟨240341124425254191797423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 640909665134011178126461 240341124425254191797423)
                    ·
                      rfl

theorem cell22_702094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 1, 4, 3].length) (baseStart_702094 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_702094 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_702094 prefixEnd_702094 := by exact prefixLift 702094
  have htrace : WordTrace (prefixWord ++ tailWord_702094) baseStart_702094 baseEnd_702094 := by
    simpa [prefixWord, tailWord_702094, baseEnd_702094] using wordTrace_append hprefix tailTrace_702094
  have hstable : (prefixWord ++ tailWord_702094).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702094).length < 2 ^ (prefixWord ++ tailWord_702094).sum := by decide
  have hdescent : baseEnd_702094 < baseStart_702094 := by decide
  rcases family_descends (prefixWord ++ tailWord_702094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702105 : List Nat := [1, 2, 1, 2, 1, 2, 2, 2, 2, 7]
def baseStart_702105 : Nat := 118140960795 + 702105 * 2 ^ 59
def prefixEnd_702105 : Nat := 4983230072969 + 3 ^ 40 * 702105 * 2
def baseEnd_702105 : Nat := 240344889950053829772389

theorem tailTrace_702105 : CollatzResearch.WordTrace tailWord_702105 prefixEnd_702105 240344889950053829772389 := by
  unfold tailWord_702105
  simp only [CollatzResearch.WordTrace]
  refine ⟨25607873121400969832587769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17071915414267313221725179 25607873121400969832587769)
  ·
    refine ⟨19205904841050727374440827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25607873121400969832587769 19205904841050727374440827)
    ·
      refine ⟨28808857261576091061661241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19205904841050727374440827 28808857261576091061661241)
      ·
        refine ⟨21606642946182068296245931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28808857261576091061661241 21606642946182068296245931)
        ·
          refine ⟨32409964419273102444368897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21606642946182068296245931 32409964419273102444368897)
          ·
            refine ⟨24307473314454826833276673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32409964419273102444368897 24307473314454826833276673)
            ·
              refine ⟨18230604985841120124957505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24307473314454826833276673 18230604985841120124957505)
              ·
                refine ⟨13672953739380840093718129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18230604985841120124957505 13672953739380840093718129)
                ·
                  refine ⟨10254715304535630070288597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13672953739380840093718129 10254715304535630070288597)
                  ·
                    refine ⟨240344889950053829772389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10254715304535630070288597 240344889950053829772389)
                    ·
                      rfl

theorem cell22_702105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 2, 7].length) (baseStart_702105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_702105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_702105 prefixEnd_702105 := by exact prefixLift 702105
  have htrace : WordTrace (prefixWord ++ tailWord_702105) baseStart_702105 baseEnd_702105 := by
    simpa [prefixWord, tailWord_702105, baseEnd_702105] using wordTrace_append hprefix tailTrace_702105
  have hstable : (prefixWord ++ tailWord_702105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702105).length < 2 ^ (prefixWord ++ tailWord_702105).sum := by decide
  have hdescent : baseEnd_702105 < baseStart_702105 := by decide
  rcases family_descends (prefixWord ++ tailWord_702105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702167 : List Nat := [1, 1, 3, 2, 1, 3, 3, 1, 2, 5]
def baseStart_702167 : Nat := 118140960795 + 702167 * 2 ^ 59
def prefixEnd_702167 : Nat := 4983230072969 + 3 ^ 40 * 702167 * 2
def baseEnd_702167 : Nat := 240366113817106334722199

theorem tailTrace_702167 : CollatzResearch.WordTrace tailWord_702167 prefixEnd_702167 240366113817106334722199 := by
  unfold tailWord_702167
  simp only [CollatzResearch.WordTrace]
  refine ⟨25610134447176354421344755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17073422964784236280896503 25610134447176354421344755)
  ·
    refine ⟨38415201670764531632017133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25610134447176354421344755 38415201670764531632017133)
    ·
      refine ⟨14405700626536699362006425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38415201670764531632017133 14405700626536699362006425)
      ·
        refine ⟨10804275469902524521504819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14405700626536699362006425 10804275469902524521504819)
        ·
          refine ⟨16206413204853786782257229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10804275469902524521504819 16206413204853786782257229)
          ·
            refine ⟨6077404951820170043346461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16206413204853786782257229 6077404951820170043346461)
            ·
              refine ⟨2279026856932563766254923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6077404951820170043346461 2279026856932563766254923)
              ·
                refine ⟨3418540285398845649382385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2279026856932563766254923 3418540285398845649382385)
                ·
                  refine ⟨2563905214049134237036789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3418540285398845649382385 2563905214049134237036789)
                  ·
                    refine ⟨240366113817106334722199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2563905214049134237036789 240366113817106334722199)
                    ·
                      rfl

theorem cell22_702167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 1, 2, 5].length) (baseStart_702167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_702167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_702167 prefixEnd_702167 := by exact prefixLift 702167
  have htrace : WordTrace (prefixWord ++ tailWord_702167) baseStart_702167 baseEnd_702167 := by
    simpa [prefixWord, tailWord_702167, baseEnd_702167] using wordTrace_append hprefix tailTrace_702167
  have hstable : (prefixWord ++ tailWord_702167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702167).length < 2 ^ (prefixWord ++ tailWord_702167).sum := by decide
  have hdescent : baseEnd_702167 < baseStart_702167 := by decide
  rcases family_descends (prefixWord ++ tailWord_702167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702173 : List Nat := [1, 4, 3, 3, 1, 1, 1, 2, 3, 3]
def baseStart_702173 : Nat := 118140960795 + 702173 * 2 ^ 59
def prefixEnd_702173 : Nat := 4983230072969 + 3 ^ 40 * 702173 * 2
def baseEnd_702173 : Nat := 240368167739724319072181

theorem tailTrace_702173 : CollatzResearch.WordTrace tailWord_702173 prefixEnd_702173 240368167739724319072181 := by
  unfold tailWord_702173
  simp only [CollatzResearch.WordTrace]
  refine ⟨25610353285154617446063173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17073568856769744964042115 25610353285154617446063173)
  ·
    refine ⟨4801941240966490771136845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25610353285154617446063173 4801941240966490771136845)
    ·
      refine ⟨1800727965362434039176317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4801941240966490771136845 1800727965362434039176317)
      ·
        refine ⟨675272987010912764691119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1800727965362434039176317 675272987010912764691119)
        ·
          refine ⟨1012909480516369147036679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 675272987010912764691119 1012909480516369147036679)
          ·
            refine ⟨1519364220774553720555019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1012909480516369147036679 1519364220774553720555019)
            ·
              refine ⟨2279046331161830580832529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1519364220774553720555019 2279046331161830580832529)
              ·
                refine ⟨1709284748371372935624397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2279046331161830580832529 1709284748371372935624397)
                ·
                  refine ⟨640981780639264850859149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1709284748371372935624397 640981780639264850859149)
                  ·
                    refine ⟨240368167739724319072181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 640981780639264850859149 240368167739724319072181)
                    ·
                      rfl

theorem cell22_702173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 2, 3, 3].length) (baseStart_702173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_702173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_702173 prefixEnd_702173 := by exact prefixLift 702173
  have htrace : WordTrace (prefixWord ++ tailWord_702173) baseStart_702173 baseEnd_702173 := by
    simpa [prefixWord, tailWord_702173, baseEnd_702173] using wordTrace_append hprefix tailTrace_702173
  have hstable : (prefixWord ++ tailWord_702173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702173).length < 2 ^ (prefixWord ++ tailWord_702173).sum := by decide
  have hdescent : baseEnd_702173 < baseStart_702173 := by decide
  rcases family_descends (prefixWord ++ tailWord_702173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702227 : List Nat := [1, 1, 1, 2, 1, 3, 2, 1, 6, 4]
def baseStart_702227 : Nat := 118140960795 + 702227 * 2 ^ 59
def prefixEnd_702227 : Nat := 4983230072969 + 3 ^ 40 * 702227 * 2
def baseEnd_702227 : Nat := 240386653043286178222015

theorem tailTrace_702227 : CollatzResearch.WordTrace tailWord_702227 prefixEnd_702227 240386653043286178222015 := by
  unfold tailWord_702227
  simp only [CollatzResearch.WordTrace]
  refine ⟨25612322826958984668528935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17074881884639323112352623 25612322826958984668528935)
  ·
    refine ⟨38418484240438477002793403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25612322826958984668528935 38418484240438477002793403)
    ·
      refine ⟨57627726360657715504190105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38418484240438477002793403 57627726360657715504190105)
      ·
        refine ⟨43220794770493286628142579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57627726360657715504190105 43220794770493286628142579)
        ·
          refine ⟨64831192155739929942213869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43220794770493286628142579 64831192155739929942213869)
          ·
            refine ⟨24311697058402473728330201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64831192155739929942213869 24311697058402473728330201)
            ·
              refine ⟨18233772793801855296247651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24311697058402473728330201 18233772793801855296247651)
              ·
                refine ⟨27350659190702782944371477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18233772793801855296247651 27350659190702782944371477)
                ·
                  refine ⟨1282062149564192950517413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 27350659190702782944371477 1282062149564192950517413)
                  ·
                    refine ⟨240386653043286178222015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1282062149564192950517413 240386653043286178222015)
                    ·
                      rfl

theorem cell22_702227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 6, 4].length) (baseStart_702227 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_702227 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_702227 prefixEnd_702227 := by exact prefixLift 702227
  have htrace : WordTrace (prefixWord ++ tailWord_702227) baseStart_702227 baseEnd_702227 := by
    simpa [prefixWord, tailWord_702227, baseEnd_702227] using wordTrace_append hprefix tailTrace_702227
  have hstable : (prefixWord ++ tailWord_702227).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702227).length < 2 ^ (prefixWord ++ tailWord_702227).sum := by decide
  have hdescent : baseEnd_702227 < baseStart_702227 := by decide
  rcases family_descends (prefixWord ++ tailWord_702227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702229 : List Nat := [1, 3, 2, 1, 2, 3, 3, 1, 1, 5]
def baseStart_702229 : Nat := 118140960795 + 702229 * 2 ^ 59
def prefixEnd_702229 : Nat := 4983230072969 + 3 ^ 40 * 702229 * 2
def baseEnd_702229 : Nat := 240387337684158839672009

theorem tailTrace_702229 : CollatzResearch.WordTrace tailWord_702229 prefixEnd_702229 240387337684158839672009 := by
  unfold tailWord_702229
  simp only [CollatzResearch.WordTrace]
  refine ⟨25612395772951739010101741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17074930515301159340067827 25612395772951739010101741)
  ·
    refine ⟨9604648414856902128788153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25612395772951739010101741 9604648414856902128788153)
    ·
      refine ⟨7203486311142676596591115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9604648414856902128788153 7203486311142676596591115)
      ·
        refine ⟨10805229466714014894886673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7203486311142676596591115 10805229466714014894886673)
        ·
          refine ⟨8103922100035511171165005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10805229466714014894886673 8103922100035511171165005)
          ·
            refine ⟨3038970787513316689186877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8103922100035511171165005 3038970787513316689186877)
            ·
              refine ⟨1139614045317493758445079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3038970787513316689186877 1139614045317493758445079)
              ·
                refine ⟨1709421067976240637667619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1139614045317493758445079 1709421067976240637667619)
                ·
                  refine ⟨2564131601964360956501429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1709421067976240637667619 2564131601964360956501429)
                  ·
                    refine ⟨240387337684158839672009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2564131601964360956501429 240387337684158839672009)
                    ·
                      rfl

theorem cell22_702229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 3, 1, 1, 5].length) (baseStart_702229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_702229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_702229 prefixEnd_702229 := by exact prefixLift 702229
  have htrace : WordTrace (prefixWord ++ tailWord_702229) baseStart_702229 baseEnd_702229 := by
    simpa [prefixWord, tailWord_702229, baseEnd_702229] using wordTrace_append hprefix tailTrace_702229
  have hstable : (prefixWord ++ tailWord_702229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702229).length < 2 ^ (prefixWord ++ tailWord_702229).sum := by decide
  have hdescent : baseEnd_702229 < baseStart_702229 := by decide
  rcases family_descends (prefixWord ++ tailWord_702229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702244 : List Nat := [2, 3, 1, 3, 2, 1, 2, 1, 1, 6]
def baseStart_702244 : Nat := 118140960795 + 702244 * 2 ^ 59
def prefixEnd_702244 : Nat := 4983230072969 + 3 ^ 40 * 702244 * 2
def baseEnd_702244 : Nat := 240392472490703800546963

theorem tailTrace_702244 : CollatzResearch.WordTrace tailWord_702244 prefixEnd_702244 240392472490703800546963 := by
  unfold tailWord_702244
  simp only [CollatzResearch.WordTrace]
  refine ⟨12806471433948698285948893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17075295245264931047931857 12806471433948698285948893)
  ·
    refine ⟨4802426787730761857230835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12806471433948698285948893 4802426787730761857230835)
    ·
      refine ⟨7203640181596142785846253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4802426787730761857230835 7203640181596142785846253)
      ·
        refine ⟨2701365068098553544692345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7203640181596142785846253 2701365068098553544692345)
        ·
          refine ⟨2026023801073915158519259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2701365068098553544692345 2026023801073915158519259)
          ·
            refine ⟨3039035701610872737778889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2026023801073915158519259 3039035701610872737778889)
            ·
              refine ⟨2279276776208154553334167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3039035701610872737778889 2279276776208154553334167)
              ·
                refine ⟨3418915164312231830001251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2279276776208154553334167 3418915164312231830001251)
                ·
                  refine ⟨5128372746468347745001877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3418915164312231830001251 5128372746468347745001877)
                  ·
                    refine ⟨240392472490703800546963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5128372746468347745001877 240392472490703800546963)
                    ·
                      rfl

theorem cell22_702244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 1, 1, 6].length) (baseStart_702244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_702244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_702244 prefixEnd_702244 := by exact prefixLift 702244
  have htrace : WordTrace (prefixWord ++ tailWord_702244) baseStart_702244 baseEnd_702244 := by
    simpa [prefixWord, tailWord_702244, baseEnd_702244] using wordTrace_append hprefix tailTrace_702244
  have hstable : (prefixWord ++ tailWord_702244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702244).length < 2 ^ (prefixWord ++ tailWord_702244).sum := by decide
  have hdescent : baseEnd_702244 < baseStart_702244 := by decide
  rcases family_descends (prefixWord ++ tailWord_702244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702248 : List Nat := [2, 1, 5, 1, 1, 4, 1, 3, 4]
def baseStart_702248 : Nat := 118140960795 + 702248 * 2 ^ 59
def prefixEnd_702248 : Nat := 4983230072969 + 3 ^ 40 * 702248 * 2
def baseEnd_702248 : Nat := 80131280590816374482317

theorem tailTrace_702248 : CollatzResearch.WordTrace tailWord_702248 prefixEnd_702248 80131280590816374482317 := by
  unfold tailWord_702248
  simp only [CollatzResearch.WordTrace]
  refine ⟨12806544379941452627521699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17075392506588603503362265 12806544379941452627521699)
  ·
    refine ⟨19209816569912178941282549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12806544379941452627521699 19209816569912178941282549)
    ·
      refine ⟨1800920303429266775745239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19209816569912178941282549 1800920303429266775745239)
      ·
        refine ⟨2701380455143900163617859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1800920303429266775745239 2701380455143900163617859)
        ·
          refine ⟨4052070682715850245426789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2701380455143900163617859 4052070682715850245426789)
          ·
            refine ⟨759763253009221921017523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4052070682715850245426789 759763253009221921017523)
            ·
              refine ⟨1139644879513832881526285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 759763253009221921017523 1139644879513832881526285)
              ·
                refine ⟨427366829817687330572357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1139644879513832881526285 427366829817687330572357)
                ·
                  refine ⟨80131280590816374482317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 427366829817687330572357 80131280590816374482317)
                  ·
                    rfl

theorem cell22_702248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 1, 3, 4].length) (baseStart_702248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_702248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_702248 prefixEnd_702248 := by exact prefixLift 702248
  have htrace : WordTrace (prefixWord ++ tailWord_702248) baseStart_702248 baseEnd_702248 := by
    simpa [prefixWord, tailWord_702248, baseEnd_702248] using wordTrace_append hprefix tailTrace_702248
  have hstable : (prefixWord ++ tailWord_702248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702248).length < 2 ^ (prefixWord ++ tailWord_702248).sum := by decide
  have hdescent : baseEnd_702248 < baseStart_702248 := by decide
  rcases family_descends (prefixWord ++ tailWord_702248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702259 : List Nat := [1, 1, 1, 2, 7, 2, 8]
def baseStart_702259 : Nat := 118140960795 + 702259 * 2 ^ 59
def prefixEnd_702259 : Nat := 4983230072969 + 3 ^ 40 * 702259 * 2
def baseEnd_702259 : Nat := 8903615085083287460071

theorem tailTrace_702259 : CollatzResearch.WordTrace tailWord_702259 prefixEnd_702259 8903615085083287460071 := by
  unfold tailWord_702259
  simp only [CollatzResearch.WordTrace]
  refine ⟨25613489962843054133693831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17075659975228702755795887 25613489962843054133693831)
  ·
    refine ⟨38420234944264581200540747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25613489962843054133693831 38420234944264581200540747)
    ·
      refine ⟨57630352416396871800811121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38420234944264581200540747 57630352416396871800811121)
      ·
        refine ⟨43222764312297653850608341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57630352416396871800811121 43222764312297653850608341)
        ·
          refine ⟨1013033538569476262123633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 43222764312297653850608341 1013033538569476262123633)
          ·
            refine ⟨759775153927107196592725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1013033538569476262123633 759775153927107196592725)
            ·
              refine ⟨8903615085083287460071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 759775153927107196592725 8903615085083287460071)
              ·
                rfl

theorem cell22_702259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 8].length) (baseStart_702259 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_702259 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_702259 prefixEnd_702259 := by exact prefixLift 702259
  have htrace : WordTrace (prefixWord ++ tailWord_702259) baseStart_702259 baseEnd_702259 := by
    simpa [prefixWord, tailWord_702259, baseEnd_702259] using wordTrace_append hprefix tailTrace_702259
  have hstable : (prefixWord ++ tailWord_702259).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702259).length < 2 ^ (prefixWord ++ tailWord_702259).sum := by decide
  have hdescent : baseEnd_702259 < baseStart_702259 := by decide
  rcases family_descends (prefixWord ++ tailWord_702259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702261 : List Nat := [1, 3, 3, 1, 4, 1, 1, 2, 2, 4]
def baseStart_702261 : Nat := 118140960795 + 702261 * 2 ^ 59
def prefixEnd_702261 : Nat := 4983230072969 + 3 ^ 40 * 702261 * 2
def baseEnd_702261 : Nat := 240398291938121422871911

theorem tailTrace_702261 : CollatzResearch.WordTrace tailWord_702261 prefixEnd_702261 240398291938121422871911 := by
  unfold tailWord_702261
  simp only [CollatzResearch.WordTrace]
  refine ⟨25613562908835808475266637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17075708605890538983511091 25613562908835808475266637)
  ·
    refine ⟨9605086090813428178224989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25613562908835808475266637 9605086090813428178224989)
    ·
      refine ⟨3601907284055035566834371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9605086090813428178224989 3601907284055035566834371)
      ·
        refine ⟨5402860926082553350251557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3601907284055035566834371 5402860926082553350251557)
        ·
          refine ⟨1013036423640478753172167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5402860926082553350251557 1013036423640478753172167)
          ·
            refine ⟨1519554635460718129758251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1013036423640478753172167 1519554635460718129758251)
            ·
              refine ⟨2279331953191077194637377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1519554635460718129758251 2279331953191077194637377)
              ·
                refine ⟨1709498964893307895978033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2279331953191077194637377 1709498964893307895978033)
                ·
                  refine ⟨1282124223669980921983525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1709498964893307895978033 1282124223669980921983525)
                  ·
                    refine ⟨240398291938121422871911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1282124223669980921983525 240398291938121422871911)
                    ·
                      rfl

theorem cell22_702261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 2, 2, 4].length) (baseStart_702261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_702261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_702261 prefixEnd_702261 := by exact prefixLift 702261
  have htrace : WordTrace (prefixWord ++ tailWord_702261) baseStart_702261 baseEnd_702261 := by
    simpa [prefixWord, tailWord_702261, baseEnd_702261] using wordTrace_append hprefix tailTrace_702261
  have hstable : (prefixWord ++ tailWord_702261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702261).length < 2 ^ (prefixWord ++ tailWord_702261).sum := by decide
  have hdescent : baseEnd_702261 < baseStart_702261 := by decide
  rcases family_descends (prefixWord ++ tailWord_702261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702265 : List Nat := [1, 2, 1, 7, 1, 1, 3, 2, 4]
def baseStart_702265 : Nat := 118140960795 + 702265 * 2 ^ 59
def prefixEnd_702265 : Nat := 4983230072969 + 3 ^ 40 * 702265 * 2
def baseEnd_702265 : Nat := 80133220406622248590633

theorem tailTrace_702265 : CollatzResearch.WordTrace tailWord_702265 prefixEnd_702265 80133220406622248590633 := by
  unfold tailWord_702265
  simp only [CollatzResearch.WordTrace]
  refine ⟨25613708800821317158412249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17075805867214211438941499 25613708800821317158412249)
  ·
    refine ⟨19210281600615987868809187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25613708800821317158412249 19210281600615987868809187)
    ·
      refine ⟨28815422400923981803213781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19210281600615987868809187 28815422400923981803213781)
      ·
        refine ⟨675361462521655823512823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 28815422400923981803213781 675361462521655823512823)
        ·
          refine ⟨1013042193782483735269235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 675361462521655823512823 1013042193782483735269235)
          ·
            refine ⟨1519563290673725602903853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1013042193782483735269235 1519563290673725602903853)
            ·
              refine ⟨569836234002647101088945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1519563290673725602903853 569836234002647101088945)
              ·
                refine ⟨427377175501985325816709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 569836234002647101088945 427377175501985325816709)
                ·
                  refine ⟨80133220406622248590633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 427377175501985325816709 80133220406622248590633)
                  ·
                    rfl

theorem cell22_702265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 3, 2, 4].length) (baseStart_702265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_702265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_702265 prefixEnd_702265 := by exact prefixLift 702265
  have htrace : WordTrace (prefixWord ++ tailWord_702265) baseStart_702265 baseEnd_702265 := by
    simpa [prefixWord, tailWord_702265, baseEnd_702265] using wordTrace_append hprefix tailTrace_702265
  have hstable : (prefixWord ++ tailWord_702265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702265).length < 2 ^ (prefixWord ++ tailWord_702265).sum := by decide
  have hdescent : baseEnd_702265 < baseStart_702265 := by decide
  rcases family_descends (prefixWord ++ tailWord_702265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702398 : List Nat := [4, 2, 1, 1, 1, 5, 1, 1, 1, 5]
def baseStart_702398 : Nat := 118140960795 + 702398 * 2 ^ 59
def prefixEnd_702398 : Nat := 4983230072969 + 3 ^ 40 * 702398 * 2
def baseEnd_702398 : Nat := 240445189837898732196491

theorem tailTrace_702398 : CollatzResearch.WordTrace tailWord_702398 prefixEnd_702398 240445189837898732196491 := by
  unfold tailWord_702398
  simp only [CollatzResearch.WordTrace]
  refine ⟨3202319963667435109125481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17079039806226320582002565 3202319963667435109125481)
  ·
    refine ⟨2401739972750576331844111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3202319963667435109125481 2401739972750576331844111)
    ·
      refine ⟨3602609959125864497766167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2401739972750576331844111 3602609959125864497766167)
      ·
        refine ⟨5403914938688796746649251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3602609959125864497766167 5403914938688796746649251)
        ·
          refine ⟨8105872408033195119973877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5403914938688796746649251 8105872408033195119973877)
          ·
            refine ⟨759925538253112042497551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8105872408033195119973877 759925538253112042497551)
            ·
              refine ⟨1139888307379668063746327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 759925538253112042497551 1139888307379668063746327)
              ·
                refine ⟨1709832461069502095619491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1139888307379668063746327 1709832461069502095619491)
                ·
                  refine ⟨2564748691604253143429237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1709832461069502095619491 2564748691604253143429237)
                  ·
                    refine ⟨240445189837898732196491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2564748691604253143429237 240445189837898732196491)
                    ·
                      rfl

theorem cell22_702398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 1, 1, 1, 5].length) (baseStart_702398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_702398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_702398 prefixEnd_702398 := by exact prefixLift 702398
  have htrace : WordTrace (prefixWord ++ tailWord_702398) baseStart_702398 baseEnd_702398 := by
    simpa [prefixWord, tailWord_702398, baseEnd_702398] using wordTrace_append hprefix tailTrace_702398
  have hstable : (prefixWord ++ tailWord_702398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702398).length < 2 ^ (prefixWord ++ tailWord_702398).sum := by decide
  have hdescent : baseEnd_702398 < baseStart_702398 := by decide
  rcases family_descends (prefixWord ++ tailWord_702398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702443 : List Nat := [1, 1, 1, 1, 2, 3, 1, 8, 1, 3]
def baseStart_702443 : Nat := 118140960795 + 702443 * 2 ^ 59
def prefixEnd_702443 : Nat := 4983230072969 + 3 ^ 40 * 702443 * 2
def baseEnd_702443 : Nat := 240460594257533614821353

theorem tailTrace_702443 : CollatzResearch.WordTrace tailWord_702443 prefixEnd_702443 240460594257533614821353 := by
  unfold tailWord_702443
  simp only [CollatzResearch.WordTrace]
  refine ⟨25620200994176453558391983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17080133996117635705594655 25620200994176453558391983)
  ·
    refine ⟨38430301491264680337587975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25620200994176453558391983 38430301491264680337587975)
    ·
      refine ⟨57645452236897020506381963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38430301491264680337587975 57645452236897020506381963)
      ·
        refine ⟨86468178355345530759572945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57645452236897020506381963 86468178355345530759572945)
        ·
          refine ⟨64851133766509148069679709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86468178355345530759572945 64851133766509148069679709)
          ·
            refine ⟨24319175162440930526129891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64851133766509148069679709 24319175162440930526129891)
            ·
              refine ⟨36478762743661395789194837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24319175162440930526129891 36478762743661395789194837)
              ·
                refine ⟨427485500902281981904627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 36478762743661395789194837 427485500902281981904627)
                ·
                  refine ⟨641228251353422972856941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 427485500902281981904627 641228251353422972856941)
                  ·
                    refine ⟨240460594257533614821353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 641228251353422972856941 240460594257533614821353)
                    ·
                      rfl

theorem cell22_702443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 8, 1, 3].length) (baseStart_702443 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_702443 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_702443 prefixEnd_702443 := by exact prefixLift 702443
  have htrace : WordTrace (prefixWord ++ tailWord_702443) baseStart_702443 baseEnd_702443 := by
    simpa [prefixWord, tailWord_702443, baseEnd_702443] using wordTrace_append hprefix tailTrace_702443
  have hstable : (prefixWord ++ tailWord_702443).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702443).length < 2 ^ (prefixWord ++ tailWord_702443).sum := by decide
  have hdescent : baseEnd_702443 < baseStart_702443 := by decide
  rcases family_descends (prefixWord ++ tailWord_702443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702518 : List Nat := [5, 1, 2, 1, 1, 1, 3, 2, 6]
def baseStart_702518 : Nat := 118140960795 + 702518 * 2 ^ 59
def prefixEnd_702518 : Nat := 4983230072969 + 3 ^ 40 * 702518 * 2
def baseEnd_702518 : Nat := 80162089430086139732041

theorem tailTrace_702518 : CollatzResearch.WordTrace tailWord_702518 prefixEnd_702518 80162089430086139732041 := by
  unfold tailWord_702518
  simp only [CollatzResearch.WordTrace]
  refine ⟨1601433529306546335460763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17081957645936494244914805 1601433529306546335460763)
  ·
    refine ⟨2402150293959819503191145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1601433529306546335460763 2402150293959819503191145)
    ·
      refine ⟨1801612720469864627393359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2402150293959819503191145 1801612720469864627393359)
      ·
        refine ⟨2702419080704796941090039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1801612720469864627393359 2702419080704796941090039)
        ·
          refine ⟨4053628621057195411635059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2702419080704796941090039 4053628621057195411635059)
          ·
            refine ⟨6080442931585793117452589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4053628621057195411635059 6080442931585793117452589)
            ·
              refine ⟨2280166099344672419044721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6080442931585793117452589 2280166099344672419044721)
              ·
                refine ⟨1710124574508504314283541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2280166099344672419044721 1710124574508504314283541)
                ·
                  refine ⟨80162089430086139732041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1710124574508504314283541 80162089430086139732041)
                  ·
                    rfl

theorem cell22_702518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 2, 6].length) (baseStart_702518 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_702518 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_702518 prefixEnd_702518 := by exact prefixLift 702518
  have htrace : WordTrace (prefixWord ++ tailWord_702518) baseStart_702518 baseEnd_702518 := by
    simpa [prefixWord, tailWord_702518, baseEnd_702518] using wordTrace_append hprefix tailTrace_702518
  have hstable : (prefixWord ++ tailWord_702518).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702518).length < 2 ^ (prefixWord ++ tailWord_702518).sum := by decide
  have hdescent : baseEnd_702518 < baseStart_702518 := by decide
  rcases family_descends (prefixWord ++ tailWord_702518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702531 : List Nat := [1, 1, 1, 3, 1, 2, 2, 5, 2, 4]
def baseStart_702531 : Nat := 118140960795 + 702531 * 2 ^ 59
def prefixEnd_702531 : Nat := 4983230072969 + 3 ^ 40 * 702531 * 2
def baseEnd_702531 : Nat := 240490718455930718621083

theorem tailTrace_702531 : CollatzResearch.WordTrace tailWord_702531 prefixEnd_702531 240490718455930718621083 := by
  unfold tailWord_702531
  simp only [CollatzResearch.WordTrace]
  refine ⟨25623410617857644587595447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17082273745238429725063631 25623410617857644587595447)
  ·
    refine ⟨38435115926786466881393171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25623410617857644587595447 38435115926786466881393171)
    ·
      refine ⟨57652673890179700322089757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38435115926786466881393171 57652673890179700322089757)
      ·
        refine ⟨21619752708817387620783659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57652673890179700322089757 21619752708817387620783659)
        ·
          refine ⟨32429629063226081431175489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21619752708817387620783659 32429629063226081431175489)
          ·
            refine ⟨24322221797419561073381617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32429629063226081431175489 24322221797419561073381617)
            ·
              refine ⟨18241666348064670805036213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24322221797419561073381617 18241666348064670805036213)
              ·
                refine ⟨1710156220131062887972145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18241666348064670805036213 1710156220131062887972145)
                ·
                  refine ⟨1282617165098297165979109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1710156220131062887972145 1282617165098297165979109)
                  ·
                    refine ⟨240490718455930718621083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1282617165098297165979109 240490718455930718621083)
                    ·
                      rfl

theorem cell22_702531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 5, 2, 4].length) (baseStart_702531 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_702531 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_702531 prefixEnd_702531 := by exact prefixLift 702531
  have htrace : WordTrace (prefixWord ++ tailWord_702531) baseStart_702531 baseEnd_702531 := by
    simpa [prefixWord, tailWord_702531, baseEnd_702531] using wordTrace_append hprefix tailTrace_702531
  have hstable : (prefixWord ++ tailWord_702531).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702531).length < 2 ^ (prefixWord ++ tailWord_702531).sum := by decide
  have hdescent : baseEnd_702531 < baseStart_702531 := by decide
  rcases family_descends (prefixWord ++ tailWord_702531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702625 : List Nat := [1, 2, 3, 3, 1, 2, 4, 1, 5]
def baseStart_702625 : Nat := 118140960795 + 702625 * 2 ^ 59
def prefixEnd_702625 : Nat := 4983230072969 + 3 ^ 40 * 702625 * 2
def baseEnd_702625 : Nat := 80174298858981935590265

theorem tailTrace_702625 : CollatzResearch.WordTrace tailWord_702625 prefixEnd_702625 80174298858981935590265 := by
  unfold tailWord_702625
  simp only [CollatzResearch.WordTrace]
  refine ⟨25626839079517098641517329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17084559386344732427678219 25626839079517098641517329)
  ·
    refine ⟨19220129309637823981137997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25626839079517098641517329 19220129309637823981137997)
    ·
      refine ⟨7207548491114183992926749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19220129309637823981137997 7207548491114183992926749)
      ·
        refine ⟨2702830684167818997347531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7207548491114183992926749 2702830684167818997347531)
        ·
          refine ⟨4054246026251728496021297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2702830684167818997347531 4054246026251728496021297)
          ·
            refine ⟨3040684519688796372015973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4054246026251728496021297 3040684519688796372015973)
            ·
              refine ⟨570128347441649319752995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3040684519688796372015973 570128347441649319752995)
              ·
                refine ⟨855192521162473979629493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 570128347441649319752995 855192521162473979629493)
                ·
                  refine ⟨80174298858981935590265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 855192521162473979629493 80174298858981935590265)
                  ·
                    rfl

theorem cell22_702625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 4, 1, 5].length) (baseStart_702625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_702625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_702625 prefixEnd_702625 := by exact prefixLift 702625
  have htrace : WordTrace (prefixWord ++ tailWord_702625) baseStart_702625 baseEnd_702625 := by
    simpa [prefixWord, tailWord_702625, baseEnd_702625] using wordTrace_append hprefix tailTrace_702625
  have hstable : (prefixWord ++ tailWord_702625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702625).length < 2 ^ (prefixWord ++ tailWord_702625).sum := by decide
  have hdescent : baseEnd_702625 < baseStart_702625 := by decide
  rcases family_descends (prefixWord ++ tailWord_702625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702685 : List Nat := [1, 4, 3, 2, 1, 1, 1, 3, 1, 5]
def baseStart_702685 : Nat := 118140960795 + 702685 * 2 ^ 59
def prefixEnd_702685 : Nat := 4983230072969 + 3 ^ 40 * 702685 * 2
def baseEnd_702685 : Nat := 240543435803125650270611

theorem tailTrace_702685 : CollatzResearch.WordTrace tailWord_702685 prefixEnd_702685 240543435803125650270611 := by
  unfold tailWord_702685
  simp only [CollatzResearch.WordTrace]
  refine ⟨25629027459299728888701509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17086018306199819259134339 25629027459299728888701509)
  ·
    refine ⟨4805442648618699166631533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25629027459299728888701509 4805442648618699166631533)
    ·
      refine ⟨1802040993232012187486825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4805442648618699166631533 1802040993232012187486825)
      ·
        refine ⟨1351530744924009140615119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1802040993232012187486825 1351530744924009140615119)
        ·
          refine ⟨2027296117386013710922679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1351530744924009140615119 2027296117386013710922679)
          ·
            refine ⟨3040944176079020566384019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2027296117386013710922679 3040944176079020566384019)
            ·
              refine ⟨4561416264118530849576029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3040944176079020566384019 4561416264118530849576029)
              ·
                refine ⟨1710531099044449068591011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4561416264118530849576029 1710531099044449068591011)
                ·
                  refine ⟨2565796648566673602886517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1710531099044449068591011 2565796648566673602886517)
                  ·
                    refine ⟨240543435803125650270611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2565796648566673602886517 240543435803125650270611)
                    ·
                      rfl

theorem cell22_702685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_702685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_702685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_702685 prefixEnd_702685 := by exact prefixLift 702685
  have htrace : WordTrace (prefixWord ++ tailWord_702685) baseStart_702685 baseEnd_702685 := by
    simpa [prefixWord, tailWord_702685, baseEnd_702685] using wordTrace_append hprefix tailTrace_702685
  have hstable : (prefixWord ++ tailWord_702685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702685).length < 2 ^ (prefixWord ++ tailWord_702685).sum := by decide
  have hdescent : baseEnd_702685 < baseStart_702685 := by decide
  rcases family_descends (prefixWord ++ tailWord_702685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702730 : List Nat := [3, 1, 2, 2, 1, 1, 3, 3, 3, 3]
def baseStart_702730 : Nat := 118140960795 + 702730 * 2 ^ 59
def prefixEnd_702730 : Nat := 4983230072969 + 3 ^ 40 * 702730 * 2
def baseEnd_702730 : Nat := 240558840222760532895473

theorem tailTrace_702730 : CollatzResearch.WordTrace tailWord_702730 prefixEnd_702730 240558840222760532895473 := by
  unfold tailWord_702730
  simp only [CollatzResearch.WordTrace]
  refine ⟨6407667186034175393522411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17087112496091134382726429 6407667186034175393522411)
  ·
    refine ⟨9611500779051263090283617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6407667186034175393522411 9611500779051263090283617)
    ·
      refine ⟨7208625584288447317712713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9611500779051263090283617 7208625584288447317712713)
      ·
        refine ⟨5406469188216335488284535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7208625584288447317712713 5406469188216335488284535)
        ·
          refine ⟨8109703782324503232426803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5406469188216335488284535 8109703782324503232426803)
          ·
            refine ⟨12164555673486754848640205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8109703782324503232426803 12164555673486754848640205)
            ·
              refine ⟨4561708377557533068240077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12164555673486754848640205 4561708377557533068240077)
              ·
                refine ⟨1710640641584074900590029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4561708377557533068240077 1710640641584074900590029)
                ·
                  refine ⟨641490240594028087721261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1710640641584074900590029 641490240594028087721261)
                  ·
                    refine ⟨240558840222760532895473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 641490240594028087721261 240558840222760532895473)
                    ·
                      rfl

theorem cell22_702730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 3, 3, 3].length) (baseStart_702730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_702730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_702730 prefixEnd_702730 := by exact prefixLift 702730
  have htrace : WordTrace (prefixWord ++ tailWord_702730) baseStart_702730 baseEnd_702730 := by
    simpa [prefixWord, tailWord_702730, baseEnd_702730] using wordTrace_append hprefix tailTrace_702730
  have hstable : (prefixWord ++ tailWord_702730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702730).length < 2 ^ (prefixWord ++ tailWord_702730).sum := by decide
  have hdescent : baseEnd_702730 < baseStart_702730 := by decide
  rcases family_descends (prefixWord ++ tailWord_702730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702749 : List Nat := [1, 4, 2, 3, 3, 1, 2, 6]
def baseStart_702749 : Nat := 118140960795 + 702749 * 2 ^ 59
def prefixEnd_702749 : Nat := 4983230072969 + 3 ^ 40 * 702749 * 2
def baseEnd_702749 : Nat := 26729482701227868518935

theorem tailTrace_702749 : CollatzResearch.WordTrace tailWord_702749 prefixEnd_702749 26729482701227868518935 := by
  unfold tailWord_702749
  simp only [CollatzResearch.WordTrace]
  refine ⟨25631361731067867819031301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17087574487378578546020867 25631361731067867819031301)
  ·
    refine ⟨4805880324575225216068369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25631361731067867819031301 4805880324575225216068369)
    ·
      refine ⟨3604410243431418912051277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4805880324575225216068369 3604410243431418912051277)
      ·
        refine ⟨1351653841286782092019229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3604410243431418912051277 1351653841286782092019229)
        ·
          refine ⟨506870190482543284507211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1351653841286782092019229 506870190482543284507211)
          ·
            refine ⟨760305285723814926760817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 506870190482543284507211 760305285723814926760817)
            ·
              refine ⟨570228964292861195070613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 760305285723814926760817 570228964292861195070613)
              ·
                refine ⟨26729482701227868518935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 570228964292861195070613 26729482701227868518935)
                ·
                  rfl

theorem cell22_702749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 2, 6].length) (baseStart_702749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_702749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_702749 prefixEnd_702749 := by exact prefixLift 702749
  have htrace : WordTrace (prefixWord ++ tailWord_702749) baseStart_702749 baseEnd_702749 := by
    simpa [prefixWord, tailWord_702749, baseEnd_702749] using wordTrace_append hprefix tailTrace_702749
  have hstable : (prefixWord ++ tailWord_702749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702749).length < 2 ^ (prefixWord ++ tailWord_702749).sum := by decide
  have hdescent : baseEnd_702749 < baseStart_702749 := by decide
  rcases family_descends (prefixWord ++ tailWord_702749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702820 : List Nat := [2, 3, 1, 1, 3, 1, 3, 2, 1, 5]
def baseStart_702820 : Nat := 118140960795 + 702820 * 2 ^ 59
def prefixEnd_702820 : Nat := 4983230072969 + 3 ^ 40 * 702820 * 2
def baseEnd_702820 : Nat := 240589649062030298145197

theorem tailTrace_702820 : CollatzResearch.WordTrace tailWord_702820 prefixEnd_702820 240589649062030298145197 := by
  unfold tailWord_702820
  simp only [CollatzResearch.WordTrace]
  refine ⟨12816975656905323472432957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17089300875873764629910609 12816975656905323472432957)
  ·
    refine ⟨4806365871339496302162359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12816975656905323472432957 4806365871339496302162359)
    ·
      refine ⟨7209548807009244453243539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4806365871339496302162359 7209548807009244453243539)
      ·
        refine ⟨10814323210513866679865309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7209548807009244453243539 10814323210513866679865309)
        ·
          refine ⟨4055371203942700004949491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10814323210513866679865309 4055371203942700004949491)
          ·
            refine ⟨6083056805914050007424237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4055371203942700004949491 6083056805914050007424237)
            ·
              refine ⟨2281146302217768752784089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6083056805914050007424237 2281146302217768752784089)
              ·
                refine ⟨1710859726663326564588067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2281146302217768752784089 1710859726663326564588067)
                ·
                  refine ⟨2566289589994989846882101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1710859726663326564588067 2566289589994989846882101)
                  ·
                    refine ⟨240589649062030298145197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2566289589994989846882101 240589649062030298145197)
                    ·
                      rfl

theorem cell22_702820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 2, 1, 5].length) (baseStart_702820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_702820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_702820 prefixEnd_702820 := by exact prefixLift 702820
  have htrace : WordTrace (prefixWord ++ tailWord_702820) baseStart_702820 baseEnd_702820 := by
    simpa [prefixWord, tailWord_702820, baseEnd_702820] using wordTrace_append hprefix tailTrace_702820
  have hstable : (prefixWord ++ tailWord_702820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702820).length < 2 ^ (prefixWord ++ tailWord_702820).sum := by decide
  have hdescent : baseEnd_702820 < baseStart_702820 := by decide
  rcases family_descends (prefixWord ++ tailWord_702820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702824 : List Nat := [2, 1, 4, 2, 2, 2, 3, 1, 1, 4]
def baseStart_702824 : Nat := 118140960795 + 702824 * 2 ^ 59
def prefixEnd_702824 : Nat := 4983230072969 + 3 ^ 40 * 702824 * 2
def baseEnd_702824 : Nat := 240591018343775621045185

theorem tailTrace_702824 : CollatzResearch.WordTrace tailWord_702824 prefixEnd_702824 240591018343775621045185 := by
  unfold tailWord_702824
  simp only [CollatzResearch.WordTrace]
  refine ⟨12817048602898077814005763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17089398137197437085341017 12817048602898077814005763)
  ·
    refine ⟨19225572904347116721008645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12817048602898077814005763 19225572904347116721008645)
    ·
      refine ⟨3604794919565084385189121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19225572904347116721008645 3604794919565084385189121)
      ·
        refine ⟨2703596189673813288891841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3604794919565084385189121 2703596189673813288891841)
        ·
          refine ⟨2027697142255359966668881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2703596189673813288891841 2027697142255359966668881)
          ·
            refine ⟨1520772856691519975001661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2027697142255359966668881 1520772856691519975001661)
            ·
              refine ⟨570289821259319990625623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1520772856691519975001661 570289821259319990625623)
              ·
                refine ⟨855434731888979985938435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 570289821259319990625623 855434731888979985938435)
                ·
                  refine ⟨1283152097833469978907653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 855434731888979985938435 1283152097833469978907653)
                  ·
                    refine ⟨240591018343775621045185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1283152097833469978907653 240591018343775621045185)
                    ·
                      rfl

theorem cell22_702824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 3, 1, 1, 4].length) (baseStart_702824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_702824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_702824 prefixEnd_702824 := by exact prefixLift 702824
  have htrace : WordTrace (prefixWord ++ tailWord_702824) baseStart_702824 baseEnd_702824 := by
    simpa [prefixWord, tailWord_702824, baseEnd_702824] using wordTrace_append hprefix tailTrace_702824
  have hstable : (prefixWord ++ tailWord_702824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702824).length < 2 ^ (prefixWord ++ tailWord_702824).sum := by decide
  have hdescent : baseEnd_702824 < baseStart_702824 := by decide
  rcases family_descends (prefixWord ++ tailWord_702824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702848 : List Nat := [2, 1, 1, 2, 1, 2, 1, 1, 4, 7]
def baseStart_702848 : Nat := 118140960795 + 702848 * 2 ^ 59
def prefixEnd_702848 : Nat := 4983230072969 + 3 ^ 40 * 702848 * 2
def baseEnd_702848 : Nat := 240599234034247558445111

theorem tailTrace_702848 : CollatzResearch.WordTrace tailWord_702848 prefixEnd_702848 240599234034247558445111 := by
  unfold tailWord_702848
  simp only [CollatzResearch.WordTrace]
  refine ⟨12817486278854603863442599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17089981705139471817923465 12817486278854603863442599)
  ·
    refine ⟨19226229418281905795163899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12817486278854603863442599 19226229418281905795163899)
    ·
      refine ⟨28839344127422858692745849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19226229418281905795163899 28839344127422858692745849)
      ·
        refine ⟨21629508095567144019559387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28839344127422858692745849 21629508095567144019559387)
        ·
          refine ⟨32444262143350716029339081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21629508095567144019559387 32444262143350716029339081)
          ·
            refine ⟨24333196607513037022004311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32444262143350716029339081 24333196607513037022004311)
            ·
              refine ⟨36499794911269555533006467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24333196607513037022004311 36499794911269555533006467)
              ·
                refine ⟨54749692366904333299509701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36499794911269555533006467 54749692366904333299509701)
                ·
                  refine ⟨10265567318794562493658069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54749692366904333299509701 10265567318794562493658069)
                  ·
                    refine ⟨240599234034247558445111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10265567318794562493658069 240599234034247558445111)
                    ·
                      rfl

theorem cell22_702848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 4, 7].length) (baseStart_702848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_702848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_702848 prefixEnd_702848 := by exact prefixLift 702848
  have htrace : WordTrace (prefixWord ++ tailWord_702848) baseStart_702848 baseEnd_702848 := by
    simpa [prefixWord, tailWord_702848, baseEnd_702848] using wordTrace_append hprefix tailTrace_702848
  have hstable : (prefixWord ++ tailWord_702848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702848).length < 2 ^ (prefixWord ++ tailWord_702848).sum := by decide
  have hdescent : baseEnd_702848 < baseStart_702848 := by decide
  rcases family_descends (prefixWord ++ tailWord_702848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702882 : List Nat := [3, 3, 1, 2, 1, 1, 1, 2, 5, 3]
def baseStart_702882 : Nat := 118140960795 + 702882 * 2 ^ 59
def prefixEnd_702882 : Nat := 4983230072969 + 3 ^ 40 * 702882 * 2
def baseEnd_702882 : Nat := 240610872929082803095007

theorem tailTrace_702882 : CollatzResearch.WordTrace tailWord_702882 prefixEnd_702882 240610872929082803095007 := by
  unfold tailWord_702882
  simp only [CollatzResearch.WordTrace]
  refine ⟨6409053159896507883405725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17090808426390687689081933 6409053159896507883405725)
  ·
    refine ⟨2403394934961190456277147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6409053159896507883405725 2403394934961190456277147)
    ·
      refine ⟨3605092402441785684415721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2403394934961190456277147 3605092402441785684415721)
      ·
        refine ⟨2703819301831339263311791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3605092402441785684415721 2703819301831339263311791)
        ·
          refine ⟨4055728952747008894967687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2703819301831339263311791 4055728952747008894967687)
          ·
            refine ⟨6083593429120513342451531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4055728952747008894967687 6083593429120513342451531)
            ·
              refine ⟨9125390143680770013677297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6083593429120513342451531 9125390143680770013677297)
              ·
                refine ⟨6844042607760577510257973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9125390143680770013677297 6844042607760577510257973)
                ·
                  refine ⟨641628994477554141586685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6844042607760577510257973 641628994477554141586685)
                  ·
                    refine ⟨240610872929082803095007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 641628994477554141586685 240610872929082803095007)
                    ·
                      rfl

theorem cell22_702882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 2, 5, 3].length) (baseStart_702882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_702882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_702882 prefixEnd_702882 := by exact prefixLift 702882
  have htrace : WordTrace (prefixWord ++ tailWord_702882) baseStart_702882 baseEnd_702882 := by
    simpa [prefixWord, tailWord_702882, baseEnd_702882] using wordTrace_append hprefix tailTrace_702882
  have hstable : (prefixWord ++ tailWord_702882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702882).length < 2 ^ (prefixWord ++ tailWord_702882).sum := by decide
  have hdescent : baseEnd_702882 < baseStart_702882 := by decide
  rcases family_descends (prefixWord ++ tailWord_702882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702970 : List Nat := [3, 1, 1, 1, 1, 2, 2, 4, 1, 6]
def baseStart_702970 : Nat := 118140960795 + 702970 * 2 ^ 59
def prefixEnd_702970 : Nat := 4983230072969 + 3 ^ 40 * 702970 * 2
def baseEnd_702970 : Nat := 240640997127479906894737

theorem tailTrace_702970 : CollatzResearch.WordTrace tailWord_702970 prefixEnd_702970 240640997127479906894737 := by
  unfold tailWord_702970
  simp only [CollatzResearch.WordTrace]
  refine ⟨6409855565816805640706591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17092948175511481708550909 6409855565816805640706591)
  ·
    refine ⟨9614783348725208461059887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6409855565816805640706591 9614783348725208461059887)
    ·
      refine ⟨14422175023087812691589831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9614783348725208461059887 14422175023087812691589831)
      ·
        refine ⟨21633262534631719037384747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14422175023087812691589831 21633262534631719037384747)
        ·
          refine ⟨32449893801947578556077121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21633262534631719037384747 32449893801947578556077121)
          ·
            refine ⟨24337420351460683917057841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32449893801947578556077121 24337420351460683917057841)
            ·
              refine ⟨18253065263595512937793381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24337420351460683917057841 18253065263595512937793381)
              ·
                refine ⟨3422449736924158675836259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18253065263595512937793381 3422449736924158675836259)
                ·
                  refine ⟨5133674605386238013754389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3422449736924158675836259 5133674605386238013754389)
                  ·
                    refine ⟨240640997127479906894737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5133674605386238013754389 240640997127479906894737)
                    ·
                      rfl

theorem cell22_702970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 4, 1, 6].length) (baseStart_702970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_702970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_702970 prefixEnd_702970 := by exact prefixLift 702970
  have htrace : WordTrace (prefixWord ++ tailWord_702970) baseStart_702970 baseEnd_702970 := by
    simpa [prefixWord, tailWord_702970, baseEnd_702970] using wordTrace_append hprefix tailTrace_702970
  have hstable : (prefixWord ++ tailWord_702970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702970).length < 2 ^ (prefixWord ++ tailWord_702970).sum := by decide
  have hdescent : baseEnd_702970 < baseStart_702970 := by decide
  rcases family_descends (prefixWord ++ tailWord_702970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702987 : List Nat := [1, 1, 1, 1, 7, 1, 1, 3, 2, 4]
def baseStart_702987 : Nat := 118140960795 + 702987 * 2 ^ 59
def prefixEnd_702987 : Nat := 4983230072969 + 3 ^ 40 * 702987 * 2
def baseEnd_702987 : Nat := 240646816574897529219685

theorem tailTrace_702987 : CollatzResearch.WordTrace tailWord_702987 prefixEnd_702987 240646816574897529219685 := by
  unfold tailWord_702987
  simp only [CollatzResearch.WordTrace]
  refine ⟨25640042304205634466195215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17093361536137089644130143 25640042304205634466195215)
  ·
    refine ⟨38460063456308451699292823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25640042304205634466195215 38460063456308451699292823)
    ·
      refine ⟨57690095184462677548939235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38460063456308451699292823 57690095184462677548939235)
      ·
        refine ⟨86535142776694016323408853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57690095184462677548939235 86535142776694016323408853)
        ·
          refine ⟨2028167408828766007579895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 86535142776694016323408853 2028167408828766007579895)
          ·
            refine ⟨3042251113243149011369843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2028167408828766007579895 3042251113243149011369843)
            ·
              refine ⟨4563376669864723517054765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3042251113243149011369843 4563376669864723517054765)
              ·
                refine ⟨1711266251199271318895537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4563376669864723517054765 1711266251199271318895537)
                ·
                  refine ⟨1283449688399453489171653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1711266251199271318895537 1283449688399453489171653)
                  ·
                    refine ⟨240646816574897529219685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1283449688399453489171653 240646816574897529219685)
                    ·
                      rfl

theorem cell22_702987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 3, 2, 4].length) (baseStart_702987 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_702987 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_702987 prefixEnd_702987 := by exact prefixLift 702987
  have htrace : WordTrace (prefixWord ++ tailWord_702987) baseStart_702987 baseEnd_702987 := by
    simpa [prefixWord, tailWord_702987, baseEnd_702987] using wordTrace_append hprefix tailTrace_702987
  have hstable : (prefixWord ++ tailWord_702987).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702987).length < 2 ^ (prefixWord ++ tailWord_702987).sum := by decide
  have hdescent : baseEnd_702987 < baseStart_702987 := by decide
  rcases family_descends (prefixWord ++ tailWord_702987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703008 : List Nat := [2, 1, 1, 6, 2, 2, 2, 2, 4]
def baseStart_703008 : Nat := 118140960795 + 703008 * 2 ^ 59
def prefixEnd_703008 : Nat := 4983230072969 + 3 ^ 40 * 703008 * 2
def baseEnd_703008 : Nat := 80218001768020158148207

theorem tailTrace_703008 : CollatzResearch.WordTrace tailWord_703008 prefixEnd_703008 80218001768020158148207 := by
  unfold tailWord_703008
  simp only [CollatzResearch.WordTrace]
  refine ⟨12820404118564777526354839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17093872158086370035139785 12820404118564777526354839)
  ·
    refine ⟨19230606177847166289532259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12820404118564777526354839 19230606177847166289532259)
    ·
      refine ⟨28845909266770749434298389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19230606177847166289532259 28845909266770749434298389)
      ·
        refine ⟨1352151996879878879732737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 28845909266770749434298389 1352151996879878879732737)
        ·
          refine ⟨1014113997659909159799553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1352151996879878879732737 1014113997659909159799553)
          ·
            refine ⟨760585498244931869849665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1014113997659909159799553 760585498244931869849665)
            ·
              refine ⟨570439123683698902387249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 760585498244931869849665 570439123683698902387249)
              ·
                refine ⟨427829342762774176790437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 570439123683698902387249 427829342762774176790437)
                ·
                  refine ⟨80218001768020158148207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 427829342762774176790437 80218001768020158148207)
                  ·
                    rfl

theorem cell22_703008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 2, 2, 4].length) (baseStart_703008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_703008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_703008 prefixEnd_703008 := by exact prefixLift 703008
  have htrace : WordTrace (prefixWord ++ tailWord_703008) baseStart_703008 baseEnd_703008 := by
    simpa [prefixWord, tailWord_703008, baseEnd_703008] using wordTrace_append hprefix tailTrace_703008
  have hstable : (prefixWord ++ tailWord_703008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703008).length < 2 ^ (prefixWord ++ tailWord_703008).sum := by decide
  have hdescent : baseEnd_703008 < baseStart_703008 := by decide
  rcases family_descends (prefixWord ++ tailWord_703008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703034 : List Nat := [3, 1, 1, 1, 3, 4, 1, 2, 3, 3]
def baseStart_703034 : Nat := 118140960795 + 703034 * 2 ^ 59
def prefixEnd_703034 : Nat := 4983230072969 + 3 ^ 40 * 703034 * 2
def baseEnd_703034 : Nat := 240662905635405073294541

theorem tailTrace_703034 : CollatzResearch.WordTrace tailWord_703034 prefixEnd_703034 240662905635405073294541 := by
  unfold tailWord_703034
  simp only [CollatzResearch.WordTrace]
  refine ⟨6410439133758840373289039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17094504356690240995437437 6410439133758840373289039)
  ·
    refine ⟨9615658700638260559933559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6410439133758840373289039 9615658700638260559933559)
    ·
      refine ⟨14423488050957390839900339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9615658700638260559933559 14423488050957390839900339)
      ·
        refine ⟨21635232076436086259850509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14423488050957390839900339 21635232076436086259850509)
        ·
          refine ⟨8113212028663532347443941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21635232076436086259850509 8113212028663532347443941)
          ·
            refine ⟨1521227255374412315145739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8113212028663532347443941 1521227255374412315145739)
            ·
              refine ⟨2281840883061618472718609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1521227255374412315145739 2281840883061618472718609)
              ·
                refine ⟨1711380662296213854538957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2281840883061618472718609 1711380662296213854538957)
                ·
                  refine ⟨641767748361080195452109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1711380662296213854538957 641767748361080195452109)
                  ·
                    refine ⟨240662905635405073294541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 641767748361080195452109 240662905635405073294541)
                    ·
                      rfl

theorem cell22_703034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 2, 3, 3].length) (baseStart_703034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_703034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_703034 prefixEnd_703034 := by exact prefixLift 703034
  have htrace : WordTrace (prefixWord ++ tailWord_703034) baseStart_703034 baseEnd_703034 := by
    simpa [prefixWord, tailWord_703034, baseEnd_703034] using wordTrace_append hprefix tailTrace_703034
  have hstable : (prefixWord ++ tailWord_703034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703034).length < 2 ^ (prefixWord ++ tailWord_703034).sum := by decide
  have hdescent : baseEnd_703034 < baseStart_703034 := by decide
  rcases family_descends (prefixWord ++ tailWord_703034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703038 : List Nat := [4, 2, 1, 4, 1, 2, 1, 1, 2, 4]
def baseStart_703038 : Nat := 118140960795 + 703038 * 2 ^ 59
def prefixEnd_703038 : Nat := 4983230072969 + 3 ^ 40 * 703038 * 2
def baseEnd_703038 : Nat := 240664274917150396194529

theorem tailTrace_703038 : CollatzResearch.WordTrace tailWord_703038 prefixEnd_703038 240664274917150396194529 := by
  unfold tailWord_703038
  simp only [CollatzResearch.WordTrace]
  refine ⟨3205237803377608772037721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17094601618013913450867845 3205237803377608772037721)
  ·
    refine ⟨2403928352533206579028291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3205237803377608772037721 2403928352533206579028291)
    ·
      refine ⟨3605892528799809868542437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2403928352533206579028291 3605892528799809868542437)
      ·
        refine ⟨676104849149964350351707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3605892528799809868542437 676104849149964350351707)
        ·
          refine ⟨1014157273724946525527561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 676104849149964350351707 1014157273724946525527561)
          ·
            refine ⟨760617955293709894145671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1014157273724946525527561 760617955293709894145671)
            ·
              refine ⟨1140926932940564841218507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 760617955293709894145671 1140926932940564841218507)
              ·
                refine ⟨1711390399410847261827761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1140926932940564841218507 1711390399410847261827761)
                ·
                  refine ⟨1283542799558135446370821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1711390399410847261827761 1283542799558135446370821)
                  ·
                    refine ⟨240664274917150396194529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1283542799558135446370821 240664274917150396194529)
                    ·
                      rfl

theorem cell22_703038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 1, 1, 2, 4].length) (baseStart_703038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_703038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_703038 prefixEnd_703038 := by exact prefixLift 703038
  have htrace : WordTrace (prefixWord ++ tailWord_703038) baseStart_703038 baseEnd_703038 := by
    simpa [prefixWord, tailWord_703038, baseEnd_703038] using wordTrace_append hprefix tailTrace_703038
  have hstable : (prefixWord ++ tailWord_703038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703038).length < 2 ^ (prefixWord ++ tailWord_703038).sum := by decide
  have hdescent : baseEnd_703038 < baseStart_703038 := by decide
  rcases family_descends (prefixWord ++ tailWord_703038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703107 : List Nat := [1, 1, 1, 3, 3, 1, 2, 4, 1, 5]
def baseStart_703107 : Nat := 118140960795 + 703107 * 2 ^ 59
def prefixEnd_703107 : Nat := 4983230072969 + 3 ^ 40 * 703107 * 2
def baseEnd_703107 : Nat := 240687895027257216219317

theorem tailTrace_703107 : CollatzResearch.WordTrace tailWord_703107 prefixEnd_703107 240687895027257216219317 := by
  unfold tailWord_703107
  simp only [CollatzResearch.WordTrace]
  refine ⟨25644419063770894960563575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17096279375847263307042383 25644419063770894960563575)
  ·
    refine ⟨38466628595656342440845363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25644419063770894960563575 38466628595656342440845363)
    ·
      refine ⟨57699942893484513661268045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38466628595656342440845363 57699942893484513661268045)
      ·
        refine ⟨21637478585056692622975517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57699942893484513661268045 21637478585056692622975517)
        ·
          refine ⟨8114054469396259733615819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21637478585056692622975517 8114054469396259733615819)
          ·
            refine ⟨12171081704094389600423729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8114054469396259733615819 12171081704094389600423729)
            ·
              refine ⟨9128311278070792200317797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12171081704094389600423729 9128311278070792200317797)
              ·
                refine ⟨1711558364638273537559587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9128311278070792200317797 1711558364638273537559587)
                ·
                  refine ⟨2567337546957410306339381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1711558364638273537559587 2567337546957410306339381)
                  ·
                    refine ⟨240687895027257216219317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2567337546957410306339381 240687895027257216219317)
                    ·
                      rfl

theorem cell22_703107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 4, 1, 5].length) (baseStart_703107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_703107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_703107 prefixEnd_703107 := by exact prefixLift 703107
  have htrace : WordTrace (prefixWord ++ tailWord_703107) baseStart_703107 baseEnd_703107 := by
    simpa [prefixWord, tailWord_703107, baseEnd_703107] using wordTrace_append hprefix tailTrace_703107
  have hstable : (prefixWord ++ tailWord_703107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703107).length < 2 ^ (prefixWord ++ tailWord_703107).sum := by decide
  have hdescent : baseEnd_703107 < baseStart_703107 := by decide
  rcases family_descends (prefixWord ++ tailWord_703107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703158 : List Nat := [5, 1, 3, 1, 2, 1, 1, 2, 1, 5]
def baseStart_703158 : Nat := 118140960795 + 703158 * 2 ^ 59
def prefixEnd_703158 : Nat := 4983230072969 + 3 ^ 40 * 703158 * 2
def baseEnd_703158 : Nat := 240705353369510083194161

theorem tailTrace_703158 : CollatzResearch.WordTrace tailWord_703158 prefixEnd_703158 240705353369510083194161 := by
  unfold tailWord_703158
  simp only [CollatzResearch.WordTrace]
  refine ⟨1602892449161633166916883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17097519457724087113780085 1602892449161633166916883)
  ·
    refine ⟨2404338673742449750375325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1602892449161633166916883 2404338673742449750375325)
    ·
      refine ⟨901627002653418656390747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2404338673742449750375325 901627002653418656390747)
      ·
        refine ⟨1352440503980127984586121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 901627002653418656390747 1352440503980127984586121)
        ·
          refine ⟨1014330377985095988439591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1352440503980127984586121 1014330377985095988439591)
          ·
            refine ⟨1521495566977643982659387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1014330377985095988439591 1521495566977643982659387)
            ·
              refine ⟨2282243350466465973989081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1521495566977643982659387 2282243350466465973989081)
              ·
                refine ⟨1711682512849849480491811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2282243350466465973989081 1711682512849849480491811)
                ·
                  refine ⟨2567523769274774220737717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1711682512849849480491811 2567523769274774220737717)
                  ·
                    refine ⟨240705353369510083194161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2567523769274774220737717 240705353369510083194161)
                    ·
                      rfl

theorem cell22_703158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_703158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_703158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_703158 prefixEnd_703158 := by exact prefixLift 703158
  have htrace : WordTrace (prefixWord ++ tailWord_703158) baseStart_703158 baseEnd_703158 := by
    simpa [prefixWord, tailWord_703158, baseEnd_703158] using wordTrace_append hprefix tailTrace_703158
  have hstable : (prefixWord ++ tailWord_703158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703158).length < 2 ^ (prefixWord ++ tailWord_703158).sum := by decide
  have hdescent : baseEnd_703158 < baseStart_703158 := by decide
  rcases family_descends (prefixWord ++ tailWord_703158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703188 : List Nat := [2, 4, 1, 3, 3, 1, 1, 7]
def baseStart_703188 : Nat := 118140960795 + 703188 * 2 ^ 59
def prefixEnd_703188 : Nat := 4983230072969 + 3 ^ 40 * 703188 * 2
def baseEnd_703188 : Nat := 26746180331400000549341

theorem tailTrace_703188 : CollatzResearch.WordTrace tailWord_703188 prefixEnd_703188 26746180331400000549341 := by
  unfold tailWord_703188
  simp only [CollatzResearch.WordTrace]
  refine ⟨12823686688238722897131109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17098248917651630529508145 12823686688238722897131109)
  ·
    refine ⟨2404441254044760543212083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12823686688238722897131109 2404441254044760543212083)
    ·
      refine ⟨3606661881067140814818125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2404441254044760543212083 3606661881067140814818125)
      ·
        refine ⟨1352498205400177805556797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3606661881067140814818125 1352498205400177805556797)
        ·
          refine ⟨507186827025066677083799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1352498205400177805556797 507186827025066677083799)
          ·
            refine ⟨760780240537600015625699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 507186827025066677083799 760780240537600015625699)
            ·
              refine ⟨1141170360806400023438549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 760780240537600015625699 1141170360806400023438549)
              ·
                refine ⟨26746180331400000549341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1141170360806400023438549 26746180331400000549341)
                ·
                  rfl

theorem cell22_703188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 1, 7].length) (baseStart_703188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_703188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_703188 prefixEnd_703188 := by exact prefixLift 703188
  have htrace : WordTrace (prefixWord ++ tailWord_703188) baseStart_703188 baseEnd_703188 := by
    simpa [prefixWord, tailWord_703188, baseEnd_703188] using wordTrace_append hprefix tailTrace_703188
  have hstable : (prefixWord ++ tailWord_703188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703188).length < 2 ^ (prefixWord ++ tailWord_703188).sum := by decide
  have hdescent : baseEnd_703188 < baseStart_703188 := by decide
  rcases family_descends (prefixWord ++ tailWord_703188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703199 : List Nat := [1, 1, 2, 3, 2, 3, 2, 3, 5]
def baseStart_703199 : Nat := 118140960795 + 703199 * 2 ^ 59
def prefixEnd_703199 : Nat := 4983230072969 + 3 ^ 40 * 703199 * 2
def baseEnd_703199 : Nat := 80239796169133214306345

theorem tailTrace_703199 : CollatzResearch.WordTrace tailWord_703199 prefixEnd_703199 80239796169133214306345 := by
  unfold tailWord_703199
  simp only [CollatzResearch.WordTrace]
  refine ⟨25647774579437594672912651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17098516386291729781941767 25647774579437594672912651)
  ·
    refine ⟨38471661869156392009368977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25647774579437594672912651 38471661869156392009368977)
    ·
      refine ⟨28853746401867294007026733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38471661869156392009368977 28853746401867294007026733)
      ·
        refine ⟨10820154900700235252635025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28853746401867294007026733 10820154900700235252635025)
        ·
          refine ⟨8115116175525176439476269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10820154900700235252635025 8115116175525176439476269)
          ·
            refine ⟨3043168565821941164803601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8115116175525176439476269 3043168565821941164803601)
            ·
              refine ⟨2282376424366455873602701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3043168565821941164803601 2282376424366455873602701)
              ·
                refine ⟨855891159137420952601013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2282376424366455873602701 855891159137420952601013)
                ·
                  refine ⟨80239796169133214306345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 855891159137420952601013 80239796169133214306345)
                  ·
                    rfl

theorem cell22_703199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 3, 5].length) (baseStart_703199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_703199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_703199 prefixEnd_703199 := by exact prefixLift 703199
  have htrace : WordTrace (prefixWord ++ tailWord_703199) baseStart_703199 baseEnd_703199 := by
    simpa [prefixWord, tailWord_703199, baseEnd_703199] using wordTrace_append hprefix tailTrace_703199
  have hstable : (prefixWord ++ tailWord_703199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703199).length < 2 ^ (prefixWord ++ tailWord_703199).sum := by decide
  have hdescent : baseEnd_703199 < baseStart_703199 := by decide
  rcases family_descends (prefixWord ++ tailWord_703199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703250 : List Nat := [3, 2, 4, 1, 2, 1, 3, 1, 5]
def baseStart_703250 : Nat := 118140960795 + 703250 * 2 ^ 59
def prefixEnd_703250 : Nat := 4983230072969 + 3 ^ 40 * 703250 * 2
def baseEnd_703250 : Nat := 80245615616550836631293

theorem tailTrace_703250 : CollatzResearch.WordTrace tailWord_703250 prefixEnd_703250 80245615616550836631293 := by
  unfold tailWord_703250
  simp only [CollatzResearch.WordTrace]
  refine ⟨6412408675563207595754801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17099756468168553588679469 6412408675563207595754801)
  ·
    refine ⟨4809306506672405696816101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6412408675563207595754801 4809306506672405696816101)
    ·
      refine ⟨901744970001076068153019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4809306506672405696816101 901744970001076068153019)
      ·
        refine ⟨1352617455001614102229529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 901744970001076068153019 1352617455001614102229529)
        ·
          refine ⟨1014463091251210576672147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1352617455001614102229529 1014463091251210576672147)
          ·
            refine ⟨1521694636876815865008221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1014463091251210576672147 1521694636876815865008221)
            ·
              refine ⟨570635488828805949378083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1521694636876815865008221 570635488828805949378083)
              ·
                refine ⟨855953233243208924067125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 570635488828805949378083 855953233243208924067125)
                ·
                  refine ⟨80245615616550836631293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 855953233243208924067125 80245615616550836631293)
                  ·
                    rfl

theorem cell22_703250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 3, 1, 5].length) (baseStart_703250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_703250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_703250 prefixEnd_703250 := by exact prefixLift 703250
  have htrace : WordTrace (prefixWord ++ tailWord_703250) baseStart_703250 baseEnd_703250 := by
    simpa [prefixWord, tailWord_703250, baseEnd_703250] using wordTrace_append hprefix tailTrace_703250
  have hstable : (prefixWord ++ tailWord_703250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703250).length < 2 ^ (prefixWord ++ tailWord_703250).sum := by decide
  have hdescent : baseEnd_703250 < baseStart_703250 := by decide
  rcases family_descends (prefixWord ++ tailWord_703250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703259 : List Nat := [1, 1, 1, 1, 1, 1, 4, 1, 8, 3]
def baseStart_703259 : Nat := 118140960795 + 703259 * 2 ^ 59
def prefixEnd_703259 : Nat := 4983230072969 + 3 ^ 40 * 703259 * 2
def baseEnd_703259 : Nat := 240739927733579486418851

theorem tailTrace_703259 : CollatzResearch.WordTrace tailWord_703259 prefixEnd_703259 240739927733579486418851 := by
  unfold tailWord_703259
  simp only [CollatzResearch.WordTrace]
  refine ⟨25649962959220224920096831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17099975306146816613397887 25649962959220224920096831)
  ·
    refine ⟨38474944438830337380145247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25649962959220224920096831 38474944438830337380145247)
    ·
      refine ⟨57712416658245506070217871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38474944438830337380145247 57712416658245506070217871)
      ·
        refine ⟨86568624987368259105326807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57712416658245506070217871 86568624987368259105326807)
        ·
          refine ⟨129852937481052388657990211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86568624987368259105326807 129852937481052388657990211)
          ·
            refine ⟨194779406221578582986985317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129852937481052388657990211 194779406221578582986985317)
            ·
              refine ⟨36521138666545984310059747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 194779406221578582986985317 36521138666545984310059747)
              ·
                refine ⟨54781707999818976465089621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36521138666545984310059747 54781707999818976465089621)
                ·
                  refine ⟨641973140622878630450269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 54781707999818976465089621 641973140622878630450269)
                  ·
                    refine ⟨240739927733579486418851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 641973140622878630450269 240739927733579486418851)
                    ·
                      rfl

theorem cell22_703259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 8, 3].length) (baseStart_703259 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_703259 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_703259 prefixEnd_703259 := by exact prefixLift 703259
  have htrace : WordTrace (prefixWord ++ tailWord_703259) baseStart_703259 baseEnd_703259 := by
    simpa [prefixWord, tailWord_703259, baseEnd_703259] using wordTrace_append hprefix tailTrace_703259
  have hstable : (prefixWord ++ tailWord_703259).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703259).length < 2 ^ (prefixWord ++ tailWord_703259).sum := by decide
  have hdescent : baseEnd_703259 < baseStart_703259 := by decide
  rcases family_descends (prefixWord ++ tailWord_703259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703355 : List Nat := [1, 1, 1, 1, 1, 5, 6, 2, 1, 3]
def baseStart_703355 : Nat := 118140960795 + 703355 * 2 ^ 59
def prefixEnd_703355 : Nat := 4983230072969 + 3 ^ 40 * 703355 * 2
def baseEnd_703355 : Nat := 240772790495467236018557

theorem tailTrace_703355 : CollatzResearch.WordTrace tailWord_703355 prefixEnd_703355 240772790495467236018557 := by
  unfold tailWord_703355
  simp only [CollatzResearch.WordTrace]
  refine ⟨25653464366872433315591519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17102309577914955543727679 25653464366872433315591519)
  ·
    refine ⟨38480196550308649973387279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25653464366872433315591519 38480196550308649973387279)
    ·
      refine ⟨57720294825462974960080919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38480196550308649973387279 57720294825462974960080919)
      ·
        refine ⟨86580442238194462440121379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57720294825462974960080919 86580442238194462440121379)
        ·
          refine ⟨129870663357291693660182069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86580442238194462440121379 129870663357291693660182069)
          ·
            refine ⟨12175374689746096280642069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 129870663357291693660182069 12175374689746096280642069)
            ·
              refine ⟨570720688581848263155097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 12175374689746096280642069 570720688581848263155097)
              ·
                refine ⟨428040516436386197366323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 570720688581848263155097 428040516436386197366323)
                ·
                  refine ⟨642060774654579296049485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 428040516436386197366323 642060774654579296049485)
                  ·
                    refine ⟨240772790495467236018557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 642060774654579296049485 240772790495467236018557)
                    ·
                      rfl

theorem cell22_703355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 6, 2, 1, 3].length) (baseStart_703355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_703355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_703355 prefixEnd_703355 := by exact prefixLift 703355
  have htrace : WordTrace (prefixWord ++ tailWord_703355) baseStart_703355 baseEnd_703355 := by
    simpa [prefixWord, tailWord_703355, baseEnd_703355] using wordTrace_append hprefix tailTrace_703355
  have hstable : (prefixWord ++ tailWord_703355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703355).length < 2 ^ (prefixWord ++ tailWord_703355).sum := by decide
  have hdescent : baseEnd_703355 < baseStart_703355 := by decide
  rcases family_descends (prefixWord ++ tailWord_703355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703381 : List Nat := [1, 3, 2, 1, 1, 4, 2, 1, 3, 4]
def baseStart_703381 : Nat := 118140960795 + 703381 * 2 ^ 59
def prefixEnd_703381 : Nat := 4983230072969 + 3 ^ 40 * 703381 * 2
def baseEnd_703381 : Nat := 240781690826811834868477

theorem tailTrace_703381 : CollatzResearch.WordTrace tailWord_703381 prefixEnd_703381 240781690826811834868477 := by
  unfold tailWord_703381
  simp only [CollatzResearch.WordTrace]
  refine ⟨25654412664778239756037997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17102941776518826504025331 25654412664778239756037997)
  ·
    refine ⟨9620404749291839908514249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25654412664778239756037997 9620404749291839908514249)
    ·
      refine ⟨7215303561968879931385687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9620404749291839908514249 7215303561968879931385687)
      ·
        refine ⟨10822955342953319897078531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7215303561968879931385687 10822955342953319897078531)
        ·
          refine ⟨16234433014429979845617797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10822955342953319897078531 16234433014429979845617797)
          ·
            refine ⟨3043956190205621221053337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16234433014429979845617797 3043956190205621221053337)
            ·
              refine ⟨2282967142654215915790003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3043956190205621221053337 2282967142654215915790003)
              ·
                refine ⟨3424450713981323873685005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2282967142654215915790003 3424450713981323873685005)
                ·
                  refine ⟨1284169017742996452631877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3424450713981323873685005 1284169017742996452631877)
                  ·
                    refine ⟨240781690826811834868477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1284169017742996452631877 240781690826811834868477)
                    ·
                      rfl

theorem cell22_703381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 1, 3, 4].length) (baseStart_703381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_703381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_703381 prefixEnd_703381 := by exact prefixLift 703381
  have htrace : WordTrace (prefixWord ++ tailWord_703381) baseStart_703381 baseEnd_703381 := by
    simpa [prefixWord, tailWord_703381, baseEnd_703381] using wordTrace_append hprefix tailTrace_703381
  have hstable : (prefixWord ++ tailWord_703381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703381).length < 2 ^ (prefixWord ++ tailWord_703381).sum := by decide
  have hdescent : baseEnd_703381 < baseStart_703381 := by decide
  rcases family_descends (prefixWord ++ tailWord_703381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703413 : List Nat := [1, 3, 3, 2, 1, 1, 1, 6, 4]
def baseStart_703413 : Nat := 118140960795 + 703413 * 2 ^ 59
def prefixEnd_703413 : Nat := 4983230072969 + 3 ^ 40 * 703413 * 2
def baseEnd_703413 : Nat := 80264215026924806022793

theorem tailTrace_703413 : CollatzResearch.WordTrace tailWord_703413 prefixEnd_703413 80264215026924806022793 := by
  unfold tailWord_703413
  simp only [CollatzResearch.WordTrace]
  refine ⟨25655579800662309221202893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17103719867108206147468595 25655579800662309221202893)
  ·
    refine ⟨9620842425248365957951085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25655579800662309221202893 9620842425248365957951085)
    ·
      refine ⟨3607815909468137234231657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9620842425248365957951085 3607815909468137234231657)
      ·
        refine ⟨2705861932101102925673743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3607815909468137234231657 2705861932101102925673743)
        ·
          refine ⟨4058792898151654388510615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2705861932101102925673743 4058792898151654388510615)
          ·
            refine ⟨6088189347227481582765923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4058792898151654388510615 6088189347227481582765923)
            ·
              refine ⟨9132284020841222374148885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6088189347227481582765923 9132284020841222374148885)
              ·
                refine ⟨428075813476932298788229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9132284020841222374148885 428075813476932298788229)
                ·
                  refine ⟨80264215026924806022793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 428075813476932298788229 80264215026924806022793)
                  ·
                    rfl

theorem cell22_703413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 6, 4].length) (baseStart_703413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_703413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_703413 prefixEnd_703413 := by exact prefixLift 703413
  have htrace : WordTrace (prefixWord ++ tailWord_703413) baseStart_703413 baseEnd_703413 := by
    simpa [prefixWord, tailWord_703413, baseEnd_703413] using wordTrace_append hprefix tailTrace_703413
  have hstable : (prefixWord ++ tailWord_703413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703413).length < 2 ^ (prefixWord ++ tailWord_703413).sum := by decide
  have hdescent : baseEnd_703413 < baseStart_703413 := by decide
  rcases family_descends (prefixWord ++ tailWord_703413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703458 : List Nat := [3, 3, 3, 1, 1, 1, 10]
def baseStart_703458 : Nat := 118140960795 + 703458 * 2 ^ 59
def prefixEnd_703458 : Nat := 4983230072969 + 3 ^ 40 * 703458 * 2
def baseEnd_703458 : Nat := 8918816648163307433083

theorem tailTrace_703458 : CollatzResearch.WordTrace tailWord_703458 prefixEnd_703458 8918816648163307433083 := by
  unfold tailWord_703458
  simp only [CollatzResearch.WordTrace]
  refine ⟨6414305271374820476647757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17104814056999521271060685 6414305271374820476647757)
  ·
    refine ⟨2405364476765557678742909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6414305271374820476647757 2405364476765557678742909)
    ·
      refine ⟨902011678787084129528591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2405364476765557678742909 902011678787084129528591)
      ·
        refine ⟨1353017518180626194292887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 902011678787084129528591 1353017518180626194292887)
        ·
          refine ⟨2029526277270939291439331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1353017518180626194292887 2029526277270939291439331)
          ·
            refine ⟨3044289415906408937158997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2029526277270939291439331 3044289415906408937158997)
            ·
              refine ⟨8918816648163307433083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 3044289415906408937158997 8918816648163307433083)
              ·
                rfl

theorem cell22_703458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 10].length) (baseStart_703458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_703458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_703458 prefixEnd_703458 := by exact prefixLift 703458
  have htrace : WordTrace (prefixWord ++ tailWord_703458) baseStart_703458 baseEnd_703458 := by
    simpa [prefixWord, tailWord_703458, baseEnd_703458] using wordTrace_append hprefix tailTrace_703458
  have hstable : (prefixWord ++ tailWord_703458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703458).length < 2 ^ (prefixWord ++ tailWord_703458).sum := by decide
  have hdescent : baseEnd_703458 < baseStart_703458 := by decide
  rcases family_descends (prefixWord ++ tailWord_703458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703524 : List Nat := [2, 3, 1, 4, 1, 1, 4, 2, 1, 3]
def baseStart_703524 : Nat := 118140960795 + 703524 * 2 ^ 59
def prefixEnd_703524 : Nat := 4983230072969 + 3 ^ 40 * 703524 * 2
def baseEnd_703524 : Nat := 240830642649207128543039

theorem tailTrace_703524 : CollatzResearch.WordTrace tailWord_703524 prefixEnd_703524 240830642649207128543039 := by
  unfold tailWord_703524
  simp only [CollatzResearch.WordTrace]
  refine ⟨12829814151630087589246813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17106418868840116785662417 12829814151630087589246813)
  ·
    refine ⟨4811180306861282845967555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12829814151630087589246813 4811180306861282845967555)
    ·
      refine ⟨7216770460291924268951333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4811180306861282845967555 7216770460291924268951333)
      ·
        refine ⟨1353144461304735800428375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7216770460291924268951333 1353144461304735800428375)
        ·
          refine ⟨2029716691957103700642563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1353144461304735800428375 2029716691957103700642563)
          ·
            refine ⟨3044575037935655550963845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2029716691957103700642563 3044575037935655550963845)
            ·
              refine ⟨570857819612935415805721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3044575037935655550963845 570857819612935415805721)
              ·
                refine ⟨428143364709701561854291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 570857819612935415805721 428143364709701561854291)
                ·
                  refine ⟨642215047064552342781437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 428143364709701561854291 642215047064552342781437)
                  ·
                    refine ⟨240830642649207128543039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 642215047064552342781437 240830642649207128543039)
                    ·
                      rfl

theorem cell22_703524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 4, 2, 1, 3].length) (baseStart_703524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_703524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_703524 prefixEnd_703524 := by exact prefixLift 703524
  have htrace : WordTrace (prefixWord ++ tailWord_703524) baseStart_703524 baseEnd_703524 := by
    simpa [prefixWord, tailWord_703524, baseEnd_703524] using wordTrace_append hprefix tailTrace_703524
  have hstable : (prefixWord ++ tailWord_703524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703524).length < 2 ^ (prefixWord ++ tailWord_703524).sum := by decide
  have hdescent : baseEnd_703524 < baseStart_703524 := by decide
  rcases family_descends (prefixWord ++ tailWord_703524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703531 : List Nat := [1, 1, 1, 1, 2, 1, 6, 3, 6]
def baseStart_703531 : Nat := 118140960795 + 703531 * 2 ^ 59
def prefixEnd_703531 : Nat := 4983230072969 + 3 ^ 40 * 703531 * 2
def baseEnd_703531 : Nat := 80277679630753814539339

theorem tailTrace_703531 : CollatzResearch.WordTrace tailWord_703531 prefixEnd_703531 80277679630753814539339 := by
  unfold tailWord_703531
  simp only [CollatzResearch.WordTrace]
  refine ⟨25659883614234815373998447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17106589076156543582665631 25659883614234815373998447)
  ·
    refine ⟨38489825421352223060997671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25659883614234815373998447 38489825421352223060997671)
    ·
      refine ⟨57734738132028334591496507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38489825421352223060997671 57734738132028334591496507)
      ·
        refine ⟨86602107198042501887244761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57734738132028334591496507 86602107198042501887244761)
        ·
          refine ⟨64951580398531876415433571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86602107198042501887244761 64951580398531876415433571)
          ·
            refine ⟨97427370597797814623150357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64951580398531876415433571 97427370597797814623150357)
            ·
              refine ⟨4566907996771772560460173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 97427370597797814623150357 4566907996771772560460173)
              ·
                refine ⟨1712590498789414710172565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4566907996771772560460173 1712590498789414710172565)
                ·
                  refine ⟨80277679630753814539339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1712590498789414710172565 80277679630753814539339)
                  ·
                    rfl

theorem cell22_703531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 3, 6].length) (baseStart_703531 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_703531 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_703531 prefixEnd_703531 := by exact prefixLift 703531
  have htrace : WordTrace (prefixWord ++ tailWord_703531) baseStart_703531 baseEnd_703531 := by
    simpa [prefixWord, tailWord_703531, baseEnd_703531] using wordTrace_append hprefix tailTrace_703531
  have hstable : (prefixWord ++ tailWord_703531).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703531).length < 2 ^ (prefixWord ++ tailWord_703531).sum := by decide
  have hdescent : baseEnd_703531 < baseStart_703531 := by decide
  rcases family_descends (prefixWord ++ tailWord_703531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703548 : List Nat := [2, 2, 2, 2, 2, 3, 1, 2, 6]
def baseStart_703548 : Nat := 118140960795 + 703548 * 2 ^ 59
def prefixEnd_703548 : Nat := 4983230072969 + 3 ^ 40 * 703548 * 2
def baseEnd_703548 : Nat := 80279619446559688647655

theorem tailTrace_703548 : CollatzResearch.WordTrace tailWord_703548 prefixEnd_703548 80279619446559688647655 := by
  unfold tailWord_703548
  simp only [CollatzResearch.WordTrace]
  refine ⟨12830251827586613638683649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17107002436782151518244865 12830251827586613638683649)
  ·
    refine ⟨9622688870689960229012737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12830251827586613638683649 9622688870689960229012737)
    ·
      refine ⟨7217016653017470171759553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9622688870689960229012737 7217016653017470171759553)
      ·
        refine ⟨5412762489763102628819665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7217016653017470171759553 5412762489763102628819665)
        ·
          refine ⟨4059571867322326971614749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5412762489763102628819665 4059571867322326971614749)
          ·
            refine ⟨1522339450245872614355531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4059571867322326971614749 1522339450245872614355531)
            ·
              refine ⟨2283509175368808921533297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1522339450245872614355531 2283509175368808921533297)
              ·
                refine ⟨1712631881526606691149973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2283509175368808921533297 1712631881526606691149973)
                ·
                  refine ⟨80279619446559688647655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1712631881526606691149973 80279619446559688647655)
                  ·
                    rfl

theorem cell22_703548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 2, 6].length) (baseStart_703548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_703548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_703548 prefixEnd_703548 := by exact prefixLift 703548
  have htrace : WordTrace (prefixWord ++ tailWord_703548) baseStart_703548 baseEnd_703548 := by
    simpa [prefixWord, tailWord_703548, baseEnd_703548] using wordTrace_append hprefix tailTrace_703548
  have hstable : (prefixWord ++ tailWord_703548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703548).length < 2 ^ (prefixWord ++ tailWord_703548).sum := by decide
  have hdescent : baseEnd_703548 < baseStart_703548 := by decide
  rcases family_descends (prefixWord ++ tailWord_703548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703550 : List Nat := [4, 2, 1, 3, 1, 1, 2, 1, 3, 4]
def baseStart_703550 : Nat := 118140960795 + 703550 * 2 ^ 59
def prefixEnd_703550 : Nat := 4983230072969 + 3 ^ 40 * 703550 * 2
def baseEnd_703550 : Nat := 240839542980551727392959

theorem tailTrace_703550 : CollatzResearch.WordTrace tailWord_703550 prefixEnd_703550 240839542980551727392959 := by
  unfold tailWord_703550
  simp only [CollatzResearch.WordTrace]
  refine ⟨3207572075145747702367513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17107051067443987745960069 3207572075145747702367513)
  ·
    refine ⟨2405679056359310776775635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3207572075145747702367513 2405679056359310776775635)
    ·
      refine ⟨3608518584538966165163453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2405679056359310776775635 3608518584538966165163453)
      ·
        refine ⟨1353194469202112311936295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3608518584538966165163453 1353194469202112311936295)
        ·
          refine ⟨2029791703803168467904443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1353194469202112311936295 2029791703803168467904443)
          ·
            refine ⟨3044687555704752701856665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2029791703803168467904443 3044687555704752701856665)
            ·
              refine ⟨2283515666778564526392499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3044687555704752701856665 2283515666778564526392499)
              ·
                refine ⟨3425273500167846789588749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2283515666778564526392499 3425273500167846789588749)
                ·
                  refine ⟨1284477562562942546095781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3425273500167846789588749 1284477562562942546095781)
                  ·
                    refine ⟨240839542980551727392959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1284477562562942546095781 240839542980551727392959)
                    ·
                      rfl

theorem cell22_703550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 1, 3, 4].length) (baseStart_703550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_703550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_703550 prefixEnd_703550 := by exact prefixLift 703550
  have htrace : WordTrace (prefixWord ++ tailWord_703550) baseStart_703550 baseEnd_703550 := by
    simpa [prefixWord, tailWord_703550, baseEnd_703550] using wordTrace_append hprefix tailTrace_703550
  have hstable : (prefixWord ++ tailWord_703550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703550).length < 2 ^ (prefixWord ++ tailWord_703550).sum := by decide
  have hdescent : baseEnd_703550 < baseStart_703550 := by decide
  rcases family_descends (prefixWord ++ tailWord_703550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703576 : List Nat := [2, 1, 2, 2, 1, 3, 11]
def baseStart_703576 : Nat := 118140960795 + 703576 * 2 ^ 59
def prefixEnd_703576 : Nat := 4983230072969 + 3 ^ 40 * 703576 * 2
def baseEnd_703576 : Nat := 8920312715255419490477

theorem tailTrace_703576 : CollatzResearch.WordTrace tailWord_703576 prefixEnd_703576 8920312715255419490477 := by
  unfold tailWord_703576
  simp only [CollatzResearch.WordTrace]
  refine ⟨12830762449535894029693291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17107683266047858706257721 12830762449535894029693291)
  ·
    refine ⟨19246143674303841044539937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12830762449535894029693291 19246143674303841044539937)
    ·
      refine ⟨14434607755727880783404953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19246143674303841044539937 14434607755727880783404953)
      ·
        refine ⟨10825955816795910587553715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14434607755727880783404953 10825955816795910587553715)
        ·
          refine ⟨16238933725193865881330573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10825955816795910587553715 16238933725193865881330573)
          ·
            refine ⟨6089600146947699705498965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16238933725193865881330573 6089600146947699705498965)
            ·
              refine ⟨8920312715255419490477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 6089600146947699705498965 8920312715255419490477)
              ·
                rfl

theorem cell22_703576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 11].length) (baseStart_703576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_703576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_703576 prefixEnd_703576 := by exact prefixLift 703576
  have htrace : WordTrace (prefixWord ++ tailWord_703576) baseStart_703576 baseEnd_703576 := by
    simpa [prefixWord, tailWord_703576, baseEnd_703576] using wordTrace_append hprefix tailTrace_703576
  have hstable : (prefixWord ++ tailWord_703576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703576).length < 2 ^ (prefixWord ++ tailWord_703576).sum := by decide
  have hdescent : baseEnd_703576 < baseStart_703576 := by decide
  rcases family_descends (prefixWord ++ tailWord_703576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703580 : List Nat := [2, 2, 4, 1, 1, 1, 3, 1, 4, 3]
def baseStart_703580 : Nat := 118140960795 + 703580 * 2 ^ 59
def prefixEnd_703580 : Nat := 4983230072969 + 3 ^ 40 * 703580 * 2
def baseEnd_703580 : Nat := 240849812593641649142867

theorem tailTrace_703580 : CollatzResearch.WordTrace tailWord_703580 prefixEnd_703580 240849812593641649142867 := by
  unfold tailWord_703580
  simp only [CollatzResearch.WordTrace]
  refine ⟨12830835395528648371266097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17107780527371531161688129 12830835395528648371266097)
  ·
    refine ⟨9623126546646486278449573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12830835395528648371266097 9623126546646486278449573)
    ·
      refine ⟨1804336227496216177209295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9623126546646486278449573 1804336227496216177209295)
      ·
        refine ⟨2706504341244324265813943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1804336227496216177209295 2706504341244324265813943)
        ·
          refine ⟨4059756511866486398720915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2706504341244324265813943 4059756511866486398720915)
          ·
            refine ⟨6089634767799729598081373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4059756511866486398720915 6089634767799729598081373)
            ·
              refine ⟨2283613037924898599280515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6089634767799729598081373 2283613037924898599280515)
              ·
                refine ⟨3425419556887347898920773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2283613037924898599280515 3425419556887347898920773)
                ·
                  refine ⟨642266166916377731047645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3425419556887347898920773 642266166916377731047645)
                  ·
                    refine ⟨240849812593641649142867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 642266166916377731047645 240849812593641649142867)
                    ·
                      rfl

theorem cell22_703580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 1, 4, 3].length) (baseStart_703580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_703580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_703580 prefixEnd_703580 := by exact prefixLift 703580
  have htrace : WordTrace (prefixWord ++ tailWord_703580) baseStart_703580 baseEnd_703580 := by
    simpa [prefixWord, tailWord_703580, baseEnd_703580] using wordTrace_append hprefix tailTrace_703580
  have hstable : (prefixWord ++ tailWord_703580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703580).length < 2 ^ (prefixWord ++ tailWord_703580).sum := by decide
  have hdescent : baseEnd_703580 < baseStart_703580 := by decide
  rcases family_descends (prefixWord ++ tailWord_703580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703582 : List Nat := [4, 4, 1, 1, 1, 1, 1, 3, 6]
def baseStart_703582 : Nat := 118140960795 + 703582 * 2 ^ 59
def prefixEnd_703582 : Nat := 4983230072969 + 3 ^ 40 * 703582 * 2
def baseEnd_703582 : Nat := 80283499078171436864287

theorem tailTrace_703582 : CollatzResearch.WordTrace tailWord_703582 prefixEnd_703582 80283499078171436864287 := by
  unfold tailWord_703582
  simp only [CollatzResearch.WordTrace]
  refine ⟨3207717967131256385513125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17107829158033367389403333 3207717967131256385513125)
  ·
    refine ⟨601447118837110572283711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3207717967131256385513125 601447118837110572283711)
    ·
      refine ⟨902170678255665858425567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 601447118837110572283711 902170678255665858425567)
      ·
        refine ⟨1353256017383498787638351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 902170678255665858425567 1353256017383498787638351)
        ·
          refine ⟨2029884026075248181457527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1353256017383498787638351 2029884026075248181457527)
          ·
            refine ⟨3044826039112872272186291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2029884026075248181457527 3044826039112872272186291)
            ·
              refine ⟨4567239058669308408279437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3044826039112872272186291 4567239058669308408279437)
              ·
                refine ⟨1712714647000990653104789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4567239058669308408279437 1712714647000990653104789)
                ·
                  refine ⟨80283499078171436864287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1712714647000990653104789 80283499078171436864287)
                  ·
                    rfl

theorem cell22_703582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_703582 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_703582 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_703582 prefixEnd_703582 := by exact prefixLift 703582
  have htrace : WordTrace (prefixWord ++ tailWord_703582) baseStart_703582 baseEnd_703582 := by
    simpa [prefixWord, tailWord_703582, baseEnd_703582] using wordTrace_append hprefix tailTrace_703582
  have hstable : (prefixWord ++ tailWord_703582).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703582).length < 2 ^ (prefixWord ++ tailWord_703582).sum := by decide
  have hdescent : baseEnd_703582 < baseStart_703582 := by decide
  rcases family_descends (prefixWord ++ tailWord_703582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703642 : List Nat := [3, 1, 1, 5, 1, 1, 3, 1, 3, 3]
def baseStart_703642 : Nat := 118140960795 + 703642 * 2 ^ 59
def prefixEnd_703642 : Nat := 4983230072969 + 3 ^ 40 * 703642 * 2
def baseEnd_703642 : Nat := 240871036460694154092677

theorem tailTrace_703642 : CollatzResearch.WordTrace tailWord_703642 prefixEnd_703642 240871036460694154092677 := by
  unfold tailWord_703642
  simp only [CollatzResearch.WordTrace]
  refine ⟨6415983029208170332822295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17109288077888454220859453 6415983029208170332822295)
  ·
    refine ⟨9623974543812255499233443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6415983029208170332822295 9623974543812255499233443)
    ·
      refine ⟨14435961815718383248850165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9623974543812255499233443 14435961815718383248850165)
      ·
        refine ⟨1353371420223598429579703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14435961815718383248850165 1353371420223598429579703)
        ·
          refine ⟨2030057130335397644369555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1353371420223598429579703 2030057130335397644369555)
          ·
            refine ⟨3045085695503096466554333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2030057130335397644369555 3045085695503096466554333)
            ·
              refine ⟨1141907135813661174957875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3045085695503096466554333 1141907135813661174957875)
              ·
                refine ⟨1712860703720491762436813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1141907135813661174957875 1712860703720491762436813)
                ·
                  refine ⟨642322763895184410913805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1712860703720491762436813 642322763895184410913805)
                  ·
                    refine ⟨240871036460694154092677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 642322763895184410913805 240871036460694154092677)
                    ·
                      rfl

theorem cell22_703642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 3, 1, 3, 3].length) (baseStart_703642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_703642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_703642 prefixEnd_703642 := by exact prefixLift 703642
  have htrace : WordTrace (prefixWord ++ tailWord_703642) baseStart_703642 baseEnd_703642 := by
    simpa [prefixWord, tailWord_703642, baseEnd_703642] using wordTrace_append hprefix tailTrace_703642
  have hstable : (prefixWord ++ tailWord_703642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703642).length < 2 ^ (prefixWord ++ tailWord_703642).sum := by decide
  have hdescent : baseEnd_703642 < baseStart_703642 := by decide
  rcases family_descends (prefixWord ++ tailWord_703642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703693 : List Nat := [1, 6, 2, 2, 1, 1, 1, 4, 1, 3]
def baseStart_703693 : Nat := 118140960795 + 703693 * 2 ^ 59
def prefixEnd_703693 : Nat := 4983230072969 + 3 ^ 40 * 703693 * 2
def baseEnd_703693 : Nat := 240888494802947021067521

theorem tailTrace_703693 : CollatzResearch.WordTrace tailWord_703693 prefixEnd_703693 240888494802947021067521 := by
  unfold tailWord_703693
  simp only [CollatzResearch.WordTrace]
  refine ⟨25665792239647917041395733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17110528159765278027597155 25665792239647917041395733)
  ·
    refine ⟨1203084011233496111315425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 25665792239647917041395733 1203084011233496111315425)
    ·
      refine ⟨902313008425122083486569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1203084011233496111315425 902313008425122083486569)
      ·
        refine ⟨676734756318841562614927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 902313008425122083486569 676734756318841562614927)
        ·
          refine ⟨1015102134478262343922391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 676734756318841562614927 1015102134478262343922391)
          ·
            refine ⟨1522653201717393515883587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1015102134478262343922391 1522653201717393515883587)
            ·
              refine ⟨2283979802576090273825381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1522653201717393515883587 2283979802576090273825381)
              ·
                refine ⟨428246212983016926342259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2283979802576090273825381 428246212983016926342259)
                ·
                  refine ⟨642369319474525389513389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 428246212983016926342259 642369319474525389513389)
                  ·
                    refine ⟨240888494802947021067521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 642369319474525389513389 240888494802947021067521)
                    ·
                      rfl

theorem cell22_703693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_703693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_703693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_703693 prefixEnd_703693 := by exact prefixLift 703693
  have htrace : WordTrace (prefixWord ++ tailWord_703693) baseStart_703693 baseEnd_703693 := by
    simpa [prefixWord, tailWord_703693, baseEnd_703693] using wordTrace_append hprefix tailTrace_703693
  have hstable : (prefixWord ++ tailWord_703693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703693).length < 2 ^ (prefixWord ++ tailWord_703693).sum := by decide
  have hdescent : baseEnd_703693 < baseStart_703693 := by decide
  rcases family_descends (prefixWord ++ tailWord_703693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703803 : List Nat := [1, 1, 1, 1, 1, 2, 1, 1, 3, 10]
def baseStart_703803 : Nat := 118140960795 + 703803 * 2 ^ 59
def prefixEnd_703803 : Nat := 4983230072969 + 3 ^ 40 * 703803 * 2
def baseEnd_703803 : Nat := 240926150050943400817183

theorem tailTrace_703803 : CollatzResearch.WordTrace tailWord_703803 prefixEnd_703803 240926150050943400817183 := by
  unfold tailWord_703803
  simp only [CollatzResearch.WordTrace]
  refine ⟨25669804269249405827900063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17113202846166270551933375 25669804269249405827900063)
  ·
    refine ⟨38504706403874108741850095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25669804269249405827900063 38504706403874108741850095)
    ·
      refine ⟨57757059605811163112775143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38504706403874108741850095 57757059605811163112775143)
      ·
        refine ⟨86635589408716744669162715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57757059605811163112775143 86635589408716744669162715)
        ·
          refine ⟨129953384113075117003744073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86635589408716744669162715 129953384113075117003744073)
          ·
            refine ⟨97465038084806337752808055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129953384113075117003744073 97465038084806337752808055)
            ·
              refine ⟨146197557127209506629212083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97465038084806337752808055 146197557127209506629212083)
              ·
                refine ⟨219296335690814259943818125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 146197557127209506629212083 219296335690814259943818125)
                ·
                  refine ⟨82236125884055347478931797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 219296335690814259943818125 82236125884055347478931797)
                  ·
                    refine ⟨240926150050943400817183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 82236125884055347478931797 240926150050943400817183)
                    ·
                      rfl

theorem cell22_703803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 10].length) (baseStart_703803 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_703803 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_703803 prefixEnd_703803 := by exact prefixLift 703803
  have htrace : WordTrace (prefixWord ++ tailWord_703803) baseStart_703803 baseEnd_703803 := by
    simpa [prefixWord, tailWord_703803, baseEnd_703803] using wordTrace_append hprefix tailTrace_703803
  have hstable : (prefixWord ++ tailWord_703803).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703803).length < 2 ^ (prefixWord ++ tailWord_703803).sum := by decide
  have hdescent : baseEnd_703803 < baseStart_703803 := by decide
  rcases family_descends (prefixWord ++ tailWord_703803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703897 : List Nat := [1, 2, 1, 2, 1, 6, 3, 6]
def baseStart_703897 : Nat := 118140960795 + 703897 * 2 ^ 59
def prefixEnd_703897 : Nat := 4983230072969 + 3 ^ 40 * 703897 * 2
def baseEnd_703897 : Nat := 26773147574662054329655

theorem tailTrace_703897 : CollatzResearch.WordTrace tailWord_703897 prefixEnd_703897 26773147574662054329655 := by
  unfold tailWord_703897
  simp only [CollatzResearch.WordTrace]
  refine ⟨25673232730908859881821945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17115488487272573254547963 25673232730908859881821945)
  ·
    refine ⟨19254924548181644911366459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25673232730908859881821945 19254924548181644911366459)
    ·
      refine ⟨28882386822272467367049689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19254924548181644911366459 28882386822272467367049689)
      ·
        refine ⟨21661790116704350525287267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28882386822272467367049689 21661790116704350525287267)
        ·
          refine ⟨32492685175056525787930901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21661790116704350525287267 32492685175056525787930901)
          ·
            refine ⟨1523094617580774646309261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 32492685175056525787930901 1523094617580774646309261)
            ·
              refine ⟨571160481592790492365973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1523094617580774646309261 571160481592790492365973)
              ·
                refine ⟨26773147574662054329655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 571160481592790492365973 26773147574662054329655)
                ·
                  rfl

theorem cell22_703897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 3, 6].length) (baseStart_703897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_703897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_703897 prefixEnd_703897 := by exact prefixLift 703897
  have htrace : WordTrace (prefixWord ++ tailWord_703897) baseStart_703897 baseEnd_703897 := by
    simpa [prefixWord, tailWord_703897, baseEnd_703897] using wordTrace_append hprefix tailTrace_703897
  have hstable : (prefixWord ++ tailWord_703897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703897).length < 2 ^ (prefixWord ++ tailWord_703897).sum := by decide
  have hdescent : baseEnd_703897 < baseStart_703897 := by decide
  rcases family_descends (prefixWord ++ tailWord_703897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704032 : List Nat := [2, 1, 1, 6, 1, 11]
def baseStart_704032 : Nat := 118140960795 + 704032 * 2 ^ 59
def prefixEnd_704032 : Nat := 4983230072969 + 3 ^ 40 * 704032 * 2
def baseEnd_704032 : Nat := 2975364709023001689401

theorem tailTrace_704032 : CollatzResearch.WordTrace tailWord_704032 prefixEnd_704032 2975364709023001689401 := by
  unfold tailWord_704032
  simp only [CollatzResearch.WordTrace]
  refine ⟨12839078292709888968993175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17118771056946518625324233 12839078292709888968993175)
  ·
    refine ⟨19258617439064833453489763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12839078292709888968993175 19258617439064833453489763)
    ·
      refine ⟨28887926158597250180234645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19258617439064833453489763 28887926158597250180234645)
      ·
        refine ⟨1354121538684246102198499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 28887926158597250180234645 1354121538684246102198499)
        ·
          refine ⟨2031182308026369153297749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1354121538684246102198499 2031182308026369153297749)
          ·
            refine ⟨2975364709023001689401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 2031182308026369153297749 2975364709023001689401)
            ·
              rfl

theorem cell22_704032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 11].length) (baseStart_704032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_704032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_704032 prefixEnd_704032 := by exact prefixLift 704032
  have htrace : WordTrace (prefixWord ++ tailWord_704032) baseStart_704032 baseEnd_704032 := by
    simpa [prefixWord, tailWord_704032, baseEnd_704032] using wordTrace_append hprefix tailTrace_704032
  have hstable : (prefixWord ++ tailWord_704032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704032).length < 2 ^ (prefixWord ++ tailWord_704032).sum := by decide
  have hdescent : baseEnd_704032 < baseStart_704032 := by decide
  rcases family_descends (prefixWord ++ tailWord_704032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704034 : List Nat := [3, 3, 1, 1, 1, 1, 4, 2, 2, 4]
def baseStart_704034 : Nat := 118140960795 + 704034 * 2 ^ 59
def prefixEnd_704034 : Nat := 4983230072969 + 3 ^ 40 * 704034 * 2
def baseEnd_704034 : Nat := 241005226071735798291475

theorem tailTrace_704034 : CollatzResearch.WordTrace tailWord_704034 prefixEnd_704034 241005226071735798291475 := by
  unfold tailWord_704034
  simp only [CollatzResearch.WordTrace]
  refine ⟨6419557382853133069889789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17118819687608354853039437 6419557382853133069889789)
  ·
    refine ⟨2407334018569924901208671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6419557382853133069889789 2407334018569924901208671)
    ·
      refine ⟨3611001027854887351813007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2407334018569924901208671 3611001027854887351813007)
      ·
        refine ⟨5416501541782331027719511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3611001027854887351813007 5416501541782331027719511)
        ·
          refine ⟨8124752312673496541579267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5416501541782331027719511 8124752312673496541579267)
          ·
            refine ⟨12187128469010244812368901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8124752312673496541579267 12187128469010244812368901)
            ·
              refine ⟨2285086587939420902319169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12187128469010244812368901 2285086587939420902319169)
              ·
                refine ⟨1713814940954565676739377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2285086587939420902319169 1713814940954565676739377)
                ·
                  refine ⟨1285361205715924257554533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1713814940954565676739377 1285361205715924257554533)
                  ·
                    refine ⟨241005226071735798291475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1285361205715924257554533 241005226071735798291475)
                    ·
                      rfl

theorem cell22_704034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 2, 2, 4].length) (baseStart_704034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_704034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_704034 prefixEnd_704034 := by exact prefixLift 704034
  have htrace : WordTrace (prefixWord ++ tailWord_704034) baseStart_704034 baseEnd_704034 := by
    simpa [prefixWord, tailWord_704034, baseEnd_704034] using wordTrace_append hprefix tailTrace_704034
  have hstable : (prefixWord ++ tailWord_704034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704034).length < 2 ^ (prefixWord ++ tailWord_704034).sum := by decide
  have hdescent : baseEnd_704034 < baseStart_704034 := by decide
  rcases family_descends (prefixWord ++ tailWord_704034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704122 : List Nat := [3, 1, 1, 1, 1, 1, 1, 5, 8]
def baseStart_704122 : Nat := 118140960795 + 704122 * 2 ^ 59
def prefixEnd_704122 : Nat := 4983230072969 + 3 ^ 40 * 704122 * 2
def baseEnd_704122 : Nat := 80345116756710967363735

theorem tailTrace_704122 : CollatzResearch.WordTrace tailWord_704122 prefixEnd_704122 80345116756710967363735 := by
  unfold tailWord_704122
  simp only [CollatzResearch.WordTrace]
  refine ⟨6420359788773430827190655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17120959436729148872508413 6420359788773430827190655)
  ·
    refine ⟨9630539683160146240785983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6420359788773430827190655 9630539683160146240785983)
    ·
      refine ⟨14445809524740219361178975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9630539683160146240785983 14445809524740219361178975)
      ·
        refine ⟨21668714287110329041768463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14445809524740219361178975 21668714287110329041768463)
        ·
          refine ⟨32503071430665493562652695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21668714287110329041768463 32503071430665493562652695)
          ·
            refine ⟨48754607145998240343979043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32503071430665493562652695 48754607145998240343979043)
            ·
              refine ⟨73131910718997360515968565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48754607145998240343979043 73131910718997360515968565)
              ·
                refine ⟨6856116629906002548372053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 73131910718997360515968565 6856116629906002548372053)
                ·
                  refine ⟨80345116756710967363735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6856116629906002548372053 80345116756710967363735)
                  ·
                    rfl

theorem cell22_704122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 5, 8].length) (baseStart_704122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_704122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_704122 prefixEnd_704122 := by exact prefixLift 704122
  have htrace : WordTrace (prefixWord ++ tailWord_704122) baseStart_704122 baseEnd_704122 := by
    simpa [prefixWord, tailWord_704122, baseEnd_704122] using wordTrace_append hprefix tailTrace_704122
  have hstable : (prefixWord ++ tailWord_704122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704122).length < 2 ^ (prefixWord ++ tailWord_704122).sum := by decide
  have hdescent : baseEnd_704122 < baseStart_704122 := by decide
  rcases family_descends (prefixWord ++ tailWord_704122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704132 : List Nat := [2, 3, 2, 1, 5, 1, 1, 3, 1, 3]
def baseStart_704132 : Nat := 118140960795 + 704132 * 2 ^ 59
def prefixEnd_704132 : Nat := 4983230072969 + 3 ^ 40 * 704132 * 2
def baseEnd_704132 : Nat := 241038773474496209341175

theorem tailTrace_704132 : CollatzResearch.WordTrace tailWord_704132 prefixEnd_704132 241038773474496209341175 := by
  unfold tailWord_704132
  simp only [CollatzResearch.WordTrace]
  refine ⟨12840901942528747508313325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17121202590038330011084433 12840901942528747508313325)
  ·
    refine ⟨4815338228448280315617497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12840901942528747508313325 4815338228448280315617497)
    ·
      refine ⟨3611503671336210236713123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4815338228448280315617497 3611503671336210236713123)
      ·
        refine ⟨5417255507004315355069685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3611503671336210236713123 5417255507004315355069685)
        ·
          refine ⟨507867703781654564537783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5417255507004315355069685 507867703781654564537783)
          ·
            refine ⟨761801555672481846806675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 507867703781654564537783 761801555672481846806675)
            ·
              refine ⟨1142702333508722770210013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 761801555672481846806675 1142702333508722770210013)
              ·
                refine ⟨428513375065771038828755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1142702333508722770210013 428513375065771038828755)
                ·
                  refine ⟨642770062598656558243133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 428513375065771038828755 642770062598656558243133)
                  ·
                    refine ⟨241038773474496209341175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 642770062598656558243133 241038773474496209341175)
                    ·
                      rfl

theorem cell22_704132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 1, 3, 1, 3].length) (baseStart_704132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_704132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_704132 prefixEnd_704132 := by exact prefixLift 704132
  have htrace : WordTrace (prefixWord ++ tailWord_704132) baseStart_704132 baseEnd_704132 := by
    simpa [prefixWord, tailWord_704132, baseEnd_704132] using wordTrace_append hprefix tailTrace_704132
  have hstable : (prefixWord ++ tailWord_704132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704132).length < 2 ^ (prefixWord ++ tailWord_704132).sum := by decide
  have hdescent : baseEnd_704132 < baseStart_704132 := by decide
  rcases family_descends (prefixWord ++ tailWord_704132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704162 : List Nat := [3, 3, 1, 4, 2, 1, 2, 1, 5]
def baseStart_704162 : Nat := 118140960795 + 704162 * 2 ^ 59
def prefixEnd_704162 : Nat := 4983230072969 + 3 ^ 40 * 704162 * 2
def baseEnd_704162 : Nat := 80349681029195377030361

theorem tailTrace_704162 : CollatzResearch.WordTrace tailWord_704162 prefixEnd_704162 80349681029195377030361 := by
  unfold tailWord_704162
  simp only [CollatzResearch.WordTrace]
  refine ⟨6420724518737202535054685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17121932049965873426812493 6420724518737202535054685)
  ·
    refine ⟨2407771694526450950645507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6420724518737202535054685 2407771694526450950645507)
    ·
      refine ⟨3611657541789676425968261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2407771694526450950645507 3611657541789676425968261)
      ·
        refine ⟨677185789085564329869049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3611657541789676425968261 677185789085564329869049)
        ·
          refine ⟨507889341814173247401787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 677185789085564329869049 507889341814173247401787)
          ·
            refine ⟨761834012721259871102681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 507889341814173247401787 761834012721259871102681)
            ·
              refine ⟨571375509540944903327011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 761834012721259871102681 571375509540944903327011)
              ·
                refine ⟨857063264311417354990517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 571375509540944903327011 857063264311417354990517)
                ·
                  refine ⟨80349681029195377030361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 857063264311417354990517 80349681029195377030361)
                  ·
                    rfl

theorem cell22_704162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 2, 1, 5].length) (baseStart_704162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_704162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_704162 prefixEnd_704162 := by exact prefixLift 704162
  have htrace : WordTrace (prefixWord ++ tailWord_704162) baseStart_704162 baseEnd_704162 := by
    simpa [prefixWord, tailWord_704162, baseEnd_704162] using wordTrace_append hprefix tailTrace_704162
  have hstable : (prefixWord ++ tailWord_704162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704162).length < 2 ^ (prefixWord ++ tailWord_704162).sum := by decide
  have hdescent : baseEnd_704162 < baseStart_704162 := by decide
  rcases family_descends (prefixWord ++ tailWord_704162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704186 : List Nat := [3, 1, 1, 1, 2, 5, 2, 1, 2, 4]
def baseStart_704186 : Nat := 118140960795 + 704186 * 2 ^ 59
def prefixEnd_704186 : Nat := 4983230072969 + 3 ^ 40 * 704186 * 2
def baseEnd_704186 : Nat := 241057258778058068491009

theorem tailTrace_704186 : CollatzResearch.WordTrace tailWord_704186 prefixEnd_704186 241057258778058068491009 := by
  unfold tailWord_704186
  simp only [CollatzResearch.WordTrace]
  refine ⟨6420943356715465559773103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17122515617907908159394941 6420943356715465559773103)
  ·
    refine ⟨9631415035073198339659655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6420943356715465559773103 9631415035073198339659655)
    ·
      refine ⟨14447122552609797509489483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9631415035073198339659655 14447122552609797509489483)
      ·
        refine ⟨21670683828914696264234225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14447122552609797509489483 21670683828914696264234225)
        ·
          refine ⟨16253012871686022198175669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21670683828914696264234225 16253012871686022198175669)
          ·
            refine ⟨1523719956720564581078969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16253012871686022198175669 1523719956720564581078969)
            ·
              refine ⟨1142789967540423435809227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1523719956720564581078969 1142789967540423435809227)
              ·
                refine ⟨1714184951310635153713841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1142789967540423435809227 1714184951310635153713841)
                ·
                  refine ⟨1285638713482976365285381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1714184951310635153713841 1285638713482976365285381)
                  ·
                    refine ⟨241057258778058068491009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1285638713482976365285381 241057258778058068491009)
                    ·
                      rfl

theorem cell22_704186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 2, 1, 2, 4].length) (baseStart_704186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_704186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_704186 prefixEnd_704186 := by exact prefixLift 704186
  have htrace : WordTrace (prefixWord ++ tailWord_704186) baseStart_704186 baseEnd_704186 := by
    simpa [prefixWord, tailWord_704186, baseEnd_704186] using wordTrace_append hprefix tailTrace_704186
  have hstable : (prefixWord ++ tailWord_704186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704186).length < 2 ^ (prefixWord ++ tailWord_704186).sum := by decide
  have hdescent : baseEnd_704186 < baseStart_704186 := by decide
  rcases family_descends (prefixWord ++ tailWord_704186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704205 : List Nat := [1, 6, 2, 1, 1, 1, 1, 4, 2, 3]
def baseStart_704205 : Nat := 118140960795 + 704205 * 2 ^ 59
def prefixEnd_704205 : Nat := 4983230072969 + 3 ^ 40 * 704205 * 2
def baseEnd_704205 : Nat := 241063762866348352265951

theorem tailTrace_704205 : CollatzResearch.WordTrace tailWord_704205 prefixEnd_704205 241063762866348352265951 := by
  unfold tailWord_704205
  simp only [CollatzResearch.WordTrace]
  refine ⟨25684466413793028484034069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17122977609195352322689379 25684466413793028484034069)
  ·
    refine ⟨1203959363146548210189097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 25684466413793028484034069 1203959363146548210189097)
    ·
      refine ⟨902969522359911157641823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1203959363146548210189097 902969522359911157641823)
      ·
        refine ⟨1354454283539866736462735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 902969522359911157641823 1354454283539866736462735)
        ·
          refine ⟨2031681425309800104694103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1354454283539866736462735 2031681425309800104694103)
          ·
            refine ⟨3047522137964700157041155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2031681425309800104694103 3047522137964700157041155)
            ·
              refine ⟨4571283206947050235561733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3047522137964700157041155 4571283206947050235561733)
              ·
                refine ⟨857115601302571919167825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4571283206947050235561733 857115601302571919167825)
                ·
                  refine ⟨642836700976928939375869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 857115601302571919167825 642836700976928939375869)
                  ·
                    refine ⟨241063762866348352265951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 642836700976928939375869 241063762866348352265951)
                    ·
                      rfl

theorem cell22_704205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_704205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_704205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_704205 prefixEnd_704205 := by exact prefixLift 704205
  have htrace : WordTrace (prefixWord ++ tailWord_704205) baseStart_704205 baseEnd_704205 := by
    simpa [prefixWord, tailWord_704205, baseEnd_704205] using wordTrace_append hprefix tailTrace_704205
  have hstable : (prefixWord ++ tailWord_704205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704205).length < 2 ^ (prefixWord ++ tailWord_704205).sum := by decide
  have hdescent : baseEnd_704205 < baseStart_704205 := by decide
  rcases family_descends (prefixWord ++ tailWord_704205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704216 : List Nat := [2, 1, 2, 2, 3, 1, 2, 3, 3, 3]
def baseStart_704216 : Nat := 118140960795 + 704216 * 2 ^ 59
def prefixEnd_704216 : Nat := 4983230072969 + 3 ^ 40 * 704216 * 2
def baseEnd_704216 : Nat := 241067528391147990240917

theorem tailTrace_704216 : CollatzResearch.WordTrace tailWord_704216 prefixEnd_704216 241067528391147990240917 := by
  unfold tailWord_704216
  simp only [CollatzResearch.WordTrace]
  refine ⟨12842433808376588681342251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17123245077835451575123001 12842433808376588681342251)
  ·
    refine ⟨19263650712564883022013377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12842433808376588681342251 19263650712564883022013377)
    ·
      refine ⟨14447738034423662266510033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19263650712564883022013377 14447738034423662266510033)
      ·
        refine ⟨10835803525817746699882525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14447738034423662266510033 10835803525817746699882525)
        ·
          refine ⟨4063426322181655012455947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10835803525817746699882525 4063426322181655012455947)
          ·
            refine ⟨6095139483272482518683921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4063426322181655012455947 6095139483272482518683921)
            ·
              refine ⟨4571354612454361889012941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6095139483272482518683921 4571354612454361889012941)
              ·
                refine ⟨1714257979670385708379853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4571354612454361889012941 1714257979670385708379853)
                ·
                  refine ⟨642846742376394640642445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1714257979670385708379853 642846742376394640642445)
                  ·
                    refine ⟨241067528391147990240917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 642846742376394640642445 241067528391147990240917)
                    ·
                      rfl

theorem cell22_704216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 3, 3, 3].length) (baseStart_704216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_704216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_704216 prefixEnd_704216 := by exact prefixLift 704216
  have htrace : WordTrace (prefixWord ++ tailWord_704216) baseStart_704216 baseEnd_704216 := by
    simpa [prefixWord, tailWord_704216, baseEnd_704216] using wordTrace_append hprefix tailTrace_704216
  have hstable : (prefixWord ++ tailWord_704216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704216).length < 2 ^ (prefixWord ++ tailWord_704216).sum := by decide
  have hdescent : baseEnd_704216 < baseStart_704216 := by decide
  rcases family_descends (prefixWord ++ tailWord_704216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704293 : List Nat := [1, 3, 1, 2, 3, 3, 2, 2, 1, 4]
def baseStart_704293 : Nat := 118140960795 + 704293 * 2 ^ 59
def prefixEnd_704293 : Nat := 4983230072969 + 3 ^ 40 * 704293 * 2
def baseEnd_704293 : Nat := 241093887064745456065681

theorem tailTrace_704293 : CollatzResearch.WordTrace tailWord_704293 prefixEnd_704293 241093887064745456065681 := by
  unfold tailWord_704293
  simp only [CollatzResearch.WordTrace]
  refine ⟨25687676037474219513237533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17125117358316146342158355 25687676037474219513237533)
  ·
    refine ⟨9632878514052832317464075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25687676037474219513237533 9632878514052832317464075)
    ·
      refine ⟨14449317771079248476196113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9632878514052832317464075 14449317771079248476196113)
      ·
        refine ⟨10836988328309436357147085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14449317771079248476196113 10836988328309436357147085)
        ·
          refine ⟨4063870623116038633930157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10836988328309436357147085 4063870623116038633930157)
          ·
            refine ⟨1523951483668514487723809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4063870623116038633930157 1523951483668514487723809)
            ·
              refine ⟨1142963612751385865792857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1523951483668514487723809 1142963612751385865792857)
              ·
                refine ⟨857222709563539399344643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1142963612751385865792857 857222709563539399344643)
                ·
                  refine ⟨1285834064345309099016965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 857222709563539399344643 1285834064345309099016965)
                  ·
                    refine ⟨241093887064745456065681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1285834064345309099016965 241093887064745456065681)
                    ·
                      rfl

theorem cell22_704293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 2, 2, 1, 4].length) (baseStart_704293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_704293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_704293 prefixEnd_704293 := by exact prefixLift 704293
  have htrace : WordTrace (prefixWord ++ tailWord_704293) baseStart_704293 baseEnd_704293 := by
    simpa [prefixWord, tailWord_704293, baseEnd_704293] using wordTrace_append hprefix tailTrace_704293
  have hstable : (prefixWord ++ tailWord_704293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704293).length < 2 ^ (prefixWord ++ tailWord_704293).sum := by decide
  have hdescent : baseEnd_704293 < baseStart_704293 := by decide
  rcases family_descends (prefixWord ++ tailWord_704293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704310 : List Nat := [5, 1, 2, 2, 1, 1, 2, 3, 1, 4]
def baseStart_704310 : Nat := 118140960795 + 704310 * 2 ^ 59
def prefixEnd_704310 : Nat := 4983230072969 + 3 ^ 40 * 704310 * 2
def baseEnd_704310 : Nat := 241099706512163078390629

theorem tailTrace_704310 : CollatzResearch.WordTrace tailWord_704310 prefixEnd_704310 241099706512163078390629 := by
  unfold tailWord_704310
  simp only [CollatzResearch.WordTrace]
  refine ⟨1605518504900789463537899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17125530718941754277737589 1605518504900789463537899)
  ·
    refine ⟨2408277757351184195306849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1605518504900789463537899 2408277757351184195306849)
    ·
      refine ⟨1806208318013388146480137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2408277757351184195306849 1806208318013388146480137)
      ·
        refine ⟨1354656238510041109860103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1806208318013388146480137 1354656238510041109860103)
        ·
          refine ⟨2031984357765061664790155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1354656238510041109860103 2031984357765061664790155)
          ·
            refine ⟨3047976536647592497185233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2031984357765061664790155 3047976536647592497185233)
            ·
              refine ⟨2285982402485694372888925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3047976536647592497185233 2285982402485694372888925)
              ·
                refine ⟨857243400932135389833347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2285982402485694372888925 857243400932135389833347)
                ·
                  refine ⟨1285865101398203084750021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 857243400932135389833347 1285865101398203084750021)
                  ·
                    refine ⟨241099706512163078390629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1285865101398203084750021 241099706512163078390629)
                    ·
                      rfl

theorem cell22_704310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_704310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_704310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_704310 prefixEnd_704310 := by exact prefixLift 704310
  have htrace : WordTrace (prefixWord ++ tailWord_704310) baseStart_704310 baseEnd_704310 := by
    simpa [prefixWord, tailWord_704310, baseEnd_704310] using wordTrace_append hprefix tailTrace_704310
  have hstable : (prefixWord ++ tailWord_704310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704310).length < 2 ^ (prefixWord ++ tailWord_704310).sum := by decide
  have hdescent : baseEnd_704310 < baseStart_704310 := by decide
  rcases family_descends (prefixWord ++ tailWord_704310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704340 : List Nat := [2, 4, 1, 1, 3, 2, 1, 3, 2, 3]
def baseStart_704340 : Nat := 118140960795 + 704340 * 2 ^ 59
def prefixEnd_704340 : Nat := 4983230072969 + 3 ^ 40 * 704340 * 2
def baseEnd_704340 : Nat := 241109976125253000140537

theorem tailTrace_704340 : CollatzResearch.WordTrace tailWord_704340 prefixEnd_704340 241109976125253000140537 := by
  unfold tailWord_704340
  simp only [CollatzResearch.WordTrace]
  refine ⟨12844695134151973270099237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17126260178869297693465649 12844695134151973270099237)
  ·
    refine ⟨2408380337653494988143607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12844695134151973270099237 2408380337653494988143607)
    ·
      refine ⟨3612570506480242482215411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2408380337653494988143607 3612570506480242482215411)
      ·
        refine ⟨5418855759720363723323117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3612570506480242482215411 5418855759720363723323117)
        ·
          refine ⟨2032070909895136396246169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5418855759720363723323117 2032070909895136396246169)
          ·
            refine ⟨1524053182421352297184627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2032070909895136396246169 1524053182421352297184627)
            ·
              refine ⟨2286079773632028445776941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1524053182421352297184627 2286079773632028445776941)
              ·
                refine ⟨857279915112010667166353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2286079773632028445776941 857279915112010667166353)
                ·
                  refine ⟨642959936334008000374765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 857279915112010667166353 642959936334008000374765)
                  ·
                    refine ⟨241109976125253000140537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 642959936334008000374765 241109976125253000140537)
                    ·
                      rfl

theorem cell22_704340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 3, 2, 3].length) (baseStart_704340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_704340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_704340 prefixEnd_704340 := by exact prefixLift 704340
  have htrace : WordTrace (prefixWord ++ tailWord_704340) baseStart_704340 baseEnd_704340 := by
    simpa [prefixWord, tailWord_704340, baseEnd_704340] using wordTrace_append hprefix tailTrace_704340
  have hstable : (prefixWord ++ tailWord_704340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704340).length < 2 ^ (prefixWord ++ tailWord_704340).sum := by decide
  have hdescent : baseEnd_704340 < baseStart_704340 := by decide
  rcases family_descends (prefixWord ++ tailWord_704340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704406 : List Nat := [5, 3, 1, 1, 3, 1, 1, 1, 2, 4]
def baseStart_704406 : Nat := 118140960795 + 704406 * 2 ^ 59
def prefixEnd_704406 : Nat := 4983230072969 + 3 ^ 40 * 704406 * 2
def baseEnd_704406 : Nat := 241132569274050827990335

theorem tailTrace_704406 : CollatzResearch.WordTrace tailWord_704406 prefixEnd_704406 241132569274050827990335 := by
  unfold tailWord_704406
  simp only [CollatzResearch.WordTrace]
  refine ⟨1605737342879052488256317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17127864990709893208067381 1605737342879052488256317)
  ·
    refine ⟨602151503579644683096119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1605737342879052488256317 602151503579644683096119)
    ·
      refine ⟨903227255369467024644179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 602151503579644683096119 903227255369467024644179)
      ·
        refine ⟨1354840883054200536966269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 903227255369467024644179 1354840883054200536966269)
        ·
          refine ⟨508065331145325201362351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1354840883054200536966269 508065331145325201362351)
          ·
            refine ⟨762097996717987802043527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 508065331145325201362351 762097996717987802043527)
            ·
              refine ⟨1143146995076981703065291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 762097996717987802043527 1143146995076981703065291)
              ·
                refine ⟨1714720492615472554597937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1143146995076981703065291 1714720492615472554597937)
                ·
                  refine ⟨1286040369461604415948453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1714720492615472554597937 1286040369461604415948453)
                  ·
                    refine ⟨241132569274050827990335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1286040369461604415948453 241132569274050827990335)
                    ·
                      rfl

theorem cell22_704406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_704406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_704406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_704406 prefixEnd_704406 := by exact prefixLift 704406
  have htrace : WordTrace (prefixWord ++ tailWord_704406) baseStart_704406 baseEnd_704406 := by
    simpa [prefixWord, tailWord_704406, baseEnd_704406] using wordTrace_append hprefix tailTrace_704406
  have hstable : (prefixWord ++ tailWord_704406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704406).length < 2 ^ (prefixWord ++ tailWord_704406).sum := by decide
  have hdescent : baseEnd_704406 < baseStart_704406 := by decide
  rcases family_descends (prefixWord ++ tailWord_704406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704458 : List Nat := [3, 1, 2, 1, 2, 1, 5, 1, 1, 5]
def baseStart_704458 : Nat := 118140960795 + 704458 * 2 ^ 59
def prefixEnd_704458 : Nat := 4983230072969 + 3 ^ 40 * 704458 * 2
def baseEnd_704458 : Nat := 241150369936740025690175

theorem tailTrace_704458 : CollatzResearch.WordTrace tailWord_704458 prefixEnd_704458 241150369936740025690175 := by
  unfold tailWord_704458
  simp only [CollatzResearch.WordTrace]
  refine ⟨6423423520469113173248507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17129129387917635128662685 6423423520469113173248507)
  ·
    refine ⟨9635135280703669759872761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6423423520469113173248507 9635135280703669759872761)
    ·
      refine ⟨7226351460527752319904571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9635135280703669759872761 7226351460527752319904571)
      ·
        refine ⟨10839527190791628479856857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7226351460527752319904571 10839527190791628479856857)
        ·
          refine ⟨8129645393093721359892643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10839527190791628479856857 8129645393093721359892643)
          ·
            refine ⟨12194468089640582039838965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8129645393093721359892643 12194468089640582039838965)
            ·
              refine ⟨1143231383403804566234903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12194468089640582039838965 1143231383403804566234903)
              ·
                refine ⟨1714847075105706849352355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1143231383403804566234903 1714847075105706849352355)
                ·
                  refine ⟨2572270612658560274028533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1714847075105706849352355 2572270612658560274028533)
                  ·
                    refine ⟨241150369936740025690175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2572270612658560274028533 241150369936740025690175)
                    ·
                      rfl

theorem cell22_704458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 5, 1, 1, 5].length) (baseStart_704458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_704458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_704458 prefixEnd_704458 := by exact prefixLift 704458
  have htrace : WordTrace (prefixWord ++ tailWord_704458) baseStart_704458 baseEnd_704458 := by
    simpa [prefixWord, tailWord_704458, baseEnd_704458] using wordTrace_append hprefix tailTrace_704458
  have hstable : (prefixWord ++ tailWord_704458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704458).length < 2 ^ (prefixWord ++ tailWord_704458).sum := by decide
  have hdescent : baseEnd_704458 < baseStart_704458 := by decide
  rcases family_descends (prefixWord ++ tailWord_704458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704471 : List Nat := [1, 1, 3, 2, 1, 1, 5, 8]
def baseStart_704471 : Nat := 118140960795 + 704471 * 2 ^ 59
def prefixEnd_704471 : Nat := 4983230072969 + 3 ^ 40 * 704471 * 2
def baseEnd_704471 : Nat := 26794980011379147235015

theorem tailTrace_704471 : CollatzResearch.WordTrace tailWord_704471 prefixEnd_704471 26794980011379147235015 := by
  unfold tailWord_704471
  simp only [CollatzResearch.WordTrace]
  refine ⟨25694168230829355913217267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17129445487219570608811511 25694168230829355913217267)
  ·
    refine ⟨38541252346244033869825901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25694168230829355913217267 38541252346244033869825901)
    ·
      refine ⟨14452969629841512701184713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38541252346244033869825901 14452969629841512701184713)
      ·
        refine ⟨10839727222381134525888535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14452969629841512701184713 10839727222381134525888535)
        ·
          refine ⟨16259590833571701788832803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10839727222381134525888535 16259590833571701788832803)
          ·
            refine ⟨24389386250357552683249205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16259590833571701788832803 24389386250357552683249205)
            ·
              refine ⟨2286504960971020564054613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24389386250357552683249205 2286504960971020564054613)
              ·
                refine ⟨26794980011379147235015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2286504960971020564054613 26794980011379147235015)
                ·
                  rfl

theorem cell22_704471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 8].length) (baseStart_704471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_704471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_704471 prefixEnd_704471 := by exact prefixLift 704471
  have htrace : WordTrace (prefixWord ++ tailWord_704471) baseStart_704471 baseEnd_704471 := by
    simpa [prefixWord, tailWord_704471, baseEnd_704471] using wordTrace_append hprefix tailTrace_704471
  have hstable : (prefixWord ++ tailWord_704471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704471).length < 2 ^ (prefixWord ++ tailWord_704471).sum := by decide
  have hdescent : baseEnd_704471 < baseStart_704471 := by decide
  rcases family_descends (prefixWord ++ tailWord_704471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704554 : List Nat := [3, 1, 4, 1, 2, 2, 1, 4, 1, 3]
def baseStart_704554 : Nat := 118140960795 + 704554 * 2 ^ 59
def prefixEnd_704554 : Nat := 4983230072969 + 3 ^ 40 * 704554 * 2
def baseEnd_704554 : Nat := 241183232698627775289881

theorem tailTrace_704554 : CollatzResearch.WordTrace tailWord_704554 prefixEnd_704554 241183232698627775289881 := by
  unfold tailWord_704554
  simp only [CollatzResearch.WordTrace]
  refine ⟨6424298872382165272122179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17131463659685774058992477 6424298872382165272122179)
  ·
    refine ⟨9636448308573247908183269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6424298872382165272122179 9636448308573247908183269)
    ·
      refine ⟨1806834057857483982784363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9636448308573247908183269 1806834057857483982784363)
      ·
        refine ⟨2710251086786225974176545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1806834057857483982784363 2710251086786225974176545)
        ·
          refine ⟨2032688315089669480632409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2710251086786225974176545 2032688315089669480632409)
          ·
            refine ⟨1524516236317252110474307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2032688315089669480632409 1524516236317252110474307)
            ·
              refine ⟨2286774354475878165711461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1524516236317252110474307 2286774354475878165711461)
              ·
                refine ⟨428770191464227156070899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2286774354475878165711461 428770191464227156070899)
                ·
                  refine ⟨643155287196340734106349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 428770191464227156070899 643155287196340734106349)
                  ·
                    refine ⟨241183232698627775289881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 643155287196340734106349 241183232698627775289881)
                    ·
                      rfl

theorem cell22_704554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 4, 1, 3].length) (baseStart_704554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_704554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_704554 prefixEnd_704554 := by exact prefixLift 704554
  have htrace : WordTrace (prefixWord ++ tailWord_704554) baseStart_704554 baseEnd_704554 := by
    simpa [prefixWord, tailWord_704554, baseEnd_704554] using wordTrace_append hprefix tailTrace_704554
  have hstable : (prefixWord ++ tailWord_704554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704554).length < 2 ^ (prefixWord ++ tailWord_704554).sum := by decide
  have hdescent : baseEnd_704554 < baseStart_704554 := by decide
  rcases family_descends (prefixWord ++ tailWord_704554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704563 : List Nat := [1, 1, 1, 2, 4, 1, 3, 2, 3, 4]
def baseStart_704563 : Nat := 118140960795 + 704563 * 2 ^ 59
def prefixEnd_704563 : Nat := 4983230072969 + 3 ^ 40 * 704563 * 2
def baseEnd_704563 : Nat := 241186313582554751814853

theorem tailTrace_704563 : CollatzResearch.WordTrace tailWord_704563 prefixEnd_704563 241186313582554751814853 := by
  unfold tailWord_704563
  simp only [CollatzResearch.WordTrace]
  refine ⟨25697523746496055625566343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17131682497664037083710895 25697523746496055625566343)
  ·
    refine ⟨38546285619744083438349515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25697523746496055625566343 38546285619744083438349515)
    ·
      refine ⟨57819428429616125157524273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38546285619744083438349515 57819428429616125157524273)
      ·
        refine ⟨43364571322212093868143205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57819428429616125157524273 43364571322212093868143205)
        ·
          refine ⟨8130857122914767600276851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43364571322212093868143205 8130857122914767600276851)
          ·
            refine ⟨12196285684372151400415277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8130857122914767600276851 12196285684372151400415277)
            ·
              refine ⟨4573607131639556775155729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12196285684372151400415277 4573607131639556775155729)
              ·
                refine ⟨3430205348729667581366797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4573607131639556775155729 3430205348729667581366797)
                ·
                  refine ⟨1286327005773625343012549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3430205348729667581366797 1286327005773625343012549)
                  ·
                    refine ⟨241186313582554751814853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1286327005773625343012549 241186313582554751814853)
                    ·
                      rfl

theorem cell22_704563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 2, 3, 4].length) (baseStart_704563 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_704563 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_704563 prefixEnd_704563 := by exact prefixLift 704563
  have htrace : WordTrace (prefixWord ++ tailWord_704563) baseStart_704563 baseEnd_704563 := by
    simpa [prefixWord, tailWord_704563, baseEnd_704563] using wordTrace_append hprefix tailTrace_704563
  have hstable : (prefixWord ++ tailWord_704563).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704563).length < 2 ^ (prefixWord ++ tailWord_704563).sum := by decide
  have hdescent : baseEnd_704563 < baseStart_704563 := by decide
  rcases family_descends (prefixWord ++ tailWord_704563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704597 : List Nat := [1, 3, 2, 2, 1, 3, 4, 1, 1, 4]
def baseStart_704597 : Nat := 118140960795 + 704597 * 2 ^ 59
def prefixEnd_704597 : Nat := 4983230072969 + 3 ^ 40 * 704597 * 2
def baseEnd_704597 : Nat := 241197952477389996464749

theorem tailTrace_704597 : CollatzResearch.WordTrace tailWord_704597 prefixEnd_704597 241197952477389996464749 := by
  unfold tailWord_704597
  simp only [CollatzResearch.WordTrace]
  refine ⟨25698763828372879432304045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17132509218915252954869363 25698763828372879432304045)
  ·
    refine ⟨9637036435639829787114017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25698763828372879432304045 9637036435639829787114017)
    ·
      refine ⟨7227777326729872340335513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9637036435639829787114017 7227777326729872340335513)
      ·
        refine ⟨5420832995047404255251635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7227777326729872340335513 5420832995047404255251635)
        ·
          refine ⟨8131249492571106382877453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5420832995047404255251635 8131249492571106382877453)
          ·
            refine ⟨3049218559714164893579045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8131249492571106382877453 3049218559714164893579045)
            ·
              refine ⟨571728479946405917546071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3049218559714164893579045 571728479946405917546071)
              ·
                refine ⟨857592719919608876319107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 571728479946405917546071 857592719919608876319107)
                ·
                  refine ⟨1286389079879413314478661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 857592719919608876319107 1286389079879413314478661)
                  ·
                    refine ⟨241197952477389996464749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1286389079879413314478661 241197952477389996464749)
                    ·
                      rfl

theorem cell22_704597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 4, 1, 1, 4].length) (baseStart_704597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_704597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_704597 prefixEnd_704597 := by exact prefixLift 704597
  have htrace : WordTrace (prefixWord ++ tailWord_704597) baseStart_704597 baseEnd_704597 := by
    simpa [prefixWord, tailWord_704597, baseEnd_704597] using wordTrace_append hprefix tailTrace_704597
  have hstable : (prefixWord ++ tailWord_704597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704597).length < 2 ^ (prefixWord ++ tailWord_704597).sum := by decide
  have hdescent : baseEnd_704597 < baseStart_704597 := by decide
  rcases family_descends (prefixWord ++ tailWord_704597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704672 : List Nat := [2, 1, 1, 4, 2, 2, 3, 1, 3, 3]
def baseStart_704672 : Nat := 118140960795 + 704672 * 2 ^ 59
def prefixEnd_704672 : Nat := 4983230072969 + 3 ^ 40 * 704672 * 2
def baseEnd_704672 : Nat := 241223626510114800839519

theorem tailTrace_704672 : CollatzResearch.WordTrace tailWord_704672 prefixEnd_704672 241223626510114800839519 := by
  unfold tailWord_704672
  simp only [CollatzResearch.WordTrace]
  refine ⟨12850749651550583620642135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17134332868734111494189513 12850749651550583620642135)
  ·
    refine ⟨19276124477325875430963203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12850749651550583620642135 19276124477325875430963203)
    ·
      refine ⟨28914186715988813146444805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19276124477325875430963203 28914186715988813146444805)
      ·
        refine ⟨5421410009247902464958401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28914186715988813146444805 5421410009247902464958401)
        ·
          refine ⟨4066057506935926848718801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5421410009247902464958401 4066057506935926848718801)
          ·
            refine ⟨3049543130201945136539101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4066057506935926848718801 3049543130201945136539101)
            ·
              refine ⟨1143578673825729426202163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3049543130201945136539101 1143578673825729426202163)
              ·
                refine ⟨1715368010738594139303245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1143578673825729426202163 1715368010738594139303245)
                ·
                  refine ⟨643263004026972802238717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1715368010738594139303245 643263004026972802238717)
                  ·
                    refine ⟨241223626510114800839519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 643263004026972802238717 241223626510114800839519)
                    ·
                      rfl

theorem cell22_704672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3, 1, 3, 3].length) (baseStart_704672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_704672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_704672 prefixEnd_704672 := by exact prefixLift 704672
  have htrace : WordTrace (prefixWord ++ tailWord_704672) baseStart_704672 baseEnd_704672 := by
    simpa [prefixWord, tailWord_704672, baseEnd_704672] using wordTrace_append hprefix tailTrace_704672
  have hstable : (prefixWord ++ tailWord_704672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704672).length < 2 ^ (prefixWord ++ tailWord_704672).sum := by decide
  have hdescent : baseEnd_704672 < baseStart_704672 := by decide
  rcases family_descends (prefixWord ++ tailWord_704672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704683 : List Nat := [1, 1, 1, 1, 2, 1, 1, 1, 8, 5]
def baseStart_704683 : Nat := 118140960795 + 704683 * 2 ^ 59
def prefixEnd_704683 : Nat := 4983230072969 + 3 ^ 40 * 704683 * 2
def baseEnd_704683 : Nat := 241227392034914438814485

theorem tailTrace_704683 : CollatzResearch.WordTrace tailWord_704683 prefixEnd_704683 241227392034914438814485 := by
  unfold tailWord_704683
  simp only [CollatzResearch.WordTrace]
  refine ⟨25701900506061316119934703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17134600337374210746623135 25701900506061316119934703)
  ·
    refine ⟨38552850759091974179902055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25701900506061316119934703 38552850759091974179902055)
    ·
      refine ⟨57829276138637961269853083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38552850759091974179902055 57829276138637961269853083)
      ·
        refine ⟨86743914207956941904779625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57829276138637961269853083 86743914207956941904779625)
        ·
          refine ⟨65057935655967706428584719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86743914207956941904779625 65057935655967706428584719)
          ·
            refine ⟨97586903483951559642877079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65057935655967706428584719 97586903483951559642877079)
            ·
              refine ⟨146380355225927339464315619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97586903483951559642877079 146380355225927339464315619)
              ·
                refine ⟨219570532838891009196473429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 146380355225927339464315619 219570532838891009196473429)
                ·
                  refine ⟨2573092181705754014021173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 219570532838891009196473429 2573092181705754014021173)
                  ·
                    refine ⟨241227392034914438814485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2573092181705754014021173 241227392034914438814485)
                    ·
                      rfl

theorem cell22_704683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 8, 5].length) (baseStart_704683 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_704683 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_704683 prefixEnd_704683 := by exact prefixLift 704683
  have htrace : WordTrace (prefixWord ++ tailWord_704683) baseStart_704683 baseEnd_704683 := by
    simpa [prefixWord, tailWord_704683, baseEnd_704683] using wordTrace_append hprefix tailTrace_704683
  have hstable : (prefixWord ++ tailWord_704683).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704683).length < 2 ^ (prefixWord ++ tailWord_704683).sum := by decide
  have hdescent : baseEnd_704683 < baseStart_704683 := by decide
  rcases family_descends (prefixWord ++ tailWord_704683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704713 : List Nat := [1, 2, 1, 1, 2, 1, 1, 3, 10]
def baseStart_704713 : Nat := 118140960795 + 704713 * 2 ^ 59
def prefixEnd_704713 : Nat := 4983230072969 + 3 ^ 40 * 704713 * 2
def baseEnd_704713 : Nat := 80412553882668120188131

theorem tailTrace_704713 : CollatzResearch.WordTrace tailWord_704713 prefixEnd_704713 80412553882668120188131 := by
  unfold tailWord_704713
  simp only [CollatzResearch.WordTrace]
  refine ⟨25702994695952631243526793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17135329797301754162351195 25702994695952631243526793)
  ·
    refine ⟨19277246021964473432645095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25702994695952631243526793 19277246021964473432645095)
    ·
      refine ⟨28915869032946710148967643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19277246021964473432645095 28915869032946710148967643)
      ·
        refine ⟨43373803549420065223451465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28915869032946710148967643 43373803549420065223451465)
        ·
          refine ⟨32530352662065048917588599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43373803549420065223451465 32530352662065048917588599)
          ·
            refine ⟨48795528993097573376382899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32530352662065048917588599 48795528993097573376382899)
            ·
              refine ⟨73193293489646360064574349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48795528993097573376382899 73193293489646360064574349)
              ·
                refine ⟨27447485058617385024215381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73193293489646360064574349 27447485058617385024215381)
                ·
                  refine ⟨80412553882668120188131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 27447485058617385024215381 80412553882668120188131)
                  ·
                    rfl

theorem cell22_704713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 10].length) (baseStart_704713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_704713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_704713 prefixEnd_704713 := by exact prefixLift 704713
  have htrace : WordTrace (prefixWord ++ tailWord_704713) baseStart_704713 baseEnd_704713 := by
    simpa [prefixWord, tailWord_704713, baseEnd_704713] using wordTrace_append hprefix tailTrace_704713
  have hstable : (prefixWord ++ tailWord_704713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704713).length < 2 ^ (prefixWord ++ tailWord_704713).sum := by decide
  have hdescent : baseEnd_704713 < baseStart_704713 := by decide
  rcases family_descends (prefixWord ++ tailWord_704713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704764 : List Nat := [2, 2, 2, 1, 4, 2, 2, 3, 4]
def baseStart_704764 : Nat := 118140960795 + 704764 * 2 ^ 59
def prefixEnd_704764 : Nat := 4983230072969 + 3 ^ 40 * 704764 * 2
def baseEnd_704764 : Nat := 80418373330085742513079

theorem tailTrace_704764 : CollatzResearch.WordTrace tailWord_704764 prefixEnd_704764 80418373330085742513079 := by
  unfold tailWord_704764
  simp only [CollatzResearch.WordTrace]
  refine ⟨12852427409383933476816673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17136569879178577969088897 12852427409383933476816673)
  ·
    refine ⟨9639320557037950107612505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12852427409383933476816673 9639320557037950107612505)
    ·
      refine ⟨7229490417778462580709379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9639320557037950107612505 7229490417778462580709379)
      ·
        refine ⟨10844235626667693871064069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7229490417778462580709379 10844235626667693871064069)
        ·
          refine ⟨2033294180000192600824513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10844235626667693871064069 2033294180000192600824513)
          ·
            refine ⟨1524970635000144450618385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2033294180000192600824513 1524970635000144450618385)
            ·
              refine ⟨1143727976250108337963789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1524970635000144450618385 1143727976250108337963789)
              ·
                refine ⟨428897991093790626736421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1143727976250108337963789 428897991093790626736421)
                ·
                  refine ⟨80418373330085742513079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 428897991093790626736421 80418373330085742513079)
                  ·
                    rfl

theorem cell22_704764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 2, 3, 4].length) (baseStart_704764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_704764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_704764 prefixEnd_704764 := by exact prefixLift 704764
  have htrace : WordTrace (prefixWord ++ tailWord_704764) baseStart_704764 baseEnd_704764 := by
    simpa [prefixWord, tailWord_704764, baseEnd_704764] using wordTrace_append hprefix tailTrace_704764
  have hstable : (prefixWord ++ tailWord_704764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704764).length < 2 ^ (prefixWord ++ tailWord_704764).sum := by decide
  have hdescent : baseEnd_704764 < baseStart_704764 := by decide
  rcases family_descends (prefixWord ++ tailWord_704764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704835 : List Nat := [1, 1, 1, 3, 1, 3, 2, 1, 4, 5]
def baseStart_704835 : Nat := 118140960795 + 704835 * 2 ^ 59
def prefixEnd_704835 : Nat := 4983230072969 + 3 ^ 40 * 704835 * 2
def baseEnd_704835 : Nat := 241279424741236709014019

theorem tailTrace_704835 : CollatzResearch.WordTrace tailWord_704835 prefixEnd_704835 241279424741236709014019 := by
  unfold tailWord_704835
  simp only [CollatzResearch.WordTrace]
  refine ⟨25707444401510646079467959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17138296267673764052978639 25707444401510646079467959)
  ·
    refine ⟨38561166602265969119201939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25707444401510646079467959 38561166602265969119201939)
    ·
      refine ⟨57841749903398953678802909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38561166602265969119201939 57841749903398953678802909)
      ·
        refine ⟨21690656213774607629551091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57841749903398953678802909 21690656213774607629551091)
        ·
          refine ⟨32535984320661911444326637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21690656213774607629551091 32535984320661911444326637)
          ·
            refine ⟨12200994120248216791622489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32535984320661911444326637 12200994120248216791622489)
            ·
              refine ⟨9150745590186162593716867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12200994120248216791622489 9150745590186162593716867)
              ·
                refine ⟨13726118385279243890575301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9150745590186162593716867 13726118385279243890575301)
                ·
                  refine ⟨2573647197239858229482869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13726118385279243890575301 2573647197239858229482869)
                  ·
                    refine ⟨241279424741236709014019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2573647197239858229482869 241279424741236709014019)
                    ·
                      rfl

theorem cell22_704835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 4, 5].length) (baseStart_704835 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_704835 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_704835 prefixEnd_704835 := by exact prefixLift 704835
  have htrace : WordTrace (prefixWord ++ tailWord_704835) baseStart_704835 baseEnd_704835 := by
    simpa [prefixWord, tailWord_704835, baseEnd_704835] using wordTrace_append hprefix tailTrace_704835
  have hstable : (prefixWord ++ tailWord_704835).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704835).length < 2 ^ (prefixWord ++ tailWord_704835).sum := by decide
  have hdescent : baseEnd_704835 < baseStart_704835 := by decide
  rcases family_descends (prefixWord ++ tailWord_704835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704867 : List Nat := [1, 1, 1, 5, 2, 1, 3, 1, 3, 4]
def baseStart_704867 : Nat := 118140960795 + 704867 * 2 ^ 59
def prefixEnd_704867 : Nat := 4983230072969 + 3 ^ 40 * 704867 * 2
def baseEnd_704867 : Nat := 241290378995199292213921

theorem tailTrace_704867 : CollatzResearch.WordTrace tailWord_704867 prefixEnd_704867 241290378995199292213921 := by
  unfold tailWord_704867
  simp only [CollatzResearch.WordTrace]
  refine ⟨25708611537394715544632855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17139074358263143696421903 25708611537394715544632855)
  ·
    refine ⟨38562917306092073316949283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25708611537394715544632855 38562917306092073316949283)
    ·
      refine ⟨57844375959138109975423925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38562917306092073316949283 57844375959138109975423925)
      ·
        refine ⟨5422910246169197810195993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 57844375959138109975423925 5422910246169197810195993)
        ·
          refine ⟨4067182684626898357646995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5422910246169197810195993 4067182684626898357646995)
          ·
            refine ⟨6100774026940347536470493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4067182684626898357646995 6100774026940347536470493)
            ·
              refine ⟨2287790260102630326176435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6100774026940347536470493 2287790260102630326176435)
              ·
                refine ⟨3431685390153945489264653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2287790260102630326176435 3431685390153945489264653)
                ·
                  refine ⟨1286882021307729558474245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3431685390153945489264653 1286882021307729558474245)
                  ·
                    refine ⟨241290378995199292213921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1286882021307729558474245 241290378995199292213921)
                    ·
                      rfl

theorem cell22_704867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 1, 3, 4].length) (baseStart_704867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_704867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_704867 prefixEnd_704867 := by exact prefixLift 704867
  have htrace : WordTrace (prefixWord ++ tailWord_704867) baseStart_704867 baseEnd_704867 := by
    simpa [prefixWord, tailWord_704867, baseEnd_704867] using wordTrace_append hprefix tailTrace_704867
  have hstable : (prefixWord ++ tailWord_704867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704867).length < 2 ^ (prefixWord ++ tailWord_704867).sum := by decide
  have hdescent : baseEnd_704867 < baseStart_704867 := by decide
  rcases family_descends (prefixWord ++ tailWord_704867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704978 : List Nat := [3, 2, 2, 4, 1, 2, 2, 6]
def baseStart_704978 : Nat := 118140960795 + 704978 * 2 ^ 59
def prefixEnd_704978 : Nat := 4983230072969 + 3 ^ 40 * 704978 * 2
def baseEnd_704978 : Nat := 26814264062625778076509

theorem tailTrace_704978 : CollatzResearch.WordTrace tailWord_704978 prefixEnd_704978 26814264062625778076509 := by
  unfold tailWord_704978
  simp only [CollatzResearch.WordTrace]
  refine ⟨6428165009998145375480897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17141773359995054334615725 6428165009998145375480897)
  ·
    refine ⟨4821123757498609031610673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6428165009998145375480897 4821123757498609031610673)
    ·
      refine ⟨3615842818123956773708005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4821123757498609031610673 3615842818123956773708005)
      ·
        refine ⟨677970528398241895070251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3615842818123956773708005 677970528398241895070251)
        ·
          refine ⟨1016955792597362842605377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 677970528398241895070251 1016955792597362842605377)
          ·
            refine ⟨762716844448022131954033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1016955792597362842605377 762716844448022131954033)
            ·
              refine ⟨572037633336016598965525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 762716844448022131954033 572037633336016598965525)
              ·
                refine ⟨26814264062625778076509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 572037633336016598965525 26814264062625778076509)
                ·
                  rfl

theorem cell22_704978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 2, 6].length) (baseStart_704978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_704978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_704978 prefixEnd_704978 := by exact prefixLift 704978
  have htrace : WordTrace (prefixWord ++ tailWord_704978) baseStart_704978 baseEnd_704978 := by
    simpa [prefixWord, tailWord_704978, baseEnd_704978] using wordTrace_append hprefix tailTrace_704978
  have hstable : (prefixWord ++ tailWord_704978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704978).length < 2 ^ (prefixWord ++ tailWord_704978).sum := by decide
  have hdescent : baseEnd_704978 < baseStart_704978 := by decide
  rcases family_descends (prefixWord ++ tailWord_704978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705010 : List Nat := [3, 2, 1, 4, 3, 1, 1, 1, 3, 3]
def baseStart_705010 : Nat := 118140960795 + 705010 * 2 ^ 59
def prefixEnd_705010 : Nat := 4983230072969 + 3 ^ 40 * 705010 * 2
def baseEnd_705010 : Nat := 241339330817594585888483

theorem tailTrace_705010 : CollatzResearch.WordTrace tailWord_705010 prefixEnd_705010 241339330817594585888483 := by
  unfold tailWord_705010
  simp only [CollatzResearch.WordTrace]
  refine ⟨6428456793969162741772121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17142551450584433978058989 6428456793969162741772121)
  ·
    refine ⟨4821342595476872056329091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6428456793969162741772121 4821342595476872056329091)
    ·
      refine ⟨7232013893215308084493637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4821342595476872056329091 7232013893215308084493637)
      ·
        refine ⟨1356002604977870265842557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7232013893215308084493637 1356002604977870265842557)
        ·
          refine ⟨508500976866701349690959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1356002604977870265842557 508500976866701349690959)
          ·
            refine ⟨762751465300052024536439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 508500976866701349690959 762751465300052024536439)
            ·
              refine ⟨1144127197950078036804659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 762751465300052024536439 1144127197950078036804659)
              ·
                refine ⟨1716190796925117055206989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1144127197950078036804659 1716190796925117055206989)
                ·
                  refine ⟨643571548846918895702621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1716190796925117055206989 643571548846918895702621)
                  ·
                    refine ⟨241339330817594585888483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 643571548846918895702621 241339330817594585888483)
                    ·
                      rfl

theorem cell22_705010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 1, 1, 3, 3].length) (baseStart_705010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_705010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_705010 prefixEnd_705010 := by exact prefixLift 705010
  have htrace : WordTrace (prefixWord ++ tailWord_705010) baseStart_705010 baseEnd_705010 := by
    simpa [prefixWord, tailWord_705010, baseEnd_705010] using wordTrace_append hprefix tailTrace_705010
  have hstable : (prefixWord ++ tailWord_705010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705010).length < 2 ^ (prefixWord ++ tailWord_705010).sum := by decide
  have hdescent : baseEnd_705010 < baseStart_705010 := by decide
  rcases family_descends (prefixWord ++ tailWord_705010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705036 : List Nat := [2, 2, 1, 2, 4, 1, 3, 2, 1, 4]
def baseStart_705036 : Nat := 118140960795 + 705036 * 2 ^ 59
def prefixEnd_705036 : Nat := 4983230072969 + 3 ^ 40 * 705036 * 2
def baseEnd_705036 : Nat := 241348231148939184738403

theorem tailTrace_705036 : CollatzResearch.WordTrace tailWord_705036 prefixEnd_705036 241348231148939184738403 := by
  unfold tailWord_705036
  simp only [CollatzResearch.WordTrace]
  refine ⟨12857387736891228703767481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17143183649188304938356641 12857387736891228703767481)
  ·
    refine ⟨9643040802668421527825611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12857387736891228703767481 9643040802668421527825611)
    ·
      refine ⟨14464561204002632291738417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9643040802668421527825611 14464561204002632291738417)
      ·
        refine ⟨10848420903001974218803813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14464561204002632291738417 10848420903001974218803813)
        ·
          refine ⟨2034078919312870166025715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10848420903001974218803813 2034078919312870166025715)
          ·
            refine ⟨3051118378969305249038573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2034078919312870166025715 3051118378969305249038573)
            ·
              refine ⟨1144169392113489468389465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3051118378969305249038573 1144169392113489468389465)
              ·
                refine ⟨858127044085117101292099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1144169392113489468389465 858127044085117101292099)
                ·
                  refine ⟨1287190566127675651938149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 858127044085117101292099 1287190566127675651938149)
                  ·
                    refine ⟨241348231148939184738403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1287190566127675651938149 241348231148939184738403)
                    ·
                      rfl

theorem cell22_705036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 3, 2, 1, 4].length) (baseStart_705036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_705036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_705036 prefixEnd_705036 := by exact prefixLift 705036
  have htrace : WordTrace (prefixWord ++ tailWord_705036) baseStart_705036 baseEnd_705036 := by
    simpa [prefixWord, tailWord_705036, baseEnd_705036] using wordTrace_append hprefix tailTrace_705036
  have hstable : (prefixWord ++ tailWord_705036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705036).length < 2 ^ (prefixWord ++ tailWord_705036).sum := by decide
  have hdescent : baseEnd_705036 < baseStart_705036 := by decide
  rcases family_descends (prefixWord ++ tailWord_705036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705053 : List Nat := [1, 4, 2, 2, 1, 3, 3, 1, 1, 4]
def baseStart_705053 : Nat := 118140960795 + 705053 * 2 ^ 59
def prefixEnd_705053 : Nat := 4983230072969 + 3 ^ 40 * 705053 * 2
def baseEnd_705053 : Nat := 241354050596356807063351

theorem tailTrace_705053 : CollatzResearch.WordTrace tailWord_705053 prefixEnd_705053 241354050596356807063351 := by
  unfold tailWord_705053
  simp only [CollatzResearch.WordTrace]
  refine ⟨25715395514720869310903813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17143597009813912873935875 25715395514720869310903813)
  ·
    refine ⟨4821636659010162995794465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25715395514720869310903813 4821636659010162995794465)
    ·
      refine ⟨3616227494257622246845849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4821636659010162995794465 3616227494257622246845849)
      ·
        refine ⟨2712170620693216685134387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3616227494257622246845849 2712170620693216685134387)
        ·
          refine ⟨4068255931039825027701581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2712170620693216685134387 4068255931039825027701581)
          ·
            refine ⟨1525595974139934385388093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4068255931039825027701581 1525595974139934385388093)
            ·
              refine ⟨572098490302475394520535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1525595974139934385388093 572098490302475394520535)
              ·
                refine ⟨858147735453713091780803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 572098490302475394520535 858147735453713091780803)
                ·
                  refine ⟨1287221603180569637671205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 858147735453713091780803 1287221603180569637671205)
                  ·
                    refine ⟨241354050596356807063351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1287221603180569637671205 241354050596356807063351)
                    ·
                      rfl

theorem cell22_705053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 3, 1, 1, 4].length) (baseStart_705053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_705053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_705053 prefixEnd_705053 := by exact prefixLift 705053
  have htrace : WordTrace (prefixWord ++ tailWord_705053) baseStart_705053 baseEnd_705053 := by
    simpa [prefixWord, tailWord_705053, baseEnd_705053] using wordTrace_append hprefix tailTrace_705053
  have hstable : (prefixWord ++ tailWord_705053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705053).length < 2 ^ (prefixWord ++ tailWord_705053).sum := by decide
  have hdescent : baseEnd_705053 < baseStart_705053 := by decide
  rcases family_descends (prefixWord ++ tailWord_705053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705124 : List Nat := [2, 3, 1, 1, 2, 2, 3, 1, 7]
def baseStart_705124 : Nat := 118140960795 + 705124 * 2 ^ 59
def prefixEnd_705124 : Nat := 4983230072969 + 3 ^ 40 * 705124 * 2
def baseEnd_705124 : Nat := 80459451782445429512711

theorem tailTrace_705124 : CollatzResearch.WordTrace tailWord_705124 prefixEnd_705124 80459451782445429512711 := by
  unfold tailWord_705124
  simp only [CollatzResearch.WordTrace]
  refine ⟨12858992548731824218369213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17145323398309098957825617 12858992548731824218369213)
  ·
    refine ⟨4822122205774434081888455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12858992548731824218369213 4822122205774434081888455)
    ·
      refine ⟨7233183308661651122832683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4822122205774434081888455 7233183308661651122832683)
      ·
        refine ⟨10849774962992476684249025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7233183308661651122832683 10849774962992476684249025)
        ·
          refine ⟨8137331222244357513186769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10849774962992476684249025 8137331222244357513186769)
          ·
            refine ⟨6102998416683268134890077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8137331222244357513186769 6102998416683268134890077)
            ·
              refine ⟨2288624406256225550583779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6102998416683268134890077 2288624406256225550583779)
              ·
                refine ⟨3432936609384338325875669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2288624406256225550583779 3432936609384338325875669)
                ·
                  refine ⟨80459451782445429512711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3432936609384338325875669 80459451782445429512711)
                  ·
                    rfl

theorem cell22_705124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 1, 7].length) (baseStart_705124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_705124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_705124 prefixEnd_705124 := by exact prefixLift 705124
  have htrace : WordTrace (prefixWord ++ tailWord_705124) baseStart_705124 baseEnd_705124 := by
    simpa [prefixWord, tailWord_705124, baseEnd_705124] using wordTrace_append hprefix tailTrace_705124
  have hstable : (prefixWord ++ tailWord_705124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705124).length < 2 ^ (prefixWord ++ tailWord_705124).sum := by decide
  have hdescent : baseEnd_705124 < baseStart_705124 := by decide
  rcases family_descends (prefixWord ++ tailWord_705124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705162 : List Nat := [3, 1, 2, 3, 3, 2, 1, 3, 1, 3]
def baseStart_705162 : Nat := 118140960795 + 705162 * 2 ^ 59
def prefixEnd_705162 : Nat := 4983230072969 + 3 ^ 40 * 705162 * 2
def baseEnd_705162 : Nat := 241391363523916856088017

theorem tailTrace_705162 : CollatzResearch.WordTrace tailWord_705162 prefixEnd_705162 241391363523916856088017 := by
  unfold tailWord_705162
  simp only [CollatzResearch.WordTrace]
  refine ⟨6429842767831495231655435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17146247380883987284414493 6429842767831495231655435)
  ·
    refine ⟨9644764151747242847483153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6429842767831495231655435 9644764151747242847483153)
    ·
      refine ⟨7233573113810432135612365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9644764151747242847483153 7233573113810432135612365)
      ·
        refine ⟨2712589917678912050854637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7233573113810432135612365 2712589917678912050854637)
        ·
          refine ⟨1017221219129592019070489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2712589917678912050854637 1017221219129592019070489)
          ·
            refine ⟨762915914347194014302867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1017221219129592019070489 762915914347194014302867)
            ·
              refine ⟨1144373871520791021454301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 762915914347194014302867 1144373871520791021454301)
              ·
                refine ⟨429140201820296633045363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1144373871520791021454301 429140201820296633045363)
                ·
                  refine ⟨643710302730444949568045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 429140201820296633045363 643710302730444949568045)
                  ·
                    refine ⟨241391363523916856088017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 643710302730444949568045 241391363523916856088017)
                    ·
                      rfl

theorem cell22_705162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 1, 3, 1, 3].length) (baseStart_705162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_705162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_705162 prefixEnd_705162 := by exact prefixLift 705162
  have htrace : WordTrace (prefixWord ++ tailWord_705162) baseStart_705162 baseEnd_705162 := by
    simpa [prefixWord, tailWord_705162, baseEnd_705162] using wordTrace_append hprefix tailTrace_705162
  have hstable : (prefixWord ++ tailWord_705162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705162).length < 2 ^ (prefixWord ++ tailWord_705162).sum := by decide
  have hdescent : baseEnd_705162 < baseStart_705162 := by decide
  rcases family_descends (prefixWord ++ tailWord_705162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705205 : List Nat := [1, 3, 3, 3, 1, 3, 1, 2, 1, 4]
def baseStart_705205 : Nat := 118140960795 + 705205 * 2 ^ 59
def prefixEnd_705205 : Nat := 4983230072969 + 3 ^ 40 * 705205 * 2
def baseEnd_705205 : Nat := 241406083302679077262885

theorem tailTrace_705205 : CollatzResearch.WordTrace tailWord_705205 prefixEnd_705205 241406083302679077262885 := by
  unfold tailWord_705205
  simp only [CollatzResearch.WordTrace]
  refine ⟨25720939410170199270437069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17147292940113466180291379 25720939410170199270437069)
  ·
    refine ⟨9645352278813824726413901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25720939410170199270437069 9645352278813824726413901)
    ·
      refine ⟨3617007104555184272405213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9645352278813824726413901 3617007104555184272405213)
      ·
        refine ⟨1356377664208194102151955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3617007104555184272405213 1356377664208194102151955)
        ·
          refine ⟨2034566496312291153227933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1356377664208194102151955 2034566496312291153227933)
          ·
            refine ⟨762962436117109182460475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2034566496312291153227933 762962436117109182460475)
            ·
              refine ⟨1144443654175663773690713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 762962436117109182460475 1144443654175663773690713)
              ·
                refine ⟨858332740631747830268035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1144443654175663773690713 858332740631747830268035)
                ·
                  refine ⟨1287499110947621745402053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 858332740631747830268035 1287499110947621745402053)
                  ·
                    refine ⟨241406083302679077262885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1287499110947621745402053 241406083302679077262885)
                    ·
                      rfl

theorem cell22_705205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 1, 2, 1, 4].length) (baseStart_705205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_705205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_705205 prefixEnd_705205 := by exact prefixLift 705205
  have htrace : WordTrace (prefixWord ++ tailWord_705205) baseStart_705205 baseEnd_705205 := by
    simpa [prefixWord, tailWord_705205, baseEnd_705205] using wordTrace_append hprefix tailTrace_705205
  have hstable : (prefixWord ++ tailWord_705205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705205).length < 2 ^ (prefixWord ++ tailWord_705205).sum := by decide
  have hdescent : baseEnd_705205 < baseStart_705205 := by decide
  rcases family_descends (prefixWord ++ tailWord_705205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705216 : List Nat := [2, 1, 1, 2, 4, 2, 1, 3, 2, 4]
def baseStart_705216 : Nat := 118140960795 + 705216 * 2 ^ 59
def prefixEnd_705216 : Nat := 4983230072969 + 3 ^ 40 * 705216 * 2
def baseEnd_705216 : Nat := 241409848827478715237851

theorem tailTrace_705216 : CollatzResearch.WordTrace tailWord_705216 prefixEnd_705216 241409848827478715237851 := by
  unfold tailWord_705216
  simp only [CollatzResearch.WordTrace]
  refine ⟨12860670306565174074543751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17147560408753565432725001 12860670306565174074543751)
  ·
    refine ⟨19291005459847761111815627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12860670306565174074543751 19291005459847761111815627)
    ·
      refine ⟨28936508189771641667723441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19291005459847761111815627 28936508189771641667723441)
      ·
        refine ⟨21702381142328731250792581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28936508189771641667723441 21702381142328731250792581)
        ·
          refine ⟨4069196464186637109523609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21702381142328731250792581 4069196464186637109523609)
          ·
            refine ⟨3051897348139977832142707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4069196464186637109523609 3051897348139977832142707)
            ·
              refine ⟨4577846022209966748214061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3051897348139977832142707 4577846022209966748214061)
              ·
                refine ⟨1716692258328737530580273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4577846022209966748214061 1716692258328737530580273)
                ·
                  refine ⟨1287519193746553147935205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1716692258328737530580273 1287519193746553147935205)
                  ·
                    refine ⟨241409848827478715237851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1287519193746553147935205 241409848827478715237851)
                    ·
                      rfl

theorem cell22_705216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 3, 2, 4].length) (baseStart_705216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_705216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_705216 prefixEnd_705216 := by exact prefixLift 705216
  have htrace : WordTrace (prefixWord ++ tailWord_705216) baseStart_705216 baseEnd_705216 := by
    simpa [prefixWord, tailWord_705216, baseEnd_705216] using wordTrace_append hprefix tailTrace_705216
  have hstable : (prefixWord ++ tailWord_705216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705216).length < 2 ^ (prefixWord ++ tailWord_705216).sum := by decide
  have hdescent : baseEnd_705216 < baseStart_705216 := by decide
  rcases family_descends (prefixWord ++ tailWord_705216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705259 : List Nat := [1, 1, 1, 1, 2, 4, 1, 2, 9]
def baseStart_705259 : Nat := 118140960795 + 705259 * 2 ^ 59
def prefixEnd_705259 : Nat := 4983230072969 + 3 ^ 40 * 705259 * 2
def baseEnd_705259 : Nat := 80474856202080312137573

theorem tailTrace_705259 : CollatzResearch.WordTrace tailWord_705259 prefixEnd_705259 80474856202080312137573 := by
  unfold tailWord_705259
  simp only [CollatzResearch.WordTrace]
  refine ⟨25722908951974566492902831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17148605967983044328601887 25722908951974566492902831)
  ·
    refine ⟨38584363427961849739354247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25722908951974566492902831 38584363427961849739354247)
    ·
      refine ⟨57876545141942774609031371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38584363427961849739354247 57876545141942774609031371)
      ·
        refine ⟨86814817712914161913547057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57876545141942774609031371 86814817712914161913547057)
        ·
          refine ⟨65111113284685621435160293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86814817712914161913547057 65111113284685621435160293)
          ·
            refine ⟨12208333740878554019092555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65111113284685621435160293 12208333740878554019092555)
            ·
              refine ⟨18312500611317831028638833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12208333740878554019092555 18312500611317831028638833)
              ·
                refine ⟨13734375458488373271479125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18312500611317831028638833 13734375458488373271479125)
                ·
                  refine ⟨80474856202080312137573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 13734375458488373271479125 80474856202080312137573)
                  ·
                    rfl

theorem cell22_705259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 9].length) (baseStart_705259 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_705259 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_705259 prefixEnd_705259 := by exact prefixLift 705259
  have htrace : WordTrace (prefixWord ++ tailWord_705259) baseStart_705259 baseEnd_705259 := by
    simpa [prefixWord, tailWord_705259, baseEnd_705259] using wordTrace_append hprefix tailTrace_705259
  have hstable : (prefixWord ++ tailWord_705259).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705259).length < 2 ^ (prefixWord ++ tailWord_705259).sum := by decide
  have hdescent : baseEnd_705259 < baseStart_705259 := by decide
  rcases family_descends (prefixWord ++ tailWord_705259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705261 : List Nat := [1, 5, 1, 2, 1, 1, 1, 2, 2, 6]
def baseStart_705261 : Nat := 118140960795 + 705261 * 2 ^ 59
def prefixEnd_705261 : Nat := 4983230072969 + 3 ^ 40 * 705261 * 2
def baseEnd_705261 : Nat := 241425253247113597862713

theorem tailTrace_705261 : CollatzResearch.WordTrace tailWord_705261 prefixEnd_705261 241425253247113597862713 := by
  unfold tailWord_705261
  simp only [CollatzResearch.WordTrace]
  refine ⟨25722981897967320834475637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17148654598644880556317091 25722981897967320834475637)
  ·
    refine ⟨2411529552934436328232091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25722981897967320834475637 2411529552934436328232091)
    ·
      refine ⟨3617294329401654492348137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2411529552934436328232091 3617294329401654492348137)
      ·
        refine ⟨2712970747051240869261103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3617294329401654492348137 2712970747051240869261103)
        ·
          refine ⟨4069456120576861303891655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2712970747051240869261103 4069456120576861303891655)
          ·
            refine ⟨6104184180865291955837483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4069456120576861303891655 6104184180865291955837483)
            ·
              refine ⟨9156276271297937933756225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6104184180865291955837483 9156276271297937933756225)
              ·
                refine ⟨6867207203473453450317169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9156276271297937933756225 6867207203473453450317169)
                ·
                  refine ⟨5150405402605090087737877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6867207203473453450317169 5150405402605090087737877)
                  ·
                    refine ⟨241425253247113597862713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5150405402605090087737877 241425253247113597862713)
                    ·
                      rfl

theorem cell22_705261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 2, 2, 6].length) (baseStart_705261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_705261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_705261 prefixEnd_705261 := by exact prefixLift 705261
  have htrace : WordTrace (prefixWord ++ tailWord_705261) baseStart_705261 baseEnd_705261 := by
    simpa [prefixWord, tailWord_705261, baseEnd_705261] using wordTrace_append hprefix tailTrace_705261
  have hstable : (prefixWord ++ tailWord_705261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705261).length < 2 ^ (prefixWord ++ tailWord_705261).sum := by decide
  have hdescent : baseEnd_705261 < baseStart_705261 := by decide
  rcases family_descends (prefixWord ++ tailWord_705261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705263 : List Nat := [1, 1, 2, 1, 5, 3, 1, 2, 3, 3]
def baseStart_705263 : Nat := 118140960795 + 705263 * 2 ^ 59
def prefixEnd_705263 : Nat := 4983230072969 + 3 ^ 40 * 705263 * 2
def baseEnd_705263 : Nat := 241425937887986259312707

theorem tailTrace_705263 : CollatzResearch.WordTrace tailWord_705263 prefixEnd_705263 241425937887986259312707 := by
  unfold tailWord_705263
  simp only [CollatzResearch.WordTrace]
  refine ⟨25723054843960075176048443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17148703229306716784032295 25723054843960075176048443)
  ·
    refine ⟨38584582265940112764072665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25723054843960075176048443 38584582265940112764072665)
    ·
      refine ⟨28938436699455084573054499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38584582265940112764072665 28938436699455084573054499)
      ·
        refine ⟨43407655049182626859581749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28938436699455084573054499 43407655049182626859581749)
        ·
          refine ⟨4069467660860871268085789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 43407655049182626859581749 4069467660860871268085789)
          ·
            refine ⟨1526050372822826725532171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4069467660860871268085789 1526050372822826725532171)
            ·
              refine ⟨2289075559234240088298257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1526050372822826725532171 2289075559234240088298257)
              ·
                refine ⟨1716806669425680066223693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2289075559234240088298257 1716806669425680066223693)
                ·
                  refine ⟨643802501034630024833885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1716806669425680066223693 643802501034630024833885)
                  ·
                    refine ⟨241425937887986259312707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 643802501034630024833885 241425937887986259312707)
                    ·
                      rfl

theorem cell22_705263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 2, 3, 3].length) (baseStart_705263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_705263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_705263 prefixEnd_705263 := by exact prefixLift 705263
  have htrace : WordTrace (prefixWord ++ tailWord_705263) baseStart_705263 baseEnd_705263 := by
    simpa [prefixWord, tailWord_705263, baseEnd_705263] using wordTrace_append hprefix tailTrace_705263
  have hstable : (prefixWord ++ tailWord_705263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705263).length < 2 ^ (prefixWord ++ tailWord_705263).sum := by decide
  have hdescent : baseEnd_705263 < baseStart_705263 := by decide
  rcases family_descends (prefixWord ++ tailWord_705263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705336 : List Nat := [2, 1, 2, 1, 3, 2, 2, 1, 3, 5]
def baseStart_705336 : Nat := 118140960795 + 705336 * 2 ^ 59
def prefixEnd_705336 : Nat := 4983230072969 + 3 ^ 40 * 705336 * 2
def baseEnd_705336 : Nat := 241450927279838402237483

theorem tailTrace_705336 : CollatzResearch.WordTrace tailWord_705336 prefixEnd_705336 241450927279838402237483 := by
  unfold tailWord_705336
  simp only [CollatzResearch.WordTrace]
  refine ⟨12862858686347804321727931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17150478248463739095637241 12862858686347804321727931)
  ·
    refine ⟨19294288029521706482591897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12862858686347804321727931 19294288029521706482591897)
    ·
      refine ⟨14470716022141279861943923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19294288029521706482591897 14470716022141279861943923)
      ·
        refine ⟨21706074033211919792915885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14470716022141279861943923 21706074033211919792915885)
        ·
          refine ⟨8139777762454469922343457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21706074033211919792915885 8139777762454469922343457)
          ·
            refine ⟨6104833321840852441757593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8139777762454469922343457 6104833321840852441757593)
            ·
              refine ⟨4578624991380639331318195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6104833321840852441757593 4578624991380639331318195)
              ·
                refine ⟨6867937487070958996977293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4578624991380639331318195 6867937487070958996977293)
                ·
                  refine ⟨2575476557651609623866485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6867937487070958996977293 2575476557651609623866485)
                  ·
                    refine ⟨241450927279838402237483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2575476557651609623866485 241450927279838402237483)
                    ·
                      rfl

theorem cell22_705336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 1, 3, 5].length) (baseStart_705336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_705336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_705336 prefixEnd_705336 := by exact prefixLift 705336
  have htrace : WordTrace (prefixWord ++ tailWord_705336) baseStart_705336 baseEnd_705336 := by
    simpa [prefixWord, tailWord_705336, baseEnd_705336] using wordTrace_append hprefix tailTrace_705336
  have hstable : (prefixWord ++ tailWord_705336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705336).length < 2 ^ (prefixWord ++ tailWord_705336).sum := by decide
  have hdescent : baseEnd_705336 < baseStart_705336 := by decide
  rcases family_descends (prefixWord ++ tailWord_705336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705353 : List Nat := [1, 2, 1, 1, 2, 5, 2, 1, 4, 3]
def baseStart_705353 : Nat := 118140960795 + 705353 * 2 ^ 59
def prefixEnd_705353 : Nat := 4983230072969 + 3 ^ 40 * 705353 * 2
def baseEnd_705353 : Nat := 241456746727256024562431

theorem tailTrace_705353 : CollatzResearch.WordTrace tailWord_705353 prefixEnd_705353 241456746727256024562431 := by
  unfold tailWord_705353
  simp only [CollatzResearch.WordTrace]
  refine ⟨25726337413634020546824713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17150891609089347031216475 25726337413634020546824713)
  ·
    refine ⟨19294753060225515410118535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25726337413634020546824713 19294753060225515410118535)
    ·
      refine ⟨28942129590338273115177803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19294753060225515410118535 28942129590338273115177803)
      ·
        refine ⟨43413194385507409672766705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28942129590338273115177803 43413194385507409672766705)
        ·
          refine ⟨32559895789130557254575029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43413194385507409672766705 32559895789130557254575029)
          ·
            refine ⟨3052490230230989742616409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32559895789130557254575029 3052490230230989742616409)
            ·
              refine ⟨2289367672673242306962307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3052490230230989742616409 2289367672673242306962307)
              ·
                refine ⟨3434051509009863460443461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2289367672673242306962307 3434051509009863460443461)
                ·
                  refine ⟨643884657939349398833149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3434051509009863460443461 643884657939349398833149)
                  ·
                    refine ⟨241456746727256024562431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 643884657939349398833149 241456746727256024562431)
                    ·
                      rfl

theorem cell22_705353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 1, 4, 3].length) (baseStart_705353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_705353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_705353 prefixEnd_705353 := by exact prefixLift 705353
  have htrace : WordTrace (prefixWord ++ tailWord_705353) baseStart_705353 baseEnd_705353 := by
    simpa [prefixWord, tailWord_705353, baseEnd_705353] using wordTrace_append hprefix tailTrace_705353
  have hstable : (prefixWord ++ tailWord_705353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705353).length < 2 ^ (prefixWord ++ tailWord_705353).sum := by decide
  have hdescent : baseEnd_705353 < baseStart_705353 := by decide
  rcases family_descends (prefixWord ++ tailWord_705353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705370 : List Nat := [3, 1, 1, 2, 1, 5, 1, 3, 2, 3]
def baseStart_705370 : Nat := 118140960795 + 705370 * 2 ^ 59
def prefixEnd_705370 : Nat := 4983230072969 + 3 ^ 40 * 705370 * 2
def baseEnd_705370 : Nat := 241462566174673646887379

theorem tailTrace_705370 : CollatzResearch.WordTrace tailWord_705370 prefixEnd_705370 241462566174673646887379 := by
  unfold tailWord_705370
  simp only [CollatzResearch.WordTrace]
  refine ⟨6431739363643108112548391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17151304969714954966795709 6431739363643108112548391)
  ·
    refine ⟨9647609045464662168822587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6431739363643108112548391 9647609045464662168822587)
    ·
      refine ⟨14471413568196993253233881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9647609045464662168822587 14471413568196993253233881)
      ·
        refine ⟨10853560176147744939925411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14471413568196993253233881 10853560176147744939925411)
        ·
          refine ⟨16280340264221617409888117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10853560176147744939925411 16280340264221617409888117)
          ·
            refine ⟨1526281899770776632177011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16280340264221617409888117 1526281899770776632177011)
            ·
              refine ⟨2289422849656164948265517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1526281899770776632177011 2289422849656164948265517)
              ·
                refine ⟨858533568621061855599569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2289422849656164948265517 858533568621061855599569)
                ·
                  refine ⟨643900176465796391699677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 858533568621061855599569 643900176465796391699677)
                  ·
                    refine ⟨241462566174673646887379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 643900176465796391699677 241462566174673646887379)
                    ·
                      rfl

theorem cell22_705370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 3, 2, 3].length) (baseStart_705370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_705370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_705370 prefixEnd_705370 := by exact prefixLift 705370
  have htrace : WordTrace (prefixWord ++ tailWord_705370) baseStart_705370 baseEnd_705370 := by
    simpa [prefixWord, tailWord_705370, baseEnd_705370] using wordTrace_append hprefix tailTrace_705370
  have hstable : (prefixWord ++ tailWord_705370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705370).length < 2 ^ (prefixWord ++ tailWord_705370).sum := by decide
  have hdescent : baseEnd_705370 < baseStart_705370 := by decide
  rcases family_descends (prefixWord ++ tailWord_705370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705381 : List Nat := [1, 3, 1, 3, 1, 1, 2, 1, 2, 7]
def baseStart_705381 : Nat := 118140960795 + 705381 * 2 ^ 59
def prefixEnd_705381 : Nat := 4983230072969 + 3 ^ 40 * 705381 * 2
def baseEnd_705381 : Nat := 241466331699473284862345

theorem tailTrace_705381 : CollatzResearch.WordTrace tailWord_705381 prefixEnd_705381 241466331699473284862345 := by
  unfold tailWord_705381
  simp only [CollatzResearch.WordTrace]
  refine ⟨25727358657532581328843997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17151572438355054219229331 25727358657532581328843997)
  ·
    refine ⟨9647759496574717998316499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25727358657532581328843997 9647759496574717998316499)
    ·
      refine ⟨14471639244862076997474749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9647759496574717998316499 14471639244862076997474749)
      ·
        refine ⟨5426864716823278874053031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14471639244862076997474749 5426864716823278874053031)
        ·
          refine ⟨8140297075234918311079547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5426864716823278874053031 8140297075234918311079547)
          ·
            refine ⟨12210445612852377466619321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8140297075234918311079547 12210445612852377466619321)
            ·
              refine ⟨9157834209639283099964491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12210445612852377466619321 9157834209639283099964491)
              ·
                refine ⟨13736751314458924649946737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9157834209639283099964491 13736751314458924649946737)
                ·
                  refine ⟨10302563485844193487460053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13736751314458924649946737 10302563485844193487460053)
                  ·
                    refine ⟨241466331699473284862345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10302563485844193487460053 241466331699473284862345)
                    ·
                      rfl

theorem cell22_705381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 2, 7].length) (baseStart_705381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_705381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_705381 prefixEnd_705381 := by exact prefixLift 705381
  have htrace : WordTrace (prefixWord ++ tailWord_705381) baseStart_705381 baseEnd_705381 := by
    simpa [prefixWord, tailWord_705381, baseEnd_705381] using wordTrace_append hprefix tailTrace_705381
  have hstable : (prefixWord ++ tailWord_705381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705381).length < 2 ^ (prefixWord ++ tailWord_705381).sum := by decide
  have hdescent : baseEnd_705381 < baseStart_705381 := by decide
  rcases family_descends (prefixWord ++ tailWord_705381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705406 : List Nat := [4, 2, 3, 1, 2, 2, 2, 2, 4]
def baseStart_705406 : Nat := 118140960795 + 705406 * 2 ^ 59
def prefixEnd_705406 : Nat := 4983230072969 + 3 ^ 40 * 705406 * 2
def baseEnd_705406 : Nat := 80491629903460517662423

theorem tailTrace_705406 : CollatzResearch.WordTrace tailWord_705406 prefixEnd_705406 80491629903460517662423 := by
  unfold tailWord_705406
  simp only [CollatzResearch.WordTrace]
  refine ⟨3216033810305251324813009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17152180321628007065669381 3216033810305251324813009)
  ·
    refine ⟨2412025357728938493609757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3216033810305251324813009 2412025357728938493609757)
    ·
      refine ⟨904509509148351935103659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2412025357728938493609757 904509509148351935103659)
      ·
        refine ⟨1356764263722527902655489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 904509509148351935103659 1356764263722527902655489)
        ·
          refine ⟨1017573197791895926991617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1356764263722527902655489 1017573197791895926991617)
          ·
            refine ⟨763179898343921945243713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1017573197791895926991617 763179898343921945243713)
            ·
              refine ⟨572384923757941458932785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 763179898343921945243713 572384923757941458932785)
              ·
                refine ⟨429288692818456094199589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 572384923757941458932785 429288692818456094199589)
                ·
                  refine ⟨80491629903460517662423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 429288692818456094199589 80491629903460517662423)
                  ·
                    rfl

theorem cell22_705406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 2, 2, 4].length) (baseStart_705406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_705406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_705406 prefixEnd_705406 := by exact prefixLift 705406
  have htrace : WordTrace (prefixWord ++ tailWord_705406) baseStart_705406 baseEnd_705406 := by
    simpa [prefixWord, tailWord_705406, baseEnd_705406] using wordTrace_append hprefix tailTrace_705406
  have hstable : (prefixWord ++ tailWord_705406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705406).length < 2 ^ (prefixWord ++ tailWord_705406).sum := by decide
  have hdescent : baseEnd_705406 < baseStart_705406 := by decide
  rcases family_descends (prefixWord ++ tailWord_705406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705490 : List Nat := [3, 2, 2, 3, 1, 1, 2, 2, 6]
def baseStart_705490 : Nat := 118140960795 + 705490 * 2 ^ 59
def prefixEnd_705490 : Nat := 4983230072969 + 3 ^ 40 * 705490 * 2
def baseEnd_705490 : Nat := 80501214875677777962337

theorem tailTrace_705490 : CollatzResearch.WordTrace tailWord_705490 prefixEnd_705490 80501214875677777962337 := by
  unfold tailWord_705490
  simp only [CollatzResearch.WordTrace]
  refine ⟨6432833553534423236140481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17154222809425128629707949 6432833553534423236140481)
  ·
    refine ⟨4824625165150817427105361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6432833553534423236140481 4824625165150817427105361)
    ·
      refine ⟨3618468873863113070329021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4824625165150817427105361 3618468873863113070329021)
      ·
        refine ⟨1356925827698667401373383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3618468873863113070329021 1356925827698667401373383)
        ·
          refine ⟨2035388741548001102060075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1356925827698667401373383 2035388741548001102060075)
          ·
            refine ⟨3053083112322001653090113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2035388741548001102060075 3053083112322001653090113)
            ·
              refine ⟨2289812334241501239817585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3053083112322001653090113 2289812334241501239817585)
              ·
                refine ⟨1717359250681125929863189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2289812334241501239817585 1717359250681125929863189)
                ·
                  refine ⟨80501214875677777962337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1717359250681125929863189 80501214875677777962337)
                  ·
                    rfl

theorem cell22_705490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 2, 6].length) (baseStart_705490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_705490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_705490 prefixEnd_705490 := by exact prefixLift 705490
  have htrace : WordTrace (prefixWord ++ tailWord_705490) baseStart_705490 baseEnd_705490 := by
    simpa [prefixWord, tailWord_705490, baseEnd_705490] using wordTrace_append hprefix tailTrace_705490
  have hstable : (prefixWord ++ tailWord_705490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705490).length < 2 ^ (prefixWord ++ tailWord_705490).sum := by decide
  have hdescent : baseEnd_705490 < baseStart_705490 := by decide
  rcases family_descends (prefixWord ++ tailWord_705490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705492 : List Nat := [2, 4, 1, 2, 1, 3, 2, 2, 1, 4]
def baseStart_705492 : Nat := 118140960795 + 705492 * 2 ^ 59
def prefixEnd_705492 : Nat := 4983230072969 + 3 ^ 40 * 705492 * 2
def baseEnd_705492 : Nat := 241504329267905995337005

theorem tailTrace_705492 : CollatzResearch.WordTrace tailWord_705492 prefixEnd_705492 241504329267905995337005 := by
  unfold tailWord_705492
  simp only [CollatzResearch.WordTrace]
  refine ⟨12865703580065223643067365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17154271440086964857423153 12865703580065223643067365)
  ·
    refine ⟨2412319421262229433075131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12865703580065223643067365 2412319421262229433075131)
    ·
      refine ⟨3618479131893344149612697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2412319421262229433075131 3618479131893344149612697)
      ·
        refine ⟨2713859348920008112209523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3618479131893344149612697 2713859348920008112209523)
        ·
          refine ⟨4070789023380012168314285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2713859348920008112209523 4070789023380012168314285)
          ·
            refine ⟨1526545883767504563117857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4070789023380012168314285 1526545883767504563117857)
            ·
              refine ⟨1144909412825628422338393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1526545883767504563117857 1144909412825628422338393)
              ·
                refine ⟨858682059619221316753795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1144909412825628422338393 858682059619221316753795)
                ·
                  refine ⟨1288023089428831975130693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 858682059619221316753795 1288023089428831975130693)
                  ·
                    refine ⟨241504329267905995337005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1288023089428831975130693 241504329267905995337005)
                    ·
                      rfl

theorem cell22_705492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2, 2, 1, 4].length) (baseStart_705492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_705492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_705492 prefixEnd_705492 := by exact prefixLift 705492
  have htrace : WordTrace (prefixWord ++ tailWord_705492) baseStart_705492 baseEnd_705492 := by
    simpa [prefixWord, tailWord_705492, baseEnd_705492] using wordTrace_append hprefix tailTrace_705492
  have hstable : (prefixWord ++ tailWord_705492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705492).length < 2 ^ (prefixWord ++ tailWord_705492).sum := by decide
  have hdescent : baseEnd_705492 < baseStart_705492 := by decide
  rcases family_descends (prefixWord ++ tailWord_705492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705580 : List Nat := [2, 2, 1, 1, 1, 2, 6, 2, 5]
def baseStart_705580 : Nat := 118140960795 + 705580 * 2 ^ 59
def prefixEnd_705580 : Nat := 4983230072969 + 3 ^ 40 * 705580 * 2
def baseEnd_705580 : Nat := 80511484488767699712245

theorem tailTrace_705580 : CollatzResearch.WordTrace tailWord_705580 prefixEnd_705580 80511484488767699712245 := by
  unfold tailWord_705580
  simp only [CollatzResearch.WordTrace]
  refine ⟨12867308391905819157669097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17156411189207758876892129 12867308391905819157669097)
  ·
    refine ⟨9650481293929364368251823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12867308391905819157669097 9650481293929364368251823)
    ·
      refine ⟨14475721940894046552377735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9650481293929364368251823 14475721940894046552377735)
      ·
        refine ⟨21713582911341069828566603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14475721940894046552377735 21713582911341069828566603)
        ·
          refine ⟨32570374367011604742849905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21713582911341069828566603 32570374367011604742849905)
          ·
            refine ⟨24427780775258703557137429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32570374367011604742849905 24427780775258703557137429)
            ·
              refine ⟨1145052223840251729240817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 24427780775258703557137429 1145052223840251729240817)
              ·
                refine ⟨858789167880188796930613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1145052223840251729240817 858789167880188796930613)
                ·
                  refine ⟨80511484488767699712245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 858789167880188796930613 80511484488767699712245)
                  ·
                    rfl

theorem cell22_705580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 5].length) (baseStart_705580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_705580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_705580 prefixEnd_705580 := by exact prefixLift 705580
  have htrace : WordTrace (prefixWord ++ tailWord_705580) baseStart_705580 baseEnd_705580 := by
    simpa [prefixWord, tailWord_705580, baseEnd_705580] using wordTrace_append hprefix tailTrace_705580
  have hstable : (prefixWord ++ tailWord_705580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705580).length < 2 ^ (prefixWord ++ tailWord_705580).sum := by decide
  have hdescent : baseEnd_705580 < baseStart_705580 := by decide
  rcases family_descends (prefixWord ++ tailWord_705580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705610 : List Nat := [3, 1, 2, 1, 1, 2, 4, 1, 3, 4]
def baseStart_705610 : Nat := 118140960795 + 705610 * 2 ^ 59
def prefixEnd_705610 : Nat := 4983230072969 + 3 ^ 40 * 705610 * 2
def baseEnd_705610 : Nat := 241544723079393020886643

theorem tailTrace_705610 : CollatzResearch.WordTrace tailWord_705610 prefixEnd_705610 241544723079393020886643 := by
  unfold tailWord_705610
  simp only [CollatzResearch.WordTrace]
  refine ⟨6433927743425738359732571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17157140649135302292620189 6433927743425738359732571)
  ·
    refine ⟨9650891615138607539598857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6433927743425738359732571 9650891615138607539598857)
    ·
      refine ⟨7238168711353955654699143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9650891615138607539598857 7238168711353955654699143)
      ·
        refine ⟨10857253067030933482048715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7238168711353955654699143 10857253067030933482048715)
        ·
          refine ⟨16285879600546400223073073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10857253067030933482048715 16285879600546400223073073)
          ·
            refine ⟨12214409700409800167304805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16285879600546400223073073 12214409700409800167304805)
            ·
              refine ⟨2290201818826837531369651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12214409700409800167304805 2290201818826837531369651)
              ·
                refine ⟨3435302728240256297054477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2290201818826837531369651 3435302728240256297054477)
                ·
                  refine ⟨1288238523090096111395429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3435302728240256297054477 1288238523090096111395429)
                  ·
                    refine ⟨241544723079393020886643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1288238523090096111395429 241544723079393020886643)
                    ·
                      rfl

theorem cell22_705610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 1, 3, 4].length) (baseStart_705610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_705610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_705610 prefixEnd_705610 := by exact prefixLift 705610
  have htrace : WordTrace (prefixWord ++ tailWord_705610) baseStart_705610 baseEnd_705610 := by
    simpa [prefixWord, tailWord_705610, baseEnd_705610] using wordTrace_append hprefix tailTrace_705610
  have hstable : (prefixWord ++ tailWord_705610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705610).length < 2 ^ (prefixWord ++ tailWord_705610).sum := by decide
  have hdescent : baseEnd_705610 < baseStart_705610 := by decide
  rcases family_descends (prefixWord ++ tailWord_705610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705642 : List Nat := [3, 1, 3, 2, 2, 2, 2, 1, 6]
def baseStart_705642 : Nat := 118140960795 + 705642 * 2 ^ 59
def prefixEnd_705642 : Nat := 4983230072969 + 3 ^ 40 * 705642 * 2
def baseEnd_705642 : Nat := 80518559111118534695515

theorem tailTrace_705642 : CollatzResearch.WordTrace tailWord_705642 prefixEnd_705642 80518559111118534695515 := by
  unfold tailWord_705642
  simp only [CollatzResearch.WordTrace]
  refine ⟨6434219527396755726023795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17157918739724681936063453 6434219527396755726023795)
  ·
    refine ⟨9651329291095133589035693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6434219527396755726023795 9651329291095133589035693)
    ·
      refine ⟨3619248484160675095888385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9651329291095133589035693 3619248484160675095888385)
      ·
        refine ⟨2714436363120506321916289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3619248484160675095888385 2714436363120506321916289)
        ·
          refine ⟨2035827272340379741437217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2714436363120506321916289 2035827272340379741437217)
          ·
            refine ⟨1526870454255284806077913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2035827272340379741437217 1526870454255284806077913)
            ·
              refine ⟨1145152840691463604558435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1526870454255284806077913 1145152840691463604558435)
              ·
                refine ⟨1717729261037195406837653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1145152840691463604558435 1717729261037195406837653)
                ·
                  refine ⟨80518559111118534695515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1717729261037195406837653 80518559111118534695515)
                  ·
                    rfl

theorem cell22_705642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 2, 1, 6].length) (baseStart_705642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_705642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_705642 prefixEnd_705642 := by exact prefixLift 705642
  have htrace : WordTrace (prefixWord ++ tailWord_705642) baseStart_705642 baseEnd_705642 := by
    simpa [prefixWord, tailWord_705642, baseEnd_705642] using wordTrace_append hprefix tailTrace_705642
  have hstable : (prefixWord ++ tailWord_705642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705642).length < 2 ^ (prefixWord ++ tailWord_705642).sum := by decide
  have hdescent : baseEnd_705642 < baseStart_705642 := by decide
  rcases family_descends (prefixWord ++ tailWord_705642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705749 : List Nat := [1, 3, 2, 4, 1, 2, 2, 2, 5]
def baseStart_705749 : Nat := 118140960795 + 705749 * 2 ^ 59
def prefixEnd_705749 : Nat := 4983230072969 + 3 ^ 40 * 705749 * 2
def baseEnd_705749 : Nat := 80530768540014330553739

theorem tailTrace_705749 : CollatzResearch.WordTrace tailWord_705749 prefixEnd_705749 80530768540014330553739 := by
  unfold tailWord_705749
  simp only [CollatzResearch.WordTrace]
  refine ⟨25740780720199380178240301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17160520480132920118826867 25740780720199380178240301)
  ·
    refine ⟨9652792770074767566840113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25740780720199380178240301 9652792770074767566840113)
    ·
      refine ⟨7239594577556075675130085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9652792770074767566840113 7239594577556075675130085)
      ·
        refine ⟨1357423983291764189086891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7239594577556075675130085 1357423983291764189086891)
        ·
          refine ⟨2036135974937646283630337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1357423983291764189086891 2036135974937646283630337)
          ·
            refine ⟨1527101981203234712722753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2036135974937646283630337 1527101981203234712722753)
            ·
              refine ⟨1145326485902426034542065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1527101981203234712722753 1145326485902426034542065)
              ·
                refine ⟨858994864426819525906549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1145326485902426034542065 858994864426819525906549)
                ·
                  refine ⟨80530768540014330553739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 858994864426819525906549 80530768540014330553739)
                  ·
                    rfl

theorem cell22_705749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 2, 2, 5].length) (baseStart_705749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_705749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_705749 prefixEnd_705749 := by exact prefixLift 705749
  have htrace : WordTrace (prefixWord ++ tailWord_705749) baseStart_705749 baseEnd_705749 := by
    simpa [prefixWord, tailWord_705749, baseEnd_705749] using wordTrace_append hprefix tailTrace_705749
  have hstable : (prefixWord ++ tailWord_705749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705749).length < 2 ^ (prefixWord ++ tailWord_705749).sum := by decide
  have hdescent : baseEnd_705749 < baseStart_705749 := by decide
  rcases family_descends (prefixWord ++ tailWord_705749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705792 : List Nat := [2, 1, 1, 2, 1, 1, 3, 4, 4, 3]
def baseStart_705792 : Nat := 118140960795 + 705792 * 2 ^ 59
def prefixEnd_705792 : Nat := 4983230072969 + 3 ^ 40 * 705792 * 2
def baseEnd_705792 : Nat := 241607025398805212836085

theorem tailTrace_705792 : CollatzResearch.WordTrace tailWord_705792 prefixEnd_705792 241607025398805212836085 := by
  unfold tailWord_705792
  simp only [CollatzResearch.WordTrace]
  refine ⟨12871174529521799261027815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17161566039362399014703753 12871174529521799261027815)
  ·
    refine ⟨19306761794282698891541723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12871174529521799261027815 19306761794282698891541723)
    ·
      refine ⟨28960142691424048337312585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19306761794282698891541723 28960142691424048337312585)
      ·
        refine ⟨21720107018568036252984439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28960142691424048337312585 21720107018568036252984439)
        ·
          refine ⟨32580160527852054379476659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21720107018568036252984439 32580160527852054379476659)
          ·
            refine ⟨48870240791778081569214989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32580160527852054379476659 48870240791778081569214989)
            ·
              refine ⟨18326340296916780588455621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48870240791778081569214989 18326340296916780588455621)
              ·
                refine ⟨3436188805671896360335429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18326340296916780588455621 3436188805671896360335429)
                ·
                  refine ⟨644285401063480567562893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3436188805671896360335429 644285401063480567562893)
                  ·
                    refine ⟨241607025398805212836085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 644285401063480567562893 241607025398805212836085)
                    ·
                      rfl

theorem cell22_705792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 4, 4, 3].length) (baseStart_705792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_705792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_705792 prefixEnd_705792 := by exact prefixLift 705792
  have htrace : WordTrace (prefixWord ++ tailWord_705792) baseStart_705792 baseEnd_705792 := by
    simpa [prefixWord, tailWord_705792, baseEnd_705792] using wordTrace_append hprefix tailTrace_705792
  have hstable : (prefixWord ++ tailWord_705792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705792).length < 2 ^ (prefixWord ++ tailWord_705792).sum := by decide
  have hdescent : baseEnd_705792 < baseStart_705792 := by decide
  rcases family_descends (prefixWord ++ tailWord_705792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705796 : List Nat := [2, 3, 2, 2, 2, 1, 4, 1, 1, 4]
def baseStart_705796 : Nat := 118140960795 + 705796 * 2 ^ 59
def prefixEnd_705796 : Nat := 4983230072969 + 3 ^ 40 * 705796 * 2
def baseEnd_705796 : Nat := 241608394680550535736073

theorem tailTrace_705796 : CollatzResearch.WordTrace tailWord_705796 prefixEnd_705796 241608394680550535736073 := by
  unfold tailWord_705796
  simp only [CollatzResearch.WordTrace]
  refine ⟨12871247475514553602600621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17161663300686071470134161 12871247475514553602600621)
  ·
    refine ⟨4826717803317957600975233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12871247475514553602600621 4826717803317957600975233)
    ·
      refine ⟨3620038352488468200731425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4826717803317957600975233 3620038352488468200731425)
      ·
        refine ⟨2715028764366351150548569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3620038352488468200731425 2715028764366351150548569)
        ·
          refine ⟨2036271573274763362911427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2715028764366351150548569 2036271573274763362911427)
          ·
            refine ⟨3054407359912145044367141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2036271573274763362911427 3054407359912145044367141)
            ·
              refine ⟨572701379983527195818839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3054407359912145044367141 572701379983527195818839)
              ·
                refine ⟨859052069975290793728259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 572701379983527195818839 859052069975290793728259)
                ·
                  refine ⟨1288578104962936190592389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 859052069975290793728259 1288578104962936190592389)
                  ·
                    refine ⟨241608394680550535736073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1288578104962936190592389 241608394680550535736073)
                    ·
                      rfl

theorem cell22_705796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 4, 1, 1, 4].length) (baseStart_705796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_705796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_705796 prefixEnd_705796 := by exact prefixLift 705796
  have htrace : WordTrace (prefixWord ++ tailWord_705796) baseStart_705796 baseEnd_705796 := by
    simpa [prefixWord, tailWord_705796, baseEnd_705796] using wordTrace_append hprefix tailTrace_705796
  have hstable : (prefixWord ++ tailWord_705796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705796).length < 2 ^ (prefixWord ++ tailWord_705796).sum := by decide
  have hdescent : baseEnd_705796 < baseStart_705796 := by decide
  rcases family_descends (prefixWord ++ tailWord_705796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705826 : List Nat := [3, 3, 1, 1, 4, 2, 1, 1, 1, 5]
def baseStart_705826 : Nat := 118140960795 + 705826 * 2 ^ 59
def prefixEnd_705826 : Nat := 4983230072969 + 3 ^ 40 * 705826 * 2
def baseEnd_705826 : Nat := 241618664293640457485981

theorem tailTrace_705826 : CollatzResearch.WordTrace tailWord_705826 prefixEnd_705826 241618664293640457485981 := by
  unfold tailWord_705826
  simp only [CollatzResearch.WordTrace]
  refine ⟨6435897285230105582198333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17162392760613614885862221 6435897285230105582198333)
  ·
    refine ⟨2413461481961289593324375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6435897285230105582198333 2413461481961289593324375)
    ·
      refine ⟨3620192222941934389986563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2413461481961289593324375 3620192222941934389986563)
      ·
        refine ⟨5430288334412901584979845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3620192222941934389986563 5430288334412901584979845)
        ·
          refine ⟨1018179062702419047183721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5430288334412901584979845 1018179062702419047183721)
          ·
            refine ⟨763634297026814285387791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1018179062702419047183721 763634297026814285387791)
            ·
              refine ⟨1145451445540221428081687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 763634297026814285387791 1145451445540221428081687)
              ·
                refine ⟨1718177168310332142122531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1145451445540221428081687 1718177168310332142122531)
                ·
                  refine ⟨2577265752465498213183797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1718177168310332142122531 2577265752465498213183797)
                  ·
                    refine ⟨241618664293640457485981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2577265752465498213183797 241618664293640457485981)
                    ·
                      rfl

theorem cell22_705826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 1, 1, 1, 5].length) (baseStart_705826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_705826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_705826 prefixEnd_705826 := by exact prefixLift 705826
  have htrace : WordTrace (prefixWord ++ tailWord_705826) baseStart_705826 baseEnd_705826 := by
    simpa [prefixWord, tailWord_705826, baseEnd_705826] using wordTrace_append hprefix tailTrace_705826
  have hstable : (prefixWord ++ tailWord_705826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705826).length < 2 ^ (prefixWord ++ tailWord_705826).sum := by decide
  have hdescent : baseEnd_705826 < baseStart_705826 := by decide
  rcases family_descends (prefixWord ++ tailWord_705826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705862 : List Nat := [6, 1, 1, 3, 1, 1, 3, 2, 4]
def baseStart_705862 : Nat := 118140960795 + 705862 * 2 ^ 59
def prefixEnd_705862 : Nat := 4983230072969 + 3 ^ 40 * 705862 * 2
def baseEnd_705862 : Nat := 80543662609782787861957

theorem tailTrace_705862 : CollatzResearch.WordTrace tailWord_705862 prefixEnd_705862 80543662609782787861957 := by
  unfold tailWord_705862
  simp only [CollatzResearch.WordTrace]
  refine ⟨804528192774687514909495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 17163268112526666984735893 804528192774687514909495)
  ·
    refine ⟨1206792289162031272364243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 804528192774687514909495 1206792289162031272364243)
    ·
      refine ⟨1810188433743046908546365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1206792289162031272364243 1810188433743046908546365)
      ·
        refine ⟨678820662653642590704887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1810188433743046908546365 678820662653642590704887)
        ·
          refine ⟨1018230993980463886057331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 678820662653642590704887 1018230993980463886057331)
          ·
            refine ⟨1527346490970695829085997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1018230993980463886057331 1527346490970695829085997)
            ·
              refine ⟨572754934114010935907249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1527346490970695829085997 572754934114010935907249)
              ·
                refine ⟨429566200585508201930437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 572754934114010935907249 429566200585508201930437)
                ·
                  refine ⟨80543662609782787861957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 429566200585508201930437 80543662609782787861957)
                  ·
                    rfl

theorem cell22_705862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 3, 2, 4].length) (baseStart_705862 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_705862 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_705862 prefixEnd_705862 := by exact prefixLift 705862
  have htrace : WordTrace (prefixWord ++ tailWord_705862) baseStart_705862 baseEnd_705862 := by
    simpa [prefixWord, tailWord_705862, baseEnd_705862] using wordTrace_append hprefix tailTrace_705862
  have hstable : (prefixWord ++ tailWord_705862).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705862).length < 2 ^ (prefixWord ++ tailWord_705862).sum := by decide
  have hdescent : baseEnd_705862 < baseStart_705862 := by decide
  rcases family_descends (prefixWord ++ tailWord_705862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705882 : List Nat := [3, 1, 1, 2, 1, 2, 2, 3, 2, 5]
def baseStart_705882 : Nat := 118140960795 + 705882 * 2 ^ 59
def prefixEnd_705882 : Nat := 4983230072969 + 3 ^ 40 * 705882 * 2
def baseEnd_705882 : Nat := 241637834238074978085809

theorem tailTrace_705882 : CollatzResearch.WordTrace tailWord_705882 prefixEnd_705882 241637834238074978085809 := by
  unfold tailWord_705882
  simp only [CollatzResearch.WordTrace]
  refine ⟨6436407907179385973207975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17163754419145029261887933 6436407907179385973207975)
  ·
    refine ⟨9654611860769078959811963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6436407907179385973207975 9654611860769078959811963)
    ·
      refine ⟨14481917791153618439717945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9654611860769078959811963 14481917791153618439717945)
      ·
        refine ⟨10861438343365213829788459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14481917791153618439717945 10861438343365213829788459)
        ·
          refine ⟨16292157515047820744682689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10861438343365213829788459 16292157515047820744682689)
          ·
            refine ⟨12219118136285865558512017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16292157515047820744682689 12219118136285865558512017)
            ·
              refine ⟨9164338602214399168884013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12219118136285865558512017 9164338602214399168884013)
              ·
                refine ⟨3436626975830399688331505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9164338602214399168884013 3436626975830399688331505)
                ·
                  refine ⟨2577470231872799766248629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3436626975830399688331505 2577470231872799766248629)
                  ·
                    refine ⟨241637834238074978085809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2577470231872799766248629 241637834238074978085809)
                    ·
                      rfl

theorem cell22_705882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 3, 2, 5].length) (baseStart_705882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_705882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_705882 prefixEnd_705882 := by exact prefixLift 705882
  have htrace : WordTrace (prefixWord ++ tailWord_705882) baseStart_705882 baseEnd_705882 := by
    simpa [prefixWord, tailWord_705882, baseEnd_705882] using wordTrace_append hprefix tailTrace_705882
  have hstable : (prefixWord ++ tailWord_705882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705882).length < 2 ^ (prefixWord ++ tailWord_705882).sum := by decide
  have hdescent : baseEnd_705882 < baseStart_705882 := by decide
  rcases family_descends (prefixWord ++ tailWord_705882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705922 : List Nat := [3, 4, 2, 1, 1, 1, 4, 2, 1, 3]
def baseStart_705922 : Nat := 118140960795 + 705922 * 2 ^ 59
def prefixEnd_705922 : Nat := 4983230072969 + 3 ^ 40 * 705922 * 2
def baseEnd_705922 : Nat := 241651527055528207085687

theorem tailTrace_705922 : CollatzResearch.WordTrace tailWord_705922 prefixEnd_705922 241651527055528207085687 := by
  unfold tailWord_705922
  simp only [CollatzResearch.WordTrace]
  refine ⟨6436772637143157681072005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17164727032381753816192013 6436772637143157681072005)
  ·
    refine ⟨1206894869464342065201001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6436772637143157681072005 1206894869464342065201001)
    ·
      refine ⟨905171152098256548900751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1206894869464342065201001 905171152098256548900751)
      ·
        refine ⟨1357756728147384823351127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 905171152098256548900751 1357756728147384823351127)
        ·
          refine ⟨2036635092221077235026691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1357756728147384823351127 2036635092221077235026691)
          ·
            refine ⟨3054952638331615852540037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2036635092221077235026691 3054952638331615852540037)
            ·
              refine ⟨572803619687177972351257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3054952638331615852540037 572803619687177972351257)
              ·
                refine ⟨429602714765383479263443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 572803619687177972351257 429602714765383479263443)
                ·
                  refine ⟨644404072148075218895165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 429602714765383479263443 644404072148075218895165)
                  ·
                    refine ⟨241651527055528207085687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 644404072148075218895165 241651527055528207085687)
                    ·
                      rfl

theorem cell22_705922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_705922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_705922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_705922 prefixEnd_705922 := by exact prefixLift 705922
  have htrace : WordTrace (prefixWord ++ tailWord_705922) baseStart_705922 baseEnd_705922 := by
    simpa [prefixWord, tailWord_705922, baseEnd_705922] using wordTrace_append hprefix tailTrace_705922
  have hstable : (prefixWord ++ tailWord_705922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705922).length < 2 ^ (prefixWord ++ tailWord_705922).sum := by decide
  have hdescent : baseEnd_705922 < baseStart_705922 := by decide
  rcases family_descends (prefixWord ++ tailWord_705922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705959 : List Nat := [1, 1, 6, 1, 1, 1, 3, 1, 1, 6]
def baseStart_705959 : Nat := 118140960795 + 705959 * 2 ^ 59
def prefixEnd_705959 : Nat := 4983230072969 + 3 ^ 40 * 705959 * 2
def baseEnd_705959 : Nat := 241664192911672443910573

theorem tailTrace_705959 : CollatzResearch.WordTrace tailWord_705959 prefixEnd_705959 241664192911672443910573 := by
  unfold tailWord_705959
  simp only [CollatzResearch.WordTrace]
  refine ⟨25748440049438586043384931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17165626699625724028923287 25748440049438586043384931)
  ·
    refine ⟨38622660074157879065077397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25748440049438586043384931 38622660074157879065077397)
    ·
      refine ⟨1810437190976150581175503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 38622660074157879065077397 1810437190976150581175503)
      ·
        refine ⟨2715655786464225871763255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1810437190976150581175503 2715655786464225871763255)
        ·
          refine ⟨4073483679696338807644883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2715655786464225871763255 4073483679696338807644883)
          ·
            refine ⟨6110225519544508211467325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4073483679696338807644883 6110225519544508211467325)
            ·
              refine ⟨2291334569829190579300247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6110225519544508211467325 2291334569829190579300247)
              ·
                refine ⟨3437001854743785868950371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2291334569829190579300247 3437001854743785868950371)
                ·
                  refine ⟨5155502782115678803425557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3437001854743785868950371 5155502782115678803425557)
                  ·
                    refine ⟨241664192911672443910573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5155502782115678803425557 241664192911672443910573)
                    ·
                      rfl

theorem cell22_705959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_705959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_705959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_705959 prefixEnd_705959 := by exact prefixLift 705959
  have htrace : WordTrace (prefixWord ++ tailWord_705959) baseStart_705959 baseEnd_705959 := by
    simpa [prefixWord, tailWord_705959, baseEnd_705959] using wordTrace_append hprefix tailTrace_705959
  have hstable : (prefixWord ++ tailWord_705959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705959).length < 2 ^ (prefixWord ++ tailWord_705959).sum := by decide
  have hdescent : baseEnd_705959 < baseStart_705959 := by decide
  rcases family_descends (prefixWord ++ tailWord_705959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705965 : List Nat := [1, 5, 2, 2, 1, 3, 2, 1, 1, 4]
def baseStart_705965 : Nat := 118140960795 + 705965 * 2 ^ 59
def prefixEnd_705965 : Nat := 4983230072969 + 3 ^ 40 * 705965 * 2
def baseEnd_705965 : Nat := 241666246834290428260555

theorem tailTrace_705965 : CollatzResearch.WordTrace tailWord_705965 prefixEnd_705965 241666246834290428260555 := by
  unfold tailWord_705965
  simp only [CollatzResearch.WordTrace]
  refine ⟨25748658887416849068103349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17165772591611232712068899 25748658887416849068103349)
  ·
    refine ⟨2413936770695329600134689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25748658887416849068103349 2413936770695329600134689)
    ·
      refine ⟨1810452578021497200101017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2413936770695329600134689 1810452578021497200101017)
      ·
        refine ⟨1357839433516122900075763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1810452578021497200101017 1357839433516122900075763)
        ·
          refine ⟨2036759150274184350113645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1357839433516122900075763 2036759150274184350113645)
          ·
            refine ⟨763784681352819131292617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2036759150274184350113645 763784681352819131292617)
            ·
              refine ⟨572838511014614348469463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 763784681352819131292617 572838511014614348469463)
              ·
                refine ⟨859257766521921522704195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 572838511014614348469463 859257766521921522704195)
                ·
                  refine ⟨1288886649782882284056293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 859257766521921522704195 1288886649782882284056293)
                  ·
                    refine ⟨241666246834290428260555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1288886649782882284056293 241666246834290428260555)
                    ·
                      rfl

theorem cell22_705965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 2, 1, 1, 4].length) (baseStart_705965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_705965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_705965 prefixEnd_705965 := by exact prefixLift 705965
  have htrace : WordTrace (prefixWord ++ tailWord_705965) baseStart_705965 baseEnd_705965 := by
    simpa [prefixWord, tailWord_705965, baseEnd_705965] using wordTrace_append hprefix tailTrace_705965
  have hstable : (prefixWord ++ tailWord_705965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705965).length < 2 ^ (prefixWord ++ tailWord_705965).sum := by decide
  have hdescent : baseEnd_705965 < baseStart_705965 := by decide
  rcases family_descends (prefixWord ++ tailWord_705965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705987 : List Nat := [1, 1, 1, 3, 1, 1, 4, 1, 1, 8]
def baseStart_705987 : Nat := 118140960795 + 705987 * 2 ^ 59
def prefixEnd_705987 : Nat := 4983230072969 + 3 ^ 40 * 705987 * 2
def baseEnd_705987 : Nat := 241673777883889704210487

theorem tailTrace_705987 : CollatzResearch.WordTrace tailWord_705987 prefixEnd_705987 241673777883889704210487 := by
  unfold tailWord_705987
  simp only [CollatzResearch.WordTrace]
  refine ⟨25749461293337146825404215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17166307528891431216936143 25749461293337146825404215)
  ·
    refine ⟨38624191940005720238106323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25749461293337146825404215 38624191940005720238106323)
    ·
      refine ⟨57936287910008580357159485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38624191940005720238106323 57936287910008580357159485)
      ·
        refine ⟨21726107966253217633934807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57936287910008580357159485 21726107966253217633934807)
        ·
          refine ⟨32589161949379826450902211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21726107966253217633934807 32589161949379826450902211)
          ·
            refine ⟨48883742924069739676353317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32589161949379826450902211 48883742924069739676353317)
            ·
              refine ⟨9165701798263076189316247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48883742924069739676353317 9165701798263076189316247)
              ·
                refine ⟨13748552697394614283974371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9165701798263076189316247 13748552697394614283974371)
                ·
                  refine ⟨20622829046091921425961557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13748552697394614283974371 20622829046091921425961557)
                  ·
                    refine ⟨241673777883889704210487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 20622829046091921425961557 241673777883889704210487)
                    ·
                      rfl

theorem cell22_705987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 8].length) (baseStart_705987 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_705987 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_705987 prefixEnd_705987 := by exact prefixLift 705987
  have htrace : WordTrace (prefixWord ++ tailWord_705987) baseStart_705987 baseEnd_705987 := by
    simpa [prefixWord, tailWord_705987, baseEnd_705987] using wordTrace_append hprefix tailTrace_705987
  have hstable : (prefixWord ++ tailWord_705987).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705987).length < 2 ^ (prefixWord ++ tailWord_705987).sum := by decide
  have hdescent : baseEnd_705987 < baseStart_705987 := by decide
  rcases family_descends (prefixWord ++ tailWord_705987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706019 : List Nat := [1, 1, 1, 6, 2, 1, 1, 2, 7]
def baseStart_706019 : Nat := 118140960795 + 706019 * 2 ^ 59
def prefixEnd_706019 : Nat := 4983230072969 + 3 ^ 40 * 706019 * 2
def baseEnd_706019 : Nat := 80561577379284095803463

theorem tailTrace_706019 : CollatzResearch.WordTrace tailWord_706019 prefixEnd_706019 80561577379284095803463 := by
  unfold tailWord_706019
  simp only [CollatzResearch.WordTrace]
  refine ⟨25750628429221216290569111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17167085619480810860379407 25750628429221216290569111)
  ·
    refine ⟨38625942643831824435853667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25750628429221216290569111 38625942643831824435853667)
    ·
      refine ⟨57938913965747736653780501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38625942643831824435853667 57938913965747736653780501)
      ·
        refine ⟨2715886592144425155645961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 57938913965747736653780501 2715886592144425155645961)
        ·
          refine ⟨2036914944108318866734471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2715886592144425155645961 2036914944108318866734471)
          ·
            refine ⟨3055372416162478300101707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2036914944108318866734471 3055372416162478300101707)
            ·
              refine ⟨4583058624243717450152561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3055372416162478300101707 4583058624243717450152561)
              ·
                refine ⟨3437293968182788087614421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4583058624243717450152561 3437293968182788087614421)
                ·
                  refine ⟨80561577379284095803463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3437293968182788087614421 80561577379284095803463)
                  ·
                    rfl

theorem cell22_706019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 2, 7].length) (baseStart_706019 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_706019 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_706019 prefixEnd_706019 := by exact prefixLift 706019
  have htrace : WordTrace (prefixWord ++ tailWord_706019) baseStart_706019 baseEnd_706019 := by
    simpa [prefixWord, tailWord_706019, baseEnd_706019] using wordTrace_append hprefix tailTrace_706019
  have hstable : (prefixWord ++ tailWord_706019).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706019).length < 2 ^ (prefixWord ++ tailWord_706019).sum := by decide
  have hdescent : baseEnd_706019 < baseStart_706019 := by decide
  rcases family_descends (prefixWord ++ tailWord_706019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706040 : List Nat := [2, 1, 2, 1, 1, 6, 3, 2, 1, 3]
def baseStart_706040 : Nat := 118140960795 + 706040 * 2 ^ 59
def prefixEnd_706040 : Nat := 4983230072969 + 3 ^ 40 * 706040 * 2
def baseEnd_706040 : Nat := 241691920867015232635325

theorem tailTrace_706040 : CollatzResearch.WordTrace tailWord_706040 prefixEnd_706040 241691920867015232635325 := by
  unfold tailWord_706040
  simp only [CollatzResearch.WordTrace]
  refine ⟨12875697181072568438541787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17167596241430091251389049 12875697181072568438541787)
  ·
    refine ⟨19313545771608852657812681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12875697181072568438541787 19313545771608852657812681)
    ·
      refine ⟨14485159328706639493359511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19313545771608852657812681 14485159328706639493359511)
      ·
        refine ⟨21727738993059959240039267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14485159328706639493359511 21727738993059959240039267)
        ·
          refine ⟨32591608489589938860058901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21727738993059959240039267 32591608489589938860058901)
          ·
            refine ⟨1527731647949528384065261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 32591608489589938860058901 1527731647949528384065261)
            ·
              refine ⟨572899367981073144024473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1527731647949528384065261 572899367981073144024473)
              ·
                refine ⟨429674525985804858018355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 572899367981073144024473 429674525985804858018355)
                ·
                  refine ⟨644511788978707287027533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 429674525985804858018355 644511788978707287027533)
                  ·
                    refine ⟨241691920867015232635325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 644511788978707287027533 241691920867015232635325)
                    ·
                      rfl

theorem cell22_706040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 3, 2, 1, 3].length) (baseStart_706040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_706040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_706040 prefixEnd_706040 := by exact prefixLift 706040
  have htrace : WordTrace (prefixWord ++ tailWord_706040) baseStart_706040 baseEnd_706040 := by
    simpa [prefixWord, tailWord_706040, baseEnd_706040] using wordTrace_append hprefix tailTrace_706040
  have hstable : (prefixWord ++ tailWord_706040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706040).length < 2 ^ (prefixWord ++ tailWord_706040).sum := by decide
  have hdescent : baseEnd_706040 < baseStart_706040 := by decide
  rcases family_descends (prefixWord ++ tailWord_706040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706079 : List Nat := [1, 1, 2, 4, 1, 1, 3, 1, 3, 5]
def baseStart_706079 : Nat := 118140960795 + 706079 * 2 ^ 59
def prefixEnd_706079 : Nat := 4983230072969 + 3 ^ 40 * 706079 * 2
def baseEnd_706079 : Nat := 241705271364032130910205

theorem tailTrace_706079 : CollatzResearch.WordTrace tailWord_706079 prefixEnd_706079 241705271364032130910205 := by
  unfold tailWord_706079
  simp only [CollatzResearch.WordTrace]
  refine ⟨25752816809003846537753291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17168544539335897691835527 25752816809003846537753291)
  ·
    refine ⟨38629225213505769806629937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25752816809003846537753291 38629225213505769806629937)
    ·
      refine ⟨28971918910129327354972453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38629225213505769806629937 28971918910129327354972453)
      ·
        refine ⟨5432234795649248879057335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28971918910129327354972453 5432234795649248879057335)
        ·
          refine ⟨8148352193473873318586003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5432234795649248879057335 8148352193473873318586003)
          ·
            refine ⟨12222528290210809977879005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8148352193473873318586003 12222528290210809977879005)
            ·
              refine ⟨4583448108829053741704627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12222528290210809977879005 4583448108829053741704627)
              ·
                refine ⟨6875172163243580612556941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4583448108829053741704627 6875172163243580612556941)
                ·
                  refine ⟨2578189561216342729708853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6875172163243580612556941 2578189561216342729708853)
                  ·
                    refine ⟨241705271364032130910205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2578189561216342729708853 241705271364032130910205)
                    ·
                      rfl

theorem cell22_706079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 1, 3, 5].length) (baseStart_706079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_706079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_706079 prefixEnd_706079 := by exact prefixLift 706079
  have htrace : WordTrace (prefixWord ++ tailWord_706079) baseStart_706079 baseEnd_706079 := by
    simpa [prefixWord, tailWord_706079, baseEnd_706079] using wordTrace_append hprefix tailTrace_706079
  have hstable : (prefixWord ++ tailWord_706079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706079).length < 2 ^ (prefixWord ++ tailWord_706079).sum := by decide
  have hdescent : baseEnd_706079 < baseStart_706079 := by decide
  rcases family_descends (prefixWord ++ tailWord_706079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706113 : List Nat := [1, 2, 5, 1, 1, 1, 1, 5, 2, 3]
def baseStart_706113 : Nat := 118140960795 + 706113 * 2 ^ 59
def prefixEnd_706113 : Nat := 4983230072969 + 3 ^ 40 * 706113 * 2
def baseEnd_706113 : Nat := 241716910258867375560101

theorem tailTrace_706113 : CollatzResearch.WordTrace tailWord_706113 prefixEnd_706113 241716910258867375560101 := by
  unfold tailWord_706113
  simp only [CollatzResearch.WordTrace]
  refine ⟨25754056890880670344490993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17169371260587113562993995 25754056890880670344490993)
  ·
    refine ⟨19315542668160502758368245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25754056890880670344490993 19315542668160502758368245)
    ·
      refine ⟨1810832125140047133597023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19315542668160502758368245 1810832125140047133597023)
      ·
        refine ⟨2716248187710070700395535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1810832125140047133597023 2716248187710070700395535)
        ·
          refine ⟨4074372281565106050593303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2716248187710070700395535 4074372281565106050593303)
          ·
            refine ⟨6111558422347659075889955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4074372281565106050593303 6111558422347659075889955)
            ·
              refine ⟨9167337633521488613834933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6111558422347659075889955 9167337633521488613834933)
              ·
                refine ⟨859437903142639557547025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9167337633521488613834933 859437903142639557547025)
                ·
                  refine ⟨644578427356979668160269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 859437903142639557547025 644578427356979668160269)
                  ·
                    refine ⟨241716910258867375560101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 644578427356979668160269 241716910258867375560101)
                    ·
                      rfl

theorem cell22_706113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 5, 2, 3].length) (baseStart_706113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_706113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_706113 prefixEnd_706113 := by exact prefixLift 706113
  have htrace : WordTrace (prefixWord ++ tailWord_706113) baseStart_706113 baseEnd_706113 := by
    simpa [prefixWord, tailWord_706113, baseEnd_706113] using wordTrace_append hprefix tailTrace_706113
  have hstable : (prefixWord ++ tailWord_706113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706113).length < 2 ^ (prefixWord ++ tailWord_706113).sum := by decide
  have hdescent : baseEnd_706113 < baseStart_706113 := by decide
  rcases family_descends (prefixWord ++ tailWord_706113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706252 : List Nat := [2, 2, 1, 5, 2, 1, 3, 1, 1, 4]
def baseStart_706252 : Nat := 118140960795 + 706252 * 2 ^ 59
def prefixEnd_706252 : Nat := 4983230072969 + 3 ^ 40 * 706252 * 2
def baseEnd_706252 : Nat := 241764492799517346334675

theorem tailTrace_706252 : CollatzResearch.WordTrace tailWord_706252 prefixEnd_706252 241764492799517346334675 := by
  unfold tailWord_706252
  simp only [CollatzResearch.WordTrace]
  refine ⟨12879563318688548541900505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17172751091584731389200673 12879563318688548541900505)
  ·
    refine ⟨9659672489016411406425379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12879563318688548541900505 9659672489016411406425379)
    ·
      refine ⟨14489508733524617109638069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9659672489016411406425379 14489508733524617109638069)
      ·
        refine ⟨1358391443767932854028569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14489508733524617109638069 1358391443767932854028569)
        ·
          refine ⟨1018793582825949640521427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1358391443767932854028569 1018793582825949640521427)
          ·
            refine ⟨1528190374238924460782141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1018793582825949640521427 1528190374238924460782141)
            ·
              refine ⟨573071390339596672793303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1528190374238924460782141 573071390339596672793303)
              ·
                refine ⟨859607085509395009189955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 573071390339596672793303 859607085509395009189955)
                ·
                  refine ⟨1289410628264092513784933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 859607085509395009189955 1289410628264092513784933)
                  ·
                    refine ⟨241764492799517346334675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1289410628264092513784933 241764492799517346334675)
                    ·
                      rfl

theorem cell22_706252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 3, 1, 1, 4].length) (baseStart_706252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_706252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_706252 prefixEnd_706252 := by exact prefixLift 706252
  have htrace : WordTrace (prefixWord ++ tailWord_706252) baseStart_706252 baseEnd_706252 := by
    simpa [prefixWord, tailWord_706252, baseEnd_706252] using wordTrace_append hprefix tailTrace_706252
  have hstable : (prefixWord ++ tailWord_706252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706252).length < 2 ^ (prefixWord ++ tailWord_706252).sum := by decide
  have hdescent : baseEnd_706252 < baseStart_706252 := by decide
  rcases family_descends (prefixWord ++ tailWord_706252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706265 : List Nat := [1, 2, 1, 2, 3, 4, 2, 2, 2, 3]
def baseStart_706265 : Nat := 118140960795 + 706265 * 2 ^ 59
def prefixEnd_706265 : Nat := 4983230072969 + 3 ^ 40 * 706265 * 2
def baseEnd_706265 : Nat := 241768942965189645759635

theorem tailTrace_706265 : CollatzResearch.WordTrace tailWord_706265 prefixEnd_706265 241768942965189645759635 := by
  unfold tailWord_706265
  simp only [CollatzResearch.WordTrace]
  refine ⟨25759600786330000304024249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17173067190886666869349499 25759600786330000304024249)
  ·
    refine ⟨19319700589747500228018187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25759600786330000304024249 19319700589747500228018187)
    ·
      refine ⟨28979550884621250342027281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19319700589747500228018187 28979550884621250342027281)
      ·
        refine ⟨21734663163465937756520461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28979550884621250342027281 21734663163465937756520461)
        ·
          refine ⟨8150498686299726658695173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21734663163465937756520461 8150498686299726658695173)
          ·
            refine ⟨1528218503681198748505345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8150498686299726658695173 1528218503681198748505345)
            ·
              refine ⟨1146163877760899061379009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1528218503681198748505345 1146163877760899061379009)
              ·
                refine ⟨859622908320674296034257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1146163877760899061379009 859622908320674296034257)
                ·
                  refine ⟨644717181240505722025693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 859622908320674296034257 644717181240505722025693)
                  ·
                    refine ⟨241768942965189645759635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 644717181240505722025693 241768942965189645759635)
                    ·
                      rfl

theorem cell22_706265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 2, 2, 2, 3].length) (baseStart_706265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_706265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_706265 prefixEnd_706265 := by exact prefixLift 706265
  have htrace : WordTrace (prefixWord ++ tailWord_706265) baseStart_706265 baseEnd_706265 := by
    simpa [prefixWord, tailWord_706265, baseEnd_706265] using wordTrace_append hprefix tailTrace_706265
  have hstable : (prefixWord ++ tailWord_706265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706265).length < 2 ^ (prefixWord ++ tailWord_706265).sum := by decide
  have hdescent : baseEnd_706265 < baseStart_706265 := by decide
  rcases family_descends (prefixWord ++ tailWord_706265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706327 : List Nat := [1, 1, 3, 4, 2, 1, 2, 4, 1, 3]
def baseStart_706327 : Nat := 118140960795 + 706327 * 2 ^ 59
def prefixEnd_706327 : Nat := 4983230072969 + 3 ^ 40 * 706327 * 2
def baseEnd_706327 : Nat := 241790166832242150709445

theorem tailTrace_706327 : CollatzResearch.WordTrace tailWord_706327 prefixEnd_706327 241790166832242150709445 := by
  unfold tailWord_706327
  simp only [CollatzResearch.WordTrace]
  refine ⟨25761862112105384892781235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17174574741403589928520823 25761862112105384892781235)
  ·
    refine ⟨38642793168158077339171853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25761862112105384892781235 38642793168158077339171853)
    ·
      refine ⟨14491047438059279002189445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38642793168158077339171853 14491047438059279002189445)
      ·
        refine ⟨2717071394636114812910521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14491047438059279002189445 2717071394636114812910521)
        ·
          refine ⟨2037803545977086109682891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2717071394636114812910521 2037803545977086109682891)
          ·
            refine ⟨3056705318965629164524337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2037803545977086109682891 3056705318965629164524337)
            ·
              refine ⟨2292528989224221873393253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3056705318965629164524337 2292528989224221873393253)
              ·
                refine ⟨429849185479541601261235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2292528989224221873393253 429849185479541601261235)
                ·
                  refine ⟨644773778219312401891853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 429849185479541601261235 644773778219312401891853)
                  ·
                    refine ⟨241790166832242150709445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 644773778219312401891853 241790166832242150709445)
                    ·
                      rfl

theorem cell22_706327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 4, 1, 3].length) (baseStart_706327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_706327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_706327 prefixEnd_706327 := by exact prefixLift 706327
  have htrace : WordTrace (prefixWord ++ tailWord_706327) baseStart_706327 baseEnd_706327 := by
    simpa [prefixWord, tailWord_706327, baseEnd_706327] using wordTrace_append hprefix tailTrace_706327
  have hstable : (prefixWord ++ tailWord_706327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706327).length < 2 ^ (prefixWord ++ tailWord_706327).sum := by decide
  have hdescent : baseEnd_706327 < baseStart_706327 := by decide
  rcases family_descends (prefixWord ++ tailWord_706327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706338 : List Nat := [3, 3, 1, 1, 2, 1, 1, 3, 2, 5]
def baseStart_706338 : Nat := 118140960795 + 706338 * 2 ^ 59
def prefixEnd_706338 : Nat := 4983230072969 + 3 ^ 40 * 706338 * 2
def baseEnd_706338 : Nat := 241793932357041788684411

theorem tailTrace_706338 : CollatzResearch.WordTrace tailWord_706338 prefixEnd_706338 241793932357041788684411 := by
  unfold tailWord_706338
  simp only [CollatzResearch.WordTrace]
  refine ⟨6440565828766383442857917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17174842210043689180954445 6440565828766383442857917)
  ·
    refine ⟨2415212185787393791071719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6440565828766383442857917 2415212185787393791071719)
    ·
      refine ⟨3622818278681090686607579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2415212185787393791071719 3622818278681090686607579)
      ·
        refine ⟨5434227418021636029911369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3622818278681090686607579 5434227418021636029911369)
        ·
          refine ⟨4075670563516227022433527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5434227418021636029911369 4075670563516227022433527)
          ·
            refine ⟨6113505845274340533650291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4075670563516227022433527 6113505845274340533650291)
            ·
              refine ⟨9170258767911510800475437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6113505845274340533650291 9170258767911510800475437)
              ·
                refine ⟨3438847037966816550178289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9170258767911510800475437 3438847037966816550178289)
                ·
                  refine ⟨2579135278475112412633717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3438847037966816550178289 2579135278475112412633717)
                  ·
                    refine ⟨241793932357041788684411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2579135278475112412633717 241793932357041788684411)
                    ·
                      rfl

theorem cell22_706338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 3, 2, 5].length) (baseStart_706338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_706338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_706338 prefixEnd_706338 := by exact prefixLift 706338
  have htrace : WordTrace (prefixWord ++ tailWord_706338) baseStart_706338 baseEnd_706338 := by
    simpa [prefixWord, tailWord_706338, baseEnd_706338] using wordTrace_append hprefix tailTrace_706338
  have hstable : (prefixWord ++ tailWord_706338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706338).length < 2 ^ (prefixWord ++ tailWord_706338).sum := by decide
  have hdescent : baseEnd_706338 < baseStart_706338 := by decide
  rcases family_descends (prefixWord ++ tailWord_706338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706361 : List Nat := [1, 2, 1, 7, 1, 2, 1, 3, 1, 3]
def baseStart_706361 : Nat := 118140960795 + 706361 * 2 ^ 59
def prefixEnd_706361 : Nat := 4983230072969 + 3 ^ 40 * 706361 * 2
def baseEnd_706361 : Nat := 241801805727077395359341

theorem tailTrace_706361 : CollatzResearch.WordTrace tailWord_706361 prefixEnd_706361 241801805727077395359341 := by
  unfold tailWord_706361
  simp only [CollatzResearch.WordTrace]
  refine ⟨25763102193982208699518937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17175401462654805799679291 25763102193982208699518937)
  ·
    refine ⟨19322326645486656524639203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25763102193982208699518937 19322326645486656524639203)
    ·
      refine ⟨28983489968229984786958805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19322326645486656524639203 28983489968229984786958805)
      ·
        refine ⟨679300546130390268444347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 28983489968229984786958805 679300546130390268444347)
        ·
          refine ⟨1018950819195585402666521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 679300546130390268444347 1018950819195585402666521)
          ·
            refine ⟨764213114396689051999891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1018950819195585402666521 764213114396689051999891)
            ·
              refine ⟨1146319671595033577999837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 764213114396689051999891 1146319671595033577999837)
              ·
                refine ⟨429869876848137591749939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1146319671595033577999837 429869876848137591749939)
                ·
                  refine ⟨644804815272206387624909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 429869876848137591749939 644804815272206387624909)
                  ·
                    refine ⟨241801805727077395359341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 644804815272206387624909 241801805727077395359341)
                    ·
                      rfl

theorem cell22_706361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 1, 3, 1, 3].length) (baseStart_706361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_706361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_706361 prefixEnd_706361 := by exact prefixLift 706361
  have htrace : WordTrace (prefixWord ++ tailWord_706361) baseStart_706361 baseEnd_706361 := by
    simpa [prefixWord, tailWord_706361, baseEnd_706361] using wordTrace_append hprefix tailTrace_706361
  have hstable : (prefixWord ++ tailWord_706361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706361).length < 2 ^ (prefixWord ++ tailWord_706361).sum := by decide
  have hdescent : baseEnd_706361 < baseStart_706361 := by decide
  rcases family_descends (prefixWord ++ tailWord_706361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706385 : List Nat := [1, 2, 2, 1, 5, 3, 1, 1, 6]
def baseStart_706385 : Nat := 118140960795 + 706385 * 2 ^ 59
def prefixEnd_706385 : Nat := 4983230072969 + 3 ^ 40 * 706385 * 2
def baseEnd_706385 : Nat := 80603340472516444253089

theorem tailTrace_706385 : CollatzResearch.WordTrace tailWord_706385 prefixEnd_706385 80603340472516444253089 := by
  unfold tailWord_706385
  simp only [CollatzResearch.WordTrace]
  refine ⟨25763977545895260798392609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17175985030596840532261739 25763977545895260798392609)
  ·
    refine ⟨19322983159421445598794457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25763977545895260798392609 19322983159421445598794457)
    ·
      refine ⟨14492237369566084199095843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19322983159421445598794457 14492237369566084199095843)
      ·
        refine ⟨21738356054349126298643765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14492237369566084199095843 21738356054349126298643765)
        ·
          refine ⟨2037970880095230590497853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21738356054349126298643765 2037970880095230590497853)
          ·
            refine ⟨764239080035711471436695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2037970880095230590497853 764239080035711471436695)
            ·
              refine ⟨1146358620053567207155043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 764239080035711471436695 1146358620053567207155043)
              ·
                refine ⟨1719537930080350810732565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1146358620053567207155043 1719537930080350810732565)
                ·
                  refine ⟨80603340472516444253089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1719537930080350810732565 80603340472516444253089)
                  ·
                    rfl

theorem cell22_706385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 1, 1, 6].length) (baseStart_706385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_706385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_706385 prefixEnd_706385 := by exact prefixLift 706385
  have htrace : WordTrace (prefixWord ++ tailWord_706385) baseStart_706385 baseEnd_706385 := by
    simpa [prefixWord, tailWord_706385, baseEnd_706385] using wordTrace_append hprefix tailTrace_706385
  have hstable : (prefixWord ++ tailWord_706385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706385).length < 2 ^ (prefixWord ++ tailWord_706385).sum := by decide
  have hdescent : baseEnd_706385 < baseStart_706385 := by decide
  rcases family_descends (prefixWord ++ tailWord_706385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706404 : List Nat := [2, 3, 1, 1, 6, 1, 1, 2, 1, 4]
def baseStart_706404 : Nat := 118140960795 + 706404 * 2 ^ 59
def prefixEnd_706404 : Nat := 4983230072969 + 3 ^ 40 * 706404 * 2
def baseEnd_706404 : Nat := 241816525505839616534209

theorem tailTrace_706404 : CollatzResearch.WordTrace tailWord_706404 prefixEnd_706404 241816525505839616534209 := by
  unfold tailWord_706404
  simp only [CollatzResearch.WordTrace]
  refine ⟨12882335266413213521667133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17176447021884284695556177 12882335266413213521667133)
  ·
    refine ⟨4830875724904955070625175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12882335266413213521667133 4830875724904955070625175)
    ·
      refine ⟨7246313587357432605937763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4830875724904955070625175 7246313587357432605937763)
      ·
        refine ⟨10869470381036148908906645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7246313587357432605937763 10869470381036148908906645)
        ·
          refine ⟨509506424111069480104999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 10869470381036148908906645 509506424111069480104999)
          ·
            refine ⟨764259636166604220157499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 509506424111069480104999 764259636166604220157499)
            ·
              refine ⟨1146389454249906330236249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 764259636166604220157499 1146389454249906330236249)
              ·
                refine ⟨859792090687429747677187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1146389454249906330236249 859792090687429747677187)
                ·
                  refine ⟨1289688136031144621515781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 859792090687429747677187 1289688136031144621515781)
                  ·
                    refine ⟨241816525505839616534209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1289688136031144621515781 241816525505839616534209)
                    ·
                      rfl

theorem cell22_706404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 1, 2, 1, 4].length) (baseStart_706404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_706404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_706404 prefixEnd_706404 := by exact prefixLift 706404
  have htrace : WordTrace (prefixWord ++ tailWord_706404) baseStart_706404 baseEnd_706404 := by
    simpa [prefixWord, tailWord_706404, baseEnd_706404] using wordTrace_append hprefix tailTrace_706404
  have hstable : (prefixWord ++ tailWord_706404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706404).length < 2 ^ (prefixWord ++ tailWord_706404).sum := by decide
  have hdescent : baseEnd_706404 < baseStart_706404 := by decide
  rcases family_descends (prefixWord ++ tailWord_706404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706413 : List Nat := [1, 5, 1, 1, 1, 1, 4, 8]
def baseStart_706413 : Nat := 118140960795 + 706413 * 2 ^ 59
def prefixEnd_706413 : Nat := 4983230072969 + 3 ^ 40 * 706413 * 2
def baseEnd_706413 : Nat := 26868845154418510339909

theorem tailTrace_706413 : CollatzResearch.WordTrace tailWord_706413 prefixEnd_706413 26868845154418510339909 := by
  unfold tailWord_706413
  simp only [CollatzResearch.WordTrace]
  refine ⟨25764998789793821580411893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17176665859862547720274595 25764998789793821580411893)
  ·
    refine ⟨2415468636543170773163615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25764998789793821580411893 2415468636543170773163615)
    ·
      refine ⟨3623202954814756159745423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2415468636543170773163615 3623202954814756159745423)
      ·
        refine ⟨5434804432222134239618135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3623202954814756159745423 5434804432222134239618135)
        ·
          refine ⟨8152206648333201359427203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5434804432222134239618135 8152206648333201359427203)
          ·
            refine ⟨12228309972499802039140805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8152206648333201359427203 12228309972499802039140805)
            ·
              refine ⟨2292808119843712882338901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12228309972499802039140805 2292808119843712882338901)
              ·
                refine ⟨26868845154418510339909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2292808119843712882338901 26868845154418510339909)
                ·
                  rfl

theorem cell22_706413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 8].length) (baseStart_706413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_706413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_706413 prefixEnd_706413 := by exact prefixLift 706413
  have htrace : WordTrace (prefixWord ++ tailWord_706413) baseStart_706413 baseEnd_706413 := by
    simpa [prefixWord, tailWord_706413, baseEnd_706413] using wordTrace_append hprefix tailTrace_706413
  have hstable : (prefixWord ++ tailWord_706413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706413).length < 2 ^ (prefixWord ++ tailWord_706413).sum := by decide
  have hdescent : baseEnd_706413 < baseStart_706413 := by decide
  rcases family_descends (prefixWord ++ tailWord_706413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706430 : List Nat := [4, 2, 3, 1, 1, 11]
def baseStart_706430 : Nat := 118140960795 + 706430 * 2 ^ 59
def prefixEnd_706430 : Nat := 4983230072969 + 3 ^ 40 * 706430 * 2
def baseEnd_706430 : Nat := 2985499084409681671409

theorem tailTrace_706430 : CollatzResearch.WordTrace tailWord_706430 prefixEnd_706430 2985499084409681671409 := by
  unfold tailWord_706430
  simp only [CollatzResearch.WordTrace]
  refine ⟨3220702353841529185472593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17177079220488155655853829 3220702353841529185472593)
  ·
    refine ⟨2415526765381146889104445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3220702353841529185472593 2415526765381146889104445)
    ·
      refine ⟨905822537017930083414167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2415526765381146889104445 905822537017930083414167)
      ·
        refine ⟨1358733805526895125121251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 905822537017930083414167 1358733805526895125121251)
        ·
          refine ⟨2038100708290342687681877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1358733805526895125121251 2038100708290342687681877)
          ·
            refine ⟨2985499084409681671409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 2038100708290342687681877 2985499084409681671409)
            ·
              rfl

theorem cell22_706430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 11].length) (baseStart_706430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_706430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_706430 prefixEnd_706430 := by exact prefixLift 706430
  have htrace : WordTrace (prefixWord ++ tailWord_706430) baseStart_706430 baseEnd_706430 := by
    simpa [prefixWord, tailWord_706430, baseEnd_706430] using wordTrace_append hprefix tailTrace_706430
  have hstable : (prefixWord ++ tailWord_706430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706430).length < 2 ^ (prefixWord ++ tailWord_706430).sum := by decide
  have hdescent : baseEnd_706430 < baseStart_706430 := by decide
  rcases family_descends (prefixWord ++ tailWord_706430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706492 : List Nat := [2, 2, 2, 5, 1, 1, 1, 1, 7]
def baseStart_706492 : Nat := 118140960795 + 706492 * 2 ^ 59
def prefixEnd_706492 : Nat := 4983230072969 + 3 ^ 40 * 706492 * 2
def baseEnd_706492 : Nat := 80615549901412240111313

theorem tailTrace_706492 : CollatzResearch.WordTrace tailWord_706492 prefixEnd_706492 80615549901412240111313 := by
  unfold tailWord_706492
  simp only [CollatzResearch.WordTrace]
  refine ⟨12883940078253809036268865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17178586771005078715025153 12883940078253809036268865)
  ·
    refine ⟨9662955058690356777201649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12883940078253809036268865 9662955058690356777201649)
    ·
      refine ⟨7247216294017767582901237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9662955058690356777201649 7247216294017767582901237)
      ·
        refine ⟨679426527564165710896991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7247216294017767582901237 679426527564165710896991)
        ·
          refine ⟨1019139791346248566345487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 679426527564165710896991 1019139791346248566345487)
          ·
            refine ⟨1528709687019372849518231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1019139791346248566345487 1528709687019372849518231)
            ·
              refine ⟨2293064530529059274277347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1528709687019372849518231 2293064530529059274277347)
              ·
                refine ⟨3439596795793588911416021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2293064530529059274277347 3439596795793588911416021)
                ·
                  refine ⟨80615549901412240111313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3439596795793588911416021 80615549901412240111313)
                  ·
                    rfl

theorem cell22_706492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 1, 7].length) (baseStart_706492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_706492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_706492 prefixEnd_706492 := by exact prefixLift 706492
  have htrace : WordTrace (prefixWord ++ tailWord_706492) baseStart_706492 baseEnd_706492 := by
    simpa [prefixWord, tailWord_706492, baseEnd_706492] using wordTrace_append hprefix tailTrace_706492
  have hstable : (prefixWord ++ tailWord_706492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706492).length < 2 ^ (prefixWord ++ tailWord_706492).sum := by decide
  have hdescent : baseEnd_706492 < baseStart_706492 := by decide
  rcases family_descends (prefixWord ++ tailWord_706492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706530 : List Nat := [3, 3, 3, 1, 3, 1, 1, 3, 1, 3]
def baseStart_706530 : Nat := 118140960795 + 706530 * 2 ^ 59
def prefixEnd_706530 : Nat := 4983230072969 + 3 ^ 40 * 706530 * 2
def baseEnd_706530 : Nat := 241859657880817287883823

theorem tailTrace_706530 : CollatzResearch.WordTrace tailWord_706530 prefixEnd_706530 241859657880817287883823 := by
  unfold tailWord_706530
  simp only [CollatzResearch.WordTrace]
  refine ⟨6442316532592487640605261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17179510753579967041614029 6442316532592487640605261)
  ·
    refine ⟨2415868699722182865226973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6442316532592487640605261 2415868699722182865226973)
    ·
      refine ⟨905950762395818574460115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2415868699722182865226973 905950762395818574460115)
      ·
        refine ⟨1358926143593727861690173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 905950762395818574460115 1358926143593727861690173)
        ·
          refine ⟨509597303847647948133815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1358926143593727861690173 509597303847647948133815)
          ·
            refine ⟨764395955771471922200723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 509597303847647948133815 764395955771471922200723)
            ·
              refine ⟨1146593933657207883301085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 764395955771471922200723 1146593933657207883301085)
              ·
                refine ⟨429972725121452956237907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1146593933657207883301085 429972725121452956237907)
                ·
                  refine ⟨644959087682179434356861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 429972725121452956237907 644959087682179434356861)
                  ·
                    refine ⟨241859657880817287883823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 644959087682179434356861 241859657880817287883823)
                    ·
                      rfl

theorem cell22_706530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_706530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_706530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_706530 prefixEnd_706530 := by exact prefixLift 706530
  have htrace : WordTrace (prefixWord ++ tailWord_706530) baseStart_706530 baseEnd_706530 := by
    simpa [prefixWord, tailWord_706530, baseEnd_706530] using wordTrace_append hprefix tailTrace_706530
  have hstable : (prefixWord ++ tailWord_706530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706530).length < 2 ^ (prefixWord ++ tailWord_706530).sum := by decide
  have hdescent : baseEnd_706530 < baseStart_706530 := by decide
  rcases family_descends (prefixWord ++ tailWord_706530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706565 : List Nat := [1, 3, 1, 1, 2, 5, 2, 7]
def baseStart_706565 : Nat := 118140960795 + 706565 * 2 ^ 59
def prefixEnd_706565 : Nat := 4983230072969 + 3 ^ 40 * 706565 * 2
def baseEnd_706565 : Nat := 26874626566232095917635

theorem tailTrace_706565 : CollatzResearch.WordTrace tailWord_706565 prefixEnd_706565 26874626566232095917635 := by
  unfold tailWord_706565
  simp only [CollatzResearch.WordTrace]
  refine ⟨25770542685243151539945149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17180361790162101026630099 25770542685243151539945149)
  ·
    refine ⟨9663953506966181827479431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25770542685243151539945149 9663953506966181827479431)
    ·
      refine ⟨14495930260449272741219147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9663953506966181827479431 14495930260449272741219147)
      ·
        refine ⟨21743895390673909111828721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14495930260449272741219147 21743895390673909111828721)
        ·
          refine ⟨16307921543005431833871541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21743895390673909111828721 16307921543005431833871541)
          ·
            refine ⟨1528867644656759234425457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16307921543005431833871541 1528867644656759234425457)
            ·
              refine ⟨1146650733492569425819093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1528867644656759234425457 1146650733492569425819093)
              ·
                refine ⟨26874626566232095917635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1146650733492569425819093 26874626566232095917635)
                ·
                  rfl

theorem cell22_706565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 2, 7].length) (baseStart_706565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_706565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_706565 prefixEnd_706565 := by exact prefixLift 706565
  have htrace : WordTrace (prefixWord ++ tailWord_706565) baseStart_706565 baseEnd_706565 := by
    simpa [prefixWord, tailWord_706565, baseEnd_706565] using wordTrace_append hprefix tailTrace_706565
  have hstable : (prefixWord ++ tailWord_706565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706565).length < 2 ^ (prefixWord ++ tailWord_706565).sum := by decide
  have hdescent : baseEnd_706565 < baseStart_706565 := by decide
  rcases family_descends (prefixWord ++ tailWord_706565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706614 : List Nat := [5, 1, 2, 1, 1, 1, 2, 3, 3, 3]
def baseStart_706614 : Nat := 118140960795 + 706614 * 2 ^ 59
def prefixEnd_706614 : Nat := 4983230072969 + 3 ^ 40 * 706614 * 2
def baseEnd_706614 : Nat := 241888412797469068783565

theorem tailTrace_706614 : CollatzResearch.WordTrace tailWord_706614 prefixEnd_706614 241888412797469068783565 := by
  unfold tailWord_706614
  simp only [CollatzResearch.WordTrace]
  refine ⟨1610770616379102056779931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17181553241377088605652597 1610770616379102056779931)
  ·
    refine ⟨2416155924568653085169897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1610770616379102056779931 2416155924568653085169897)
    ·
      refine ⟨1812116943426489813877423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2416155924568653085169897 1812116943426489813877423)
      ·
        refine ⟨2718175415139734720816135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1812116943426489813877423 2718175415139734720816135)
        ·
          refine ⟨4077263122709602081224203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2718175415139734720816135 4077263122709602081224203)
          ·
            refine ⟨6115894684064403121836305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4077263122709602081224203 6115894684064403121836305)
            ·
              refine ⟨4586921013048302341377229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6115894684064403121836305 4586921013048302341377229)
              ·
                refine ⟨1720095379893113378016461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4586921013048302341377229 1720095379893113378016461)
                ·
                  refine ⟨645035767459917516756173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1720095379893113378016461 645035767459917516756173)
                  ·
                    refine ⟨241888412797469068783565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 645035767459917516756173 241888412797469068783565)
                    ·
                      rfl

theorem cell22_706614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 3, 3, 3].length) (baseStart_706614 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_706614 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_706614 prefixEnd_706614 := by exact prefixLift 706614
  have htrace : WordTrace (prefixWord ++ tailWord_706614) baseStart_706614 baseEnd_706614 := by
    simpa [prefixWord, tailWord_706614, baseEnd_706614] using wordTrace_append hprefix tailTrace_706614
  have hstable : (prefixWord ++ tailWord_706614).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706614).length < 2 ^ (prefixWord ++ tailWord_706614).sum := by decide
  have hdescent : baseEnd_706614 < baseStart_706614 := by decide
  rcases family_descends (prefixWord ++ tailWord_706614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706672 : List Nat := [2, 1, 1, 1, 5, 3, 2, 1, 6]
def baseStart_706672 : Nat := 118140960795 + 706672 * 2 ^ 59
def prefixEnd_706672 : Nat := 4983230072969 + 3 ^ 40 * 706672 * 2
def baseEnd_706672 : Nat := 80636089127592083611129

theorem tailTrace_706672 : CollatzResearch.WordTrace tailWord_706672 prefixEnd_706672 80636089127592083611129 := by
  unfold tailWord_706672
  simp only [CollatzResearch.WordTrace]
  refine ⟨12887222647927754407045135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17182963530570339209393513 12887222647927754407045135)
  ·
    refine ⟨19330833971891631610567703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12887222647927754407045135 19330833971891631610567703)
    ·
      refine ⟨28996250957837447415851555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19330833971891631610567703 28996250957837447415851555)
      ·
        refine ⟨43494376436756171123777333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28996250957837447415851555 43494376436756171123777333)
        ·
          refine ⟨4077597790945891042854125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 43494376436756171123777333 4077597790945891042854125)
          ·
            refine ⟨1529099171604709141070297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4077597790945891042854125 1529099171604709141070297)
            ·
              refine ⟨1146824378703531855802723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1529099171604709141070297 1146824378703531855802723)
              ·
                refine ⟨1720236568055297783704085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1146824378703531855802723 1720236568055297783704085)
                ·
                  refine ⟨80636089127592083611129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1720236568055297783704085 80636089127592083611129)
                  ·
                    rfl

theorem cell22_706672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 2, 1, 6].length) (baseStart_706672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_706672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_706672 prefixEnd_706672 := by exact prefixLift 706672
  have htrace : WordTrace (prefixWord ++ tailWord_706672) baseStart_706672 baseEnd_706672 := by
    simpa [prefixWord, tailWord_706672, baseEnd_706672] using wordTrace_append hprefix tailTrace_706672
  have hstable : (prefixWord ++ tailWord_706672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706672).length < 2 ^ (prefixWord ++ tailWord_706672).sum := by decide
  have hdescent : baseEnd_706672 < baseStart_706672 := by decide
  rcases family_descends (prefixWord ++ tailWord_706672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706717 : List Nat := [1, 4, 2, 1, 1, 5, 8]
def baseStart_706717 : Nat := 118140960795 + 706717 * 2 ^ 59
def prefixEnd_706717 : Nat := 4983230072969 + 3 ^ 40 * 706717 * 2
def baseEnd_706717 : Nat := 8960135992681893831787

theorem tailTrace_706717 : CollatzResearch.WordTrace tailWord_706717 prefixEnd_706717 8960135992681893831787 := by
  unfold tailWord_706717
  simp only [CollatzResearch.WordTrace]
  refine ⟨25776086580692481499478405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17184057720461654332985603 25776086580692481499478405)
  ·
    refine ⟨4833016233879840281152201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25776086580692481499478405 4833016233879840281152201)
    ·
      refine ⟨3624762175409880210864151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4833016233879840281152201 3624762175409880210864151)
      ·
        refine ⟨5437143263114820316296227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3624762175409880210864151 5437143263114820316296227)
        ·
          refine ⟨8155714894672230474444341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5437143263114820316296227 8155714894672230474444341)
          ·
            refine ⟨764598271375521606979157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8155714894672230474444341 764598271375521606979157)
            ·
              refine ⟨8960135992681893831787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 764598271375521606979157 8960135992681893831787)
              ·
                rfl

theorem cell22_706717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 8].length) (baseStart_706717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_706717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_706717 prefixEnd_706717 := by exact prefixLift 706717
  have htrace : WordTrace (prefixWord ++ tailWord_706717) baseStart_706717 baseEnd_706717 := by
    simpa [prefixWord, tailWord_706717, baseEnd_706717] using wordTrace_append hprefix tailTrace_706717
  have hstable : (prefixWord ++ tailWord_706717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706717).length < 2 ^ (prefixWord ++ tailWord_706717).sum := by decide
  have hdescent : baseEnd_706717 < baseStart_706717 := by decide
  rcases family_descends (prefixWord ++ tailWord_706717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706719 : List Nat := [1, 1, 2, 6, 1, 2, 1, 2, 2, 4]
def baseStart_706719 : Nat := 118140960795 + 706719 * 2 ^ 59
def prefixEnd_706719 : Nat := 4983230072969 + 3 ^ 40 * 706719 * 2
def baseEnd_706719 : Nat := 241924356443283794908243

theorem tailTrace_706719 : CollatzResearch.WordTrace tailWord_706719 prefixEnd_706719 241924356443283794908243 := by
  unfold tailWord_706719
  simp only [CollatzResearch.WordTrace]
  refine ⟨25776159526685235841051211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17184106351123490560700807 25776159526685235841051211)
  ·
    refine ⟨38664239290027853761576817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25776159526685235841051211 38664239290027853761576817)
    ·
      refine ⟨28998179467520890321182613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38664239290027853761576817 28998179467520890321182613)
      ·
        refine ⟨1359289662540041733805435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 28998179467520890321182613 1359289662540041733805435)
        ·
          refine ⟨2038934493810062600708153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1359289662540041733805435 2038934493810062600708153)
          ·
            refine ⟨1529200870357546950531115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2038934493810062600708153 1529200870357546950531115)
            ·
              refine ⟨2293801305536320425796673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1529200870357546950531115 2293801305536320425796673)
              ·
                refine ⟨1720350979152240319347505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2293801305536320425796673 1720350979152240319347505)
                ·
                  refine ⟨1290263234364180239510629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1720350979152240319347505 1290263234364180239510629)
                  ·
                    refine ⟨241924356443283794908243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1290263234364180239510629 241924356443283794908243)
                    ·
                      rfl

theorem cell22_706719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 2, 2, 4].length) (baseStart_706719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_706719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_706719 prefixEnd_706719 := by exact prefixLift 706719
  have htrace : WordTrace (prefixWord ++ tailWord_706719) baseStart_706719 baseEnd_706719 := by
    simpa [prefixWord, tailWord_706719, baseEnd_706719] using wordTrace_append hprefix tailTrace_706719
  have hstable : (prefixWord ++ tailWord_706719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706719).length < 2 ^ (prefixWord ++ tailWord_706719).sum := by decide
  have hdescent : baseEnd_706719 < baseStart_706719 := by decide
  rcases family_descends (prefixWord ++ tailWord_706719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706826 : List Nat := [3, 1, 2, 2, 1, 1, 6, 1, 1, 4]
def baseStart_706826 : Nat := 118140960795 + 706826 * 2 ^ 59
def prefixEnd_706826 : Nat := 4983230072969 + 3 ^ 40 * 706826 * 2
def baseEnd_706826 : Nat := 241960984729971182482915

theorem tailTrace_706826 : CollatzResearch.WordTrace tailWord_706826 prefixEnd_706826 241960984729971182482915 := by
  unfold tailWord_706826
  simp only [CollatzResearch.WordTrace]
  refine ⟨6445015534324398278799083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17186708091531728743464221 6445015534324398278799083)
  ·
    refine ⟨9667523301486597418198625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6445015534324398278799083 9667523301486597418198625)
    ·
      refine ⟨7250642476114948063648969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9667523301486597418198625 7250642476114948063648969)
      ·
        refine ⟨5437981857086211047736727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7250642476114948063648969 5437981857086211047736727)
        ·
          refine ⟨8156972785629316571605091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5437981857086211047736727 8156972785629316571605091)
          ·
            refine ⟨12235459178443974857407637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8156972785629316571605091 12235459178443974857407637)
            ·
              refine ⟨573537148989561321440983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 12235459178443974857407637 573537148989561321440983)
              ·
                refine ⟨860305723484341982161475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 573537148989561321440983 860305723484341982161475)
                ·
                  refine ⟨1290458585226512973242213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 860305723484341982161475 1290458585226512973242213)
                  ·
                    refine ⟨241960984729971182482915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1290458585226512973242213 241960984729971182482915)
                    ·
                      rfl

theorem cell22_706826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 6, 1, 1, 4].length) (baseStart_706826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_706826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_706826 prefixEnd_706826 := by exact prefixLift 706826
  have htrace : WordTrace (prefixWord ++ tailWord_706826) baseStart_706826 baseEnd_706826 := by
    simpa [prefixWord, tailWord_706826, baseEnd_706826] using wordTrace_append hprefix tailTrace_706826
  have hstable : (prefixWord ++ tailWord_706826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706826).length < 2 ^ (prefixWord ++ tailWord_706826).sum := by decide
  have hdescent : baseEnd_706826 < baseStart_706826 := by decide
  rcases family_descends (prefixWord ++ tailWord_706826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706867 : List Nat := [1, 1, 1, 2, 5, 1, 1, 1, 2, 7]
def baseStart_706867 : Nat := 118140960795 + 706867 * 2 ^ 59
def prefixEnd_706867 : Nat := 4983230072969 + 3 ^ 40 * 706867 * 2
def baseEnd_706867 : Nat := 241975019867860742207789

theorem tailTrace_706867 : CollatzResearch.WordTrace tailWord_706867 prefixEnd_706867 241975019867860742207789 := by
  unfold tailWord_706867
  simp only [CollatzResearch.WordTrace]
  refine ⟨25781557530149057117438855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17187705020099371411625903 25781557530149057117438855)
  ·
    refine ⟨38672336295223585676158283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25781557530149057117438855 38672336295223585676158283)
    ·
      refine ⟨58008504442835378514237425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38672336295223585676158283 58008504442835378514237425)
      ·
        refine ⟨43506378332126533885678069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58008504442835378514237425 43506378332126533885678069)
        ·
          refine ⟨4078722968636862551782319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 43506378332126533885678069 4078722968636862551782319)
          ·
            refine ⟨6118084452955293827673479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4078722968636862551782319 6118084452955293827673479)
            ·
              refine ⟨9177126679432940741510219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6118084452955293827673479 9177126679432940741510219)
              ·
                refine ⟨13765690019149411112265329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9177126679432940741510219 13765690019149411112265329)
                ·
                  refine ⟨10324267514362058334198997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13765690019149411112265329 10324267514362058334198997)
                  ·
                    refine ⟨241975019867860742207789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10324267514362058334198997 241975019867860742207789)
                    ·
                      rfl

theorem cell22_706867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 2, 7].length) (baseStart_706867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_706867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_706867 prefixEnd_706867 := by exact prefixLift 706867
  have htrace : WordTrace (prefixWord ++ tailWord_706867) baseStart_706867 baseEnd_706867 := by
    simpa [prefixWord, tailWord_706867, baseEnd_706867] using wordTrace_append hprefix tailTrace_706867
  have hstable : (prefixWord ++ tailWord_706867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706867).length < 2 ^ (prefixWord ++ tailWord_706867).sum := by decide
  have hdescent : baseEnd_706867 < baseStart_706867 := by decide
  rcases family_descends (prefixWord ++ tailWord_706867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706993 : List Nat := [1, 2, 2, 4, 1, 3, 2, 3, 4]
def baseStart_706993 : Nat := 118140960795 + 706993 * 2 ^ 59
def prefixEnd_706993 : Nat := 4983230072969 + 3 ^ 40 * 706993 * 2
def baseEnd_706993 : Nat := 80672717414279471185801

theorem tailTrace_706993 : CollatzResearch.WordTrace tailWord_706993 prefixEnd_706993 80672717414279471185801 := by
  unfold tailWord_706993
  simp only [CollatzResearch.WordTrace]
  refine ⟨25786153127692580636525633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17190768751795053757683755 25786153127692580636525633)
  ·
    refine ⟨19339614845769435477394225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25786153127692580636525633 19339614845769435477394225)
    ·
      refine ⟨14504711134327076608045669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19339614845769435477394225 14504711134327076608045669)
      ·
        refine ⟨2719633337686326864008563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14504711134327076608045669 2719633337686326864008563)
        ·
          refine ⟨4079450006529490296012845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2719633337686326864008563 4079450006529490296012845)
          ·
            refine ⟨1529793752448558861004817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4079450006529490296012845 1529793752448558861004817)
            ·
              refine ⟨1147345314336419145753613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1529793752448558861004817 1147345314336419145753613)
              ·
                refine ⟨430254492876157179657605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1147345314336419145753613 430254492876157179657605)
                ·
                  refine ⟨80672717414279471185801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 430254492876157179657605 80672717414279471185801)
                  ·
                    rfl

theorem cell22_706993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 2, 3, 4].length) (baseStart_706993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_706993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_706993 prefixEnd_706993 := by exact prefixLift 706993
  have htrace : WordTrace (prefixWord ++ tailWord_706993) baseStart_706993 baseEnd_706993 := by
    simpa [prefixWord, tailWord_706993, baseEnd_706993] using wordTrace_append hprefix tailTrace_706993
  have hstable : (prefixWord ++ tailWord_706993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706993).length < 2 ^ (prefixWord ++ tailWord_706993).sum := by decide
  have hdescent : baseEnd_706993 < baseStart_706993 := by decide
  rcases family_descends (prefixWord ++ tailWord_706993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707006 : List Nat := [4, 2, 1, 1, 1, 1, 2, 4, 2, 4]
def baseStart_707006 : Nat := 118140960795 + 707006 * 2 ^ 59
def prefixEnd_707006 : Nat := 4983230072969 + 3 ^ 40 * 707006 * 2
def baseEnd_707006 : Nat := 242022602408510712982363

theorem tailTrace_707006 : CollatzResearch.WordTrace tailWord_707006 prefixEnd_707006 242022602408510712982363 := by
  unfold tailWord_707006
  simp only [CollatzResearch.WordTrace]
  refine ⟨3223328409580685482093609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17191084851096989237832581 3223328409580685482093609)
  ·
    refine ⟨2417496307185514111570207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3223328409580685482093609 2417496307185514111570207)
    ·
      refine ⟨3626244460778271167355311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2417496307185514111570207 3626244460778271167355311)
      ·
        refine ⟨5439366691167406751032967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3626244460778271167355311 5439366691167406751032967)
        ·
          refine ⟨8159050036751110126549451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5439366691167406751032967 8159050036751110126549451)
          ·
            refine ⟨12238575055126665189824177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8159050036751110126549451 12238575055126665189824177)
            ·
              refine ⟨9178931291344998892368133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12238575055126665189824177 9178931291344998892368133)
              ·
                refine ⟨1721049617127187292319025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9178931291344998892368133 1721049617127187292319025)
                ·
                  refine ⟨1290787212845390469239269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1721049617127187292319025 1290787212845390469239269)
                  ·
                    refine ⟨242022602408510712982363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1290787212845390469239269 242022602408510712982363)
                    ·
                      rfl

theorem cell22_707006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 4, 2, 4].length) (baseStart_707006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_707006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_707006 prefixEnd_707006 := by exact prefixLift 707006
  have htrace : WordTrace (prefixWord ++ tailWord_707006) baseStart_707006 baseEnd_707006 := by
    simpa [prefixWord, tailWord_707006, baseEnd_707006] using wordTrace_append hprefix tailTrace_707006
  have hstable : (prefixWord ++ tailWord_707006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707006).length < 2 ^ (prefixWord ++ tailWord_707006).sum := by decide
  have hdescent : baseEnd_707006 < baseStart_707006 := by decide
  rcases family_descends (prefixWord ++ tailWord_707006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707083 : List Nat := [1, 1, 1, 1, 7, 1, 4, 1, 5]
def baseStart_707083 : Nat := 118140960795 + 707083 * 2 ^ 59
def prefixEnd_707083 : Nat := 4983230072969 + 3 ^ 40 * 707083 * 2
def baseEnd_707083 : Nat := 80682987027369392935709

theorem tailTrace_707083 : CollatzResearch.WordTrace tailWord_707083 prefixEnd_707083 80682987027369392935709 := by
  unfold tailWord_707083
  simp only [CollatzResearch.WordTrace]
  refine ⟨25789435697366526007301903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17192957131577684004867935 25789435697366526007301903)
  ·
    refine ⟨38684153546049789010952855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25789435697366526007301903 38684153546049789010952855)
    ·
      refine ⟨58026230319074683516429283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38684153546049789010952855 58026230319074683516429283)
      ·
        refine ⟨87039345478612025274643925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58026230319074683516429283 87039345478612025274643925)
        ·
          refine ⟨2039984659654969342374467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 87039345478612025274643925 2039984659654969342374467)
          ·
            refine ⟨3059976989482454013561701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2039984659654969342374467 3059976989482454013561701)
            ·
              refine ⟨573745685527960127542819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3059976989482454013561701 573745685527960127542819)
              ·
                refine ⟨860618528291940191314229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 573745685527960127542819 860618528291940191314229)
                ·
                  refine ⟨80682987027369392935709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 860618528291940191314229 80682987027369392935709)
                  ·
                    rfl

theorem cell22_707083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 4, 1, 5].length) (baseStart_707083 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_707083 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_707083 prefixEnd_707083 := by exact prefixLift 707083
  have htrace : WordTrace (prefixWord ++ tailWord_707083) baseStart_707083 baseEnd_707083 := by
    simpa [prefixWord, tailWord_707083, baseEnd_707083] using wordTrace_append hprefix tailTrace_707083
  have hstable : (prefixWord ++ tailWord_707083).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707083).length < 2 ^ (prefixWord ++ tailWord_707083).sum := by decide
  have hdescent : baseEnd_707083 < baseStart_707083 := by decide
  rcases family_descends (prefixWord ++ tailWord_707083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707128 : List Nat := [2, 1, 2, 1, 4, 1, 3, 4, 4]
def baseStart_707128 : Nat := 118140960795 + 707128 * 2 ^ 59
def prefixEnd_707128 : Nat := 4983230072969 + 3 ^ 40 * 707128 * 2
def baseEnd_707128 : Nat := 80688121833914353810663

theorem tailTrace_707128 : CollatzResearch.WordTrace tailWord_707128 prefixEnd_707128 80688121833914353810663 := by
  unfold tailWord_707128
  simp only [CollatzResearch.WordTrace]
  refine ⟨12895538491101749346345019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17194051321468999128460025 12895538491101749346345019)
  ·
    refine ⟨19343307736652624019517529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12895538491101749346345019 19343307736652624019517529)
    ·
      refine ⟨14507480802489468014638147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19343307736652624019517529 14507480802489468014638147)
      ·
        refine ⟨21761221203734202021957221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14507480802489468014638147 21761221203734202021957221)
        ·
          refine ⟨4080228975700162879116979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21761221203734202021957221 4080228975700162879116979)
          ·
            refine ⟨6120343463550244318675469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4080228975700162879116979 6120343463550244318675469)
            ·
              refine ⟨2295128798831341619503301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6120343463550244318675469 2295128798831341619503301)
              ·
                refine ⟨430336649780876553656869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2295128798831341619503301 430336649780876553656869)
                ·
                  refine ⟨80688121833914353810663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 430336649780876553656869 80688121833914353810663)
                  ·
                    rfl

theorem cell22_707128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 4, 4].length) (baseStart_707128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_707128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_707128 prefixEnd_707128 := by exact prefixLift 707128
  have htrace : WordTrace (prefixWord ++ tailWord_707128) baseStart_707128 baseEnd_707128 := by
    simpa [prefixWord, tailWord_707128, baseEnd_707128] using wordTrace_append hprefix tailTrace_707128
  have hstable : (prefixWord ++ tailWord_707128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707128).length < 2 ^ (prefixWord ++ tailWord_707128).sum := by decide
  have hdescent : baseEnd_707128 < baseStart_707128 := by decide
  rcases family_descends (prefixWord ++ tailWord_707128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707143 : List Nat := [1, 1, 4, 1, 4, 2, 2, 1, 1, 5]
def baseStart_707143 : Nat := 118140960795 + 707143 * 2 ^ 59
def prefixEnd_707143 : Nat := 4983230072969 + 3 ^ 40 * 707143 * 2
def baseEnd_707143 : Nat := 242069500308288022306943

theorem tailTrace_707143 : CollatzResearch.WordTrace tailWord_707143 prefixEnd_707143 242069500308288022306943 := by
  unfold tailWord_707143
  simp only [CollatzResearch.WordTrace]
  refine ⟨25791624077149156254486083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17194416051432770836324055 25791624077149156254486083)
  ·
    refine ⟨38687436115723734381729125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25791624077149156254486083 38687436115723734381729125)
    ·
      refine ⟨7253894271698200196574211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38687436115723734381729125 7253894271698200196574211)
      ·
        refine ⟨10880841407547300294861317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7253894271698200196574211 10880841407547300294861317)
        ·
          refine ⟨2040157763915118805286497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10880841407547300294861317 2040157763915118805286497)
          ·
            refine ⟨1530118322936339103964873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2040157763915118805286497 1530118322936339103964873)
            ·
              refine ⟨1147588742202254327973655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1530118322936339103964873 1147588742202254327973655)
              ·
                refine ⟨1721383113303381491960483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1147588742202254327973655 1721383113303381491960483)
                ·
                  refine ⟨2582074669955072237940725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1721383113303381491960483 2582074669955072237940725)
                  ·
                    refine ⟨242069500308288022306943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2582074669955072237940725 242069500308288022306943)
                    ·
                      rfl

theorem cell22_707143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 2, 1, 1, 5].length) (baseStart_707143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_707143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_707143 prefixEnd_707143 := by exact prefixLift 707143
  have htrace : WordTrace (prefixWord ++ tailWord_707143) baseStart_707143 baseEnd_707143 := by
    simpa [prefixWord, tailWord_707143, baseEnd_707143] using wordTrace_append hprefix tailTrace_707143
  have hstable : (prefixWord ++ tailWord_707143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707143).length < 2 ^ (prefixWord ++ tailWord_707143).sum := by decide
  have hdescent : baseEnd_707143 < baseStart_707143 := by decide
  rcases family_descends (prefixWord ++ tailWord_707143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707164 : List Nat := [2, 2, 4, 1, 4, 1, 2, 1, 1, 4]
def baseStart_707164 : Nat := 118140960795 + 707164 * 2 ^ 59
def prefixEnd_707164 : Nat := 4983230072969 + 3 ^ 40 * 707164 * 2
def baseEnd_707164 : Nat := 242076689037450967531879

theorem tailTrace_707164 : CollatzResearch.WordTrace tailWord_707164 prefixEnd_707164 242076689037450967531879 := by
  unfold tailWord_707164
  simp only [CollatzResearch.WordTrace]
  refine ⟨12896195005036538420500273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17194926673382051227333697 12896195005036538420500273)
  ·
    refine ⟨9672146253777403815375205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12896195005036538420500273 9672146253777403815375205)
    ·
      refine ⟨1813527422583263215382851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9672146253777403815375205 1813527422583263215382851)
      ·
        refine ⟨2720291133874894823074277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1813527422583263215382851 2720291133874894823074277)
        ·
          refine ⟨510054587601542779326427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2720291133874894823074277 510054587601542779326427)
          ·
            refine ⟨765081881402314168989641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 510054587601542779326427 765081881402314168989641)
            ·
              refine ⟨573811411051735626742231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 765081881402314168989641 573811411051735626742231)
              ·
                refine ⟨860717116577603440113347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 573811411051735626742231 860717116577603440113347)
                ·
                  refine ⟨1291075674866405160170021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 860717116577603440113347 1291075674866405160170021)
                  ·
                    refine ⟨242076689037450967531879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1291075674866405160170021 242076689037450967531879)
                    ·
                      rfl

theorem cell22_707164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 2, 1, 1, 4].length) (baseStart_707164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_707164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_707164 prefixEnd_707164 := by exact prefixLift 707164
  have htrace : WordTrace (prefixWord ++ tailWord_707164) baseStart_707164 baseEnd_707164 := by
    simpa [prefixWord, tailWord_707164, baseEnd_707164] using wordTrace_append hprefix tailTrace_707164
  have hstable : (prefixWord ++ tailWord_707164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707164).length < 2 ^ (prefixWord ++ tailWord_707164).sum := by decide
  have hdescent : baseEnd_707164 < baseStart_707164 := by decide
  rcases family_descends (prefixWord ++ tailWord_707164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707218 : List Nat := [3, 2, 3, 1, 2, 1, 1, 2, 7]
def baseStart_707218 : Nat := 118140960795 + 707218 * 2 ^ 59
def prefixEnd_707218 : Nat := 4983230072969 + 3 ^ 40 * 707218 * 2
def baseEnd_707218 : Nat := 80698391447004275560571

theorem tailTrace_707218 : CollatzResearch.WordTrace tailWord_707218 prefixEnd_707218 80698391447004275560571 := by
  unfold tailWord_707218
  simp only [CollatzResearch.WordTrace]
  refine ⟨6448589887969361015866577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17196239701251629375644205 6448589887969361015866577)
  ·
    refine ⟨4836442415977020761899933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6448589887969361015866577 4836442415977020761899933)
    ·
      refine ⟨1813665905991382785712475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4836442415977020761899933 1813665905991382785712475)
      ·
        refine ⟨2720498858987074178568713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1813665905991382785712475 2720498858987074178568713)
        ·
          refine ⟨2040374144240305633926535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2720498858987074178568713 2040374144240305633926535)
          ·
            refine ⟨3060561216360458450889803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2040374144240305633926535 3060561216360458450889803)
            ·
              refine ⟨4590841824540687676334705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3060561216360458450889803 4590841824540687676334705)
              ·
                refine ⟨3443131368405515757251029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4590841824540687676334705 3443131368405515757251029)
                ·
                  refine ⟨80698391447004275560571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3443131368405515757251029 80698391447004275560571)
                  ·
                    rfl

theorem cell22_707218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 2, 7].length) (baseStart_707218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_707218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_707218 prefixEnd_707218 := by exact prefixLift 707218
  have htrace : WordTrace (prefixWord ++ tailWord_707218) baseStart_707218 baseEnd_707218 := by
    simpa [prefixWord, tailWord_707218, baseEnd_707218] using wordTrace_append hprefix tailTrace_707218
  have hstable : (prefixWord ++ tailWord_707218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707218).length < 2 ^ (prefixWord ++ tailWord_707218).sum := by decide
  have hdescent : baseEnd_707218 < baseStart_707218 := by decide
  rcases family_descends (prefixWord ++ tailWord_707218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707239 : List Nat := [1, 1, 6, 3, 1, 2, 1, 1, 3, 3]
def baseStart_707239 : Nat := 118140960795 + 707239 * 2 ^ 59
def prefixEnd_707239 : Nat := 4983230072969 + 3 ^ 40 * 707239 * 2
def baseEnd_707239 : Nat := 242102363070175771906649

theorem tailTrace_707239 : CollatzResearch.WordTrace tailWord_707239 prefixEnd_707239 242102363070175771906649 := by
  unfold tailWord_707239
  simp only [CollatzResearch.WordTrace]
  refine ⟨25795125484801364649980771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17196750323200909766653847 25795125484801364649980771)
  ·
    refine ⟨38692688227202046974971157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25795125484801364649980771 38692688227202046974971157)
    ·
      refine ⟨1813719760650095951951773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 38692688227202046974971157 1813719760650095951951773)
      ·
        refine ⟨680144910243785981981915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1813719760650095951951773 680144910243785981981915)
        ·
          refine ⟨1020217365365678972972873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 680144910243785981981915 1020217365365678972972873)
          ·
            refine ⟨765163024024259229729655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1020217365365678972972873 765163024024259229729655)
            ·
              refine ⟨1147744536036388844594483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 765163024024259229729655 1147744536036388844594483)
              ·
                refine ⟨1721616804054583266891725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1147744536036388844594483 1721616804054583266891725)
                ·
                  refine ⟨645606301520468725084397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1721616804054583266891725 645606301520468725084397)
                  ·
                    refine ⟨242102363070175771906649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 645606301520468725084397 242102363070175771906649)
                    ·
                      rfl

theorem cell22_707239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 1, 1, 3, 3].length) (baseStart_707239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_707239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_707239 prefixEnd_707239 := by exact prefixLift 707239
  have htrace : WordTrace (prefixWord ++ tailWord_707239) baseStart_707239 baseEnd_707239 := by
    simpa [prefixWord, tailWord_707239, baseEnd_707239] using wordTrace_append hprefix tailTrace_707239
  have hstable : (prefixWord ++ tailWord_707239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707239).length < 2 ^ (prefixWord ++ tailWord_707239).sum := by decide
  have hdescent : baseEnd_707239 < baseStart_707239 := by decide
  rcases family_descends (prefixWord ++ tailWord_707239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707278 : List Nat := [4, 1, 1, 1, 3, 2, 1, 1, 3, 5]
def baseStart_707278 : Nat := 118140960795 + 707278 * 2 ^ 59
def prefixEnd_707278 : Nat := 4983230072969 + 3 ^ 40 * 707278 * 2
def baseEnd_707278 : Nat := 242115713567192670181529

theorem tailTrace_707278 : CollatzResearch.WordTrace tailWord_707278 prefixEnd_707278 242115713567192670181529 := by
  unfold tailWord_707278
  simp only [CollatzResearch.WordTrace]
  refine ⟨3224568491457509288831311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17197698621106716207100325 3224568491457509288831311)
  ·
    refine ⟨4836852737186263933246967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3224568491457509288831311 4836852737186263933246967)
    ·
      refine ⟨7255279105779395899870451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4836852737186263933246967 7255279105779395899870451)
      ·
        refine ⟨10882918658669093849805677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7255279105779395899870451 10882918658669093849805677)
        ·
          refine ⟨4081094497000910193677129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10882918658669093849805677 4081094497000910193677129)
          ·
            refine ⟨3060820872750682645257847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4081094497000910193677129 3060820872750682645257847)
            ·
              refine ⟨4591231309126023967886771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3060820872750682645257847 4591231309126023967886771)
              ·
                refine ⟨6886846963689035951830157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4591231309126023967886771 6886846963689035951830157)
                ·
                  refine ⟨2582567611383388481936309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6886846963689035951830157 2582567611383388481936309)
                  ·
                    refine ⟨242115713567192670181529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2582567611383388481936309 242115713567192670181529)
                    ·
                      rfl

theorem cell22_707278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 1, 3, 5].length) (baseStart_707278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_707278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_707278 prefixEnd_707278 := by exact prefixLift 707278
  have htrace : WordTrace (prefixWord ++ tailWord_707278) baseStart_707278 baseEnd_707278 := by
    simpa [prefixWord, tailWord_707278, baseEnd_707278] using wordTrace_append hprefix tailTrace_707278
  have hstable : (prefixWord ++ tailWord_707278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707278).length < 2 ^ (prefixWord ++ tailWord_707278).sum := by decide
  have hdescent : baseEnd_707278 < baseStart_707278 := by decide
  rcases family_descends (prefixWord ++ tailWord_707278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707295 : List Nat := [1, 1, 2, 3, 2, 3, 1, 4, 2, 3]
def baseStart_707295 : Nat := 118140960795 + 707295 * 2 ^ 59
def prefixEnd_707295 : Nat := 4983230072969 + 3 ^ 40 * 707295 * 2
def baseEnd_707295 : Nat := 242121533014610292506477

theorem tailTrace_707295 : CollatzResearch.WordTrace tailWord_707295 prefixEnd_707295 242121533014610292506477 := by
  unfold tailWord_707295
  simp only [CollatzResearch.WordTrace]
  refine ⟨25797167972598486214019339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17198111981732324142679559 25797167972598486214019339)
  ·
    refine ⟨38695751958897729321029009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25797167972598486214019339 38695751958897729321029009)
    ·
      refine ⟨29021813969173296990771757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38695751958897729321029009 29021813969173296990771757)
      ·
        refine ⟨10883180238439986371539409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29021813969173296990771757 10883180238439986371539409)
        ·
          refine ⟨8162385178829989778654557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10883180238439986371539409 8162385178829989778654557)
          ·
            refine ⟨3060894442061246166995459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8162385178829989778654557 3060894442061246166995459)
            ·
              refine ⟨4591341663091869250493189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3060894442061246166995459 4591341663091869250493189)
              ·
                refine ⟨860876561829725484467473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4591341663091869250493189 860876561829725484467473)
                ·
                  refine ⟨645657421372294113350605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 860876561829725484467473 645657421372294113350605)
                  ·
                    refine ⟨242121533014610292506477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 645657421372294113350605 242121533014610292506477)
                    ·
                      rfl

theorem cell22_707295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 4, 2, 3].length) (baseStart_707295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_707295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_707295 prefixEnd_707295 := by exact prefixLift 707295
  have htrace : WordTrace (prefixWord ++ tailWord_707295) baseStart_707295 baseEnd_707295 := by
    simpa [prefixWord, tailWord_707295, baseEnd_707295] using wordTrace_append hprefix tailTrace_707295
  have hstable : (prefixWord ++ tailWord_707295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707295).length < 2 ^ (prefixWord ++ tailWord_707295).sum := by decide
  have hdescent : baseEnd_707295 < baseStart_707295 := by decide
  rcases family_descends (prefixWord ++ tailWord_707295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707297 : List Nat := [1, 2, 3, 1, 4, 1, 4, 2, 4]
def baseStart_707297 : Nat := 118140960795 + 707297 * 2 ^ 59
def prefixEnd_707297 : Nat := 4983230072969 + 3 ^ 40 * 707297 * 2
def baseEnd_707297 : Nat := 80707405885160984652157

theorem tailTrace_707297 : CollatzResearch.WordTrace tailWord_707297 prefixEnd_707297 80707405885160984652157 := by
  unfold tailWord_707297
  simp only [CollatzResearch.WordTrace]
  refine ⟨25797240918591240555592145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17198160612394160370394763 25797240918591240555592145)
  ·
    refine ⟨19347930688943430416694109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25797240918591240555592145 19347930688943430416694109)
    ·
      refine ⟨7255474008353786406260291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19347930688943430416694109 7255474008353786406260291)
      ·
        refine ⟨10883211012530679609390437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7255474008353786406260291 10883211012530679609390437)
        ·
          refine ⟨2040602064849502426760707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10883211012530679609390437 2040602064849502426760707)
          ·
            refine ⟨3060903097274253640141061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2040602064849502426760707 3060903097274253640141061)
            ·
              refine ⟨573919330738922557526449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3060903097274253640141061 573919330738922557526449)
              ·
                refine ⟨430439498054191918144837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 573919330738922557526449 430439498054191918144837)
                ·
                  refine ⟨80707405885160984652157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 430439498054191918144837 80707405885160984652157)
                  ·
                    rfl

theorem cell22_707297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 4, 2, 4].length) (baseStart_707297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_707297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_707297 prefixEnd_707297 := by exact prefixLift 707297
  have htrace : WordTrace (prefixWord ++ tailWord_707297) baseStart_707297 baseEnd_707297 := by
    simpa [prefixWord, tailWord_707297, baseEnd_707297] using wordTrace_append hprefix tailTrace_707297
  have hstable : (prefixWord ++ tailWord_707297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707297).length < 2 ^ (prefixWord ++ tailWord_707297).sum := by decide
  have hdescent : baseEnd_707297 < baseStart_707297 := by decide
  rcases family_descends (prefixWord ++ tailWord_707297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707346 : List Nat := [3, 2, 4, 1, 2, 2, 1, 2, 2, 3]
def baseStart_707346 : Nat := 118140960795 + 707346 * 2 ^ 59
def prefixEnd_707346 : Nat := 4983230072969 + 3 ^ 40 * 707346 * 2
def baseEnd_707346 : Nat := 242138991356863159481321

theorem tailTrace_707346 : CollatzResearch.WordTrace tailWord_707346 prefixEnd_707346 242138991356863159481321 := by
  unfold tailWord_707346
  simp only [CollatzResearch.WordTrace]
  refine ⟨6449757023853430481031473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17199352063609147949417261 6449757023853430481031473)
  ·
    refine ⟨4837317767890072860773605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6449757023853430481031473 4837317767890072860773605)
    ·
      refine ⟨906997081479388661395051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4837317767890072860773605 906997081479388661395051)
      ·
        refine ⟨1360495622219082992092577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 906997081479388661395051 1360495622219082992092577)
        ·
          refine ⟨1020371716664312244069433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1360495622219082992092577 1020371716664312244069433)
          ·
            refine ⟨765278787498234183052075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1020371716664312244069433 765278787498234183052075)
            ·
              refine ⟨1147918181247351274578113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 765278787498234183052075 1147918181247351274578113)
              ·
                refine ⟨860938635935513455933585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1147918181247351274578113 860938635935513455933585)
                ·
                  refine ⟨645703976951635091950189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 860938635935513455933585 645703976951635091950189)
                  ·
                    refine ⟨242138991356863159481321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 645703976951635091950189 242138991356863159481321)
                    ·
                      rfl

theorem cell22_707346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_707346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_707346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_707346 prefixEnd_707346 := by exact prefixLift 707346
  have htrace : WordTrace (prefixWord ++ tailWord_707346) baseStart_707346 baseEnd_707346 := by
    simpa [prefixWord, tailWord_707346, baseEnd_707346] using wordTrace_append hprefix tailTrace_707346
  have hstable : (prefixWord ++ tailWord_707346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707346).length < 2 ^ (prefixWord ++ tailWord_707346).sum := by decide
  have hdescent : baseEnd_707346 < baseStart_707346 := by decide
  rcases family_descends (prefixWord ++ tailWord_707346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707353 : List Nat := [1, 2, 1, 2, 1, 1, 1, 8, 5]
def baseStart_707353 : Nat := 118140960795 + 707353 * 2 ^ 59
def prefixEnd_707353 : Nat := 4983230072969 + 3 ^ 40 * 707353 * 2
def baseEnd_707353 : Nat := 80713795866639158185433

theorem tailTrace_707353 : CollatzResearch.WordTrace tailWord_707353 prefixEnd_707353 80713795866639158185433 := by
  unfold tailWord_707353
  simp only [CollatzResearch.WordTrace]
  refine ⟨25799283406388362119630713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17199522270925574746420475 25799283406388362119630713)
  ·
    refine ⟨19349462554791271589723035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25799283406388362119630713 19349462554791271589723035)
    ·
      refine ⟨29024193832186907384584553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19349462554791271589723035 29024193832186907384584553)
      ·
        refine ⟨21768145374140180538438415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29024193832186907384584553 21768145374140180538438415)
        ·
          refine ⟨32652218061210270807657623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21768145374140180538438415 32652218061210270807657623)
          ·
            refine ⟨48978327091815406211486435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32652218061210270807657623 48978327091815406211486435)
            ·
              refine ⟨73467490637723109317229653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48978327091815406211486435 73467490637723109317229653)
              ·
                refine ⟨860947155910817687311285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 73467490637723109317229653 860947155910817687311285)
                ·
                  refine ⟨80713795866639158185433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 860947155910817687311285 80713795866639158185433)
                  ·
                    rfl

theorem cell22_707353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 8, 5].length) (baseStart_707353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_707353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_707353 prefixEnd_707353 := by exact prefixLift 707353
  have htrace : WordTrace (prefixWord ++ tailWord_707353) baseStart_707353 baseEnd_707353 := by
    simpa [prefixWord, tailWord_707353, baseEnd_707353] using wordTrace_append hprefix tailTrace_707353
  have hstable : (prefixWord ++ tailWord_707353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707353).length < 2 ^ (prefixWord ++ tailWord_707353).sum := by decide
  have hdescent : baseEnd_707353 < baseStart_707353 := by decide
  rcases family_descends (prefixWord ++ tailWord_707353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707400 : List Nat := [2, 1, 3, 1, 1, 3, 1, 5, 1, 4]
def baseStart_707400 : Nat := 118140960795 + 707400 * 2 ^ 59
def prefixEnd_707400 : Nat := 4983230072969 + 3 ^ 40 * 707400 * 2
def baseEnd_707400 : Nat := 242157476660425018631155

theorem tailTrace_707400 : CollatzResearch.WordTrace tailWord_707400 prefixEnd_707400 242157476660425018631155 := by
  unfold tailWord_707400
  simp only [CollatzResearch.WordTrace]
  refine ⟨12900498818609044573295827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17200665091478726097727769 12900498818609044573295827)
  ·
    refine ⟨19350748227913566859943741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12900498818609044573295827 19350748227913566859943741)
    ·
      refine ⟨7256530585467587572478903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19350748227913566859943741 7256530585467587572478903)
      ·
        refine ⟨10884795878201381358718355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7256530585467587572478903 10884795878201381358718355)
        ·
          refine ⟨16327193817302072038077533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10884795878201381358718355 16327193817302072038077533)
          ·
            refine ⟨6122697681488277014279075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16327193817302072038077533 6122697681488277014279075)
            ·
              refine ⟨9184046522232415521418613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6122697681488277014279075 9184046522232415521418613)
              ·
                refine ⟨861004361459288955132995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9184046522232415521418613 861004361459288955132995)
                ·
                  refine ⟨1291506542188933432699493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 861004361459288955132995 1291506542188933432699493)
                  ·
                    refine ⟨242157476660425018631155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1291506542188933432699493 242157476660425018631155)
                    ·
                      rfl

theorem cell22_707400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 5, 1, 4].length) (baseStart_707400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_707400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_707400 prefixEnd_707400 := by exact prefixLift 707400
  have htrace : WordTrace (prefixWord ++ tailWord_707400) baseStart_707400 baseEnd_707400 := by
    simpa [prefixWord, tailWord_707400, baseEnd_707400] using wordTrace_append hprefix tailTrace_707400
  have hstable : (prefixWord ++ tailWord_707400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707400).length < 2 ^ (prefixWord ++ tailWord_707400).sum := by decide
  have hdescent : baseEnd_707400 < baseStart_707400 := by decide
  rcases family_descends (prefixWord ++ tailWord_707400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707415 : List Nat := [1, 1, 3, 2, 4, 1, 3, 1, 6]
def baseStart_707415 : Nat := 118140960795 + 707415 * 2 ^ 59
def prefixEnd_707415 : Nat := 4983230072969 + 3 ^ 40 * 707415 * 2
def baseEnd_707415 : Nat := 80720870488989993168703

theorem tailTrace_707415 : CollatzResearch.WordTrace tailWord_707415 prefixEnd_707415 80720870488989993168703 := by
  unfold tailWord_707415
  simp only [CollatzResearch.WordTrace]
  refine ⟨25801544732163746708387699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17201029821442497805591799 25801544732163746708387699)
  ·
    refine ⟨38702317098245620062581549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25801544732163746708387699 38702317098245620062581549)
    ·
      refine ⟨14513368911842107523468081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38702317098245620062581549 14513368911842107523468081)
      ·
        refine ⟨10885026683881580642601061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14513368911842107523468081 10885026683881580642601061)
        ·
          refine ⟨2040942503227796370487699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10885026683881580642601061 2040942503227796370487699)
          ·
            refine ⟨3061413754841694555731549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2040942503227796370487699 3061413754841694555731549)
            ·
              refine ⟨1148030158065635458399331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3061413754841694555731549 1148030158065635458399331)
              ·
                refine ⟨1722045237098453187598997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1148030158065635458399331 1722045237098453187598997)
                ·
                  refine ⟨80720870488989993168703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1722045237098453187598997 80720870488989993168703)
                  ·
                    rfl

theorem cell22_707415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 3, 1, 6].length) (baseStart_707415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_707415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_707415 prefixEnd_707415 := by exact prefixLift 707415
  have htrace : WordTrace (prefixWord ++ tailWord_707415) baseStart_707415 baseEnd_707415 := by
    simpa [prefixWord, tailWord_707415, baseEnd_707415] using wordTrace_append hprefix tailTrace_707415
  have hstable : (prefixWord ++ tailWord_707415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707415).length < 2 ^ (prefixWord ++ tailWord_707415).sum := by decide
  have hdescent : baseEnd_707415 < baseStart_707415 := by decide
  rcases family_descends (prefixWord ++ tailWord_707415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707443 : List Nat := [1, 1, 1, 2, 2, 1, 6, 8]
def baseStart_707443 : Nat := 118140960795 + 707443 * 2 ^ 59
def prefixEnd_707443 : Nat := 4983230072969 + 3 ^ 40 * 707443 * 2
def baseEnd_707443 : Nat := 26908021826576359978447

theorem tailTrace_707443 : CollatzResearch.WordTrace tailWord_707443 prefixEnd_707443 26908021826576359978447 := by
  unfold tailWord_707443
  simp only [CollatzResearch.WordTrace]
  refine ⟨25802565976062307490406983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17201710650708204993604655 25802565976062307490406983)
  ·
    refine ⟨38703848964093461235610475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25802565976062307490406983 38703848964093461235610475)
    ·
      refine ⟨58055773446140191853415713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38703848964093461235610475 58055773446140191853415713)
      ·
        refine ⟨43541830084605143890061785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58055773446140191853415713 43541830084605143890061785)
        ·
          refine ⟨32656372563453857917546339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43541830084605143890061785 32656372563453857917546339)
          ·
            refine ⟨48984558845180786876319509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32656372563453857917546339 48984558845180786876319509)
            ·
              refine ⟨2296151195867849384827477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 48984558845180786876319509 2296151195867849384827477)
              ·
                refine ⟨26908021826576359978447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2296151195867849384827477 26908021826576359978447)
                ·
                  rfl

theorem cell22_707443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 8].length) (baseStart_707443 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_707443 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_707443 prefixEnd_707443 := by exact prefixLift 707443
  have htrace : WordTrace (prefixWord ++ tailWord_707443) baseStart_707443 baseEnd_707443 := by
    simpa [prefixWord, tailWord_707443, baseEnd_707443] using wordTrace_append hprefix tailTrace_707443
  have hstable : (prefixWord ++ tailWord_707443).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707443).length < 2 ^ (prefixWord ++ tailWord_707443).sum := by decide
  have hdescent : baseEnd_707443 < baseStart_707443 := by decide
  rcases family_descends (prefixWord ++ tailWord_707443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707464 : List Nat := [2, 1, 3, 3, 2, 2, 2, 2, 2, 3]
def baseStart_707464 : Nat := 118140960795 + 707464 * 2 ^ 59
def prefixEnd_707464 : Nat := 4983230072969 + 3 ^ 40 * 707464 * 2
def baseEnd_707464 : Nat := 242179385168350185030959

theorem tailTrace_707464 : CollatzResearch.WordTrace tailWord_707464 prefixEnd_707464 242179385168350185030959 := by
  unfold tailWord_707464
  simp only [CollatzResearch.WordTrace]
  refine ⟨12901665954493114038460723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17202221272657485384614297 12901665954493114038460723)
  ·
    refine ⟨19352498931739671057691085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12901665954493114038460723 19352498931739671057691085)
    ·
      refine ⟨7257187099402376646634157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19352498931739671057691085 7257187099402376646634157)
      ·
        refine ⟨2721445162275891242487809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7257187099402376646634157 2721445162275891242487809)
        ·
          refine ⟨2041083871706918431865857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2721445162275891242487809 2041083871706918431865857)
          ·
            refine ⟨1530812903780188823899393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2041083871706918431865857 1530812903780188823899393)
            ·
              refine ⟨1148109677835141617924545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1530812903780188823899393 1148109677835141617924545)
              ·
                refine ⟨861082258376356213443409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1148109677835141617924545 861082258376356213443409)
                ·
                  refine ⟨645811693782267160082557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 861082258376356213443409 645811693782267160082557)
                  ·
                    refine ⟨242179385168350185030959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 645811693782267160082557 242179385168350185030959)
                    ·
                      rfl

theorem cell22_707464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2, 2, 2, 3].length) (baseStart_707464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_707464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_707464 prefixEnd_707464 := by exact prefixLift 707464
  have htrace : WordTrace (prefixWord ++ tailWord_707464) baseStart_707464 baseEnd_707464 := by
    simpa [prefixWord, tailWord_707464, baseEnd_707464] using wordTrace_append hprefix tailTrace_707464
  have hstable : (prefixWord ++ tailWord_707464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707464).length < 2 ^ (prefixWord ++ tailWord_707464).sum := by decide
  have hdescent : baseEnd_707464 < baseStart_707464 := by decide
  rcases family_descends (prefixWord ++ tailWord_707464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707466 : List Nat := [3, 1, 2, 4, 1, 3, 2, 2, 4]
def baseStart_707466 : Nat := 118140960795 + 707466 * 2 ^ 59
def prefixEnd_707466 : Nat := 4983230072969 + 3 ^ 40 * 707466 * 2
def baseEnd_707466 : Nat := 80726689936407615493651

theorem tailTrace_707466 : CollatzResearch.WordTrace tailWord_707466 prefixEnd_707466 80726689936407615493651 := by
  unfold tailWord_707466
  simp only [CollatzResearch.WordTrace]
  refine ⟨6450851213744745604623563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17202269903319321612329501 6450851213744745604623563)
  ·
    refine ⟨9676276820617118406935345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6450851213744745604623563 9676276820617118406935345)
    ·
      refine ⟨7257207615462838805201509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9676276820617118406935345 7257207615462838805201509)
      ·
        refine ⟨1360726427899282275975283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7257207615462838805201509 1360726427899282275975283)
        ·
          refine ⟨2041089641848923413962925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1360726427899282275975283 2041089641848923413962925)
          ·
            refine ⟨765408615693346280236097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2041089641848923413962925 765408615693346280236097)
            ·
              refine ⟨574056461770009710177073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 765408615693346280236097 574056461770009710177073)
              ·
                refine ⟨430542346327507282632805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 574056461770009710177073 430542346327507282632805)
                ·
                  refine ⟨80726689936407615493651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 430542346327507282632805 80726689936407615493651)
                  ·
                    rfl

theorem cell22_707466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 2, 2, 4].length) (baseStart_707466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_707466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_707466 prefixEnd_707466 := by exact prefixLift 707466
  have htrace : WordTrace (prefixWord ++ tailWord_707466) baseStart_707466 baseEnd_707466 := by
    simpa [prefixWord, tailWord_707466, baseEnd_707466] using wordTrace_append hprefix tailTrace_707466
  have hstable : (prefixWord ++ tailWord_707466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707466).length < 2 ^ (prefixWord ++ tailWord_707466).sum := by decide
  have hdescent : baseEnd_707466 < baseStart_707466 := by decide
  rcases family_descends (prefixWord ++ tailWord_707466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707492 : List Nat := [2, 3, 1, 2, 1, 2, 3, 2, 3, 3]
def baseStart_707492 : Nat := 118140960795 + 707492 * 2 ^ 59
def prefixEnd_707492 : Nat := 4983230072969 + 3 ^ 40 * 707492 * 2
def baseEnd_707492 : Nat := 242188970140567445330873

theorem tailTrace_707492 : CollatzResearch.WordTrace tailWord_707492 prefixEnd_707492 242188970140567445330873 := by
  unfold tailWord_707492
  simp only [CollatzResearch.WordTrace]
  refine ⟨12902176576442394429470365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17202902101923192572627153 12902176576442394429470365)
  ·
    refine ⟨4838316216165897911051387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12902176576442394429470365 4838316216165897911051387)
    ·
      refine ⟨7257474324248846866577081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4838316216165897911051387 7257474324248846866577081)
      ·
        refine ⟨5443105743186635149932811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7257474324248846866577081 5443105743186635149932811)
        ·
          refine ⟨8164658614779952724899217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5443105743186635149932811 8164658614779952724899217)
          ·
            refine ⟨6123493961084964543674413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8164658614779952724899217 6123493961084964543674413)
            ·
              refine ⟨2296310235406861703877905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6123493961084964543674413 2296310235406861703877905)
              ·
                refine ⟨1722232676555146277908429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2296310235406861703877905 1722232676555146277908429)
                ·
                  refine ⟨645837253708179854215661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1722232676555146277908429 645837253708179854215661)
                  ·
                    refine ⟨242188970140567445330873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 645837253708179854215661 242188970140567445330873)
                    ·
                      rfl

theorem cell22_707492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 2, 3, 3].length) (baseStart_707492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_707492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_707492 prefixEnd_707492 := by exact prefixLift 707492
  have htrace : WordTrace (prefixWord ++ tailWord_707492) baseStart_707492 baseEnd_707492 := by
    simpa [prefixWord, tailWord_707492, baseEnd_707492] using wordTrace_append hprefix tailTrace_707492
  have hstable : (prefixWord ++ tailWord_707492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707492).length < 2 ^ (prefixWord ++ tailWord_707492).sum := by decide
  have hdescent : baseEnd_707492 < baseStart_707492 := by decide
  rcases family_descends (prefixWord ++ tailWord_707492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707520 : List Nat := [2, 1, 1, 2, 3, 3, 1, 2, 2, 5]
def baseStart_707520 : Nat := 118140960795 + 707520 * 2 ^ 59
def prefixEnd_707520 : Nat := 4983230072969 + 3 ^ 40 * 707520 * 2
def baseEnd_707520 : Nat := 242198555112784705630787

theorem tailTrace_707520 : CollatzResearch.WordTrace tailWord_707520 prefixEnd_707520 242198555112784705630787 := by
  unfold tailWord_707520
  simp only [CollatzResearch.WordTrace]
  refine ⟨12902687198391674820480007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17203582931188899760640009 12902687198391674820480007)
  ·
    refine ⟨19354030797587512230720011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12902687198391674820480007 19354030797587512230720011)
    ·
      refine ⟨29031046196381268346080017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19354030797587512230720011 29031046196381268346080017)
      ·
        refine ⟨21773284647285951259560013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29031046196381268346080017 21773284647285951259560013)
        ·
          refine ⟨8164981742732231722335005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21773284647285951259560013 8164981742732231722335005)
          ·
            refine ⟨3061868153524586895875627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8164981742732231722335005 3061868153524586895875627)
            ·
              refine ⟨4592802230286880343813441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3061868153524586895875627 4592802230286880343813441)
              ·
                refine ⟨3444601672715160257860081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4592802230286880343813441 3444601672715160257860081)
                ·
                  refine ⟨2583451254536370193395061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3444601672715160257860081 2583451254536370193395061)
                  ·
                    refine ⟨242198555112784705630787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2583451254536370193395061 242198555112784705630787)
                    ·
                      rfl

theorem cell22_707520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 2, 2, 5].length) (baseStart_707520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_707520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_707520 prefixEnd_707520 := by exact prefixLift 707520
  have htrace : WordTrace (prefixWord ++ tailWord_707520) baseStart_707520 baseEnd_707520 := by
    simpa [prefixWord, tailWord_707520, baseEnd_707520] using wordTrace_append hprefix tailTrace_707520
  have hstable : (prefixWord ++ tailWord_707520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707520).length < 2 ^ (prefixWord ++ tailWord_707520).sum := by decide
  have hdescent : baseEnd_707520 < baseStart_707520 := by decide
  rcases family_descends (prefixWord ++ tailWord_707520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707595 : List Nat := [1, 1, 1, 1, 6, 2, 1, 9]
def baseStart_707595 : Nat := 118140960795 + 707595 * 2 ^ 59
def prefixEnd_707595 : Nat := 4983230072969 + 3 ^ 40 * 707595 * 2
def baseEnd_707595 : Nat := 26913803238389945556173

theorem tailTrace_707595 : CollatzResearch.WordTrace tailWord_707595 prefixEnd_707595 26913803238389945556173 := by
  unfold tailWord_707595
  simp only [CollatzResearch.WordTrace]
  refine ⟨25808109871511637449940239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17205406581007758299960159 25808109871511637449940239)
  ·
    refine ⟨38712164807267456174910359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25808109871511637449940239 38712164807267456174910359)
    ·
      refine ⟨58068247210901184262365539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38712164807267456174910359 58068247210901184262365539)
      ·
        refine ⟨87102370816351776393548309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58068247210901184262365539 87102370816351776393548309)
        ·
          refine ⟨4082923632016489518447577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 87102370816351776393548309 4082923632016489518447577)
          ·
            refine ⟨3062192724012367138835683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4082923632016489518447577 3062192724012367138835683)
            ·
              refine ⟨4593289086018550708253525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3062192724012367138835683 4593289086018550708253525)
              ·
                refine ⟨26913803238389945556173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4593289086018550708253525 26913803238389945556173)
                ·
                  rfl

theorem cell22_707595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 9].length) (baseStart_707595 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_707595 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_707595 prefixEnd_707595 := by exact prefixLift 707595
  have htrace : WordTrace (prefixWord ++ tailWord_707595) baseStart_707595 baseEnd_707595 := by
    simpa [prefixWord, tailWord_707595, baseEnd_707595] using wordTrace_append hprefix tailTrace_707595
  have hstable : (prefixWord ++ tailWord_707595).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707595).length < 2 ^ (prefixWord ++ tailWord_707595).sum := by decide
  have hdescent : baseEnd_707595 < baseStart_707595 := by decide
  rcases family_descends (prefixWord ++ tailWord_707595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707661 : List Nat := [1, 6, 1, 1, 1, 3, 1, 2, 3, 3]
def baseStart_707661 : Nat := 118140960795 + 707661 * 2 ^ 59
def prefixEnd_707661 : Nat := 4983230072969 + 3 ^ 40 * 707661 * 2
def baseEnd_707661 : Nat := 242246822294307337855355

theorem tailTrace_707661 : CollatzResearch.WordTrace tailWord_707661 prefixEnd_707661 242246822294307337855355 := by
  unfold tailWord_707661
  simp only [CollatzResearch.WordTrace]
  refine ⟨25810517089272530721842837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17207011392848353814561891 25810517089272530721842837)
  ·
    refine ⟨1209867988559649877586383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 25810517089272530721842837 1209867988559649877586383)
    ·
      refine ⟨1814801982839474816379575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1209867988559649877586383 1814801982839474816379575)
      ·
        refine ⟨2722202974259212224569363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1814801982839474816379575 2722202974259212224569363)
        ·
          refine ⟨4083304461388818336854045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2722202974259212224569363 4083304461388818336854045)
          ·
            refine ⟨1531239173020806876320267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4083304461388818336854045 1531239173020806876320267)
            ·
              refine ⟨2296858759531210314480401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1531239173020806876320267 2296858759531210314480401)
              ·
                refine ⟨1722644069648407735860301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2296858759531210314480401 1722644069648407735860301)
                ·
                  refine ⟨645991526118152900947613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1722644069648407735860301 645991526118152900947613)
                  ·
                    refine ⟨242246822294307337855355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 645991526118152900947613 242246822294307337855355)
                    ·
                      rfl

theorem cell22_707661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 2, 3, 3].length) (baseStart_707661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_707661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_707661 prefixEnd_707661 := by exact prefixLift 707661
  have htrace : WordTrace (prefixWord ++ tailWord_707661) baseStart_707661 baseEnd_707661 := by
    simpa [prefixWord, tailWord_707661, baseEnd_707661] using wordTrace_append hprefix tailTrace_707661
  have hstable : (prefixWord ++ tailWord_707661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707661).length < 2 ^ (prefixWord ++ tailWord_707661).sum := by decide
  have hdescent : baseEnd_707661 < baseStart_707661 := by decide
  rcases family_descends (prefixWord ++ tailWord_707661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707736 : List Nat := [2, 1, 2, 4, 2, 1, 3, 3, 4]
def baseStart_707736 : Nat := 118140960795 + 707736 * 2 ^ 59
def prefixEnd_707736 : Nat := 4983230072969 + 3 ^ 40 * 707736 * 2
def baseEnd_707736 : Nat := 80757498775677380743375

theorem tailTrace_707736 : CollatzResearch.WordTrace tailWord_707736 prefixEnd_707736 80757498775677380743375 := by
  unfold tailWord_707736
  simp only [CollatzResearch.WordTrace]
  refine ⟨12906626282000409265411531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17208835042667212353882041 12906626282000409265411531)
  ·
    refine ⟨19359939423000613898117297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12906626282000409265411531 19359939423000613898117297)
    ·
      refine ⟨14519954567250460423587973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19359939423000613898117297 14519954567250460423587973)
      ·
        refine ⟨2722491481359461329422745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14519954567250460423587973 2722491481359461329422745)
        ·
          refine ⟨2041868611019595997067059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2722491481359461329422745 2041868611019595997067059)
          ·
            refine ⟨3062802916529393995600589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2041868611019595997067059 3062802916529393995600589)
            ·
              refine ⟨1148551093698522748350221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3062802916529393995600589 1148551093698522748350221)
              ·
                refine ⟨430706660136946030631333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1148551093698522748350221 430706660136946030631333)
                ·
                  refine ⟨80757498775677380743375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 430706660136946030631333 80757498775677380743375)
                  ·
                    rfl

theorem cell22_707736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 3, 3, 4].length) (baseStart_707736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_707736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_707736 prefixEnd_707736 := by exact prefixLift 707736
  have htrace : WordTrace (prefixWord ++ tailWord_707736) baseStart_707736 baseEnd_707736 := by
    simpa [prefixWord, tailWord_707736, baseEnd_707736] using wordTrace_append hprefix tailTrace_707736
  have hstable : (prefixWord ++ tailWord_707736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707736).length < 2 ^ (prefixWord ++ tailWord_707736).sum := by decide
  have hdescent : baseEnd_707736 < baseStart_707736 := by decide
  rcases family_descends (prefixWord ++ tailWord_707736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707749 : List Nat := [1, 3, 1, 2, 1, 5, 1, 2, 2, 4]
def baseStart_707749 : Nat := 118140960795 + 707749 * 2 ^ 59
def prefixEnd_707749 : Nat := 4983230072969 + 3 ^ 40 * 707749 * 2
def baseEnd_707749 : Nat := 242276946492704441655085

theorem tailTrace_707749 : CollatzResearch.WordTrace tailWord_707749 prefixEnd_707749 242276946492704441655085 := by
  unfold tailWord_707749
  simp only [CollatzResearch.WordTrace]
  refine ⟨25813726712953721751046301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17209151141969147834030867 25813726712953721751046301)
  ·
    refine ⟨9680147517357645656642363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25813726712953721751046301 9680147517357645656642363)
    ·
      refine ⟨14520221276036468484963545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9680147517357645656642363 14520221276036468484963545)
      ·
        refine ⟨10890165957027351363722659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14520221276036468484963545 10890165957027351363722659)
        ·
          refine ⟨16335248935541027045583989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10890165957027351363722659 16335248935541027045583989)
          ·
            refine ⟨1531429587706971285523499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16335248935541027045583989 1531429587706971285523499)
            ·
              refine ⟨2297144381560456928285249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1531429587706971285523499 2297144381560456928285249)
              ·
                refine ⟨1722858286170342696213937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2297144381560456928285249 1722858286170342696213937)
                ·
                  refine ⟨1292143714627757022160453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1722858286170342696213937 1292143714627757022160453)
                  ·
                    refine ⟨242276946492704441655085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1292143714627757022160453 242276946492704441655085)
                    ·
                      rfl

theorem cell22_707749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 2, 2, 4].length) (baseStart_707749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_707749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_707749 prefixEnd_707749 := by exact prefixLift 707749
  have htrace : WordTrace (prefixWord ++ tailWord_707749) baseStart_707749 baseEnd_707749 := by
    simpa [prefixWord, tailWord_707749, baseEnd_707749] using wordTrace_append hprefix tailTrace_707749
  have hstable : (prefixWord ++ tailWord_707749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707749).length < 2 ^ (prefixWord ++ tailWord_707749).sum := by decide
  have hdescent : baseEnd_707749 < baseStart_707749 := by decide
  rcases family_descends (prefixWord ++ tailWord_707749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707751 : List Nat := [1, 1, 6, 2, 1, 1, 2, 1, 4, 3]
def baseStart_707751 : Nat := 118140960795 + 707751 * 2 ^ 59
def prefixEnd_707751 : Nat := 4983230072969 + 3 ^ 40 * 707751 * 2
def baseEnd_707751 : Nat := 242277631133577103105079

theorem tailTrace_707751 : CollatzResearch.WordTrace tailWord_707751 prefixEnd_707751 242277631133577103105079 := by
  unfold tailWord_707751
  simp only [CollatzResearch.WordTrace]
  refine ⟨25813799658946476092619107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17209199772630984061746071 25813799658946476092619107)
  ·
    refine ⟨38720699488419714138928661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25813799658946476092619107 38720699488419714138928661)
    ·
      refine ⟨1815032788519674100262281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 38720699488419714138928661 1815032788519674100262281)
      ·
        refine ⟨1361274591389755575196711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1815032788519674100262281 1361274591389755575196711)
        ·
          refine ⟨2041911887084633362795067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1361274591389755575196711 2041911887084633362795067)
          ·
            refine ⟨3062867830626950044192601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2041911887084633362795067 3062867830626950044192601)
            ·
              refine ⟨2297150872970212533144451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3062867830626950044192601 2297150872970212533144451)
              ·
                refine ⟨3445726309455318799716677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2297150872970212533144451 3445726309455318799716677)
                ·
                  refine ⟨646073683022872274946877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3445726309455318799716677 646073683022872274946877)
                  ·
                    refine ⟨242277631133577103105079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 646073683022872274946877 242277631133577103105079)
                    ·
                      rfl

theorem cell22_707751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 1, 4, 3].length) (baseStart_707751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_707751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_707751 prefixEnd_707751 := by exact prefixLift 707751
  have htrace : WordTrace (prefixWord ++ tailWord_707751) baseStart_707751 baseEnd_707751 := by
    simpa [prefixWord, tailWord_707751, baseEnd_707751] using wordTrace_append hprefix tailTrace_707751
  have hstable : (prefixWord ++ tailWord_707751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707751).length < 2 ^ (prefixWord ++ tailWord_707751).sum := by decide
  have hdescent : baseEnd_707751 < baseStart_707751 := by decide
  rcases family_descends (prefixWord ++ tailWord_707751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707809 : List Nat := [1, 2, 3, 1, 3, 2, 1, 4, 5]
def baseStart_707809 : Nat := 118140960795 + 707809 * 2 ^ 59
def prefixEnd_707809 : Nat := 4983230072969 + 3 ^ 40 * 707809 * 2
def baseEnd_707809 : Nat := 80765828572961428384967

theorem tailTrace_707809 : CollatzResearch.WordTrace tailWord_707809 prefixEnd_707809 80765828572961428384967 := by
  unfold tailWord_707809
  simp only [CollatzResearch.WordTrace]
  refine ⟨25815915092736351998230481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17210610061824234665486987 25815915092736351998230481)
  ·
    refine ⟨19361936319552263998672861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25815915092736351998230481 19361936319552263998672861)
    ·
      refine ⟨7260726119832098999502323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19361936319552263998672861 7260726119832098999502323)
      ·
        refine ⟨10891089179748148499253485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7260726119832098999502323 10891089179748148499253485)
        ·
          refine ⟨4084158442405555687220057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10891089179748148499253485 4084158442405555687220057)
          ·
            refine ⟨3063118831804166765415043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4084158442405555687220057 3063118831804166765415043)
            ·
              refine ⟨4594678247706250148122565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3063118831804166765415043 4594678247706250148122565)
              ·
                refine ⟨861502171444921902772981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4594678247706250148122565 861502171444921902772981)
                ·
                  refine ⟨80765828572961428384967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 861502171444921902772981 80765828572961428384967)
                  ·
                    rfl

theorem cell22_707809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 4, 5].length) (baseStart_707809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_707809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_707809 prefixEnd_707809 := by exact prefixLift 707809
  have htrace : WordTrace (prefixWord ++ tailWord_707809) baseStart_707809 baseEnd_707809 := by
    simpa [prefixWord, tailWord_707809, baseEnd_707809] using wordTrace_append hprefix tailTrace_707809
  have hstable : (prefixWord ++ tailWord_707809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707809).length < 2 ^ (prefixWord ++ tailWord_707809).sum := by decide
  have hdescent : baseEnd_707809 < baseStart_707809 := by decide
  rcases family_descends (prefixWord ++ tailWord_707809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707839 : List Nat := [1, 1, 2, 2, 1, 5, 2, 1, 3, 4]
def baseStart_707839 : Nat := 118140960795 + 707839 * 2 ^ 59
def prefixEnd_707839 : Nat := 4983230072969 + 3 ^ 40 * 707839 * 2
def baseEnd_707839 : Nat := 242307755331974206904809

theorem tailTrace_707839 : CollatzResearch.WordTrace tailWord_707839 prefixEnd_707839 242307755331974206904809 := by
  unfold tailWord_707839
  simp only [CollatzResearch.WordTrace]
  refine ⟨25817009282627667121822571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17211339521751778081215047 25817009282627667121822571)
  ·
    refine ⟨38725513923941500682733857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25817009282627667121822571 38725513923941500682733857)
    ·
      refine ⟨29044135442956125512050393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38725513923941500682733857 29044135442956125512050393)
      ·
        refine ⟨21783101582217094134037795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29044135442956125512050393 21783101582217094134037795)
        ·
          refine ⟨32674652373325641201056693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21783101582217094134037795 32674652373325641201056693)
          ·
            refine ⟨3063248659999278862599065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32674652373325641201056693 3063248659999278862599065)
            ·
              refine ⟨2297436494999459146949299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3063248659999278862599065 2297436494999459146949299)
              ·
                refine ⟨3446154742499188720423949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2297436494999459146949299 3446154742499188720423949)
                ·
                  refine ⟨1292308028437195770158981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3446154742499188720423949 1292308028437195770158981)
                  ·
                    refine ⟨242307755331974206904809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1292308028437195770158981 242307755331974206904809)
                    ·
                      rfl

theorem cell22_707839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 1, 3, 4].length) (baseStart_707839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_707839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_707839 prefixEnd_707839 := by exact prefixLift 707839
  have htrace : WordTrace (prefixWord ++ tailWord_707839) baseStart_707839 baseEnd_707839 := by
    simpa [prefixWord, tailWord_707839, baseEnd_707839] using wordTrace_append hprefix tailTrace_707839
  have hstable : (prefixWord ++ tailWord_707839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707839).length < 2 ^ (prefixWord ++ tailWord_707839).sum := by decide
  have hdescent : baseEnd_707839 < baseStart_707839 := by decide
  rcases family_descends (prefixWord ++ tailWord_707839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707871 : List Nat := [1, 1, 2, 4, 4, 1, 2, 1, 6]
def baseStart_707871 : Nat := 118140960795 + 707871 * 2 ^ 59
def prefixEnd_707871 : Nat := 4983230072969 + 3 ^ 40 * 707871 * 2
def baseEnd_707871 : Nat := 80772903195312263368237

theorem tailTrace_707871 : CollatzResearch.WordTrace tailWord_707871 prefixEnd_707871 80772903195312263368237 := by
  unfold tailWord_707871
  simp only [CollatzResearch.WordTrace]
  refine ⟨25818176418511736586987467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17212117612341157724658311 25818176418511736586987467)
  ·
    refine ⟨38727264627767604880481201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25818176418511736586987467 38727264627767604880481201)
    ·
      refine ⟨29045448470825703660360901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38727264627767604880481201 29045448470825703660360901)
      ·
        refine ⟨5446021588279819436317669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29045448470825703660360901 5446021588279819436317669)
        ·
          refine ⟨1021129047802466144309563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5446021588279819436317669 1021129047802466144309563)
          ·
            refine ⟨1531693571703699216464345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1021129047802466144309563 1531693571703699216464345)
            ·
              refine ⟨1148770178777774412348259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1531693571703699216464345 1148770178777774412348259)
              ·
                refine ⟨1723155268166661618522389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1148770178777774412348259 1723155268166661618522389)
                ·
                  refine ⟨80772903195312263368237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1723155268166661618522389 80772903195312263368237)
                  ·
                    rfl

theorem cell22_707871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 2, 1, 6].length) (baseStart_707871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_707871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_707871 prefixEnd_707871 := by exact prefixLift 707871
  have htrace : WordTrace (prefixWord ++ tailWord_707871) baseStart_707871 baseEnd_707871 := by
    simpa [prefixWord, tailWord_707871, baseEnd_707871] using wordTrace_append hprefix tailTrace_707871
  have hstable : (prefixWord ++ tailWord_707871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707871).length < 2 ^ (prefixWord ++ tailWord_707871).sum := by decide
  have hdescent : baseEnd_707871 < baseStart_707871 := by decide
  rcases family_descends (prefixWord ++ tailWord_707871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707905 : List Nat := [1, 2, 5, 2, 1, 3, 1, 3, 4]
def baseStart_707905 : Nat := 118140960795 + 707905 * 2 ^ 59
def prefixEnd_707905 : Nat := 4983230072969 + 3 ^ 40 * 707905 * 2
def baseEnd_707905 : Nat := 80776782826924011584869

theorem tailTrace_707905 : CollatzResearch.WordTrace tailWord_707905 prefixEnd_707905 80776782826924011584869 := by
  unfold tailWord_707905
  simp only [CollatzResearch.WordTrace]
  refine ⟨25819416500388560393725169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17212944333592373595816779 25819416500388560393725169)
  ·
    refine ⟨19364562375291420295293877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25819416500388560393725169 19364562375291420295293877)
    ·
      refine ⟨1815427722683570652683801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19364562375291420295293877 1815427722683570652683801)
      ·
        refine ⟨1361570792012677989512851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1815427722683570652683801 1361570792012677989512851)
        ·
          refine ⟨2042356188019016984269277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1361570792012677989512851 2042356188019016984269277)
          ·
            refine ⟨765883570507131369100979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2042356188019016984269277 765883570507131369100979)
            ·
              refine ⟨1148825355760697053651469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 765883570507131369100979 1148825355760697053651469)
              ·
                refine ⟨430809508410261395119301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1148825355760697053651469 430809508410261395119301)
                ·
                  refine ⟨80776782826924011584869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 430809508410261395119301 80776782826924011584869)
                  ·
                    rfl

theorem cell22_707905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 1, 3, 4].length) (baseStart_707905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_707905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_707905 prefixEnd_707905 := by exact prefixLift 707905
  have htrace : WordTrace (prefixWord ++ tailWord_707905) baseStart_707905 baseEnd_707905 := by
    simpa [prefixWord, tailWord_707905, baseEnd_707905] using wordTrace_append hprefix tailTrace_707905
  have hstable : (prefixWord ++ tailWord_707905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707905).length < 2 ^ (prefixWord ++ tailWord_707905).sum := by decide
  have hdescent : baseEnd_707905 < baseStart_707905 := by decide
  rcases family_descends (prefixWord ++ tailWord_707905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707982 : List Nat := [4, 1, 1, 4, 2, 1, 1, 4, 1, 3]
def baseStart_707982 : Nat := 118140960795 + 707982 * 2 ^ 59
def prefixEnd_707982 : Nat := 4983230072969 + 3 ^ 40 * 707982 * 2
def baseEnd_707982 : Nat := 242356707154369500579371

theorem tailTrace_707982 : CollatzResearch.WordTrace tailWord_707982 prefixEnd_707982 242356707154369500579371 := by
  unfold tailWord_707982
  simp only [CollatzResearch.WordTrace]
  refine ⟨3227778115138700318034775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17214816614073068362852133 3227778115138700318034775)
  ·
    refine ⟨4841667172708050477052163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3227778115138700318034775 4841667172708050477052163)
    ·
      refine ⟨7262500759062075715578245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4841667172708050477052163 7262500759062075715578245)
      ·
        refine ⟨1361718892324139196670921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7262500759062075715578245 1361718892324139196670921)
        ·
          refine ⟨1021289169243104397503191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1361718892324139196670921 1021289169243104397503191)
          ·
            refine ⟨1531933753864656596254787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1021289169243104397503191 1531933753864656596254787)
            ·
              refine ⟨2297900630796984894382181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1531933753864656596254787 2297900630796984894382181)
              ·
                refine ⟨430856368274434667696659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2297900630796984894382181 430856368274434667696659)
                ·
                  refine ⟨646284552411652001544989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 430856368274434667696659 646284552411652001544989)
                  ·
                    refine ⟨242356707154369500579371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 646284552411652001544989 242356707154369500579371)
                    ·
                      rfl

theorem cell22_707982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 4, 1, 3].length) (baseStart_707982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_707982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_707982 prefixEnd_707982 := by exact prefixLift 707982
  have htrace : WordTrace (prefixWord ++ tailWord_707982) baseStart_707982 baseEnd_707982 := by
    simpa [prefixWord, tailWord_707982, baseEnd_707982] using wordTrace_append hprefix tailTrace_707982
  have hstable : (prefixWord ++ tailWord_707982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707982).length < 2 ^ (prefixWord ++ tailWord_707982).sum := by decide
  have hdescent : baseEnd_707982 < baseStart_707982 := by decide
  rcases family_descends (prefixWord ++ tailWord_707982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708023 : List Nat := [1, 1, 3, 1, 3, 2, 4, 3, 4]
def baseStart_708023 : Nat := 118140960795 + 708023 * 2 ^ 59
def prefixEnd_708023 : Nat := 4983230072969 + 3 ^ 40 * 708023 * 2
def baseEnd_708023 : Nat := 80790247430753020101415

theorem tailTrace_708023 : CollatzResearch.WordTrace tailWord_708023 prefixEnd_708023 80790247430753020101415 := by
  unfold tailWord_708023
  simp only [CollatzResearch.WordTrace]
  refine ⟨25823720313961066546520723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17215813542640711031013815 25823720313961066546520723)
  ·
    refine ⟨38735580470941599819781085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25823720313961066546520723 38735580470941599819781085)
    ·
      refine ⟨14525842676603099932417907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38735580470941599819781085 14525842676603099932417907)
      ·
        refine ⟨21788764014904649898626861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14525842676603099932417907 21788764014904649898626861)
        ·
          refine ⟨8170786505589243711985073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21788764014904649898626861 8170786505589243711985073)
          ·
            refine ⟨6128089879191932783988805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8170786505589243711985073 6128089879191932783988805)
            ·
              refine ⟨1149016852348487396997901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6128089879191932783988805 1149016852348487396997901)
              ·
                refine ⟨430881319630682773874213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1149016852348487396997901 430881319630682773874213)
                ·
                  refine ⟨80790247430753020101415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 430881319630682773874213 80790247430753020101415)
                  ·
                    rfl

theorem cell22_708023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 4, 3, 4].length) (baseStart_708023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_708023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_708023 prefixEnd_708023 := by exact prefixLift 708023
  have htrace : WordTrace (prefixWord ++ tailWord_708023) baseStart_708023 baseEnd_708023 := by
    simpa [prefixWord, tailWord_708023, baseEnd_708023] using wordTrace_append hprefix tailTrace_708023
  have hstable : (prefixWord ++ tailWord_708023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708023).length < 2 ^ (prefixWord ++ tailWord_708023).sum := by decide
  have hdescent : baseEnd_708023 < baseStart_708023 := by decide
  rcases family_descends (prefixWord ++ tailWord_708023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708171 : List Nat := [1, 1, 1, 1, 3, 1, 3, 4, 1, 6]
def baseStart_708171 : Nat := 118140960795 + 708171 * 2 ^ 59
def prefixEnd_708171 : Nat := 4983230072969 + 3 ^ 40 * 708171 * 2
def baseEnd_708171 : Nat := 242421405716836007603791

theorem tailTrace_708171 : CollatzResearch.WordTrace tailWord_708171 prefixEnd_708171 242421405716836007603791 := by
  unfold tailWord_708171
  simp only [CollatzResearch.WordTrace]
  refine ⟨25829118317424887822908367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17219412211616591881938911 25829118317424887822908367)
  ·
    refine ⟨38743677476137331734362551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25829118317424887822908367 38743677476137331734362551)
    ·
      refine ⟨58115516214205997601543827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38743677476137331734362551 58115516214205997601543827)
      ·
        refine ⟨87173274321308996402315741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58115516214205997601543827 87173274321308996402315741)
        ·
          refine ⟨32689977870490873650868403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87173274321308996402315741 32689977870490873650868403)
          ·
            refine ⟨49034966805736310476302605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32689977870490873650868403 49034966805736310476302605)
            ·
              refine ⟨18388112552151116428613477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49034966805736310476302605 18388112552151116428613477)
              ·
                refine ⟨3447771103528334330365027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18388112552151116428613477 3447771103528334330365027)
                ·
                  refine ⟨5171656655292501495547541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3447771103528334330365027 5171656655292501495547541)
                  ·
                    refine ⟨242421405716836007603791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5171656655292501495547541 242421405716836007603791)
                    ·
                      rfl

theorem cell22_708171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 4, 1, 6].length) (baseStart_708171 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_708171 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_708171 prefixEnd_708171 := by exact prefixLift 708171
  have htrace : WordTrace (prefixWord ++ tailWord_708171) baseStart_708171 baseEnd_708171 := by
    simpa [prefixWord, tailWord_708171, baseEnd_708171] using wordTrace_append hprefix tailTrace_708171
  have hstable : (prefixWord ++ tailWord_708171).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708171).length < 2 ^ (prefixWord ++ tailWord_708171).sum := by decide
  have hdescent : baseEnd_708171 < baseStart_708171 := by decide
  rcases family_descends (prefixWord ++ tailWord_708171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708186 : List Nat := [3, 1, 1, 2, 1, 1, 1, 12]
def baseStart_708186 : Nat := 118140960795 + 708186 * 2 ^ 59
def prefixEnd_708186 : Nat := 4983230072969 + 3 ^ 40 * 708186 * 2
def baseEnd_708186 : Nat := 26936282280375663164305

theorem tailTrace_708186 : CollatzResearch.WordTrace tailWord_708186 prefixEnd_708186 26936282280375663164305 := by
  unfold tailWord_708186
  simp only [CollatzResearch.WordTrace]
  refine ⟨6457416353092636346176103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17219776941580363589802941 6457416353092636346176103)
  ·
    refine ⟨9686124529638954519264155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6457416353092636346176103 9686124529638954519264155)
    ·
      refine ⟨14529186794458431778896233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9686124529638954519264155 14529186794458431778896233)
      ·
        refine ⟨10896890095843823834172175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14529186794458431778896233 10896890095843823834172175)
        ·
          refine ⟨16345335143765735751258263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10896890095843823834172175 16345335143765735751258263)
          ·
            refine ⟨24518002715648603626887395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16345335143765735751258263 24518002715648603626887395)
            ·
              refine ⟨36777004073472905440331093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24518002715648603626887395 36777004073472905440331093)
              ·
                refine ⟨26936282280375663164305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 36777004073472905440331093 26936282280375663164305)
                ·
                  rfl

theorem cell22_708186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 12].length) (baseStart_708186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_708186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_708186 prefixEnd_708186 := by exact prefixLift 708186
  have htrace : WordTrace (prefixWord ++ tailWord_708186) baseStart_708186 baseEnd_708186 := by
    simpa [prefixWord, tailWord_708186, baseEnd_708186] using wordTrace_append hprefix tailTrace_708186
  have hstable : (prefixWord ++ tailWord_708186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708186).length < 2 ^ (prefixWord ++ tailWord_708186).sum := by decide
  have hdescent : baseEnd_708186 < baseStart_708186 := by decide
  rcases family_descends (prefixWord ++ tailWord_708186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708248 : List Nat := [2, 1, 2, 4, 1, 2, 1, 2, 7]
def baseStart_708248 : Nat := 118140960795 + 708248 * 2 ^ 59
def prefixEnd_708248 : Nat := 4983230072969 + 3 ^ 40 * 708248 * 2
def baseEnd_708248 : Nat := 80815921463477824476185

theorem tailTrace_708248 : CollatzResearch.WordTrace tailWord_708248 prefixEnd_708248 80815921463477824476185 := by
  unfold tailWord_708248
  simp only [CollatzResearch.WordTrace]
  refine ⟨12915963369072964986730699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17221284492097286648974265 12915963369072964986730699)
  ·
    refine ⟨19373945053609447480096049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12915963369072964986730699 19373945053609447480096049)
    ·
      refine ⟨14530458790207085610072037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19373945053609447480096049 14530458790207085610072037)
      ·
        refine ⟨2724461023163828551888507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14530458790207085610072037 2724461023163828551888507)
        ·
          refine ⟨4086691534745742827832761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2724461023163828551888507 4086691534745742827832761)
          ·
            refine ⟨3065018651059307120874571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4086691534745742827832761 3065018651059307120874571)
            ·
              refine ⟨4597527976588960681311857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3065018651059307120874571 4597527976588960681311857)
              ·
                refine ⟨3448145982441720510983893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4597527976588960681311857 3448145982441720510983893)
                ·
                  refine ⟨80815921463477824476185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3448145982441720510983893 80815921463477824476185)
                  ·
                    rfl

theorem cell22_708248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 2, 7].length) (baseStart_708248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_708248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_708248 prefixEnd_708248 := by exact prefixLift 708248
  have htrace : WordTrace (prefixWord ++ tailWord_708248) baseStart_708248 baseEnd_708248 := by
    simpa [prefixWord, tailWord_708248, baseEnd_708248] using wordTrace_append hprefix tailTrace_708248
  have hstable : (prefixWord ++ tailWord_708248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708248).length < 2 ^ (prefixWord ++ tailWord_708248).sum := by decide
  have hdescent : baseEnd_708248 < baseStart_708248 := by decide
  rcases family_descends (prefixWord ++ tailWord_708248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708282 : List Nat := [3, 1, 1, 1, 2, 6, 2, 1, 5]
def baseStart_708282 : Nat := 118140960795 + 708282 * 2 ^ 59
def prefixEnd_708282 : Nat := 4983230072969 + 3 ^ 40 * 708282 * 2
def baseEnd_708282 : Nat := 80819801095089572692817

theorem tailTrace_708282 : CollatzResearch.WordTrace tailWord_708282 prefixEnd_708282 80819801095089572692817 := by
  unfold tailWord_708282
  simp only [CollatzResearch.WordTrace]
  refine ⟨6458291705005688445049775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17222111213348502520132733 6458291705005688445049775)
  ·
    refine ⟨9687437557508532667574663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6458291705005688445049775 9687437557508532667574663)
    ·
      refine ⟨14531156336262799001361995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9687437557508532667574663 14531156336262799001361995)
      ·
        refine ⟨21796734504394198502042993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14531156336262799001361995 21796734504394198502042993)
        ·
          refine ⟨16347550878295648876532245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21796734504394198502042993 16347550878295648876532245)
          ·
            refine ⟨766291447420108541087449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 16347550878295648876532245 766291447420108541087449)
            ·
              refine ⟨574718585565081405815587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 766291447420108541087449 574718585565081405815587)
              ·
                refine ⟨862077878347622108723381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 574718585565081405815587 862077878347622108723381)
                ·
                  refine ⟨80819801095089572692817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 862077878347622108723381 80819801095089572692817)
                  ·
                    rfl

theorem cell22_708282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 2, 1, 5].length) (baseStart_708282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_708282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_708282 prefixEnd_708282 := by exact prefixLift 708282
  have htrace : WordTrace (prefixWord ++ tailWord_708282) baseStart_708282 baseEnd_708282 := by
    simpa [prefixWord, tailWord_708282, baseEnd_708282] using wordTrace_append hprefix tailTrace_708282
  have hstable : (prefixWord ++ tailWord_708282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708282).length < 2 ^ (prefixWord ++ tailWord_708282).sum := by decide
  have hdescent : baseEnd_708282 < baseStart_708282 := by decide
  rcases family_descends (prefixWord ++ tailWord_708282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708312 : List Nat := [2, 1, 2, 2, 3, 1, 5, 1, 1, 4]
def baseStart_708312 : Nat := 118140960795 + 708312 * 2 ^ 59
def prefixEnd_708312 : Nat := 4983230072969 + 3 ^ 40 * 708312 * 2
def baseEnd_708312 : Nat := 242469672898358639828359

theorem tailTrace_708312 : CollatzResearch.WordTrace tailWord_708312 prefixEnd_708312 242469672898358639828359 := by
  unfold tailWord_708312
  simp only [CollatzResearch.WordTrace]
  refine ⟨12917130504957034451895595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17222840673276045935860793 12917130504957034451895595)
  ·
    refine ⟨19375695757435551677843393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12917130504957034451895595 19375695757435551677843393)
    ·
      refine ⟨14531771818076663758382545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19375695757435551677843393 14531771818076663758382545)
      ·
        refine ⟨10898828863557497818786909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14531771818076663758382545 10898828863557497818786909)
        ·
          refine ⟨4087060823834061682045091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10898828863557497818786909 4087060823834061682045091)
          ·
            refine ⟨6130591235751092523067637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4087060823834061682045091 6130591235751092523067637)
            ·
              refine ⟨574742928351664924037591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6130591235751092523067637 574742928351664924037591)
              ·
                refine ⟨862114392527497386056387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 574742928351664924037591 862114392527497386056387)
                ·
                  refine ⟨1293171588791246079084581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 862114392527497386056387 1293171588791246079084581)
                  ·
                    refine ⟨242469672898358639828359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1293171588791246079084581 242469672898358639828359)
                    ·
                      rfl

theorem cell22_708312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 5, 1, 1, 4].length) (baseStart_708312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_708312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_708312 prefixEnd_708312 := by exact prefixLift 708312
  have htrace : WordTrace (prefixWord ++ tailWord_708312) baseStart_708312 baseEnd_708312 := by
    simpa [prefixWord, tailWord_708312, baseEnd_708312] using wordTrace_append hprefix tailTrace_708312
  have hstable : (prefixWord ++ tailWord_708312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708312).length < 2 ^ (prefixWord ++ tailWord_708312).sum := by decide
  have hdescent : baseEnd_708312 < baseStart_708312 := by decide
  rcases family_descends (prefixWord ++ tailWord_708312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708342 : List Nat := [5, 1, 1, 1, 1, 4, 2, 1, 1, 5]
def baseStart_708342 : Nat := 118140960795 + 708342 * 2 ^ 59
def prefixEnd_708342 : Nat := 4983230072969 + 3 ^ 40 * 708342 * 2
def baseEnd_708342 : Nat := 242479942511448561578267

theorem tailTrace_708342 : CollatzResearch.WordTrace tailWord_708342 prefixEnd_708342 242479942511448561578267 := by
  unfold tailWord_708342
  simp only [CollatzResearch.WordTrace]
  refine ⟨1614709699987836501711455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17223570133203589351588853 1614709699987836501711455)
  ·
    refine ⟨2422064549981754752567183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1614709699987836501711455 2422064549981754752567183)
    ·
      refine ⟨3633096824972632128850775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2422064549981754752567183 3633096824972632128850775)
      ·
        refine ⟨5449645237458948193276163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3633096824972632128850775 5449645237458948193276163)
        ·
          refine ⟨8174467856188422289914245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5449645237458948193276163 8174467856188422289914245)
          ·
            refine ⟨1532712723035329179358921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8174467856188422289914245 1532712723035329179358921)
            ·
              refine ⟨1149534542276496884519191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1532712723035329179358921 1149534542276496884519191)
              ·
                refine ⟨1724301813414745326778787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1149534542276496884519191 1724301813414745326778787)
                ·
                  refine ⟨2586452720122117990168181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1724301813414745326778787 2586452720122117990168181)
                  ·
                    refine ⟨242479942511448561578267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2586452720122117990168181 242479942511448561578267)
                    ·
                      rfl

theorem cell22_708342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 2, 1, 1, 5].length) (baseStart_708342 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_708342 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_708342 prefixEnd_708342 := by exact prefixLift 708342
  have htrace : WordTrace (prefixWord ++ tailWord_708342) baseStart_708342 baseEnd_708342 := by
    simpa [prefixWord, tailWord_708342, baseEnd_708342] using wordTrace_append hprefix tailTrace_708342
  have hstable : (prefixWord ++ tailWord_708342).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708342).length < 2 ^ (prefixWord ++ tailWord_708342).sum := by decide
  have hdescent : baseEnd_708342 < baseStart_708342 := by decide
  rcases family_descends (prefixWord ++ tailWord_708342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708404 : List Nat := [2, 5, 1, 1, 2, 1, 2, 2, 3, 3]
def baseStart_708404 : Nat := 118140960795 + 708404 * 2 ^ 59
def prefixEnd_708404 : Nat := 4983230072969 + 3 ^ 40 * 708404 * 2
def baseEnd_708404 : Nat := 242501166378501066528077

theorem tailTrace_708404 : CollatzResearch.WordTrace tailWord_708404 prefixEnd_708404 242501166378501066528077 := by
  unfold tailWord_708404
  simp only [CollatzResearch.WordTrace]
  refine ⟨12918808262790384308070133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17225077683720512410760177 12918808262790384308070133)
  ·
    refine ⟨1211138274636598528881575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12918808262790384308070133 1211138274636598528881575)
    ·
      refine ⟨1816707411954897793322363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1211138274636598528881575 1816707411954897793322363)
      ·
        refine ⟨2725061117932346689983545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1816707411954897793322363 2725061117932346689983545)
        ·
          refine ⟨2043795838449260017487659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2725061117932346689983545 2043795838449260017487659)
          ·
            refine ⟨3065693757673890026231489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2043795838449260017487659 3065693757673890026231489)
            ·
              refine ⟨2299270318255417519673617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3065693757673890026231489 2299270318255417519673617)
              ·
                refine ⟨1724452738691563139755213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2299270318255417519673617 1724452738691563139755213)
                ·
                  refine ⟨646669777009336177408205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1724452738691563139755213 646669777009336177408205)
                  ·
                    refine ⟨242501166378501066528077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 646669777009336177408205 242501166378501066528077)
                    ·
                      rfl

theorem cell22_708404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 2, 3, 3].length) (baseStart_708404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_708404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_708404 prefixEnd_708404 := by exact prefixLift 708404
  have htrace : WordTrace (prefixWord ++ tailWord_708404) baseStart_708404 baseEnd_708404 := by
    simpa [prefixWord, tailWord_708404, baseEnd_708404] using wordTrace_append hprefix tailTrace_708404
  have hstable : (prefixWord ++ tailWord_708404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708404).length < 2 ^ (prefixWord ++ tailWord_708404).sum := by decide
  have hdescent : baseEnd_708404 < baseStart_708404 := by decide
  rcases family_descends (prefixWord ++ tailWord_708404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708430 : List Nat := [4, 1, 1, 1, 1, 1, 1, 1, 7, 4]
def baseStart_708430 : Nat := 118140960795 + 708430 * 2 ^ 59
def prefixEnd_708430 : Nat := 4983230072969 + 3 ^ 40 * 708430 * 2
def baseEnd_708430 : Nat := 242510066709845665377997

theorem tailTrace_708430 : CollatzResearch.WordTrace tailWord_708430 prefixEnd_708430 242510066709845665377997 := by
  unfold tailWord_708430
  simp only [CollatzResearch.WordTrace]
  refine ⟨3229820602935821882073343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17225709882324383371057829 3229820602935821882073343)
  ·
    refine ⟨4844730904403732823110015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3229820602935821882073343 4844730904403732823110015)
    ·
      refine ⟨7267096356605599234665023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4844730904403732823110015 7267096356605599234665023)
      ·
        refine ⟨10900644534908398851997535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7267096356605599234665023 10900644534908398851997535)
        ·
          refine ⟨16350966802362598277996303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10900644534908398851997535 16350966802362598277996303)
          ·
            refine ⟨24526450203543897416994455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16350966802362598277996303 24526450203543897416994455)
            ·
              refine ⟨36789675305315846125491683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24526450203543897416994455 36789675305315846125491683)
              ·
                refine ⟨55184512957973769188237525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36789675305315846125491683 55184512957973769188237525)
                ·
                  refine ⟨1293387022452510215349317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 55184512957973769188237525 1293387022452510215349317)
                  ·
                    refine ⟨242510066709845665377997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1293387022452510215349317 242510066709845665377997)
                    ·
                      rfl

theorem cell22_708430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 7, 4].length) (baseStart_708430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_708430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_708430 prefixEnd_708430 := by exact prefixLift 708430
  have htrace : WordTrace (prefixWord ++ tailWord_708430) baseStart_708430 baseEnd_708430 := by
    simpa [prefixWord, tailWord_708430, baseEnd_708430] using wordTrace_append hprefix tailTrace_708430
  have hstable : (prefixWord ++ tailWord_708430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708430).length < 2 ^ (prefixWord ++ tailWord_708430).sum := by decide
  have hdescent : baseEnd_708430 < baseStart_708430 := by decide
  rcases family_descends (prefixWord ++ tailWord_708430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708451 : List Nat := [1, 1, 1, 5, 5, 1, 2, 1, 5]
def baseStart_708451 : Nat := 118140960795 + 708451 * 2 ^ 59
def prefixEnd_708451 : Nat := 4983230072969 + 3 ^ 40 * 708451 * 2
def baseEnd_708451 : Nat := 80839085146336203534311

theorem tailTrace_708451 : CollatzResearch.WordTrace tailWord_708451 prefixEnd_708451 80839085146336203534311 := by
  unfold tailWord_708451
  simp only [CollatzResearch.WordTrace]
  refine ⟨25839330756410495643101207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17226220504273663762067471 25839330756410495643101207)
  ·
    refine ⟨38758996134615743464651811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25839330756410495643101207 38758996134615743464651811)
    ·
      refine ⟨58138494201923615196977717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38758996134615743464651811 58138494201923615196977717)
      ·
        refine ⟨5450483831430338924716661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 58138494201923615196977717 5450483831430338924716661)
        ·
          refine ⟨510982859196594274192187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5450483831430338924716661 510982859196594274192187)
          ·
            refine ⟨766474288794891411288281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 510982859196594274192187 766474288794891411288281)
            ·
              refine ⟨574855716596168558466211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 766474288794891411288281 574855716596168558466211)
              ·
                refine ⟨862283574894252837699317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 574855716596168558466211 862283574894252837699317)
                ·
                  refine ⟨80839085146336203534311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 862283574894252837699317 80839085146336203534311)
                  ·
                    rfl

theorem cell22_708451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 2, 1, 5].length) (baseStart_708451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_708451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_708451 prefixEnd_708451 := by exact prefixLift 708451
  have htrace : WordTrace (prefixWord ++ tailWord_708451) baseStart_708451 baseEnd_708451 := by
    simpa [prefixWord, tailWord_708451, baseEnd_708451] using wordTrace_append hprefix tailTrace_708451
  have hstable : (prefixWord ++ tailWord_708451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708451).length < 2 ^ (prefixWord ++ tailWord_708451).sum := by decide
  have hdescent : baseEnd_708451 < baseStart_708451 := by decide
  rcases family_descends (prefixWord ++ tailWord_708451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708490 : List Nat := [3, 1, 2, 4, 12]
def baseStart_708490 : Nat := 118140960795 + 708490 * 2 ^ 59
def prefixEnd_708490 : Nat := 4983230072969 + 3 ^ 40 * 708490 * 2
def baseEnd_708490 : Nat := 998068337185290159991

theorem tailTrace_708490 : CollatzResearch.WordTrace tailWord_708490 prefixEnd_708490 998068337185290159991 := by
  unfold tailWord_708490
  simp only [CollatzResearch.WordTrace]
  refine ⟨6460188300817301325942731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17227168802179470202513949 6460188300817301325942731)
  ·
    refine ⟨9690282451225951988914097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6460188300817301325942731 9690282451225951988914097)
    ·
      refine ⟨7267711838419463991685573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9690282451225951988914097 7267711838419463991685573)
      ·
        refine ⟨1362695969703649498441045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7267711838419463991685573 1362695969703649498441045)
        ·
          refine ⟨998068337185290159991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 1362695969703649498441045 998068337185290159991)
          ·
            rfl

theorem cell22_708490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 12].length) (baseStart_708490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_708490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_708490 prefixEnd_708490 := by exact prefixLift 708490
  have htrace : WordTrace (prefixWord ++ tailWord_708490) baseStart_708490 baseEnd_708490 := by
    simpa [prefixWord, tailWord_708490, baseEnd_708490] using wordTrace_append hprefix tailTrace_708490
  have hstable : (prefixWord ++ tailWord_708490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708490).length < 2 ^ (prefixWord ++ tailWord_708490).sum := by decide
  have hdescent : baseEnd_708490 < baseStart_708490 := by decide
  rcases family_descends (prefixWord ++ tailWord_708490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708535 : List Nat := [1, 1, 3, 1, 3, 1, 1, 4, 7]
def baseStart_708535 : Nat := 118140960795 + 708535 * 2 ^ 59
def prefixEnd_708535 : Nat := 4983230072969 + 3 ^ 40 * 708535 * 2
def baseEnd_708535 : Nat := 80848670118553463834225

theorem tailTrace_708535 : CollatzResearch.WordTrace tailWord_708535 prefixEnd_708535 80848670118553463834225 := by
  unfold tailWord_708535
  simp only [CollatzResearch.WordTrace]
  refine ⟨25842394488106177989159059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17228262992070785326106039 25842394488106177989159059)
  ·
    refine ⟨38763591732159266983738589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25842394488106177989159059 38763591732159266983738589)
    ·
      refine ⟨14536346899559725118901971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38763591732159266983738589 14536346899559725118901971)
      ·
        refine ⟨21804520349339587678352957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14536346899559725118901971 21804520349339587678352957)
        ·
          refine ⟨8176695131002345379382359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21804520349339587678352957 8176695131002345379382359)
          ·
            refine ⟨12265042696503518069073539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8176695131002345379382359 12265042696503518069073539)
            ·
              refine ⟨18397564044755277103610309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12265042696503518069073539 18397564044755277103610309)
              ·
                refine ⟨3449543258391614456926933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18397564044755277103610309 3449543258391614456926933)
                ·
                  refine ⟨80848670118553463834225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3449543258391614456926933 80848670118553463834225)
                  ·
                    rfl

theorem cell22_708535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 4, 7].length) (baseStart_708535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_708535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_708535 prefixEnd_708535 := by exact prefixLift 708535
  have htrace : WordTrace (prefixWord ++ tailWord_708535) baseStart_708535 baseEnd_708535 := by
    simpa [prefixWord, tailWord_708535, baseEnd_708535] using wordTrace_append hprefix tailTrace_708535
  have hstable : (prefixWord ++ tailWord_708535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708535).length < 2 ^ (prefixWord ++ tailWord_708535).sum := by decide
  have hdescent : baseEnd_708535 < baseStart_708535 := by decide
  rcases family_descends (prefixWord ++ tailWord_708535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708539 : List Nat := [1, 1, 1, 1, 1, 2, 2, 9, 1, 3]
def baseStart_708539 : Nat := 118140960795 + 708539 * 2 ^ 59
def prefixEnd_708539 : Nat := 4983230072969 + 3 ^ 40 * 708539 * 2
def baseEnd_708539 : Nat := 242547379637405714402663

theorem tailTrace_708539 : CollatzResearch.WordTrace tailWord_708539 prefixEnd_708539 242547379637405714402663 := by
  unfold tailWord_708539
  simp only [CollatzResearch.WordTrace]
  refine ⟨25842540380091686672304671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17228360253394457781536447 25842540380091686672304671)
  ·
    refine ⟨38763810570137530008457007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25842540380091686672304671 38763810570137530008457007)
    ·
      refine ⟨58145715855206295012685511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38763810570137530008457007 58145715855206295012685511)
      ·
        refine ⟨87218573782809442519028267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58145715855206295012685511 87218573782809442519028267)
        ·
          refine ⟨130827860674214163778542401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87218573782809442519028267 130827860674214163778542401)
          ·
            refine ⟨98120895505660622833906801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130827860674214163778542401 98120895505660622833906801)
            ·
              refine ⟨73590671629245467125430101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98120895505660622833906801 73590671629245467125430101)
              ·
                refine ⟨431195341577610158938067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 73590671629245467125430101 431195341577610158938067)
                ·
                  refine ⟨646793012366415238407101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 431195341577610158938067 646793012366415238407101)
                  ·
                    refine ⟨242547379637405714402663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 646793012366415238407101 242547379637405714402663)
                    ·
                      rfl

theorem cell22_708539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 9, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 9, 1, 3].length) (baseStart_708539 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_708539 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_708539 prefixEnd_708539 := by exact prefixLift 708539
  have htrace : WordTrace (prefixWord ++ tailWord_708539) baseStart_708539 baseEnd_708539 := by
    simpa [prefixWord, tailWord_708539, baseEnd_708539] using wordTrace_append hprefix tailTrace_708539
  have hstable : (prefixWord ++ tailWord_708539).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708539).length < 2 ^ (prefixWord ++ tailWord_708539).sum := by decide
  have hdescent : baseEnd_708539 < baseStart_708539 := by decide
  rcases family_descends (prefixWord ++ tailWord_708539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708552 : List Nat := [2, 1, 3, 1, 4, 2, 1, 1, 7]
def baseStart_708552 : Nat := 118140960795 + 708552 * 2 ^ 59
def prefixEnd_708552 : Nat := 4983230072969 + 3 ^ 40 * 708552 * 2
def baseEnd_708552 : Nat := 80850609934359337942541

theorem tailTrace_708552 : CollatzResearch.WordTrace tailWord_708552 prefixEnd_708552 80850609934359337942541 := by
  unfold tailWord_708552
  simp only [CollatzResearch.WordTrace]
  refine ⟨12921507264522294946263955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17228676352696393261685273 12921507264522294946263955)
  ·
    refine ⟨19382260896783442419395933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12921507264522294946263955 19382260896783442419395933)
    ·
      refine ⟨7268347836293790907273475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19382260896783442419395933 7268347836293790907273475)
      ·
        refine ⟨10902521754440686360910213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7268347836293790907273475 10902521754440686360910213)
        ·
          refine ⟨2044222828957628692670665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10902521754440686360910213 2044222828957628692670665)
          ·
            refine ⟨1533167121718221519502999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2044222828957628692670665 1533167121718221519502999)
            ·
              refine ⟨2299750682577332279254499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1533167121718221519502999 2299750682577332279254499)
              ·
                refine ⟨3449626023865998418881749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2299750682577332279254499 3449626023865998418881749)
                ·
                  refine ⟨80850609934359337942541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3449626023865998418881749 80850609934359337942541)
                  ·
                    rfl

theorem cell22_708552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 1, 7].length) (baseStart_708552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_708552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_708552 prefixEnd_708552 := by exact prefixLift 708552
  have htrace : WordTrace (prefixWord ++ tailWord_708552) baseStart_708552 baseEnd_708552 := by
    simpa [prefixWord, tailWord_708552, baseEnd_708552] using wordTrace_append hprefix tailTrace_708552
  have hstable : (prefixWord ++ tailWord_708552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708552).length < 2 ^ (prefixWord ++ tailWord_708552).sum := by decide
  have hdescent : baseEnd_708552 < baseStart_708552 := by decide
  rcases family_descends (prefixWord ++ tailWord_708552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708556 : List Nat := [2, 2, 1, 4, 1, 2, 2, 4, 1, 3]
def baseStart_708556 : Nat := 118140960795 + 708556 * 2 ^ 59
def prefixEnd_708556 : Nat := 4983230072969 + 3 ^ 40 * 708556 * 2
def baseEnd_708556 : Nat := 242553199084823336727611

theorem tailTrace_708556 : CollatzResearch.WordTrace tailWord_708556 prefixEnd_708556 242553199084823336727611 := by
  unfold tailWord_708556
  simp only [CollatzResearch.WordTrace]
  refine ⟨12921580210515049287836761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17228773614020065717115681 12921580210515049287836761)
  ·
    refine ⟨9691185157886286965877571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12921580210515049287836761 9691185157886286965877571)
    ·
      refine ⟨14536777736829430448816357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9691185157886286965877571 14536777736829430448816357)
      ·
        refine ⟨2725645825655518209153067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14536777736829430448816357 2725645825655518209153067)
        ·
          refine ⟨4088468738483277313729601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2725645825655518209153067 4088468738483277313729601)
          ·
            refine ⟨3066351553862457985297201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4088468738483277313729601 3066351553862457985297201)
            ·
              refine ⟨2299763665396843488972901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3066351553862457985297201 2299763665396843488972901)
              ·
                refine ⟨431205687261908154182419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2299763665396843488972901 431205687261908154182419)
                ·
                  refine ⟨646808530892862231273629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 431205687261908154182419 646808530892862231273629)
                  ·
                    refine ⟨242553199084823336727611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 646808530892862231273629 242553199084823336727611)
                    ·
                      rfl

theorem cell22_708556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 4, 1, 3].length) (baseStart_708556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_708556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_708556 prefixEnd_708556 := by exact prefixLift 708556
  have htrace : WordTrace (prefixWord ++ tailWord_708556) baseStart_708556 baseEnd_708556 := by
    simpa [prefixWord, tailWord_708556, baseEnd_708556] using wordTrace_append hprefix tailTrace_708556
  have hstable : (prefixWord ++ tailWord_708556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708556).length < 2 ^ (prefixWord ++ tailWord_708556).sum := by decide
  have hdescent : baseEnd_708556 < baseStart_708556 := by decide
  rcases family_descends (prefixWord ++ tailWord_708556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708642 : List Nat := [3, 3, 1, 1, 1, 2, 1, 10]
def baseStart_708642 : Nat := 118140960795 + 708642 * 2 ^ 59
def prefixEnd_708642 : Nat := 4983230072969 + 3 ^ 40 * 708642 * 2
def baseEnd_708642 : Nat := 26953626515816419897483

theorem tailTrace_708642 : CollatzResearch.WordTrace tailWord_708642 prefixEnd_708642 26953626515816419897483 := by
  unfold tailWord_708642
  simp only [CollatzResearch.WordTrace]
  refine ⟨6461574274679633815826045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17230864732479023508869453 6461574274679633815826045)
  ·
    refine ⟨2423090353004862680934767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6461574274679633815826045 2423090353004862680934767)
    ·
      refine ⟨3634635529507294021402151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2423090353004862680934767 3634635529507294021402151)
      ·
        refine ⟨5451953294260941032103227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3634635529507294021402151 5451953294260941032103227)
        ·
          refine ⟨8177929941391411548154841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5451953294260941032103227 8177929941391411548154841)
          ·
            refine ⟨6133447456043558661116131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8177929941391411548154841 6133447456043558661116131)
            ·
              refine ⟨9200171184065337991674197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6133447456043558661116131 9200171184065337991674197)
              ·
                refine ⟨26953626515816419897483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 9200171184065337991674197 26953626515816419897483)
                ·
                  rfl

theorem cell22_708642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 10].length) (baseStart_708642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_708642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_708642 prefixEnd_708642 := by exact prefixLift 708642
  have htrace : WordTrace (prefixWord ++ tailWord_708642) baseStart_708642 baseEnd_708642 := by
    simpa [prefixWord, tailWord_708642, baseEnd_708642] using wordTrace_append hprefix tailTrace_708642
  have hstable : (prefixWord ++ tailWord_708642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708642).length < 2 ^ (prefixWord ++ tailWord_708642).sum := by decide
  have hdescent : baseEnd_708642 < baseStart_708642 := by decide
  rcases family_descends (prefixWord ++ tailWord_708642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708665 : List Nat := [1, 2, 1, 5, 4, 1, 2, 2, 4]
def baseStart_708665 : Nat := 118140960795 + 708665 * 2 ^ 59
def prefixEnd_708665 : Nat := 4983230072969 + 3 ^ 40 * 708665 * 2
def baseEnd_708665 : Nat := 80863504004127795250759

theorem tailTrace_708665 : CollatzResearch.WordTrace tailWord_708665 prefixEnd_708665 80863504004127795250759 := by
  unfold tailWord_708665
  simp only [CollatzResearch.WordTrace]
  refine ⟨25847135977635210191391449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17231423985090140127594299 25847135977635210191391449)
  ·
    refine ⟨19385351983226407643543587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25847135977635210191391449 19385351983226407643543587)
    ·
      refine ⟨29078027974839611465315381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19385351983226407643543587 29078027974839611465315381)
      ·
        refine ⟨2726065122641213574873317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29078027974839611465315381 2726065122641213574873317)
        ·
          refine ⟨511137210495227545288747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2726065122641213574873317 511137210495227545288747)
          ·
            refine ⟨766705815742841317933121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 511137210495227545288747 766705815742841317933121)
            ·
              refine ⟨575029361807130988449841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 766705815742841317933121 575029361807130988449841)
              ·
                refine ⟨431272021355348241337381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 575029361807130988449841 431272021355348241337381)
                ·
                  refine ⟨80863504004127795250759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 431272021355348241337381 80863504004127795250759)
                  ·
                    rfl

theorem cell22_708665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 2, 2, 4].length) (baseStart_708665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_708665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_708665 prefixEnd_708665 := by exact prefixLift 708665
  have htrace : WordTrace (prefixWord ++ tailWord_708665) baseStart_708665 baseEnd_708665 := by
    simpa [prefixWord, tailWord_708665, baseEnd_708665] using wordTrace_append hprefix tailTrace_708665
  have hstable : (prefixWord ++ tailWord_708665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708665).length < 2 ^ (prefixWord ++ tailWord_708665).sum := by decide
  have hdescent : baseEnd_708665 < baseStart_708665 := by decide
  rcases family_descends (prefixWord ++ tailWord_708665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708672 : List Nat := [2, 1, 1, 2, 2, 4, 1, 1, 2, 6]
def baseStart_708672 : Nat := 118140960795 + 708672 * 2 ^ 59
def prefixEnd_708672 : Nat := 4983230072969 + 3 ^ 40 * 708672 * 2
def baseEnd_708672 : Nat := 242592908255437700827255

theorem tailTrace_708672 : CollatzResearch.WordTrace tailWord_708672 prefixEnd_708672 242592908255437700827255 := by
  unfold tailWord_708672
  simp only [CollatzResearch.WordTrace]
  refine ⟨12923695644304925193448135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17231594192406566924597513 12923695644304925193448135)
  ·
    refine ⟨19385543466457387790172203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12923695644304925193448135 19385543466457387790172203)
    ·
      refine ⟨29078315199686081685258305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19385543466457387790172203 29078315199686081685258305)
      ·
        refine ⟨21808736399764561263943729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29078315199686081685258305 21808736399764561263943729)
        ·
          refine ⟨16356552299823420947957797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21808736399764561263943729 16356552299823420947957797)
          ·
            refine ⟨3066853556216891427742087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16356552299823420947957797 3066853556216891427742087)
            ·
              refine ⟨4600280334325337141613131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3066853556216891427742087 4600280334325337141613131)
              ·
                refine ⟨6900420501488005712419697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4600280334325337141613131 6900420501488005712419697)
                ·
                  refine ⟨5175315376116004284314773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6900420501488005712419697 5175315376116004284314773)
                  ·
                    refine ⟨242592908255437700827255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5175315376116004284314773 242592908255437700827255)
                    ·
                      rfl

theorem cell22_708672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 1, 2, 6].length) (baseStart_708672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_708672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_708672 prefixEnd_708672 := by exact prefixLift 708672
  have htrace : WordTrace (prefixWord ++ tailWord_708672) baseStart_708672 baseEnd_708672 := by
    simpa [prefixWord, tailWord_708672, baseEnd_708672] using wordTrace_append hprefix tailTrace_708672
  have hstable : (prefixWord ++ tailWord_708672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708672).length < 2 ^ (prefixWord ++ tailWord_708672).sum := by decide
  have hdescent : baseEnd_708672 < baseStart_708672 := by decide
  rcases family_descends (prefixWord ++ tailWord_708672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708764 : List Nat := [2, 2, 3, 2, 1, 1, 2, 1, 3, 5]
def baseStart_708764 : Nat := 118140960795 + 708764 * 2 ^ 59
def prefixEnd_708764 : Nat := 4983230072969 + 3 ^ 40 * 708764 * 2
def baseEnd_708764 : Nat := 242624401735580127526973

theorem tailTrace_708764 : CollatzResearch.WordTrace tailWord_708764 prefixEnd_708764 242624401735580127526973 := by
  unfold tailWord_708764
  simp only [CollatzResearch.WordTrace]
  refine ⟨12925373402138275049622673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17233831202851033399496897 12925373402138275049622673)
  ·
    refine ⟨9694030051603706287217005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12925373402138275049622673 9694030051603706287217005)
    ·
      refine ⟨3635261269351389857706377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9694030051603706287217005 3635261269351389857706377)
      ·
        refine ⟨2726445952013542393279783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3635261269351389857706377 2726445952013542393279783)
        ·
          refine ⟨4089668928020313589919675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2726445952013542393279783 4089668928020313589919675)
          ·
            refine ⟨6134503392030470384879513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4089668928020313589919675 6134503392030470384879513)
            ·
              refine ⟨4600877544022852788659635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6134503392030470384879513 4600877544022852788659635)
              ·
                refine ⟨6901316316034279182989453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4600877544022852788659635 6901316316034279182989453)
                ·
                  refine ⟨2587993618512854693621045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6901316316034279182989453 2587993618512854693621045)
                  ·
                    refine ⟨242624401735580127526973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2587993618512854693621045 242624401735580127526973)
                    ·
                      rfl

theorem cell22_708764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 1, 3, 5].length) (baseStart_708764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_708764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_708764 prefixEnd_708764 := by exact prefixLift 708764
  have htrace : WordTrace (prefixWord ++ tailWord_708764) baseStart_708764 baseEnd_708764 := by
    simpa [prefixWord, tailWord_708764, baseEnd_708764] using wordTrace_append hprefix tailTrace_708764
  have hstable : (prefixWord ++ tailWord_708764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708764).length < 2 ^ (prefixWord ++ tailWord_708764).sum := by decide
  have hdescent : baseEnd_708764 < baseStart_708764 := by decide
  rcases family_descends (prefixWord ++ tailWord_708764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708802 : List Nat := [3, 5, 1, 1, 1, 3, 1, 2, 1, 4]
def baseStart_708802 : Nat := 118140960795 + 708802 * 2 ^ 59
def prefixEnd_708802 : Nat := 4983230072969 + 3 ^ 40 * 708802 * 2
def baseEnd_708802 : Nat := 242637409912160695076857

theorem tailTrace_708802 : CollatzResearch.WordTrace tailWord_708802 prefixEnd_708802 242637409912160695076857 := by
  unfold tailWord_708802
  simp only [CollatzResearch.WordTrace]
  refine ⟨6463033194534720647282165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17234755185425921726085773 6463033194534720647282165)
  ·
    refine ⟨605909361987630060682703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6463033194534720647282165 605909361987630060682703)
    ·
      refine ⟨908864042981445091024055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 605909361987630060682703 908864042981445091024055)
      ·
        refine ⟨1363296064472167636536083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 908864042981445091024055 1363296064472167636536083)
        ·
          refine ⟨2044944096708251454804125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1363296064472167636536083 2044944096708251454804125)
          ·
            refine ⟨766854036265594295551547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2044944096708251454804125 766854036265594295551547)
            ·
              refine ⟨1150281054398391443327321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 766854036265594295551547 1150281054398391443327321)
              ·
                refine ⟨862710790798793582495491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1150281054398391443327321 862710790798793582495491)
                ·
                  refine ⟨1294066186198190373743237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 862710790798793582495491 1294066186198190373743237)
                  ·
                    refine ⟨242637409912160695076857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1294066186198190373743237 242637409912160695076857)
                    ·
                      rfl

theorem cell22_708802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_708802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_708802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_708802 prefixEnd_708802 := by exact prefixLift 708802
  have htrace : WordTrace (prefixWord ++ tailWord_708802) baseStart_708802 baseEnd_708802 := by
    simpa [prefixWord, tailWord_708802, baseEnd_708802] using wordTrace_append hprefix tailTrace_708802
  have hstable : (prefixWord ++ tailWord_708802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708802).length < 2 ^ (prefixWord ++ tailWord_708802).sum := by decide
  have hdescent : baseEnd_708802 < baseStart_708802 := by decide
  rcases family_descends (prefixWord ++ tailWord_708802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708828 : List Nat := [2, 2, 5, 2, 2, 9]
def baseStart_708828 : Nat := 118140960795 + 708828 * 2 ^ 59
def prefixEnd_708828 : Nat := 4983230072969 + 3 ^ 40 * 708828 * 2
def baseEnd_708828 : Nat := 2995633459796361653417

theorem tailTrace_708828 : CollatzResearch.WordTrace tailWord_708828 prefixEnd_708828 2995633459796361653417 := by
  unfold tailWord_708828
  simp only [CollatzResearch.WordTrace]
  refine ⟨12926540538022344514787569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17235387384029792686383425 12926540538022344514787569)
  ·
    refine ⟨9694905403516758386090677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12926540538022344514787569 9694905403516758386090677)
    ·
      refine ⟨908897381579696098696001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9694905403516758386090677 908897381579696098696001)
      ·
        refine ⟨681673036184772074022001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 908897381579696098696001 681673036184772074022001)
        ·
          refine ⟨511254777138579055516501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 681673036184772074022001 511254777138579055516501)
          ·
            refine ⟨2995633459796361653417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 511254777138579055516501 2995633459796361653417)
            ·
              rfl

theorem cell22_708828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 9].length) (baseStart_708828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_708828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_708828 prefixEnd_708828 := by exact prefixLift 708828
  have htrace : WordTrace (prefixWord ++ tailWord_708828) baseStart_708828 baseEnd_708828 := by
    simpa [prefixWord, tailWord_708828, baseEnd_708828] using wordTrace_append hprefix tailTrace_708828
  have hstable : (prefixWord ++ tailWord_708828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708828).length < 2 ^ (prefixWord ++ tailWord_708828).sum := by decide
  have hdescent : baseEnd_708828 < baseStart_708828 := by decide
  rcases family_descends (prefixWord ++ tailWord_708828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708843 : List Nat := [1, 1, 1, 1, 2, 5, 3, 4, 1, 3]
def baseStart_708843 : Nat := 118140960795 + 708843 * 2 ^ 59
def prefixEnd_708843 : Nat := 4983230072969 + 3 ^ 40 * 708843 * 2
def baseEnd_708843 : Nat := 242651445050050254801731

theorem tailTrace_708843 : CollatzResearch.WordTrace tailWord_708843 prefixEnd_708843 242651445050050254801731 := by
  unfold tailWord_708843
  simp only [CollatzResearch.WordTrace]
  refine ⟨25853628170990346591371183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17235752113993564394247455 25853628170990346591371183)
  ·
    refine ⟨38780442256485519887056775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25853628170990346591371183 38780442256485519887056775)
    ·
      refine ⟨58170663384728279830585163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38780442256485519887056775 58170663384728279830585163)
      ·
        refine ⟨87255995077092419745877745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58170663384728279830585163 87255995077092419745877745)
        ·
          refine ⟨65441996307819314809408309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87255995077092419745877745 65441996307819314809408309)
          ·
            refine ⟨6135187153858060763382029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 65441996307819314809408309 6135187153858060763382029)
            ·
              refine ⟨2300695182696772786268261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6135187153858060763382029 2300695182696772786268261)
              ·
                refine ⟨431380346755644897425299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2300695182696772786268261 431380346755644897425299)
                ·
                  refine ⟨647070520133467346137949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 431380346755644897425299 647070520133467346137949)
                  ·
                    refine ⟨242651445050050254801731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 647070520133467346137949 242651445050050254801731)
                    ·
                      rfl

theorem cell22_708843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 4, 1, 3].length) (baseStart_708843 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_708843 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_708843 prefixEnd_708843 := by exact prefixLift 708843
  have htrace : WordTrace (prefixWord ++ tailWord_708843) baseStart_708843 baseEnd_708843 := by
    simpa [prefixWord, tailWord_708843, baseEnd_708843] using wordTrace_append hprefix tailTrace_708843
  have hstable : (prefixWord ++ tailWord_708843).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708843).length < 2 ^ (prefixWord ++ tailWord_708843).sum := by decide
  have hdescent : baseEnd_708843 < baseStart_708843 := by decide
  rcases family_descends (prefixWord ++ tailWord_708843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708890 : List Nat := [3, 1, 1, 3, 5, 1, 1, 2, 5]
def baseStart_708890 : Nat := 118140960795 + 708890 * 2 ^ 59
def prefixEnd_708890 : Nat := 4983230072969 + 3 ^ 40 * 708890 * 2
def baseEnd_708890 : Nat := 80889178036852599625529

theorem tailTrace_708890 : CollatzResearch.WordTrace tailWord_708890 prefixEnd_708890 80889178036852599625529 := by
  unfold tailWord_708890
  simp only [CollatzResearch.WordTrace]
  refine ⟨6463835600455018404583031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17236894934546715745554749 6463835600455018404583031)
  ·
    refine ⟨9695753400682527606874547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6463835600455018404583031 9695753400682527606874547)
    ·
      refine ⟨14543630101023791410311821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9695753400682527606874547 14543630101023791410311821)
      ·
        refine ⟨5453861287883921778866933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14543630101023791410311821 5453861287883921778866933)
        ·
          refine ⟨511299495739117666768775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5453861287883921778866933 511299495739117666768775)
          ·
            refine ⟨766949243608676500153163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 511299495739117666768775 766949243608676500153163)
            ·
              refine ⟨1150423865413014750229745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 766949243608676500153163 1150423865413014750229745)
              ·
                refine ⟨862817899059761062672309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1150423865413014750229745 862817899059761062672309)
                ·
                  refine ⟨80889178036852599625529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 862817899059761062672309 80889178036852599625529)
                  ·
                    rfl

theorem cell22_708890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 1, 2, 5].length) (baseStart_708890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_708890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_708890 prefixEnd_708890 := by exact prefixLift 708890
  have htrace : WordTrace (prefixWord ++ tailWord_708890) baseStart_708890 baseEnd_708890 := by
    simpa [prefixWord, tailWord_708890, baseEnd_708890] using wordTrace_append hprefix tailTrace_708890
  have hstable : (prefixWord ++ tailWord_708890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708890).length < 2 ^ (prefixWord ++ tailWord_708890).sum := by decide
  have hdescent : baseEnd_708890 < baseStart_708890 := by decide
  rcases family_descends (prefixWord ++ tailWord_708890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708948 : List Nat := [2, 4, 1, 1, 2, 3, 1, 2, 2, 4]
def baseStart_708948 : Nat := 118140960795 + 708948 * 2 ^ 59
def prefixEnd_708948 : Nat := 4983230072969 + 3 ^ 40 * 708948 * 2
def baseEnd_708948 : Nat := 242687388695864980926409

theorem tailTrace_708948 : CollatzResearch.WordTrace tailWord_708948 prefixEnd_708948 242687388695864980926409 := by
  unfold tailWord_708948
  simp only [CollatzResearch.WordTrace]
  refine ⟨12928728917804974761971749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17238305223739966349295665 12928728917804974761971749)
  ·
    refine ⟨2424136672088432767869703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12928728917804974761971749 2424136672088432767869703)
    ·
      refine ⟨3636205008132649151804555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2424136672088432767869703 3636205008132649151804555)
      ·
        refine ⟨5454307512198973727706833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3636205008132649151804555 5454307512198973727706833)
        ·
          refine ⟨4090730634149230295780125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5454307512198973727706833 4090730634149230295780125)
          ·
            refine ⟨1534023987805961360917547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4090730634149230295780125 1534023987805961360917547)
            ·
              refine ⟨2301035981708942041376321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1534023987805961360917547 2301035981708942041376321)
              ·
                refine ⟨1725776986281706531032241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2301035981708942041376321 1725776986281706531032241)
                ·
                  refine ⟨1294332739711279898274181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1725776986281706531032241 1294332739711279898274181)
                  ·
                    refine ⟨242687388695864980926409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1294332739711279898274181 242687388695864980926409)
                    ·
                      rfl

theorem cell22_708948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 2, 2, 4].length) (baseStart_708948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_708948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_708948 prefixEnd_708948 := by exact prefixLift 708948
  have htrace : WordTrace (prefixWord ++ tailWord_708948) baseStart_708948 baseEnd_708948 := by
    simpa [prefixWord, tailWord_708948, baseEnd_708948] using wordTrace_append hprefix tailTrace_708948
  have hstable : (prefixWord ++ tailWord_708948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708948).length < 2 ^ (prefixWord ++ tailWord_708948).sum := by decide
  have hdescent : baseEnd_708948 < baseStart_708948 := by decide
  rcases family_descends (prefixWord ++ tailWord_708948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708958 : List Nat := [4, 4, 2, 1, 2, 1, 2, 1, 5]
def baseStart_708958 : Nat := 118140960795 + 708958 * 2 ^ 59
def prefixEnd_708958 : Nat := 4983230072969 + 3 ^ 40 * 708958 * 2
def baseEnd_708958 : Nat := 80896937300076096058793

theorem tailTrace_708958 : CollatzResearch.WordTrace tailWord_708958 prefixEnd_708958 80896937300076096058793 := by
  unfold tailWord_708958
  simp only [CollatzResearch.WordTrace]
  refine ⟨3232227820696715153975941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17238548377049147487871685 3232227820696715153975941)
  ·
    refine ⟨606042716380634091370489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3232227820696715153975941 606042716380634091370489)
    ·
      refine ⟨454532037285475568527867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 606042716380634091370489 454532037285475568527867)
      ·
        refine ⟨681798055928213352791801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 454532037285475568527867 681798055928213352791801)
        ·
          refine ⟨511348541946160014593851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 681798055928213352791801 511348541946160014593851)
          ·
            refine ⟨767022812919240021890777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 511348541946160014593851 767022812919240021890777)
            ·
              refine ⟨575267109689430016418083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 767022812919240021890777 575267109689430016418083)
              ·
                refine ⟨862900664534145024627125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 575267109689430016418083 862900664534145024627125)
                ·
                  refine ⟨80896937300076096058793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 862900664534145024627125 80896937300076096058793)
                  ·
                    rfl

theorem cell22_708958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_708958 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_708958 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_708958 prefixEnd_708958 := by exact prefixLift 708958
  have htrace : WordTrace (prefixWord ++ tailWord_708958) baseStart_708958 baseEnd_708958 := by
    simpa [prefixWord, tailWord_708958, baseEnd_708958] using wordTrace_append hprefix tailTrace_708958
  have hstable : (prefixWord ++ tailWord_708958).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708958).length < 2 ^ (prefixWord ++ tailWord_708958).sum := by decide
  have hdescent : baseEnd_708958 < baseStart_708958 := by decide
  rcases family_descends (prefixWord ++ tailWord_708958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708967 : List Nat := [1, 1, 5, 1, 3, 3, 2, 1, 2, 3]
def baseStart_708967 : Nat := 118140960795 + 708967 * 2 ^ 59
def prefixEnd_708967 : Nat := 4983230072969 + 3 ^ 40 * 708967 * 2
def baseEnd_708967 : Nat := 242693892784155264701351

theorem tailTrace_708967 : CollatzResearch.WordTrace tailWord_708967 prefixEnd_708967 242693892784155264701351 := by
  unfold tailWord_708967
  simp only [CollatzResearch.WordTrace]
  refine ⟨25858150822541115768885155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17238767215027410512590103 25858150822541115768885155)
  ·
    refine ⟨38787226233811673653327733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25858150822541115768885155 38787226233811673653327733)
    ·
      refine ⟨3636302459419844404999475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38787226233811673653327733 3636302459419844404999475)
      ·
        refine ⟨5454453689129766607499213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3636302459419844404999475 5454453689129766607499213)
        ·
          refine ⟨2045420133423662477812205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5454453689129766607499213 2045420133423662477812205)
          ·
            refine ⟨767032550033873429179577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2045420133423662477812205 767032550033873429179577)
            ·
              refine ⟨575274412525405071884683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 767032550033873429179577 575274412525405071884683)
              ·
                refine ⟨862911618788107607827025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 575274412525405071884683 862911618788107607827025)
                ·
                  refine ⟨647183714091080705870269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 862911618788107607827025 647183714091080705870269)
                  ·
                    refine ⟨242693892784155264701351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 647183714091080705870269 242693892784155264701351)
                    ·
                      rfl

theorem cell22_708967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 2, 1, 2, 3].length) (baseStart_708967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_708967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_708967 prefixEnd_708967 := by exact prefixLift 708967
  have htrace : WordTrace (prefixWord ++ tailWord_708967) baseStart_708967 baseEnd_708967 := by
    simpa [prefixWord, tailWord_708967, baseEnd_708967] using wordTrace_append hprefix tailTrace_708967
  have hstable : (prefixWord ++ tailWord_708967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708967).length < 2 ^ (prefixWord ++ tailWord_708967).sum := by decide
  have hdescent : baseEnd_708967 < baseStart_708967 := by decide
  rcases family_descends (prefixWord ++ tailWord_708967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708982 : List Nat := [5, 1, 1, 4, 1, 1, 2, 1, 2, 4]
def baseStart_708982 : Nat := 118140960795 + 708982 * 2 ^ 59
def prefixEnd_708982 : Nat := 4983230072969 + 3 ^ 40 * 708982 * 2
def baseEnd_708982 : Nat := 242699027590700225576305

theorem tailTrace_708982 : CollatzResearch.WordTrace tailWord_708982 prefixEnd_708982 242699027590700225576305 := by
  unfold tailWord_708982
  simp only [CollatzResearch.WordTrace]
  refine ⟨1616168619842923333167575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17239131944991182220454133 1616168619842923333167575)
  ·
    refine ⟨2424252929764384999751363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1616168619842923333167575 2424252929764384999751363)
    ·
      refine ⟨3636379394646577499627045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2424252929764384999751363 3636379394646577499627045)
      ·
        refine ⟨681821136496233281180071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3636379394646577499627045 681821136496233281180071)
        ·
          refine ⟨1022731704744349921770107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 681821136496233281180071 1022731704744349921770107)
          ·
            refine ⟨1534097557116524882655161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1022731704744349921770107 1534097557116524882655161)
            ·
              refine ⟨1150573167837393661991371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1534097557116524882655161 1150573167837393661991371)
              ·
                refine ⟨1725859751756090492987057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1150573167837393661991371 1725859751756090492987057)
                ·
                  refine ⟨1294394813817067869740293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1725859751756090492987057 1294394813817067869740293)
                  ·
                    refine ⟨242699027590700225576305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1294394813817067869740293 242699027590700225576305)
                    ·
                      rfl

theorem cell22_708982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 2, 1, 2, 4].length) (baseStart_708982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_708982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_708982 prefixEnd_708982 := by exact prefixLift 708982
  have htrace : WordTrace (prefixWord ++ tailWord_708982) baseStart_708982 baseEnd_708982 := by
    simpa [prefixWord, tailWord_708982, baseEnd_708982] using wordTrace_append hprefix tailTrace_708982
  have hstable : (prefixWord ++ tailWord_708982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708982).length < 2 ^ (prefixWord ++ tailWord_708982).sum := by decide
  have hdescent : baseEnd_708982 < baseStart_708982 := by decide
  rcases family_descends (prefixWord ++ tailWord_708982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709014 : List Nat := [5, 3, 1, 2, 1, 2, 1, 7]
def baseStart_709014 : Nat := 118140960795 + 709014 * 2 ^ 59
def prefixEnd_709014 : Nat := 4983230072969 + 3 ^ 40 * 709014 * 2
def baseEnd_709014 : Nat := 26967775760518089864023

theorem tailTrace_709014 : CollatzResearch.WordTrace tailWord_709014 prefixEnd_709014 26967775760518089864023 := by
  unfold tailWord_709014
  simp only [CollatzResearch.WordTrace]
  refine ⟨1616241565835677674740381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17239910035580561863897397 1616241565835677674740381)
  ·
    refine ⟨606090587188379128027643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1616241565835677674740381 606090587188379128027643)
    ·
      refine ⟨909135880782568692041465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 606090587188379128027643 909135880782568692041465)
      ·
        refine ⟨681851910586926519031099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 909135880782568692041465 681851910586926519031099)
        ·
          refine ⟨1022777865880389778546649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 681851910586926519031099 1022777865880389778546649)
          ·
            refine ⟨767083399410292333909987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1022777865880389778546649 767083399410292333909987)
            ·
              refine ⟨1150625099115438500864981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 767083399410292333909987 1150625099115438500864981)
              ·
                refine ⟨26967775760518089864023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1150625099115438500864981 26967775760518089864023)
                ·
                  rfl

theorem cell22_709014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 1, 7].length) (baseStart_709014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_709014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_709014 prefixEnd_709014 := by exact prefixLift 709014
  have htrace : WordTrace (prefixWord ++ tailWord_709014) baseStart_709014 baseEnd_709014 := by
    simpa [prefixWord, tailWord_709014, baseEnd_709014] using wordTrace_append hprefix tailTrace_709014
  have hstable : (prefixWord ++ tailWord_709014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709014).length < 2 ^ (prefixWord ++ tailWord_709014).sum := by decide
  have hdescent : baseEnd_709014 < baseStart_709014 := by decide
  rcases family_descends (prefixWord ++ tailWord_709014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709081 : List Nat := [1, 2, 1, 2, 4, 1, 2, 9]
def baseStart_709081 : Nat := 118140960795 + 709081 * 2 ^ 59
def prefixEnd_709081 : Nat := 4983230072969 + 3 ^ 40 * 709081 * 2
def baseEnd_709081 : Nat := 26970324145988551927889

theorem tailTrace_709081 : CollatzResearch.WordTrace tailWord_709081 prefixEnd_709081 26970324145988551927889 := by
  unfold tailWord_709081
  simp only [CollatzResearch.WordTrace]
  refine ⟨25862308744128113238535097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17241539162752075492356731 25862308744128113238535097)
  ·
    refine ⟨19396731558096084928901323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25862308744128113238535097 19396731558096084928901323)
    ·
      refine ⟨29095097337144127393351985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19396731558096084928901323 29095097337144127393351985)
      ·
        refine ⟨21821323002858095545013989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29095097337144127393351985 21821323002858095545013989)
        ·
          refine ⟨4091498063035892914690123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21821323002858095545013989 4091498063035892914690123)
          ·
            refine ⟨6137247094553839372035185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4091498063035892914690123 6137247094553839372035185)
            ·
              refine ⟨4602935320915379529026389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6137247094553839372035185 4602935320915379529026389)
              ·
                refine ⟨26970324145988551927889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4602935320915379529026389 26970324145988551927889)
                ·
                  rfl

theorem cell22_709081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 9].length) (baseStart_709081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_709081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_709081 prefixEnd_709081 := by exact prefixLift 709081
  have htrace : WordTrace (prefixWord ++ tailWord_709081) baseStart_709081 baseEnd_709081 := by
    simpa [prefixWord, tailWord_709081, baseEnd_709081] using wordTrace_append hprefix tailTrace_709081
  have hstable : (prefixWord ++ tailWord_709081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709081).length < 2 ^ (prefixWord ++ tailWord_709081).sum := by decide
  have hdescent : baseEnd_709081 < baseStart_709081 := by decide
  rcases family_descends (prefixWord ++ tailWord_709081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709098 : List Nat := [3, 1, 3, 1, 3, 2, 1, 8]
def baseStart_709098 : Nat := 118140960795 + 709098 * 2 ^ 59
def prefixEnd_709098 : Nat := 4983230072969 + 3 ^ 40 * 709098 * 2
def baseEnd_709098 : Nat := 26970970751257176630661

theorem tailTrace_709098 : CollatzResearch.WordTrace tailWord_709098 prefixEnd_709098 26970970751257176630661 := by
  unfold tailWord_709098
  simp only [CollatzResearch.WordTrace]
  refine ⟨6465732196266631285475987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17241952523377683427935965 6465732196266631285475987)
  ·
    refine ⟨9698598294399946928213981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6465732196266631285475987 9698598294399946928213981)
    ·
      refine ⟨3636974360399980098080243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9698598294399946928213981 3636974360399980098080243)
      ·
        refine ⟨5455461540599970147120365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3636974360399980098080243 5455461540599970147120365)
        ·
          refine ⟨2045798077724988805170137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5455461540599970147120365 2045798077724988805170137)
          ·
            refine ⟨1534348558293741603877603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2045798077724988805170137 1534348558293741603877603)
            ·
              refine ⟨2301522837440612405816405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1534348558293741603877603 2301522837440612405816405)
              ·
                refine ⟨26970970751257176630661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2301522837440612405816405 26970970751257176630661)
                ·
                  rfl

theorem cell22_709098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 8].length) (baseStart_709098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_709098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_709098 prefixEnd_709098 := by exact prefixLift 709098
  have htrace : WordTrace (prefixWord ++ tailWord_709098) baseStart_709098 baseEnd_709098 := by
    simpa [prefixWord, tailWord_709098, baseEnd_709098] using wordTrace_append hprefix tailTrace_709098
  have hstable : (prefixWord ++ tailWord_709098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709098).length < 2 ^ (prefixWord ++ tailWord_709098).sum := by decide
  have hdescent : baseEnd_709098 < baseStart_709098 := by decide
  rcases family_descends (prefixWord ++ tailWord_709098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709113 : List Nat := [1, 2, 1, 3, 1, 2, 2, 2, 5, 3]
def baseStart_709113 : Nat := 118140960795 + 709113 * 2 ^ 59
def prefixEnd_709113 : Nat := 4983230072969 + 3 ^ 40 * 709113 * 2
def baseEnd_709113 : Nat := 242743871567859550550903

theorem tailTrace_709113 : CollatzResearch.WordTrace tailWord_709113 prefixEnd_709113 242743871567859550550903 := by
  unfold tailWord_709113
  simp only [CollatzResearch.WordTrace]
  refine ⟨25863475880012182703699993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17242317253341455135799995 25863475880012182703699993)
  ·
    refine ⟨19397606910009137027774995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25863475880012182703699993 19397606910009137027774995)
    ·
      refine ⟨29096410365013705541662493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19397606910009137027774995 29096410365013705541662493)
      ·
        refine ⟨10911153886880139578123435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29096410365013705541662493 10911153886880139578123435)
        ·
          refine ⟨16366730830320209367185153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10911153886880139578123435 16366730830320209367185153)
          ·
            refine ⟨12275048122740157025388865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16366730830320209367185153 12275048122740157025388865)
            ·
              refine ⟨9206286092055117769041649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12275048122740157025388865 9206286092055117769041649)
              ·
                refine ⟨6904714569041338326781237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9206286092055117769041649 6904714569041338326781237)
                ·
                  refine ⟨647316990847625468135741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6904714569041338326781237 647316990847625468135741)
                  ·
                    refine ⟨242743871567859550550903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 647316990847625468135741 242743871567859550550903)
                    ·
                      rfl

theorem cell22_709113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 2, 5, 3].length) (baseStart_709113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_709113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_709113 prefixEnd_709113 := by exact prefixLift 709113
  have htrace : WordTrace (prefixWord ++ tailWord_709113) baseStart_709113 baseEnd_709113 := by
    simpa [prefixWord, tailWord_709113, baseEnd_709113] using wordTrace_append hprefix tailTrace_709113
  have hstable : (prefixWord ++ tailWord_709113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709113).length < 2 ^ (prefixWord ++ tailWord_709113).sum := by decide
  have hdescent : baseEnd_709113 < baseStart_709113 := by decide
  rcases family_descends (prefixWord ++ tailWord_709113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709181 : List Nat := [1, 4, 1, 3, 2, 3, 2, 2, 1, 3]
def baseStart_709181 : Nat := 118140960795 + 709181 * 2 ^ 59
def prefixEnd_709181 : Nat := 4983230072969 + 3 ^ 40 * 709181 * 2
def baseEnd_709181 : Nat := 242767149357530039850695

theorem tailTrace_709181 : CollatzResearch.WordTrace tailWord_709181 prefixEnd_709181 242767149357530039850695 := by
  unfold tailWord_709181
  simp only [CollatzResearch.WordTrace]
  refine ⟨25865956043765830317175397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17243970695843886878116931 25865956043765830317175397)
  ·
    refine ⟨4849866758206093184470387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25865956043765830317175397 4849866758206093184470387)
    ·
      refine ⟨7274800137309139776705581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4849866758206093184470387 7274800137309139776705581)
      ·
        refine ⟨2728050051490927416264593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7274800137309139776705581 2728050051490927416264593)
        ·
          refine ⟨2046037538618195562198445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2728050051490927416264593 2046037538618195562198445)
          ·
            refine ⟨767264076981823335824417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2046037538618195562198445 767264076981823335824417)
            ·
              refine ⟨575448057736367501868313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 767264076981823335824417 575448057736367501868313)
              ·
                refine ⟨431586043302275626401235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 575448057736367501868313 431586043302275626401235)
                ·
                  refine ⟨647379064953413439601853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 431586043302275626401235 647379064953413439601853)
                  ·
                    refine ⟨242767149357530039850695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 647379064953413439601853 242767149357530039850695)
                    ·
                      rfl

theorem cell22_709181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 2, 2, 1, 3].length) (baseStart_709181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_709181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_709181 prefixEnd_709181 := by exact prefixLift 709181
  have htrace : WordTrace (prefixWord ++ tailWord_709181) baseStart_709181 baseEnd_709181 := by
    simpa [prefixWord, tailWord_709181, baseEnd_709181] using wordTrace_append hprefix tailTrace_709181
  have hstable : (prefixWord ++ tailWord_709181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709181).length < 2 ^ (prefixWord ++ tailWord_709181).sum := by decide
  have hdescent : baseEnd_709181 < baseStart_709181 := by decide
  rcases family_descends (prefixWord ++ tailWord_709181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709220 : List Nat := [2, 3, 1, 1, 2, 2, 2, 2, 4, 3]
def baseStart_709220 : Nat := 118140960795 + 709220 * 2 ^ 59
def prefixEnd_709220 : Nat := 4983230072969 + 3 ^ 40 * 709220 * 2
def baseEnd_709220 : Nat := 242780499854546938125575

theorem tailTrace_709220 : CollatzResearch.WordTrace tailWord_709220 prefixEnd_709220 242780499854546938125575 := by
  unfold tailWord_709220
  simp only [CollatzResearch.WordTrace]
  refine ⟨12933689245312269988922557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17244918993749693318563409 12933689245312269988922557)
  ·
    refine ⟨4850133466992101245845959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12933689245312269988922557 4850133466992101245845959)
    ·
      refine ⟨7275200200488151868768939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4850133466992101245845959 7275200200488151868768939)
      ·
        refine ⟨10912800300732227803153409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7275200200488151868768939 10912800300732227803153409)
        ·
          refine ⟨8184600225549170852365057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10912800300732227803153409 8184600225549170852365057)
          ·
            refine ⟨6138450169161878139273793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8184600225549170852365057 6138450169161878139273793)
            ·
              refine ⟨4603837626871408604455345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6138450169161878139273793 4603837626871408604455345)
              ·
                refine ⟨3452878220153556453341509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4603837626871408604455345 3452878220153556453341509)
                ·
                  refine ⟨647414666278791835001533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3452878220153556453341509 647414666278791835001533)
                  ·
                    refine ⟨242780499854546938125575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 647414666278791835001533 242780499854546938125575)
                    ·
                      rfl

theorem cell22_709220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 2, 4, 3].length) (baseStart_709220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_709220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_709220 prefixEnd_709220 := by exact prefixLift 709220
  have htrace : WordTrace (prefixWord ++ tailWord_709220) baseStart_709220 baseEnd_709220 := by
    simpa [prefixWord, tailWord_709220, baseEnd_709220] using wordTrace_append hprefix tailTrace_709220
  have hstable : (prefixWord ++ tailWord_709220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709220).length < 2 ^ (prefixWord ++ tailWord_709220).sum := by decide
  have hdescent : baseEnd_709220 < baseStart_709220 := by decide
  rcases family_descends (prefixWord ++ tailWord_709220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709310 : List Nat := [4, 2, 1, 1, 2, 1, 2, 1, 1, 7]
def baseStart_709310 : Nat := 118140960795 + 709310 * 2 ^ 59
def prefixEnd_709310 : Nat := 4983230072969 + 3 ^ 40 * 709310 * 2
def baseEnd_709310 : Nat := 242811308693816703375299

theorem tailTrace_709310 : CollatzResearch.WordTrace tailWord_709310 prefixEnd_709310 242811308693816703375299 := by
  unfold tailWord_709310
  simp only [CollatzResearch.WordTrace]
  refine ⟨3233832632537310668577673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17247107373532323565747589 3233832632537310668577673)
  ·
    refine ⟨2425374474402983001433255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3233832632537310668577673 2425374474402983001433255)
    ·
      refine ⟨3638061711604474502149883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2425374474402983001433255 3638061711604474502149883)
      ·
        refine ⟨5457092567406711753224825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3638061711604474502149883 5457092567406711753224825)
        ·
          refine ⟨4092819425555033814918619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5457092567406711753224825 4092819425555033814918619)
          ·
            refine ⟨6139229138332550722377929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4092819425555033814918619 6139229138332550722377929)
            ·
              refine ⟨4604421853749413041783447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6139229138332550722377929 4604421853749413041783447)
              ·
                refine ⟨6906632780624119562675171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4604421853749413041783447 6906632780624119562675171)
                ·
                  refine ⟨10359949170936179344012757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6906632780624119562675171 10359949170936179344012757)
                  ·
                    refine ⟨242811308693816703375299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10359949170936179344012757 242811308693816703375299)
                    ·
                      rfl

theorem cell22_709310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 1, 1, 7].length) (baseStart_709310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_709310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_709310 prefixEnd_709310 := by exact prefixLift 709310
  have htrace : WordTrace (prefixWord ++ tailWord_709310) baseStart_709310 baseEnd_709310 := by
    simpa [prefixWord, tailWord_709310, baseEnd_709310] using wordTrace_append hprefix tailTrace_709310
  have hstable : (prefixWord ++ tailWord_709310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709310).length < 2 ^ (prefixWord ++ tailWord_709310).sum := by decide
  have hdescent : baseEnd_709310 < baseStart_709310 := by decide
  rcases family_descends (prefixWord ++ tailWord_709310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709312 : List Nat := [2, 1, 1, 2, 4, 2, 4, 1, 5]
def baseStart_709312 : Nat := 118140960795 + 709312 * 2 ^ 59
def prefixEnd_709312 : Nat := 4983230072969 + 3 ^ 40 * 709312 * 2
def baseEnd_709312 : Nat := 80937331111563121608431

theorem tailTrace_709312 : CollatzResearch.WordTrace tailWord_709312 prefixEnd_709312 80937331111563121608431 := by
  unfold tailWord_709312
  simp only [CollatzResearch.WordTrace]
  refine ⟨12935367003145619845097095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17247156004194159793462793 12935367003145619845097095)
  ·
    refine ⟨19403050504718429767645643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12935367003145619845097095 19403050504718429767645643)
    ·
      refine ⟨29104575757077644651468465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19403050504718429767645643 29104575757077644651468465)
      ·
        refine ⟨21828431817808233488601349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29104575757077644651468465 21828431817808233488601349)
        ·
          refine ⟨4092830965839043779112753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21828431817808233488601349 4092830965839043779112753)
          ·
            refine ⟨3069623224379282834334565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4092830965839043779112753 3069623224379282834334565)
            ·
              refine ⟨575554354571115531437731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3069623224379282834334565 575554354571115531437731)
              ·
                refine ⟨863331531856673297156597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 575554354571115531437731 863331531856673297156597)
                ·
                  refine ⟨80937331111563121608431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 863331531856673297156597 80937331111563121608431)
                  ·
                    rfl

theorem cell22_709312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 4, 1, 5].length) (baseStart_709312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_709312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_709312 prefixEnd_709312 := by exact prefixLift 709312
  have htrace : WordTrace (prefixWord ++ tailWord_709312) baseStart_709312 baseEnd_709312 := by
    simpa [prefixWord, tailWord_709312, baseEnd_709312] using wordTrace_append hprefix tailTrace_709312
  have hstable : (prefixWord ++ tailWord_709312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709312).length < 2 ^ (prefixWord ++ tailWord_709312).sum := by decide
  have hdescent : baseEnd_709312 < baseStart_709312 := by decide
  rcases family_descends (prefixWord ++ tailWord_709312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709370 : List Nat := [3, 1, 1, 1, 1, 3, 2, 2, 4, 4]
def baseStart_709370 : Nat := 118140960795 + 709370 * 2 ^ 59
def prefixEnd_709370 : Nat := 4983230072969 + 3 ^ 40 * 709370 * 2
def baseEnd_709370 : Nat := 242831847919996546875115

theorem tailTrace_709370 : CollatzResearch.WordTrace tailWord_709370 prefixEnd_709370 242831847919996546875115 := by
  unfold tailWord_709370
  simp only [CollatzResearch.WordTrace]
  refine ⟨6468212360020278898951391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17248566293387410397203709 6468212360020278898951391)
  ·
    refine ⟨9702318540030418348427087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6468212360020278898951391 9702318540030418348427087)
    ·
      refine ⟨14553477810045627522640631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9702318540030418348427087 14553477810045627522640631)
      ·
        refine ⟨21830216715068441283960947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14553477810045627522640631 21830216715068441283960947)
        ·
          refine ⟨32745325072602661925941421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21830216715068441283960947 32745325072602661925941421)
          ·
            refine ⟨12279496902225998222228033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32745325072602661925941421 12279496902225998222228033)
            ·
              refine ⟨9209622676669498666671025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12279496902225998222228033 9209622676669498666671025)
              ·
                refine ⟨6907217007502124000003269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9209622676669498666671025 6907217007502124000003269)
                ·
                  refine ⟨1295103188906648250000613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6907217007502124000003269 1295103188906648250000613)
                  ·
                    refine ⟨242831847919996546875115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1295103188906648250000613 242831847919996546875115)
                    ·
                      rfl

theorem cell22_709370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 2, 4, 4].length) (baseStart_709370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_709370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_709370 prefixEnd_709370 := by exact prefixLift 709370
  have htrace : WordTrace (prefixWord ++ tailWord_709370) baseStart_709370 baseEnd_709370 := by
    simpa [prefixWord, tailWord_709370, baseEnd_709370] using wordTrace_append hprefix tailTrace_709370
  have hstable : (prefixWord ++ tailWord_709370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709370).length < 2 ^ (prefixWord ++ tailWord_709370).sum := by decide
  have hdescent : baseEnd_709370 < baseStart_709370 := by decide
  rcases family_descends (prefixWord ++ tailWord_709370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709372 : List Nat := [2, 2, 2, 1, 3, 3, 2, 1, 1, 5]
def baseStart_709372 : Nat := 118140960795 + 709372 * 2 ^ 59
def prefixEnd_709372 : Nat := 4983230072969 + 3 ^ 40 * 709372 * 2
def baseEnd_709372 : Nat := 242832532560869208325109

theorem tailTrace_709372 : CollatzResearch.WordTrace tailWord_709372 prefixEnd_709372 242832532560869208325109 := by
  unfold tailWord_709372
  simp only [CollatzResearch.WordTrace]
  refine ⟨12936461193036934968689185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17248614924049246624918913 12936461193036934968689185)
  ·
    refine ⟨9702345894777701226516889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12936461193036934968689185 9702345894777701226516889)
    ·
      refine ⟨7276759421083275919887667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9702345894777701226516889 7276759421083275919887667)
      ·
        refine ⟨10915139131624913879831501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7276759421083275919887667 10915139131624913879831501)
        ·
          refine ⟨4093177174359342704936813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10915139131624913879831501 4093177174359342704936813)
          ·
            refine ⟨1534941440384753514351305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4093177174359342704936813 1534941440384753514351305)
            ·
              refine ⟨1151206080288565135763479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1534941440384753514351305 1151206080288565135763479)
              ·
                refine ⟨1726809120432847703645219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1151206080288565135763479 1726809120432847703645219)
                ·
                  refine ⟨2590213680649271555467829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1726809120432847703645219 2590213680649271555467829)
                  ·
                    refine ⟨242832532560869208325109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2590213680649271555467829 242832532560869208325109)
                    ·
                      rfl

theorem cell22_709372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 2, 1, 1, 5].length) (baseStart_709372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_709372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_709372 prefixEnd_709372 := by exact prefixLift 709372
  have htrace : WordTrace (prefixWord ++ tailWord_709372) baseStart_709372 baseEnd_709372 := by
    simpa [prefixWord, tailWord_709372, baseEnd_709372] using wordTrace_append hprefix tailTrace_709372
  have hstable : (prefixWord ++ tailWord_709372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709372).length < 2 ^ (prefixWord ++ tailWord_709372).sum := by decide
  have hdescent : baseEnd_709372 < baseStart_709372 := by decide
  rcases family_descends (prefixWord ++ tailWord_709372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709445 : List Nat := [1, 3, 1, 1, 1, 2, 2, 2, 4, 5]
def baseStart_709445 : Nat := 118140960795 + 709445 * 2 ^ 59
def prefixEnd_709445 : Nat := 4983230072969 + 3 ^ 40 * 709445 * 2
def baseEnd_709445 : Nat := 242857521952721351249885

theorem tailTrace_709445 : CollatzResearch.WordTrace tailWord_709445 prefixEnd_709445 242857521952721351249885 := by
  unfold tailWord_709445
  simp only [CollatzResearch.WordTrace]
  refine ⟨25875584914809403404785789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17250389943206268936523859 25875584914809403404785789)
  ·
    refine ⟨9703344343053526276794671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25875584914809403404785789 9703344343053526276794671)
    ·
      refine ⟨14555016514580289415192007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9703344343053526276794671 14555016514580289415192007)
      ·
        refine ⟨21832524771870434122788011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14555016514580289415192007 21832524771870434122788011)
        ·
          refine ⟨32748787157805651184182017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21832524771870434122788011 32748787157805651184182017)
          ·
            refine ⟨24561590368354238388136513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32748787157805651184182017 24561590368354238388136513)
            ·
              refine ⟨18421192776265678791102385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24561590368354238388136513 18421192776265678791102385)
              ·
                refine ⟨13815894582199259093326789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18421192776265678791102385 13815894582199259093326789)
                ·
                  refine ⟨2590480234162361079998773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13815894582199259093326789 2590480234162361079998773)
                  ·
                    refine ⟨242857521952721351249885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2590480234162361079998773 242857521952721351249885)
                    ·
                      rfl

theorem cell22_709445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 4, 5].length) (baseStart_709445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_709445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_709445 prefixEnd_709445 := by exact prefixLift 709445
  have htrace : WordTrace (prefixWord ++ tailWord_709445) baseStart_709445 baseEnd_709445 := by
    simpa [prefixWord, tailWord_709445, baseEnd_709445] using wordTrace_append hprefix tailTrace_709445
  have hstable : (prefixWord ++ tailWord_709445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709445).length < 2 ^ (prefixWord ++ tailWord_709445).sum := by decide
  have hdescent : baseEnd_709445 < baseStart_709445 := by decide
  rcases family_descends (prefixWord ++ tailWord_709445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709507 : List Nat := [1, 1, 1, 3, 4, 1, 3, 2, 1, 5]
def baseStart_709507 : Nat := 118140960795 + 709507 * 2 ^ 59
def prefixEnd_709507 : Nat := 4983230072969 + 3 ^ 40 * 709507 * 2
def baseEnd_709507 : Nat := 242878745819773856199695

theorem tailTrace_709507 : CollatzResearch.WordTrace tailWord_709507 prefixEnd_709507 242878745819773856199695 := by
  unfold tailWord_709507
  simp only [CollatzResearch.WordTrace]
  refine ⟨25877846240584787993542775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17251897493723191995695183 25877846240584787993542775)
  ·
    refine ⟨38816769360877181990314163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25877846240584787993542775 38816769360877181990314163)
    ·
      refine ⟨58225154041315772985471245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38816769360877181990314163 58225154041315772985471245)
      ·
        refine ⟨21834432765493414869551717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58225154041315772985471245 21834432765493414869551717)
        ·
          refine ⟨4093956143530015288040947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21834432765493414869551717 4093956143530015288040947)
          ·
            refine ⟨6140934215295022932061421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4093956143530015288040947 6140934215295022932061421)
            ·
              refine ⟨2302850330735633599523033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6140934215295022932061421 2302850330735633599523033)
              ·
                refine ⟨1727137748051725199642275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2302850330735633599523033 1727137748051725199642275)
                ·
                  refine ⟨2590706622077587799463413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1727137748051725199642275 2590706622077587799463413)
                  ·
                    refine ⟨242878745819773856199695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2590706622077587799463413 242878745819773856199695)
                    ·
                      rfl

theorem cell22_709507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 2, 1, 5].length) (baseStart_709507 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_709507 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_709507 prefixEnd_709507 := by exact prefixLift 709507
  have htrace : WordTrace (prefixWord ++ tailWord_709507) baseStart_709507 baseEnd_709507 := by
    simpa [prefixWord, tailWord_709507, baseEnd_709507] using wordTrace_append hprefix tailTrace_709507
  have hstable : (prefixWord ++ tailWord_709507).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709507).length < 2 ^ (prefixWord ++ tailWord_709507).sum := by decide
  have hdescent : baseEnd_709507 < baseStart_709507 := by decide
  rcases family_descends (prefixWord ++ tailWord_709507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709511 : List Nat := [1, 1, 4, 2, 3, 2, 3, 1, 1, 4]
def baseStart_709511 : Nat := 118140960795 + 709511 * 2 ^ 59
def prefixEnd_709511 : Nat := 4983230072969 + 3 ^ 40 * 709511 * 2
def baseEnd_709511 : Nat := 242880115101519179099683

theorem tailTrace_709511 : CollatzResearch.WordTrace tailWord_709511 prefixEnd_709511 242880115101519179099683 := by
  unfold tailWord_709511
  simp only [CollatzResearch.WordTrace]
  refine ⟨25877992132570296676688387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17251994755046864451125591 25877992132570296676688387)
  ·
    refine ⟨38816988198855445015032581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25877992132570296676688387 38816988198855445015032581)
    ·
      refine ⟨7278185287285395940318609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38816988198855445015032581 7278185287285395940318609)
      ·
        refine ⟨5458638965464046955238957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7278185287285395940318609 5458638965464046955238957)
        ·
          refine ⟨2046989612049017608214609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5458638965464046955238957 2046989612049017608214609)
          ·
            refine ⟨1535242209036763206160957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2046989612049017608214609 1535242209036763206160957)
            ·
              refine ⟨575715828388786202310359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1535242209036763206160957 575715828388786202310359)
              ·
                refine ⟨863573742583179303465539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 575715828388786202310359 863573742583179303465539)
                ·
                  refine ⟨1295360613874768955198309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 863573742583179303465539 1295360613874768955198309)
                  ·
                    refine ⟨242880115101519179099683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1295360613874768955198309 242880115101519179099683)
                    ·
                      rfl

theorem cell22_709511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 3, 1, 1, 4].length) (baseStart_709511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_709511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_709511 prefixEnd_709511 := by exact prefixLift 709511
  have htrace : WordTrace (prefixWord ++ tailWord_709511) baseStart_709511 baseEnd_709511 := by
    simpa [prefixWord, tailWord_709511, baseEnd_709511] using wordTrace_append hprefix tailTrace_709511
  have hstable : (prefixWord ++ tailWord_709511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709511).length < 2 ^ (prefixWord ++ tailWord_709511).sum := by decide
  have hdescent : baseEnd_709511 < baseStart_709511 := by decide
  rcases family_descends (prefixWord ++ tailWord_709511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709556 : List Nat := [2, 5, 2, 1, 1, 2, 1, 1, 1, 6]
def baseStart_709556 : Nat := 118140960795 + 709556 * 2 ^ 59
def prefixEnd_709556 : Nat := 4983230072969 + 3 ^ 40 * 709556 * 2
def baseEnd_709556 : Nat := 242895519521154061724545

theorem tailTrace_709556 : CollatzResearch.WordTrace tailWord_709556 prefixEnd_709556 242895519521154061724545 := by
  unfold tailWord_709556
  simp only [CollatzResearch.WordTrace]
  refine ⟨12939816708703634681038261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17253088944938179574717681 12939816708703634681038261)
  ·
    refine ⟨1213107816440965751347337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12939816708703634681038261 1213107816440965751347337)
    ·
      refine ⟨909830862330724313510503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1213107816440965751347337 909830862330724313510503)
      ·
        refine ⟨1364746293496086470265755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 909830862330724313510503 1364746293496086470265755)
        ·
          refine ⟨2047119440244129705398633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1364746293496086470265755 2047119440244129705398633)
          ·
            refine ⟨1535339580183097279048975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2047119440244129705398633 1535339580183097279048975)
            ·
              refine ⟨2303009370274645918573463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1535339580183097279048975 2303009370274645918573463)
              ·
                refine ⟨3454514055411968877860195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2303009370274645918573463 3454514055411968877860195)
                ·
                  refine ⟨5181771083117953316790293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3454514055411968877860195 5181771083117953316790293)
                  ·
                    refine ⟨242895519521154061724545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5181771083117953316790293 242895519521154061724545)
                    ·
                      rfl

theorem cell22_709556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_709556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_709556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_709556 prefixEnd_709556 := by exact prefixLift 709556
  have htrace : WordTrace (prefixWord ++ tailWord_709556) baseStart_709556 baseEnd_709556 := by
    simpa [prefixWord, tailWord_709556, baseEnd_709556] using wordTrace_append hprefix tailTrace_709556
  have hstable : (prefixWord ++ tailWord_709556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709556).length < 2 ^ (prefixWord ++ tailWord_709556).sum := by decide
  have hdescent : baseEnd_709556 < baseStart_709556 := by decide
  rcases family_descends (prefixWord ++ tailWord_709556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709586 : List Nat := [3, 2, 2, 3, 1, 1, 1, 3, 3, 3]
def baseStart_709586 : Nat := 118140960795 + 709586 * 2 ^ 59
def prefixEnd_709586 : Nat := 4983230072969 + 3 ^ 40 * 709586 * 2
def baseEnd_709586 : Nat := 242905789134243983474453

theorem tailTrace_709586 : CollatzResearch.WordTrace tailWord_709586 prefixEnd_709586 242905789134243983474453 := by
  unfold tailWord_709586
  simp only [CollatzResearch.WordTrace]
  refine ⟨6470181901824646121417153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17253818404865722990445741 6470181901824646121417153)
  ·
    refine ⟨4852636426368484591062865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6470181901824646121417153 4852636426368484591062865)
    ·
      refine ⟨3639477319776363443297149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4852636426368484591062865 3639477319776363443297149)
      ·
        refine ⟨1364803994916136291236431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3639477319776363443297149 1364803994916136291236431)
        ·
          refine ⟨2047205992374204436854647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1364803994916136291236431 2047205992374204436854647)
          ·
            refine ⟨3070808988561306655281971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2047205992374204436854647 3070808988561306655281971)
            ·
              refine ⟨4606213482841959982922957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3070808988561306655281971 4606213482841959982922957)
              ·
                refine ⟨1727330056065734993596109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4606213482841959982922957 1727330056065734993596109)
                ·
                  refine ⟨647748771024650622598541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1727330056065734993596109 647748771024650622598541)
                  ·
                    refine ⟨242905789134243983474453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 647748771024650622598541 242905789134243983474453)
                    ·
                      rfl

theorem cell22_709586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 3, 3, 3].length) (baseStart_709586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_709586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_709586 prefixEnd_709586 := by exact prefixLift 709586
  have htrace : WordTrace (prefixWord ++ tailWord_709586) baseStart_709586 baseEnd_709586 := by
    simpa [prefixWord, tailWord_709586, baseEnd_709586] using wordTrace_append hprefix tailTrace_709586
  have hstable : (prefixWord ++ tailWord_709586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709586).length < 2 ^ (prefixWord ++ tailWord_709586).sum := by decide
  have hdescent : baseEnd_709586 < baseStart_709586 := by decide
  rcases family_descends (prefixWord ++ tailWord_709586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709644 : List Nat := [2, 2, 1, 2, 3, 2, 3, 1, 6]
def baseStart_709644 : Nat := 118140960795 + 709644 * 2 ^ 59
def prefixEnd_709644 : Nat := 4983230072969 + 3 ^ 40 * 709644 * 2
def baseEnd_709644 : Nat := 80975214573183721841425

theorem tailTrace_709644 : CollatzResearch.WordTrace tailWord_709644 prefixEnd_709644 80975214573183721841425 := by
  unfold tailWord_709644
  simp only [CollatzResearch.WordTrace]
  refine ⟨12941421520544230195639993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17255228694058973594186657 12941421520544230195639993)
  ·
    refine ⟨9706066140408172646729995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12941421520544230195639993 9706066140408172646729995)
    ·
      refine ⟨14559099210612258970094993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9706066140408172646729995 14559099210612258970094993)
      ·
        refine ⟨10919324407959194227571245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14559099210612258970094993 10919324407959194227571245)
        ·
          refine ⟨4094746652984697835339217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10919324407959194227571245 4094746652984697835339217)
          ·
            refine ⟨3071059989738523376504413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4094746652984697835339217 3071059989738523376504413)
            ·
              refine ⟨1151647496151946266189155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3071059989738523376504413 1151647496151946266189155)
              ·
                refine ⟨1727471244227919399283733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1151647496151946266189155 1727471244227919399283733)
                ·
                  refine ⟨80975214573183721841425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1727471244227919399283733 80975214573183721841425)
                  ·
                    rfl

theorem cell22_709644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 3, 1, 6].length) (baseStart_709644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_709644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_709644 prefixEnd_709644 := by exact prefixLift 709644
  have htrace : WordTrace (prefixWord ++ tailWord_709644) baseStart_709644 baseEnd_709644 := by
    simpa [prefixWord, tailWord_709644, baseEnd_709644] using wordTrace_append hprefix tailTrace_709644
  have hstable : (prefixWord ++ tailWord_709644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709644).length < 2 ^ (prefixWord ++ tailWord_709644).sum := by decide
  have hdescent : baseEnd_709644 < baseStart_709644 := by decide
  rcases family_descends (prefixWord ++ tailWord_709644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709650 : List Nat := [3, 2, 5, 1, 1, 1, 1, 3, 5]
def baseStart_709650 : Nat := 118140960795 + 709650 * 2 ^ 59
def prefixEnd_709650 : Nat := 4983230072969 + 3 ^ 40 * 709650 * 2
def baseEnd_709650 : Nat := 80975899214056383291419

theorem tailTrace_709650 : CollatzResearch.WordTrace tailWord_709650 prefixEnd_709650 80975899214056383291419 := by
  unfold tailWord_709650
  simp only [CollatzResearch.WordTrace]
  refine ⟨6470765469766680853999601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17255374586044482277332269 6470765469766680853999601)
  ·
    refine ⟨4853074102325010640499701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6470765469766680853999601 4853074102325010640499701)
    ·
      refine ⟨454975697092969747546847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4853074102325010640499701 454975697092969747546847)
      ·
        refine ⟨682463545639454621320271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 454975697092969747546847 682463545639454621320271)
        ·
          refine ⟨1023695318459181931980407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 682463545639454621320271 1023695318459181931980407)
          ·
            refine ⟨1535542977688772897970611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1023695318459181931980407 1535542977688772897970611)
            ·
              refine ⟨2303314466533159346955917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1535542977688772897970611 2303314466533159346955917)
              ·
                refine ⟨863742924949934755108469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2303314466533159346955917 863742924949934755108469)
                ·
                  refine ⟨80975899214056383291419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 863742924949934755108469 80975899214056383291419)
                  ·
                    rfl

theorem cell22_709650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 3, 5].length) (baseStart_709650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_709650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_709650 prefixEnd_709650 := by exact prefixLift 709650
  have htrace : WordTrace (prefixWord ++ tailWord_709650) baseStart_709650 baseEnd_709650 := by
    simpa [prefixWord, tailWord_709650, baseEnd_709650] using wordTrace_append hprefix tailTrace_709650
  have hstable : (prefixWord ++ tailWord_709650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709650).length < 2 ^ (prefixWord ++ tailWord_709650).sum := by decide
  have hdescent : baseEnd_709650 < baseStart_709650 := by decide
  rcases family_descends (prefixWord ++ tailWord_709650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709657 : List Nat := [1, 2, 1, 2, 1, 1, 4, 1, 3, 6]
def baseStart_709657 : Nat := 118140960795 + 709657 * 2 ^ 59
def prefixEnd_709657 : Nat := 4983230072969 + 3 ^ 40 * 709657 * 2
def baseEnd_709657 : Nat := 242930093885223464949235

theorem tailTrace_709657 : CollatzResearch.WordTrace tailWord_709657 prefixEnd_709657 242930093885223464949235 := by
  unfold tailWord_709657
  simp only [CollatzResearch.WordTrace]
  refine ⟨25883317190041363611503225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17255544793360909074335483 25883317190041363611503225)
  ·
    refine ⟨19412487892531022708627419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25883317190041363611503225 19412487892531022708627419)
    ·
      refine ⟨29118731838796534062941129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19412487892531022708627419 29118731838796534062941129)
      ·
        refine ⟨21839048879097400547205847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29118731838796534062941129 21839048879097400547205847)
        ·
          refine ⟨32758573318646100820808771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21839048879097400547205847 32758573318646100820808771)
          ·
            refine ⟨49137859977969151231213157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32758573318646100820808771 49137859977969151231213157)
            ·
              refine ⟨9213348745869215855852467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49137859977969151231213157 9213348745869215855852467)
              ·
                refine ⟨13820023118803823783778701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9213348745869215855852467 13820023118803823783778701)
                ·
                  refine ⟨5182508669551433918917013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13820023118803823783778701 5182508669551433918917013)
                  ·
                    refine ⟨242930093885223464949235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5182508669551433918917013 242930093885223464949235)
                    ·
                      rfl

theorem cell22_709657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 3, 6].length) (baseStart_709657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_709657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_709657 prefixEnd_709657 := by exact prefixLift 709657
  have htrace : WordTrace (prefixWord ++ tailWord_709657) baseStart_709657 baseEnd_709657 := by
    simpa [prefixWord, tailWord_709657, baseEnd_709657] using wordTrace_append hprefix tailTrace_709657
  have hstable : (prefixWord ++ tailWord_709657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709657).length < 2 ^ (prefixWord ++ tailWord_709657).sum := by decide
  have hdescent : baseEnd_709657 < baseStart_709657 := by decide
  rcases family_descends (prefixWord ++ tailWord_709657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709693 : List Nat := [1, 4, 1, 3, 1, 3, 2, 2, 2, 3]
def baseStart_709693 : Nat := 118140960795 + 709693 * 2 ^ 59
def prefixEnd_709693 : Nat := 4983230072969 + 3 ^ 40 * 709693 * 2
def baseEnd_709693 : Nat := 242942417420931371049125

theorem tailTrace_709693 : CollatzResearch.WordTrace tailWord_709693 prefixEnd_709693 242942417420931371049125 := by
  unfold tailWord_709693
  simp only [CollatzResearch.WordTrace]
  refine ⟨25884630217910941759813733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17256420145273961173209155 25884630217910941759813733)
  ·
    refine ⟨4853368165858301579965075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25884630217910941759813733 4853368165858301579965075)
    ·
      refine ⟨7280052248787452369947613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4853368165858301579965075 7280052248787452369947613)
      ·
        refine ⟨2730019593295294638730355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7280052248787452369947613 2730019593295294638730355)
        ·
          refine ⟨4095029389942941958095533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2730019593295294638730355 4095029389942941958095533)
          ·
            refine ⟨1535636021228603234285825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4095029389942941958095533 1535636021228603234285825)
            ·
              refine ⟨1151727015921452425714369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1535636021228603234285825 1151727015921452425714369)
              ·
                refine ⟨863795261941089319285777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1151727015921452425714369 863795261941089319285777)
                ·
                  refine ⟨647846446455816989464333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 863795261941089319285777 647846446455816989464333)
                  ·
                    refine ⟨242942417420931371049125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 647846446455816989464333 242942417420931371049125)
                    ·
                      rfl

theorem cell22_709693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 2, 2, 2, 3].length) (baseStart_709693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_709693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_709693 prefixEnd_709693 := by exact prefixLift 709693
  have htrace : WordTrace (prefixWord ++ tailWord_709693) baseStart_709693 baseEnd_709693 := by
    simpa [prefixWord, tailWord_709693, baseEnd_709693] using wordTrace_append hprefix tailTrace_709693
  have hstable : (prefixWord ++ tailWord_709693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709693).length < 2 ^ (prefixWord ++ tailWord_709693).sum := by decide
  have hdescent : baseEnd_709693 < baseStart_709693 := by decide
  rcases family_descends (prefixWord ++ tailWord_709693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709725 : List Nat := [1, 4, 4, 1, 2, 2, 1, 1, 2, 4]
def baseStart_709725 : Nat := 118140960795 + 709725 * 2 ^ 59
def prefixEnd_709725 : Nat := 4983230072969 + 3 ^ 40 * 709725 * 2
def baseEnd_709725 : Nat := 242953371674893954249027

theorem tailTrace_709725 : CollatzResearch.WordTrace tailWord_709725 prefixEnd_709725 242953371674893954249027 := by
  unfold tailWord_709725
  simp only [CollatzResearch.WordTrace]
  refine ⟨25885797353795011224978629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17257198235863340816652419 25885797353795011224978629)
  ·
    refine ⟨4853587003836564604683493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25885797353795011224978629 4853587003836564604683493)
    ·
      refine ⟨910047563219355863378155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4853587003836564604683493 910047563219355863378155)
      ·
        refine ⟨1365071344829033795067233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 910047563219355863378155 1365071344829033795067233)
        ·
          refine ⟨1023803508621775346300425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1365071344829033795067233 1023803508621775346300425)
          ·
            refine ⟨767852631466331509725319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1023803508621775346300425 767852631466331509725319)
            ·
              refine ⟨1151778947199497264587979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 767852631466331509725319 1151778947199497264587979)
              ·
                refine ⟨1727668420799245896881969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1151778947199497264587979 1727668420799245896881969)
                ·
                  refine ⟨1295751315599434422661477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1727668420799245896881969 1295751315599434422661477)
                  ·
                    refine ⟨242953371674893954249027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1295751315599434422661477 242953371674893954249027)
                    ·
                      rfl

theorem cell22_709725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_709725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_709725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_709725 prefixEnd_709725 := by exact prefixLift 709725
  have htrace : WordTrace (prefixWord ++ tailWord_709725) baseStart_709725 baseEnd_709725 := by
    simpa [prefixWord, tailWord_709725, baseEnd_709725] using wordTrace_append hprefix tailTrace_709725
  have hstable : (prefixWord ++ tailWord_709725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709725).length < 2 ^ (prefixWord ++ tailWord_709725).sum := by decide
  have hdescent : baseEnd_709725 < baseStart_709725 := by decide
  rcases family_descends (prefixWord ++ tailWord_709725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709779 : List Nat := [1, 1, 1, 2, 1, 2, 6, 2, 6]
def baseStart_709779 : Nat := 118140960795 + 709779 * 2 ^ 59
def prefixEnd_709779 : Nat := 4983230072969 + 3 ^ 40 * 709779 * 2
def baseEnd_709779 : Nat := 80990618992818604466287

theorem tailTrace_709779 : CollatzResearch.WordTrace tailWord_709779 prefixEnd_709779 80990618992818604466287 := by
  unfold tailWord_709779
  simp only [CollatzResearch.WordTrace]
  refine ⟨25887766895599378447444391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17258511263732918964962927 25887766895599378447444391)
  ·
    refine ⟨38831650343399067671166587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25887766895599378447444391 38831650343399067671166587)
    ·
      refine ⟨58247475515098601506749881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38831650343399067671166587 58247475515098601506749881)
      ·
        refine ⟨43685606636323951130062411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58247475515098601506749881 43685606636323951130062411)
        ·
          refine ⟨65528409954485926695093617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43685606636323951130062411 65528409954485926695093617)
          ·
            refine ⟨49146307465864445021320213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65528409954485926695093617 49146307465864445021320213)
            ·
              refine ⟨2303733162462395860374385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 49146307465864445021320213 2303733162462395860374385)
              ·
                refine ⟨1727799871846796895280789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2303733162462395860374385 1727799871846796895280789)
                ·
                  refine ⟨80990618992818604466287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1727799871846796895280789 80990618992818604466287)
                  ·
                    rfl

theorem cell22_709779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 2, 6].length) (baseStart_709779 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_709779 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_709779 prefixEnd_709779 := by exact prefixLift 709779
  have htrace : WordTrace (prefixWord ++ tailWord_709779) baseStart_709779 baseEnd_709779 := by
    simpa [prefixWord, tailWord_709779, baseEnd_709779] using wordTrace_append hprefix tailTrace_709779
  have hstable : (prefixWord ++ tailWord_709779).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709779).length < 2 ^ (prefixWord ++ tailWord_709779).sum := by decide
  have hdescent : baseEnd_709779 < baseStart_709779 := by decide
  rcases family_descends (prefixWord ++ tailWord_709779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709811 : List Nat := [1, 1, 1, 2, 3, 2, 4, 1, 4, 3]
def baseStart_709811 : Nat := 118140960795 + 709811 * 2 ^ 59
def prefixEnd_709811 : Nat := 4983230072969 + 3 ^ 40 * 709811 * 2
def baseEnd_709811 : Nat := 242982811232418396598763

theorem tailTrace_709811 : CollatzResearch.WordTrace tailWord_709811 prefixEnd_709811 242982811232418396598763 := by
  unfold tailWord_709811
  simp only [CollatzResearch.WordTrace]
  refine ⟨25888934031483447912609287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17259289354322298608406191 25888934031483447912609287)
  ·
    refine ⟨38833401047225171868913931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25888934031483447912609287 38833401047225171868913931)
    ·
      refine ⟨58250101570837757803370897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38833401047225171868913931 58250101570837757803370897)
      ·
        refine ⟨43687576178128318352528173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58250101570837757803370897 43687576178128318352528173)
        ·
          refine ⟨16382841066798119382198065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43687576178128318352528173 16382841066798119382198065)
          ·
            refine ⟨12287130800098589536648549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16382841066798119382198065 12287130800098589536648549)
            ·
              refine ⟨2303837025018485538121603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12287130800098589536648549 2303837025018485538121603)
              ·
                refine ⟨3455755537527728307182405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2303837025018485538121603 3455755537527728307182405)
                ·
                  refine ⟨647954163286449057596701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3455755537527728307182405 647954163286449057596701)
                  ·
                    refine ⟨242982811232418396598763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 647954163286449057596701 242982811232418396598763)
                    ·
                      rfl

theorem cell22_709811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 1, 4, 3].length) (baseStart_709811 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_709811 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_709811 prefixEnd_709811 := by exact prefixLift 709811
  have htrace : WordTrace (prefixWord ++ tailWord_709811) baseStart_709811 baseEnd_709811 := by
    simpa [prefixWord, tailWord_709811, baseEnd_709811] using wordTrace_append hprefix tailTrace_709811
  have hstable : (prefixWord ++ tailWord_709811).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709811).length < 2 ^ (prefixWord ++ tailWord_709811).sum := by decide
  have hdescent : baseEnd_709811 < baseStart_709811 := by decide
  rcases family_descends (prefixWord ++ tailWord_709811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709920 : List Nat := [2, 1, 1, 5, 3, 2, 1, 2, 5]
def baseStart_709920 : Nat := 118140960795 + 709920 * 2 ^ 59
def prefixEnd_709920 : Nat := 4983230072969 + 3 ^ 40 * 709920 * 2
def baseEnd_709920 : Nat := 81006708053326148541143

theorem tailTrace_709920 : CollatzResearch.WordTrace tailWord_709920 prefixEnd_709920 81006708053326148541143 := by
  unfold tailWord_709920
  simp only [CollatzResearch.WordTrace]
  refine ⟨12946454794044279764163607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17261939725392373018884809 12946454794044279764163607)
  ·
    refine ⟨19419682191066419646245411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12946454794044279764163607 19419682191066419646245411)
    ·
      refine ⟨29129523286599629469368117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19419682191066419646245411 29129523286599629469368117)
      ·
        refine ⟨2730892808118715262753261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29129523286599629469368117 2730892808118715262753261)
        ·
          refine ⟨1024084803044518223532473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2730892808118715262753261 1024084803044518223532473)
          ·
            refine ⟨768063602283388667649355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1024084803044518223532473 768063602283388667649355)
            ·
              refine ⟨1152095403425083001474033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 768063602283388667649355 1152095403425083001474033)
              ·
                refine ⟨864071552568812251105525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1152095403425083001474033 864071552568812251105525)
                ·
                  refine ⟨81006708053326148541143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 864071552568812251105525 81006708053326148541143)
                  ·
                    rfl

theorem cell22_709920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 1, 2, 5].length) (baseStart_709920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_709920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_709920 prefixEnd_709920 := by exact prefixLift 709920
  have htrace : WordTrace (prefixWord ++ tailWord_709920) baseStart_709920 baseEnd_709920 := by
    simpa [prefixWord, tailWord_709920, baseEnd_709920] using wordTrace_append hprefix tailTrace_709920
  have hstable : (prefixWord ++ tailWord_709920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709920).length < 2 ^ (prefixWord ++ tailWord_709920).sum := by decide
  have hdescent : baseEnd_709920 < baseStart_709920 := by decide
  rcases family_descends (prefixWord ++ tailWord_709920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709950 : List Nat := [4, 2, 1, 2, 1, 1, 4, 2, 1, 4]
def baseStart_709950 : Nat := 118140960795 + 709950 * 2 ^ 59
def prefixEnd_709950 : Nat := 4983230072969 + 3 ^ 40 * 709950 * 2
def baseEnd_709950 : Nat := 243030393773068367373337

theorem tailTrace_709950 : CollatzResearch.WordTrace tailWord_709950 prefixEnd_709950 243030393773068367373337 := by
  unfold tailWord_709950
  simp only [CollatzResearch.WordTrace]
  refine ⟨3236750472247484331489913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17262669185319916434612869 3236750472247484331489913)
  ·
    refine ⟨2427562854185613248617435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3236750472247484331489913 2427562854185613248617435)
    ·
      refine ⟨3641344281278419872926153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2427562854185613248617435 3641344281278419872926153)
      ·
        refine ⟨2731008210958814904694615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3641344281278419872926153 2731008210958814904694615)
        ·
          refine ⟨4096512316438222357041923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2731008210958814904694615 4096512316438222357041923)
          ·
            refine ⟨6144768474657333535562885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4096512316438222357041923 6144768474657333535562885)
            ·
              refine ⟨1152144088998250037918041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6144768474657333535562885 1152144088998250037918041)
              ·
                refine ⟨864108066748687528438531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1152144088998250037918041 864108066748687528438531)
                ·
                  refine ⟨1296162100123031292657797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 864108066748687528438531 1296162100123031292657797)
                  ·
                    refine ⟨243030393773068367373337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1296162100123031292657797 243030393773068367373337)
                    ·
                      rfl

theorem cell22_709950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 4, 2, 1, 4].length) (baseStart_709950 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_709950 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_709950 prefixEnd_709950 := by exact prefixLift 709950
  have htrace : WordTrace (prefixWord ++ tailWord_709950) baseStart_709950 baseEnd_709950 := by
    simpa [prefixWord, tailWord_709950, baseEnd_709950] using wordTrace_append hprefix tailTrace_709950
  have hstable : (prefixWord ++ tailWord_709950).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709950).length < 2 ^ (prefixWord ++ tailWord_709950).sum := by decide
  have hdescent : baseEnd_709950 < baseStart_709950 := by decide
  rcases family_descends (prefixWord ++ tailWord_709950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709958 : List Nat := [6, 1, 1, 3, 1, 2, 1, 3, 1, 3]
def baseStart_709958 : Nat := 118140960795 + 709958 * 2 ^ 59
def prefixEnd_709958 : Nat := 4983230072969 + 3 ^ 40 * 709958 * 2
def baseEnd_709958 : Nat := 243033132336559013173313

theorem tailTrace_709958 : CollatzResearch.WordTrace tailWord_709958 prefixEnd_709958 243033132336559013173313 := by
  unfold tailWord_709958
  simp only [CollatzResearch.WordTrace]
  refine ⟨809196736310965375569079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 17262863707967261345473685 809196736310965375569079)
  ·
    refine ⟨1213795104466448063353619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 809196736310965375569079 1213795104466448063353619)
    ·
      refine ⟨1820692656699672095030429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1213795104466448063353619 1820692656699672095030429)
      ·
        refine ⟨682759746262377035636411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1820692656699672095030429 682759746262377035636411)
        ·
          refine ⟨1024139619393565553454617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 682759746262377035636411 1024139619393565553454617)
          ·
            refine ⟨768104714545174165090963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1024139619393565553454617 768104714545174165090963)
            ·
              refine ⟨1152157071817761247636445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 768104714545174165090963 1152157071817761247636445)
              ·
                refine ⟨432058901931660467863667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1152157071817761247636445 432058901931660467863667)
                ·
                  refine ⟨648088352897490701795501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 432058901931660467863667 648088352897490701795501)
                  ·
                    refine ⟨243033132336559013173313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 648088352897490701795501 243033132336559013173313)
                    ·
                      rfl

theorem cell22_709958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 1, 3, 1, 3].length) (baseStart_709958 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_709958 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_709958 prefixEnd_709958 := by exact prefixLift 709958
  have htrace : WordTrace (prefixWord ++ tailWord_709958) baseStart_709958 baseEnd_709958 := by
    simpa [prefixWord, tailWord_709958, baseEnd_709958] using wordTrace_append hprefix tailTrace_709958
  have hstable : (prefixWord ++ tailWord_709958).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709958).length < 2 ^ (prefixWord ++ tailWord_709958).sum := by decide
  have hdescent : baseEnd_709958 < baseStart_709958 := by decide
  rcases family_descends (prefixWord ++ tailWord_709958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709961 : List Nat := [1, 2, 1, 1, 2, 3, 4, 1, 1, 6]
def baseStart_709961 : Nat := 118140960795 + 709961 * 2 ^ 59
def prefixEnd_709961 : Nat := 4983230072969 + 3 ^ 40 * 709961 * 2
def baseEnd_709961 : Nat := 243034159297868005348303

theorem tailTrace_709961 : CollatzResearch.WordTrace tailWord_709961 prefixEnd_709961 243034159297868005348303 := by
  unfold tailWord_709961
  simp only [CollatzResearch.WordTrace]
  refine ⟨25894404980940023530569737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17262936653960015687046491 25894404980940023530569737)
  ·
    refine ⟨19420803735705017647927303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25894404980940023530569737 19420803735705017647927303)
    ·
      refine ⟨29131205603557526471890955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19420803735705017647927303 29131205603557526471890955)
      ·
        refine ⟨43696808405336289707836433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29131205603557526471890955 43696808405336289707836433)
        ·
          refine ⟨32772606304002217280877325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43696808405336289707836433 32772606304002217280877325)
          ·
            refine ⟨12289727364000831480328997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32772606304002217280877325 12289727364000831480328997)
            ·
              refine ⟨2304323880750155902561687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12289727364000831480328997 2304323880750155902561687)
              ·
                refine ⟨3456485821125233853842531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2304323880750155902561687 3456485821125233853842531)
                ·
                  refine ⟨5184728731687850780763797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3456485821125233853842531 5184728731687850780763797)
                  ·
                    refine ⟨243034159297868005348303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5184728731687850780763797 243034159297868005348303)
                    ·
                      rfl

theorem cell22_709961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 1, 1, 6].length) (baseStart_709961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_709961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_709961 prefixEnd_709961 := by exact prefixLift 709961
  have htrace : WordTrace (prefixWord ++ tailWord_709961) baseStart_709961 baseEnd_709961 := by
    simpa [prefixWord, tailWord_709961, baseEnd_709961] using wordTrace_append hprefix tailTrace_709961
  have hstable : (prefixWord ++ tailWord_709961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709961).length < 2 ^ (prefixWord ++ tailWord_709961).sum := by decide
  have hdescent : baseEnd_709961 < baseStart_709961 := by decide
  rcases family_descends (prefixWord ++ tailWord_709961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709997 : List Nat := [1, 5, 1, 1, 1, 3, 4, 1, 2, 3]
def baseStart_709997 : Nat := 118140960795 + 709997 * 2 ^ 59
def prefixEnd_709997 : Nat := 4983230072969 + 3 ^ 40 * 709997 * 2
def baseEnd_709997 : Nat := 243046482833575911448193

theorem tailTrace_709997 : CollatzResearch.WordTrace tailWord_709997 prefixEnd_709997 243046482833575911448193 := by
  unfold tailWord_709997
  simp only [CollatzResearch.WordTrace]
  refine ⟨25895718008809601678880245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17263812005873067785920163 25895718008809601678880245)
  ·
    refine ⟨2427723563325900157395023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25895718008809601678880245 2427723563325900157395023)
    ·
      refine ⟨3641585344988850236092535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2427723563325900157395023 3641585344988850236092535)
      ·
        refine ⟨5462378017483275354138803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3641585344988850236092535 5462378017483275354138803)
        ·
          refine ⟨8193567026224913031208205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5462378017483275354138803 8193567026224913031208205)
          ·
            refine ⟨3072587634834342386703077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8193567026224913031208205 3072587634834342386703077)
            ·
              refine ⟨576110181531439197506827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3072587634834342386703077 576110181531439197506827)
              ·
                refine ⟨864165272297158796260241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 576110181531439197506827 864165272297158796260241)
                ·
                  refine ⟨648123954222869097195181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 864165272297158796260241 648123954222869097195181)
                  ·
                    refine ⟨243046482833575911448193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 648123954222869097195181 243046482833575911448193)
                    ·
                      rfl

theorem cell22_709997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 4, 1, 2, 3].length) (baseStart_709997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_709997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_709997 prefixEnd_709997 := by exact prefixLift 709997
  have htrace : WordTrace (prefixWord ++ tailWord_709997) baseStart_709997 baseEnd_709997 := by
    simpa [prefixWord, tailWord_709997, baseEnd_709997] using wordTrace_append hprefix tailTrace_709997
  have hstable : (prefixWord ++ tailWord_709997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709997).length < 2 ^ (prefixWord ++ tailWord_709997).sum := by decide
  have hdescent : baseEnd_709997 < baseStart_709997 := by decide
  rcases family_descends (prefixWord ++ tailWord_709997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710021 : List Nat := [1, 3, 1, 1, 3, 1, 2, 1, 9]
def baseStart_710021 : Nat := 118140960795 + 710021 * 2 ^ 59
def prefixEnd_710021 : Nat := 4983230072969 + 3 ^ 40 * 710021 * 2
def baseEnd_710021 : Nat := 81018232841349282949373

theorem tailTrace_710021 : CollatzResearch.WordTrace tailWord_710021 prefixEnd_710021 81018232841349282949373 := by
  unfold tailWord_710021
  simp only [CollatzResearch.WordTrace]
  refine ⟨25896593360722653777753917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17264395573815102518502611 25896593360722653777753917)
  ·
    refine ⟨9711222510270995166657719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25896593360722653777753917 9711222510270995166657719)
    ·
      refine ⟨14566833765406492749986579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9711222510270995166657719 14566833765406492749986579)
      ·
        refine ⟨21850250648109739124979869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14566833765406492749986579 21850250648109739124979869)
        ·
          refine ⟨8193843993041152171867451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21850250648109739124979869 8193843993041152171867451)
          ·
            refine ⟨12290765989561728257801177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8193843993041152171867451 12290765989561728257801177)
            ·
              refine ⟨9218074492171296193350883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12290765989561728257801177 9218074492171296193350883)
              ·
                refine ⟨13827111738256944290026325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9218074492171296193350883 13827111738256944290026325)
                ·
                  refine ⟨81018232841349282949373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 13827111738256944290026325 81018232841349282949373)
                  ·
                    rfl

theorem cell22_710021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 9].length) (baseStart_710021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_710021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_710021 prefixEnd_710021 := by exact prefixLift 710021
  have htrace : WordTrace (prefixWord ++ tailWord_710021) baseStart_710021 baseEnd_710021 := by
    simpa [prefixWord, tailWord_710021, baseEnd_710021] using wordTrace_append hprefix tailTrace_710021
  have hstable : (prefixWord ++ tailWord_710021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710021).length < 2 ^ (prefixWord ++ tailWord_710021).sum := by decide
  have hdescent : baseEnd_710021 < baseStart_710021 := by decide
  rcases family_descends (prefixWord ++ tailWord_710021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710042 : List Nat := [3, 1, 1, 4, 1, 1, 3, 4, 1, 3]
def baseStart_710042 : Nat := 118140960795 + 710042 * 2 ^ 59
def prefixEnd_710042 : Nat := 4983230072969 + 3 ^ 40 * 710042 * 2
def baseEnd_710042 : Nat := 243061887253210794073055

theorem tailTrace_710042 : CollatzResearch.WordTrace tailWord_710042 prefixEnd_710042 243061887253210794073055 := by
  unfold tailWord_710042
  simp only [CollatzResearch.WordTrace]
  refine ⟨6474339823411643591067095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17264906195764382909512253 6474339823411643591067095)
  ·
    refine ⟨9711509735117465386600643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6474339823411643591067095 9711509735117465386600643)
    ·
      refine ⟨14567264602676198079900965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9711509735117465386600643 14567264602676198079900965)
      ·
        refine ⟨2731362113001787139981431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14567264602676198079900965 2731362113001787139981431)
        ·
          refine ⟨4097043169502680709972147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2731362113001787139981431 4097043169502680709972147)
          ·
            refine ⟨6145564754254021064958221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4097043169502680709972147 6145564754254021064958221)
            ·
              refine ⟨2304586782845257899359333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6145564754254021064958221 2304586782845257899359333)
              ·
                refine ⟨432110021783485856129875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2304586782845257899359333 432110021783485856129875)
                ·
                  refine ⟨648165032675228784194813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 432110021783485856129875 648165032675228784194813)
                  ·
                    refine ⟨243061887253210794073055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 648165032675228784194813 243061887253210794073055)
                    ·
                      rfl

theorem cell22_710042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 4, 1, 3].length) (baseStart_710042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_710042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_710042 prefixEnd_710042 := by exact prefixLift 710042
  have htrace : WordTrace (prefixWord ++ tailWord_710042) baseStart_710042 baseEnd_710042 := by
    simpa [prefixWord, tailWord_710042, baseEnd_710042] using wordTrace_append hprefix tailTrace_710042
  have hstable : (prefixWord ++ tailWord_710042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710042).length < 2 ^ (prefixWord ++ tailWord_710042).sum := by decide
  have hdescent : baseEnd_710042 < baseStart_710042 := by decide
  rcases family_descends (prefixWord ++ tailWord_710042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710113 : List Nat := [1, 2, 3, 1, 2, 3, 1, 2, 1, 6]
def baseStart_710113 : Nat := 118140960795 + 710113 * 2 ^ 59
def prefixEnd_710113 : Nat := 4983230072969 + 3 ^ 40 * 710113 * 2
def baseEnd_710113 : Nat := 243086192004190275547837

theorem tailTrace_710113 : CollatzResearch.WordTrace tailWord_710113 prefixEnd_710113 243086192004190275547837 := by
  unfold tailWord_710113
  simp only [CollatzResearch.WordTrace]
  refine ⟨25899948876389353490102993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17266632584259568993401995 25899948876389353490102993)
  ·
    refine ⟨19424961657292015117577245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25899948876389353490102993 19424961657292015117577245)
    ·
      refine ⟨7284360621484505669091467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19424961657292015117577245 7284360621484505669091467)
      ·
        refine ⟨10926540932226758503637201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7284360621484505669091467 10926540932226758503637201)
        ·
          refine ⟨8194905699170068877727901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10926540932226758503637201 8194905699170068877727901)
          ·
            refine ⟨3073089637188775829147963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8194905699170068877727901 3073089637188775829147963)
            ·
              refine ⟨4609634455783163743721945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3073089637188775829147963 4609634455783163743721945)
              ·
                refine ⟨3457225841837372807791459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4609634455783163743721945 3457225841837372807791459)
                ·
                  refine ⟨5185838762756059211687189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3457225841837372807791459 5185838762756059211687189)
                  ·
                    refine ⟨243086192004190275547837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5185838762756059211687189 243086192004190275547837)
                    ·
                      rfl

theorem cell22_710113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 2, 1, 6].length) (baseStart_710113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_710113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_710113 prefixEnd_710113 := by exact prefixLift 710113
  have htrace : WordTrace (prefixWord ++ tailWord_710113) baseStart_710113 baseEnd_710113 := by
    simpa [prefixWord, tailWord_710113, baseEnd_710113] using wordTrace_append hprefix tailTrace_710113
  have hstable : (prefixWord ++ tailWord_710113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710113).length < 2 ^ (prefixWord ++ tailWord_710113).sum := by decide
  have hdescent : baseEnd_710113 < baseStart_710113 := by decide
  rcases family_descends (prefixWord ++ tailWord_710113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710115 : List Nat := [1, 1, 1, 6, 2, 1, 3, 1, 1, 5]
def baseStart_710115 : Nat := 118140960795 + 710115 * 2 ^ 59
def prefixEnd_710115 : Nat := 4983230072969 + 3 ^ 40 * 710115 * 2
def baseEnd_710115 : Nat := 243086876645062936997831

theorem tailTrace_710115 : CollatzResearch.WordTrace tailWord_710115 prefixEnd_710115 243086876645062936997831 := by
  unfold tailWord_710115
  simp only [CollatzResearch.WordTrace]
  refine ⟨25900021822382107831675799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17266681214921405221117199 25900021822382107831675799)
  ·
    refine ⟨38850032733573161747513699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25900021822382107831675799 38850032733573161747513699)
    ·
      refine ⟨58275049100359742621270549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38850032733573161747513699 58275049100359742621270549)
      ·
        refine ⟨2731642926579362935372057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 58275049100359742621270549 2731642926579362935372057)
        ·
          refine ⟨2048732194934522201529043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2731642926579362935372057 2048732194934522201529043)
          ·
            refine ⟨3073098292401783302293565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2048732194934522201529043 3073098292401783302293565)
            ·
              refine ⟨1152411859650668738360087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3073098292401783302293565 1152411859650668738360087)
              ·
                refine ⟨1728617789476003107540131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1152411859650668738360087 1728617789476003107540131)
                ·
                  refine ⟨2592926684214004661310197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1728617789476003107540131 2592926684214004661310197)
                  ·
                    refine ⟨243086876645062936997831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2592926684214004661310197 243086876645062936997831)
                    ·
                      rfl

theorem cell22_710115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 3, 1, 1, 5].length) (baseStart_710115 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_710115 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_710115 prefixEnd_710115 := by exact prefixLift 710115
  have htrace : WordTrace (prefixWord ++ tailWord_710115) baseStart_710115 baseEnd_710115 := by
    simpa [prefixWord, tailWord_710115, baseEnd_710115] using wordTrace_append hprefix tailTrace_710115
  have hstable : (prefixWord ++ tailWord_710115).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710115).length < 2 ^ (prefixWord ++ tailWord_710115).sum := by decide
  have hdescent : baseEnd_710115 < baseStart_710115 := by decide
  rcases family_descends (prefixWord ++ tailWord_710115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710128 : List Nat := [2, 1, 1, 1, 3, 5, 1, 8]
def baseStart_710128 : Nat := 118140960795 + 710128 * 2 ^ 59
def prefixEnd_710128 : Nat := 4983230072969 + 3 ^ 40 * 710128 * 2
def baseEnd_710128 : Nat := 27010147423415026269199

theorem tailTrace_710128 : CollatzResearch.WordTrace tailWord_710128 prefixEnd_710128 27010147423415026269199 := by
  unfold tailWord_710128
  simp only [CollatzResearch.WordTrace]
  refine ⟨12950247985667505525949519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17266997314223340701266025 12950247985667505525949519)
  ·
    refine ⟨19425371978501258288924279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12950247985667505525949519 19425371978501258288924279)
    ·
      refine ⟨29138057967751887433386419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19425371978501258288924279 29138057967751887433386419)
      ·
        refine ⟨43707086951627831150079629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29138057967751887433386419 43707086951627831150079629)
        ·
          refine ⟨16390157606860436681279861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43707086951627831150079629 16390157606860436681279861)
          ·
            refine ⟨1536577275643165938869987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16390157606860436681279861 1536577275643165938869987)
            ·
              refine ⟨2304865913464748908304981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1536577275643165938869987 2304865913464748908304981)
              ·
                refine ⟨27010147423415026269199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2304865913464748908304981 27010147423415026269199)
                ·
                  rfl

theorem cell22_710128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 8].length) (baseStart_710128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_710128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_710128 prefixEnd_710128 := by exact prefixLift 710128
  have htrace : WordTrace (prefixWord ++ tailWord_710128) baseStart_710128 baseEnd_710128 := by
    simpa [prefixWord, tailWord_710128, baseEnd_710128] using wordTrace_append hprefix tailTrace_710128
  have hstable : (prefixWord ++ tailWord_710128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710128).length < 2 ^ (prefixWord ++ tailWord_710128).sum := by decide
  have hdescent : baseEnd_710128 < baseStart_710128 := by decide
  rcases family_descends (prefixWord ++ tailWord_710128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710130 : List Nat := [3, 2, 1, 4, 1, 1, 2, 1, 1, 6]
def baseStart_710130 : Nat := 118140960795 + 710130 * 2 ^ 59
def prefixEnd_710130 : Nat := 4983230072969 + 3 ^ 40 * 710130 * 2
def baseEnd_710130 : Nat := 243092011451607897872785

theorem tailTrace_710130 : CollatzResearch.WordTrace tailWord_710130 prefixEnd_710130 243092011451607897872785 := by
  unfold tailWord_710130
  simp only [CollatzResearch.WordTrace]
  refine ⟨6475142229331941348367961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17267045944885176928981229 6475142229331941348367961)
  ·
    refine ⟨4856356671998956011275971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6475142229331941348367961 4856356671998956011275971)
    ·
      refine ⟨7284535007998434016913957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4856356671998956011275971 7284535007998434016913957)
      ·
        refine ⟨1365850313999706378171367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7284535007998434016913957 1365850313999706378171367)
        ·
          refine ⟨2048775470999559567257051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1365850313999706378171367 2048775470999559567257051)
          ·
            refine ⟨3073163206499339350885577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2048775470999559567257051 3073163206499339350885577)
            ·
              refine ⟨2304872404874504513164183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3073163206499339350885577 2304872404874504513164183)
              ·
                refine ⟨3457308607311756769746275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2304872404874504513164183 3457308607311756769746275)
                ·
                  refine ⟨5185962910967635154619413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3457308607311756769746275 5185962910967635154619413)
                  ·
                    refine ⟨243092011451607897872785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5185962910967635154619413 243092011451607897872785)
                    ·
                      rfl

theorem cell22_710130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 1, 1, 6].length) (baseStart_710130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_710130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_710130 prefixEnd_710130 := by exact prefixLift 710130
  have htrace : WordTrace (prefixWord ++ tailWord_710130) baseStart_710130 baseEnd_710130 := by
    simpa [prefixWord, tailWord_710130, baseEnd_710130] using wordTrace_append hprefix tailTrace_710130
  have hstable : (prefixWord ++ tailWord_710130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710130).length < 2 ^ (prefixWord ++ tailWord_710130).sum := by decide
  have hdescent : baseEnd_710130 < baseStart_710130 := by decide
  rcases family_descends (prefixWord ++ tailWord_710130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710134 : List Nat := [5, 1, 1, 1, 2, 4, 1, 3, 4]
def baseStart_710134 : Nat := 118140960795 + 710134 * 2 ^ 59
def prefixEnd_710134 : Nat := 4983230072969 + 3 ^ 40 * 710134 * 2
def baseEnd_710134 : Nat := 81031126911117740257591

theorem tailTrace_710134 : CollatzResearch.WordTrace tailWord_710134 prefixEnd_710134 81031126911117740257591 := by
  unfold tailWord_710134
  simp only [CollatzResearch.WordTrace]
  refine ⟨1618794675582079629788591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17267143206208849384411637 1618794675582079629788591)
  ·
    refine ⟨2428192013373119444682887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1618794675582079629788591 2428192013373119444682887)
    ·
      refine ⟨3642288020059679167024331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2428192013373119444682887 3642288020059679167024331)
      ·
        refine ⟨5463432030089518750536497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3642288020059679167024331 5463432030089518750536497)
        ·
          refine ⟨4097574022567139062902373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5463432030089518750536497 4097574022567139062902373)
          ·
            refine ⟨768295129231338574294195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4097574022567139062902373 768295129231338574294195)
            ·
              refine ⟨1152442693847007861441293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 768295129231338574294195 1152442693847007861441293)
              ·
                refine ⟨432166010192627948040485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1152442693847007861441293 432166010192627948040485)
                ·
                  refine ⟨81031126911117740257591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 432166010192627948040485 81031126911117740257591)
                  ·
                    rfl

theorem cell22_710134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 1, 3, 4].length) (baseStart_710134 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_710134 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_710134 prefixEnd_710134 := by exact prefixLift 710134
  have htrace : WordTrace (prefixWord ++ tailWord_710134) baseStart_710134 baseEnd_710134 := by
    simpa [prefixWord, tailWord_710134, baseEnd_710134] using wordTrace_append hprefix tailTrace_710134
  have hstable : (prefixWord ++ tailWord_710134).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710134).length < 2 ^ (prefixWord ++ tailWord_710134).sum := by decide
  have hdescent : baseEnd_710134 < baseStart_710134 := by decide
  rcases family_descends (prefixWord ++ tailWord_710134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710145 : List Nat := [1, 2, 4, 1, 4, 2, 8]
def baseStart_710145 : Nat := 118140960795 + 710145 * 2 ^ 59
def prefixEnd_710145 : Nat := 4983230072969 + 3 ^ 40 * 710145 * 2
def baseEnd_710145 : Nat := 9003598009561216990657

theorem tailTrace_710145 : CollatzResearch.WordTrace tailWord_710145 prefixEnd_710145 9003598009561216990657 := by
  unfold tailWord_710145
  simp only [CollatzResearch.WordTrace]
  refine ⟨25901116012273422955267889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17267410674848948636845259 25901116012273422955267889)
  ·
    refine ⟨19425837009205067216450917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25901116012273422955267889 19425837009205067216450917)
    ·
      refine ⟨3642344439225950103084547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19425837009205067216450917 3642344439225950103084547)
      ·
        refine ⟨5463516658838925154626821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3642344439225950103084547 5463516658838925154626821)
        ·
          refine ⟨1024409373532298466492529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5463516658838925154626821 1024409373532298466492529)
          ·
            refine ⟨768307030149223849869397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1024409373532298466492529 768307030149223849869397)
            ·
              refine ⟨9003598009561216990657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 768307030149223849869397 9003598009561216990657)
              ·
                rfl

theorem cell22_710145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 8].length) (baseStart_710145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_710145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_710145 prefixEnd_710145 := by exact prefixLift 710145
  have htrace : WordTrace (prefixWord ++ tailWord_710145) baseStart_710145 baseEnd_710145 := by
    simpa [prefixWord, tailWord_710145, baseEnd_710145] using wordTrace_append hprefix tailTrace_710145
  have hstable : (prefixWord ++ tailWord_710145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710145).length < 2 ^ (prefixWord ++ tailWord_710145).sum := by decide
  have hdescent : baseEnd_710145 < baseStart_710145 := by decide
  rcases family_descends (prefixWord ++ tailWord_710145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710188 : List Nat := [2, 2, 1, 1, 1, 2, 1, 1, 6, 5]
def baseStart_710188 : Nat := 118140960795 + 710188 * 2 ^ 59
def prefixEnd_710188 : Nat := 4983230072969 + 3 ^ 40 * 710188 * 2
def baseEnd_710188 : Nat := 243111866036915079922607

theorem tailTrace_710188 : CollatzResearch.WordTrace tailWord_710188 prefixEnd_710188 243111866036915079922607 := by
  unfold tailWord_710188
  simp only [CollatzResearch.WordTrace]
  refine ⟨12951342175558820649541609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17268456234078427532722145 12951342175558820649541609)
  ·
    refine ⟨9713506631669115487156207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12951342175558820649541609 9713506631669115487156207)
    ·
      refine ⟨14570259947503673230734311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9713506631669115487156207 14570259947503673230734311)
      ·
        refine ⟨21855389921255509846101467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14570259947503673230734311 21855389921255509846101467)
        ·
          refine ⟨32783084881883264769152201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21855389921255509846101467 32783084881883264769152201)
          ·
            refine ⟨24587313661412448576864151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32783084881883264769152201 24587313661412448576864151)
            ·
              refine ⟨36880970492118672865296227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24587313661412448576864151 36880970492118672865296227)
              ·
                refine ⟨55321455738178009297944341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36880970492118672865296227 55321455738178009297944341)
                ·
                  refine ⟨2593193237727094185841141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 55321455738178009297944341 2593193237727094185841141)
                  ·
                    refine ⟨243111866036915079922607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2593193237727094185841141 243111866036915079922607)
                    ·
                      rfl

theorem cell22_710188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 5].length) (baseStart_710188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_710188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_710188 prefixEnd_710188 := by exact prefixLift 710188
  have htrace : WordTrace (prefixWord ++ tailWord_710188) baseStart_710188 baseEnd_710188 := by
    simpa [prefixWord, tailWord_710188, baseEnd_710188] using wordTrace_append hprefix tailTrace_710188
  have hstable : (prefixWord ++ tailWord_710188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710188).length < 2 ^ (prefixWord ++ tailWord_710188).sum := by decide
  have hdescent : baseEnd_710188 < baseStart_710188 := by decide
  rcases family_descends (prefixWord ++ tailWord_710188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710220 : List Nat := [2, 2, 1, 3, 1, 3, 1, 2, 3, 4]
def baseStart_710220 : Nat := 118140960795 + 710220 * 2 ^ 59
def prefixEnd_710220 : Nat := 4983230072969 + 3 ^ 40 * 710220 * 2
def baseEnd_710220 : Nat := 243122820290877663122509

theorem tailTrace_710220 : CollatzResearch.WordTrace tailWord_710220 prefixEnd_710220 243122820290877663122509 := by
  unfold tailWord_710220
  simp only [CollatzResearch.WordTrace]
  refine ⟨12951925743500855382124057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17269234324667807176165409 12951925743500855382124057)
  ·
    refine ⟨9713944307625641536593043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12951925743500855382124057 9713944307625641536593043)
    ·
      refine ⟨14570916461438462304889565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9713944307625641536593043 14570916461438462304889565)
      ·
        refine ⟨5464093673039423364333587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14570916461438462304889565 5464093673039423364333587)
        ·
          refine ⟨8196140509559135046500381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5464093673039423364333587 8196140509559135046500381)
          ·
            refine ⟨3073552691084675642437643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8196140509559135046500381 3073552691084675642437643)
            ·
              refine ⟨4610329036627013463656465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3073552691084675642437643 4610329036627013463656465)
              ·
                refine ⟨3457746777470260097742349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4610329036627013463656465 3457746777470260097742349)
                ·
                  refine ⟨1296655041551347536653381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3457746777470260097742349 1296655041551347536653381)
                  ·
                    refine ⟨243122820290877663122509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1296655041551347536653381 243122820290877663122509)
                    ·
                      rfl

theorem cell22_710220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 2, 3, 4].length) (baseStart_710220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_710220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_710220 prefixEnd_710220 := by exact prefixLift 710220
  have htrace : WordTrace (prefixWord ++ tailWord_710220) baseStart_710220 baseEnd_710220 := by
    simpa [prefixWord, tailWord_710220, baseEnd_710220] using wordTrace_append hprefix tailTrace_710220
  have hstable : (prefixWord ++ tailWord_710220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710220).length < 2 ^ (prefixWord ++ tailWord_710220).sum := by decide
  have hdescent : baseEnd_710220 < baseStart_710220 := by decide
  rcases family_descends (prefixWord ++ tailWord_710220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710254 : List Nat := [4, 1, 2, 2, 3, 1, 1, 3, 1, 4]
def baseStart_710254 : Nat := 118140960795 + 710254 * 2 ^ 59
def prefixEnd_710254 : Nat := 4983230072969 + 3 ^ 40 * 710254 * 2
def baseEnd_710254 : Nat := 243134459185712907772405

theorem tailTrace_710254 : CollatzResearch.WordTrace tailWord_710254 prefixEnd_710254 243134459185712907772405 := by
  unfold tailWord_710254
  simp only [CollatzResearch.WordTrace]
  refine ⟨3238136446109816821373227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17270061045919023047323877 3238136446109816821373227)
  ·
    refine ⟨4857204669164725232059841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3238136446109816821373227 4857204669164725232059841)
    ·
      refine ⟨3642903501873543924044881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4857204669164725232059841 3642903501873543924044881)
      ·
        refine ⟨2732177626405157943033661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3642903501873543924044881 2732177626405157943033661)
        ·
          refine ⟨1024566609901934228637623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2732177626405157943033661 1024566609901934228637623)
          ·
            refine ⟨1536849914852901342956435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1024566609901934228637623 1536849914852901342956435)
            ·
              refine ⟨2305274872279352014434653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1536849914852901342956435 2305274872279352014434653)
              ·
                refine ⟨864478077104757005412995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2305274872279352014434653 864478077104757005412995)
                ·
                  refine ⟨1296717115657135508119493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 864478077104757005412995 1296717115657135508119493)
                  ·
                    refine ⟨243134459185712907772405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1296717115657135508119493 243134459185712907772405)
                    ·
                      rfl

theorem cell22_710254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 3, 1, 4].length) (baseStart_710254 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_710254 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_710254 prefixEnd_710254 := by exact prefixLift 710254
  have htrace : WordTrace (prefixWord ++ tailWord_710254) baseStart_710254 baseEnd_710254 := by
    simpa [prefixWord, tailWord_710254, baseEnd_710254] using wordTrace_append hprefix tailTrace_710254
  have hstable : (prefixWord ++ tailWord_710254).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710254).length < 2 ^ (prefixWord ++ tailWord_710254).sum := by decide
  have hdescent : baseEnd_710254 < baseStart_710254 := by decide
  rcases family_descends (prefixWord ++ tailWord_710254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710265 : List Nat := [1, 2, 1, 3, 3, 1, 2, 1, 4, 4]
def baseStart_710265 : Nat := 118140960795 + 710265 * 2 ^ 59
def prefixEnd_710265 : Nat := 4983230072969 + 3 ^ 40 * 710265 * 2
def baseEnd_710265 : Nat := 243138224710512545747371

theorem tailTrace_710265 : CollatzResearch.WordTrace tailWord_710265 prefixEnd_710265 243138224710512545747371 := by
  unfold tailWord_710265
  simp only [CollatzResearch.WordTrace]
  refine ⟨25905492771838683449636249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17270328514559122299757499 25905492771838683449636249)
  ·
    refine ⟨19429119578879012587227187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25905492771838683449636249 19429119578879012587227187)
    ·
      refine ⟨29143679368318518880840781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19429119578879012587227187 29143679368318518880840781)
      ·
        refine ⟨10928879763119444580315293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29143679368318518880840781 10928879763119444580315293)
        ·
          refine ⟨4098329911169791717618235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10928879763119444580315293 4098329911169791717618235)
          ·
            refine ⟨6147494866754687576427353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4098329911169791717618235 6147494866754687576427353)
            ·
              refine ⟨4610621150066015682320515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6147494866754687576427353 4610621150066015682320515)
              ·
                refine ⟨6915931725099023523480773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4610621150066015682320515 6915931725099023523480773)
                ·
                  refine ⟨1296737198456066910652645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6915931725099023523480773 1296737198456066910652645)
                  ·
                    refine ⟨243138224710512545747371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1296737198456066910652645 243138224710512545747371)
                    ·
                      rfl

theorem cell22_710265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 1, 4, 4].length) (baseStart_710265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_710265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_710265 prefixEnd_710265 := by exact prefixLift 710265
  have htrace : WordTrace (prefixWord ++ tailWord_710265) baseStart_710265 baseEnd_710265 := by
    simpa [prefixWord, tailWord_710265, baseEnd_710265] using wordTrace_append hprefix tailTrace_710265
  have hstable : (prefixWord ++ tailWord_710265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710265).length < 2 ^ (prefixWord ++ tailWord_710265).sum := by decide
  have hdescent : baseEnd_710265 < baseStart_710265 := by decide
  rcases family_descends (prefixWord ++ tailWord_710265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710284 : List Nat := [2, 2, 1, 2, 1, 1, 7, 1, 2, 3]
def baseStart_710284 : Nat := 118140960795 + 710284 * 2 ^ 59
def prefixEnd_710284 : Nat := 4983230072969 + 3 ^ 40 * 710284 * 2
def baseEnd_710284 : Nat := 243144728798802829522313

theorem tailTrace_710284 : CollatzResearch.WordTrace tailWord_710284 prefixEnd_710284 243144728798802829522313 := by
  unfold tailWord_710284
  simp only [CollatzResearch.WordTrace]
  refine ⟨12953092879384924847288953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17270790505846566463051937 12953092879384924847288953)
  ·
    refine ⟨9714819659538693635466715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12953092879384924847288953 9714819659538693635466715)
    ·
      refine ⟨14572229489308040453200073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9714819659538693635466715 14572229489308040453200073)
      ·
        refine ⟨10929172116981030339900055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14572229489308040453200073 10929172116981030339900055)
        ·
          refine ⟨16393758175471545509850083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10929172116981030339900055 16393758175471545509850083)
          ·
            refine ⟨24590637263207318264775125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16393758175471545509850083 24590637263207318264775125)
            ·
              refine ⟨576343060856421521830667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 24590637263207318264775125 576343060856421521830667)
              ·
                refine ⟨864514591284632282746001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 576343060856421521830667 864514591284632282746001)
                ·
                  refine ⟨648385943463474212059501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 864514591284632282746001 648385943463474212059501)
                  ·
                    refine ⟨243144728798802829522313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 648385943463474212059501 243144728798802829522313)
                    ·
                      rfl

theorem cell22_710284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 7, 1, 2, 3].length) (baseStart_710284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_710284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_710284 prefixEnd_710284 := by exact prefixLift 710284
  have htrace : WordTrace (prefixWord ++ tailWord_710284) baseStart_710284 baseEnd_710284 := by
    simpa [prefixWord, tailWord_710284, baseEnd_710284] using wordTrace_append hprefix tailTrace_710284
  have hstable : (prefixWord ++ tailWord_710284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710284).length < 2 ^ (prefixWord ++ tailWord_710284).sum := by decide
  have hdescent : baseEnd_710284 < baseStart_710284 := by decide
  rcases family_descends (prefixWord ++ tailWord_710284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710303 : List Nat := [1, 1, 2, 7, 2, 1, 1, 3, 4]
def baseStart_710303 : Nat := 118140960795 + 710303 * 2 ^ 59
def prefixEnd_710303 : Nat := 4983230072969 + 3 ^ 40 * 710303 * 2
def baseEnd_710303 : Nat := 81050410962364371099085

theorem tailTrace_710303 : CollatzResearch.WordTrace tailWord_710303 prefixEnd_710303 81050410962364371099085 := by
  unfold tailWord_710303
  simp only [CollatzResearch.WordTrace]
  refine ⟨25906878745701015939519563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17271252497134010626346375 25906878745701015939519563)
  ·
    refine ⟨38860318118551523909279345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25906878745701015939519563 38860318118551523909279345)
    ·
      refine ⟨29145238588913642931959509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38860318118551523909279345 29145238588913642931959509)
      ·
        refine ⟨683091529427663506217801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 29145238588913642931959509 683091529427663506217801)
        ·
          refine ⟨512318647070747629663351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 683091529427663506217801 512318647070747629663351)
          ·
            refine ⟨768477970606121444495027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 512318647070747629663351 768477970606121444495027)
            ·
              refine ⟨1152716955909182166742541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 768477970606121444495027 1152716955909182166742541)
              ·
                refine ⟨432268858465943312528453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1152716955909182166742541 432268858465943312528453)
                ·
                  refine ⟨81050410962364371099085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 432268858465943312528453 81050410962364371099085)
                  ·
                    rfl

theorem cell22_710303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 1, 3, 4].length) (baseStart_710303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_710303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_710303 prefixEnd_710303 := by exact prefixLift 710303
  have htrace : WordTrace (prefixWord ++ tailWord_710303) baseStart_710303 baseEnd_710303 := by
    simpa [prefixWord, tailWord_710303, baseEnd_710303] using wordTrace_append hprefix tailTrace_710303
  have hstable : (prefixWord ++ tailWord_710303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710303).length < 2 ^ (prefixWord ++ tailWord_710303).sum := by decide
  have hdescent : baseEnd_710303 < baseStart_710303 := by decide
  rcases family_descends (prefixWord ++ tailWord_710303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710329 : List Nat := [1, 2, 1, 4, 1, 1, 2, 6, 1, 3]
def baseStart_710329 : Nat := 118140960795 + 710329 * 2 ^ 59
def prefixEnd_710329 : Nat := 4983230072969 + 3 ^ 40 * 710329 * 2
def baseEnd_710329 : Nat := 243160133218437712147175

theorem tailTrace_710329 : CollatzResearch.WordTrace tailWord_710329 prefixEnd_710329 243160133218437712147175 := by
  unfold tailWord_710329
  simp only [CollatzResearch.WordTrace]
  refine ⟨25907827043606822379966041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17271884695737881586644027 25907827043606822379966041)
  ·
    refine ⟨19430870282705116784974531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25907827043606822379966041 19430870282705116784974531)
    ·
      refine ⟨29146305424057675177461797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19430870282705116784974531 29146305424057675177461797)
      ·
        refine ⟨5464932267010814095774087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29146305424057675177461797 5464932267010814095774087)
        ·
          refine ⟨8197398400516221143661131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5464932267010814095774087 8197398400516221143661131)
          ·
            refine ⟨12296097600774331715491697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8197398400516221143661131 12296097600774331715491697)
            ·
              refine ⟨9222073200580748786618773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12296097600774331715491697 9222073200580748786618773)
              ·
                refine ⟨432284681277222599372755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9222073200580748786618773 432284681277222599372755)
                ·
                  refine ⟨648427021915833899059133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 432284681277222599372755 648427021915833899059133)
                  ·
                    refine ⟨243160133218437712147175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 648427021915833899059133 243160133218437712147175)
                    ·
                      rfl

theorem cell22_710329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 6, 1, 3].length) (baseStart_710329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_710329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_710329 prefixEnd_710329 := by exact prefixLift 710329
  have htrace : WordTrace (prefixWord ++ tailWord_710329) baseStart_710329 baseEnd_710329 := by
    simpa [prefixWord, tailWord_710329, baseEnd_710329] using wordTrace_append hprefix tailTrace_710329
  have hstable : (prefixWord ++ tailWord_710329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710329).length < 2 ^ (prefixWord ++ tailWord_710329).sum := by decide
  have hdescent : baseEnd_710329 < baseStart_710329 := by decide
  rcases family_descends (prefixWord ++ tailWord_710329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710400 : List Nat := [2, 1, 1, 2, 1, 1, 2, 3, 3, 6]
def baseStart_710400 : Nat := 118140960795 + 710400 * 2 ^ 59
def prefixEnd_710400 : Nat := 4983230072969 + 3 ^ 40 * 710400 * 2
def baseEnd_710400 : Nat := 243184437969417193621957

theorem tailTrace_710400 : CollatzResearch.WordTrace tailWord_710400 prefixEnd_710400 243184437969417193621957 := by
  unfold tailWord_710400
  simp only [CollatzResearch.WordTrace]
  refine ⟨12955208313174800752900327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17273611084233067670533769 12955208313174800752900327)
  ·
    refine ⟨19432812469762201129350491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12955208313174800752900327 19432812469762201129350491)
    ·
      refine ⟨29149218704643301694025737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19432812469762201129350491 29149218704643301694025737)
      ·
        refine ⟨21861914028482476270519303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29149218704643301694025737 21861914028482476270519303)
        ·
          refine ⟨32792871042723714405778955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21861914028482476270519303 32792871042723714405778955)
          ·
            refine ⟨49189306564085571608668433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32792871042723714405778955 49189306564085571608668433)
            ·
              refine ⟨36891979923064178706501325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49189306564085571608668433 36891979923064178706501325)
              ·
                refine ⟨13834492471149067014937997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36891979923064178706501325 13834492471149067014937997)
                ·
                  refine ⟨5187934676680900130601749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13834492471149067014937997 5187934676680900130601749)
                  ·
                    refine ⟨243184437969417193621957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5187934676680900130601749 243184437969417193621957)
                    ·
                      rfl

theorem cell22_710400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 3, 6].length) (baseStart_710400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_710400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_710400 prefixEnd_710400 := by exact prefixLift 710400
  have htrace : WordTrace (prefixWord ++ tailWord_710400) baseStart_710400 baseEnd_710400 := by
    simpa [prefixWord, tailWord_710400, baseEnd_710400] using wordTrace_append hprefix tailTrace_710400
  have hstable : (prefixWord ++ tailWord_710400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710400).length < 2 ^ (prefixWord ++ tailWord_710400).sum := by decide
  have hdescent : baseEnd_710400 < baseStart_710400 := by decide
  rcases family_descends (prefixWord ++ tailWord_710400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710436 : List Nat := [2, 3, 1, 3, 2, 1, 3, 2, 2, 3]
def baseStart_710436 : Nat := 118140960795 + 710436 * 2 ^ 59
def prefixEnd_710436 : Nat := 4983230072969 + 3 ^ 40 * 710436 * 2
def baseEnd_710436 : Nat := 243196761505125099721847

theorem tailTrace_710436 : CollatzResearch.WordTrace tailWord_710436 prefixEnd_710436 243196761505125099721847 := by
  unfold tailWord_710436
  simp only [CollatzResearch.WordTrace]
  refine ⟨12955864827109589827055581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17274486436146119769407441 12955864827109589827055581)
  ·
    refine ⟨4858449310166096185145843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12955864827109589827055581 4858449310166096185145843)
    ·
      refine ⟨7287673965249144277718765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4858449310166096185145843 7287673965249144277718765)
      ·
        refine ⟨2732877736968429104144537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7287673965249144277718765 2732877736968429104144537)
        ·
          refine ⟨2049658302726321828108403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2732877736968429104144537 2049658302726321828108403)
          ·
            refine ⟨3074487454089482742162605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2049658302726321828108403 3074487454089482742162605)
            ·
              refine ⟨1152932795283556028310977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3074487454089482742162605 1152932795283556028310977)
              ·
                refine ⟨864699596462667021233233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1152932795283556028310977 864699596462667021233233)
                ·
                  refine ⟨648524697347000265924925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 864699596462667021233233 648524697347000265924925)
                  ·
                    refine ⟨243196761505125099721847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 648524697347000265924925 243196761505125099721847)
                    ·
                      rfl

theorem cell22_710436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 3, 2, 2, 3].length) (baseStart_710436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_710436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_710436 prefixEnd_710436 := by exact prefixLift 710436
  have htrace : WordTrace (prefixWord ++ tailWord_710436) baseStart_710436 baseEnd_710436 := by
    simpa [prefixWord, tailWord_710436, baseEnd_710436] using wordTrace_append hprefix tailTrace_710436
  have hstable : (prefixWord ++ tailWord_710436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710436).length < 2 ^ (prefixWord ++ tailWord_710436).sum := by decide
  have hdescent : baseEnd_710436 < baseStart_710436 := by decide
  rcases family_descends (prefixWord ++ tailWord_710436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710447 : List Nat := [1, 1, 2, 1, 2, 1, 2, 2, 7, 3]
def baseStart_710447 : Nat := 118140960795 + 710447 * 2 ^ 59
def prefixEnd_710447 : Nat := 4983230072969 + 3 ^ 40 * 710447 * 2
def baseEnd_710447 : Nat := 243200527029924737696813

theorem tailTrace_710447 : CollatzResearch.WordTrace tailWord_710447 prefixEnd_710447 243200527029924737696813 := by
  unfold tailWord_710447
  simp only [CollatzResearch.WordTrace]
  refine ⟨25912130857179328532761595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17274753904786219021841063 25912130857179328532761595)
  ·
    refine ⟨38868196285768992799142393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25912130857179328532761595 38868196285768992799142393)
    ·
      refine ⟨29151147214326744599356795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38868196285768992799142393 29151147214326744599356795)
      ·
        refine ⟨43726720821490116899035193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29151147214326744599356795 43726720821490116899035193)
        ·
          refine ⟨32795040616117587674276395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43726720821490116899035193 32795040616117587674276395)
          ·
            refine ⟨49192560924176381511414593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32795040616117587674276395 49192560924176381511414593)
            ·
              refine ⟨36894420693132286133560945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49192560924176381511414593 36894420693132286133560945)
              ·
                refine ⟨27670815519849214600170709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36894420693132286133560945 27670815519849214600170709)
                ·
                  refine ⟨648534738746465967191501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 27670815519849214600170709 648534738746465967191501)
                  ·
                    refine ⟨243200527029924737696813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 648534738746465967191501 243200527029924737696813)
                    ·
                      rfl

theorem cell22_710447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 7, 3].length) (baseStart_710447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_710447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_710447 prefixEnd_710447 := by exact prefixLift 710447
  have htrace : WordTrace (prefixWord ++ tailWord_710447) baseStart_710447 baseEnd_710447 := by
    simpa [prefixWord, tailWord_710447, baseEnd_710447] using wordTrace_append hprefix tailTrace_710447
  have hstable : (prefixWord ++ tailWord_710447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710447).length < 2 ^ (prefixWord ++ tailWord_710447).sum := by decide
  have hdescent : baseEnd_710447 < baseStart_710447 := by decide
  rcases family_descends (prefixWord ++ tailWord_710447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710453 : List Nat := [1, 3, 3, 1, 4, 1, 3, 1, 2, 3]
def baseStart_710453 : Nat := 118140960795 + 710453 * 2 ^ 59
def prefixEnd_710453 : Nat := 4983230072969 + 3 ^ 40 * 710453 * 2
def baseEnd_710453 : Nat := 243202580952542722046795

theorem tailTrace_710453 : CollatzResearch.WordTrace tailWord_710453 prefixEnd_710453 243202580952542722046795 := by
  unfold tailWord_710453
  simp only [CollatzResearch.WordTrace]
  refine ⟨25912349695157591557480013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17274899796771727704986675 25912349695157591557480013)
  ·
    refine ⟨9717131135684096834055005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25912349695157591557480013 9717131135684096834055005)
    ·
      refine ⟨3643924175881536312770627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9717131135684096834055005 3643924175881536312770627)
      ·
        refine ⟨5465886263822304469155941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3643924175881536312770627 5465886263822304469155941)
        ·
          refine ⟨1024853674466682087966739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5465886263822304469155941 1024853674466682087966739)
          ·
            refine ⟨1537280511700023131950109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1024853674466682087966739 1537280511700023131950109)
            ·
              refine ⟨576480191887508674481291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1537280511700023131950109 576480191887508674481291)
              ·
                refine ⟨864720287831263011721937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 576480191887508674481291 864720287831263011721937)
                ·
                  refine ⟨648540215873447258791453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 864720287831263011721937 648540215873447258791453)
                  ·
                    refine ⟨243202580952542722046795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 648540215873447258791453 243202580952542722046795)
                    ·
                      rfl

theorem cell22_710453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 3, 1, 2, 3].length) (baseStart_710453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_710453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_710453 prefixEnd_710453 := by exact prefixLift 710453
  have htrace : WordTrace (prefixWord ++ tailWord_710453) baseStart_710453 baseEnd_710453 := by
    simpa [prefixWord, tailWord_710453, baseEnd_710453] using wordTrace_append hprefix tailTrace_710453
  have hstable : (prefixWord ++ tailWord_710453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710453).length < 2 ^ (prefixWord ++ tailWord_710453).sum := by decide
  have hdescent : baseEnd_710453 < baseStart_710453 := by decide
  rcases family_descends (prefixWord ++ tailWord_710453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710498 : List Nat := [3, 3, 2, 1, 2, 3, 1, 1, 3, 3]
def baseStart_710498 : Nat := 118140960795 + 710498 * 2 ^ 59
def prefixEnd_710498 : Nat := 4983230072969 + 3 ^ 40 * 710498 * 2
def baseEnd_710498 : Nat := 243217985372177604671657

theorem tailTrace_710498 : CollatzResearch.WordTrace tailWord_710498 prefixEnd_710498 243217985372177604671657 := by
  unfold tailWord_710498
  simp only [CollatzResearch.WordTrace]
  refine ⟨6478497744998641060717037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17275993986663042828578765 6478497744998641060717037)
  ·
    refine ⟨2429436654374490397768889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6478497744998641060717037 2429436654374490397768889)
    ·
      refine ⟨1822077490780867798326667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2429436654374490397768889 1822077490780867798326667)
      ·
        refine ⟨2733116236171301697490001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1822077490780867798326667 2733116236171301697490001)
        ·
          refine ⟨2049837177128476273117501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2733116236171301697490001 2049837177128476273117501)
          ·
            refine ⟨768688941423178602419063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2049837177128476273117501 768688941423178602419063)
            ·
              refine ⟨1153033412134767903628595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 768688941423178602419063 1153033412134767903628595)
              ·
                refine ⟨1729550118202151855442893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1153033412134767903628595 1729550118202151855442893)
                ·
                  refine ⟨648581294325806945791085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1729550118202151855442893 648581294325806945791085)
                  ·
                    refine ⟨243217985372177604671657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 648581294325806945791085 243217985372177604671657)
                    ·
                      rfl

theorem cell22_710498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 1, 1, 3, 3].length) (baseStart_710498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_710498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_710498 prefixEnd_710498 := by exact prefixLift 710498
  have htrace : WordTrace (prefixWord ++ tailWord_710498) baseStart_710498 baseEnd_710498 := by
    simpa [prefixWord, tailWord_710498, baseEnd_710498] using wordTrace_append hprefix tailTrace_710498
  have hstable : (prefixWord ++ tailWord_710498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710498).length < 2 ^ (prefixWord ++ tailWord_710498).sum := by decide
  have hdescent : baseEnd_710498 < baseStart_710498 := by decide
  rcases family_descends (prefixWord ++ tailWord_710498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710507 : List Nat := [1, 1, 1, 1, 2, 2, 3, 4, 3, 4]
def baseStart_710507 : Nat := 118140960795 + 710507 * 2 ^ 59
def prefixEnd_710507 : Nat := 4983230072969 + 3 ^ 40 * 710507 * 2
def baseEnd_710507 : Nat := 243221066256104581196629

theorem tailTrace_710507 : CollatzResearch.WordTrace tailWord_710507 prefixEnd_710507 243221066256104581196629 := by
  unfold tailWord_710507
  simp only [CollatzResearch.WordTrace]
  refine ⟨25914319236961958779945775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17276212824641305853297183 25914319236961958779945775)
  ·
    refine ⟨38871478855442938169918663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25914319236961958779945775 38871478855442938169918663)
    ·
      refine ⟨58307218283164407254877995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38871478855442938169918663 58307218283164407254877995)
      ·
        refine ⟨87460827424746610882316993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58307218283164407254877995 87460827424746610882316993)
        ·
          refine ⟨65595620568559958161737745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87460827424746610882316993 65595620568559958161737745)
          ·
            refine ⟨49196715426419968621303309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65595620568559958161737745 49196715426419968621303309)
            ·
              refine ⟨18448768284907488232988741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49196715426419968621303309 18448768284907488232988741)
              ·
                refine ⟨3459144053420154043685389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18448768284907488232988741 3459144053420154043685389)
                ·
                  refine ⟨1297179020032557766382021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3459144053420154043685389 1297179020032557766382021)
                  ·
                    refine ⟨243221066256104581196629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1297179020032557766382021 243221066256104581196629)
                    ·
                      rfl

theorem cell22_710507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 4, 3, 4].length) (baseStart_710507 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_710507 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_710507 prefixEnd_710507 := by exact prefixLift 710507
  have htrace : WordTrace (prefixWord ++ tailWord_710507) baseStart_710507 baseEnd_710507 := by
    simpa [prefixWord, tailWord_710507, baseEnd_710507] using wordTrace_append hprefix tailTrace_710507
  have hstable : (prefixWord ++ tailWord_710507).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710507).length < 2 ^ (prefixWord ++ tailWord_710507).sum := by decide
  have hdescent : baseEnd_710507 < baseStart_710507 := by decide
  rcases family_descends (prefixWord ++ tailWord_710507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710522 : List Nat := [3, 1, 1, 1, 1, 1, 4, 4, 6]
def baseStart_710522 : Nat := 118140960795 + 710522 * 2 ^ 59
def prefixEnd_710522 : Nat := 4983230072969 + 3 ^ 40 * 710522 * 2
def baseEnd_710522 : Nat := 81075400354216514023861

theorem tailTrace_710522 : CollatzResearch.WordTrace tailWord_710522 prefixEnd_710522 81075400354216514023861 := by
  unfold tailWord_710522
  simp only [CollatzResearch.WordTrace]
  refine ⟨6478716582976904085435455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17276577554605077561161213 6478716582976904085435455)
  ·
    refine ⟨9718074874465356128153183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6478716582976904085435455 9718074874465356128153183)
    ·
      refine ⟨14577112311698034192229775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9718074874465356128153183 14577112311698034192229775)
      ·
        refine ⟨21865668467547051288344663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14577112311698034192229775 21865668467547051288344663)
        ·
          refine ⟨32798502701320576932516995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21865668467547051288344663 32798502701320576932516995)
          ·
            refine ⟨49197754051980865398775493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32798502701320576932516995 49197754051980865398775493)
            ·
              refine ⟨9224578884746412262270405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49197754051980865398775493 9224578884746412262270405)
              ·
                refine ⟨1729608540889952299175701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9224578884746412262270405 1729608540889952299175701)
                ·
                  refine ⟨81075400354216514023861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1729608540889952299175701 81075400354216514023861)
                  ·
                    rfl

theorem cell22_710522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 4, 6].length) (baseStart_710522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_710522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_710522 prefixEnd_710522 := by exact prefixLift 710522
  have htrace : WordTrace (prefixWord ++ tailWord_710522) baseStart_710522 baseEnd_710522 := by
    simpa [prefixWord, tailWord_710522, baseEnd_710522] using wordTrace_append hprefix tailTrace_710522
  have hstable : (prefixWord ++ tailWord_710522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710522).length < 2 ^ (prefixWord ++ tailWord_710522).sum := by decide
  have hdescent : baseEnd_710522 < baseStart_710522 := by decide
  rcases family_descends (prefixWord ++ tailWord_710522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710539 : List Nat := [1, 1, 1, 1, 4, 2, 1, 7, 4]
def baseStart_710539 : Nat := 118140960795 + 710539 * 2 ^ 59
def prefixEnd_710539 : Nat := 4983230072969 + 3 ^ 40 * 710539 * 2
def baseEnd_710539 : Nat := 81077340170022388132177

theorem tailTrace_710539 : CollatzResearch.WordTrace tailWord_710539 prefixEnd_710539 81077340170022388132177 := by
  unfold tailWord_710539
  simp only [CollatzResearch.WordTrace]
  refine ⟨25915486372846028245110671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17276990915230685496740447 25915486372846028245110671)
  ·
    refine ⟨38873229559269042367666007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25915486372846028245110671 38873229559269042367666007)
    ·
      refine ⟨58309844338903563551499011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38873229559269042367666007 58309844338903563551499011)
      ·
        refine ⟨87464766508355345327248517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58309844338903563551499011 87464766508355345327248517)
        ·
          refine ⟨16399643720316627248859097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87464766508355345327248517 16399643720316627248859097)
          ·
            refine ⟨12299732790237470436644323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16399643720316627248859097 12299732790237470436644323)
            ·
              refine ⟨18449599185356205654966485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12299732790237470436644323 18449599185356205654966485)
              ·
                refine ⟨432412480906786070038277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 18449599185356205654966485 432412480906786070038277)
                ·
                  refine ⟨81077340170022388132177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 432412480906786070038277 81077340170022388132177)
                  ·
                    rfl

theorem cell22_710539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 7, 4].length) (baseStart_710539 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_710539 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_710539 prefixEnd_710539 := by exact prefixLift 710539
  have htrace : WordTrace (prefixWord ++ tailWord_710539) baseStart_710539 baseEnd_710539 := by
    simpa [prefixWord, tailWord_710539, baseEnd_710539] using wordTrace_append hprefix tailTrace_710539
  have hstable : (prefixWord ++ tailWord_710539).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710539).length < 2 ^ (prefixWord ++ tailWord_710539).sum := by decide
  have hdescent : baseEnd_710539 < baseStart_710539 := by decide
  rcases family_descends (prefixWord ++ tailWord_710539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710584 : List Nat := [2, 1, 2, 1, 2, 3, 5, 6]
def baseStart_710584 : Nat := 118140960795 + 710584 * 2 ^ 59
def prefixEnd_710584 : Nat := 4983230072969 + 3 ^ 40 * 710584 * 2
def baseEnd_710584 : Nat := 27027491658855783002377

theorem tailTrace_710584 : CollatzResearch.WordTrace tailWord_710584 prefixEnd_710584 27027491658855783002377 := by
  unfold tailWord_710584
  simp only [CollatzResearch.WordTrace]
  refine ⟨12958563828841500465249403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17278085105122000620332537 12958563828841500465249403)
  ·
    refine ⟨19437845743262250697874105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12958563828841500465249403 19437845743262250697874105)
    ·
      refine ⟨14578384307446688023405579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19437845743262250697874105 14578384307446688023405579)
      ·
        refine ⟨21867576461170032035108369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14578384307446688023405579 21867576461170032035108369)
        ·
          refine ⟨16400682345877524026331277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21867576461170032035108369 16400682345877524026331277)
          ·
            refine ⟨6150255879704071509874229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16400682345877524026331277 6150255879704071509874229)
            ·
              refine ⟨576586488722256704050709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6150255879704071509874229 576586488722256704050709)
              ·
                refine ⟨27027491658855783002377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 576586488722256704050709 27027491658855783002377)
                ·
                  rfl

theorem cell22_710584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 5, 6].length) (baseStart_710584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_710584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_710584 prefixEnd_710584 := by exact prefixLift 710584
  have htrace : WordTrace (prefixWord ++ tailWord_710584) baseStart_710584 baseEnd_710584 := by
    simpa [prefixWord, tailWord_710584, baseEnd_710584] using wordTrace_append hprefix tailTrace_710584
  have hstable : (prefixWord ++ tailWord_710584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710584).length < 2 ^ (prefixWord ++ tailWord_710584).sum := by decide
  have hdescent : baseEnd_710584 < baseStart_710584 := by decide
  rcases family_descends (prefixWord ++ tailWord_710584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710597 : List Nat := [1, 3, 1, 1, 1, 1, 1, 4, 1, 8]
def baseStart_710597 : Nat := 118140960795 + 710597 * 2 ^ 59
def prefixEnd_710597 : Nat := 4983230072969 + 3 ^ 40 * 710597 * 2
def baseEnd_710597 : Nat := 243251875095374346446353

theorem tailTrace_710597 : CollatzResearch.WordTrace tailWord_710597 prefixEnd_710597 243251875095374346446353 := by
  unfold tailWord_710597
  simp only [CollatzResearch.WordTrace]
  refine ⟨25917601806635904150722045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17278401204423936100481363 25917601806635904150722045)
  ·
    refine ⟨9719100677488464056520767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25917601806635904150722045 9719100677488464056520767)
    ·
      refine ⟨14578651016232696084781151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9719100677488464056520767 14578651016232696084781151)
      ·
        refine ⟨21867976524349044127171727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14578651016232696084781151 21867976524349044127171727)
        ·
          refine ⟨32801964786523566190757591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21867976524349044127171727 32801964786523566190757591)
          ·
            refine ⟨49202947179785349286136387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32801964786523566190757591 49202947179785349286136387)
            ·
              refine ⟨73804420769678023929204581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49202947179785349286136387 73804420769678023929204581)
              ·
                refine ⟨13838328894314629486725859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 73804420769678023929204581 13838328894314629486725859)
                ·
                  refine ⟨20757493341471944230088789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13838328894314629486725859 20757493341471944230088789)
                  ·
                    refine ⟨243251875095374346446353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 20757493341471944230088789 243251875095374346446353)
                    ·
                      rfl

theorem cell22_710597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 8].length) (baseStart_710597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_710597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_710597 prefixEnd_710597 := by exact prefixLift 710597
  have htrace : WordTrace (prefixWord ++ tailWord_710597) baseStart_710597 baseEnd_710597 := by
    simpa [prefixWord, tailWord_710597, baseEnd_710597] using wordTrace_append hprefix tailTrace_710597
  have hstable : (prefixWord ++ tailWord_710597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710597).length < 2 ^ (prefixWord ++ tailWord_710597).sum := by decide
  have hdescent : baseEnd_710597 < baseStart_710597 := by decide
  rcases family_descends (prefixWord ++ tailWord_710597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710599 : List Nat := [1, 1, 4, 1, 1, 2, 1, 1, 7, 3]
def baseStart_710599 : Nat := 118140960795 + 710599 * 2 ^ 59
def prefixEnd_710599 : Nat := 4983230072969 + 3 ^ 40 * 710599 * 2
def baseEnd_710599 : Nat := 243252559736247007896347

theorem tailTrace_710599 : CollatzResearch.WordTrace tailWord_710599 prefixEnd_710599 243252559736247007896347 := by
  unfold tailWord_710599
  simp only [CollatzResearch.WordTrace]
  refine ⟨25917674752628658492294851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17278449835085772328196567 25917674752628658492294851)
  ·
    refine ⟨38876512128942987738442277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25917674752628658492294851 38876512128942987738442277)
    ·
      refine ⟨7289346024176810200957927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38876512128942987738442277 7289346024176810200957927)
      ·
        refine ⟨10934019036265215301436891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7289346024176810200957927 10934019036265215301436891)
        ·
          refine ⟨16401028554397822952155337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10934019036265215301436891 16401028554397822952155337)
          ·
            refine ⟨12300771415798367214116503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16401028554397822952155337 12300771415798367214116503)
            ·
              refine ⟨18451157123697550821174755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12300771415798367214116503 18451157123697550821174755)
              ·
                refine ⟨27676735685546326231762133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18451157123697550821174755 27676735685546326231762133)
                ·
                  refine ⟨648673492629992021056925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 27676735685546326231762133 648673492629992021056925)
                  ·
                    refine ⟨243252559736247007896347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 648673492629992021056925 243252559736247007896347)
                    ·
                      rfl

theorem cell22_710599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 7, 3].length) (baseStart_710599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_710599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_710599 prefixEnd_710599 := by exact prefixLift 710599
  have htrace : WordTrace (prefixWord ++ tailWord_710599) baseStart_710599 baseEnd_710599 := by
    simpa [prefixWord, tailWord_710599, baseEnd_710599] using wordTrace_append hprefix tailTrace_710599
  have hstable : (prefixWord ++ tailWord_710599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710599).length < 2 ^ (prefixWord ++ tailWord_710599).sum := by decide
  have hdescent : baseEnd_710599 < baseStart_710599 := by decide
  rcases family_descends (prefixWord ++ tailWord_710599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710616 : List Nat := [2, 1, 2, 2, 2, 2, 4, 1, 3, 3]
def baseStart_710616 : Nat := 118140960795 + 710616 * 2 ^ 59
def prefixEnd_710616 : Nat := 4983230072969 + 3 ^ 40 * 710616 * 2
def baseEnd_710616 : Nat := 243258379183664630221295

theorem tailTrace_710616 : CollatzResearch.WordTrace tailWord_710616 prefixEnd_710616 243258379183664630221295 := by
  unfold tailWord_710616
  simp only [CollatzResearch.WordTrace]
  refine ⟨12959147396783535197831851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17278863195711380263775801 12959147396783535197831851)
  ·
    refine ⟨19438721095175302796747777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12959147396783535197831851 19438721095175302796747777)
    ·
      refine ⟨14579040821381477097560833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19438721095175302796747777 14579040821381477097560833)
      ·
        refine ⟨10934280616036107823170625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14579040821381477097560833 10934280616036107823170625)
        ·
          refine ⟨8200710462027080867377969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10934280616036107823170625 8200710462027080867377969)
          ·
            refine ⟨6150532846520310650533477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8200710462027080867377969 6150532846520310650533477)
            ·
              refine ⟨1153224908722558246975027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6150532846520310650533477 1153224908722558246975027)
              ·
                refine ⟨1729837363083837370462541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1153224908722558246975027 1729837363083837370462541)
                ·
                  refine ⟨648689011156439013923453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1729837363083837370462541 648689011156439013923453)
                  ·
                    refine ⟨243258379183664630221295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 648689011156439013923453 243258379183664630221295)
                    ·
                      rfl

theorem cell22_710616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 4, 1, 3, 3].length) (baseStart_710616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_710616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_710616 prefixEnd_710616 := by exact prefixLift 710616
  have htrace : WordTrace (prefixWord ++ tailWord_710616) baseStart_710616 baseEnd_710616 := by
    simpa [prefixWord, tailWord_710616, baseEnd_710616] using wordTrace_append hprefix tailTrace_710616
  have hstable : (prefixWord ++ tailWord_710616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710616).length < 2 ^ (prefixWord ++ tailWord_710616).sum := by decide
  have hdescent : baseEnd_710616 < baseStart_710616 := by decide
  rcases family_descends (prefixWord ++ tailWord_710616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710693 : List Nat := [1, 3, 1, 2, 2, 5, 1, 2, 1, 4]
def baseStart_710693 : Nat := 118140960795 + 710693 * 2 ^ 59
def prefixEnd_710693 : Nat := 4983230072969 + 3 ^ 40 * 710693 * 2
def baseEnd_710693 : Nat := 243284737857262096046059

theorem tailTrace_710693 : CollatzResearch.WordTrace tailWord_710693 prefixEnd_710693 243284737857262096046059 := by
  unfold tailWord_710693
  simp only [CollatzResearch.WordTrace]
  refine ⟨25921103214288112546216733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17280735476192075030811155 25921103214288112546216733)
  ·
    refine ⟨9720413705358042204831275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25921103214288112546216733 9720413705358042204831275)
    ·
      refine ⟨14580620558037063307246913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9720413705358042204831275 14580620558037063307246913)
      ·
        refine ⟨10935465418527797480435185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14580620558037063307246913 10935465418527797480435185)
        ·
          refine ⟨8201599063895848110326389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10935465418527797480435185 8201599063895848110326389)
          ·
            refine ⟨768899912240235760343099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8201599063895848110326389 768899912240235760343099)
            ·
              refine ⟨1153349868360353640514649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 768899912240235760343099 1153349868360353640514649)
              ·
                refine ⟨865012401270265230385987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1153349868360353640514649 865012401270265230385987)
                ·
                  refine ⟨1297518601905397845578981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 865012401270265230385987 1297518601905397845578981)
                  ·
                    refine ⟨243284737857262096046059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1297518601905397845578981 243284737857262096046059)
                    ·
                      rfl

theorem cell22_710693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 1, 2, 1, 4].length) (baseStart_710693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_710693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_710693 prefixEnd_710693 := by exact prefixLift 710693
  have htrace : WordTrace (prefixWord ++ tailWord_710693) baseStart_710693 baseEnd_710693 := by
    simpa [prefixWord, tailWord_710693, baseEnd_710693] using wordTrace_append hprefix tailTrace_710693
  have hstable : (prefixWord ++ tailWord_710693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710693).length < 2 ^ (prefixWord ++ tailWord_710693).sum := by decide
  have hdescent : baseEnd_710693 < baseStart_710693 := by decide
  rcases family_descends (prefixWord ++ tailWord_710693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710706 : List Nat := [3, 2, 1, 1, 2, 4, 1, 2, 1, 5]
def baseStart_710706 : Nat := 118140960795 + 710706 * 2 ^ 59
def prefixEnd_710706 : Nat := 4983230072969 + 3 ^ 40 * 710706 * 2
def baseEnd_710706 : Nat := 243289188022934395471019

theorem tailTrace_710706 : CollatzResearch.WordTrace tailWord_710706 prefixEnd_710706 243289188022934395471019 := by
  unfold tailWord_710706
  simp only [CollatzResearch.WordTrace]
  refine ⟨6480394340810253941609993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17281051575494010510959981 6480394340810253941609993)
  ·
    refine ⟨4860295755607690456207495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6480394340810253941609993 4860295755607690456207495)
    ·
      refine ⟨7290443633411535684311243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4860295755607690456207495 7290443633411535684311243)
      ·
        refine ⟨10935665450117303526466865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7290443633411535684311243 10935665450117303526466865)
        ·
          refine ⟨8201749087587977644850149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10935665450117303526466865 8201749087587977644850149)
          ·
            refine ⟨1537827953922745808409403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8201749087587977644850149 1537827953922745808409403)
            ·
              refine ⟨2306741930884118712614105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1537827953922745808409403 2306741930884118712614105)
              ·
                refine ⟨1730056448163089034460579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2306741930884118712614105 1730056448163089034460579)
                ·
                  refine ⟨2595084672244633551690869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1730056448163089034460579 2595084672244633551690869)
                  ·
                    refine ⟨243289188022934395471019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2595084672244633551690869 243289188022934395471019)
                    ·
                      rfl

theorem cell22_710706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 2, 1, 5].length) (baseStart_710706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_710706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_710706 prefixEnd_710706 := by exact prefixLift 710706
  have htrace : WordTrace (prefixWord ++ tailWord_710706) baseStart_710706 baseEnd_710706 := by
    simpa [prefixWord, tailWord_710706, baseEnd_710706] using wordTrace_append hprefix tailTrace_710706
  have hstable : (prefixWord ++ tailWord_710706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710706).length < 2 ^ (prefixWord ++ tailWord_710706).sum := by decide
  have hdescent : baseEnd_710706 < baseStart_710706 := by decide
  rcases family_descends (prefixWord ++ tailWord_710706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710710 : List Nat := [5, 1, 2, 1, 1, 1, 5, 1, 1, 4]
def baseStart_710710 : Nat := 118140960795 + 710710 * 2 ^ 59
def prefixEnd_710710 : Nat := 4983230072969 + 3 ^ 40 * 710710 * 2
def baseEnd_710710 : Nat := 243290557304679718371007

theorem tailTrace_710710 : CollatzResearch.WordTrace tailWord_710710 prefixEnd_710710 243290557304679718371007 := by
  unfold tailWord_710710
  simp only [CollatzResearch.WordTrace]
  refine ⟨1620107703451657778099099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17281148836817682966390389 1620107703451657778099099)
  ·
    refine ⟨2430161555177486667148649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1620107703451657778099099 2430161555177486667148649)
    ·
      refine ⟨1822621166383115000361487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2430161555177486667148649 1822621166383115000361487)
      ·
        refine ⟨2733931749574672500542231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1822621166383115000361487 2733931749574672500542231)
        ·
          refine ⟨4100897624362008750813347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2733931749574672500542231 4100897624362008750813347)
          ·
            refine ⟨6151346436543013126220021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4100897624362008750813347 6151346436543013126220021)
            ·
              refine ⟨576688728425907480583127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6151346436543013126220021 576688728425907480583127)
              ·
                refine ⟨865033092638861220874691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 576688728425907480583127 865033092638861220874691)
                ·
                  refine ⟨1297549638958291831312037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 865033092638861220874691 1297549638958291831312037)
                  ·
                    refine ⟨243290557304679718371007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1297549638958291831312037 243290557304679718371007)
                    ·
                      rfl

theorem cell22_710710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 5, 1, 1, 4].length) (baseStart_710710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_710710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_710710 prefixEnd_710710 := by exact prefixLift 710710
  have htrace : WordTrace (prefixWord ++ tailWord_710710) baseStart_710710 baseEnd_710710 := by
    simpa [prefixWord, tailWord_710710, baseEnd_710710] using wordTrace_append hprefix tailTrace_710710
  have hstable : (prefixWord ++ tailWord_710710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710710).length < 2 ^ (prefixWord ++ tailWord_710710).sum := by decide
  have hdescent : baseEnd_710710 < baseStart_710710 := by decide
  rcases family_descends (prefixWord ++ tailWord_710710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
