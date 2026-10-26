import V185TrunkScan21Chunk163

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_1999243 : List Nat := [1, 1, 1, 1, 4, 6, 2, 5]
def baseStart_1999243 : Nat := 118140960795 + 1999243 * 2 ^ 59
def prefixEnd_1999243 : Nat := 4983230072969 + 3 ^ 40 * 1999243 * 2
def baseEnd_1999243 : Nat := 152084830242492842410097

theorem tailTrace_1999243 : CollatzResearch.WordTrace tailWord_1999243 prefixEnd_1999243 152084830242492842410097 := by
  unfold tailWord_1999243
  simp only [CollatzResearch.WordTrace]
  refine ⟨72918382696091529365802383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48612255130727686243868255 72918382696091529365802383)
  ·
    refine ⟨109377574044137294048703575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72918382696091529365802383 109377574044137294048703575)
    ·
      refine ⟨164066361066205941073055363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109377574044137294048703575 164066361066205941073055363)
      ·
        refine ⟨246099541599308911609583045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164066361066205941073055363 246099541599308911609583045)
        ·
          refine ⟨46143664049870420926796821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 246099541599308911609583045 46143664049870420926796821)
          ·
            refine ⟨2162984252337675980943601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 46143664049870420926796821 2162984252337675980943601)
            ·
              refine ⟨1622238189253256985707701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2162984252337675980943601 1622238189253256985707701)
              ·
                refine ⟨152084830242492842410097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1622238189253256985707701 152084830242492842410097)
                ·
                  rfl

theorem cell21_1999243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 2, 5].length) (baseStart_1999243 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1999243 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1999243 prefixEnd_1999243 := by exact prefixLift 1999243
  have htrace : WordTrace (prefixWord ++ tailWord_1999243) baseStart_1999243 baseEnd_1999243 := by
    simpa [prefixWord, tailWord_1999243, baseEnd_1999243] using wordTrace_append hprefix tailTrace_1999243
  have hstable : (prefixWord ++ tailWord_1999243).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1999243).length < 2 ^ (prefixWord ++ tailWord_1999243).sum := by decide
  have hdescent : baseEnd_1999243 < baseStart_1999243 := by decide
  rcases family_descends (prefixWord ++ tailWord_1999243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1999347 : List Nat := [1, 1, 1, 2, 2, 2, 3, 5, 4]
def baseStart_1999347 : Nat := 118140960795 + 1999347 * 2 ^ 59
def prefixEnd_1999347 : Nat := 4983230072969 + 3 ^ 40 * 1999347 * 2
def baseEnd_1999347 : Nat := 456278224944397457496745

theorem tailTrace_1999347 : CollatzResearch.WordTrace tailWord_1999347 prefixEnd_1999347 456278224944397457496745 := by
  unfold tailWord_1999347
  simp only [CollatzResearch.WordTrace]
  refine ⟨72922175887714755127588295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48614783925143170085058863 72922175887714755127588295)
  ·
    refine ⟨109383263831572132691382443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72922175887714755127588295 109383263831572132691382443)
    ·
      refine ⟨164074895747358199037073665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109383263831572132691382443 164074895747358199037073665)
      ·
        refine ⟨123056171810518649277805249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164074895747358199037073665 123056171810518649277805249)
        ·
          refine ⟨92292128857888986958353937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123056171810518649277805249 92292128857888986958353937)
          ·
            refine ⟨69219096643416740218765453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92292128857888986958353937 69219096643416740218765453)
            ·
              refine ⟨25957161241281277582037045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69219096643416740218765453 25957161241281277582037045)
              ·
                refine ⟨2433483866370119773315973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25957161241281277582037045 2433483866370119773315973)
                ·
                  refine ⟨456278224944397457496745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2433483866370119773315973 456278224944397457496745)
                  ·
                    rfl

theorem cell21_1999347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 5, 4].length) (baseStart_1999347 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1999347 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1999347 prefixEnd_1999347 := by exact prefixLift 1999347
  have htrace : WordTrace (prefixWord ++ tailWord_1999347) baseStart_1999347 baseEnd_1999347 := by
    simpa [prefixWord, tailWord_1999347, baseEnd_1999347] using wordTrace_append hprefix tailTrace_1999347
  have hstable : (prefixWord ++ tailWord_1999347).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1999347).length < 2 ^ (prefixWord ++ tailWord_1999347).sum := by decide
  have hdescent : baseEnd_1999347 < baseStart_1999347 := by decide
  rcases family_descends (prefixWord ++ tailWord_1999347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1999367 : List Nat := [1, 1, 4, 3, 3, 1, 2, 3, 3]
def baseStart_1999367 : Nat := 118140960795 + 1999367 * 2 ^ 59
def prefixEnd_1999367 : Nat := 4983230072969 + 3 ^ 40 * 1999367 * 2
def baseEnd_1999367 : Nat := 456282789216881867163371

theorem tailTrace_1999367 : CollatzResearch.WordTrace tailWord_1999367 prefixEnd_1999367 456282789216881867163371 := by
  unfold tailWord_1999367
  simp only [CollatzResearch.WordTrace]
  refine ⟨72922905347642298543316355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48615270231761532362210903 72922905347642298543316355)
  ·
    refine ⟨109384358021463447814974533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72922905347642298543316355 109384358021463447814974533)
    ·
      refine ⟨20509567129024396465307725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109384358021463447814974533 20509567129024396465307725)
      ·
        refine ⟨7691087673384148674490397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20509567129024396465307725 7691087673384148674490397)
        ·
          refine ⟨2884157877519055752933899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7691087673384148674490397 2884157877519055752933899)
          ·
            refine ⟨4326236816278583629400849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2884157877519055752933899 4326236816278583629400849)
            ·
              refine ⟨3244677612208937722050637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4326236816278583629400849 3244677612208937722050637)
              ·
                refine ⟨1216754104578351645768989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3244677612208937722050637 1216754104578351645768989)
                ·
                  refine ⟨456282789216881867163371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1216754104578351645768989 456282789216881867163371)
                  ·
                    rfl

theorem cell21_1999367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 2, 3, 3].length) (baseStart_1999367 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1999367 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1999367 prefixEnd_1999367 := by exact prefixLift 1999367
  have htrace : WordTrace (prefixWord ++ tailWord_1999367) baseStart_1999367 baseEnd_1999367 := by
    simpa [prefixWord, tailWord_1999367, baseEnd_1999367] using wordTrace_append hprefix tailTrace_1999367
  have hstable : (prefixWord ++ tailWord_1999367).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1999367).length < 2 ^ (prefixWord ++ tailWord_1999367).sum := by decide
  have hdescent : baseEnd_1999367 < baseStart_1999367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1999367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1999412 : List Nat := [2, 5, 1, 3, 1, 1, 1, 7]
def baseStart_1999412 : Nat := 118140960795 + 1999412 * 2 ^ 59
def prefixEnd_1999412 : Nat := 4983230072969 + 3 ^ 40 * 1999412 * 2
def baseEnd_1999412 : Nat := 152097686276657262971093

theorem tailTrace_1999412 : CollatzResearch.WordTrace tailWord_1999412 prefixEnd_1999412 152097686276657262971093 := by
  unfold tailWord_1999412
  simp only [CollatzResearch.WordTrace]
  refine ⟨36462273316239635614352245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48616364421652847485802993 36462273316239635614352245)
  ·
    refine ⟨3418338123397465838845523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36462273316239635614352245 3418338123397465838845523)
    ·
      refine ⟨5127507185096198758268285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3418338123397465838845523 5127507185096198758268285)
      ·
        refine ⟨1922815194411074534350607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5127507185096198758268285 1922815194411074534350607)
        ·
          refine ⟨2884222791616611801525911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1922815194411074534350607 2884222791616611801525911)
          ·
            refine ⟨4326334187424917702288867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2884222791616611801525911 4326334187424917702288867)
            ·
              refine ⟨6489501281137376553433301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4326334187424917702288867 6489501281137376553433301)
              ·
                refine ⟨152097686276657262971093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6489501281137376553433301 152097686276657262971093)
                ·
                  rfl

theorem cell21_1999412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 7].length) (baseStart_1999412 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1999412 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1999412 prefixEnd_1999412 := by exact prefixLift 1999412
  have htrace : WordTrace (prefixWord ++ tailWord_1999412) baseStart_1999412 baseEnd_1999412 := by
    simpa [prefixWord, tailWord_1999412, baseEnd_1999412] using wordTrace_append hprefix tailTrace_1999412
  have hstable : (prefixWord ++ tailWord_1999412).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1999412).length < 2 ^ (prefixWord ++ tailWord_1999412).sum := by decide
  have hdescent : baseEnd_1999412 < baseStart_1999412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1999412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1999457 : List Nat := [1, 2, 3, 1, 1, 6, 2, 1, 4]
def baseStart_1999457 : Nat := 118140960795 + 1999457 * 2 ^ 59
def prefixEnd_1999457 : Nat := 4983230072969 + 3 ^ 40 * 1999457 * 2
def baseEnd_1999457 : Nat := 456303328443061710663187

theorem tailTrace_1999457 : CollatzResearch.WordTrace tailWord_1999457 prefixEnd_1999457 456303328443061710663187 := by
  unfold tailWord_1999457
  simp only [CollatzResearch.WordTrace]
  refine ⟨72926187917316243914092625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48617458611544162609395083 72926187917316243914092625)
  ·
    refine ⟨54694640937987182935569469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72926187917316243914092625 54694640937987182935569469)
    ·
      refine ⟨20510490351745193600838551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54694640937987182935569469 20510490351745193600838551)
      ·
        refine ⟨30765735527617790401257827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20510490351745193600838551 30765735527617790401257827)
        ·
          refine ⟨46148603291426685601886741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30765735527617790401257827 46148603291426685601886741)
          ·
            refine ⟨2163215779285625887588441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 46148603291426685601886741 2163215779285625887588441)
            ·
              refine ⟨1622411834464219415691331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2163215779285625887588441 1622411834464219415691331)
              ·
                refine ⟨2433617751696329123536997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1622411834464219415691331 2433617751696329123536997)
                ·
                  refine ⟨456303328443061710663187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2433617751696329123536997 456303328443061710663187)
                  ·
                    rfl

theorem cell21_1999457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 2, 1, 4].length) (baseStart_1999457 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1999457 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1999457 prefixEnd_1999457 := by exact prefixLift 1999457
  have htrace : WordTrace (prefixWord ++ tailWord_1999457) baseStart_1999457 baseEnd_1999457 := by
    simpa [prefixWord, tailWord_1999457, baseEnd_1999457] using wordTrace_append hprefix tailTrace_1999457
  have hstable : (prefixWord ++ tailWord_1999457).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1999457).length < 2 ^ (prefixWord ++ tailWord_1999457).sum := by decide
  have hdescent : baseEnd_1999457 < baseStart_1999457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1999457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1999468 : List Nat := [2, 2, 1, 1, 3, 1, 2, 4, 5]
def baseStart_1999468 : Nat := 118140960795 + 1999468 * 2 ^ 59
def prefixEnd_1999468 : Nat := 4983230072969 + 3 ^ 40 * 1999468 * 2
def baseEnd_1999468 : Nat := 456305838792928135979831

theorem tailTrace_1999468 : CollatzResearch.WordTrace tailWord_1999468 prefixEnd_1999468 456305838792928135979831 := by
  unfold tailWord_1999468
  simp only [CollatzResearch.WordTrace]
  refine ⟨36463294560138196396371529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48617726080184261861828705 36463294560138196396371529)
  ·
    refine ⟨27347470920103647297278647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36463294560138196396371529 27347470920103647297278647)
    ·
      refine ⟨41021206380155470945917971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27347470920103647297278647 41021206380155470945917971)
      ·
        refine ⟨61531809570233206418876957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41021206380155470945917971 61531809570233206418876957)
        ·
          refine ⟨23074428588837452407078859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61531809570233206418876957 23074428588837452407078859)
          ·
            refine ⟨34611642883256178610618289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23074428588837452407078859 34611642883256178610618289)
            ·
              refine ⟨25958732162442133957963717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34611642883256178610618289 25958732162442133957963717)
              ·
                refine ⟨4867262280457900117118197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25958732162442133957963717 4867262280457900117118197)
                ·
                  refine ⟨456305838792928135979831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4867262280457900117118197 456305838792928135979831)
                  ·
                    rfl

theorem cell21_1999468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 5].length) (baseStart_1999468 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1999468 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1999468 prefixEnd_1999468 := by exact prefixLift 1999468
  have htrace : WordTrace (prefixWord ++ tailWord_1999468) baseStart_1999468 baseEnd_1999468 := by
    simpa [prefixWord, tailWord_1999468, baseEnd_1999468] using wordTrace_append hprefix tailTrace_1999468
  have hstable : (prefixWord ++ tailWord_1999468).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1999468).length < 2 ^ (prefixWord ++ tailWord_1999468).sum := by decide
  have hdescent : baseEnd_1999468 < baseStart_1999468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1999468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1999502 : List Nat := [4, 1, 1, 3, 1, 1, 3, 4, 3]
def baseStart_1999502 : Nat := 118140960795 + 1999502 * 2 ^ 59
def prefixEnd_1999502 : Nat := 4983230072969 + 3 ^ 40 * 1999502 * 2
def baseEnd_1999502 : Nat := 456313598056151632413095

theorem tailTrace_1999502 : CollatzResearch.WordTrace tailWord_1999502 prefixEnd_1999502 456313598056151632413095 := by
  unfold tailWord_1999502
  simp only [CollatzResearch.WordTrace]
  refine ⟨9115978650269152074935095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48618552801435477732987173 9115978650269152074935095)
  ·
    refine ⟨13673967975403728112402643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9115978650269152074935095 13673967975403728112402643)
    ·
      refine ⟨20510951963105592168603965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13673967975403728112402643 20510951963105592168603965)
      ·
        refine ⟨7691606986164597063226487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20510951963105592168603965 7691606986164597063226487)
        ·
          refine ⟨11537410479246895594839731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7691606986164597063226487 11537410479246895594839731)
          ·
            refine ⟨17306115718870343392259597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11537410479246895594839731 17306115718870343392259597)
            ·
              refine ⟨6489793394576378772097349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17306115718870343392259597 6489793394576378772097349)
              ·
                refine ⟨1216836261483071019768253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6489793394576378772097349 1216836261483071019768253)
                ·
                  refine ⟨456313598056151632413095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1216836261483071019768253 456313598056151632413095)
                  ·
                    rfl

theorem cell21_1999502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 4, 3].length) (baseStart_1999502 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1999502 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1999502 prefixEnd_1999502 := by exact prefixLift 1999502
  have htrace : WordTrace (prefixWord ++ tailWord_1999502) baseStart_1999502 baseEnd_1999502 := by
    simpa [prefixWord, tailWord_1999502, baseEnd_1999502] using wordTrace_append hprefix tailTrace_1999502
  have hstable : (prefixWord ++ tailWord_1999502).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1999502).length < 2 ^ (prefixWord ++ tailWord_1999502).sum := by decide
  have hdescent : baseEnd_1999502 < baseStart_1999502 := by decide
  rcases family_descends (prefixWord ++ tailWord_1999502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1999516 : List Nat := [2, 2, 3, 2, 2, 1, 2, 3, 4]
def baseStart_1999516 : Nat := 118140960795 + 1999516 * 2 ^ 59
def prefixEnd_1999516 : Nat := 4983230072969 + 3 ^ 40 * 1999516 * 2
def baseEnd_1999516 : Nat := 456316793046890719179733

theorem tailTrace_1999516 : CollatzResearch.WordTrace tailWord_1999516 prefixEnd_1999516 456316793046890719179733 := by
  unfold tailWord_1999516
  simp only [CollatzResearch.WordTrace]
  refine ⟨36464169912051248495245201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48618893216068331326993601 36464169912051248495245201)
  ·
    refine ⟨27348127434038436371433901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36464169912051248495245201 27348127434038436371433901)
    ·
      refine ⟨10255547787764413639287713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27348127434038436371433901 10255547787764413639287713)
      ·
        refine ⟨7691660840823310229465785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10255547787764413639287713 7691660840823310229465785)
        ·
          refine ⟨5768745630617482672099339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7691660840823310229465785 5768745630617482672099339)
          ·
            refine ⟨8653118445926224008149009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5768745630617482672099339 8653118445926224008149009)
            ·
              refine ⟨6489838834444668006111757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8653118445926224008149009 6489838834444668006111757)
              ·
                refine ⟨2433689562916750502291909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6489838834444668006111757 2433689562916750502291909)
                ·
                  refine ⟨456316793046890719179733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2433689562916750502291909 456316793046890719179733)
                  ·
                    rfl

theorem cell21_1999516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 3, 4].length) (baseStart_1999516 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1999516 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1999516 prefixEnd_1999516 := by exact prefixLift 1999516
  have htrace : WordTrace (prefixWord ++ tailWord_1999516) baseStart_1999516 baseEnd_1999516 := by
    simpa [prefixWord, tailWord_1999516, baseEnd_1999516] using wordTrace_append hprefix tailTrace_1999516
  have hstable : (prefixWord ++ tailWord_1999516).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1999516).length < 2 ^ (prefixWord ++ tailWord_1999516).sum := by decide
  have hdescent : baseEnd_1999516 < baseStart_1999516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1999516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1999831 : List Nat := [1, 1, 3, 2, 1, 1, 2, 1, 9]
def baseStart_1999831 : Nat := 118140960795 + 1999831 * 2 ^ 59
def prefixEnd_1999831 : Nat := 4983230072969 + 3 ^ 40 * 1999831 * 2
def baseEnd_1999831 : Nat := 456388680338520171429089

theorem tailTrace_1999831 : CollatzResearch.WordTrace tailWord_1999831 prefixEnd_1999831 456388680338520171429089 := by
  unfold tailWord_1999831
  simp only [CollatzResearch.WordTrace]
  refine ⟨72939828817961305788207347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48626552545307537192138231 72939828817961305788207347)
  ·
    refine ⟨109409743226941958682311021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72939828817961305788207347 109409743226941958682311021)
    ·
      refine ⟨41028653710103234505866633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109409743226941958682311021 41028653710103234505866633)
      ·
        refine ⟨30771490282577425879399975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41028653710103234505866633 30771490282577425879399975)
        ·
          refine ⟨46157235423866138819099963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30771490282577425879399975 46157235423866138819099963)
          ·
            refine ⟨69235853135799208228649945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46157235423866138819099963 69235853135799208228649945)
            ·
              refine ⟨51926889851849406171487459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69235853135799208228649945 51926889851849406171487459)
              ·
                refine ⟨77890334777774109257231189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51926889851849406171487459 77890334777774109257231189)
                ·
                  refine ⟨456388680338520171429089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 77890334777774109257231189 456388680338520171429089)
                  ·
                    rfl

theorem cell21_1999831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 9].length) (baseStart_1999831 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1999831 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1999831 prefixEnd_1999831 := by exact prefixLift 1999831
  have htrace : WordTrace (prefixWord ++ tailWord_1999831) baseStart_1999831 baseEnd_1999831 := by
    simpa [prefixWord, tailWord_1999831, baseEnd_1999831] using wordTrace_append hprefix tailTrace_1999831
  have hstable : (prefixWord ++ tailWord_1999831).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1999831).length < 2 ^ (prefixWord ++ tailWord_1999831).sum := by decide
  have hdescent : baseEnd_1999831 < baseStart_1999831 := by decide
  rcases family_descends (prefixWord ++ tailWord_1999831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1999882 : List Nat := [3, 1, 2, 2, 3, 2, 2, 3, 3]
def baseStart_1999882 : Nat := 118140960795 + 1999882 * 2 ^ 59
def prefixEnd_1999882 : Nat := 4983230072969 + 3 ^ 40 * 1999882 * 2
def baseEnd_1999882 : Nat := 456400319233355416078985

theorem tailTrace_1999882 : CollatzResearch.WordTrace tailWord_1999882 prefixEnd_1999882 456400319233355416078985 := by
  unfold tailWord_1999882
  simp only [CollatzResearch.WordTrace]
  refine ⟨18235422235194135374578475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48627792627184360998875933 18235422235194135374578475)
  ·
    refine ⟨27353133352791203061867713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18235422235194135374578475 27353133352791203061867713)
    ·
      refine ⟨20514850014593402296400785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27353133352791203061867713 20514850014593402296400785)
      ·
        refine ⟨15386137510945051722300589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20514850014593402296400785 15386137510945051722300589)
        ·
          refine ⟨5769801566604394395862721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15386137510945051722300589 5769801566604394395862721)
          ·
            refine ⟨4327351174953295796897041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5769801566604394395862721 4327351174953295796897041)
            ·
              refine ⟨3245513381214971847672781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4327351174953295796897041 3245513381214971847672781)
              ·
                refine ⟨1217067517955614442877293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3245513381214971847672781 1217067517955614442877293)
                ·
                  refine ⟨456400319233355416078985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1217067517955614442877293 456400319233355416078985)
                  ·
                    rfl

theorem cell21_1999882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 2, 3, 3].length) (baseStart_1999882 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1999882 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1999882 prefixEnd_1999882 := by exact prefixLift 1999882
  have htrace : WordTrace (prefixWord ++ tailWord_1999882) baseStart_1999882 baseEnd_1999882 := by
    simpa [prefixWord, tailWord_1999882, baseEnd_1999882] using wordTrace_append hprefix tailTrace_1999882
  have hstable : (prefixWord ++ tailWord_1999882).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1999882).length < 2 ^ (prefixWord ++ tailWord_1999882).sum := by decide
  have hdescent : baseEnd_1999882 < baseStart_1999882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1999882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1999893 : List Nat := [1, 3, 2, 1, 4, 2, 8]
def baseStart_1999893 : Nat := 118140960795 + 1999893 * 2 ^ 59
def prefixEnd_1999893 : Nat := 4983230072969 + 3 ^ 40 * 1999893 * 2
def baseEnd_1999893 : Nat := 50711425509246871266181

theorem tailTrace_1999893 : CollatzResearch.WordTrace tailWord_1999893 prefixEnd_1999893 50711425509246871266181 := by
  unfold tailWord_1999893
  simp only [CollatzResearch.WordTrace]
  refine ⟨72942090143736690376964333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48628060095824460251309555 72942090143736690376964333)
  ·
    refine ⟨27353283803901258891361625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72942090143736690376964333 27353283803901258891361625)
    ·
      refine ⟨20514962852925944168521219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27353283803901258891361625 20514962852925944168521219)
      ·
        refine ⟨30772444279388916252781829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20514962852925944168521219 30772444279388916252781829)
        ·
          refine ⟨5769833302385421797396593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30772444279388916252781829 5769833302385421797396593)
          ·
            refine ⟨4327374976789066348047445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5769833302385421797396593 4327374976789066348047445)
            ·
              refine ⟨50711425509246871266181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4327374976789066348047445 50711425509246871266181)
              ·
                rfl

theorem cell21_1999893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 8].length) (baseStart_1999893 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1999893 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1999893 prefixEnd_1999893 := by exact prefixLift 1999893
  have htrace : WordTrace (prefixWord ++ tailWord_1999893) baseStart_1999893 baseEnd_1999893 := by
    simpa [prefixWord, tailWord_1999893, baseEnd_1999893] using wordTrace_append hprefix tailTrace_1999893
  have hstable : (prefixWord ++ tailWord_1999893).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1999893).length < 2 ^ (prefixWord ++ tailWord_1999893).sum := by decide
  have hdescent : baseEnd_1999893 < baseStart_1999893 := by decide
  rcases family_descends (prefixWord ++ tailWord_1999893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1999896 : List Nat := [2, 1, 2, 3, 2, 4, 1, 2, 4]
def baseStart_1999896 : Nat := 118140960795 + 1999896 * 2 ^ 59
def prefixEnd_1999896 : Nat := 4983230072969 + 3 ^ 40 * 1999896 * 2
def baseEnd_1999896 : Nat := 456403514224094502845623

theorem tailTrace_1999896 : CollatzResearch.WordTrace tailWord_1999896 prefixEnd_1999896 456403514224094502845623 := by
  unfold tailWord_1999896
  simp only [CollatzResearch.WordTrace]
  refine ⟨36471099781362910944661771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48628133041817214592882361 36471099781362910944661771)
  ·
    refine ⟨54706649672044366416992657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36471099781362910944661771 54706649672044366416992657)
    ·
      refine ⟨41029987254033274812744493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54706649672044366416992657 41029987254033274812744493)
      ·
        refine ⟨15386245220262478054779185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41029987254033274812744493 15386245220262478054779185)
        ·
          refine ⟨11539683915196858541084389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15386245220262478054779185 11539683915196858541084389)
          ·
            refine ⟨2163690734099410976453323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11539683915196858541084389 2163690734099410976453323)
            ·
              refine ⟨3245536101149116464679985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2163690734099410976453323 3245536101149116464679985)
              ·
                refine ⟨2434152075861837348509989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3245536101149116464679985 2434152075861837348509989)
                ·
                  refine ⟨456403514224094502845623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2434152075861837348509989 456403514224094502845623)
                  ·
                    rfl

theorem cell21_1999896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 1, 2, 4].length) (baseStart_1999896 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1999896 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1999896 prefixEnd_1999896 := by exact prefixLift 1999896
  have htrace : WordTrace (prefixWord ++ tailWord_1999896) baseStart_1999896 baseEnd_1999896 := by
    simpa [prefixWord, tailWord_1999896, baseEnd_1999896] using wordTrace_append hprefix tailTrace_1999896
  have hstable : (prefixWord ++ tailWord_1999896).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1999896).length < 2 ^ (prefixWord ++ tailWord_1999896).sum := by decide
  have hdescent : baseEnd_1999896 < baseStart_1999896 := by decide
  rcases family_descends (prefixWord ++ tailWord_1999896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1999941 : List Nat := [1, 3, 1, 1, 1, 3, 5, 3, 3]
def baseStart_1999941 : Nat := 118140960795 + 1999941 * 2 ^ 59
def prefixEnd_1999941 : Nat := 4983230072969 + 3 ^ 40 * 1999941 * 2
def baseEnd_1999941 : Nat := 456413783837184424595531

theorem tailTrace_1999941 : CollatzResearch.WordTrace tailWord_1999941 prefixEnd_1999941 456413783837184424595531 := by
  unfold tailWord_1999941
  simp only [CollatzResearch.WordTrace]
  refine ⟨72943840847562794574711677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48629227231708529716474451 72943840847562794574711677)
  ·
    refine ⟨27353940317836047965516879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72943840847562794574711677 27353940317836047965516879)
    ·
      refine ⟨41030910476754071948275319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27353940317836047965516879 41030910476754071948275319)
      ·
        refine ⟨61546365715131107922412979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41030910476754071948275319 61546365715131107922412979)
        ·
          refine ⟨92319548572696661883619469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61546365715131107922412979 92319548572696661883619469)
          ·
            refine ⟨34619830714761248206357301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92319548572696661883619469 34619830714761248206357301)
            ·
              refine ⟨3245609129508867019345997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34619830714761248206357301 3245609129508867019345997)
              ·
                refine ⟨1217103423565825132254749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3245609129508867019345997 1217103423565825132254749)
                ·
                  refine ⟨456413783837184424595531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1217103423565825132254749 456413783837184424595531)
                  ·
                    rfl

theorem cell21_1999941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5, 3, 3].length) (baseStart_1999941 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1999941 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1999941 prefixEnd_1999941 := by exact prefixLift 1999941
  have htrace : WordTrace (prefixWord ++ tailWord_1999941) baseStart_1999941 baseEnd_1999941 := by
    simpa [prefixWord, tailWord_1999941, baseEnd_1999941] using wordTrace_append hprefix tailTrace_1999941
  have hstable : (prefixWord ++ tailWord_1999941).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1999941).length < 2 ^ (prefixWord ++ tailWord_1999941).sum := by decide
  have hdescent : baseEnd_1999941 < baseStart_1999941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1999941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1999983 : List Nat := [1, 1, 2, 1, 3, 3, 2, 1, 7]
def baseStart_1999983 : Nat := 118140960795 + 1999983 * 2 ^ 59
def prefixEnd_1999983 : Nat := 4983230072969 + 3 ^ 40 * 1999983 * 2
def baseEnd_1999983 : Nat := 456423368809401684895445

theorem tailTrace_1999983 : CollatzResearch.WordTrace tailWord_1999983 prefixEnd_1999983 456423368809401684895445 := by
  unfold tailWord_1999983
  simp only [CollatzResearch.WordTrace]
  refine ⟨72945372713410635747740603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48630248475607090498493735 72945372713410635747740603)
  ·
    refine ⟨109418059070115953621610905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72945372713410635747740603 109418059070115953621610905)
    ·
      refine ⟨82063544302586965216208179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109418059070115953621610905 82063544302586965216208179)
      ·
        refine ⟨123095316453880447824312269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82063544302586965216208179 123095316453880447824312269)
        ·
          refine ⟨46160743670205167934117101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123095316453880447824312269 46160743670205167934117101)
          ·
            refine ⟨17310278876326937975293913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46160743670205167934117101 17310278876326937975293913)
            ·
              refine ⟨12982709157245203481470435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17310278876326937975293913 12982709157245203481470435)
              ·
                refine ⟨19474063735867805222205653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12982709157245203481470435 19474063735867805222205653)
                ·
                  refine ⟨456423368809401684895445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19474063735867805222205653 456423368809401684895445)
                  ·
                    rfl

theorem cell21_1999983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 1, 7].length) (baseStart_1999983 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1999983 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1999983 prefixEnd_1999983 := by exact prefixLift 1999983
  have htrace : WordTrace (prefixWord ++ tailWord_1999983) baseStart_1999983 baseEnd_1999983 := by
    simpa [prefixWord, tailWord_1999983, baseEnd_1999983] using wordTrace_append hprefix tailTrace_1999983
  have hstable : (prefixWord ++ tailWord_1999983).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1999983).length < 2 ^ (prefixWord ++ tailWord_1999983).sum := by decide
  have hdescent : baseEnd_1999983 < baseStart_1999983 := by decide
  rcases family_descends (prefixWord ++ tailWord_1999983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2000065 : List Nat := [1, 2, 6, 1, 1, 3, 1, 2, 4]
def baseStart_2000065 : Nat := 118140960795 + 2000065 * 2 ^ 59
def prefixEnd_2000065 : Nat := 4983230072969 + 3 ^ 40 * 2000065 * 2
def baseEnd_2000065 : Nat := 456442082326587764528611

theorem tailTrace_2000065 : CollatzResearch.WordTrace tailWord_2000065 prefixEnd_2000065 456442082326587764528611 := by
  unfold tailWord_2000065
  simp only [CollatzResearch.WordTrace]
  refine ⟨72948363499113563752225649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48632242332742375834817099 72948363499113563752225649)
  ·
    refine ⟨54711272624335172814169237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72948363499113563752225649 54711272624335172814169237)
    ·
      refine ⟨2564590904265711225664183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 54711272624335172814169237 2564590904265711225664183)
      ·
        refine ⟨3846886356398566838496275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2564590904265711225664183 3846886356398566838496275)
        ·
          refine ⟨5770329534597850257744413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3846886356398566838496275 5770329534597850257744413)
          ·
            refine ⟨2163873575474193846654155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5770329534597850257744413 2163873575474193846654155)
            ·
              refine ⟨3245810363211290769981233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2163873575474193846654155 3245810363211290769981233)
              ·
                refine ⟨2434357772408468077485925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3245810363211290769981233 2434357772408468077485925)
                ·
                  refine ⟨456442082326587764528611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2434357772408468077485925 456442082326587764528611)
                  ·
                    rfl

theorem cell21_2000065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 1, 2, 4].length) (baseStart_2000065 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2000065 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2000065 prefixEnd_2000065 := by exact prefixLift 2000065
  have htrace : WordTrace (prefixWord ++ tailWord_2000065) baseStart_2000065 baseEnd_2000065 := by
    simpa [prefixWord, tailWord_2000065, baseEnd_2000065] using wordTrace_append hprefix tailTrace_2000065
  have hstable : (prefixWord ++ tailWord_2000065).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2000065).length < 2 ^ (prefixWord ++ tailWord_2000065).sum := by decide
  have hdescent : baseEnd_2000065 < baseStart_2000065 := by decide
  rcases family_descends (prefixWord ++ tailWord_2000065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2000211 : List Nat := [1, 1, 1, 2, 1, 1, 7, 2, 5]
def baseStart_2000211 : Nat := 118140960795 + 2000211 * 2 ^ 59
def prefixEnd_2000211 : Nat := 4983230072969 + 3 ^ 40 * 2000211 * 2
def baseEnd_2000211 : Nat := 456475401515723955094979

theorem tailTrace_2000211 : CollatzResearch.WordTrace tailWord_2000211 prefixEnd_2000211 456475401515723955094979 := by
  unfold tailWord_2000211
  simp only [CollatzResearch.WordTrace]
  refine ⟨72953688556584630687040487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48635792371056420458026991 72953688556584630687040487)
  ·
    refine ⟨109430532834876946030560731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72953688556584630687040487 109430532834876946030560731)
    ·
      refine ⟨164145799252315419045841097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109430532834876946030560731 164145799252315419045841097)
      ·
        refine ⟨123109349439236564284380823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164145799252315419045841097 123109349439236564284380823)
        ·
          refine ⟨184664024158854846426571235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123109349439236564284380823 184664024158854846426571235)
          ·
            refine ⟨276996036238282269639856853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184664024158854846426571235 276996036238282269639856853)
            ·
              refine ⟨6492094599334740694684145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 276996036238282269639856853 6492094599334740694684145)
              ·
                refine ⟨4869070949501055521013109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6492094599334740694684145 4869070949501055521013109)
                ·
                  refine ⟨456475401515723955094979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4869070949501055521013109 456475401515723955094979)
                  ·
                    rfl

theorem cell21_2000211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 2, 5].length) (baseStart_2000211 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2000211 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2000211 prefixEnd_2000211 := by exact prefixLift 2000211
  have htrace : WordTrace (prefixWord ++ tailWord_2000211) baseStart_2000211 baseEnd_2000211 := by
    simpa [prefixWord, tailWord_2000211, baseEnd_2000211] using wordTrace_append hprefix tailTrace_2000211
  have hstable : (prefixWord ++ tailWord_2000211).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2000211).length < 2 ^ (prefixWord ++ tailWord_2000211).sum := by decide
  have hdescent : baseEnd_2000211 < baseStart_2000211 := by decide
  rcases family_descends (prefixWord ++ tailWord_2000211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2000242 : List Nat := [3, 2, 1, 2, 1, 2, 3, 1, 6]
def baseStart_2000242 : Nat := 118140960795 + 2000242 * 2 ^ 59
def prefixEnd_2000242 : Nat := 4983230072969 + 3 ^ 40 * 2000242 * 2
def baseEnd_2000242 : Nat := 456482476138074790078249

theorem tailTrace_2000242 : CollatzResearch.WordTrace tailWord_2000242 prefixEnd_2000242 456482476138074790078249 := by
  unfold tailWord_2000242
  simp only [CollatzResearch.WordTrace]
  refine ⟨18238704804868080745354745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48636546146314881987612653 18238704804868080745354745)
  ·
    refine ⟨13679028603651060559016059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18238704804868080745354745 13679028603651060559016059)
    ·
      refine ⟨20518542905476590838524089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13679028603651060559016059 20518542905476590838524089)
      ·
        refine ⟨15388907179107443128893067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20518542905476590838524089 15388907179107443128893067)
        ·
          refine ⟨23083360768661164693339601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15388907179107443128893067 23083360768661164693339601)
          ·
            refine ⟨17312520576495873520004701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23083360768661164693339601 17312520576495873520004701)
            ·
              refine ⟨6492195216185952570001763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17312520576495873520004701 6492195216185952570001763)
              ·
                refine ⟨9738292824278928855002645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6492195216185952570001763 9738292824278928855002645)
                ·
                  refine ⟨456482476138074790078249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9738292824278928855002645 456482476138074790078249)
                  ·
                    rfl

theorem cell21_2000242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 1, 6].length) (baseStart_2000242 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2000242 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2000242 prefixEnd_2000242 := by exact prefixLift 2000242
  have htrace : WordTrace (prefixWord ++ tailWord_2000242) baseStart_2000242 baseEnd_2000242 := by
    simpa [prefixWord, tailWord_2000242, baseEnd_2000242] using wordTrace_append hprefix tailTrace_2000242
  have hstable : (prefixWord ++ tailWord_2000242).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2000242).length < 2 ^ (prefixWord ++ tailWord_2000242).sum := by decide
  have hdescent : baseEnd_2000242 < baseStart_2000242 := by decide
  rcases family_descends (prefixWord ++ tailWord_2000242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2000245 : List Nat := [1, 3, 4, 1, 3, 1, 2, 1, 5]
def baseStart_2000245 : Nat := 118140960795 + 2000245 * 2 ^ 59
def prefixEnd_2000245 : Nat := 4983230072969 + 3 ^ 40 * 2000245 * 2
def baseEnd_2000245 : Nat := 456483160778947451528243

theorem tailTrace_2000245 : CollatzResearch.WordTrace tailWord_2000245 prefixEnd_2000245 456483160778947451528243 := by
  unfold tailWord_2000245
  simp only [CollatzResearch.WordTrace]
  refine ⟨72954928638461454493778189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48636619092307636329185459 72954928638461454493778189)
  ·
    refine ⟨27358098239423045435166821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72954928638461454493778189 27358098239423045435166821)
    ·
      refine ⟨5129643419891821019093779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27358098239423045435166821 5129643419891821019093779)
      ·
        refine ⟨7694465129837731528640669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5129643419891821019093779 7694465129837731528640669)
        ·
          refine ⟨2885424423689149323240251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7694465129837731528640669 2885424423689149323240251)
          ·
            refine ⟨4328136635533723984860377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2885424423689149323240251 4328136635533723984860377)
            ·
              refine ⟨3246102476650292988645283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4328136635533723984860377 3246102476650292988645283)
              ·
                refine ⟨4869153714975439482967925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3246102476650292988645283 4869153714975439482967925)
                ·
                  refine ⟨456483160778947451528243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4869153714975439482967925 456483160778947451528243)
                  ·
                    rfl

theorem cell21_2000245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 2, 1, 5].length) (baseStart_2000245 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2000245 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2000245 prefixEnd_2000245 := by exact prefixLift 2000245
  have htrace : WordTrace (prefixWord ++ tailWord_2000245) baseStart_2000245 baseEnd_2000245 := by
    simpa [prefixWord, tailWord_2000245, baseEnd_2000245] using wordTrace_append hprefix tailTrace_2000245
  have hstable : (prefixWord ++ tailWord_2000245).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2000245).length < 2 ^ (prefixWord ++ tailWord_2000245).sum := by decide
  have hdescent : baseEnd_2000245 < baseStart_2000245 := by decide
  rcases family_descends (prefixWord ++ tailWord_2000245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2000377 : List Nat := [1, 2, 1, 3, 1, 2, 1, 2, 8]
def baseStart_2000377 : Nat := 118140960795 + 2000377 * 2 ^ 59
def prefixEnd_2000377 : Nat := 4983230072969 + 3 ^ 40 * 2000377 * 2
def baseEnd_2000377 : Nat := 456513284977344555327973

theorem tailTrace_2000377 : CollatzResearch.WordTrace tailWord_2000377 prefixEnd_2000377 456513284977344555327973 := by
  unfold tailWord_2000377
  simp only [CollatzResearch.WordTrace]
  refine ⟨72959743073983241037583385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48639828715988827358388923 72959743073983241037583385)
  ·
    refine ⟨54719807305487430778187539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72959743073983241037583385 54719807305487430778187539)
    ·
      refine ⟨82079710958231146167281309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54719807305487430778187539 82079710958231146167281309)
      ·
        refine ⟨30779891609336679812730491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82079710958231146167281309 30779891609336679812730491)
        ·
          refine ⟨46169837414005019719095737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30779891609336679812730491 46169837414005019719095737)
          ·
            refine ⟨34627378060503764789321803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46169837414005019719095737 34627378060503764789321803)
            ·
              refine ⟨51941067090755647183982705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34627378060503764789321803 51941067090755647183982705)
              ·
                refine ⟨38955800318066735387987029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51941067090755647183982705 38955800318066735387987029)
                ·
                  refine ⟨456513284977344555327973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38955800318066735387987029 456513284977344555327973)
                  ·
                    rfl

theorem cell21_2000377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 8].length) (baseStart_2000377 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2000377 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2000377 prefixEnd_2000377 := by exact prefixLift 2000377
  have htrace : WordTrace (prefixWord ++ tailWord_2000377) baseStart_2000377 baseEnd_2000377 := by
    simpa [prefixWord, tailWord_2000377, baseEnd_2000377] using wordTrace_append hprefix tailTrace_2000377
  have hstable : (prefixWord ++ tailWord_2000377).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2000377).length < 2 ^ (prefixWord ++ tailWord_2000377).sum := by decide
  have hdescent : baseEnd_2000377 < baseStart_2000377 := by decide
  rcases family_descends (prefixWord ++ tailWord_2000377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2000439 : List Nat := [1, 1, 3, 1, 2, 4, 2, 2, 5]
def baseStart_2000439 : Nat := 118140960795 + 2000439 * 2 ^ 59
def prefixEnd_2000439 : Nat := 4983230072969 + 3 ^ 40 * 2000439 * 2
def baseEnd_2000439 : Nat := 456527434222046225294513

theorem tailTrace_2000439 : CollatzResearch.WordTrace tailWord_2000439 prefixEnd_2000439 456527434222046225294513 := by
  unfold tailWord_2000439
  simp only [CollatzResearch.WordTrace]
  refine ⟨72962004399758625626340371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48641336266505750417560247 72962004399758625626340371)
  ·
    refine ⟨109443006599637938439510557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72962004399758625626340371 109443006599637938439510557)
    ·
      refine ⟨41041127474864226914816459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109443006599637938439510557 41041127474864226914816459)
      ·
        refine ⟨61561691212296340372224689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41041127474864226914816459 61561691212296340372224689)
        ·
          refine ⟨46171268409222255279168517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61561691212296340372224689 46171268409222255279168517)
          ·
            refine ⟨8657112826729172864844097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46171268409222255279168517 8657112826729172864844097)
            ·
              refine ⟨6492834620046879648633073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8657112826729172864844097 6492834620046879648633073)
              ·
                refine ⟨4869625965035159736474805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6492834620046879648633073 4869625965035159736474805)
                ·
                  refine ⟨456527434222046225294513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4869625965035159736474805 456527434222046225294513)
                  ·
                    rfl

theorem cell21_2000439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 2, 5].length) (baseStart_2000439 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2000439 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2000439 prefixEnd_2000439 := by exact prefixLift 2000439
  have htrace : WordTrace (prefixWord ++ tailWord_2000439) baseStart_2000439 baseEnd_2000439 := by
    simpa [prefixWord, tailWord_2000439, baseEnd_2000439] using wordTrace_append hprefix tailTrace_2000439
  have hstable : (prefixWord ++ tailWord_2000439).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2000439).length < 2 ^ (prefixWord ++ tailWord_2000439).sum := by decide
  have hdescent : baseEnd_2000439 < baseStart_2000439 := by decide
  rcases family_descends (prefixWord ++ tailWord_2000439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2000453 : List Nat := [1, 3, 1, 1, 1, 4, 1, 1, 8]
def baseStart_2000453 : Nat := 118140960795 + 2000453 * 2 ^ 59
def prefixEnd_2000453 : Nat := 4983230072969 + 3 ^ 40 * 2000453 * 2
def baseEnd_2000453 : Nat := 456530629212785312061151

theorem tailTrace_2000453 : CollatzResearch.WordTrace tailWord_2000453 prefixEnd_2000453 456530629212785312061151 := by
  unfold tailWord_2000453
  simp only [CollatzResearch.WordTrace]
  refine ⟨72962515021707906017350013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48641676681138604011566675 72962515021707906017350013)
  ·
    refine ⟨27360943133140464756506255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72962515021707906017350013 27360943133140464756506255)
    ·
      refine ⟨41041414699710697134759383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27360943133140464756506255 41041414699710697134759383)
      ·
        refine ⟨61562122049566045702139075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41041414699710697134759383 61562122049566045702139075)
        ·
          refine ⟨92343183074349068553208613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61562122049566045702139075 92343183074349068553208613)
          ·
            refine ⟨17314346826440450353726615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92343183074349068553208613 17314346826440450353726615)
            ·
              refine ⟨25971520239660675530589923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17314346826440450353726615 25971520239660675530589923)
              ·
                refine ⟨38957280359491013295884885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25971520239660675530589923 38957280359491013295884885)
                ·
                  refine ⟨456530629212785312061151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38957280359491013295884885 456530629212785312061151)
                  ·
                    rfl

theorem cell21_2000453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 8].length) (baseStart_2000453 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2000453 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2000453 prefixEnd_2000453 := by exact prefixLift 2000453
  have htrace : WordTrace (prefixWord ++ tailWord_2000453) baseStart_2000453 baseEnd_2000453 := by
    simpa [prefixWord, tailWord_2000453, baseEnd_2000453] using wordTrace_append hprefix tailTrace_2000453
  have hstable : (prefixWord ++ tailWord_2000453).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2000453).length < 2 ^ (prefixWord ++ tailWord_2000453).sum := by decide
  have hdescent : baseEnd_2000453 < baseStart_2000453 := by decide
  rcases family_descends (prefixWord ++ tailWord_2000453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2000484 : List Nat := [2, 3, 1, 1, 2, 3, 1, 8]
def baseStart_2000484 : Nat := 118140960795 + 2000484 * 2 ^ 59
def prefixEnd_2000484 : Nat := 4983230072969 + 3 ^ 40 * 2000484 * 2
def baseEnd_2000484 : Nat := 152179234611712049014807

theorem tailTrace_2000484 : CollatzResearch.WordTrace tailWord_2000484 prefixEnd_2000484 152179234611712049014807 := by
  unfold tailWord_2000484
  simp only [CollatzResearch.WordTrace]
  refine ⟨36481822842297799155864253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48642430456397065541152337 36481822842297799155864253)
  ·
    refine ⟨13680683565861674683449095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36481822842297799155864253 13680683565861674683449095)
    ·
      refine ⟨20521025348792512025173643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13680683565861674683449095 20521025348792512025173643)
      ·
        refine ⟨30781538023188768037760465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20521025348792512025173643 30781538023188768037760465)
        ·
          refine ⟨23086153517391576028320349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30781538023188768037760465 23086153517391576028320349)
          ·
            refine ⟨8657307569021841010620131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23086153517391576028320349 8657307569021841010620131)
            ·
              refine ⟨12985961353532761515930197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8657307569021841010620131 12985961353532761515930197)
              ·
                refine ⟨152179234611712049014807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12985961353532761515930197 152179234611712049014807)
                ·
                  rfl

theorem cell21_2000484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 8].length) (baseStart_2000484 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2000484 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2000484 prefixEnd_2000484 := by exact prefixLift 2000484
  have htrace : WordTrace (prefixWord ++ tailWord_2000484) baseStart_2000484 baseEnd_2000484 := by
    simpa [prefixWord, tailWord_2000484, baseEnd_2000484] using wordTrace_append hprefix tailTrace_2000484
  have hstable : (prefixWord ++ tailWord_2000484).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2000484).length < 2 ^ (prefixWord ++ tailWord_2000484).sum := by decide
  have hdescent : baseEnd_2000484 < baseStart_2000484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2000484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2000487 : List Nat := [1, 1, 5, 1, 1, 1, 6, 1, 4]
def baseStart_2000487 : Nat := 118140960795 + 2000487 * 2 ^ 59
def prefixEnd_2000487 : Nat := 4983230072969 + 3 ^ 40 * 2000487 * 2
def baseEnd_2000487 : Nat := 456538388476008808494415

theorem tailTrace_2000487 : CollatzResearch.WordTrace tailWord_2000487 prefixEnd_2000487 456538388476008808494415 := by
  unfold tailWord_2000487
  simp only [CollatzResearch.WordTrace]
  refine ⟨72963755103584729824087715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48642503402389819882725143 72963755103584729824087715)
  ·
    refine ⟨109445632655377094736131573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72963755103584729824087715 109445632655377094736131573)
    ·
      refine ⟨10260528061441602631512335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 109445632655377094736131573 10260528061441602631512335)
      ·
        refine ⟨15390792092162403947268503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10260528061441602631512335 15390792092162403947268503)
        ·
          refine ⟨23086188138243605920902755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15390792092162403947268503 23086188138243605920902755)
          ·
            refine ⟨34629282207365408881354133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23086188138243605920902755 34629282207365408881354133)
            ·
              refine ⟨1623247603470253541313475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 34629282207365408881354133 1623247603470253541313475)
              ·
                refine ⟨2434871405205380311970213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1623247603470253541313475 2434871405205380311970213)
                ·
                  refine ⟨456538388476008808494415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2434871405205380311970213 456538388476008808494415)
                  ·
                    rfl

theorem cell21_2000487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 6, 1, 4].length) (baseStart_2000487 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2000487 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2000487 prefixEnd_2000487 := by exact prefixLift 2000487
  have htrace : WordTrace (prefixWord ++ tailWord_2000487) baseStart_2000487 baseEnd_2000487 := by
    simpa [prefixWord, tailWord_2000487, baseEnd_2000487] using wordTrace_append hprefix tailTrace_2000487
  have hstable : (prefixWord ++ tailWord_2000487).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2000487).length < 2 ^ (prefixWord ++ tailWord_2000487).sum := by decide
  have hdescent : baseEnd_2000487 < baseStart_2000487 := by decide
  rcases family_descends (prefixWord ++ tailWord_2000487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2000501 : List Nat := [1, 3, 4, 2, 1, 1, 2, 7]
def baseStart_2000501 : Nat := 118140960795 + 2000501 * 2 ^ 59
def prefixEnd_2000501 : Nat := 4983230072969 + 3 ^ 40 * 2000501 * 2
def baseEnd_2000501 : Nat := 152180527822249298420351

theorem tailTrace_2000501 : CollatzResearch.WordTrace tailWord_2000501 prefixEnd_2000501 152180527822249298420351 := by
  unfold tailWord_2000501
  simp only [CollatzResearch.WordTrace]
  refine ⟨72964265725534010215097357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48642843817022673476731571 72964265725534010215097357)
  ·
    refine ⟨27361599647075253830661509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72964265725534010215097357 27361599647075253830661509)
    ·
      refine ⟨5130299933826610093249033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27361599647075253830661509 5130299933826610093249033)
      ·
        refine ⟨3847724950369957569936775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5130299933826610093249033 3847724950369957569936775)
        ·
          refine ⟨5771587425554936354905163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3847724950369957569936775 5771587425554936354905163)
          ·
            refine ⟨8657381138332404532357745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5771587425554936354905163 8657381138332404532357745)
            ·
              refine ⟨6493035853749303399268309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8657381138332404532357745 6493035853749303399268309)
              ·
                refine ⟨152180527822249298420351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6493035853749303399268309 152180527822249298420351)
                ·
                  rfl

theorem cell21_2000501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 7].length) (baseStart_2000501 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2000501 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2000501 prefixEnd_2000501 := by exact prefixLift 2000501
  have htrace : WordTrace (prefixWord ++ tailWord_2000501) baseStart_2000501 baseEnd_2000501 := by
    simpa [prefixWord, tailWord_2000501, baseEnd_2000501] using wordTrace_append hprefix tailTrace_2000501
  have hstable : (prefixWord ++ tailWord_2000501).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2000501).length < 2 ^ (prefixWord ++ tailWord_2000501).sum := by decide
  have hdescent : baseEnd_2000501 < baseStart_2000501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2000501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2000552 : List Nat := [2, 1, 7, 1, 1, 1, 3, 5]
def baseStart_2000552 : Nat := 118140960795 + 2000552 * 2 ^ 59
def prefixEnd_2000552 : Nat := 4983230072969 + 3 ^ 40 * 2000552 * 2
def baseEnd_2000552 : Nat := 152184407453861046636983

theorem tailTrace_2000552 : CollatzResearch.WordTrace tailWord_2000552 prefixEnd_2000552 152184407453861046636983 := by
  unfold tailWord_2000552
  simp only [CollatzResearch.WordTrace]
  refine ⟨36483062924174622962601955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48644083898899497283469273 36483062924174622962601955)
  ·
    refine ⟨54724594386261934443902933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36483062924174622962601955 54724594386261934443902933)
    ·
      refine ⟨1282607680928014088528975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 54724594386261934443902933 1282607680928014088528975)
      ·
        refine ⟨1923911521392021132793463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1282607680928014088528975 1923911521392021132793463)
        ·
          refine ⟨2885867282088031699190195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1923911521392021132793463 2885867282088031699190195)
          ·
            refine ⟨4328800923132047548785293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2885867282088031699190195 4328800923132047548785293)
            ·
              refine ⟨1623300346174517830794485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4328800923132047548785293 1623300346174517830794485)
              ·
                refine ⟨152184407453861046636983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1623300346174517830794485 152184407453861046636983)
                ·
                  rfl

theorem cell21_2000552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 3, 5].length) (baseStart_2000552 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2000552 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2000552 prefixEnd_2000552 := by exact prefixLift 2000552
  have htrace : WordTrace (prefixWord ++ tailWord_2000552) baseStart_2000552 baseEnd_2000552 := by
    simpa [prefixWord, tailWord_2000552, baseEnd_2000552] using wordTrace_append hprefix tailTrace_2000552
  have hstable : (prefixWord ++ tailWord_2000552).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2000552).length < 2 ^ (prefixWord ++ tailWord_2000552).sum := by decide
  have hdescent : baseEnd_2000552 < baseStart_2000552 := by decide
  rcases family_descends (prefixWord ++ tailWord_2000552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2000566 : List Nat := [5, 1, 3, 1, 1, 1, 1, 5, 3]
def baseStart_2000566 : Nat := 118140960795 + 2000566 * 2 ^ 59
def prefixEnd_2000566 : Nat := 4983230072969 + 3 ^ 40 * 2000566 * 2
def baseEnd_2000566 : Nat := 456556417352322226677587

theorem tailTrace_2000566 : CollatzResearch.WordTrace tailWord_2000566 prefixEnd_2000566 456556417352322226677587 := by
  unfold tailWord_2000566
  simp only [CollatzResearch.WordTrace]
  refine ⟨4560414779393657894763347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48644424313532350877475701 4560414779393657894763347)
  ·
    refine ⟨6840622169090486842145021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4560414779393657894763347 6840622169090486842145021)
    ·
      refine ⟨2565233313408932565804383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6840622169090486842145021 2565233313408932565804383)
      ·
        refine ⟨3847849970113398848706575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2565233313408932565804383 3847849970113398848706575)
        ·
          refine ⟨5771774955170098273059863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3847849970113398848706575 5771774955170098273059863)
          ·
            refine ⟨8657662432755147409589795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5771774955170098273059863 8657662432755147409589795)
            ·
              refine ⟨12986493649132721114384693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8657662432755147409589795 12986493649132721114384693)
              ·
                refine ⟨1217483779606192604473565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12986493649132721114384693 1217483779606192604473565)
                ·
                  refine ⟨456556417352322226677587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1217483779606192604473565 456556417352322226677587)
                  ·
                    rfl

theorem cell21_2000566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 5, 3].length) (baseStart_2000566 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2000566 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2000566 prefixEnd_2000566 := by exact prefixLift 2000566
  have htrace : WordTrace (prefixWord ++ tailWord_2000566) baseStart_2000566 baseEnd_2000566 := by
    simpa [prefixWord, tailWord_2000566, baseEnd_2000566] using wordTrace_append hprefix tailTrace_2000566
  have hstable : (prefixWord ++ tailWord_2000566).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2000566).length < 2 ^ (prefixWord ++ tailWord_2000566).sum := by decide
  have hdescent : baseEnd_2000566 < baseStart_2000566 := by decide
  rcases family_descends (prefixWord ++ tailWord_2000566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2000611 : List Nat := [1, 1, 1, 7, 3, 1, 2, 5]
def baseStart_2000611 : Nat := 118140960795 + 2000611 * 2 ^ 59
def prefixEnd_2000611 : Nat := 4983230072969 + 3 ^ 40 * 2000611 * 2
def baseEnd_2000611 : Nat := 152188895655137382809165

theorem tailTrace_2000611 : CollatzResearch.WordTrace tailWord_2000611 prefixEnd_2000611 152188895655137382809165 := by
  unfold tailWord_2000611
  simp only [CollatzResearch.WordTrace]
  refine ⟨72968277755135499001601687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48645518503423666001067791 72968277755135499001601687)
  ·
    refine ⟨109452416632703248502402531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72968277755135499001601687 109452416632703248502402531)
    ·
      refine ⟨164178624949054872753603797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109452416632703248502402531 164178624949054872753603797)
      ·
        refine ⟨3847936522243473580162589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 164178624949054872753603797 3847936522243473580162589)
        ·
          refine ⟨1442976195841302592560971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3847936522243473580162589 1442976195841302592560971)
          ·
            refine ⟨2164464293761953888841457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1442976195841302592560971 2164464293761953888841457)
            ·
              refine ⟨1623348220321465416631093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2164464293761953888841457 1623348220321465416631093)
              ·
                refine ⟨152188895655137382809165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1623348220321465416631093 152188895655137382809165)
                ·
                  rfl

theorem cell21_2000611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 2, 5].length) (baseStart_2000611 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2000611 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2000611 prefixEnd_2000611 := by exact prefixLift 2000611
  have htrace : WordTrace (prefixWord ++ tailWord_2000611) baseStart_2000611 baseEnd_2000611 := by
    simpa [prefixWord, tailWord_2000611, baseEnd_2000611] using wordTrace_append hprefix tailTrace_2000611
  have hstable : (prefixWord ++ tailWord_2000611).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2000611).length < 2 ^ (prefixWord ++ tailWord_2000611).sum := by decide
  have hdescent : baseEnd_2000611 < baseStart_2000611 := by decide
  rcases family_descends (prefixWord ++ tailWord_2000611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2000625 : List Nat := [1, 2, 2, 2, 2, 5, 1, 3, 3]
def baseStart_2000625 : Nat := 118140960795 + 2000625 * 2 ^ 59
def prefixEnd_2000625 : Nat := 4983230072969 + 3 ^ 40 * 2000625 * 2
def baseEnd_2000625 : Nat := 456569881956151235194133

theorem tailTrace_2000625 : CollatzResearch.WordTrace tailWord_2000625 prefixEnd_2000625 456569881956151235194133 := by
  unfold tailWord_2000625
  simp only [CollatzResearch.WordTrace]
  refine ⟨72968788377084779392611329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48645858918056519595074219 72968788377084779392611329)
  ·
    refine ⟨54726591282813584544458497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72968788377084779392611329 54726591282813584544458497)
    ·
      refine ⟨41044943462110188408343873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54726591282813584544458497 41044943462110188408343873)
      ·
        refine ⟨30783707596582641306257905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41044943462110188408343873 30783707596582641306257905)
        ·
          refine ⟨23087780697436980979693429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30783707596582641306257905 23087780697436980979693429)
          ·
            refine ⟨2164479440384716966846259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23087780697436980979693429 2164479440384716966846259)
            ·
              refine ⟨3246719160577075450269389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2164479440384716966846259 3246719160577075450269389)
              ·
                refine ⟨1217519685216403293851021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3246719160577075450269389 1217519685216403293851021)
                ·
                  refine ⟨456569881956151235194133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1217519685216403293851021 456569881956151235194133)
                  ·
                    rfl

theorem cell21_2000625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 1, 3, 3].length) (baseStart_2000625 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2000625 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2000625 prefixEnd_2000625 := by exact prefixLift 2000625
  have htrace : WordTrace (prefixWord ++ tailWord_2000625) baseStart_2000625 baseEnd_2000625 := by
    simpa [prefixWord, tailWord_2000625, baseEnd_2000625] using wordTrace_append hprefix tailTrace_2000625
  have hstable : (prefixWord ++ tailWord_2000625).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2000625).length < 2 ^ (prefixWord ++ tailWord_2000625).sum := by decide
  have hdescent : baseEnd_2000625 < baseStart_2000625 := by decide
  rcases family_descends (prefixWord ++ tailWord_2000625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2000642 : List Nat := [3, 4, 1, 1, 1, 1, 5, 2, 3]
def baseStart_2000642 : Nat := 118140960795 + 2000642 * 2 ^ 59
def prefixEnd_2000642 : Nat := 4983230072969 + 3 ^ 40 * 2000642 * 2
def baseEnd_2000642 : Nat := 456573761587762983410765

theorem tailTrace_2000642 : CollatzResearch.WordTrace tailWord_2000642 prefixEnd_2000642 456573761587762983410765 := by
  unfold tailWord_2000642
  simp only [CollatzResearch.WordTrace]
  refine ⟨18242352104505797823995045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48646272278682127530653453 18242352104505797823995045)
  ·
    refine ⟨3420441019594837091999071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18242352104505797823995045 3420441019594837091999071)
    ·
      refine ⟨5130661529392255637998607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3420441019594837091999071 5130661529392255637998607)
      ·
        refine ⟨7695992294088383456997911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5130661529392255637998607 7695992294088383456997911)
        ·
          refine ⟨11543988441132575185496867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7695992294088383456997911 11543988441132575185496867)
          ·
            refine ⟨17315982661698862778245301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11543988441132575185496867 17315982661698862778245301)
            ·
              refine ⟨1623373374534268385460497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17315982661698862778245301 1623373374534268385460497)
              ·
                refine ⟨1217530030900701289095373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1623373374534268385460497 1217530030900701289095373)
                ·
                  refine ⟨456573761587762983410765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1217530030900701289095373 456573761587762983410765)
                  ·
                    rfl

theorem cell21_2000642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 5, 2, 3].length) (baseStart_2000642 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2000642 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2000642 prefixEnd_2000642 := by exact prefixLift 2000642
  have htrace : WordTrace (prefixWord ++ tailWord_2000642) baseStart_2000642 baseEnd_2000642 := by
    simpa [prefixWord, tailWord_2000642, baseEnd_2000642] using wordTrace_append hprefix tailTrace_2000642
  have hstable : (prefixWord ++ tailWord_2000642).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2000642).length < 2 ^ (prefixWord ++ tailWord_2000642).sum := by decide
  have hdescent : baseEnd_2000642 < baseStart_2000642 := by decide
  rcases family_descends (prefixWord ++ tailWord_2000642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2000698 : List Nat := [3, 1, 1, 1, 5, 1, 1, 4, 4]
def baseStart_2000698 : Nat := 118140960795 + 2000698 * 2 ^ 59
def prefixEnd_2000698 : Nat := 4983230072969 + 3 ^ 40 * 2000698 * 2
def baseEnd_2000698 : Nat := 456586541550719330477317

theorem tailTrace_2000698 : CollatzResearch.WordTrace tailWord_2000698 prefixEnd_2000698 456586541550719330477317 := by
  unfold tailWord_2000698
  simp only [CollatzResearch.WordTrace]
  refine ⟨18242862726455078215004687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48647633937213541906679165 18242862726455078215004687)
  ·
    refine ⟨27364294089682617322507031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18242862726455078215004687 27364294089682617322507031)
    ·
      refine ⟨41046441134523925983760547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27364294089682617322507031 41046441134523925983760547)
      ·
        refine ⟨61569661701785888975640821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41046441134523925983760547 61569661701785888975640821)
        ·
          refine ⟨5772155784542427091466327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 61569661701785888975640821 5772155784542427091466327)
          ·
            refine ⟨8658233676813640637199491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5772155784542427091466327 8658233676813640637199491)
            ·
              refine ⟨12987350515220460955799237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8658233676813640637199491 12987350515220460955799237)
              ·
                refine ⟨2435128221603836429212357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12987350515220460955799237 2435128221603836429212357)
                ·
                  refine ⟨456586541550719330477317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2435128221603836429212357 456586541550719330477317)
                  ·
                    rfl

theorem cell21_2000698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 4, 4].length) (baseStart_2000698 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2000698 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2000698 prefixEnd_2000698 := by exact prefixLift 2000698
  have htrace : WordTrace (prefixWord ++ tailWord_2000698) baseStart_2000698 baseEnd_2000698 := by
    simpa [prefixWord, tailWord_2000698, baseEnd_2000698] using wordTrace_append hprefix tailTrace_2000698
  have hstable : (prefixWord ++ tailWord_2000698).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2000698).length < 2 ^ (prefixWord ++ tailWord_2000698).sum := by decide
  have hdescent : baseEnd_2000698 < baseStart_2000698 := by decide
  rcases family_descends (prefixWord ++ tailWord_2000698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2000701 : List Nat := [1, 4, 1, 4, 1, 2, 1, 4, 3]
def baseStart_2000701 : Nat := 118140960795 + 2000701 * 2 ^ 59
def prefixEnd_2000701 : Nat := 4983230072969 + 3 ^ 40 * 2000701 * 2
def baseEnd_2000701 : Nat := 456587226191591991927311

theorem tailTrace_2000701 : CollatzResearch.WordTrace tailWord_2000701 prefixEnd_2000701 456587226191591991927311 := by
  unfold tailWord_2000701
  simp only [CollatzResearch.WordTrace]
  refine ⟨72971560324809444372377957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48647706883206296248251971 72971560324809444372377957)
  ·
    refine ⟨13682167560901770819820867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72971560324809444372377957 13682167560901770819820867)
    ·
      refine ⟨20523251341352656229731301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13682167560901770819820867 20523251341352656229731301)
      ·
        refine ⟨3848109626503623043074619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20523251341352656229731301 3848109626503623043074619)
        ·
          refine ⟨5772164439755434564611929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3848109626503623043074619 5772164439755434564611929)
          ·
            refine ⟨4329123329816575923458947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5772164439755434564611929 4329123329816575923458947)
            ·
              refine ⟨6493684994724863885188421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4329123329816575923458947 6493684994724863885188421)
              ·
                refine ⟨1217565936510911978472829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6493684994724863885188421 1217565936510911978472829)
                ·
                  refine ⟨456587226191591991927311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1217565936510911978472829 456587226191591991927311)
                  ·
                    rfl

theorem cell21_2000701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 4, 3].length) (baseStart_2000701 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2000701 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2000701 prefixEnd_2000701 := by exact prefixLift 2000701
  have htrace : WordTrace (prefixWord ++ tailWord_2000701) baseStart_2000701 baseEnd_2000701 := by
    simpa [prefixWord, tailWord_2000701, baseEnd_2000701] using wordTrace_append hprefix tailTrace_2000701
  have hstable : (prefixWord ++ tailWord_2000701).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2000701).length < 2 ^ (prefixWord ++ tailWord_2000701).sum := by decide
  have hdescent : baseEnd_2000701 < baseStart_2000701 := by decide
  rcases family_descends (prefixWord ++ tailWord_2000701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2000712 : List Nat := [2, 1, 3, 1, 1, 4, 3, 6]
def baseStart_2000712 : Nat := 118140960795 + 2000712 * 2 ^ 59
def prefixEnd_2000712 : Nat := 4983230072969 + 3 ^ 40 * 2000712 * 2
def baseEnd_2000712 : Nat := 152196578847152805747985

theorem tailTrace_2000712 : CollatzResearch.WordTrace tailWord_2000712 prefixEnd_2000712 152196578847152805747985 := by
  unfold tailWord_2000712
  simp only [CollatzResearch.WordTrace]
  refine ⟨36485980763884796625514195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48647974351846395500685593 36485980763884796625514195)
  ·
    refine ⟨54728971145827194938271293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36485980763884796625514195 54728971145827194938271293)
    ·
      refine ⟨20523364179685198101851735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54728971145827194938271293 20523364179685198101851735)
      ·
        refine ⟨30785046269527797152777603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20523364179685198101851735 30785046269527797152777603)
        ·
          refine ⟨46177569404291695729166405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30785046269527797152777603 46177569404291695729166405)
          ·
            refine ⟨8658294263304692949218701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46177569404291695729166405 8658294263304692949218701)
            ·
              refine ⟨3246860348739259855957013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8658294263304692949218701 3246860348739259855957013)
              ·
                refine ⟨152196578847152805747985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3246860348739259855957013 152196578847152805747985)
                ·
                  rfl

theorem cell21_2000712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 3, 6].length) (baseStart_2000712 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2000712 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2000712 prefixEnd_2000712 := by exact prefixLift 2000712
  have htrace : WordTrace (prefixWord ++ tailWord_2000712) baseStart_2000712 baseEnd_2000712 := by
    simpa [prefixWord, tailWord_2000712, baseEnd_2000712] using wordTrace_append hprefix tailTrace_2000712
  have hstable : (prefixWord ++ tailWord_2000712).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2000712).length < 2 ^ (prefixWord ++ tailWord_2000712).sum := by decide
  have hdescent : baseEnd_2000712 < baseStart_2000712 := by decide
  rcases family_descends (prefixWord ++ tailWord_2000712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2000847 : List Nat := [1, 1, 2, 1, 1, 5, 1, 9]
def baseStart_2000847 : Nat := 118140960795 + 2000847 * 2 ^ 59
def prefixEnd_2000847 : Nat := 4983230072969 + 3 ^ 40 * 2000847 * 2
def baseEnd_2000847 : Nat := 152206848460242727497893

theorem tailTrace_2000847 : CollatzResearch.WordTrace tailWord_2000847 prefixEnd_2000847 152206848460242727497893 := by
  unfold tailWord_2000847
  simp only [CollatzResearch.WordTrace]
  refine ⟨72976885382280511307192795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48651256921520340871461863 72976885382280511307192795)
  ·
    refine ⟨109465328073420766960789193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72976885382280511307192795 109465328073420766960789193)
    ·
      refine ⟨82098996055065575220591895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109465328073420766960789193 82098996055065575220591895)
      ·
        refine ⟨123148494082598362830887843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82098996055065575220591895 123148494082598362830887843)
        ·
          refine ⟨184722741123897544246331765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123148494082598362830887843 184722741123897544246331765)
          ·
            refine ⟨17317756980365394773093603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 184722741123897544246331765 17317756980365394773093603)
            ·
              refine ⟨25976635470548092159640405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17317756980365394773093603 25976635470548092159640405)
              ·
                refine ⟨152206848460242727497893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25976635470548092159640405 152206848460242727497893)
                ·
                  rfl

theorem cell21_2000847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 9].length) (baseStart_2000847 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2000847 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2000847 prefixEnd_2000847 := by exact prefixLift 2000847
  have htrace : WordTrace (prefixWord ++ tailWord_2000847) baseStart_2000847 baseEnd_2000847 := by
    simpa [prefixWord, tailWord_2000847, baseEnd_2000847] using wordTrace_append hprefix tailTrace_2000847
  have hstable : (prefixWord ++ tailWord_2000847).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2000847).length < 2 ^ (prefixWord ++ tailWord_2000847).sum := by decide
  have hdescent : baseEnd_2000847 < baseStart_2000847 := by decide
  rcases family_descends (prefixWord ++ tailWord_2000847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2000881 : List Nat := [1, 2, 2, 2, 5, 2, 1, 6]
def baseStart_2000881 : Nat := 118140960795 + 2000881 * 2 ^ 59
def prefixEnd_2000881 : Nat := 4983230072969 + 3 ^ 40 * 2000881 * 2
def baseEnd_2000881 : Nat := 152209434881317226308981

theorem tailTrace_2000881 : CollatzResearch.WordTrace tailWord_2000881 prefixEnd_2000881 152209434881317226308981 := by
  unfold tailWord_2000881
  simp only [CollatzResearch.WordTrace]
  refine ⟨72978125464157335113930497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48652083642771556742620331 72978125464157335113930497)
  ·
    refine ⟨54733594098118001335447873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72978125464157335113930497 54733594098118001335447873)
    ·
      refine ⟨41050195573588501001585905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54733594098118001335447873 41050195573588501001585905)
      ·
        refine ⟨30787646680191375751189429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41050195573588501001585905 30787646680191375751189429)
        ·
          refine ⟨2886341876267941476674009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30787646680191375751189429 2886341876267941476674009)
          ·
            refine ⟨2164756407200956107505507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2886341876267941476674009 2164756407200956107505507)
            ·
              refine ⟨3247134610801434161258261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2164756407200956107505507 3247134610801434161258261)
              ·
                refine ⟨152209434881317226308981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3247134610801434161258261 152209434881317226308981)
                ·
                  rfl

theorem cell21_2000881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 1, 6].length) (baseStart_2000881 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2000881 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2000881 prefixEnd_2000881 := by exact prefixLift 2000881
  have htrace : WordTrace (prefixWord ++ tailWord_2000881) baseStart_2000881 baseEnd_2000881 := by
    simpa [prefixWord, tailWord_2000881, baseEnd_2000881] using wordTrace_append hprefix tailTrace_2000881
  have hstable : (prefixWord ++ tailWord_2000881).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2000881).length < 2 ^ (prefixWord ++ tailWord_2000881).sum := by decide
  have hdescent : baseEnd_2000881 < baseStart_2000881 := by decide
  rcases family_descends (prefixWord ++ tailWord_2000881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2000985 : List Nat := [1, 2, 1, 2, 2, 1, 4, 4, 4]
def baseStart_2000985 : Nat := 118140960795 + 2000985 * 2 ^ 59
def prefixEnd_2000985 : Nat := 4983230072969 + 3 ^ 40 * 2000985 * 2
def baseEnd_2000985 : Nat := 456652038860870609193397

theorem tailTrace_2000985 : CollatzResearch.WordTrace tailWord_2000985 prefixEnd_2000985 456652038860870609193397 := by
  unfold tailWord_2000985
  simp only [CollatzResearch.WordTrace]
  refine ⟨72981918655780560875716409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48654612437187040583810939 72981918655780560875716409)
  ·
    refine ⟨54736438991835420656787307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72981918655780560875716409 54736438991835420656787307)
    ·
      refine ⟨82104658487753130985180961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54736438991835420656787307 82104658487753130985180961)
      ·
        refine ⟨61578493865814848238885721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82104658487753130985180961 61578493865814848238885721)
        ·
          refine ⟨46183870399361136179164291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61578493865814848238885721 46183870399361136179164291)
          ·
            refine ⟨69275805599041704268746437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46183870399361136179164291 69275805599041704268746437)
            ·
              refine ⟨12989213549820319550389957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69275805599041704268746437 12989213549820319550389957)
              ·
                refine ⟨2435477540591309915698117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12989213549820319550389957 2435477540591309915698117)
                ·
                  refine ⟨456652038860870609193397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2435477540591309915698117 456652038860870609193397)
                  ·
                    rfl

theorem cell21_2000985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 4, 4].length) (baseStart_2000985 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2000985 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2000985 prefixEnd_2000985 := by exact prefixLift 2000985
  have htrace : WordTrace (prefixWord ++ tailWord_2000985) baseStart_2000985 baseEnd_2000985 := by
    simpa [prefixWord, tailWord_2000985, baseEnd_2000985] using wordTrace_append hprefix tailTrace_2000985
  have hstable : (prefixWord ++ tailWord_2000985).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2000985).length < 2 ^ (prefixWord ++ tailWord_2000985).sum := by decide
  have hdescent : baseEnd_2000985 < baseStart_2000985 := by decide
  rcases family_descends (prefixWord ++ tailWord_2000985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2000988 : List Nat := [2, 2, 4, 1, 1, 4, 1, 1, 5]
def baseStart_2000988 : Nat := 118140960795 + 2000988 * 2 ^ 59
def prefixEnd_2000988 : Nat := 4983230072969 + 3 ^ 40 * 2000988 * 2
def baseEnd_2000988 : Nat := 456652723501743270643391

theorem tailTrace_2000988 : CollatzResearch.WordTrace tailWord_2000988 prefixEnd_2000988 456652723501743270643391 := by
  unfold tailWord_2000988
  simp only [CollatzResearch.WordTrace]
  refine ⟨36491014037384846194037809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48654685383179794925383745 36491014037384846194037809)
  ·
    refine ⟨27368260528038634645528357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36491014037384846194037809 27368260528038634645528357)
    ·
      refine ⟨5131548849007243996036567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27368260528038634645528357 5131548849007243996036567)
      ·
        refine ⟨7697323273510865994054851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5131548849007243996036567 7697323273510865994054851)
        ·
          refine ⟨11545984910266298991082277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7697323273510865994054851 11545984910266298991082277)
          ·
            refine ⟨2164872170674931060827927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11545984910266298991082277 2164872170674931060827927)
            ·
              refine ⟨3247308256012396591241891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2164872170674931060827927 3247308256012396591241891)
              ·
                refine ⟨4870962384018594886862837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3247308256012396591241891 4870962384018594886862837)
                ·
                  refine ⟨456652723501743270643391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4870962384018594886862837 456652723501743270643391)
                  ·
                    rfl

theorem cell21_2000988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 1, 1, 5].length) (baseStart_2000988 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2000988 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2000988 prefixEnd_2000988 := by exact prefixLift 2000988
  have htrace : WordTrace (prefixWord ++ tailWord_2000988) baseStart_2000988 baseEnd_2000988 := by
    simpa [prefixWord, tailWord_2000988, baseEnd_2000988] using wordTrace_append hprefix tailTrace_2000988
  have hstable : (prefixWord ++ tailWord_2000988).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2000988).length < 2 ^ (prefixWord ++ tailWord_2000988).sum := by decide
  have hdescent : baseEnd_2000988 < baseStart_2000988 := by decide
  rcases family_descends (prefixWord ++ tailWord_2000988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2001050 : List Nat := [3, 1, 1, 5, 3, 1, 1, 6]
def baseStart_2001050 : Nat := 118140960795 + 2001050 * 2 ^ 59
def prefixEnd_2001050 : Nat := 4983230072969 + 3 ^ 40 * 2001050 * 2
def baseEnd_2001050 : Nat := 152222290915481646869977

theorem tailTrace_2001050 : CollatzResearch.WordTrace tailWord_2001050 prefixEnd_2001050 152222290915481646869977 := by
  unfold tailWord_2001050
  simp only [CollatzResearch.WordTrace]
  refine ⟨18246072350136269244208151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48656192933696717984555069 18246072350136269244208151)
  ·
    refine ⟨27369108525204403866312227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18246072350136269244208151 27369108525204403866312227)
    ·
      refine ⟨41053662787806605799468341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27369108525204403866312227 41053662787806605799468341)
      ·
        refine ⟨3848780886356869293700157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41053662787806605799468341 3848780886356869293700157)
        ·
          refine ⟨1443292832383825985137559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3848780886356869293700157 1443292832383825985137559)
          ·
            refine ⟨2164939248575738977706339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1443292832383825985137559 2164939248575738977706339)
            ·
              refine ⟨3247408872863608466559509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2164939248575738977706339 3247408872863608466559509)
              ·
                refine ⟨152222290915481646869977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3247408872863608466559509 152222290915481646869977)
                ·
                  rfl

theorem cell21_2001050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 1, 6].length) (baseStart_2001050 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2001050 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2001050 prefixEnd_2001050 := by exact prefixLift 2001050
  have htrace : WordTrace (prefixWord ++ tailWord_2001050) baseStart_2001050 baseEnd_2001050 := by
    simpa [prefixWord, tailWord_2001050, baseEnd_2001050] using wordTrace_append hprefix tailTrace_2001050
  have hstable : (prefixWord ++ tailWord_2001050).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2001050).length < 2 ^ (prefixWord ++ tailWord_2001050).sum := by decide
  have hdescent : baseEnd_2001050 < baseStart_2001050 := by decide
  rcases family_descends (prefixWord ++ tailWord_2001050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2001061 : List Nat := [1, 3, 1, 2, 1, 3, 1, 5, 4]
def baseStart_2001061 : Nat := 118140960795 + 2001061 * 2 ^ 59
def prefixEnd_2001061 : Nat := 4983230072969 + 3 ^ 40 * 2001061 * 2
def baseEnd_2001061 : Nat := 456669383096311365926575

theorem tailTrace_2001061 : CollatzResearch.WordTrace tailWord_2001061 prefixEnd_2001061 456669383096311365926575 := by
  unfold tailWord_2001061
  simp only [CollatzResearch.WordTrace]
  refine ⟨72984690603505225855483037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48656460402336817236988691 72984690603505225855483037)
  ·
    refine ⟨27369258976314459695806139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72984690603505225855483037 27369258976314459695806139)
    ·
      refine ⟨41053888464471689543709209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27369258976314459695806139 41053888464471689543709209)
      ·
        refine ⟨30790416348353767157781907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41053888464471689543709209 30790416348353767157781907)
        ·
          refine ⟨46185624522530650736672861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30790416348353767157781907 46185624522530650736672861)
          ·
            refine ⟨17319609195948994026252323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46185624522530650736672861 17319609195948994026252323)
            ·
              refine ⟨25979413793923491039378485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17319609195948994026252323 25979413793923491039378485)
              ·
                refine ⟨2435570043180327284941733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25979413793923491039378485 2435570043180327284941733)
                ·
                  refine ⟨456669383096311365926575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2435570043180327284941733 456669383096311365926575)
                  ·
                    rfl

theorem cell21_2001061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 5, 4].length) (baseStart_2001061 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2001061 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2001061 prefixEnd_2001061 := by exact prefixLift 2001061
  have htrace : WordTrace (prefixWord ++ tailWord_2001061) baseStart_2001061 baseEnd_2001061 := by
    simpa [prefixWord, tailWord_2001061, baseEnd_2001061] using wordTrace_append hprefix tailTrace_2001061
  have hstable : (prefixWord ++ tailWord_2001061).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2001061).length < 2 ^ (prefixWord ++ tailWord_2001061).sum := by decide
  have hdescent : baseEnd_2001061 < baseStart_2001061 := by decide
  rcases family_descends (prefixWord ++ tailWord_2001061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2001092 : List Nat := [2, 3, 3, 1, 2, 2, 8]
def baseStart_2001092 : Nat := 118140960795 + 2001092 * 2 ^ 59
def prefixEnd_2001092 : Nat := 4983230072969 + 3 ^ 40 * 2001092 * 2
def baseEnd_2001092 : Nat := 50741828635406911212205

theorem tailTrace_2001092 : CollatzResearch.WordTrace tailWord_2001092 prefixEnd_2001092 50741828635406911212205 := by
  unfold tailWord_2001092
  simp only [CollatzResearch.WordTrace]
  refine ⟨36492910633196459074930765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48657214177595278766574353 36492910633196459074930765)
  ·
    refine ⟨13684841487448672153099037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36492910633196459074930765 13684841487448672153099037)
    ·
      refine ⟨5131815557793252057412139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13684841487448672153099037 5131815557793252057412139)
      ·
        refine ⟨7697723336689878086118209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5131815557793252057412139 7697723336689878086118209)
        ·
          refine ⟨5773292502517408564588657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7697723336689878086118209 5773292502517408564588657)
          ·
            refine ⟨4329969376888056423441493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5773292502517408564588657 4329969376888056423441493)
            ·
              refine ⟨50741828635406911212205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4329969376888056423441493 50741828635406911212205)
              ·
                rfl

theorem cell21_2001092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 8].length) (baseStart_2001092 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2001092 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2001092 prefixEnd_2001092 := by exact prefixLift 2001092
  have htrace : WordTrace (prefixWord ++ tailWord_2001092) baseStart_2001092 baseEnd_2001092 := by
    simpa [prefixWord, tailWord_2001092, baseEnd_2001092] using wordTrace_append hprefix tailTrace_2001092
  have hstable : (prefixWord ++ tailWord_2001092).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2001092).length < 2 ^ (prefixWord ++ tailWord_2001092).sum := by decide
  have hdescent : baseEnd_2001092 < baseStart_2001092 := by decide
  rcases family_descends (prefixWord ++ tailWord_2001092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2001154 : List Nat := [3, 4, 1, 1, 2, 1, 2, 1, 6]
def baseStart_2001154 : Nat := 118140960795 + 2001154 * 2 ^ 59
def prefixEnd_2001154 : Nat := 4983230072969 + 3 ^ 40 * 2001154 * 2
def baseEnd_2001154 : Nat := 456690606963363870876385

theorem tailTrace_2001154 : CollatzResearch.WordTrace tailWord_2001154 prefixEnd_2001154 456690606963363870876385 := by
  unfold tailWord_2001154
  simp only [CollatzResearch.WordTrace]
  refine ⟨18247020648042075684654629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48658721728112201825745677 18247020648042075684654629)
  ·
    refine ⟨3421316371507889190872743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18247020648042075684654629 3421316371507889190872743)
    ·
      refine ⟨5131974557261833786309115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3421316371507889190872743 5131974557261833786309115)
      ·
        refine ⟨7697961835892750679463673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5131974557261833786309115 7697961835892750679463673)
        ·
          refine ⟨5773471376919563009597755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7697961835892750679463673 5773471376919563009597755)
          ·
            refine ⟨8660207065379344514396633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5773471376919563009597755 8660207065379344514396633)
            ·
              refine ⟨6495155299034508385797475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8660207065379344514396633 6495155299034508385797475)
              ·
                refine ⟨9742732948551762578696213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6495155299034508385797475 9742732948551762578696213)
                ·
                  refine ⟨456690606963363870876385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9742732948551762578696213 456690606963363870876385)
                  ·
                    rfl

theorem cell21_2001154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_2001154 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2001154 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2001154 prefixEnd_2001154 := by exact prefixLift 2001154
  have htrace : WordTrace (prefixWord ++ tailWord_2001154) baseStart_2001154 baseEnd_2001154 := by
    simpa [prefixWord, tailWord_2001154, baseEnd_2001154] using wordTrace_append hprefix tailTrace_2001154
  have hstable : (prefixWord ++ tailWord_2001154).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2001154).length < 2 ^ (prefixWord ++ tailWord_2001154).sum := by decide
  have hdescent : baseEnd_2001154 < baseStart_2001154 := by decide
  rcases family_descends (prefixWord ++ tailWord_2001154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2001196 : List Nat := [2, 2, 1, 1, 1, 3, 2, 1, 8]
def baseStart_2001196 : Nat := 118140960795 + 2001196 * 2 ^ 59
def prefixEnd_2001196 : Nat := 4983230072969 + 3 ^ 40 * 2001196 * 2
def baseEnd_2001196 : Nat := 456700191935581131176299

theorem tailTrace_2001196 : CollatzResearch.WordTrace tailWord_2001196 prefixEnd_2001196 456700191935581131176299 := by
  unfold tailWord_2001196
  simp only [CollatzResearch.WordTrace]
  refine ⟨36494807229008071955823721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48659742972010762607764961 36494807229008071955823721)
  ·
    refine ⟨27371105421756053966867791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36494807229008071955823721 27371105421756053966867791)
    ·
      refine ⟨41056658132634080950301687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27371105421756053966867791 41056658132634080950301687)
      ·
        refine ⟨61584987198951121425452531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41056658132634080950301687 61584987198951121425452531)
        ·
          refine ⟨92377480798426682138178797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61584987198951121425452531 92377480798426682138178797)
          ·
            refine ⟨34641555299410005801817049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92377480798426682138178797 34641555299410005801817049)
            ·
              refine ⟨25981166474557504351362787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34641555299410005801817049 25981166474557504351362787)
              ·
                refine ⟨38971749711836256527044181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25981166474557504351362787 38971749711836256527044181)
                ·
                  refine ⟨456700191935581131176299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38971749711836256527044181 456700191935581131176299)
                  ·
                    rfl

theorem cell21_2001196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 8].length) (baseStart_2001196 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2001196 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2001196 prefixEnd_2001196 := by exact prefixLift 2001196
  have htrace : WordTrace (prefixWord ++ tailWord_2001196) baseStart_2001196 baseEnd_2001196 := by
    simpa [prefixWord, tailWord_2001196, baseEnd_2001196] using wordTrace_append hprefix tailTrace_2001196
  have hstable : (prefixWord ++ tailWord_2001196).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2001196).length < 2 ^ (prefixWord ++ tailWord_2001196).sum := by decide
  have hdescent : baseEnd_2001196 < baseStart_2001196 := by decide
  rcases family_descends (prefixWord ++ tailWord_2001196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2001275 : List Nat := [1, 1, 1, 1, 1, 7, 2, 4, 3]
def baseStart_2001275 : Nat := 118140960795 + 2001275 * 2 ^ 59
def prefixEnd_2001275 : Nat := 4983230072969 + 3 ^ 40 * 2001275 * 2
def baseEnd_2001275 : Nat := 456718220811894549359471

theorem tailTrace_2001275 : CollatzResearch.WordTrace tailWord_2001275 prefixEnd_2001275 456718220811894549359471 := by
  unfold tailWord_2001275
  simp only [CollatzResearch.WordTrace]
  refine ⟨72992495824729940403773279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48661663883153293602515519 72992495824729940403773279)
  ·
    refine ⟨109488743737094910605659919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72992495824729940403773279 109488743737094910605659919)
    ·
      refine ⟨164233115605642365908489879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109488743737094910605659919 164233115605642365908489879)
      ·
        refine ⟨246349673408463548862734819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164233115605642365908489879 246349673408463548862734819)
        ·
          refine ⟨369524510112695323294102229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246349673408463548862734819 369524510112695323294102229)
          ·
            refine ⟨8660730705766296639705521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 369524510112695323294102229 8660730705766296639705521)
            ·
              refine ⟨6495548029324722479779141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8660730705766296639705521 6495548029324722479779141)
              ·
                refine ⟨1217915255498385464958589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6495548029324722479779141 1217915255498385464958589)
                ·
                  refine ⟨456718220811894549359471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1217915255498385464958589 456718220811894549359471)
                  ·
                    rfl

theorem cell21_2001275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 4, 3].length) (baseStart_2001275 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2001275 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2001275 prefixEnd_2001275 := by exact prefixLift 2001275
  have htrace : WordTrace (prefixWord ++ tailWord_2001275) baseStart_2001275 baseEnd_2001275 := by
    simpa [prefixWord, tailWord_2001275, baseEnd_2001275] using wordTrace_append hprefix tailTrace_2001275
  have hstable : (prefixWord ++ tailWord_2001275).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2001275).length < 2 ^ (prefixWord ++ tailWord_2001275).sum := by decide
  have hdescent : baseEnd_2001275 < baseStart_2001275 := by decide
  rcases family_descends (prefixWord ++ tailWord_2001275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2001309 : List Nat := [1, 4, 2, 1, 4, 2, 1, 3, 3]
def baseStart_2001309 : Nat := 118140960795 + 2001309 * 2 ^ 59
def prefixEnd_2001309 : Nat := 4983230072969 + 3 ^ 40 * 2001309 * 2
def baseEnd_2001309 : Nat := 456725980075118045792735

theorem tailTrace_2001309 : CollatzResearch.WordTrace tailWord_2001309 prefixEnd_2001309 456725980075118045792735 := by
  unfold tailWord_2001309
  simp only [CollatzResearch.WordTrace]
  refine ⟨72993735906606764210510981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48662490604404509473673987 72993735906606764210510981)
  ·
    refine ⟨13686325482488768289470809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72993735906606764210510981 13686325482488768289470809)
    ·
      refine ⟨10264744111866576217103107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13686325482488768289470809 10264744111866576217103107)
      ·
        refine ⟨15397116167799864325654661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10264744111866576217103107 15397116167799864325654661)
        ·
          refine ⟨2886959281462474561060249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15397116167799864325654661 2886959281462474561060249)
          ·
            refine ⟨2165219461096855920795187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2886959281462474561060249 2165219461096855920795187)
            ·
              refine ⟨3247829191645283881192781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2165219461096855920795187 3247829191645283881192781)
              ·
                refine ⟨1217935946866981455447293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3247829191645283881192781 1217935946866981455447293)
                ·
                  refine ⟨456725980075118045792735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1217935946866981455447293 456725980075118045792735)
                  ·
                    rfl

theorem cell21_2001309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 1, 3, 3].length) (baseStart_2001309 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2001309 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2001309 prefixEnd_2001309 := by exact prefixLift 2001309
  have htrace : WordTrace (prefixWord ++ tailWord_2001309) baseStart_2001309 baseEnd_2001309 := by
    simpa [prefixWord, tailWord_2001309, baseEnd_2001309] using wordTrace_append hprefix tailTrace_2001309
  have hstable : (prefixWord ++ tailWord_2001309).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2001309).length < 2 ^ (prefixWord ++ tailWord_2001309).sum := by decide
  have hdescent : baseEnd_2001309 < baseStart_2001309 := by decide
  rcases family_descends (prefixWord ++ tailWord_2001309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2001320 : List Nat := [2, 1, 6, 1, 1, 1, 9]
def baseStart_2001320 : Nat := 118140960795 + 2001320 * 2 ^ 59
def prefixEnd_2001320 : Nat := 4983230072969 + 3 ^ 40 * 2001320 * 2
def baseEnd_2001320 : Nat := 50747610047220496789931

theorem tailTrace_2001320 : CollatzResearch.WordTrace tailWord_2001320 prefixEnd_2001320 50747610047220496789931 := by
  unfold tailWord_2001320
  simp only [CollatzResearch.WordTrace]
  refine ⟨36497068554783456544580707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48662758073044608726107609 36497068554783456544580707)
  ·
    refine ⟨54745602832175184816871061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36497068554783456544580707 54745602832175184816871061)
    ·
      refine ⟨2566200132758211788290831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 54745602832175184816871061 2566200132758211788290831)
      ·
        refine ⟨3849300199137317682436247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2566200132758211788290831 3849300199137317682436247)
        ·
          refine ⟨5773950298705976523654371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3849300199137317682436247 5773950298705976523654371)
          ·
            refine ⟨8660925448058964785481557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5773950298705976523654371 8660925448058964785481557)
            ·
              refine ⟨50747610047220496789931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8660925448058964785481557 50747610047220496789931)
              ·
                rfl

theorem cell21_2001320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 9].length) (baseStart_2001320 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2001320 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2001320 prefixEnd_2001320 := by exact prefixLift 2001320
  have htrace : WordTrace (prefixWord ++ tailWord_2001320) baseStart_2001320 baseEnd_2001320 := by
    simpa [prefixWord, tailWord_2001320, baseEnd_2001320] using wordTrace_append hprefix tailTrace_2001320
  have hstable : (prefixWord ++ tailWord_2001320).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2001320).length < 2 ^ (prefixWord ++ tailWord_2001320).sum := by decide
  have hdescent : baseEnd_2001320 < baseStart_2001320 := by decide
  rcases family_descends (prefixWord ++ tailWord_2001320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2001379 : List Nat := [1, 1, 1, 6, 3, 9]
def baseStart_2001379 : Nat := 118140960795 + 2001379 * 2 ^ 59
def prefixEnd_2001379 : Nat := 4983230072969 + 3 ^ 40 * 2001379 * 2
def baseEnd_2001379 : Nat := 16916368704770869615775

theorem tailTrace_2001379 : CollatzResearch.WordTrace tailWord_2001379 prefixEnd_2001379 16916368704770869615775 := by
  unfold tailWord_2001379
  simp only [CollatzResearch.WordTrace]
  refine ⟨72996289016353166165559191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48664192677568777443706127 72996289016353166165559191)
  ·
    refine ⟨109494433524529749248338787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72996289016353166165559191 109494433524529749248338787)
    ·
      refine ⟨164241650286794623872508181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109494433524529749248338787 164241650286794623872508181)
      ·
        refine ⟨7698827357193497994023821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 164241650286794623872508181 7698827357193497994023821)
        ·
          refine ⟨2887060258947561747758933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7698827357193497994023821 2887060258947561747758933)
          ·
            refine ⟨16916368704770869615775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2887060258947561747758933 16916368704770869615775)
            ·
              rfl

theorem cell21_2001379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 9].length) (baseStart_2001379 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2001379 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2001379 prefixEnd_2001379 := by exact prefixLift 2001379
  have htrace : WordTrace (prefixWord ++ tailWord_2001379) baseStart_2001379 baseEnd_2001379 := by
    simpa [prefixWord, tailWord_2001379, baseEnd_2001379] using wordTrace_append hprefix tailTrace_2001379
  have hstable : (prefixWord ++ tailWord_2001379).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2001379).length < 2 ^ (prefixWord ++ tailWord_2001379).sum := by decide
  have hdescent : baseEnd_2001379 < baseStart_2001379 := by decide
  rcases family_descends (prefixWord ++ tailWord_2001379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2001427 : List Nat := [1, 1, 1, 2, 1, 5, 4, 3, 3]
def baseStart_2001427 : Nat := 118140960795 + 2001427 * 2 ^ 59
def prefixEnd_2001427 : Nat := 4983230072969 + 3 ^ 40 * 2001427 * 2
def baseEnd_2001427 : Nat := 456752909282776062825827

theorem tailTrace_2001427 : CollatzResearch.WordTrace tailWord_2001427 prefixEnd_2001427 456752909282776062825827 := by
  unfold tailWord_2001427
  simp only [CollatzResearch.WordTrace]
  refine ⟨72998039720179270363306535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48665359813452846908871023 72998039720179270363306535)
  ·
    refine ⟨109497059580268905544959803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72998039720179270363306535 109497059580268905544959803)
    ·
      refine ⟨164245589370403358317439705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109497059580268905544959803 164245589370403358317439705)
      ·
        refine ⟨123184192027802518738079779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164245589370403358317439705 123184192027802518738079779)
        ·
          refine ⟨184776288041703778107119669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123184192027802518738079779 184776288041703778107119669)
          ·
            refine ⟨17322777003909729197542469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 184776288041703778107119669 17322777003909729197542469)
            ·
              refine ⟨3248020688233074224539213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17322777003909729197542469 3248020688233074224539213)
              ·
                refine ⟨1218007758087402834202205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3248020688233074224539213 1218007758087402834202205)
                ·
                  refine ⟨456752909282776062825827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1218007758087402834202205 456752909282776062825827)
                  ·
                    rfl

theorem cell21_2001427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 4, 3, 3].length) (baseStart_2001427 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2001427 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2001427 prefixEnd_2001427 := by exact prefixLift 2001427
  have htrace : WordTrace (prefixWord ++ tailWord_2001427) baseStart_2001427 baseEnd_2001427 := by
    simpa [prefixWord, tailWord_2001427, baseEnd_2001427] using wordTrace_append hprefix tailTrace_2001427
  have hstable : (prefixWord ++ tailWord_2001427).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2001427).length < 2 ^ (prefixWord ++ tailWord_2001427).sum := by decide
  have hdescent : baseEnd_2001427 < baseStart_2001427 := by decide
  rcases family_descends (prefixWord ++ tailWord_2001427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2001444 : List Nat := [2, 3, 1, 5, 1, 1, 2, 1, 5]
def baseStart_2001444 : Nat := 118140960795 + 2001444 * 2 ^ 59
def prefixEnd_2001444 : Nat := 4983230072969 + 3 ^ 40 * 2001444 * 2
def baseEnd_2001444 : Nat := 456756788914387811042459

theorem tailTrace_2001444 : CollatzResearch.WordTrace tailWord_2001444 prefixEnd_2001444 456756788914387811042459 := by
  unfold tailWord_2001444
  simp only [CollatzResearch.WordTrace]
  refine ⟨36499329880558841133337693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48665773174078454844450257 36499329880558841133337693)
  ·
    refine ⟨13687248705209565425001635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36499329880558841133337693 13687248705209565425001635)
    ·
      refine ⟨20530873057814348137502453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13687248705209565425001635 20530873057814348137502453)
      ·
        refine ⟨1924769349170095137890855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20530873057814348137502453 1924769349170095137890855)
        ·
          refine ⟨2887154023755142706836283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1924769349170095137890855 2887154023755142706836283)
          ·
            refine ⟨4330731035632714060254425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2887154023755142706836283 4330731035632714060254425)
            ·
              refine ⟨3248048276724535545190819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4330731035632714060254425 3248048276724535545190819)
              ·
                refine ⟨4872072415086803317786229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3248048276724535545190819 4872072415086803317786229)
                ·
                  refine ⟨456756788914387811042459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4872072415086803317786229 456756788914387811042459)
                  ·
                    rfl

theorem cell21_2001444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 2, 1, 5].length) (baseStart_2001444 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2001444 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2001444 prefixEnd_2001444 := by exact prefixLift 2001444
  have htrace : WordTrace (prefixWord ++ tailWord_2001444) baseStart_2001444 baseEnd_2001444 := by
    simpa [prefixWord, tailWord_2001444, baseEnd_2001444] using wordTrace_append hprefix tailTrace_2001444
  have hstable : (prefixWord ++ tailWord_2001444).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2001444).length < 2 ^ (prefixWord ++ tailWord_2001444).sum := by decide
  have hdescent : baseEnd_2001444 < baseStart_2001444 := by decide
  rcases family_descends (prefixWord ++ tailWord_2001444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2001478 : List Nat := [6, 1, 1, 1, 2, 3, 1, 3, 3]
def baseStart_2001478 : Nat := 118140960795 + 2001478 * 2 ^ 59
def prefixEnd_2001478 : Nat := 4983230072969 + 3 ^ 40 * 2001478 * 2
def baseEnd_2001478 : Nat := 456764548177611307475723

theorem tailTrace_2001478 : CollatzResearch.WordTrace tailWord_2001478 prefixEnd_2001478 456764548177611307475723 := by
  unfold tailWord_2001478
  simp only [CollatzResearch.WordTrace]
  refine ⟨2281246870093578314794159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 48666599895329670715608725 2281246870093578314794159)
  ·
    refine ⟨3421870305140367472191239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2281246870093578314794159 3421870305140367472191239)
    ·
      refine ⟨5132805457710551208286859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3421870305140367472191239 5132805457710551208286859)
      ·
        refine ⟨7699208186565826812430289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5132805457710551208286859 7699208186565826812430289)
        ·
          refine ⟨5774406139924370109322717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7699208186565826812430289 5774406139924370109322717)
          ·
            refine ⟨2165402302471638790996019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5774406139924370109322717 2165402302471638790996019)
            ·
              refine ⟨3248103453707458186494029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2165402302471638790996019 3248103453707458186494029)
              ·
                refine ⟨1218038795140296819935261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3248103453707458186494029 1218038795140296819935261)
                ·
                  refine ⟨456764548177611307475723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1218038795140296819935261 456764548177611307475723)
                  ·
                    rfl

theorem cell21_2001478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 1, 3, 3].length) (baseStart_2001478 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2001478 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2001478 prefixEnd_2001478 := by exact prefixLift 2001478
  have htrace : WordTrace (prefixWord ++ tailWord_2001478) baseStart_2001478 baseEnd_2001478 := by
    simpa [prefixWord, tailWord_2001478, baseEnd_2001478] using wordTrace_append hprefix tailTrace_2001478
  have hstable : (prefixWord ++ tailWord_2001478).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2001478).length < 2 ^ (prefixWord ++ tailWord_2001478).sum := by decide
  have hdescent : baseEnd_2001478 < baseStart_2001478 := by decide
  rcases family_descends (prefixWord ++ tailWord_2001478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2001610 : List Nat := [3, 1, 2, 1, 4, 3, 1, 2, 4]
def baseStart_2001610 : Nat := 118140960795 + 2001610 * 2 ^ 59
def prefixEnd_2001610 : Nat := 4983230072969 + 3 ^ 40 * 2001610 * 2
def baseEnd_2001610 : Nat := 456794672376008411275453

theorem tailTrace_2001610 : CollatzResearch.WordTrace tailWord_2001610 prefixEnd_2001610 456794672376008411275453 := by
  unfold tailWord_2001610
  simp only [CollatzResearch.WordTrace]
  refine ⟨18251178569629073154304571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48669809519010861744812189 18251178569629073154304571)
  ·
    refine ⟨27376767854443609731456857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18251178569629073154304571 27376767854443609731456857)
    ·
      refine ⟨20532575890832707298592643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27376767854443609731456857 20532575890832707298592643)
      ·
        refine ⟨30798863836249060947888965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20532575890832707298592643 30798863836249060947888965)
        ·
          refine ⟨5774786969296698927729181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30798863836249060947888965 5774786969296698927729181)
          ·
            refine ⟨2165545113486262097898443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5774786969296698927729181 2165545113486262097898443)
            ·
              refine ⟨3248317670229393146847665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2165545113486262097898443 3248317670229393146847665)
              ·
                refine ⟨2436238252672044860135749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3248317670229393146847665 2436238252672044860135749)
                ·
                  refine ⟨456794672376008411275453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2436238252672044860135749 456794672376008411275453)
                  ·
                    rfl

theorem cell21_2001610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 1, 2, 4].length) (baseStart_2001610 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2001610 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2001610 prefixEnd_2001610 := by exact prefixLift 2001610
  have htrace : WordTrace (prefixWord ++ tailWord_2001610) baseStart_2001610 baseEnd_2001610 := by
    simpa [prefixWord, tailWord_2001610, baseEnd_2001610] using wordTrace_append hprefix tailTrace_2001610
  have hstable : (prefixWord ++ tailWord_2001610).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2001610).length < 2 ^ (prefixWord ++ tailWord_2001610).sum := by decide
  have hdescent : baseEnd_2001610 < baseStart_2001610 := by decide
  rcases family_descends (prefixWord ++ tailWord_2001610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2001672 : List Nat := [2, 1, 3, 2, 2, 3, 3, 2, 3]
def baseStart_2001672 : Nat := 118140960795 + 2001672 * 2 ^ 59
def prefixEnd_2001672 : Nat := 4983230072969 + 3 ^ 40 * 2001672 * 2
def baseEnd_2001672 : Nat := 456808821620710081241993

theorem tailTrace_2001672 : CollatzResearch.WordTrace tailWord_2001672 prefixEnd_2001672 456808821620710081241993 := by
  unfold tailWord_2001672
  simp only [CollatzResearch.WordTrace]
  refine ⟨36503487802145838602987635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48671317069527784803983513 36503487802145838602987635)
  ·
    refine ⟨54755231703218757904481453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36503487802145838602987635 54755231703218757904481453)
    ·
      refine ⟨20533211888707034214180545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54755231703218757904481453 20533211888707034214180545)
      ·
        refine ⟨15399908916530275660635409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20533211888707034214180545 15399908916530275660635409)
        ·
          refine ⟨11549931687397706745476557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15399908916530275660635409 11549931687397706745476557)
          ·
            refine ⟨4331224382774140029553709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11549931687397706745476557 4331224382774140029553709)
            ·
              refine ⟨1624209143540302511082641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4331224382774140029553709 1624209143540302511082641)
              ·
                refine ⟨1218156857655226883311981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1624209143540302511082641 1218156857655226883311981)
                ·
                  refine ⟨456808821620710081241993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1218156857655226883311981 456808821620710081241993)
                  ·
                    rfl

theorem cell21_2001672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 3, 2, 3].length) (baseStart_2001672 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2001672 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2001672 prefixEnd_2001672 := by exact prefixLift 2001672
  have htrace : WordTrace (prefixWord ++ tailWord_2001672) baseStart_2001672 baseEnd_2001672 := by
    simpa [prefixWord, tailWord_2001672, baseEnd_2001672] using wordTrace_append hprefix tailTrace_2001672
  have hstable : (prefixWord ++ tailWord_2001672).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2001672).length < 2 ^ (prefixWord ++ tailWord_2001672).sum := by decide
  have hdescent : baseEnd_2001672 < baseStart_2001672 := by decide
  rcases family_descends (prefixWord ++ tailWord_2001672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2001697 : List Nat := [1, 2, 3, 2, 1, 2, 2, 1, 7]
def baseStart_2001697 : Nat := 118140960795 + 2001697 * 2 ^ 59
def prefixEnd_2001697 : Nat := 4983230072969 + 3 ^ 40 * 2001697 * 2
def baseEnd_2001697 : Nat := 456814526961315593325275

theorem tailTrace_2001697 : CollatzResearch.WordTrace tailWord_2001697 prefixEnd_2001697 456814526961315593325275 := by
  unfold tailWord_2001697
  simp only [CollatzResearch.WordTrace]
  refine ⟨73007887429201106475635345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48671924952800737650423563 73007887429201106475635345)
  ·
    refine ⟨54755915571900829856726509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73007887429201106475635345 54755915571900829856726509)
    ·
      refine ⟨20533468339462811196272441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54755915571900829856726509 20533468339462811196272441)
      ·
        refine ⟨15400101254597108397204331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20533468339462811196272441 15400101254597108397204331)
        ·
          refine ⟨23100151881895662595806497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15400101254597108397204331 23100151881895662595806497)
          ·
            refine ⟨17325113911421746946854873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23100151881895662595806497 17325113911421746946854873)
            ·
              refine ⟨12993835433566310210141155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17325113911421746946854873 12993835433566310210141155)
              ·
                refine ⟨19490753150349465315211733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12993835433566310210141155 19490753150349465315211733)
                ·
                  refine ⟨456814526961315593325275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19490753150349465315211733 456814526961315593325275)
                  ·
                    rfl

theorem cell21_2001697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 1, 7].length) (baseStart_2001697 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2001697 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2001697 prefixEnd_2001697 := by exact prefixLift 2001697
  have htrace : WordTrace (prefixWord ++ tailWord_2001697) baseStart_2001697 baseEnd_2001697 := by
    simpa [prefixWord, tailWord_2001697, baseEnd_2001697] using wordTrace_append hprefix tailTrace_2001697
  have hstable : (prefixWord ++ tailWord_2001697).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2001697).length < 2 ^ (prefixWord ++ tailWord_2001697).sum := by decide
  have hdescent : baseEnd_2001697 < baseStart_2001697 := by decide
  rcases family_descends (prefixWord ++ tailWord_2001697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2001734 : List Nat := [6, 1, 1, 2, 2, 2, 1, 6]
def baseStart_2001734 : Nat := 118140960795 + 2001734 * 2 ^ 59
def prefixEnd_2001734 : Nat := 4983230072969 + 3 ^ 40 * 2001734 * 2
def baseEnd_2001734 : Nat := 152274323621803917069511

theorem tailTrace_2001734 : CollatzResearch.WordTrace tailWord_2001734 prefixEnd_2001734 152274323621803917069511 := by
  unfold tailWord_2001734
  simp only [CollatzResearch.WordTrace]
  refine ⟨2281538654064595681085383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 48672824620044707863154837 2281538654064595681085383)
  ·
    refine ⟨3422307981096893521628075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2281538654064595681085383 3422307981096893521628075)
    ·
      refine ⟨5133461971645340282442113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3422307981096893521628075 5133461971645340282442113)
      ·
        refine ⟨3850096478734005211831585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5133461971645340282442113 3850096478734005211831585)
        ·
          refine ⟨2887572359050503908873689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3850096478734005211831585 2887572359050503908873689)
          ·
            refine ⟨2165679269287877931655267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2887572359050503908873689 2165679269287877931655267)
            ·
              refine ⟨3248518903931816897482901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2165679269287877931655267 3248518903931816897482901)
              ·
                refine ⟨152274323621803917069511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3248518903931816897482901 152274323621803917069511)
                ·
                  rfl

theorem cell21_2001734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 1, 6].length) (baseStart_2001734 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2001734 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2001734 prefixEnd_2001734 := by exact prefixLift 2001734
  have htrace : WordTrace (prefixWord ++ tailWord_2001734) baseStart_2001734 baseEnd_2001734 := by
    simpa [prefixWord, tailWord_2001734, baseEnd_2001734] using wordTrace_append hprefix tailTrace_2001734
  have hstable : (prefixWord ++ tailWord_2001734).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2001734).length < 2 ^ (prefixWord ++ tailWord_2001734).sum := by decide
  have hdescent : baseEnd_2001734 < baseStart_2001734 := by decide
  rcases family_descends (prefixWord ++ tailWord_2001734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2001759 : List Nat := [1, 1, 2, 3, 1, 3, 5, 5]
def baseStart_2001759 : Nat := 118140960795 + 2001759 * 2 ^ 59
def prefixEnd_2001759 : Nat := 4983230072969 + 3 ^ 40 * 2001759 * 2
def baseEnd_2001759 : Nat := 152276225402005754430605

theorem tailTrace_2001759 : CollatzResearch.WordTrace tailWord_2001759 prefixEnd_2001759 152276225402005754430605 := by
  unfold tailWord_2001759
  simp only [CollatzResearch.WordTrace]
  refine ⟨73010148754976491064392331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48673432503317660709594887 73010148754976491064392331)
  ·
    refine ⟨109515223132464736596588497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73010148754976491064392331 109515223132464736596588497)
    ·
      refine ⟨82136417349348552447441373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109515223132464736596588497 82136417349348552447441373)
      ·
        refine ⟨30801156506005707167790515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82136417349348552447441373 30801156506005707167790515)
        ·
          refine ⟨46201734759008560751685773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30801156506005707167790515 46201734759008560751685773)
          ·
            refine ⟨17325650534628210281882165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46201734759008560751685773 17325650534628210281882165)
            ·
              refine ⟨1624279737621394713926453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17325650534628210281882165 1624279737621394713926453)
              ·
                refine ⟨152276225402005754430605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1624279737621394713926453 152276225402005754430605)
                ·
                  rfl

theorem cell21_2001759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 5, 5].length) (baseStart_2001759 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2001759 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2001759 prefixEnd_2001759 := by exact prefixLift 2001759
  have htrace : WordTrace (prefixWord ++ tailWord_2001759) baseStart_2001759 baseEnd_2001759 := by
    simpa [prefixWord, tailWord_2001759, baseEnd_2001759] using wordTrace_append hprefix tailTrace_2001759
  have hstable : (prefixWord ++ tailWord_2001759).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2001759).length < 2 ^ (prefixWord ++ tailWord_2001759).sum := by decide
  have hdescent : baseEnd_2001759 < baseStart_2001759 := by decide
  rcases family_descends (prefixWord ++ tailWord_2001759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2001773 : List Nat := [1, 5, 1, 1, 1, 1, 1, 1, 9]
def baseStart_2001773 : Nat := 118140960795 + 2001773 * 2 ^ 59
def prefixEnd_2001773 : Nat := 4983230072969 + 3 ^ 40 * 2001773 * 2
def baseEnd_2001773 : Nat := 456831871196756350058453

theorem tailTrace_2001773 : CollatzResearch.WordTrace tailWord_2001773 prefixEnd_2001773 456831871196756350058453 := by
  unfold tailWord_2001773
  simp only [CollatzResearch.WordTrace]
  refine ⟨73010659376925771455401973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48673772917950514303601315 73010659376925771455401973)
  ·
    refine ⟨6844749316586791073943935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 73010659376925771455401973 6844749316586791073943935)
    ·
      refine ⟨10267123974880186610915903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6844749316586791073943935 10267123974880186610915903)
      ·
        refine ⟨15400685962320279916373855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10267123974880186610915903 15400685962320279916373855)
        ·
          refine ⟨23101028943480419874560783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15400685962320279916373855 23101028943480419874560783)
          ·
            refine ⟨34651543415220629811841175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23101028943480419874560783 34651543415220629811841175)
            ·
              refine ⟨51977315122830944717761763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34651543415220629811841175 51977315122830944717761763)
              ·
                refine ⟨77965972684246417076642645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51977315122830944717761763 77965972684246417076642645)
                ·
                  refine ⟨456831871196756350058453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 77965972684246417076642645 456831871196756350058453)
                  ·
                    rfl

theorem cell21_2001773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 9].length) (baseStart_2001773 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2001773 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2001773 prefixEnd_2001773 := by exact prefixLift 2001773
  have htrace : WordTrace (prefixWord ++ tailWord_2001773) baseStart_2001773 baseEnd_2001773 := by
    simpa [prefixWord, tailWord_2001773, baseEnd_2001773] using wordTrace_append hprefix tailTrace_2001773
  have hstable : (prefixWord ++ tailWord_2001773).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2001773).length < 2 ^ (prefixWord ++ tailWord_2001773).sum := by decide
  have hdescent : baseEnd_2001773 < baseStart_2001773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2001773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2001804 : List Nat := [2, 2, 1, 2, 1, 2, 2, 5, 4]
def baseStart_2001804 : Nat := 118140960795 + 2001804 * 2 ^ 59
def prefixEnd_2001804 : Nat := 4983230072969 + 3 ^ 40 * 2001804 * 2
def baseEnd_2001804 : Nat := 456838945819107185041723

theorem tailTrace_2001804 : CollatzResearch.WordTrace tailWord_2001804 prefixEnd_2001804 456838945819107185041723 := by
  unfold tailWord_2001804
  simp only [CollatzResearch.WordTrace]
  refine ⟨36505895019906731874890233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48674526693208975833186977 36505895019906731874890233)
  ·
    refine ⟨27379421264930048906167675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36505895019906731874890233 27379421264930048906167675)
    ·
      refine ⟨41069131897395073359251513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27379421264930048906167675 41069131897395073359251513)
      ·
        refine ⟨30801848923046305019438635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41069131897395073359251513 30801848923046305019438635)
        ·
          refine ⟨46202773384569457529157953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30801848923046305019438635 46202773384569457529157953)
          ·
            refine ⟨34652080038427093146868465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46202773384569457529157953 34652080038427093146868465)
            ·
              refine ⟨25989060028820319860151349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34652080038427093146868465 25989060028820319860151349)
              ·
                refine ⟨2436474377701904986889189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25989060028820319860151349 2436474377701904986889189)
                ·
                  refine ⟨456838945819107185041723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2436474377701904986889189 456838945819107185041723)
                  ·
                    rfl

theorem cell21_2001804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 5, 4].length) (baseStart_2001804 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2001804 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2001804 prefixEnd_2001804 := by exact prefixLift 2001804
  have htrace : WordTrace (prefixWord ++ tailWord_2001804) baseStart_2001804 baseEnd_2001804 := by
    simpa [prefixWord, tailWord_2001804, baseEnd_2001804] using wordTrace_append hprefix tailTrace_2001804
  have hstable : (prefixWord ++ tailWord_2001804).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2001804).length < 2 ^ (prefixWord ++ tailWord_2001804).sum := by decide
  have hdescent : baseEnd_2001804 < baseStart_2001804 := by decide
  rcases family_descends (prefixWord ++ tailWord_2001804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2001810 : List Nat := [3, 2, 3, 2, 3, 1, 2, 5]
def baseStart_2001810 : Nat := 118140960795 + 2001810 * 2 ^ 59
def prefixEnd_2001810 : Nat := 4983230072969 + 3 ^ 40 * 2001810 * 2
def baseEnd_2001810 : Nat := 152280105033617502647237

theorem tailTrace_2001810 : CollatzResearch.WordTrace tailWord_2001810 prefixEnd_2001810 152280105033617502647237 := by
  unfold tailWord_2001810
  simp only [CollatzResearch.WordTrace]
  refine ⟨18253002219447931693624721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48674672585194484516332589 18253002219447931693624721)
  ·
    refine ⟨13689751664585948770218541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18253002219447931693624721 13689751664585948770218541)
    ·
      refine ⟨5133656874219730788831953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13689751664585948770218541 5133656874219730788831953)
      ·
        refine ⟨3850242655664798091623965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5133656874219730788831953 3850242655664798091623965)
        ·
          refine ⟨1443840995874299284358987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3850242655664798091623965 1443840995874299284358987)
          ·
            refine ⟨2165761493811448926538481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1443840995874299284358987 2165761493811448926538481)
            ·
              refine ⟨1624321120358586694903861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2165761493811448926538481 1624321120358586694903861)
              ·
                refine ⟨152280105033617502647237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1624321120358586694903861 152280105033617502647237)
                ·
                  rfl

theorem cell21_2001810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 2, 5].length) (baseStart_2001810 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2001810 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2001810 prefixEnd_2001810 := by exact prefixLift 2001810
  have htrace : WordTrace (prefixWord ++ tailWord_2001810) baseStart_2001810 baseEnd_2001810 := by
    simpa [prefixWord, tailWord_2001810, baseEnd_2001810] using wordTrace_append hprefix tailTrace_2001810
  have hstable : (prefixWord ++ tailWord_2001810).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2001810).length < 2 ^ (prefixWord ++ tailWord_2001810).sum := by decide
  have hdescent : baseEnd_2001810 < baseStart_2001810 := by decide
  rcases family_descends (prefixWord ++ tailWord_2001810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2001925 : List Nat := [1, 3, 1, 1, 2, 3, 3, 2, 5]
def baseStart_2001925 : Nat := 118140960795 + 2001925 * 2 ^ 59
def prefixEnd_2001925 : Nat := 4983230072969 + 3 ^ 40 * 2001925 * 2
def baseEnd_2001925 : Nat := 456866559667637863524809

theorem tailTrace_2001925 : CollatzResearch.WordTrace tailWord_2001925 prefixEnd_2001925 456866559667637863524809 := by
  unfold tailWord_2001925
  simp only [CollatzResearch.WordTrace]
  refine ⟨73016203272375101414935229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48677468848250067609956819 73016203272375101414935229)
  ·
    refine ⟨27381076227140663030600711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73016203272375101414935229 27381076227140663030600711)
    ·
      refine ⟨41071614340710994545901067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27381076227140663030600711 41071614340710994545901067)
      ·
        refine ⟨61607421511066491818851601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41071614340710994545901067 61607421511066491818851601)
        ·
          refine ⟨46205566133299868864138701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61607421511066491818851601 46205566133299868864138701)
          ·
            refine ⟨17327087299987450824052013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46205566133299868864138701 17327087299987450824052013)
            ·
              refine ⟨6497657737495294059019505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17327087299987450824052013 6497657737495294059019505)
              ·
                refine ⟨4873243303121470544264629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6497657737495294059019505 4873243303121470544264629)
                ·
                  refine ⟨456866559667637863524809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4873243303121470544264629 456866559667637863524809)
                  ·
                    rfl

theorem cell21_2001925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 2, 5].length) (baseStart_2001925 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2001925 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2001925 prefixEnd_2001925 := by exact prefixLift 2001925
  have htrace : WordTrace (prefixWord ++ tailWord_2001925) baseStart_2001925 baseEnd_2001925 := by
    simpa [prefixWord, tailWord_2001925, baseEnd_2001925] using wordTrace_append hprefix tailTrace_2001925
  have hstable : (prefixWord ++ tailWord_2001925).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2001925).length < 2 ^ (prefixWord ++ tailWord_2001925).sum := by decide
  have hdescent : baseEnd_2001925 < baseStart_2001925 := by decide
  rcases family_descends (prefixWord ++ tailWord_2001925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2001939 : List Nat := [1, 1, 1, 2, 1, 4, 1, 4, 6]
def baseStart_2001939 : Nat := 118140960795 + 2001939 * 2 ^ 59
def prefixEnd_2001939 : Nat := 4983230072969 + 3 ^ 40 * 2001939 * 2
def baseEnd_2001939 : Nat := 456869754658376950291447

theorem tailTrace_2001939 : CollatzResearch.WordTrace tailWord_2001939 prefixEnd_2001939 456869754658376950291447 := by
  unfold tailWord_2001939
  simp only [CollatzResearch.WordTrace]
  refine ⟨73016713894324381805944871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48677809262882921203963247 73016713894324381805944871)
  ·
    refine ⟨109525070841486572708917307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73016713894324381805944871 109525070841486572708917307)
    ·
      refine ⟨164287606262229859063375961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109525070841486572708917307 164287606262229859063375961)
      ·
        refine ⟨123215704696672394297531971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164287606262229859063375961 123215704696672394297531971)
        ·
          refine ⟨184823557045008591446297957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123215704696672394297531971 184823557045008591446297957)
          ·
            refine ⟨34654416945939110896180867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 184823557045008591446297957 34654416945939110896180867)
            ·
              refine ⟨51981625418908666344271301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34654416945939110896180867 51981625418908666344271301)
              ·
                refine ⟨9746554766045374939550869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51981625418908666344271301 9746554766045374939550869)
                ·
                  refine ⟨456869754658376950291447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9746554766045374939550869 456869754658376950291447)
                  ·
                    rfl

theorem cell21_2001939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 4, 6].length) (baseStart_2001939 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2001939 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2001939 prefixEnd_2001939 := by exact prefixLift 2001939
  have htrace : WordTrace (prefixWord ++ tailWord_2001939) baseStart_2001939 baseEnd_2001939 := by
    simpa [prefixWord, tailWord_2001939, baseEnd_2001939] using wordTrace_append hprefix tailTrace_2001939
  have hstable : (prefixWord ++ tailWord_2001939).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2001939).length < 2 ^ (prefixWord ++ tailWord_2001939).sum := by decide
  have hdescent : baseEnd_2001939 < baseStart_2001939 := by decide
  rcases family_descends (prefixWord ++ tailWord_2001939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2001959 : List Nat := [1, 1, 7, 1, 1, 2, 2, 1, 5]
def baseStart_2001959 : Nat := 118140960795 + 2001959 * 2 ^ 59
def prefixEnd_2001959 : Nat := 4983230072969 + 3 ^ 40 * 2001959 * 2
def baseEnd_2001959 : Nat := 456874318930861359958073

theorem tailTrace_2001959 : CollatzResearch.WordTrace tailWord_2001959 prefixEnd_2001959 456874318930861359958073 := by
  unfold tailWord_2001959
  simp only [CollatzResearch.WordTrace]
  refine ⟨73017443354251925221672931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48678295569501283481115287 73017443354251925221672931)
  ·
    refine ⟨109526165031377887832509397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73017443354251925221672931 109526165031377887832509397)
    ·
      refine ⟨2567019492922919246074439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 109526165031377887832509397 2567019492922919246074439)
      ·
        refine ⟨3850529239384378869111659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2567019492922919246074439 3850529239384378869111659)
        ·
          refine ⟨5775793859076568303667489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3850529239384378869111659 5775793859076568303667489)
          ·
            refine ⟨4331845394307426227750617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5775793859076568303667489 4331845394307426227750617)
            ·
              refine ⟨3248884045730569670812963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4331845394307426227750617 3248884045730569670812963)
              ·
                refine ⟨4873326068595854506219445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3248884045730569670812963 4873326068595854506219445)
                ·
                  refine ⟨456874318930861359958073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4873326068595854506219445 456874318930861359958073)
                  ·
                    rfl

theorem cell21_2001959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 2, 1, 5].length) (baseStart_2001959 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2001959 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2001959 prefixEnd_2001959 := by exact prefixLift 2001959
  have htrace : WordTrace (prefixWord ++ tailWord_2001959) baseStart_2001959 baseEnd_2001959 := by
    simpa [prefixWord, tailWord_2001959, baseEnd_2001959] using wordTrace_append hprefix tailTrace_2001959
  have hstable : (prefixWord ++ tailWord_2001959).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2001959).length < 2 ^ (prefixWord ++ tailWord_2001959).sum := by decide
  have hdescent : baseEnd_2001959 < baseStart_2001959 := by decide
  rcases family_descends (prefixWord ++ tailWord_2001959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2001970 : List Nat := [3, 2, 1, 1, 2, 2, 2, 8]
def baseStart_2001970 : Nat := 118140960795 + 2001970 * 2 ^ 59
def prefixEnd_2001970 : Nat := 4983230072969 + 3 ^ 40 * 2001970 * 2
def baseEnd_2001970 : Nat := 152292276426909261758239

theorem tailTrace_2001970 : CollatzResearch.WordTrace tailWord_2001970 prefixEnd_2001970 152292276426909261758239 := by
  unfold tailWord_2001970
  simp only [CollatzResearch.WordTrace]
  refine ⟨18254461139303018525080841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48678563038141382733548909 18254461139303018525080841)
  ·
    refine ⟨13690845854477263893810631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18254461139303018525080841 13690845854477263893810631)
    ·
      refine ⟨20536268781715895840715947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13690845854477263893810631 20536268781715895840715947)
      ·
        refine ⟨30804403172573843761073921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20536268781715895840715947 30804403172573843761073921)
        ·
          refine ⟨23103302379430382820805441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30804403172573843761073921 23103302379430382820805441)
          ·
            refine ⟨17327476784572787115604081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23103302379430382820805441 17327476784572787115604081)
            ·
              refine ⟨12995607588429590336703061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17327476784572787115604081 12995607588429590336703061)
              ·
                refine ⟨152292276426909261758239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12995607588429590336703061 152292276426909261758239)
                ·
                  rfl

theorem cell21_2001970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 8].length) (baseStart_2001970 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2001970 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2001970 prefixEnd_2001970 := by exact prefixLift 2001970
  have htrace : WordTrace (prefixWord ++ tailWord_2001970) baseStart_2001970 baseEnd_2001970 := by
    simpa [prefixWord, tailWord_2001970, baseEnd_2001970] using wordTrace_append hprefix tailTrace_2001970
  have hstable : (prefixWord ++ tailWord_2001970).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2001970).length < 2 ^ (prefixWord ++ tailWord_2001970).sum := by decide
  have hdescent : baseEnd_2001970 < baseStart_2001970 := by decide
  rcases family_descends (prefixWord ++ tailWord_2001970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002015 : List Nat := [1, 1, 2, 3, 1, 1, 3, 3, 6]
def baseStart_2002015 : Nat := 118140960795 + 2002015 * 2 ^ 59
def prefixEnd_2002015 : Nat := 4983230072969 + 3 ^ 40 * 2002015 * 2
def baseEnd_2002015 : Nat := 456887098893817707024625

theorem tailTrace_2002015 : CollatzResearch.WordTrace tailWord_2002015 prefixEnd_2002015 456887098893817707024625 := by
  unfold tailWord_2002015
  simp only [CollatzResearch.WordTrace]
  refine ⟨73019485842049046785711499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48679657228032697857140999 73019485842049046785711499)
  ·
    refine ⟨109529228763073570178567249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73019485842049046785711499 109529228763073570178567249)
    ·
      refine ⟨82146921572305177633925437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109529228763073570178567249 82146921572305177633925437)
      ·
        refine ⟨30805095589614441612722039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82146921572305177633925437 30805095589614441612722039)
        ·
          refine ⟨46207643384421662419083059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30805095589614441612722039 46207643384421662419083059)
          ·
            refine ⟨69311465076632493628624589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46207643384421662419083059 69311465076632493628624589)
            ·
              refine ⟨25991799403737185110734221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69311465076632493628624589 25991799403737185110734221)
              ·
                refine ⟨9746924776401444416525333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25991799403737185110734221 9746924776401444416525333)
                ·
                  refine ⟨456887098893817707024625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9746924776401444416525333 456887098893817707024625)
                  ·
                    rfl

theorem cell21_2002015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 3, 6].length) (baseStart_2002015 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2002015 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2002015 prefixEnd_2002015 := by exact prefixLift 2002015
  have htrace : WordTrace (prefixWord ++ tailWord_2002015) baseStart_2002015 baseEnd_2002015 := by
    simpa [prefixWord, tailWord_2002015, baseEnd_2002015] using wordTrace_append hprefix tailTrace_2002015
  have hstable : (prefixWord ++ tailWord_2002015).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002015).length < 2 ^ (prefixWord ++ tailWord_2002015).sum := by decide
  have hdescent : baseEnd_2002015 < baseStart_2002015 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002024 : List Nat := [2, 1, 4, 4, 2, 1, 2, 1, 4]
def baseStart_2002024 : Nat := 118140960795 + 2002024 * 2 ^ 59
def prefixEnd_2002024 : Nat := 4983230072969 + 3 ^ 40 * 2002024 * 2
def baseEnd_2002024 : Nat := 456889152816435691374607

theorem tailTrace_2002024 : CollatzResearch.WordTrace tailWord_2002024 prefixEnd_2002024 456889152816435691374607 := by
  unfold tailWord_2002024
  simp only [CollatzResearch.WordTrace]
  refine ⟨36509907049508220661394563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48679876066010960881859417 36509907049508220661394563)
  ·
    refine ⟨54764860574262330992091845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36509907049508220661394563 54764860574262330992091845)
    ·
      refine ⟨10268411357674187061017221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54764860574262330992091845 10268411357674187061017221)
      ·
        refine ⟨1925327129563910073940729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10268411357674187061017221 1925327129563910073940729)
        ·
          refine ⟨1443995347172932555455547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1925327129563910073940729 1443995347172932555455547)
          ·
            refine ⟨2165993020759398833183321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1443995347172932555455547 2165993020759398833183321)
            ·
              refine ⟨1624494765569549124887491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2165993020759398833183321 1624494765569549124887491)
              ·
                refine ⟨2436742148354323687331237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1624494765569549124887491 2436742148354323687331237)
                ·
                  refine ⟨456889152816435691374607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2436742148354323687331237 456889152816435691374607)
                  ·
                    rfl

theorem cell21_2002024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 2, 1, 4].length) (baseStart_2002024 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2002024 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2002024 prefixEnd_2002024 := by exact prefixLift 2002024
  have htrace : WordTrace (prefixWord ++ tailWord_2002024) baseStart_2002024 baseEnd_2002024 := by
    simpa [prefixWord, tailWord_2002024, baseEnd_2002024] using wordTrace_append hprefix tailTrace_2002024
  have hstable : (prefixWord ++ tailWord_2002024).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002024).length < 2 ^ (prefixWord ++ tailWord_2002024).sum := by decide
  have hdescent : baseEnd_2002024 < baseStart_2002024 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002032 : List Nat := [2, 1, 1, 1, 5, 1, 3, 3, 4]
def baseStart_2002032 : Nat := 118140960795 + 2002032 * 2 ^ 59
def prefixEnd_2002032 : Nat := 4983230072969 + 3 ^ 40 * 2002032 * 2
def baseEnd_2002032 : Nat := 456890978525429455241257

theorem tailTrace_2002032 : CollatzResearch.WordTrace tailWord_2002032 prefixEnd_2002032 456890978525429455241257 := by
  unfold tailWord_2002032
  simp only [CollatzResearch.WordTrace]
  refine ⟨36510052941493729344540175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48680070588658305792720233 36510052941493729344540175)
  ·
    refine ⟨54765079412240594016810263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36510052941493729344540175 54765079412240594016810263)
    ·
      refine ⟨82147619118360891025215395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54765079412240594016810263 82147619118360891025215395)
      ·
        refine ⟨123221428677541336537823093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82147619118360891025215395 123221428677541336537823093)
        ·
          refine ⟨11552008938519500300420915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 123221428677541336537823093 11552008938519500300420915)
          ·
            refine ⟨17328013407779250450631373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11552008938519500300420915 17328013407779250450631373)
            ·
              refine ⟨6498005027917218918986765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17328013407779250450631373 6498005027917218918986765)
              ·
                refine ⟨2436751885468957094620037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6498005027917218918986765 2436751885468957094620037)
                ·
                  refine ⟨456890978525429455241257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2436751885468957094620037 456890978525429455241257)
                  ·
                    rfl

theorem cell21_2002032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 3, 4].length) (baseStart_2002032 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2002032 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2002032 prefixEnd_2002032 := by exact prefixLift 2002032
  have htrace : WordTrace (prefixWord ++ tailWord_2002032) baseStart_2002032 baseEnd_2002032 := by
    simpa [prefixWord, tailWord_2002032, baseEnd_2002032] using wordTrace_append hprefix tailTrace_2002032
  have hstable : (prefixWord ++ tailWord_2002032).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002032).length < 2 ^ (prefixWord ++ tailWord_2002032).sum := by decide
  have hdescent : baseEnd_2002032 < baseStart_2002032 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002077 : List Nat := [1, 4, 2, 1, 1, 2, 2, 3, 5]
def baseStart_2002077 : Nat := 118140960795 + 2002077 * 2 ^ 59
def prefixEnd_2002077 : Nat := 4983230072969 + 3 ^ 40 * 2002077 * 2
def baseEnd_2002077 : Nat := 456901248138519376991165

theorem tailTrace_2002077 : CollatzResearch.WordTrace tailWord_2002077 prefixEnd_2002077 456901248138519376991165 := by
  unfold tailWord_2002077
  simp only [CollatzResearch.WordTrace]
  refine ⟨73021747167824431374468485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48681164778549620916312323 73021747167824431374468485)
  ·
    refine ⟨13691577593967080882712841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73021747167824431374468485 13691577593967080882712841)
    ·
      refine ⟨10268683195475310662034631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13691577593967080882712841 10268683195475310662034631)
      ·
        refine ⟨15403024793212965993051947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10268683195475310662034631 15403024793212965993051947)
        ·
          refine ⟨23104537189819448989577921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15403024793212965993051947 23104537189819448989577921)
          ·
            refine ⟨17328402892364586742183441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23104537189819448989577921 17328402892364586742183441)
            ·
              refine ⟨12996302169273440056637581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17328402892364586742183441 12996302169273440056637581)
              ·
                refine ⟨4873613313477540021239093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12996302169273440056637581 4873613313477540021239093)
                ·
                  refine ⟨456901248138519376991165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4873613313477540021239093 456901248138519376991165)
                  ·
                    rfl

theorem cell21_2002077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 3, 5].length) (baseStart_2002077 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2002077 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2002077 prefixEnd_2002077 := by exact prefixLift 2002077
  have htrace : WordTrace (prefixWord ++ tailWord_2002077) baseStart_2002077 baseEnd_2002077 := by
    simpa [prefixWord, tailWord_2002077, baseEnd_2002077] using wordTrace_append hprefix tailTrace_2002077
  have hstable : (prefixWord ++ tailWord_2002077).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002077).length < 2 ^ (prefixWord ++ tailWord_2002077).sum := by decide
  have hdescent : baseEnd_2002077 < baseStart_2002077 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002122 : List Nat := [3, 1, 2, 1, 3, 3, 8]
def baseStart_2002122 : Nat := 118140960795 + 2002122 * 2 ^ 59
def prefixEnd_2002122 : Nat := 4983230072969 + 3 ^ 40 * 2002122 * 2
def baseEnd_2002122 : Nat := 50767946416845477637897

theorem tailTrace_2002122 : CollatzResearch.WordTrace tailWord_2002122 prefixEnd_2002122 50767946416845477637897 := by
  unfold tailWord_2002122
  simp only [CollatzResearch.WordTrace]
  refine ⟨18255847113165351014964155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48682258968440936039904413 18255847113165351014964155)
  ·
    refine ⟨27383770669748026522446233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18255847113165351014964155 27383770669748026522446233)
    ·
      refine ⟨20537828002311019891834675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27383770669748026522446233 20537828002311019891834675)
      ·
        refine ⟨30806742003466529837752013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20537828002311019891834675 30806742003466529837752013)
        ·
          refine ⟨11552528251299948689157005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30806742003466529837752013 11552528251299948689157005)
          ·
            refine ⟨4332198094237480758433877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11552528251299948689157005 4332198094237480758433877)
            ·
              refine ⟨50767946416845477637897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4332198094237480758433877 50767946416845477637897)
              ·
                rfl

theorem cell21_2002122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 8].length) (baseStart_2002122 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2002122 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2002122 prefixEnd_2002122 := by exact prefixLift 2002122
  have htrace : WordTrace (prefixWord ++ tailWord_2002122) baseStart_2002122 baseEnd_2002122 := by
    simpa [prefixWord, tailWord_2002122, baseEnd_2002122] using wordTrace_append hprefix tailTrace_2002122
  have hstable : (prefixWord ++ tailWord_2002122).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002122).length < 2 ^ (prefixWord ++ tailWord_2002122).sum := by decide
  have hdescent : baseEnd_2002122 < baseStart_2002122 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002187 : List Nat := [1, 1, 1, 1, 5, 4, 3, 2, 3]
def baseStart_2002187 : Nat := 118140960795 + 2002187 * 2 ^ 59
def prefixEnd_2002187 : Nat := 4983230072969 + 3 ^ 40 * 2002187 * 2
def baseEnd_2002187 : Nat := 456926351637183630157607

theorem tailTrace_2002187 : CollatzResearch.WordTrace tailWord_2002187 prefixEnd_2002187 456926351637183630157607 := by
  unfold tailWord_2002187
  simp only [CollatzResearch.WordTrace]
  refine ⟨73025759197425920160972815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48683839464950613440648543 73025759197425920160972815)
  ·
    refine ⟨109538638796138880241459223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73025759197425920160972815 109538638796138880241459223)
    ·
      refine ⟨164307958194208320362188835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109538638796138880241459223 164307958194208320362188835)
      ·
        refine ⟨246461937291312480543283253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164307958194208320362188835 246461937291312480543283253)
        ·
          refine ⟨23105806621060545050932805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 246461937291312480543283253 23105806621060545050932805)
          ·
            refine ⟨4332338741448852197049901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23105806621060545050932805 4332338741448852197049901)
            ·
              refine ⟨1624627028043319573893713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4332338741448852197049901 1624627028043319573893713)
              ·
                refine ⟨1218470271032489680420285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1624627028043319573893713 1218470271032489680420285)
                ·
                  refine ⟨456926351637183630157607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1218470271032489680420285 456926351637183630157607)
                  ·
                    rfl

theorem cell21_2002187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 3, 2, 3].length) (baseStart_2002187 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2002187 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2002187 prefixEnd_2002187 := by exact prefixLift 2002187
  have htrace : WordTrace (prefixWord ++ tailWord_2002187) baseStart_2002187 baseEnd_2002187 := by
    simpa [prefixWord, tailWord_2002187, baseEnd_2002187] using wordTrace_append hprefix tailTrace_2002187
  have hstable : (prefixWord ++ tailWord_2002187).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002187).length < 2 ^ (prefixWord ++ tailWord_2002187).sum := by decide
  have hdescent : baseEnd_2002187 < baseStart_2002187 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002260 : List Nat := [2, 4, 1, 1, 2, 1, 1, 5, 4]
def baseStart_2002260 : Nat := 118140960795 + 2002260 * 2 ^ 59
def prefixEnd_2002260 : Nat := 4983230072969 + 3 ^ 40 * 2002260 * 2
def baseEnd_2002260 : Nat := 456943011231751725440791

theorem tailTrace_2002260 : CollatzResearch.WordTrace tailWord_2002260 prefixEnd_2002260 456943011231751725440791 := by
  unfold tailWord_2002260
  simp only [CollatzResearch.WordTrace]
  refine ⟨36514210863080726814190117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48685614484107635752253489 36514210863080726814190117)
  ·
    refine ⟨6846414536827636277660647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36514210863080726814190117 6846414536827636277660647)
    ·
      refine ⟨10269621805241454416490971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6846414536827636277660647 10269621805241454416490971)
      ·
        refine ⟨15404432707862181624736457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10269621805241454416490971 15404432707862181624736457)
        ·
          refine ⟨11553324530896636218552343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15404432707862181624736457 11553324530896636218552343)
          ·
            refine ⟨17329986796344954327828515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11553324530896636218552343 17329986796344954327828515)
            ·
              refine ⟨25994980194517431491742773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17329986796344954327828515 25994980194517431491742773)
              ·
                refine ⟨2437029393236009202350885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25994980194517431491742773 2437029393236009202350885)
                ·
                  refine ⟨456943011231751725440791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2437029393236009202350885 456943011231751725440791)
                  ·
                    rfl

theorem cell21_2002260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 5, 4].length) (baseStart_2002260 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2002260 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2002260 prefixEnd_2002260 := by exact prefixLift 2002260
  have htrace : WordTrace (prefixWord ++ tailWord_2002260) baseStart_2002260 baseEnd_2002260 := by
    simpa [prefixWord, tailWord_2002260, baseEnd_2002260] using wordTrace_append hprefix tailTrace_2002260
  have hstable : (prefixWord ++ tailWord_2002260).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002260).length < 2 ^ (prefixWord ++ tailWord_2002260).sum := by decide
  have hdescent : baseEnd_2002260 < baseStart_2002260 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002288 : List Nat := [2, 1, 1, 1, 4, 2, 1, 2, 7]
def baseStart_2002288 : Nat := 118140960795 + 2002288 * 2 ^ 59
def prefixEnd_2002288 : Nat := 4983230072969 + 3 ^ 40 * 2002288 * 2
def baseEnd_2002288 : Nat := 456949401213229898974067

theorem tailTrace_2002288 : CollatzResearch.WordTrace tailWord_2002288 prefixEnd_2002288 456949401213229898974067 := by
  unfold tailWord_2002288
  simp only [CollatzResearch.WordTrace]
  refine ⟨36514721485030007205199759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48686295313373342940266345 36514721485030007205199759)
  ·
    refine ⟨54772082227545010807799639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36514721485030007205199759 54772082227545010807799639)
    ·
      refine ⟨82158123341317516211699459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54772082227545010807799639 82158123341317516211699459)
      ·
        refine ⟨123237185011976274317549189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82158123341317516211699459 123237185011976274317549189)
        ·
          refine ⟨23106972189745551434540473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 123237185011976274317549189 23106972189745551434540473)
          ·
            refine ⟨17330229142309163575905355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23106972189745551434540473 17330229142309163575905355)
            ·
              refine ⟨25995343713463745363858033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17330229142309163575905355 25995343713463745363858033)
              ·
                refine ⟨19496507785097809022893525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25995343713463745363858033 19496507785097809022893525)
                ·
                  refine ⟨456949401213229898974067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19496507785097809022893525 456949401213229898974067)
                  ·
                    rfl

theorem cell21_2002288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 2, 7].length) (baseStart_2002288 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2002288 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2002288 prefixEnd_2002288 := by exact prefixLift 2002288
  have htrace : WordTrace (prefixWord ++ tailWord_2002288) baseStart_2002288 baseEnd_2002288 := by
    simpa [prefixWord, tailWord_2002288, baseEnd_2002288] using wordTrace_append hprefix tailTrace_2002288
  have hstable : (prefixWord ++ tailWord_2002288).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002288).length < 2 ^ (prefixWord ++ tailWord_2002288).sum := by decide
  have hdescent : baseEnd_2002288 < baseStart_2002288 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002440 : List Nat := [2, 1, 3, 2, 1, 1, 3, 1, 7]
def baseStart_2002440 : Nat := 118140960795 + 2002440 * 2 ^ 59
def prefixEnd_2002440 : Nat := 4983230072969 + 3 ^ 40 * 2002440 * 2
def baseEnd_2002440 : Nat := 456984089684111412440423

theorem tailTrace_2002440 : CollatzResearch.WordTrace tailWord_2002440 prefixEnd_2002440 456984089684111412440423 := by
  unfold tailWord_2002440
  simp only [CollatzResearch.WordTrace]
  refine ⟨36517493432754672184966387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48689991243672896246621849 36517493432754672184966387)
  ·
    refine ⟨54776240149132008277449581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36517493432754672184966387 54776240149132008277449581)
    ·
      refine ⟨20541090055924503104043593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54776240149132008277449581 20541090055924503104043593)
      ·
        refine ⟨15405817541943377328032695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20541090055924503104043593 15405817541943377328032695)
        ·
          refine ⟨23108726312915065992049043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15405817541943377328032695 23108726312915065992049043)
          ·
            refine ⟨34663089469372598988073565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23108726312915065992049043 34663089469372598988073565)
            ·
              refine ⟨12998658551014724620527587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34663089469372598988073565 12998658551014724620527587)
              ·
                refine ⟨19497987826522086930791381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12998658551014724620527587 19497987826522086930791381)
                ·
                  refine ⟨456984089684111412440423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19497987826522086930791381 456984089684111412440423)
                  ·
                    rfl

theorem cell21_2002440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 1, 7].length) (baseStart_2002440 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2002440 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2002440 prefixEnd_2002440 := by exact prefixLift 2002440
  have htrace : WordTrace (prefixWord ++ tailWord_2002440) baseStart_2002440 baseEnd_2002440 := by
    simpa [prefixWord, tailWord_2002440, baseEnd_2002440] using wordTrace_append hprefix tailTrace_2002440
  have hstable : (prefixWord ++ tailWord_2002440).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002440).length < 2 ^ (prefixWord ++ tailWord_2002440).sum := by decide
  have hdescent : baseEnd_2002440 < baseStart_2002440 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002443 : List Nat := [1, 1, 1, 1, 8, 1, 3, 5]
def baseStart_2002443 : Nat := 118140960795 + 2002443 * 2 ^ 59
def prefixEnd_2002443 : Nat := 4983230072969 + 3 ^ 40 * 2002443 * 2
def baseEnd_2002443 : Nat := 152328258108328024630139

theorem tailTrace_2002443 : CollatzResearch.WordTrace tailWord_2002443 prefixEnd_2002443 152328258108328024630139 := by
  unfold tailWord_2002443
  simp only [CollatzResearch.WordTrace]
  refine ⟨73035096284498475882291983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48690064189665650588194655 73035096284498475882291983)
  ·
    refine ⟨109552644426747713823437975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73035096284498475882291983 109552644426747713823437975)
    ·
      refine ⟨164328966640121570735156963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109552644426747713823437975 164328966640121570735156963)
      ·
        refine ⟨246493449960182356102735445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164328966640121570735156963 246493449960182356102735445)
        ·
          refine ⟨2888595116720886985578931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 246493449960182356102735445 2888595116720886985578931)
          ·
            refine ⟨4332892675081330478368397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2888595116720886985578931 4332892675081330478368397)
            ·
              refine ⟨1624834753155498929388149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4332892675081330478368397 1624834753155498929388149)
              ·
                refine ⟨152328258108328024630139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1624834753155498929388149 152328258108328024630139)
                ·
                  rfl

theorem cell21_2002443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 3, 5].length) (baseStart_2002443 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2002443 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2002443 prefixEnd_2002443 := by exact prefixLift 2002443
  have htrace : WordTrace (prefixWord ++ tailWord_2002443) baseStart_2002443 baseEnd_2002443 := by
    simpa [prefixWord, tailWord_2002443, baseEnd_2002443] using wordTrace_append hprefix tailTrace_2002443
  have hstable : (prefixWord ++ tailWord_2002443).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002443).length < 2 ^ (prefixWord ++ tailWord_2002443).sum := by decide
  have hdescent : baseEnd_2002443 < baseStart_2002443 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002474 : List Nat := [3, 1, 4, 1, 1, 1, 1, 6, 3]
def baseStart_2002474 : Nat := 118140960795 + 2002474 * 2 ^ 59
def prefixEnd_2002474 : Nat := 4983230072969 + 3 ^ 40 * 2002474 * 2
def baseEnd_2002474 : Nat := 456991848947334908873687

theorem tailTrace_2002474 : CollatzResearch.WordTrace tailWord_2002474 prefixEnd_2002474 456991848947334908873687 := by
  unfold tailWord_2002474
  simp only [CollatzResearch.WordTrace]
  refine ⟨18259056736846542044167619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48690817964924112117780317 18259056736846542044167619)
  ·
    refine ⟨27388585105269813066251429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18259056736846542044167619 27388585105269813066251429)
    ·
      refine ⟨5135359707238089949922143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27388585105269813066251429 5135359707238089949922143)
      ·
        refine ⟨7703039560857134924883215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5135359707238089949922143 7703039560857134924883215)
        ·
          refine ⟨11554559341285702387324823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7703039560857134924883215 11554559341285702387324823)
          ·
            refine ⟨17331839011928553580987235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11554559341285702387324823 17331839011928553580987235)
            ·
              refine ⟨25997758517892830371480853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17331839011928553580987235 25997758517892830371480853)
              ·
                refine ⟨1218644930526226423663165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 25997758517892830371480853 1218644930526226423663165)
                ·
                  refine ⟨456991848947334908873687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1218644930526226423663165 456991848947334908873687)
                  ·
                    rfl

theorem cell21_2002474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 6, 3].length) (baseStart_2002474 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2002474 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2002474 prefixEnd_2002474 := by exact prefixLift 2002474
  have htrace : WordTrace (prefixWord ++ tailWord_2002474) baseStart_2002474 baseEnd_2002474 := by
    simpa [prefixWord, tailWord_2002474, baseEnd_2002474] using wordTrace_append hprefix tailTrace_2002474
  have hstable : (prefixWord ++ tailWord_2002474).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002474).length < 2 ^ (prefixWord ++ tailWord_2002474).sum := by decide
  have hdescent : baseEnd_2002474 < baseStart_2002474 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002525 : List Nat := [1, 4, 4, 2, 1, 1, 3, 2, 3]
def baseStart_2002525 : Nat := 118140960795 + 2002525 * 2 ^ 59
def prefixEnd_2002525 : Nat := 4983230072969 + 3 ^ 40 * 2002525 * 2
def baseEnd_2002525 : Nat := 457003487842170153523583

theorem tailTrace_2002525 : CollatzResearch.WordTrace tailWord_2002525 prefixEnd_2002525 457003487842170153523583 := by
  unfold tailWord_2002525
  simp only [CollatzResearch.WordTrace]
  refine ⟨73038087070201403886777029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48692058046800935924518019 73038087070201403886777029)
  ·
    refine ⟨13694641325662763228770693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73038087070201403886777029 13694641325662763228770693)
    ·
      refine ⟨2567745248561768105394505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13694641325662763228770693 2567745248561768105394505)
      ·
        refine ⟨1925808936421326079045879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2567745248561768105394505 1925808936421326079045879)
        ·
          refine ⟨2888713404631989118568819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1925808936421326079045879 2888713404631989118568819)
          ·
            refine ⟨4333070106947983677853229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2888713404631989118568819 4333070106947983677853229)
            ·
              refine ⟨1624901290105493879194961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4333070106947983677853229 1624901290105493879194961)
              ·
                refine ⟨1218675967579120409396221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1624901290105493879194961 1218675967579120409396221)
                ·
                  refine ⟨457003487842170153523583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1218675967579120409396221 457003487842170153523583)
                  ·
                    rfl

theorem cell21_2002525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 3, 2, 3].length) (baseStart_2002525 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2002525 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2002525 prefixEnd_2002525 := by exact prefixLift 2002525
  have htrace : WordTrace (prefixWord ++ tailWord_2002525) baseStart_2002525 baseEnd_2002525 := by
    simpa [prefixWord, tailWord_2002525, baseEnd_2002525] using wordTrace_append hprefix tailTrace_2002525
  have hstable : (prefixWord ++ tailWord_2002525).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002525).length < 2 ^ (prefixWord ++ tailWord_2002525).sum := by decide
  have hdescent : baseEnd_2002525 < baseStart_2002525 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002533 : List Nat := [1, 3, 1, 3, 3, 1, 3, 1, 5]
def baseStart_2002533 : Nat := 118140960795 + 2002533 * 2 ^ 59
def prefixEnd_2002533 : Nat := 4983230072969 + 3 ^ 40 * 2002533 * 2
def baseEnd_2002533 : Nat := 457005313551163917390233

theorem tailTrace_2002533 : CollatzResearch.WordTrace tailWord_2002533 prefixEnd_2002533 457005313551163917390233 := by
  unfold tailWord_2002533
  simp only [CollatzResearch.WordTrace]
  refine ⟨73038378854172421253068253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48692252569448280835378835 73038378854172421253068253)
  ·
    refine ⟨27389392070314657969900595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73038378854172421253068253 27389392070314657969900595)
    ·
      refine ⟨41084088105471986954850893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27389392070314657969900595 41084088105471986954850893)
      ·
        refine ⟨15406533039551995108069085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41084088105471986954850893 15406533039551995108069085)
        ·
          refine ⟨5777449889831998165525907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15406533039551995108069085 5777449889831998165525907)
          ·
            refine ⟨8666174834747997248288861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5777449889831998165525907 8666174834747997248288861)
            ·
              refine ⟨3249815563030498968108323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8666174834747997248288861 3249815563030498968108323)
              ·
                refine ⟨4874723344545748452162485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3249815563030498968108323 4874723344545748452162485)
                ·
                  refine ⟨457005313551163917390233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4874723344545748452162485 457005313551163917390233)
                  ·
                    rfl

theorem cell21_2002533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 3, 1, 5].length) (baseStart_2002533 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2002533 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2002533 prefixEnd_2002533 := by exact prefixLift 2002533
  have htrace : WordTrace (prefixWord ++ tailWord_2002533) baseStart_2002533 baseEnd_2002533 := by
    simpa [prefixWord, tailWord_2002533, baseEnd_2002533] using wordTrace_append hprefix tailTrace_2002533
  have hstable : (prefixWord ++ tailWord_2002533).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002533).length < 2 ^ (prefixWord ++ tailWord_2002533).sum := by decide
  have hdescent : baseEnd_2002533 < baseStart_2002533 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002578 : List Nat := [3, 2, 3, 1, 3, 9]
def baseStart_2002578 : Nat := 118140960795 + 2002578 * 2 ^ 59
def prefixEnd_2002578 : Nat := 4983230072969 + 3 ^ 40 * 2002578 * 2
def baseEnd_2002578 : Nat := 16926503080157549597783

theorem tailTrace_2002578 : CollatzResearch.WordTrace tailWord_2002578 prefixEnd_2002578 16926503080157549597783 := by
  unfold tailWord_2002578
  simp only [CollatzResearch.WordTrace]
  refine ⟨18260005034752348484614097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48693346759339595958970925 18260005034752348484614097)
  ·
    refine ⟨13695003776064261363460573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18260005034752348484614097 13695003776064261363460573)
    ·
      refine ⟨5135626416024098011297715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13695003776064261363460573 5135626416024098011297715)
      ·
        refine ⟨7703439624036147016946573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5135626416024098011297715 7703439624036147016946573)
        ·
          refine ⟨2888789859013555131354965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7703439624036147016946573 2888789859013555131354965)
          ·
            refine ⟨16926503080157549597783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2888789859013555131354965 16926503080157549597783)
            ·
              rfl

theorem cell21_2002578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 9].length) (baseStart_2002578 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2002578 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2002578 prefixEnd_2002578 := by exact prefixLift 2002578
  have htrace : WordTrace (prefixWord ++ tailWord_2002578) baseStart_2002578 baseEnd_2002578 := by
    simpa [prefixWord, tailWord_2002578, baseEnd_2002578] using wordTrace_append hprefix tailTrace_2002578
  have hstable : (prefixWord ++ tailWord_2002578).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002578).length < 2 ^ (prefixWord ++ tailWord_2002578).sum := by decide
  have hdescent : baseEnd_2002578 < baseStart_2002578 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002657 : List Nat := [1, 2, 3, 1, 5, 1, 3, 1, 4]
def baseStart_2002657 : Nat := 118140960795 + 2002657 * 2 ^ 59
def prefixEnd_2002657 : Nat := 4983230072969 + 3 ^ 40 * 2002657 * 2
def baseEnd_2002657 : Nat := 457033612040567257323313

theorem tailTrace_2002657 : CollatzResearch.WordTrace tailWord_2002657 prefixEnd_2002657 457033612040567257323313 := by
  unfold tailWord_2002657
  simp only [CollatzResearch.WordTrace]
  refine ⟨73042901505723190430582225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48695267670482126953721483 73042901505723190430582225)
  ·
    refine ⟨54782176129292392822936669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73042901505723190430582225 54782176129292392822936669)
    ·
      refine ⟨20543316048484647308601251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54782176129292392822936669 20543316048484647308601251)
      ·
        refine ⟨30814974072726970962901877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20543316048484647308601251 30814974072726970962901877)
        ·
          refine ⟨2888903819318153527772051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30814974072726970962901877 2888903819318153527772051)
          ·
            refine ⟨4333355728977230291658077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2888903819318153527772051 4333355728977230291658077)
            ·
              refine ⟨1625008398366461359371779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4333355728977230291658077 1625008398366461359371779)
              ·
                refine ⟨2437512597549692039057669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1625008398366461359371779 2437512597549692039057669)
                ·
                  refine ⟨457033612040567257323313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2437512597549692039057669 457033612040567257323313)
                  ·
                    rfl

theorem cell21_2002657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 3, 1, 4].length) (baseStart_2002657 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2002657 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2002657 prefixEnd_2002657 := by exact prefixLift 2002657
  have htrace : WordTrace (prefixWord ++ tailWord_2002657) baseStart_2002657 baseEnd_2002657 := by
    simpa [prefixWord, tailWord_2002657, baseEnd_2002657] using wordTrace_append hprefix tailTrace_2002657
  have hstable : (prefixWord ++ tailWord_2002657).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002657).length < 2 ^ (prefixWord ++ tailWord_2002657).sum := by decide
  have hdescent : baseEnd_2002657 < baseStart_2002657 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002668 : List Nat := [2, 2, 1, 1, 2, 2, 4, 2, 5]
def baseStart_2002668 : Nat := 118140960795 + 2002668 * 2 ^ 59
def prefixEnd_2002668 : Nat := 4983230072969 + 3 ^ 40 * 2002668 * 2
def baseEnd_2002668 : Nat := 457036122390433682639957

theorem tailTrace_2002668 : CollatzResearch.WordTrace tailWord_2002668 prefixEnd_2002668 457036122390433682639957 := by
  unfold tailWord_2002668
  simp only [CollatzResearch.WordTrace]
  refine ⟨36521651354341669654616329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48695535139122226206155105 36521651354341669654616329)
  ·
    refine ⟨27391238515756252240962247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36521651354341669654616329 27391238515756252240962247)
    ·
      refine ⟨41086857773634378361443371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27391238515756252240962247 41086857773634378361443371)
      ·
        refine ⟨61630286660451567542165057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41086857773634378361443371 61630286660451567542165057)
        ·
          refine ⟨46222714995338675656623793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61630286660451567542165057 46222714995338675656623793)
          ·
            refine ⟨34667036246504006742467845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46222714995338675656623793 34667036246504006742467845)
            ·
              refine ⟨6500069296219501264212721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34667036246504006742467845 6500069296219501264212721)
              ·
                refine ⟨4875051972164625948159541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6500069296219501264212721 4875051972164625948159541)
                ·
                  refine ⟨457036122390433682639957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4875051972164625948159541 457036122390433682639957)
                  ·
                    rfl

theorem cell21_2002668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 5].length) (baseStart_2002668 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2002668 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2002668 prefixEnd_2002668 := by exact prefixLift 2002668
  have htrace : WordTrace (prefixWord ++ tailWord_2002668) baseStart_2002668 baseEnd_2002668 := by
    simpa [prefixWord, tailWord_2002668, baseEnd_2002668] using wordTrace_append hprefix tailTrace_2002668
  have hstable : (prefixWord ++ tailWord_2002668).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002668).length < 2 ^ (prefixWord ++ tailWord_2002668).sum := by decide
  have hdescent : baseEnd_2002668 < baseStart_2002668 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002685 : List Nat := [1, 4, 1, 1, 1, 1, 2, 7, 3]
def baseStart_2002685 : Nat := 118140960795 + 2002685 * 2 ^ 59
def prefixEnd_2002685 : Nat := 4983230072969 + 3 ^ 40 * 2002685 * 2
def baseEnd_2002685 : Nat := 457040002022045430856589

theorem tailTrace_2002685 : CollatzResearch.WordTrace tailWord_2002685 prefixEnd_2002685 457040002022045430856589 := by
  unfold tailWord_2002685
  simp only [CollatzResearch.WordTrace]
  refine ⟨73043922749621751212601509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48695948499747834141734339 73043922749621751212601509)
  ·
    refine ⟨13695735515554078352362783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73043922749621751212601509 13695735515554078352362783)
    ·
      refine ⟨20543603273331117528544175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13695735515554078352362783 20543603273331117528544175)
      ·
        refine ⟨30815404909996676292816263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20543603273331117528544175 30815404909996676292816263)
        ·
          refine ⟨46223107364995014439224395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30815404909996676292816263 46223107364995014439224395)
          ·
            refine ⟨69334661047492521658836593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46223107364995014439224395 69334661047492521658836593)
            ·
              refine ⟨52000995785619391244127445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69334661047492521658836593 52000995785619391244127445)
              ·
                refine ⟨1218773338725454482284237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 52000995785619391244127445 1218773338725454482284237)
                ·
                  refine ⟨457040002022045430856589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1218773338725454482284237 457040002022045430856589)
                  ·
                    rfl

theorem cell21_2002685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 7, 3].length) (baseStart_2002685 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2002685 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2002685 prefixEnd_2002685 := by exact prefixLift 2002685
  have htrace : WordTrace (prefixWord ++ tailWord_2002685) baseStart_2002685 baseEnd_2002685 := by
    simpa [prefixWord, tailWord_2002685, baseEnd_2002685] using wordTrace_append hprefix tailTrace_2002685
  have hstable : (prefixWord ++ tailWord_2002685).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002685).length < 2 ^ (prefixWord ++ tailWord_2002685).sum := by decide
  have hdescent : baseEnd_2002685 < baseStart_2002685 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002694 : List Nat := [6, 2, 2, 1, 1, 2, 1, 1, 5]
def baseStart_2002694 : Nat := 118140960795 + 2002694 * 2 ^ 59
def prefixEnd_2002694 : Nat := 4983230072969 + 3 ^ 40 * 2002694 * 2
def baseEnd_2002694 : Nat := 457042055944663415206571

theorem tailTrace_2002694 : CollatzResearch.WordTrace tailWord_2002694 prefixEnd_2002694 457042055944663415206571 := by
  unfold tailWord_2002694
  simp only [CollatzResearch.WordTrace]
  refine ⟨2282632843955910804677473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 48696167337726097166452757 2282632843955910804677473)
  ·
    refine ⟨1711974632966933103508105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2282632843955910804677473 1711974632966933103508105)
    ·
      refine ⟨1283980974725199827631079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1711974632966933103508105 1283980974725199827631079)
      ·
        refine ⟨1925971462087799741446619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1283980974725199827631079 1925971462087799741446619)
        ·
          refine ⟨2888957193131699612169929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1925971462087799741446619 2888957193131699612169929)
          ·
            refine ⟨2166717894848774709127447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2888957193131699612169929 2166717894848774709127447)
            ·
              refine ⟨3250076842273162063691171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2166717894848774709127447 3250076842273162063691171)
              ·
                refine ⟨4875115263409743095536757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3250076842273162063691171 4875115263409743095536757)
                ·
                  refine ⟨457042055944663415206571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4875115263409743095536757 457042055944663415206571)
                  ·
                    rfl

theorem cell21_2002694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_2002694 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2002694 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2002694 prefixEnd_2002694 := by exact prefixLift 2002694
  have htrace : WordTrace (prefixWord ++ tailWord_2002694) baseStart_2002694 baseEnd_2002694 := by
    simpa [prefixWord, tailWord_2002694, baseEnd_2002694] using wordTrace_append hprefix tailTrace_2002694
  have hstable : (prefixWord ++ tailWord_2002694).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002694).length < 2 ^ (prefixWord ++ tailWord_2002694).sum := by decide
  have hdescent : baseEnd_2002694 < baseStart_2002694 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002708 : List Nat := [2, 4, 4, 1, 1, 2, 2, 1, 4]
def baseStart_2002708 : Nat := 118140960795 + 2002708 * 2 ^ 59
def prefixEnd_2002708 : Nat := 4983230072969 + 3 ^ 40 * 2002708 * 2
def baseEnd_2002708 : Nat := 457045250935402501973209

theorem tailTrace_2002708 : CollatzResearch.WordTrace tailWord_2002708 prefixEnd_2002708 457045250935402501973209 := by
  unfold tailWord_2002708
  simp only [CollatzResearch.WordTrace]
  refine ⟨36522380814269213070344389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48696507752358950760459185 36522380814269213070344389)
  ·
    refine ⟨6847946402675477450689573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36522380814269213070344389 6847946402675477450689573)
    ·
      refine ⟨1283989950501652022004295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6847946402675477450689573 1283989950501652022004295)
      ·
        refine ⟨1925984925752478033006443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1283989950501652022004295 1925984925752478033006443)
        ·
          refine ⟨2888977388628717049509665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1925984925752478033006443 2888977388628717049509665)
          ·
            refine ⟨2166733041471537787132249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2888977388628717049509665 2166733041471537787132249)
            ·
              refine ⟨1625049781103653340349187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2166733041471537787132249 1625049781103653340349187)
              ·
                refine ⟨2437574671655480010523781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1625049781103653340349187 2437574671655480010523781)
                ·
                  refine ⟨457045250935402501973209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2437574671655480010523781 457045250935402501973209)
                  ·
                    rfl

theorem cell21_2002708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 2, 1, 4].length) (baseStart_2002708 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2002708 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2002708 prefixEnd_2002708 := by exact prefixLift 2002708
  have htrace : WordTrace (prefixWord ++ tailWord_2002708) baseStart_2002708 baseEnd_2002708 := by
    simpa [prefixWord, tailWord_2002708, baseEnd_2002708] using wordTrace_append hprefix tailTrace_2002708
  have hstable : (prefixWord ++ tailWord_2002708).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002708).length < 2 ^ (prefixWord ++ tailWord_2002708).sum := by decide
  have hdescent : baseEnd_2002708 < baseStart_2002708 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002761 : List Nat := [1, 2, 1, 1, 2, 4, 3, 4, 3]
def baseStart_2002761 : Nat := 118140960795 + 2002761 * 2 ^ 59
def prefixEnd_2002761 : Nat := 4983230072969 + 3 ^ 40 * 2002761 * 2
def baseEnd_2002761 : Nat := 457057346257486187589767

theorem tailTrace_2002761 : CollatzResearch.WordTrace tailWord_2002761 prefixEnd_2002761 457057346257486187589767 := by
  unfold tailWord_2002761
  simp only [CollatzResearch.WordTrace]
  refine ⟨73046694697346416192368137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48697796464897610794912091 73046694697346416192368137)
  ·
    refine ⟨54785021023009812144276103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73046694697346416192368137 54785021023009812144276103)
    ·
      refine ⟨82177531534514718216414155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54785021023009812144276103 82177531534514718216414155)
      ·
        refine ⟨123266297301772077324621233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82177531534514718216414155 123266297301772077324621233)
        ·
          refine ⟨92449722976329057993465925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123266297301772077324621233 92449722976329057993465925)
          ·
            refine ⟨17334323058061698373774861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92449722976329057993465925 17334323058061698373774861)
            ·
              refine ⟨6500371146773136890165573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17334323058061698373774861 6500371146773136890165573)
              ·
                refine ⟨1218819590019963166906045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6500371146773136890165573 1218819590019963166906045)
                ·
                  refine ⟨457057346257486187589767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1218819590019963166906045 457057346257486187589767)
                  ·
                    rfl

theorem cell21_2002761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 4, 3].length) (baseStart_2002761 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2002761 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2002761 prefixEnd_2002761 := by exact prefixLift 2002761
  have htrace : WordTrace (prefixWord ++ tailWord_2002761) baseStart_2002761 baseEnd_2002761 := by
    simpa [prefixWord, tailWord_2002761, baseEnd_2002761] using wordTrace_append hprefix tailTrace_2002761
  have hstable : (prefixWord ++ tailWord_2002761).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002761).length < 2 ^ (prefixWord ++ tailWord_2002761).sum := by decide
  have hdescent : baseEnd_2002761 < baseStart_2002761 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002803 : List Nat := [1, 1, 1, 2, 2, 1, 3, 1, 9]
def baseStart_2002803 : Nat := 118140960795 + 2002803 * 2 ^ 59
def prefixEnd_2002803 : Nat := 4983230072969 + 3 ^ 40 * 2002803 * 2
def baseEnd_2002803 : Nat := 457066931229703447889681

theorem tailTrace_2002803 : CollatzResearch.WordTrace tailWord_2002803 prefixEnd_2002803 457066931229703447889681 := by
  unfold tailWord_2002803
  simp only [CollatzResearch.WordTrace]
  refine ⟨73048226563194257365397063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48698817708796171576931375 73048226563194257365397063)
  ·
    refine ⟨109572339844791386048095595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73048226563194257365397063 109572339844791386048095595)
    ·
      refine ⟨164358509767187079072143393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109572339844791386048095595 164358509767187079072143393)
      ·
        refine ⟨123268882325390309304107545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164358509767187079072143393 123268882325390309304107545)
        ·
          refine ⟨92451661744042731978080659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123268882325390309304107545 92451661744042731978080659)
          ·
            refine ⟨138677492616064097967120989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92451661744042731978080659 138677492616064097967120989)
            ·
              refine ⟨52004059731024036737670371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138677492616064097967120989 52004059731024036737670371)
              ·
                refine ⟨78006089596536055106505557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52004059731024036737670371 78006089596536055106505557)
                ·
                  refine ⟨457066931229703447889681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 78006089596536055106505557 457066931229703447889681)
                  ·
                    rfl

theorem cell21_2002803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 9].length) (baseStart_2002803 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2002803 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2002803 prefixEnd_2002803 := by exact prefixLift 2002803
  have htrace : WordTrace (prefixWord ++ tailWord_2002803) baseStart_2002803 baseEnd_2002803 := by
    simpa [prefixWord, tailWord_2002803, baseEnd_2002803] using wordTrace_append hprefix tailTrace_2002803
  have hstable : (prefixWord ++ tailWord_2002803).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002803).length < 2 ^ (prefixWord ++ tailWord_2002803).sum := by decide
  have hdescent : baseEnd_2002803 < baseStart_2002803 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002820 : List Nat := [2, 3, 2, 1, 1, 1, 3, 3, 5]
def baseStart_2002820 : Nat := 118140960795 + 2002820 * 2 ^ 59
def prefixEnd_2002820 : Nat := 4983230072969 + 3 ^ 40 * 2002820 * 2
def baseEnd_2002820 : Nat := 457070810861315196106313

theorem tailTrace_2002820 : CollatzResearch.WordTrace tailWord_2002820 prefixEnd_2002820 457070810861315196106313 := by
  unfold tailWord_2002820
  simp only [CollatzResearch.WordTrace]
  refine ⟨36524423302066334634382957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48699231069421779512510609 36524423302066334634382957)
  ·
    refine ⟨13696658738274875487893609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36524423302066334634382957 13696658738274875487893609)
    ·
      refine ⟨10272494053706156615920207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13696658738274875487893609 10272494053706156615920207)
      ·
        refine ⟨15408741080559234923880311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10272494053706156615920207 15408741080559234923880311)
        ·
          refine ⟨23113111620838852385820467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15408741080559234923880311 23113111620838852385820467)
          ·
            refine ⟨34669667431258278578730701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23113111620838852385820467 34669667431258278578730701)
            ·
              refine ⟨13001125286721854467024013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34669667431258278578730701 13001125286721854467024013)
              ·
                refine ⟨4875421982520695425134005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13001125286721854467024013 4875421982520695425134005)
                ·
                  refine ⟨457070810861315196106313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4875421982520695425134005 457070810861315196106313)
                  ·
                    rfl

theorem cell21_2002820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 3, 5].length) (baseStart_2002820 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2002820 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2002820 prefixEnd_2002820 := by exact prefixLift 2002820
  have htrace : WordTrace (prefixWord ++ tailWord_2002820) baseStart_2002820 baseEnd_2002820 := by
    simpa [prefixWord, tailWord_2002820, baseEnd_2002820] using wordTrace_append hprefix tailTrace_2002820
  have hstable : (prefixWord ++ tailWord_2002820).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002820).length < 2 ^ (prefixWord ++ tailWord_2002820).sum := by decide
  have hdescent : baseEnd_2002820 < baseStart_2002820 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002840 : List Nat := [2, 1, 2, 6, 1, 2, 2, 5]
def baseStart_2002840 : Nat := 118140960795 + 2002840 * 2 ^ 59
def prefixEnd_2002840 : Nat := 4983230072969 + 3 ^ 40 * 2002840 * 2
def baseEnd_2002840 : Nat := 152358458377933201924313

theorem tailTrace_2002840 : CollatzResearch.WordTrace tailWord_2002840 prefixEnd_2002840 152358458377933201924313 := by
  unfold tailWord_2002840
  simp only [CollatzResearch.WordTrace]
  refine ⟨36524788032030106342246987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48699717376040141789662649 36524788032030106342246987)
  ·
    refine ⟨54787182048045159513370481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36524788032030106342246987 54787182048045159513370481)
    ·
      refine ⟨41090386536033869635027861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54787182048045159513370481 41090386536033869635027861)
      ·
        refine ⟨1926111868876587639141931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 41090386536033869635027861 1926111868876587639141931)
        ·
          refine ⟨2889167803314881458712897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1926111868876587639141931 2889167803314881458712897)
          ·
            refine ⟨2166875852486161094034673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2889167803314881458712897 2166875852486161094034673)
            ·
              refine ⟨1625156889364620820526005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2166875852486161094034673 1625156889364620820526005)
              ·
                refine ⟨152358458377933201924313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1625156889364620820526005 152358458377933201924313)
                ·
                  rfl

theorem cell21_2002840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 2, 5].length) (baseStart_2002840 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2002840 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2002840 prefixEnd_2002840 := by exact prefixLift 2002840
  have htrace : WordTrace (prefixWord ++ tailWord_2002840) baseStart_2002840 baseEnd_2002840 := by
    simpa [prefixWord, tailWord_2002840, baseEnd_2002840] using wordTrace_append hprefix tailTrace_2002840
  have hstable : (prefixWord ++ tailWord_2002840).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002840).length < 2 ^ (prefixWord ++ tailWord_2002840).sum := by decide
  have hdescent : baseEnd_2002840 < baseStart_2002840 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002865 : List Nat := [1, 2, 2, 4, 2, 1, 9]
def baseStart_2002865 : Nat := 118140960795 + 2002865 * 2 ^ 59
def prefixEnd_2002865 : Nat := 4983230072969 + 3 ^ 40 * 2002865 * 2
def baseEnd_2002865 : Nat := 50786786719378346428469

theorem tailTrace_2002865 : CollatzResearch.WordTrace tailWord_2002865 prefixEnd_2002865 50786786719378346428469 := by
  unfold tailWord_2002865
  simp only [CollatzResearch.WordTrace]
  refine ⟨73050487888969641954154049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48700325259313094636102699 73050487888969641954154049)
  ·
    refine ⟨54787865916727231465615537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73050487888969641954154049 54787865916727231465615537)
    ·
      refine ⟨41090899437545423599211653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54787865916727231465615537 41090899437545423599211653)
      ·
        refine ⟨7704543644539766924852185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41090899437545423599211653 7704543644539766924852185)
        ·
          refine ⟨5778407733404825193639139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7704543644539766924852185 5778407733404825193639139)
          ·
            refine ⟨8667611600107237790458709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5778407733404825193639139 8667611600107237790458709)
            ·
              refine ⟨50786786719378346428469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8667611600107237790458709 50786786719378346428469)
              ·
                rfl

theorem cell21_2002865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 9].length) (baseStart_2002865 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2002865 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2002865 prefixEnd_2002865 := by exact prefixLift 2002865
  have htrace : WordTrace (prefixWord ++ tailWord_2002865) baseStart_2002865 baseEnd_2002865 := by
    simpa [prefixWord, tailWord_2002865, baseEnd_2002865] using wordTrace_append hprefix tailTrace_2002865
  have hstable : (prefixWord ++ tailWord_2002865).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002865).length < 2 ^ (prefixWord ++ tailWord_2002865).sum := by decide
  have hdescent : baseEnd_2002865 < baseStart_2002865 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002927 : List Nat := [1, 1, 2, 1, 4, 2, 4, 2, 4]
def baseStart_2002927 : Nat := 118140960795 + 2002927 * 2 ^ 59
def prefixEnd_2002927 : Nat := 4983230072969 + 3 ^ 40 * 2002927 * 2
def baseEnd_2002927 : Nat := 457095229719106787822761

theorem tailTrace_2002927 : CollatzResearch.WordTrace tailWord_2002927 prefixEnd_2002927 457095229719106787822761 := by
  unfold tailWord_2002927
  simp only [CollatzResearch.WordTrace]
  refine ⟨73052749214745026542911035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48701832809830017695274023 73052749214745026542911035)
  ·
    refine ⟨109579123822117539814366553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73052749214745026542911035 109579123822117539814366553)
    ·
      refine ⟨82184342866588154860774915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109579123822117539814366553 82184342866588154860774915)
      ·
        refine ⟨123276514299882232291162373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82184342866588154860774915 123276514299882232291162373)
        ·
          refine ⟨23114346431227918554592945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 123276514299882232291162373 23114346431227918554592945)
          ·
            refine ⟨17335759823420938915944709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23114346431227918554592945 17335759823420938915944709)
            ·
              refine ⟨3250454966891426046739633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17335759823420938915944709 3250454966891426046739633)
              ·
                refine ⟨2437841225168569535054725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3250454966891426046739633 2437841225168569535054725)
                ·
                  refine ⟨457095229719106787822761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2437841225168569535054725 457095229719106787822761)
                  ·
                    rfl

theorem cell21_2002927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 4, 2, 4].length) (baseStart_2002927 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2002927 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2002927 prefixEnd_2002927 := by exact prefixLift 2002927
  have htrace : WordTrace (prefixWord ++ tailWord_2002927) baseStart_2002927 baseEnd_2002927 := by
    simpa [prefixWord, tailWord_2002927, baseEnd_2002927] using wordTrace_append hprefix tailTrace_2002927
  have hstable : (prefixWord ++ tailWord_2002927).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002927).length < 2 ^ (prefixWord ++ tailWord_2002927).sum := by decide
  have hdescent : baseEnd_2002927 < baseStart_2002927 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002941 : List Nat := [1, 4, 1, 1, 1, 2, 5, 6]
def baseStart_2002941 : Nat := 118140960795 + 2002941 * 2 ^ 59
def prefixEnd_2002941 : Nat := 4983230072969 + 3 ^ 40 * 2002941 * 2
def baseEnd_2002941 : Nat := 152366141569948624863133

theorem tailTrace_2002941 : CollatzResearch.WordTrace tailWord_2002941 prefixEnd_2002941 152366141569948624863133 := by
  unfold tailWord_2002941
  simp only [CollatzResearch.WordTrace]
  refine ⟨73053259836694306933920677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48702173224462871289280451 73053259836694306933920677)
  ·
    refine ⟨13697486219380182550110127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73053259836694306933920677 13697486219380182550110127)
    ·
      refine ⟨20546229329070273825165191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13697486219380182550110127 20546229329070273825165191)
      ·
        refine ⟨30819343993605410737747787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20546229329070273825165191 30819343993605410737747787)
        ·
          refine ⟨46229015990408116106621681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30819343993605410737747787 46229015990408116106621681)
          ·
            refine ⟨34671761992806087079966261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46229015990408116106621681 34671761992806087079966261)
            ·
              refine ⟨3250477686825570663746837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34671761992806087079966261 3250477686825570663746837)
              ·
                refine ⟨152366141569948624863133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3250477686825570663746837 152366141569948624863133)
                ·
                  rfl

theorem cell21_2002941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 5, 6].length) (baseStart_2002941 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2002941 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2002941 prefixEnd_2002941 := by exact prefixLift 2002941
  have htrace : WordTrace (prefixWord ++ tailWord_2002941) baseStart_2002941 baseEnd_2002941 := by
    simpa [prefixWord, tailWord_2002941, baseEnd_2002941] using wordTrace_append hprefix tailTrace_2002941
  have hstable : (prefixWord ++ tailWord_2002941).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002941).length < 2 ^ (prefixWord ++ tailWord_2002941).sum := by decide
  have hdescent : baseEnd_2002941 < baseStart_2002941 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002950 : List Nat := [6, 2, 1, 2, 1, 1, 3, 5]
def baseStart_2002950 : Nat := 118140960795 + 2002950 * 2 ^ 59
def prefixEnd_2002950 : Nat := 4983230072969 + 3 ^ 40 * 2002950 * 2
def baseEnd_2002950 : Nat := 152366826210821286313127

theorem tailTrace_2002950 : CollatzResearch.WordTrace tailWord_2002950 prefixEnd_2002950 152366826210821286313127 := by
  unfold tailWord_2002950
  simp only [CollatzResearch.WordTrace]
  refine ⟨2282924627926928170968697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 48702392062441134313998869 2282924627926928170968697)
  ·
    refine ⟨1712193470945196128226523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2282924627926928170968697 1712193470945196128226523)
    ·
      refine ⟨2568290206417794192339785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1712193470945196128226523 2568290206417794192339785)
      ·
        refine ⟨1926217654813345644254839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2568290206417794192339785 1926217654813345644254839)
        ·
          refine ⟨2889326482220018466382259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1926217654813345644254839 2889326482220018466382259)
          ·
            refine ⟨4333989723330027699573389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2889326482220018466382259 4333989723330027699573389)
            ·
              refine ⟨1625246146248760387340021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4333989723330027699573389 1625246146248760387340021)
              ·
                refine ⟨152366826210821286313127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1625246146248760387340021 152366826210821286313127)
                ·
                  rfl

theorem cell21_2002950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 3, 5].length) (baseStart_2002950 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2002950 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2002950 prefixEnd_2002950 := by exact prefixLift 2002950
  have htrace : WordTrace (prefixWord ++ tailWord_2002950) baseStart_2002950 baseEnd_2002950 := by
    simpa [prefixWord, tailWord_2002950, baseEnd_2002950] using wordTrace_append hprefix tailTrace_2002950
  have hstable : (prefixWord ++ tailWord_2002950).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002950).length < 2 ^ (prefixWord ++ tailWord_2002950).sum := by decide
  have hdescent : baseEnd_2002950 < baseStart_2002950 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002958 : List Nat := [4, 1, 1, 2, 2, 1, 5, 5]
def baseStart_2002958 : Nat := 118140960795 + 2002958 * 2 ^ 59
def prefixEnd_2002958 : Nat := 4983230072969 + 3 ^ 40 * 2002958 * 2
def baseEnd_2002958 : Nat := 152367434780485874268677

theorem tailTrace_2002958 : CollatzResearch.WordTrace tailWord_2002958 prefixEnd_2002958 152367434780485874268677 := by
  unfold tailWord_2002958
  simp only [CollatzResearch.WordTrace]
  refine ⟨9131734984704089854661191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48702586585088479224859685 9131734984704089854661191)
  ·
    refine ⟨13697602477056134781991787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9131734984704089854661191 13697602477056134781991787)
    ·
      refine ⟨20546403715584202172987681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13697602477056134781991787 20546403715584202172987681)
      ·
        refine ⟨15409802786688151629740761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20546403715584202172987681 15409802786688151629740761)
        ·
          refine ⟨11557352090016113722305571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15409802786688151629740761 11557352090016113722305571)
          ·
            refine ⟨17336028135024170583458357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11557352090016113722305571 17336028135024170583458357)
            ·
              refine ⟨1625252637658515992199221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17336028135024170583458357 1625252637658515992199221)
              ·
                refine ⟨152367434780485874268677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1625252637658515992199221 152367434780485874268677)
                ·
                  rfl

theorem cell21_2002958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 5, 5].length) (baseStart_2002958 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2002958 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2002958 prefixEnd_2002958 := by exact prefixLift 2002958
  have htrace : WordTrace (prefixWord ++ tailWord_2002958) baseStart_2002958 baseEnd_2002958 := by
    simpa [prefixWord, tailWord_2002958, baseEnd_2002958] using wordTrace_append hprefix tailTrace_2002958
  have hstable : (prefixWord ++ tailWord_2002958).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002958).length < 2 ^ (prefixWord ++ tailWord_2002958).sum := by decide
  have hdescent : baseEnd_2002958 < baseStart_2002958 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002964 : List Nat := [2, 4, 3, 2, 1, 1, 2, 3, 3]
def baseStart_2002964 : Nat := 118140960795 + 2002964 * 2 ^ 59
def prefixEnd_2002964 : Nat := 4983230072969 + 3 ^ 40 * 2002964 * 2
def baseEnd_2002964 : Nat := 457103673623202945706019

theorem tailTrace_2002964 : CollatzResearch.WordTrace tailWord_2002964 prefixEnd_2002964 457103673623202945706019 := by
  unfold tailWord_2002964
  simp only [CollatzResearch.WordTrace]
  refine ⟨36527049357805490931003973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48702732477073987908005297 36527049357805490931003973)
  ·
    refine ⟨6848821754588529549563245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36527049357805490931003973 6848821754588529549563245)
    ·
      refine ⟨2568308157970698581086217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6848821754588529549563245 2568308157970698581086217)
      ·
        refine ⟨1926231118478023935814663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2568308157970698581086217 1926231118478023935814663)
        ·
          refine ⟨2889346677717035903721995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1926231118478023935814663 2889346677717035903721995)
          ·
            refine ⟨4334020016575553855582993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2889346677717035903721995 4334020016575553855582993)
            ·
              refine ⟨3250515012431665391687245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4334020016575553855582993 3250515012431665391687245)
              ·
                refine ⟨1218943129661874521882717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3250515012431665391687245 1218943129661874521882717)
                ·
                  refine ⟨457103673623202945706019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1218943129661874521882717 457103673623202945706019)
                  ·
                    rfl

theorem cell21_2002964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 2, 3, 3].length) (baseStart_2002964 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2002964 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2002964 prefixEnd_2002964 := by exact prefixLift 2002964
  have htrace : WordTrace (prefixWord ++ tailWord_2002964) baseStart_2002964 baseEnd_2002964 := by
    simpa [prefixWord, tailWord_2002964, baseEnd_2002964] using wordTrace_append hprefix tailTrace_2002964
  have hstable : (prefixWord ++ tailWord_2002964).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002964).length < 2 ^ (prefixWord ++ tailWord_2002964).sum := by decide
  have hdescent : baseEnd_2002964 < baseStart_2002964 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2003031 : List Nat := [1, 1, 3, 2, 2, 1, 2, 2, 7]
def baseStart_2003031 : Nat := 118140960795 + 2003031 * 2 ^ 59
def prefixEnd_2003031 : Nat := 4983230072969 + 3 ^ 40 * 2003031 * 2
def baseEnd_2003031 : Nat := 457118963936025718089215

theorem tailTrace_2003031 : CollatzResearch.WordTrace tailWord_2003031 prefixEnd_2003031 457118963936025718089215 := by
  unfold tailWord_2003031
  simp only [CollatzResearch.WordTrace]
  refine ⟨73056542406368252304696947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48704361604245501536464631 73056542406368252304696947)
  ·
    refine ⟨109584813609552378457045421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73056542406368252304696947 109584813609552378457045421)
    ·
      refine ⟨41094305103582141921392033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109584813609552378457045421 41094305103582141921392033)
      ·
        refine ⟨30820728827686606441044025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41094305103582141921392033 30820728827686606441044025)
        ·
          refine ⟨23115546620764954830783019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30820728827686606441044025 23115546620764954830783019)
          ·
            refine ⟨34673319931147432246174529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23115546620764954830783019 34673319931147432246174529)
            ·
              refine ⟨26004989948360574184630897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34673319931147432246174529 26004989948360574184630897)
              ·
                refine ⟨19503742461270430638473173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26004989948360574184630897 19503742461270430638473173)
                ·
                  refine ⟨457118963936025718089215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19503742461270430638473173 457118963936025718089215)
                  ·
                    rfl

theorem cell21_2003031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 2, 7].length) (baseStart_2003031 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2003031 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2003031 prefixEnd_2003031 := by exact prefixLift 2003031
  have htrace : WordTrace (prefixWord ++ tailWord_2003031) baseStart_2003031 baseEnd_2003031 := by
    simpa [prefixWord, tailWord_2003031, baseEnd_2003031] using wordTrace_append hprefix tailTrace_2003031
  have hstable : (prefixWord ++ tailWord_2003031).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2003031).length < 2 ^ (prefixWord ++ tailWord_2003031).sum := by decide
  have hdescent : baseEnd_2003031 < baseStart_2003031 := by decide
  rcases family_descends (prefixWord ++ tailWord_2003031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2003096 : List Nat := [2, 1, 2, 4, 3, 1, 2, 2, 4]
def baseStart_2003096 : Nat := 118140960795 + 2003096 * 2 ^ 59
def prefixEnd_2003096 : Nat := 4983230072969 + 3 ^ 40 * 2003096 * 2
def baseEnd_2003096 : Nat := 457133797821600049505749

theorem tailTrace_2003096 : CollatzResearch.WordTrace tailWord_2003096 prefixEnd_2003096 457133797821600049505749 := by
  unfold tailWord_2003096
  simp only [CollatzResearch.WordTrace]
  refine ⟨36529456575566384202906571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48705942100755178937208761 36529456575566384202906571)
  ·
    refine ⟨54794184863349576304359857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36529456575566384202906571 54794184863349576304359857)
    ·
      refine ⟨41095638647512182228269893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54794184863349576304359857 41095638647512182228269893)
      ·
        refine ⟨7705432246408534167800605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41095638647512182228269893 7705432246408534167800605)
        ·
          refine ⟨2889537092403200312925227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7705432246408534167800605 2889537092403200312925227)
          ·
            refine ⟨4334305638604800469387841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2889537092403200312925227 4334305638604800469387841)
            ·
              refine ⟨3250729228953600352040881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4334305638604800469387841 3250729228953600352040881)
              ·
                refine ⟨2438046921715200264030661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3250729228953600352040881 2438046921715200264030661)
                ·
                  refine ⟨457133797821600049505749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2438046921715200264030661 457133797821600049505749)
                  ·
                    rfl

theorem cell21_2003096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 2, 2, 4].length) (baseStart_2003096 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2003096 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2003096 prefixEnd_2003096 := by exact prefixLift 2003096
  have htrace : WordTrace (prefixWord ++ tailWord_2003096) baseStart_2003096 baseEnd_2003096 := by
    simpa [prefixWord, tailWord_2003096, baseEnd_2003096] using wordTrace_append hprefix tailTrace_2003096
  have hstable : (prefixWord ++ tailWord_2003096).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2003096).length < 2 ^ (prefixWord ++ tailWord_2003096).sum := by decide
  have hdescent : baseEnd_2003096 < baseStart_2003096 := by decide
  rcases family_descends (prefixWord ++ tailWord_2003096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2003158 : List Nat := [5, 2, 1, 2, 1, 2, 2, 1, 5]
def baseStart_2003158 : Nat := 118140960795 + 2003158 * 2 ^ 59
def prefixEnd_2003158 : Nat := 4983230072969 + 3 ^ 40 * 2003158 * 2
def baseEnd_2003158 : Nat := 457147947066301719472289

theorem tailTrace_2003158 : CollatzResearch.WordTrace tailWord_2003158 prefixEnd_2003158 457147947066301719472289 := by
  unfold tailWord_2003158
  simp only [CollatzResearch.WordTrace]
  refine ⟨4566323404806759562160633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48707449651272101996380085 4566323404806759562160633)
  ·
    refine ⟨3424742553605069671620475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4566323404806759562160633 3424742553605069671620475)
    ·
      refine ⟨5137113830407604507430713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3424742553605069671620475 5137113830407604507430713)
      ·
        refine ⟨3852835372805703380573035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5137113830407604507430713 3852835372805703380573035)
        ·
          refine ⟨5779253059208555070859553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3852835372805703380573035 5779253059208555070859553)
          ·
            refine ⟨4334439794406416303144665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5779253059208555070859553 4334439794406416303144665)
            ·
              refine ⟨3250829845804812227358499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4334439794406416303144665 3250829845804812227358499)
              ·
                refine ⟨4876244768707218341037749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3250829845804812227358499 4876244768707218341037749)
                ·
                  refine ⟨457147947066301719472289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4876244768707218341037749 457147947066301719472289)
                  ·
                    rfl

theorem cell21_2003158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_2003158 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2003158 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2003158 prefixEnd_2003158 := by exact prefixLift 2003158
  have htrace : WordTrace (prefixWord ++ tailWord_2003158) baseStart_2003158 baseEnd_2003158 := by
    simpa [prefixWord, tailWord_2003158, baseEnd_2003158] using wordTrace_append hprefix tailTrace_2003158
  have hstable : (prefixWord ++ tailWord_2003158).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2003158).length < 2 ^ (prefixWord ++ tailWord_2003158).sum := by decide
  have hdescent : baseEnd_2003158 < baseStart_2003158 := by decide
  rcases family_descends (prefixWord ++ tailWord_2003158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2003186 : List Nat := [3, 2, 1, 3, 2, 1, 4, 5]
def baseStart_2003186 : Nat := 118140960795 + 2003186 * 2 ^ 59
def prefixEnd_2003186 : Nat := 4983230072969 + 3 ^ 40 * 2003186 * 2
def baseEnd_2003186 : Nat := 152384779015926631001855

theorem tailTrace_2003186 : CollatzResearch.WordTrace tailWord_2003186 prefixEnd_2003186 152384779015926631001855 := by
  unfold tailWord_2003186
  simp only [CollatzResearch.WordTrace]
  refine ⟨18265548930201678444147353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48708130480537809184392941 18265548930201678444147353)
  ·
    refine ⟨13699161697651258833110515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18265548930201678444147353 13699161697651258833110515)
    ·
      refine ⟨20548742546476888249665773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13699161697651258833110515 20548742546476888249665773)
      ·
        refine ⟨7705778454928833093624665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20548742546476888249665773 7705778454928833093624665)
        ·
          refine ⟨5779333841196624820218499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7705778454928833093624665 5779333841196624820218499)
          ·
            refine ⟨8669000761794937230327749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5779333841196624820218499 8669000761794937230327749)
            ·
              refine ⟨1625437642836550730686453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8669000761794937230327749 1625437642836550730686453)
              ·
                refine ⟨152384779015926631001855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1625437642836550730686453 152384779015926631001855)
                ·
                  rfl

theorem cell21_2003186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 4, 5].length) (baseStart_2003186 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2003186 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2003186 prefixEnd_2003186 := by exact prefixLift 2003186
  have htrace : WordTrace (prefixWord ++ tailWord_2003186) baseStart_2003186 baseEnd_2003186 := by
    simpa [prefixWord, tailWord_2003186, baseEnd_2003186] using wordTrace_append hprefix tailTrace_2003186
  have hstable : (prefixWord ++ tailWord_2003186).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2003186).length < 2 ^ (prefixWord ++ tailWord_2003186).sum := by decide
  have hdescent : baseEnd_2003186 < baseStart_2003186 := by decide
  rcases family_descends (prefixWord ++ tailWord_2003186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2003214 : List Nat := [4, 1, 1, 2, 1, 2, 1, 3, 6]
def baseStart_2003214 : Nat := 118140960795 + 2003214 * 2 ^ 59
def prefixEnd_2003214 : Nat := 4983230072969 + 3 ^ 40 * 2003214 * 2
def baseEnd_2003214 : Nat := 457160727029258066538841

theorem tailTrace_2003214 : CollatzResearch.WordTrace tailWord_2003214 prefixEnd_2003214 457160727029258066538841 := by
  unfold tailWord_2003214
  simp only [CollatzResearch.WordTrace]
  refine ⟨9132902120588159319826087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48708811309803516372405797 9132902120588159319826087)
  ·
    refine ⟨13699353180882238979739131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9132902120588159319826087 13699353180882238979739131)
    ·
      refine ⟨20549029771323358469608697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13699353180882238979739131 20549029771323358469608697)
      ·
        refine ⟨15411772328492518852206523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20549029771323358469608697 15411772328492518852206523)
        ·
          refine ⟨23117658492738778278309785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15411772328492518852206523 23117658492738778278309785)
          ·
            refine ⟨17338243869554083708732339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23117658492738778278309785 17338243869554083708732339)
            ·
              refine ⟨26007365804331125563098509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17338243869554083708732339 26007365804331125563098509)
              ·
                refine ⟨9752762176624172086161941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26007365804331125563098509 9752762176624172086161941)
                ·
                  refine ⟨457160727029258066538841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9752762176624172086161941 457160727029258066538841)
                  ·
                    rfl

theorem cell21_2003214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 3, 6].length) (baseStart_2003214 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2003214 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2003214 prefixEnd_2003214 := by exact prefixLift 2003214
  have htrace : WordTrace (prefixWord ++ tailWord_2003214) baseStart_2003214 baseEnd_2003214 := by
    simpa [prefixWord, tailWord_2003214, baseEnd_2003214] using wordTrace_append hprefix tailTrace_2003214
  have hstable : (prefixWord ++ tailWord_2003214).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2003214).length < 2 ^ (prefixWord ++ tailWord_2003214).sum := by decide
  have hdescent : baseEnd_2003214 < baseStart_2003214 := by decide
  rcases family_descends (prefixWord ++ tailWord_2003214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2003231 : List Nat := [1, 1, 2, 4, 3, 2, 1, 3, 4]
def baseStart_2003231 : Nat := 118140960795 + 2003231 * 2 ^ 59
def prefixEnd_2003231 : Nat := 4983230072969 + 3 ^ 40 * 2003231 * 2
def baseEnd_2003231 : Nat := 457164606660869814755473

theorem tailTrace_2003231 : CollatzResearch.WordTrace tailWord_2003231 prefixEnd_2003231 457164606660869814755473 := by
  unfold tailWord_2003231
  simp only [CollatzResearch.WordTrace]
  refine ⟨73063837005643686461977547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48709224670429124307985031 73063837005643686461977547)
  ·
    refine ⟨109595755508465529692966321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73063837005643686461977547 109595755508465529692966321)
    ·
      refine ⟨82196816631349147269724741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109595755508465529692966321 82196816631349147269724741)
      ·
        refine ⟨15411903118377965113073389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82196816631349147269724741 15411903118377965113073389)
        ·
          refine ⟨5779463669391736917402521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15411903118377965113073389 5779463669391736917402521)
          ·
            refine ⟨4334597752043802688051891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5779463669391736917402521 4334597752043802688051891)
            ·
              refine ⟨6501896628065704032077837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4334597752043802688051891 6501896628065704032077837)
              ·
                refine ⟨2438211235524639012029189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6501896628065704032077837 2438211235524639012029189)
                ·
                  refine ⟨457164606660869814755473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2438211235524639012029189 457164606660869814755473)
                  ·
                    rfl

theorem cell21_2003231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 3, 4].length) (baseStart_2003231 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2003231 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2003231 prefixEnd_2003231 := by exact prefixLift 2003231
  have htrace : WordTrace (prefixWord ++ tailWord_2003231) baseStart_2003231 baseEnd_2003231 := by
    simpa [prefixWord, tailWord_2003231, baseEnd_2003231] using wordTrace_append hprefix tailTrace_2003231
  have hstable : (prefixWord ++ tailWord_2003231).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2003231).length < 2 ^ (prefixWord ++ tailWord_2003231).sum := by decide
  have hdescent : baseEnd_2003231 < baseStart_2003231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2003231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2003268 : List Nat := [2, 3, 4, 1, 2, 2, 2, 2, 3]
def baseStart_2003268 : Nat := 118140960795 + 2003268 * 2 ^ 59
def prefixEnd_2003268 : Nat := 4983230072969 + 3 ^ 40 * 2003268 * 2
def baseEnd_2003268 : Nat := 457173050564965972638731

theorem tailTrace_2003268 : CollatzResearch.WordTrace tailWord_2003268 prefixEnd_2003268 457173050564965972638731 := by
  unfold tailWord_2003268
  simp only [CollatzResearch.WordTrace]
  refine ⟨36532593253254820890537229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48710124337673094520716305 36532593253254820890537229)
  ·
    refine ⟨13699722469970557833951461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36532593253254820890537229 13699722469970557833951461)
    ·
      refine ⟨2568697963119479593865899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13699722469970557833951461 2568697963119479593865899)
      ·
        refine ⟨3853046944679219390798849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2568697963119479593865899 3853046944679219390798849)
        ·
          refine ⟨2889785208509414543099137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3853046944679219390798849 2889785208509414543099137)
          ·
            refine ⟨2167338906382060907324353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2889785208509414543099137 2167338906382060907324353)
            ·
              refine ⟨1625504179786545680493265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2167338906382060907324353 1625504179786545680493265)
              ·
                refine ⟨1219128134839909260369949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1625504179786545680493265 1219128134839909260369949)
                ·
                  refine ⟨457173050564965972638731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1219128134839909260369949 457173050564965972638731)
                  ·
                    rfl

theorem cell21_2003268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 2, 2, 3].length) (baseStart_2003268 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2003268 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2003268 prefixEnd_2003268 := by exact prefixLift 2003268
  have htrace : WordTrace (prefixWord ++ tailWord_2003268) baseStart_2003268 baseEnd_2003268 := by
    simpa [prefixWord, tailWord_2003268, baseEnd_2003268] using wordTrace_append hprefix tailTrace_2003268
  have hstable : (prefixWord ++ tailWord_2003268).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2003268).length < 2 ^ (prefixWord ++ tailWord_2003268).sum := by decide
  have hdescent : baseEnd_2003268 < baseStart_2003268 := by decide
  rcases family_descends (prefixWord ++ tailWord_2003268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2003352 : List Nat := [2, 1, 2, 5, 1, 1, 2, 2, 5]
def baseStart_2003352 : Nat := 118140960795 + 2003352 * 2 ^ 59
def prefixEnd_2003352 : Nat := 4983230072969 + 3 ^ 40 * 2003352 * 2
def baseEnd_2003352 : Nat := 457192220509400493238559

theorem tailTrace_2003352 : CollatzResearch.WordTrace tailWord_2003352 prefixEnd_2003352 457192220509400493238559 := by
  unfold tailWord_2003352
  simp only [CollatzResearch.WordTrace]
  refine ⟨36534125119102662063566155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48712166825470216084754873 36534125119102662063566155)
  ·
    refine ⟨54801187678653993095349233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36534125119102662063566155 54801187678653993095349233)
    ·
      refine ⟨41100890758990494821511925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54801187678653993095349233 41100890758990494821511925)
      ·
        refine ⟨3853208508655358889516743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41100890758990494821511925 3853208508655358889516743)
        ·
          refine ⟨5779812762983038334275115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3853208508655358889516743 5779812762983038334275115)
          ·
            refine ⟨8669719144474557501412673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5779812762983038334275115 8669719144474557501412673)
            ·
              refine ⟨6502289358355918126059505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8669719144474557501412673 6502289358355918126059505)
              ·
                refine ⟨4876717018766938594544629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6502289358355918126059505 4876717018766938594544629)
                ·
                  refine ⟨457192220509400493238559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4876717018766938594544629 457192220509400493238559)
                  ·
                    rfl

theorem cell21_2003352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 2, 5].length) (baseStart_2003352 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2003352 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2003352 prefixEnd_2003352 := by exact prefixLift 2003352
  have htrace : WordTrace (prefixWord ++ tailWord_2003352) baseStart_2003352 baseEnd_2003352 := by
    simpa [prefixWord, tailWord_2003352, baseEnd_2003352] using wordTrace_append hprefix tailTrace_2003352
  have hstable : (prefixWord ++ tailWord_2003352).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2003352).length < 2 ^ (prefixWord ++ tailWord_2003352).sum := by decide
  have hdescent : baseEnd_2003352 < baseStart_2003352 := by decide
  rcases family_descends (prefixWord ++ tailWord_2003352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2003400 : List Nat := [2, 1, 3, 1, 3, 4, 2, 1, 4]
def baseStart_2003400 : Nat := 118140960795 + 2003400 * 2 ^ 59
def prefixEnd_2003400 : Nat := 4983230072969 + 3 ^ 40 * 2003400 * 2
def baseEnd_2003400 : Nat := 457203174763363076438461

theorem tailTrace_2003400 : CollatzResearch.WordTrace tailWord_2003400 prefixEnd_2003400 457203174763363076438461 := by
  unfold tailWord_2003400
  simp only [CollatzResearch.WordTrace]
  refine ⟨36535000471015714162439827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48713333961354285549919769 36535000471015714162439827)
  ·
    refine ⟨54802500706523571243659741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36535000471015714162439827 54802500706523571243659741)
    ·
      refine ⟨20550937764946339216372403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54802500706523571243659741 20550937764946339216372403)
      ·
        refine ⟨30826406647419508824558605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20550937764946339216372403 30826406647419508824558605)
        ·
          refine ⟨11559902492782315809209477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30826406647419508824558605 11559902492782315809209477)
          ·
            refine ⟨2167481717396684214226777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11559902492782315809209477 2167481717396684214226777)
            ·
              refine ⟨1625611288047513160670083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2167481717396684214226777 1625611288047513160670083)
              ·
                refine ⟨2438416932071269741005125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1625611288047513160670083 2438416932071269741005125)
                ·
                  refine ⟨457203174763363076438461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2438416932071269741005125 457203174763363076438461)
                  ·
                    rfl

theorem cell21_2003400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 2, 1, 4].length) (baseStart_2003400 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2003400 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2003400 prefixEnd_2003400 := by exact prefixLift 2003400
  have htrace : WordTrace (prefixWord ++ tailWord_2003400) baseStart_2003400 baseEnd_2003400 := by
    simpa [prefixWord, tailWord_2003400, baseEnd_2003400] using wordTrace_append hprefix tailTrace_2003400
  have hstable : (prefixWord ++ tailWord_2003400).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2003400).length < 2 ^ (prefixWord ++ tailWord_2003400).sum := by decide
  have hdescent : baseEnd_2003400 < baseStart_2003400 := by decide
  rcases family_descends (prefixWord ++ tailWord_2003400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2003462 : List Nat := [6, 2, 1, 1, 1, 1, 1, 1, 7]
def baseStart_2003462 : Nat := 118140960795 + 2003462 * 2 ^ 59
def prefixEnd_2003462 : Nat := 4983230072969 + 3 ^ 40 * 2003462 * 2
def baseEnd_2003462 : Nat := 457217324008064746405001

theorem tailTrace_2003462 : CollatzResearch.WordTrace tailWord_2003462 prefixEnd_2003462 457217324008064746405001 := by
  unfold tailWord_2003462
  simp only [CollatzResearch.WordTrace]
  refine ⟨2283508195868962903551145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 48714841511871208609091093 2283508195868962903551145)
  ·
    refine ⟨1712631146901722177663359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2283508195868962903551145 1712631146901722177663359)
    ·
      refine ⟨2568946720352583266495039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1712631146901722177663359 2568946720352583266495039)
      ·
        refine ⟨3853420080528874899742559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2568946720352583266495039 3853420080528874899742559)
        ·
          refine ⟨5780130120793312349613839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3853420080528874899742559 5780130120793312349613839)
          ·
            refine ⟨8670195181189968524420759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5780130120793312349613839 8670195181189968524420759)
            ·
              refine ⟨13005292771784952786631139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8670195181189968524420759 13005292771784952786631139)
              ·
                refine ⟨19507939157677429179946709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13005292771784952786631139 19507939157677429179946709)
                ·
                  refine ⟨457217324008064746405001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19507939157677429179946709 457217324008064746405001)
                  ·
                    rfl

theorem cell21_2003462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_2003462 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2003462 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2003462 prefixEnd_2003462 := by exact prefixLift 2003462
  have htrace : WordTrace (prefixWord ++ tailWord_2003462) baseStart_2003462 baseEnd_2003462 := by
    simpa [prefixWord, tailWord_2003462, baseEnd_2003462] using wordTrace_append hprefix tailTrace_2003462
  have hstable : (prefixWord ++ tailWord_2003462).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2003462).length < 2 ^ (prefixWord ++ tailWord_2003462).sum := by decide
  have hdescent : baseEnd_2003462 < baseStart_2003462 := by decide
  rcases family_descends (prefixWord ++ tailWord_2003462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2003504 : List Nat := [2, 1, 1, 1, 2, 3, 4, 4, 3]
def baseStart_2003504 : Nat := 118140960795 + 2003504 * 2 ^ 59
def prefixEnd_2003504 : Nat := 4983230072969 + 3 ^ 40 * 2003504 * 2
def baseEnd_2003504 : Nat := 457226908980282006704915

theorem tailTrace_2003504 : CollatzResearch.WordTrace tailWord_2003504 prefixEnd_2003504 457226908980282006704915 := by
  unfold tailWord_2003504
  simp only [CollatzResearch.WordTrace]
  refine ⟨36536897066827327043332783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48715862755769769391110377 36536897066827327043332783)
  ·
    refine ⟨54805345600240990564999175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36536897066827327043332783 54805345600240990564999175)
    ·
      refine ⟨82208018400361485847498763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54805345600240990564999175 82208018400361485847498763)
      ·
        refine ⟨123312027600542228771248145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82208018400361485847498763 123312027600542228771248145)
        ·
          refine ⟨92484020700406671578436109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123312027600542228771248145 92484020700406671578436109)
          ·
            refine ⟨34681507762652501841913541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92484020700406671578436109 34681507762652501841913541)
            ·
              refine ⟨6502782705497344095358789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34681507762652501841913541 6502782705497344095358789)
              ·
                refine ⟨1219271757280752017879773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6502782705497344095358789 1219271757280752017879773)
                ·
                  refine ⟨457226908980282006704915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1219271757280752017879773 457226908980282006704915)
                  ·
                    rfl

theorem cell21_2003504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 4, 3].length) (baseStart_2003504 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2003504 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2003504 prefixEnd_2003504 := by exact prefixLift 2003504
  have htrace : WordTrace (prefixWord ++ tailWord_2003504) baseStart_2003504 baseEnd_2003504 := by
    simpa [prefixWord, tailWord_2003504, baseEnd_2003504] using wordTrace_append hprefix tailTrace_2003504
  have hstable : (prefixWord ++ tailWord_2003504).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2003504).length < 2 ^ (prefixWord ++ tailWord_2003504).sum := by decide
  have hdescent : baseEnd_2003504 < baseStart_2003504 := by decide
  rcases family_descends (prefixWord ++ tailWord_2003504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2003532 : List Nat := [2, 2, 1, 3, 1, 2, 3, 7]
def baseStart_2003532 : Nat := 118140960795 + 2003532 * 2 ^ 59
def prefixEnd_2003532 : Nat := 4983230072969 + 3 ^ 40 * 2003532 * 2
def baseEnd_2003532 : Nat := 152411099653920060079397

theorem tailTrace_2003532 : CollatzResearch.WordTrace tailWord_2003532 prefixEnd_2003532 152411099653920060079397 := by
  unfold tailWord_2003532
  simp only [CollatzResearch.WordTrace]
  refine ⟨36537407688776607434342425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48716543585035476579123233 36537407688776607434342425)
  ·
    refine ⟨27403055766582455575756819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36537407688776607434342425 27403055766582455575756819)
    ·
      refine ⟨41104583649873683363635229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27403055766582455575756819 41104583649873683363635229)
      ·
        refine ⟨15414218868702631261363211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41104583649873683363635229 15414218868702631261363211)
        ·
          refine ⟨23121328303053946892044817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15414218868702631261363211 23121328303053946892044817)
          ·
            refine ⟨17340996227290460169033613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23121328303053946892044817 17340996227290460169033613)
            ·
              refine ⟨6502873585233922563387605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17340996227290460169033613 6502873585233922563387605)
              ·
                refine ⟨152411099653920060079397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6502873585233922563387605 152411099653920060079397)
                ·
                  rfl

theorem cell21_2003532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 7].length) (baseStart_2003532 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2003532 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2003532 prefixEnd_2003532 := by exact prefixLift 2003532
  have htrace : WordTrace (prefixWord ++ tailWord_2003532) baseStart_2003532 baseEnd_2003532 := by
    simpa [prefixWord, tailWord_2003532, baseEnd_2003532] using wordTrace_append hprefix tailTrace_2003532
  have hstable : (prefixWord ++ tailWord_2003532).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2003532).length < 2 ^ (prefixWord ++ tailWord_2003532).sum := by decide
  have hdescent : baseEnd_2003532 < baseStart_2003532 := by decide
  rcases family_descends (prefixWord ++ tailWord_2003532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2003656 : List Nat := [2, 1, 3, 1, 2, 3, 1, 5, 3]
def baseStart_2003656 : Nat := 118140960795 + 2003656 * 2 ^ 59
def prefixEnd_2003656 : Nat := 4983230072969 + 3 ^ 40 * 2003656 * 2
def baseEnd_2003656 : Nat := 457261597451163520171271

theorem tailTrace_2003656 : CollatzResearch.WordTrace tailWord_2003656 prefixEnd_2003656 457261597451163520171271 := by
  unfold tailWord_2003656
  simp only [CollatzResearch.WordTrace]
  refine ⟨36539669014551992023099411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48719558686069322697465881 36539669014551992023099411)
  ·
    refine ⟨54809503521827988034649117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36539669014551992023099411 54809503521827988034649117)
    ·
      refine ⟨20553563820685495512993419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54809503521827988034649117 20553563820685495512993419)
      ·
        refine ⟨30830345731028243269490129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20553563820685495512993419 30830345731028243269490129)
        ·
          refine ⟨23122759298271182452117597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30830345731028243269490129 23122759298271182452117597)
          ·
            refine ⟨8671034736851693419544099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23122759298271182452117597 8671034736851693419544099)
            ·
              refine ⟨13006552105277540129316149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8671034736851693419544099 13006552105277540129316149)
              ·
                refine ⟨1219364259869769387123389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13006552105277540129316149 1219364259869769387123389)
                ·
                  refine ⟨457261597451163520171271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1219364259869769387123389 457261597451163520171271)
                  ·
                    rfl

theorem cell21_2003656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 5, 3].length) (baseStart_2003656 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2003656 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2003656 prefixEnd_2003656 := by exact prefixLift 2003656
  have htrace : WordTrace (prefixWord ++ tailWord_2003656) baseStart_2003656 baseEnd_2003656 := by
    simpa [prefixWord, tailWord_2003656, baseEnd_2003656] using wordTrace_append hprefix tailTrace_2003656
  have hstable : (prefixWord ++ tailWord_2003656).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2003656).length < 2 ^ (prefixWord ++ tailWord_2003656).sum := by decide
  have hdescent : baseEnd_2003656 < baseStart_2003656 := by decide
  rcases family_descends (prefixWord ++ tailWord_2003656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2003729 : List Nat := [1, 2, 2, 1, 1, 3, 4, 1, 6]
def baseStart_2003729 : Nat := 118140960795 + 2003729 * 2 ^ 59
def prefixEnd_2003729 : Nat := 4983230072969 + 3 ^ 40 * 2003729 * 2
def baseEnd_2003729 : Nat := 457278257045731615454455

theorem tailTrace_2003729 : CollatzResearch.WordTrace tailWord_2003729 prefixEnd_2003729 457278257045731615454455 := by
  unfold tailWord_2003729
  simp only [CollatzResearch.WordTrace]
  refine ⟨73082000557839517513606241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48721333705226345009070827 73082000557839517513606241)
  ·
    refine ⟨54811500418379638135204681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73082000557839517513606241 54811500418379638135204681)
    ·
      refine ⟨41108625313784728601403511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54811500418379638135204681 41108625313784728601403511)
      ·
        refine ⟨61662937970677092902105267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41108625313784728601403511 61662937970677092902105267)
        ·
          refine ⟨92494406956015639353157901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61662937970677092902105267 92494406956015639353157901)
          ·
            refine ⟨34685402608505864757434213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92494406956015639353157901 34685402608505864757434213)
            ·
              refine ⟨6503512989094849642018915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34685402608505864757434213 6503512989094849642018915)
              ·
                refine ⟨9755269483642274463028373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6503512989094849642018915 9755269483642274463028373)
                ·
                  refine ⟨457278257045731615454455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9755269483642274463028373 457278257045731615454455)
                  ·
                    rfl

theorem cell21_2003729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 1, 6].length) (baseStart_2003729 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2003729 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2003729 prefixEnd_2003729 := by exact prefixLift 2003729
  have htrace : WordTrace (prefixWord ++ tailWord_2003729) baseStart_2003729 baseEnd_2003729 := by
    simpa [prefixWord, tailWord_2003729, baseEnd_2003729] using wordTrace_append hprefix tailTrace_2003729
  have hstable : (prefixWord ++ tailWord_2003729).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2003729).length < 2 ^ (prefixWord ++ tailWord_2003729).sum := by decide
  have hdescent : baseEnd_2003729 < baseStart_2003729 := by decide
  rcases family_descends (prefixWord ++ tailWord_2003729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2003777 : List Nat := [1, 2, 5, 3, 1, 9]
def baseStart_2003777 : Nat := 118140960795 + 2003777 * 2 ^ 59
def prefixEnd_2003777 : Nat := 4983230072969 + 3 ^ 40 * 2003777 * 2
def baseEnd_2003777 : Nat := 16936637455544229579791

theorem tailTrace_2003777 : CollatzResearch.WordTrace tailWord_2003777 prefixEnd_2003777 16936637455544229579791 := by
  unfold tailWord_2003777
  simp only [CollatzResearch.WordTrace]
  refine ⟨73083751261665621711353585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48722500841110414474235723 73083751261665621711353585)
  ·
    refine ⟨54812813446249216283515189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73083751261665621711353585 54812813446249216283515189)
    ·
      refine ⟨5138701260585864026579549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54812813446249216283515189 5138701260585864026579549)
      ·
        refine ⟨1927012972719699009967331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5138701260585864026579549 1927012972719699009967331)
        ·
          refine ⟨2890519459079548514950997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1927012972719699009967331 2890519459079548514950997)
          ·
            refine ⟨16936637455544229579791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2890519459079548514950997 16936637455544229579791)
            ·
              rfl

theorem cell21_2003777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 9].length) (baseStart_2003777 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2003777 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2003777 prefixEnd_2003777 := by exact prefixLift 2003777
  have htrace : WordTrace (prefixWord ++ tailWord_2003777) baseStart_2003777 baseEnd_2003777 := by
    simpa [prefixWord, tailWord_2003777, baseEnd_2003777] using wordTrace_append hprefix tailTrace_2003777
  have hstable : (prefixWord ++ tailWord_2003777).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2003777).length < 2 ^ (prefixWord ++ tailWord_2003777).sum := by decide
  have hdescent : baseEnd_2003777 < baseStart_2003777 := by decide
  rcases family_descends (prefixWord ++ tailWord_2003777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2003819 : List Nat := [1, 1, 1, 1, 2, 2, 4, 9]
def baseStart_2003819 : Nat := 118140960795 + 2003819 * 2 ^ 59
def prefixEnd_2003819 : Nat := 4983230072969 + 3 ^ 40 * 2003819 * 2
def baseEnd_2003819 : Nat := 152432932090637152984757

theorem tailTrace_2003819 : CollatzResearch.WordTrace tailWord_2003819 prefixEnd_2003819 152432932090637152984757 := by
  unfold tailWord_2003819
  simp only [CollatzResearch.WordTrace]
  refine ⟨73085283127513462884382511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48723522085008975256255007 73085283127513462884382511)
  ·
    refine ⟨109627924691270194326573767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73085283127513462884382511 109627924691270194326573767)
    ·
      refine ⟨164441887036905291489860651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109627924691270194326573767 164441887036905291489860651)
      ·
        refine ⟨246662830555357937234790977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164441887036905291489860651 246662830555357937234790977)
        ·
          refine ⟨184997122916518452926093233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246662830555357937234790977 184997122916518452926093233)
          ·
            refine ⟨138747842187388839694569925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184997122916518452926093233 138747842187388839694569925)
            ·
              refine ⟨26015220410135407442731861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 138747842187388839694569925 26015220410135407442731861)
              ·
                refine ⟨152432932090637152984757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26015220410135407442731861 152432932090637152984757)
                ·
                  rfl

theorem cell21_2003819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 9].length) (baseStart_2003819 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2003819 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2003819 prefixEnd_2003819 := by exact prefixLift 2003819
  have htrace : WordTrace (prefixWord ++ tailWord_2003819) baseStart_2003819 baseEnd_2003819 := by
    simpa [prefixWord, tailWord_2003819, baseEnd_2003819] using wordTrace_append hprefix tailTrace_2003819
  have hstable : (prefixWord ++ tailWord_2003819).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2003819).length < 2 ^ (prefixWord ++ tailWord_2003819).sum := by decide
  have hdescent : baseEnd_2003819 < baseStart_2003819 := by decide
  rcases family_descends (prefixWord ++ tailWord_2003819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2003842 : List Nat := [3, 4, 2, 2, 1, 1, 2, 1, 5]
def baseStart_2003842 : Nat := 118140960795 + 2003842 * 2 ^ 59
def prefixEnd_2003842 : Nat := 4983230072969 + 3 ^ 40 * 2003842 * 2
def baseEnd_2003842 : Nat := 457304045185268530070891

theorem tailTrace_2003842 : CollatzResearch.WordTrace tailWord_2003842 prefixEnd_2003842 457304045185268530070891 := by
  unfold tailWord_2003842
  simp only [CollatzResearch.WordTrace]
  refine ⟨18271530501607534453117445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48724081337620091874979853 18271530501607534453117445)
  ·
    refine ⟨3425911969051412709959521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18271530501607534453117445 3425911969051412709959521)
    ·
      refine ⟨2569433976788559532469641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3425911969051412709959521 2569433976788559532469641)
      ·
        refine ⟨1927075482591419649352231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2569433976788559532469641 1927075482591419649352231)
        ·
          refine ⟨2890613223887129474028347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1927075482591419649352231 2890613223887129474028347)
          ·
            refine ⟨4335919835830694211042521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2890613223887129474028347 4335919835830694211042521)
            ·
              refine ⟨3251939876873020658281891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4335919835830694211042521 3251939876873020658281891)
              ·
                refine ⟨4877909815309530987422837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3251939876873020658281891 4877909815309530987422837)
                ·
                  refine ⟨457304045185268530070891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4877909815309530987422837 457304045185268530070891)
                  ·
                    rfl

theorem cell21_2003842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_2003842 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2003842 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2003842 prefixEnd_2003842 := by exact prefixLift 2003842
  have htrace : WordTrace (prefixWord ++ tailWord_2003842) baseStart_2003842 baseEnd_2003842 := by
    simpa [prefixWord, tailWord_2003842, baseEnd_2003842] using wordTrace_append hprefix tailTrace_2003842
  have hstable : (prefixWord ++ tailWord_2003842).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2003842).length < 2 ^ (prefixWord ++ tailWord_2003842).sum := by decide
  have hdescent : baseEnd_2003842 < baseStart_2003842 := by decide
  rcases family_descends (prefixWord ++ tailWord_2003842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2003895 : List Nat := [1, 1, 3, 1, 3, 1, 11]
def baseStart_2003895 : Nat := 118140960795 + 2003895 * 2 ^ 59
def prefixEnd_2003895 : Nat := 4983230072969 + 3 ^ 40 * 2003895 * 2
def baseEnd_2003895 : Nat := 50812904500816912854161

theorem tailTrace_2003895 : CollatzResearch.WordTrace tailWord_2003895 prefixEnd_2003895 50812904500816912854161 := by
  unfold tailWord_2003895
  simp only [CollatzResearch.WordTrace]
  refine ⟨73088055075238127864149139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48725370050158751909432759 73088055075238127864149139)
  ·
    refine ⟨109632082612857191796223709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73088055075238127864149139 109632082612857191796223709)
    ·
      refine ⟨41112030979821446923583891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109632082612857191796223709 41112030979821446923583891)
      ·
        refine ⟨61668046469732170385375837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41112030979821446923583891 61668046469732170385375837)
        ·
          refine ⟨23125517426149563894515939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61668046469732170385375837 23125517426149563894515939)
          ·
            refine ⟨34688276139224345841773909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23125517426149563894515939 34688276139224345841773909)
            ·
              refine ⟨50812904500816912854161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 34688276139224345841773909 50812904500816912854161)
              ·
                rfl

theorem cell21_2003895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 11].length) (baseStart_2003895 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2003895 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2003895 prefixEnd_2003895 := by exact prefixLift 2003895
  have htrace : WordTrace (prefixWord ++ tailWord_2003895) baseStart_2003895 baseEnd_2003895 := by
    simpa [prefixWord, tailWord_2003895, baseEnd_2003895] using wordTrace_append hprefix tailTrace_2003895
  have hstable : (prefixWord ++ tailWord_2003895).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2003895).length < 2 ^ (prefixWord ++ tailWord_2003895).sum := by decide
  have hdescent : baseEnd_2003895 < baseStart_2003895 := by decide
  rcases family_descends (prefixWord ++ tailWord_2003895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2003901 : List Nat := [1, 4, 1, 2, 5, 1, 1, 1, 5]
def baseStart_2003901 : Nat := 118140960795 + 2003901 * 2 ^ 59
def prefixEnd_2003901 : Nat := 4983230072969 + 3 ^ 40 * 2003901 * 2
def baseEnd_2003901 : Nat := 457317509789097538587437

theorem tailTrace_2003901 : CollatzResearch.WordTrace tailWord_2003901 prefixEnd_2003901 457317509789097538587437 := by
  unfold tailWord_2003901
  simp only [CollatzResearch.WordTrace]
  refine ⟨73088273913216390888867557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48725515942144260592578371 73088273913216390888867557)
  ·
    refine ⟨13704051358728073291662667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73088273913216390888867557 13704051358728073291662667)
    ·
      refine ⟨20556077038092109937494001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13704051358728073291662667 20556077038092109937494001)
      ·
        refine ⟨15417057778569082453120501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20556077038092109937494001 15417057778569082453120501)
        ·
          refine ⟨1445349166740851479980047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15417057778569082453120501 1445349166740851479980047)
          ·
            refine ⟨2168023750111277219970071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1445349166740851479980047 2168023750111277219970071)
            ·
              refine ⟨3252035625166915829955107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2168023750111277219970071 3252035625166915829955107)
              ·
                refine ⟨4878053437750373744932661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3252035625166915829955107 4878053437750373744932661)
                ·
                  refine ⟨457317509789097538587437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4878053437750373744932661 457317509789097538587437)
                  ·
                    rfl

theorem cell21_2003901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 1, 1, 5].length) (baseStart_2003901 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2003901 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2003901 prefixEnd_2003901 := by exact prefixLift 2003901
  have htrace : WordTrace (prefixWord ++ tailWord_2003901) baseStart_2003901 baseEnd_2003901 := by
    simpa [prefixWord, tailWord_2003901, baseEnd_2003901] using wordTrace_append hprefix tailTrace_2003901
  have hstable : (prefixWord ++ tailWord_2003901).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2003901).length < 2 ^ (prefixWord ++ tailWord_2003901).sum := by decide
  have hdescent : baseEnd_2003901 < baseStart_2003901 := by decide
  rcases family_descends (prefixWord ++ tailWord_2003901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2003915 : List Nat := [1, 1, 1, 1, 3, 7, 2, 1, 4]
def baseStart_2003915 : Nat := 118140960795 + 2003915 * 2 ^ 59
def prefixEnd_2003915 : Nat := 4983230072969 + 3 ^ 40 * 2003915 * 2
def baseEnd_2003915 : Nat := 457320704779836625354075

theorem tailTrace_2003915 : CollatzResearch.WordTrace tailWord_2003915 prefixEnd_2003915 457320704779836625354075 := by
  unfold tailWord_2003915
  simp only [CollatzResearch.WordTrace]
  refine ⟨73088784535165671279877199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48725856356777114186584799 73088784535165671279877199)
  ·
    refine ⟨109633176802748506919815799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73088784535165671279877199 109633176802748506919815799)
    ·
      refine ⟨164449765204122760379723699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109633176802748506919815799 164449765204122760379723699)
      ·
        refine ⟨246674647806184140569585549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164449765204122760379723699 246674647806184140569585549)
        ·
          refine ⟨92502992927319052713594581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 246674647806184140569585549 92502992927319052713594581)
          ·
            refine ⟨2168038896734040297974873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 92502992927319052713594581 2168038896734040297974873)
            ·
              refine ⟨1626029172550530223481155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2168038896734040297974873 1626029172550530223481155)
              ·
                refine ⟨2439043758825795335221733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1626029172550530223481155 2439043758825795335221733)
                ·
                  refine ⟨457320704779836625354075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2439043758825795335221733 457320704779836625354075)
                  ·
                    rfl

theorem cell21_2003915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 2, 1, 4].length) (baseStart_2003915 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2003915 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2003915 prefixEnd_2003915 := by exact prefixLift 2003915
  have htrace : WordTrace (prefixWord ++ tailWord_2003915) baseStart_2003915 baseEnd_2003915 := by
    simpa [prefixWord, tailWord_2003915, baseEnd_2003915] using wordTrace_append hprefix tailTrace_2003915
  have hstable : (prefixWord ++ tailWord_2003915).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2003915).length < 2 ^ (prefixWord ++ tailWord_2003915).sum := by decide
  have hdescent : baseEnd_2003915 < baseStart_2003915 := by decide
  rcases family_descends (prefixWord ++ tailWord_2003915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2004275 : List Nat := [1, 1, 1, 2, 5, 2, 2, 7]
def baseStart_2004275 : Nat := 118140960795 + 2004275 * 2 ^ 59
def prefixEnd_2004275 : Nat := 4983230072969 + 3 ^ 40 * 2004275 * 2
def baseEnd_2004275 : Nat := 152467620561518666451113

theorem tailTrace_2004275 : CollatzResearch.WordTrace tailWord_2004275 prefixEnd_2004275 152467620561518666451113 := by
  unfold tailWord_2004275
  simp only [CollatzResearch.WordTrace]
  refine ⟨73101914813861452762982279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48734609875907635175321519 73101914813861452762982279)
  ·
    refine ⟨109652872220792179144473419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73101914813861452762982279 109652872220792179144473419)
    ·
      refine ⟨164479308331188268716710129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109652872220792179144473419 164479308331188268716710129)
      ·
        refine ⟨123359481248391201537532597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164479308331188268716710129 123359481248391201537532597)
        ·
          refine ⟨11564951367036675144143681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 123359481248391201537532597 11564951367036675144143681)
          ·
            refine ⟨8673713525277506358107761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11564951367036675144143681 8673713525277506358107761)
            ·
              refine ⟨6505285143958129768580821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8673713525277506358107761 6505285143958129768580821)
              ·
                refine ⟨152467620561518666451113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6505285143958129768580821 152467620561518666451113)
                ·
                  rfl

theorem cell21_2004275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 7].length) (baseStart_2004275 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2004275 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2004275 prefixEnd_2004275 := by exact prefixLift 2004275
  have htrace : WordTrace (prefixWord ++ tailWord_2004275) baseStart_2004275 baseEnd_2004275 := by
    simpa [prefixWord, tailWord_2004275, baseEnd_2004275] using wordTrace_append hprefix tailTrace_2004275
  have hstable : (prefixWord ++ tailWord_2004275).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2004275).length < 2 ^ (prefixWord ++ tailWord_2004275).sum := by decide
  have hdescent : baseEnd_2004275 < baseStart_2004275 := by decide
  rcases family_descends (prefixWord ++ tailWord_2004275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2004292 : List Nat := [2, 3, 4, 1, 1, 10]
def baseStart_2004292 : Nat := 118140960795 + 2004292 * 2 ^ 59
def prefixEnd_2004292 : Nat := 4983230072969 + 3 ^ 40 * 2004292 * 2
def baseEnd_2004292 : Nat := 16940990419117323984073

theorem tailTrace_2004292 : CollatzResearch.WordTrace tailWord_2004292 prefixEnd_2004292 16940990419117323984073 := by
  unfold tailWord_2004292
  simp only [CollatzResearch.WordTrace]
  refine ⟨36551267427399932333175565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48735023236533243110900753 36551267427399932333175565)
  ·
    refine ⟨13706725285274974624940837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36551267427399932333175565 13706725285274974624940837)
    ·
      refine ⟨2570010990989057742176407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13706725285274974624940837 2570010990989057742176407)
      ·
        refine ⟨3855016486483586613264611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2570010990989057742176407 3855016486483586613264611)
        ·
          refine ⟨5782524729725379919896917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3855016486483586613264611 5782524729725379919896917)
          ·
            refine ⟨16940990419117323984073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5782524729725379919896917 16940990419117323984073)
            ·
              rfl

theorem cell21_2004292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 10].length) (baseStart_2004292 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2004292 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2004292 prefixEnd_2004292 := by exact prefixLift 2004292
  have htrace : WordTrace (prefixWord ++ tailWord_2004292) baseStart_2004292 baseEnd_2004292 := by
    simpa [prefixWord, tailWord_2004292, baseEnd_2004292] using wordTrace_append hprefix tailTrace_2004292
  have hstable : (prefixWord ++ tailWord_2004292).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2004292).length < 2 ^ (prefixWord ++ tailWord_2004292).sum := by decide
  have hdescent : baseEnd_2004292 < baseStart_2004292 := by decide
  rcases family_descends (prefixWord ++ tailWord_2004292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2004306 : List Nat := [3, 2, 2, 1, 1, 1, 1, 5, 5]
def baseStart_2004306 : Nat := 118140960795 + 2004306 * 2 ^ 59
def prefixEnd_2004306 : Nat := 4983230072969 + 3 ^ 40 * 2004306 * 2
def baseEnd_2004306 : Nat := 457409936306906834336609

theorem tailTrace_2004306 : CollatzResearch.WordTrace tailWord_2004306 prefixEnd_2004306 457409936306906834336609 := by
  unfold tailWord_2004306
  simp only [CollatzResearch.WordTrace]
  refine ⟨18275761369187286264340193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48735363651166096704907181 18275761369187286264340193)
  ·
    refine ⟨13706821026890464698255145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18275761369187286264340193 13706821026890464698255145)
    ·
      refine ⟨10280115770167848523691359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13706821026890464698255145 10280115770167848523691359)
      ·
        refine ⟨15420173655251772785537039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10280115770167848523691359 15420173655251772785537039)
        ·
          refine ⟨23130260482877659178305559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15420173655251772785537039 23130260482877659178305559)
          ·
            refine ⟨34695390724316488767458339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23130260482877659178305559 34695390724316488767458339)
            ·
              refine ⟨52043086086474733151187509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34695390724316488767458339 52043086086474733151187509)
              ·
                refine ⟨4879039320607006232923829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52043086086474733151187509 4879039320607006232923829)
                ·
                  refine ⟨457409936306906834336609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4879039320607006232923829 457409936306906834336609)
                  ·
                    rfl

theorem cell21_2004306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 5, 5].length) (baseStart_2004306 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2004306 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2004306 prefixEnd_2004306 := by exact prefixLift 2004306
  have htrace : WordTrace (prefixWord ++ tailWord_2004306) baseStart_2004306 baseEnd_2004306 := by
    simpa [prefixWord, tailWord_2004306, baseEnd_2004306] using wordTrace_append hprefix tailTrace_2004306
  have hstable : (prefixWord ++ tailWord_2004306).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2004306).length < 2 ^ (prefixWord ++ tailWord_2004306).sum := by decide
  have hdescent : baseEnd_2004306 < baseStart_2004306 := by decide
  rcases family_descends (prefixWord ++ tailWord_2004306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2004396 : List Nat := [2, 2, 1, 1, 1, 1, 5, 2, 6]
def baseStart_2004396 : Nat := 118140960795 + 2004396 * 2 ^ 59
def prefixEnd_2004396 : Nat := 4983230072969 + 3 ^ 40 * 2004396 * 2
def baseEnd_2004396 : Nat := 457430475533086677836425

theorem tailTrace_2004396 : CollatzResearch.WordTrace tailWord_2004396 prefixEnd_2004396 457430475533086677836425 := by
  unfold tailWord_2004396
  simp only [CollatzResearch.WordTrace]
  refine ⟨36553164023211545214068521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48737552030948726952091361 36553164023211545214068521)
  ·
    refine ⟨27414873017408658910551391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36553164023211545214068521 27414873017408658910551391)
    ·
      refine ⟨41122309526112988365827087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27414873017408658910551391 41122309526112988365827087)
      ·
        refine ⟨61683464289169482548740631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41122309526112988365827087 61683464289169482548740631)
        ·
          refine ⟨92525196433754223823110947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61683464289169482548740631 92525196433754223823110947)
          ·
            refine ⟨138787794650631335734666421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92525196433754223823110947 138787794650631335734666421)
            ·
              refine ⟨13011355748496687725124977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 138787794650631335734666421 13011355748496687725124977)
              ·
                refine ⟨9758516811372515793843733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13011355748496687725124977 9758516811372515793843733)
                ·
                  refine ⟨457430475533086677836425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9758516811372515793843733 457430475533086677836425)
                  ·
                    rfl

theorem cell21_2004396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 6].length) (baseStart_2004396 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2004396 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2004396 prefixEnd_2004396 := by exact prefixLift 2004396
  have htrace : WordTrace (prefixWord ++ tailWord_2004396) baseStart_2004396 baseEnd_2004396 := by
    simpa [prefixWord, tailWord_2004396, baseEnd_2004396] using wordTrace_append hprefix tailTrace_2004396
  have hstable : (prefixWord ++ tailWord_2004396).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2004396).length < 2 ^ (prefixWord ++ tailWord_2004396).sum := by decide
  have hdescent : baseEnd_2004396 < baseStart_2004396 := by decide
  rcases family_descends (prefixWord ++ tailWord_2004396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2004413 : List Nat := [1, 4, 1, 2, 2, 1, 2, 4, 4]
def baseStart_2004413 : Nat := 118140960795 + 2004413 * 2 ^ 59
def prefixEnd_2004413 : Nat := 4983230072969 + 3 ^ 40 * 2004413 * 2
def baseEnd_2004413 : Nat := 457434355164698426053057

theorem tailTrace_2004413 : CollatzResearch.WordTrace tailWord_2004413 prefixEnd_2004413 457434355164698426053057 := by
  unfold tailWord_2004413
  simp only [CollatzResearch.WordTrace]
  refine ⟨73106948087361502331505893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48737965391574334887670595 73106948087361502331505893)
  ·
    refine ⟨13707552766380281687157355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73106948087361502331505893 13707552766380281687157355)
    ·
      refine ⟨20561329149570422530736033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13707552766380281687157355 20561329149570422530736033)
      ·
        refine ⟨15420996862177816898052025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20561329149570422530736033 15420996862177816898052025)
        ·
          refine ⟨11565747646633362673539019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15420996862177816898052025 11565747646633362673539019)
          ·
            refine ⟨17348621469950044010308529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11565747646633362673539019 17348621469950044010308529)
            ·
              refine ⟨13011466102462533007731397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17348621469950044010308529 13011466102462533007731397)
              ·
                refine ⟨2439649894211724938949637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13011466102462533007731397 2439649894211724938949637)
                ·
                  refine ⟨457434355164698426053057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2439649894211724938949637 457434355164698426053057)
                  ·
                    rfl

theorem cell21_2004413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 4, 4].length) (baseStart_2004413 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2004413 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2004413 prefixEnd_2004413 := by exact prefixLift 2004413
  have htrace : WordTrace (prefixWord ++ tailWord_2004413) baseStart_2004413 baseEnd_2004413 := by
    simpa [prefixWord, tailWord_2004413, baseEnd_2004413] using wordTrace_append hprefix tailTrace_2004413
  have hstable : (prefixWord ++ tailWord_2004413).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2004413).length < 2 ^ (prefixWord ++ tailWord_2004413).sum := by decide
  have hdescent : baseEnd_2004413 < baseStart_2004413 := by decide
  rcases family_descends (prefixWord ++ tailWord_2004413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2004430 : List Nat := [4, 1, 1, 1, 2, 1, 6, 1, 4]
def baseStart_2004430 : Nat := 118140960795 + 2004430 * 2 ^ 59
def prefixEnd_2004430 : Nat := 4983230072969 + 3 ^ 40 * 2004430 * 2
def baseEnd_2004430 : Nat := 457438234796310174269689

theorem tailTrace_2004430 : CollatzResearch.WordTrace tailWord_2004430 prefixEnd_2004430 457438234796310174269689 := by
  unfold tailWord_2004430
  simp only [CollatzResearch.WordTrace]
  refine ⟨9138446016037489279359343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48738378752199942823249829 9138446016037489279359343)
  ·
    refine ⟨13707669024056233919039015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9138446016037489279359343 13707669024056233919039015)
    ·
      refine ⟨20561503536084350878558523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13707669024056233919039015 20561503536084350878558523)
      ·
        refine ⟨30842255304126526317837785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20561503536084350878558523 30842255304126526317837785)
        ·
          refine ⟨23131691478094894738378339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30842255304126526317837785 23131691478094894738378339)
          ·
            refine ⟨34697537217142342107567509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23131691478094894738378339 34697537217142342107567509)
            ·
              refine ⟨1626447057053547286292227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 34697537217142342107567509 1626447057053547286292227)
              ·
                refine ⟨2439670585580320929438341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1626447057053547286292227 2439670585580320929438341)
                ·
                  refine ⟨457438234796310174269689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2439670585580320929438341 457438234796310174269689)
                  ·
                    rfl

theorem cell21_2004430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 6, 1, 4].length) (baseStart_2004430 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2004430 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2004430 prefixEnd_2004430 := by exact prefixLift 2004430
  have htrace : WordTrace (prefixWord ++ tailWord_2004430) baseStart_2004430 baseEnd_2004430 := by
    simpa [prefixWord, tailWord_2004430, baseEnd_2004430] using wordTrace_append hprefix tailTrace_2004430
  have hstable : (prefixWord ++ tailWord_2004430).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2004430).length < 2 ^ (prefixWord ++ tailWord_2004430).sum := by decide
  have hdescent : baseEnd_2004430 < baseStart_2004430 := by decide
  rcases family_descends (prefixWord ++ tailWord_2004430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2004478 : List Nat := [4, 2, 2, 3, 1, 2, 1, 6]
def baseStart_2004478 : Nat := 118140960795 + 2004478 * 2 ^ 59
def prefixEnd_2004478 : Nat := 4983230072969 + 3 ^ 40 * 2004478 * 2
def baseEnd_2004478 : Nat := 152483063016757585823197

theorem tailTrace_2004478 : CollatzResearch.WordTrace tailWord_2004478 prefixEnd_2004478 152483063016757585823197 := by
  unfold tailWord_2004478
  simp only [CollatzResearch.WordTrace]
  refine ⟨9138664854015752304077761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48739545888084012288414725 9138664854015752304077761)
  ·
    refine ⟨6853998640511814228058321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9138664854015752304077761 6853998640511814228058321)
    ·
      refine ⟨5140498980383860671043741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6853998640511814228058321 5140498980383860671043741)
      ·
        refine ⟨1927687117643947751641403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5140498980383860671043741 1927687117643947751641403)
        ·
          refine ⟨2891530676465921627462105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1927687117643947751641403 2891530676465921627462105)
          ·
            refine ⟨2168648007349441220596579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2891530676465921627462105 2168648007349441220596579)
            ·
              refine ⟨3252972011024161830894869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2168648007349441220596579 3252972011024161830894869)
              ·
                refine ⟨152483063016757585823197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3252972011024161830894869 152483063016757585823197)
                ·
                  rfl

theorem cell21_2004478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 1, 6].length) (baseStart_2004478 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2004478 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2004478 prefixEnd_2004478 := by exact prefixLift 2004478
  have htrace : WordTrace (prefixWord ++ tailWord_2004478) baseStart_2004478 baseEnd_2004478 := by
    simpa [prefixWord, tailWord_2004478, baseEnd_2004478] using wordTrace_append hprefix tailTrace_2004478
  have hstable : (prefixWord ++ tailWord_2004478).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2004478).length < 2 ^ (prefixWord ++ tailWord_2004478).sum := by decide
  have hdescent : baseEnd_2004478 < baseStart_2004478 := by decide
  rcases family_descends (prefixWord ++ tailWord_2004478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2004517 : List Nat := [1, 3, 1, 2, 2, 1, 1, 1, 9]
def baseStart_2004517 : Nat := 118140960795 + 2004517 * 2 ^ 59
def prefixEnd_2004517 : Nat := 4983230072969 + 3 ^ 40 * 2004517 * 2
def baseEnd_2004517 : Nat := 457458089381617356319511

theorem tailTrace_2004517 : CollatzResearch.WordTrace tailWord_2004517 prefixEnd_2004517 457458089381617356319511 := by
  unfold tailWord_2004517
  simp only [CollatzResearch.WordTrace]
  refine ⟨73110741278984728093291805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48740494185989818728861203 73110741278984728093291805)
  ·
    refine ⟨27416527979619273034984427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73110741278984728093291805 27416527979619273034984427)
    ·
      refine ⟨41124791969428909552476641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27416527979619273034984427 41124791969428909552476641)
      ·
        refine ⟨30843593977071682164357481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41124791969428909552476641 30843593977071682164357481)
        ·
          refine ⟨23132695482803761623268111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30843593977071682164357481 23132695482803761623268111)
          ·
            refine ⟨34699043224205642434902167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23132695482803761623268111 34699043224205642434902167)
            ·
              refine ⟨52048564836308463652353251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34699043224205642434902167 52048564836308463652353251)
              ·
                refine ⟨78072847254462695478529877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52048564836308463652353251 78072847254462695478529877)
                ·
                  refine ⟨457458089381617356319511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 78072847254462695478529877 457458089381617356319511)
                  ·
                    rfl

theorem cell21_2004517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 9].length) (baseStart_2004517 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2004517 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2004517 prefixEnd_2004517 := by exact prefixLift 2004517
  have htrace : WordTrace (prefixWord ++ tailWord_2004517) baseStart_2004517 baseEnd_2004517 := by
    simpa [prefixWord, tailWord_2004517, baseEnd_2004517] using wordTrace_append hprefix tailTrace_2004517
  have hstable : (prefixWord ++ tailWord_2004517).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2004517).length < 2 ^ (prefixWord ++ tailWord_2004517).sum := by decide
  have hdescent : baseEnd_2004517 < baseStart_2004517 := by decide
  rcases family_descends (prefixWord ++ tailWord_2004517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2004520 : List Nat := [2, 1, 5, 2, 2, 1, 8]
def baseStart_2004520 : Nat := 118140960795 + 2004520 * 2 ^ 59
def prefixEnd_2004520 : Nat := 4983230072969 + 3 ^ 40 * 2004520 * 2
def baseEnd_2004520 : Nat := 50828752669165557529945

theorem tailTrace_2004520 : CollatzResearch.WordTrace tailWord_2004520 prefixEnd_2004520 50828752669165557529945 := by
  unfold tailWord_2004520
  simp only [CollatzResearch.WordTrace]
  refine ⟨36555425348986929802825507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48740567131982573070434009 36555425348986929802825507)
  ·
    refine ⟨54833138023480394704238261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36555425348986929802825507 54833138023480394704238261)
    ·
      refine ⟨5140606689701287003522337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54833138023480394704238261 5140606689701287003522337)
      ·
        refine ⟨3855455017275965252641753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5140606689701287003522337 3855455017275965252641753)
        ·
          refine ⟨2891591262956973939481315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3855455017275965252641753 2891591262956973939481315)
          ·
            refine ⟨4337386894435460909221973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2891591262956973939481315 4337386894435460909221973)
            ·
              refine ⟨50828752669165557529945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4337386894435460909221973 50828752669165557529945)
              ·
                rfl

theorem cell21_2004520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 8].length) (baseStart_2004520 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2004520 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2004520 prefixEnd_2004520 := by exact prefixLift 2004520
  have htrace : WordTrace (prefixWord ++ tailWord_2004520) baseStart_2004520 baseEnd_2004520 := by
    simpa [prefixWord, tailWord_2004520, baseEnd_2004520] using wordTrace_append hprefix tailTrace_2004520
  have hstable : (prefixWord ++ tailWord_2004520).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2004520).length < 2 ^ (prefixWord ++ tailWord_2004520).sum := by decide
  have hdescent : baseEnd_2004520 < baseStart_2004520 := by decide
  rcases family_descends (prefixWord ++ tailWord_2004520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2004579 : List Nat := [1, 1, 1, 5, 1, 5, 7]
def baseStart_2004579 : Nat := 118140960795 + 2004579 * 2 ^ 59
def prefixEnd_2004579 : Nat := 4983230072969 + 3 ^ 40 * 2004579 * 2
def baseEnd_2004579 : Nat := 50830248736257669587339

theorem tailTrace_2004579 : CollatzResearch.WordTrace tailWord_2004579 prefixEnd_2004579 50830248736257669587339 := by
  unfold tailWord_2004579
  simp only [CollatzResearch.WordTrace]
  refine ⟨73113002604760112682048791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48742001736506741788032527 73113002604760112682048791)
  ·
    refine ⟨109669503907140169023073187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73113002604760112682048791 109669503907140169023073187)
    ·
      refine ⟨164504255860710253534609781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109669503907140169023073187 164504255860710253534609781)
      ·
        refine ⟨15422273986941586268869667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 164504255860710253534609781 15422273986941586268869667)
        ·
          refine ⟨23133410980412379403304501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15422273986941586268869667 23133410980412379403304501)
          ·
            refine ⟨2168757279413660569059797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23133410980412379403304501 2168757279413660569059797)
            ·
              refine ⟨50830248736257669587339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2168757279413660569059797 50830248736257669587339)
              ·
                rfl

theorem cell21_2004579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 7].length) (baseStart_2004579 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2004579 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2004579 prefixEnd_2004579 := by exact prefixLift 2004579
  have htrace : WordTrace (prefixWord ++ tailWord_2004579) baseStart_2004579 baseEnd_2004579 := by
    simpa [prefixWord, tailWord_2004579, baseEnd_2004579] using wordTrace_append hprefix tailTrace_2004579
  have hstable : (prefixWord ++ tailWord_2004579).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2004579).length < 2 ^ (prefixWord ++ tailWord_2004579).sum := by decide
  have hdescent : baseEnd_2004579 < baseStart_2004579 := by decide
  rcases family_descends (prefixWord ++ tailWord_2004579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2004641 : List Nat := [1, 2, 3, 3, 2, 1, 1, 4, 4]
def baseStart_2004641 : Nat := 118140960795 + 2004641 * 2 ^ 59
def prefixEnd_2004641 : Nat := 4983230072969 + 3 ^ 40 * 2004641 * 2
def baseEnd_2004641 : Nat := 457486387871020696252591

theorem tailTrace_2004641 : CollatzResearch.WordTrace tailWord_2004641 prefixEnd_2004641 457486387871020696252591 := by
  unfold tailWord_2004641
  simp only [CollatzResearch.WordTrace]
  refine ⟨73115263930535497270805777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48743509287023664847203851 73115263930535497270805777)
  ·
    refine ⟨54836447947901622953104333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73115263930535497270805777 54836447947901622953104333)
    ·
      refine ⟨20563667980463108607414125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54836447947901622953104333 20563667980463108607414125)
      ·
        refine ⟨7711375492673665727780297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20563667980463108607414125 7711375492673665727780297)
        ·
          refine ⟨5783531619505249295835223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7711375492673665727780297 5783531619505249295835223)
          ·
            refine ⟨8675297429257873943752835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5783531619505249295835223 8675297429257873943752835)
            ·
              refine ⟨13012946143886810915629253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8675297429257873943752835 13012946143886810915629253)
              ·
                refine ⟨2439927401978777046680485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13012946143886810915629253 2439927401978777046680485)
                ·
                  refine ⟨457486387871020696252591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2439927401978777046680485 457486387871020696252591)
                  ·
                    rfl

theorem cell21_2004641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 4, 4].length) (baseStart_2004641 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2004641 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2004641 prefixEnd_2004641 := by exact prefixLift 2004641
  have htrace : WordTrace (prefixWord ++ tailWord_2004641) baseStart_2004641 baseEnd_2004641 := by
    simpa [prefixWord, tailWord_2004641, baseEnd_2004641] using wordTrace_append hprefix tailTrace_2004641
  have hstable : (prefixWord ++ tailWord_2004641).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2004641).length < 2 ^ (prefixWord ++ tailWord_2004641).sum := by decide
  have hdescent : baseEnd_2004641 < baseStart_2004641 := by decide
  rcases family_descends (prefixWord ++ tailWord_2004641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2004644 : List Nat := [2, 3, 1, 2, 2, 2, 4, 2, 3]
def baseStart_2004644 : Nat := 118140960795 + 2004644 * 2 ^ 59
def prefixEnd_2004644 : Nat := 4983230072969 + 3 ^ 40 * 2004644 * 2
def baseEnd_2004644 : Nat := 457487072511893357702585

theorem tailTrace_2004644 : CollatzResearch.WordTrace tailWord_2004644 prefixEnd_2004644 457487072511893357702585 := by
  unfold tailWord_2004644
  simp only [CollatzResearch.WordTrace]
  refine ⟨36557686674762314391582493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48743582233016419188776657 36557686674762314391582493)
  ·
    refine ⟨13709132503035867896843435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36557686674762314391582493 13709132503035867896843435)
    ·
      refine ⟨20563698754553801845265153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13709132503035867896843435 20563698754553801845265153)
      ·
        refine ⟨15422774065915351383948865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20563698754553801845265153 15422774065915351383948865)
        ·
          refine ⟨11567080549436513537961649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15422774065915351383948865 11567080549436513537961649)
          ·
            refine ⟨8675310412077385153471237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11567080549436513537961649 8675310412077385153471237)
            ·
              refine ⟨1626620702264509716275857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8675310412077385153471237 1626620702264509716275857)
              ·
                refine ⟨1219965526698382287206893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1626620702264509716275857 1219965526698382287206893)
                ·
                  refine ⟨457487072511893357702585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1219965526698382287206893 457487072511893357702585)
                  ·
                    rfl

theorem cell21_2004644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 4, 2, 3].length) (baseStart_2004644 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2004644 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2004644 prefixEnd_2004644 := by exact prefixLift 2004644
  have htrace : WordTrace (prefixWord ++ tailWord_2004644) baseStart_2004644 baseEnd_2004644 := by
    simpa [prefixWord, tailWord_2004644, baseEnd_2004644] using wordTrace_append hprefix tailTrace_2004644
  have hstable : (prefixWord ++ tailWord_2004644).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2004644).length < 2 ^ (prefixWord ++ tailWord_2004644).sum := by decide
  have hdescent : baseEnd_2004644 < baseStart_2004644 := by decide
  rcases family_descends (prefixWord ++ tailWord_2004644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2004678 : List Nat := [6, 1, 2, 1, 1, 2, 2, 3, 3]
def baseStart_2004678 : Nat := 118140960795 + 2004678 * 2 ^ 59
def prefixEnd_2004678 : Nat := 4983230072969 + 3 ^ 40 * 2004678 * 2
def baseEnd_2004678 : Nat := 457494831775116854135849

theorem tailTrace_2004678 : CollatzResearch.WordTrace tailWord_2004678 prefixEnd_2004678 457494831775116854135849 := by
  unfold tailWord_2004678
  simp only [CollatzResearch.WordTrace]
  refine ⟨2284894169731295393434459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 48744408954267635059935125 2284894169731295393434459)
  ·
    refine ⟨3427341254596943090151689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2284894169731295393434459 3427341254596943090151689)
    ·
      refine ⟨2570505940947707317613767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3427341254596943090151689 2570505940947707317613767)
      ·
        refine ⟨3855758911421560976420651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2570505940947707317613767 3855758911421560976420651)
        ·
          refine ⟨5783638367132341464630977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3855758911421560976420651 5783638367132341464630977)
          ·
            refine ⟨4337728775349256098473233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5783638367132341464630977 4337728775349256098473233)
            ·
              refine ⟨3253296581511942073854925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4337728775349256098473233 3253296581511942073854925)
              ·
                refine ⟨1219986218066978277695597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3253296581511942073854925 1219986218066978277695597)
                ·
                  refine ⟨457494831775116854135849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1219986218066978277695597 457494831775116854135849)
                  ·
                    rfl

theorem cell21_2004678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 2, 3, 3].length) (baseStart_2004678 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2004678 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2004678 prefixEnd_2004678 := by exact prefixLift 2004678
  have htrace : WordTrace (prefixWord ++ tailWord_2004678) baseStart_2004678 baseEnd_2004678 := by
    simpa [prefixWord, tailWord_2004678, baseEnd_2004678] using wordTrace_append hprefix tailTrace_2004678
  have hstable : (prefixWord ++ tailWord_2004678).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2004678).length < 2 ^ (prefixWord ++ tailWord_2004678).sum := by decide
  have hdescent : baseEnd_2004678 < baseStart_2004678 := by decide
  rcases family_descends (prefixWord ++ tailWord_2004678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2004762 : List Nat := [3, 1, 1, 3, 2, 2, 3, 1, 5]
def baseStart_2004762 : Nat := 118140960795 + 2004762 * 2 ^ 59
def prefixEnd_2004762 : Nat := 4983230072969 + 3 ^ 40 * 2004762 * 2
def baseEnd_2004762 : Nat := 457514001719551374735677

theorem tailTrace_2004762 : CollatzResearch.WordTrace tailWord_2004762 prefixEnd_2004762 457514001719551374735677 := by
  unfold tailWord_2004762
  simp only [CollatzResearch.WordTrace]
  refine ⟨18279919290774283733990135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48746451442064756623973693 18279919290774283733990135)
  ·
    refine ⟨27419878936161425600985203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18279919290774283733990135 27419878936161425600985203)
    ·
      refine ⟨41129818404242138401477805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27419878936161425600985203 41129818404242138401477805)
      ·
        refine ⟨15423681901590801900554177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41129818404242138401477805 15423681901590801900554177)
        ·
          refine ⟨11567761426193101425415633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15423681901590801900554177 11567761426193101425415633)
          ·
            refine ⟨8675821069644826069061725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11567761426193101425415633 8675821069644826069061725)
            ·
              refine ⟨3253432901116809775898147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8675821069644826069061725 3253432901116809775898147)
              ·
                refine ⟨4880149351675214663847221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3253432901116809775898147 4880149351675214663847221)
                ·
                  refine ⟨457514001719551374735677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4880149351675214663847221 457514001719551374735677)
                  ·
                    rfl

theorem cell21_2004762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3, 1, 5].length) (baseStart_2004762 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2004762 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2004762 prefixEnd_2004762 := by exact prefixLift 2004762
  have htrace : WordTrace (prefixWord ++ tailWord_2004762) baseStart_2004762 baseEnd_2004762 := by
    simpa [prefixWord, tailWord_2004762, baseEnd_2004762] using wordTrace_append hprefix tailTrace_2004762
  have hstable : (prefixWord ++ tailWord_2004762).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2004762).length < 2 ^ (prefixWord ++ tailWord_2004762).sum := by decide
  have hdescent : baseEnd_2004762 < baseStart_2004762 := by decide
  rcases family_descends (prefixWord ++ tailWord_2004762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2004813 : List Nat := [1, 6, 1, 2, 1, 1, 4, 2, 3]
def baseStart_2004813 : Nat := 118140960795 + 2004813 * 2 ^ 59
def prefixEnd_2004813 : Nat := 4983230072969 + 3 ^ 40 * 2004813 * 2
def baseEnd_2004813 : Nat := 457525640614386619385573

theorem tailTrace_2004813 : CollatzResearch.WordTrace tailWord_2004813 prefixEnd_2004813 457525640614386619385573 := by
  unfold tailWord_2004813
  simp only [CollatzResearch.WordTrace]
  refine ⟨73121537285912370646067093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48747691523941580430711395 73121537285912370646067093)
  ·
    refine ⟨3427572060277142374034395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 73121537285912370646067093 3427572060277142374034395)
    ·
      refine ⟨5141358090415713561051593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3427572060277142374034395 5141358090415713561051593)
      ·
        refine ⟨3856018567811785170788695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5141358090415713561051593 3856018567811785170788695)
        ·
          refine ⟨5784027851717677756183043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3856018567811785170788695 5784027851717677756183043)
          ·
            refine ⟨8676041777576516634274565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5784027851717677756183043 8676041777576516634274565)
            ·
              refine ⟨1626757833295596868926481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8676041777576516634274565 1626757833295596868926481)
              ·
                refine ⟨1220068374971697651694861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1626757833295596868926481 1220068374971697651694861)
                ·
                  refine ⟨457525640614386619385573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1220068374971697651694861 457525640614386619385573)
                  ·
                    rfl

theorem cell21_2004813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 4, 2, 3].length) (baseStart_2004813 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2004813 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2004813 prefixEnd_2004813 := by exact prefixLift 2004813
  have htrace : WordTrace (prefixWord ++ tailWord_2004813) baseStart_2004813 baseEnd_2004813 := by
    simpa [prefixWord, tailWord_2004813, baseEnd_2004813] using wordTrace_append hprefix tailTrace_2004813
  have hstable : (prefixWord ++ tailWord_2004813).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2004813).length < 2 ^ (prefixWord ++ tailWord_2004813).sum := by decide
  have hdescent : baseEnd_2004813 < baseStart_2004813 := by decide
  rcases family_descends (prefixWord ++ tailWord_2004813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2004900 : List Nat := [2, 3, 1, 2, 1, 5, 2, 5]
def baseStart_2004900 : Nat := 118140960795 + 2004900 * 2 ^ 59
def prefixEnd_2004900 : Nat := 4983230072969 + 3 ^ 40 * 2004900 * 2
def baseEnd_2004900 : Nat := 152515165066564600478465

theorem tailTrace_2004900 : CollatzResearch.WordTrace tailWord_2004900 prefixEnd_2004900 152515165066564600478465 := by
  unfold tailWord_2004900
  simp only [CollatzResearch.WordTrace]
  refine ⟨36562355218298592252242077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48749806957731456336322769 36562355218298592252242077)
  ·
    refine ⟨13710883206861972094590779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36562355218298592252242077 13710883206861972094590779)
    ·
      refine ⟨20566324810292958141886169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13710883206861972094590779 20566324810292958141886169)
      ·
        refine ⟨15424743607719718606414627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20566324810292958141886169 15424743607719718606414627)
        ·
          refine ⟨23137115411579577909621941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15424743607719718606414627 23137115411579577909621941)
          ·
            refine ⟨2169104569835585429027057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23137115411579577909621941 2169104569835585429027057)
            ·
              refine ⟨1626828427376689071770293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2169104569835585429027057 1626828427376689071770293)
              ·
                refine ⟨152515165066564600478465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1626828427376689071770293 152515165066564600478465)
                ·
                  rfl

theorem cell21_2004900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 2, 5].length) (baseStart_2004900 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2004900 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2004900 prefixEnd_2004900 := by exact prefixLift 2004900
  have htrace : WordTrace (prefixWord ++ tailWord_2004900) baseStart_2004900 baseEnd_2004900 := by
    simpa [prefixWord, tailWord_2004900, baseEnd_2004900] using wordTrace_append hprefix tailTrace_2004900
  have hstable : (prefixWord ++ tailWord_2004900).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2004900).length < 2 ^ (prefixWord ++ tailWord_2004900).sum := by decide
  have hdescent : baseEnd_2004900 < baseStart_2004900 := by decide
  rcases family_descends (prefixWord ++ tailWord_2004900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2004911 : List Nat := [1, 1, 2, 1, 2, 2, 3, 1, 8]
def baseStart_2004911 : Nat := 118140960795 + 2004911 * 2 ^ 59
def prefixEnd_2004911 : Nat := 4983230072969 + 3 ^ 40 * 2004911 * 2
def baseEnd_2004911 : Nat := 457548005549560226752039

theorem tailTrace_2004911 : CollatzResearch.WordTrace tailWord_2004911 prefixEnd_2004911 457548005549560226752039 := by
  unfold tailWord_2004911
  simp only [CollatzResearch.WordTrace]
  refine ⟨73125111639557333383134587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48750074426371555588756391 73125111639557333383134587)
  ·
    refine ⟨109687667459336000074701881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73125111639557333383134587 109687667459336000074701881)
    ·
      refine ⟨82265750594502000056026411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109687667459336000074701881 82265750594502000056026411)
      ·
        refine ⟨123398625891753000084039617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82265750594502000056026411 123398625891753000084039617)
        ·
          refine ⟨92548969418814750063029713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123398625891753000084039617 92548969418814750063029713)
          ·
            refine ⟨69411727064111062547272285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92548969418814750063029713 69411727064111062547272285)
            ·
              refine ⟨26029397649041648455227107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69411727064111062547272285 26029397649041648455227107)
              ·
                refine ⟨39044096473562472682840661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26029397649041648455227107 39044096473562472682840661)
                ·
                  refine ⟨457548005549560226752039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39044096473562472682840661 457548005549560226752039)
                  ·
                    rfl

theorem cell21_2004911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 8].length) (baseStart_2004911 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2004911 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2004911 prefixEnd_2004911 := by exact prefixLift 2004911
  have htrace : WordTrace (prefixWord ++ tailWord_2004911) baseStart_2004911 baseEnd_2004911 := by
    simpa [prefixWord, tailWord_2004911, baseEnd_2004911] using wordTrace_append hprefix tailTrace_2004911
  have hstable : (prefixWord ++ tailWord_2004911).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2004911).length < 2 ^ (prefixWord ++ tailWord_2004911).sum := by decide
  have hdescent : baseEnd_2004911 < baseStart_2004911 := by decide
  rcases family_descends (prefixWord ++ tailWord_2004911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2004928 : List Nat := [2, 1, 1, 2, 3, 2, 2, 4, 4]
def baseStart_2004928 : Nat := 118140960795 + 2004928 * 2 ^ 59
def prefixEnd_2004928 : Nat := 4983230072969 + 3 ^ 40 * 2004928 * 2
def baseEnd_2004928 : Nat := 457551885181171974968671

theorem tailTrace_2004928 : CollatzResearch.WordTrace tailWord_2004928 prefixEnd_2004928 457551885181171974968671 := by
  unfold tailWord_2004928
  simp only [CollatzResearch.WordTrace]
  refine ⟨36562865840247872643251719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48750487786997163524335625 36562865840247872643251719)
  ·
    refine ⟨54844298760371808964877579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36562865840247872643251719 54844298760371808964877579)
    ·
      refine ⟨82266448140557713447316369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54844298760371808964877579 82266448140557713447316369)
      ·
        refine ⟨61699836105418285085487277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82266448140557713447316369 61699836105418285085487277)
        ·
          refine ⟨23137438539531856907057729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61699836105418285085487277 23137438539531856907057729)
          ·
            refine ⟨17353078904648892680293297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23137438539531856907057729 17353078904648892680293297)
            ·
              refine ⟨13014809178486669510219973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17353078904648892680293297 13014809178486669510219973)
              ·
                refine ⟨2440276720966250533166245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13014809178486669510219973 2440276720966250533166245)
                ·
                  refine ⟨457551885181171974968671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2440276720966250533166245 457551885181171974968671)
                  ·
                    rfl

theorem cell21_2004928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 4, 4].length) (baseStart_2004928 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2004928 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2004928 prefixEnd_2004928 := by exact prefixLift 2004928
  have htrace : WordTrace (prefixWord ++ tailWord_2004928) baseStart_2004928 baseEnd_2004928 := by
    simpa [prefixWord, tailWord_2004928, baseEnd_2004928] using wordTrace_append hprefix tailTrace_2004928
  have hstable : (prefixWord ++ tailWord_2004928).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2004928).length < 2 ^ (prefixWord ++ tailWord_2004928).sum := by decide
  have hdescent : baseEnd_2004928 < baseStart_2004928 := by decide
  rcases family_descends (prefixWord ++ tailWord_2004928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2004982 : List Nat := [5, 1, 1, 1, 5, 1, 2, 2, 3]
def baseStart_2004982 : Nat := 118140960795 + 2004982 * 2 ^ 59
def prefixEnd_2004982 : Nat := 4983230072969 + 3 ^ 40 * 2004982 * 2
def baseEnd_2004982 : Nat := 457564208716879881068561

theorem tailTrace_2004982 : CollatzResearch.WordTrace tailWord_2004982 prefixEnd_2004982 457564208716879881068561 := by
  unfold tailWord_2004982
  simp only [CollatzResearch.WordTrace]
  refine ⟨4570481326393757031810575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48751800814866741672646133 4570481326393757031810575)
  ·
    refine ⟨6855721989590635547715863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4570481326393757031810575 6855721989590635547715863)
    ·
      refine ⟨10283582984385953321573795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6855721989590635547715863 10283582984385953321573795)
      ·
        refine ⟨15425374476578929982360693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10283582984385953321573795 15425374476578929982360693)
        ·
          refine ⟨1446128857179274685846315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15425374476578929982360693 1446128857179274685846315)
          ·
            refine ⟨2169193285768912028769473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1446128857179274685846315 2169193285768912028769473)
            ·
              refine ⟨1626894964326684021577105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2169193285768912028769473 1626894964326684021577105)
              ·
                refine ⟨1220171223245013016182829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1626894964326684021577105 1220171223245013016182829)
                ·
                  refine ⟨457564208716879881068561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1220171223245013016182829 457564208716879881068561)
                  ·
                    rfl

theorem cell21_2004982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 2, 2, 3].length) (baseStart_2004982 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2004982 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2004982 prefixEnd_2004982 := by exact prefixLift 2004982
  have htrace : WordTrace (prefixWord ++ tailWord_2004982) baseStart_2004982 baseEnd_2004982 := by
    simpa [prefixWord, tailWord_2004982, baseEnd_2004982] using wordTrace_append hprefix tailTrace_2004982
  have hstable : (prefixWord ++ tailWord_2004982).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2004982).length < 2 ^ (prefixWord ++ tailWord_2004982).sum := by decide
  have hdescent : baseEnd_2004982 < baseStart_2004982 := by decide
  rcases family_descends (prefixWord ++ tailWord_2004982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2004987 : List Nat := [1, 1, 1, 1, 1, 3, 4, 3, 6]
def baseStart_2004987 : Nat := 118140960795 + 2004987 * 2 ^ 59
def prefixEnd_2004987 : Nat := 4983230072969 + 3 ^ 40 * 2004987 * 2
def baseEnd_2004987 : Nat := 457565349785000983485217

theorem tailTrace_2004987 : CollatzResearch.WordTrace tailWord_2004987 prefixEnd_2004987 457565349785000983485217 := by
  unfold tailWord_2004987
  simp only [CollatzResearch.WordTrace]
  refine ⟨73127883587281998362901215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48751922391521332241934143 73127883587281998362901215)
  ·
    refine ⟨109691825380922997544351823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73127883587281998362901215 109691825380922997544351823)
    ·
      refine ⟨164537738071384496316527735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109691825380922997544351823 164537738071384496316527735)
      ·
        refine ⟨246806607107076744474791603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164537738071384496316527735 246806607107076744474791603)
        ·
          refine ⟨370209910660615116712187405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246806607107076744474791603 370209910660615116712187405)
          ·
            refine ⟨138828716497730668767070277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 370209910660615116712187405 138828716497730668767070277)
            ·
              refine ⟨26030384343324500393825677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 138828716497730668767070277 26030384343324500393825677)
              ·
                refine ⟨9761394128746687647684629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26030384343324500393825677 9761394128746687647684629)
                ·
                  refine ⟨457565349785000983485217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9761394128746687647684629 457565349785000983485217)
                  ·
                    rfl

theorem cell21_2004987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 3, 6].length) (baseStart_2004987 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2004987 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2004987 prefixEnd_2004987 := by exact prefixLift 2004987
  have htrace : WordTrace (prefixWord ++ tailWord_2004987) baseStart_2004987 baseEnd_2004987 := by
    simpa [prefixWord, tailWord_2004987, baseEnd_2004987] using wordTrace_append hprefix tailTrace_2004987
  have hstable : (prefixWord ++ tailWord_2004987).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2004987).length < 2 ^ (prefixWord ++ tailWord_2004987).sum := by decide
  have hdescent : baseEnd_2004987 < baseStart_2004987 := by decide
  rcases family_descends (prefixWord ++ tailWord_2004987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2005004 : List Nat := [2, 2, 1, 2, 3, 1, 1, 5, 4]
def baseStart_2005004 : Nat := 118140960795 + 2005004 * 2 ^ 59
def prefixEnd_2005004 : Nat := 4983230072969 + 3 ^ 40 * 2005004 * 2
def baseEnd_2005004 : Nat := 457569229416612731701849

theorem tailTrace_2005004 : CollatzResearch.WordTrace tailWord_2005004 prefixEnd_2005004 457569229416612731701849 := by
  unfold tailWord_2005004
  simp only [CollatzResearch.WordTrace]
  refine ⟨36564251814110205133135033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48752335752146940177513377 36564251814110205133135033)
  ·
    refine ⟨27423188860582653849851275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36564251814110205133135033 27423188860582653849851275)
    ·
      refine ⟨41134783290873980774776913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27423188860582653849851275 41134783290873980774776913)
      ·
        refine ⟨30851087468155485581082685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41134783290873980774776913 30851087468155485581082685)
        ·
          refine ⟨11569157800558307092906007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30851087468155485581082685 11569157800558307092906007)
          ·
            refine ⟨17353736700837460639359011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11569157800558307092906007 17353736700837460639359011)
            ·
              refine ⟨26030605051256190959038517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17353736700837460639359011 26030605051256190959038517)
              ·
                refine ⟨2440369223555267902409861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26030605051256190959038517 2440369223555267902409861)
                ·
                  refine ⟨457569229416612731701849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2440369223555267902409861 457569229416612731701849)
                  ·
                    rfl

theorem cell21_2005004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 5, 4].length) (baseStart_2005004 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2005004 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2005004 prefixEnd_2005004 := by exact prefixLift 2005004
  have htrace : WordTrace (prefixWord ++ tailWord_2005004) baseStart_2005004 baseEnd_2005004 := by
    simpa [prefixWord, tailWord_2005004, baseEnd_2005004] using wordTrace_append hprefix tailTrace_2005004
  have hstable : (prefixWord ++ tailWord_2005004).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2005004).length < 2 ^ (prefixWord ++ tailWord_2005004).sum := by decide
  have hdescent : baseEnd_2005004 < baseStart_2005004 := by decide
  rcases family_descends (prefixWord ++ tailWord_2005004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2005038 : List Nat := [4, 1, 3, 1, 1, 4, 1, 2, 4]
def baseStart_2005038 : Nat := 118140960795 + 2005038 * 2 ^ 59
def prefixEnd_2005038 : Nat := 4983230072969 + 3 ^ 40 * 2005038 * 2
def baseEnd_2005038 : Nat := 457576988679836228135113

theorem tailTrace_2005038 : CollatzResearch.WordTrace tailWord_2005038 prefixEnd_2005038 457576988679836228135113 := by
  unfold tailWord_2005038
  simp only [CollatzResearch.WordTrace]
  refine ⟨9141217963762154259125971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48753162473398156048671845 9141217963762154259125971)
  ·
    refine ⟨13711826945643231388688957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9141217963762154259125971 13711826945643231388688957)
    ·
      refine ⟨5141935104616211770758359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13711826945643231388688957 5141935104616211770758359)
      ·
        refine ⟨7712902656924317656137539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5141935104616211770758359 7712902656924317656137539)
        ·
          refine ⟨11569353985386476484206309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7712902656924317656137539 11569353985386476484206309)
          ·
            refine ⟨2169253872259964340788683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11569353985386476484206309 2169253872259964340788683)
            ·
              refine ⟨3253880808389946511183025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2169253872259964340788683 3253880808389946511183025)
              ·
                refine ⟨2440410606292459883387269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3253880808389946511183025 2440410606292459883387269)
                ·
                  refine ⟨457576988679836228135113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2440410606292459883387269 457576988679836228135113)
                  ·
                    rfl

theorem cell21_2005038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 1, 2, 4].length) (baseStart_2005038 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2005038 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2005038 prefixEnd_2005038 := by exact prefixLift 2005038
  have htrace : WordTrace (prefixWord ++ tailWord_2005038) baseStart_2005038 baseEnd_2005038 := by
    simpa [prefixWord, tailWord_2005038, baseEnd_2005038] using wordTrace_append hprefix tailTrace_2005038
  have hstable : (prefixWord ++ tailWord_2005038).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2005038).length < 2 ^ (prefixWord ++ tailWord_2005038).sum := by decide
  have hdescent : baseEnd_2005038 < baseStart_2005038 := by decide
  rcases family_descends (prefixWord ++ tailWord_2005038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2005086 : List Nat := [4, 4, 1, 1, 3, 1, 7]
def baseStart_2005086 : Nat := 118140960795 + 2005086 * 2 ^ 59
def prefixEnd_2005086 : Nat := 4983230072969 + 3 ^ 40 * 2005086 * 2
def baseEnd_2005086 : Nat := 50843104770422090148335

theorem tailTrace_2005086 : CollatzResearch.WordTrace tailWord_2005086 prefixEnd_2005086 50843104770422090148335 := by
  unfold tailWord_2005086
  simp only [CollatzResearch.WordTrace]
  refine ⟨9141436801740417283844389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48754329609282225513836741 9141436801740417283844389)
  ·
    refine ⟨1714019400326328240720823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9141436801740417283844389 1714019400326328240720823)
    ·
      refine ⟨2571029100489492361081235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1714019400326328240720823 2571029100489492361081235)
      ·
        refine ⟨3856543650734238541621853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2571029100489492361081235 3856543650734238541621853)
        ·
          refine ⟨1446203869025339453108195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3856543650734238541621853 1446203869025339453108195)
          ·
            refine ⟨2169305803538009179662293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1446203869025339453108195 2169305803538009179662293)
            ·
              refine ⟨50843104770422090148335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2169305803538009179662293 50843104770422090148335)
              ·
                rfl

theorem cell21_2005086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 7].length) (baseStart_2005086 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2005086 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2005086 prefixEnd_2005086 := by exact prefixLift 2005086
  have htrace : WordTrace (prefixWord ++ tailWord_2005086) baseStart_2005086 baseEnd_2005086 := by
    simpa [prefixWord, tailWord_2005086, baseEnd_2005086] using wordTrace_append hprefix tailTrace_2005086
  have hstable : (prefixWord ++ tailWord_2005086).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2005086).length < 2 ^ (prefixWord ++ tailWord_2005086).sum := by decide
  have hdescent : baseEnd_2005086 < baseStart_2005086 := by decide
  rcases family_descends (prefixWord ++ tailWord_2005086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2005252 : List Nat := [2, 3, 2, 2, 3, 2, 1, 3, 3]
def baseStart_2005252 : Nat := 118140960795 + 2005252 * 2 ^ 59
def prefixEnd_2005252 : Nat := 4983230072969 + 3 ^ 40 * 2005252 * 2
def baseEnd_2005252 : Nat := 457625826395419411568009

theorem tailTrace_2005252 : CollatzResearch.WordTrace tailWord_2005252 prefixEnd_2005252 457625826395419411568009 := by
  unfold tailWord_2005252
  simp only [CollatzResearch.WordTrace]
  refine ⟨36568774465660974310649005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48758365954214632414198673 36568774465660974310649005)
  ·
    refine ⟨13713290424622865366493377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36568774465660974310649005 13713290424622865366493377)
    ·
      refine ⟨10284967818467149024870033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13713290424622865366493377 10284967818467149024870033)
      ·
        refine ⟨7713725863850361768652525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10284967818467149024870033 7713725863850361768652525)
        ·
          refine ⟨2892647198943885663244697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7713725863850361768652525 2892647198943885663244697)
          ·
            refine ⟨2169485399207914247433523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2892647198943885663244697 2169485399207914247433523)
            ·
              refine ⟨3254228098811871371150285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2169485399207914247433523 3254228098811871371150285)
              ·
                refine ⟨1220335537054451764181357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3254228098811871371150285 1220335537054451764181357)
                ·
                  refine ⟨457625826395419411568009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1220335537054451764181357 457625826395419411568009)
                  ·
                    rfl

theorem cell21_2005252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 1, 3, 3].length) (baseStart_2005252 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2005252 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2005252 prefixEnd_2005252 := by exact prefixLift 2005252
  have htrace : WordTrace (prefixWord ++ tailWord_2005252) baseStart_2005252 baseEnd_2005252 := by
    simpa [prefixWord, tailWord_2005252, baseEnd_2005252] using wordTrace_append hprefix tailTrace_2005252
  have hstable : (prefixWord ++ tailWord_2005252).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2005252).length < 2 ^ (prefixWord ++ tailWord_2005252).sum := by decide
  have hdescent : baseEnd_2005252 < baseStart_2005252 := by decide
  rcases family_descends (prefixWord ++ tailWord_2005252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2005415 : List Nat := [1, 1, 6, 1, 1, 2, 4, 5]
def baseStart_2005415 : Nat := 118140960795 + 2005415 * 2 ^ 59
def prefixEnd_2005415 : Nat := 4983230072969 + 3 ^ 40 * 2005415 * 2
def baseEnd_2005415 : Nat := 152554341738722450117003

theorem tailTrace_2005415 : CollatzResearch.WordTrace tailWord_2005415 prefixEnd_2005415 152554341738722450117003 := by
  unfold tailWord_2005415
  simp only [CollatzResearch.WordTrace]
  refine ⟨73143494029731427459481699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48762329353154284972987799 73143494029731427459481699)
  ·
    refine ⟨109715241044597141189222549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73143494029731427459481699 109715241044597141189222549)
    ·
      refine ⟨5142901923965490993244807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 109715241044597141189222549 5142901923965490993244807)
      ·
        refine ⟨7714352885948236489867211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5142901923965490993244807 7714352885948236489867211)
        ·
          refine ⟨11571529328922354734800817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7714352885948236489867211 11571529328922354734800817)
          ·
            refine ⟨8678646996691766051100613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11571529328922354734800817 8678646996691766051100613)
            ·
              refine ⟨1627246311879706134581365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8678646996691766051100613 1627246311879706134581365)
              ·
                refine ⟨152554341738722450117003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1627246311879706134581365 152554341738722450117003)
                ·
                  rfl

theorem cell21_2005415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 4, 5].length) (baseStart_2005415 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2005415 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2005415 prefixEnd_2005415 := by exact prefixLift 2005415
  have htrace : WordTrace (prefixWord ++ tailWord_2005415) baseStart_2005415 baseEnd_2005415 := by
    simpa [prefixWord, tailWord_2005415, baseEnd_2005415] using wordTrace_append hprefix tailTrace_2005415
  have hstable : (prefixWord ++ tailWord_2005415).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2005415).length < 2 ^ (prefixWord ++ tailWord_2005415).sum := by decide
  have hdescent : baseEnd_2005415 < baseStart_2005415 := by decide
  rcases family_descends (prefixWord ++ tailWord_2005415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2005421 : List Nat := [1, 5, 2, 2, 3, 1, 1, 3, 3]
def baseStart_2005421 : Nat := 118140960795 + 2005421 * 2 ^ 59
def prefixEnd_2005421 : Nat := 4983230072969 + 3 ^ 40 * 2005421 * 2
def baseEnd_2005421 : Nat := 457664394497912673250997

theorem tailTrace_2005421 : CollatzResearch.WordTrace tailWord_2005421 prefixEnd_2005421 457664394497912673250997 := by
  unfold tailWord_2005421
  simp only [CollatzResearch.WordTrace]
  refine ⟨73143712867709690484200117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48762475245139793656133411 73143712867709690484200117)
  ·
    refine ⟨6857223081347783482893761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 73143712867709690484200117 6857223081347783482893761)
    ·
      refine ⟨5142917311010837612170321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6857223081347783482893761 5142917311010837612170321)
      ·
        refine ⟨3857187983258128209127741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5142917311010837612170321 3857187983258128209127741)
        ·
          refine ⟨1446445493721798078422903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3857187983258128209127741 1446445493721798078422903)
          ·
            refine ⟨2169668240582697117634355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1446445493721798078422903 2169668240582697117634355)
            ·
              refine ⟨3254502360874045676451533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2169668240582697117634355 3254502360874045676451533)
              ·
                refine ⟨1220438385327767128669325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3254502360874045676451533 1220438385327767128669325)
                ·
                  refine ⟨457664394497912673250997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1220438385327767128669325 457664394497912673250997)
                  ·
                    rfl

theorem cell21_2005421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 1, 3, 3].length) (baseStart_2005421 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2005421 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2005421 prefixEnd_2005421 := by exact prefixLift 2005421
  have htrace : WordTrace (prefixWord ++ tailWord_2005421) baseStart_2005421 baseEnd_2005421 := by
    simpa [prefixWord, tailWord_2005421, baseEnd_2005421] using wordTrace_append hprefix tailTrace_2005421
  have hstable : (prefixWord ++ tailWord_2005421).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2005421).length < 2 ^ (prefixWord ++ tailWord_2005421).sum := by decide
  have hdescent : baseEnd_2005421 < baseStart_2005421 := by decide
  rcases family_descends (prefixWord ++ tailWord_2005421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2005443 : List Nat := [1, 1, 1, 3, 1, 1, 3, 6, 4]
def baseStart_2005443 : Nat := 118140960795 + 2005443 * 2 ^ 59
def prefixEnd_2005443 : Nat := 4983230072969 + 3 ^ 40 * 2005443 * 2
def baseEnd_2005443 : Nat := 457669415197645523884285

theorem tailTrace_2005443 : CollatzResearch.WordTrace tailWord_2005443 prefixEnd_2005443 457669415197645523884285 := by
  unfold tailWord_2005443
  simp only [CollatzResearch.WordTrace]
  refine ⟨73144515273629988241500983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48763010182419992161000655 73144515273629988241500983)
  ·
    refine ⟨109716772910444982362251475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73144515273629988241500983 109716772910444982362251475)
    ·
      refine ⟨164575159365667473543377213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109716772910444982362251475 164575159365667473543377213)
      ·
        refine ⟨61715684762125302578766455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164575159365667473543377213 61715684762125302578766455)
        ·
          refine ⟨92573527143187953868149683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61715684762125302578766455 92573527143187953868149683)
          ·
            refine ⟨138860290714781930802224525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92573527143187953868149683 138860290714781930802224525)
            ·
              refine ⟨52072609018043224050834197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138860290714781930802224525 52072609018043224050834197)
              ·
                refine ⟨2440903547720776127382853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 52072609018043224050834197 2440903547720776127382853)
                ·
                  refine ⟨457669415197645523884285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2440903547720776127382853 457669415197645523884285)
                  ·
                    rfl

theorem cell21_2005443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 6, 4].length) (baseStart_2005443 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2005443 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2005443 prefixEnd_2005443 := by exact prefixLift 2005443
  have htrace : WordTrace (prefixWord ++ tailWord_2005443) baseStart_2005443 baseEnd_2005443 := by
    simpa [prefixWord, tailWord_2005443, baseEnd_2005443] using wordTrace_append hprefix tailTrace_2005443
  have hstable : (prefixWord ++ tailWord_2005443).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2005443).length < 2 ^ (prefixWord ++ tailWord_2005443).sum := by decide
  have hdescent : baseEnd_2005443 < baseStart_2005443 := by decide
  rcases family_descends (prefixWord ++ tailWord_2005443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2005657 : List Nat := [1, 2, 1, 2, 1, 2, 4, 5, 3]
def baseStart_2005657 : Nat := 118140960795 + 2005657 * 2 ^ 59
def prefixEnd_2005657 : Nat := 4983230072969 + 3 ^ 40 * 2005657 * 2
def baseEnd_2005657 : Nat := 457718252913228707317181

theorem tailTrace_2005657 : CollatzResearch.WordTrace tailWord_2005657 prefixEnd_2005657 457718252913228707317181 := by
  unfold tailWord_2005657
  simp only [CollatzResearch.WordTrace]
  refine ⟨73152320494854702789791225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48768213663236468526527483 73152320494854702789791225)
  ·
    refine ⟨54864240371141027092343419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73152320494854702789791225 54864240371141027092343419)
    ·
      refine ⟨82296360556711540638515129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54864240371141027092343419 82296360556711540638515129)
      ·
        refine ⟨61722270417533655478886347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82296360556711540638515129 61722270417533655478886347)
        ·
          refine ⟨92583405626300483218329521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61722270417533655478886347 92583405626300483218329521)
          ·
            refine ⟨69437554219725362413747141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92583405626300483218329521 69437554219725362413747141)
            ·
              refine ⟨13019541416198505452577589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69437554219725362413747141 13019541416198505452577589)
              ·
                refine ⟨1220582007768609886179149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13019541416198505452577589 1220582007768609886179149)
                ·
                  refine ⟨457718252913228707317181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1220582007768609886179149 457718252913228707317181)
                  ·
                    rfl

theorem cell21_2005657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 5, 3].length) (baseStart_2005657 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2005657 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2005657 prefixEnd_2005657 := by exact prefixLift 2005657
  have htrace : WordTrace (prefixWord ++ tailWord_2005657) baseStart_2005657 baseEnd_2005657 := by
    simpa [prefixWord, tailWord_2005657, baseEnd_2005657] using wordTrace_append hprefix tailTrace_2005657
  have hstable : (prefixWord ++ tailWord_2005657).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2005657).length < 2 ^ (prefixWord ++ tailWord_2005657).sum := by decide
  have hdescent : baseEnd_2005657 < baseStart_2005657 := by decide
  rcases family_descends (prefixWord ++ tailWord_2005657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2005733 : List Nat := [1, 3, 1, 4, 1, 3, 2, 1, 5]
def baseStart_2005733 : Nat := 118140960795 + 2005733 * 2 ^ 59
def prefixEnd_2005733 : Nat := 4983230072969 + 3 ^ 40 * 2005733 * 2
def baseEnd_2005733 : Nat := 457735597148669464050359

theorem tailTrace_2005733 : CollatzResearch.WordTrace tailWord_2005733 prefixEnd_2005733 457735597148669464050359 := by
  unfold tailWord_2005733
  simp only [CollatzResearch.WordTrace]
  refine ⟨73155092442579367769557853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48770061628386245179705235 73155092442579367769557853)
  ·
    refine ⟨27433159665967262913584195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73155092442579367769557853 27433159665967262913584195)
    ·
      refine ⟨41149739498950894370376293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27433159665967262913584195 41149739498950894370376293)
      ·
        refine ⟨7715576156053292694445555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41149739498950894370376293 7715576156053292694445555)
        ·
          refine ⟨11573364234079939041668333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7715576156053292694445555 11573364234079939041668333)
          ·
            refine ⟨4340011587779977140625625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11573364234079939041668333 4340011587779977140625625)
            ·
              refine ⟨3255008690834982855469219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4340011587779977140625625 3255008690834982855469219)
              ·
                refine ⟨4882513036252474283203829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3255008690834982855469219 4882513036252474283203829)
                ·
                  refine ⟨457735597148669464050359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4882513036252474283203829 457735597148669464050359)
                  ·
                    rfl

theorem cell21_2005733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 2, 1, 5].length) (baseStart_2005733 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2005733 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2005733 prefixEnd_2005733 := by exact prefixLift 2005733
  have htrace : WordTrace (prefixWord ++ tailWord_2005733) baseStart_2005733 baseEnd_2005733 := by
    simpa [prefixWord, tailWord_2005733, baseEnd_2005733] using wordTrace_append hprefix tailTrace_2005733
  have hstable : (prefixWord ++ tailWord_2005733).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2005733).length < 2 ^ (prefixWord ++ tailWord_2005733).sum := by decide
  have hdescent : baseEnd_2005733 < baseStart_2005733 := by decide
  rcases family_descends (prefixWord ++ tailWord_2005733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2005767 : List Nat := [1, 1, 4, 4, 1, 3, 1, 3, 3]
def baseStart_2005767 : Nat := 118140960795 + 2005767 * 2 ^ 59
def prefixEnd_2005767 : Nat := 4983230072969 + 3 ^ 40 * 2005767 * 2
def baseEnd_2005767 : Nat := 457743356411892960483623

theorem tailTrace_2005767 : CollatzResearch.WordTrace tailWord_2005767 prefixEnd_2005767 457743356411892960483623 := by
  unfold tailWord_2005767
  simp only [CollatzResearch.WordTrace]
  refine ⟨73156332524456191576295555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48770888349637461050863703 73156332524456191576295555)
  ·
    refine ⟨109734498786684287364443333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73156332524456191576295555 109734498786684287364443333)
    ·
      refine ⟨20575218522503303880833125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109734498786684287364443333 20575218522503303880833125)
      ·
        refine ⟨3857853472969369477656211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20575218522503303880833125 3857853472969369477656211)
        ·
          refine ⟨5786780209454054216484317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3857853472969369477656211 5786780209454054216484317)
          ·
            refine ⟨2170042578545270331181619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5786780209454054216484317 2170042578545270331181619)
            ·
              refine ⟨3255063867817905496772429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2170042578545270331181619 3255063867817905496772429)
              ·
                refine ⟨1220648950431714561289661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3255063867817905496772429 1220648950431714561289661)
                ·
                  refine ⟨457743356411892960483623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1220648950431714561289661 457743356411892960483623)
                  ·
                    rfl

theorem cell21_2005767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 1, 3, 3].length) (baseStart_2005767 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2005767 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2005767 prefixEnd_2005767 := by exact prefixLift 2005767
  have htrace : WordTrace (prefixWord ++ tailWord_2005767) baseStart_2005767 baseEnd_2005767 := by
    simpa [prefixWord, tailWord_2005767, baseEnd_2005767] using wordTrace_append hprefix tailTrace_2005767
  have hstable : (prefixWord ++ tailWord_2005767).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2005767).length < 2 ^ (prefixWord ++ tailWord_2005767).sum := by decide
  have hdescent : baseEnd_2005767 < baseStart_2005767 := by decide
  rcases family_descends (prefixWord ++ tailWord_2005767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2005868 : List Nat := [2, 2, 1, 1, 4, 1, 3, 2, 5]
def baseStart_2005868 : Nat := 118140960795 + 2005868 * 2 ^ 59
def prefixEnd_2005868 : Nat := 4983230072969 + 3 ^ 40 * 2005868 * 2
def baseEnd_2005868 : Nat := 457766405987939229300083

theorem tailTrace_2005868 : CollatzResearch.WordTrace tailWord_2005868 prefixEnd_2005868 457766405987939229300083 := by
  unfold tailWord_2005868
  simp only [CollatzResearch.WordTrace]
  refine ⟨36580008148545142912861129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48773344198060190550481505 36580008148545142912861129)
  ·
    refine ⟨27435006111408857184645847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36580008148545142912861129 27435006111408857184645847)
    ·
      refine ⟨41152509167113285776968771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27435006111408857184645847 41152509167113285776968771)
      ·
        refine ⟨61728763750669928665453157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41152509167113285776968771 61728763750669928665453157)
        ·
          refine ⟨11574143203250611624772467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61728763750669928665453157 11574143203250611624772467)
          ·
            refine ⟨17361214804875917437158701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11574143203250611624772467 17361214804875917437158701)
            ·
              refine ⟨6510455551828469038934513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17361214804875917437158701 6510455551828469038934513)
              ·
                refine ⟨4882841663871351779200885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6510455551828469038934513 4882841663871351779200885)
                ·
                  refine ⟨457766405987939229300083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4882841663871351779200885 457766405987939229300083)
                  ·
                    rfl

theorem cell21_2005868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 5].length) (baseStart_2005868 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2005868 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2005868 prefixEnd_2005868 := by exact prefixLift 2005868
  have htrace : WordTrace (prefixWord ++ tailWord_2005868) baseStart_2005868 baseEnd_2005868 := by
    simpa [prefixWord, tailWord_2005868, baseEnd_2005868] using wordTrace_append hprefix tailTrace_2005868
  have hstable : (prefixWord ++ tailWord_2005868).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2005868).length < 2 ^ (prefixWord ++ tailWord_2005868).sum := by decide
  have hdescent : baseEnd_2005868 < baseStart_2005868 := by decide
  rcases family_descends (prefixWord ++ tailWord_2005868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2005882 : List Nat := [3, 1, 1, 1, 1, 1, 3, 4, 6]
def baseStart_2005882 : Nat := 118140960795 + 2005882 * 2 ^ 59
def prefixEnd_2005882 : Nat := 4983230072969 + 3 ^ 40 * 2005882 * 2
def baseEnd_2005882 : Nat := 457769600978678316066721

theorem tailTrace_2005882 : CollatzResearch.WordTrace tailWord_2005882 prefixEnd_2005882 457769600978678316066721 := by
  unfold tailWord_2005882
  simp only [CollatzResearch.WordTrace]
  refine ⟨18290131729759891554182975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48773684612693044144487933 18290131729759891554182975)
  ·
    refine ⟨27435197594639837331274463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18290131729759891554182975 27435197594639837331274463)
    ·
      refine ⟨41152796391959755996911695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27435197594639837331274463 41152796391959755996911695)
      ·
        refine ⟨61729194587939633995367543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41152796391959755996911695 61729194587939633995367543)
        ·
          refine ⟨92593791881909450993051315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61729194587939633995367543 92593791881909450993051315)
          ·
            refine ⟨138890687822864176489576973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92593791881909450993051315 138890687822864176489576973)
            ·
              refine ⟨52084007933574066183591365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138890687822864176489576973 52084007933574066183591365)
              ·
                refine ⟨9765751487545137409423381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52084007933574066183591365 9765751487545137409423381)
                ·
                  refine ⟨457769600978678316066721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9765751487545137409423381 457769600978678316066721)
                  ·
                    rfl

theorem cell21_2005882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 4, 6].length) (baseStart_2005882 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2005882 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2005882 prefixEnd_2005882 := by exact prefixLift 2005882
  have htrace : WordTrace (prefixWord ++ tailWord_2005882) baseStart_2005882 baseEnd_2005882 := by
    simpa [prefixWord, tailWord_2005882, baseEnd_2005882] using wordTrace_append hprefix tailTrace_2005882
  have hstable : (prefixWord ++ tailWord_2005882).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2005882).length < 2 ^ (prefixWord ++ tailWord_2005882).sum := by decide
  have hdescent : baseEnd_2005882 < baseStart_2005882 := by decide
  rcases family_descends (prefixWord ++ tailWord_2005882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2005885 : List Nat := [1, 4, 1, 1, 2, 1, 3, 5, 3]
def baseStart_2005885 : Nat := 118140960795 + 2005885 * 2 ^ 59
def prefixEnd_2005885 : Nat := 4983230072969 + 3 ^ 40 * 2005885 * 2
def baseEnd_2005885 : Nat := 457770285619550977516715

theorem tailTrace_2005885 : CollatzResearch.WordTrace tailWord_2005885 prefixEnd_2005885 457770285619550977516715 := by
  unfold tailWord_2005885
  simp only [CollatzResearch.WordTrace]
  refine ⟨73160636338028697729091109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48773757558685798486060739 73160636338028697729091109)
  ·
    refine ⟨13717619313380380824204583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73160636338028697729091109 13717619313380380824204583)
    ·
      refine ⟨20576428970070571236306875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13717619313380380824204583 20576428970070571236306875)
      ·
        refine ⟨30864643455105856854460313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20576428970070571236306875 30864643455105856854460313)
        ·
          refine ⟨23148482591329392640845235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30864643455105856854460313 23148482591329392640845235)
          ·
            refine ⟨34722723886994088961267853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23148482591329392640845235 34722723886994088961267853)
            ·
              refine ⟨13021021457622783360475445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34722723886994088961267853 13021021457622783360475445)
              ·
                refine ⟨1220720761652135940044573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13021021457622783360475445 1220720761652135940044573)
                ·
                  refine ⟨457770285619550977516715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1220720761652135940044573 457770285619550977516715)
                  ·
                    rfl

theorem cell21_2005885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 5, 3].length) (baseStart_2005885 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2005885 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2005885 prefixEnd_2005885 := by exact prefixLift 2005885
  have htrace : WordTrace (prefixWord ++ tailWord_2005885) baseStart_2005885 baseEnd_2005885 := by
    simpa [prefixWord, tailWord_2005885, baseEnd_2005885] using wordTrace_append hprefix tailTrace_2005885
  have hstable : (prefixWord ++ tailWord_2005885).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2005885).length < 2 ^ (prefixWord ++ tailWord_2005885).sum := by decide
  have hdescent : baseEnd_2005885 < baseStart_2005885 := by decide
  rcases family_descends (prefixWord ++ tailWord_2005885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2005899 : List Nat := [1, 1, 1, 1, 4, 2, 5, 2, 4]
def baseStart_2005899 : Nat := 118140960795 + 2005899 * 2 ^ 59
def prefixEnd_2005899 : Nat := 4983230072969 + 3 ^ 40 * 2005899 * 2
def baseEnd_2005899 : Nat := 457773480610290064283353

theorem tailTrace_2005899 : CollatzResearch.WordTrace tailWord_2005899 prefixEnd_2005899 457773480610290064283353 := by
  unfold tailWord_2005899
  simp only [CollatzResearch.WordTrace]
  refine ⟨73161146959977978120100751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48774097973318652080067167 73161146959977978120100751)
  ·
    refine ⟨109741720439966967180151127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73161146959977978120100751 109741720439966967180151127)
    ·
      refine ⟨164612580659950450770226691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109741720439966967180151127 164612580659950450770226691)
      ·
        refine ⟨246918870989925676155340037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164612580659950450770226691 246918870989925676155340037)
        ·
          refine ⟨46297288310611064279126257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 246918870989925676155340037 46297288310611064279126257)
          ·
            refine ⟨34722966232958298209344693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46297288310611064279126257 34722966232958298209344693)
            ·
              refine ⟨3255278084339840457126065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34722966232958298209344693 3255278084339840457126065)
              ·
                refine ⟨2441458563254880342844549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3255278084339840457126065 2441458563254880342844549)
                ·
                  refine ⟨457773480610290064283353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2441458563254880342844549 457773480610290064283353)
                  ·
                    rfl

theorem cell21_2005899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 5, 2, 4].length) (baseStart_2005899 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2005899 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2005899 prefixEnd_2005899 := by exact prefixLift 2005899
  have htrace : WordTrace (prefixWord ++ tailWord_2005899) baseStart_2005899 baseEnd_2005899 := by
    simpa [prefixWord, tailWord_2005899, baseEnd_2005899] using wordTrace_append hprefix tailTrace_2005899
  have hstable : (prefixWord ++ tailWord_2005899).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2005899).length < 2 ^ (prefixWord ++ tailWord_2005899).sum := by decide
  have hdescent : baseEnd_2005899 < baseStart_2005899 := by decide
  rcases family_descends (prefixWord ++ tailWord_2005899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006068 : List Nat := [2, 5, 1, 2, 1, 2, 1, 1, 6]
def baseStart_2006068 : Nat := 118140960795 + 2006068 * 2 ^ 59
def prefixEnd_2006068 : Nat := 4983230072969 + 3 ^ 40 * 2006068 * 2
def baseEnd_2006068 : Nat := 457812048712783325966341

theorem tailTrace_2006068 : CollatzResearch.WordTrace tailWord_2006068 prefixEnd_2006068 457812048712783325966341 := by
  unfold tailWord_2006068
  simp only [CollatzResearch.WordTrace]
  refine ⟨36583655448182859991501429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48778207264243813322001905 36583655448182859991501429)
  ·
    refine ⟨3429717698267143124203259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36583655448182859991501429 3429717698267143124203259)
    ·
      refine ⟨5144576547400714686304889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3429717698267143124203259 5144576547400714686304889)
      ·
        refine ⟨3858432410550536014728667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5144576547400714686304889 3858432410550536014728667)
        ·
          refine ⟨5787648615825804022093001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3858432410550536014728667 5787648615825804022093001)
          ·
            refine ⟨4340736461869353016569751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5787648615825804022093001 4340736461869353016569751)
            ·
              refine ⟨6511104692804029524854627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4340736461869353016569751 6511104692804029524854627)
              ·
                refine ⟨9766657039206044287281941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6511104692804029524854627 9766657039206044287281941)
                ·
                  refine ⟨457812048712783325966341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9766657039206044287281941 457812048712783325966341)
                  ·
                    rfl

theorem cell21_2006068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_2006068 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2006068 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2006068 prefixEnd_2006068 := by exact prefixLift 2006068
  have htrace : WordTrace (prefixWord ++ tailWord_2006068) baseStart_2006068 baseEnd_2006068 := by
    simpa [prefixWord, tailWord_2006068, baseEnd_2006068] using wordTrace_append hprefix tailTrace_2006068
  have hstable : (prefixWord ++ tailWord_2006068).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006068).length < 2 ^ (prefixWord ++ tailWord_2006068).sum := by decide
  have hdescent : baseEnd_2006068 < baseStart_2006068 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006113 : List Nat := [1, 2, 3, 1, 1, 2, 5, 3, 3]
def baseStart_2006113 : Nat := 118140960795 + 2006113 * 2 ^ 59
def prefixEnd_2006113 : Nat := 4983230072969 + 3 ^ 40 * 2006113 * 2
def baseEnd_2006113 : Nat := 457822318325873247716249

theorem tailTrace_2006113 : CollatzResearch.WordTrace tailWord_2006113 prefixEnd_2006113 457822318325873247716249 := by
  unfold tailWord_2006113
  simp only [CollatzResearch.WordTrace]
  refine ⟨73168952181202692668390993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48779301454135128445593995 73168952181202692668390993)
  ·
    refine ⟨54876714135902019501293245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73168952181202692668390993 54876714135902019501293245)
    ·
      refine ⟨20578767800963257312984967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54876714135902019501293245 20578767800963257312984967)
      ·
        refine ⟨30868151701444885969477451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20578767800963257312984967 30868151701444885969477451)
        ·
          refine ⟨46302227552167328954216177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30868151701444885969477451 46302227552167328954216177)
          ·
            refine ⟨34726670664125496715662133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46302227552167328954216177 34726670664125496715662133)
            ·
              refine ⟨3255625374761765317093325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34726670664125496715662133 3255625374761765317093325)
              ·
                refine ⟨1220859515535661993909997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3255625374761765317093325 1220859515535661993909997)
                ·
                  refine ⟨457822318325873247716249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1220859515535661993909997 457822318325873247716249)
                  ·
                    rfl

theorem cell21_2006113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 5, 3, 3].length) (baseStart_2006113 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2006113 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2006113 prefixEnd_2006113 := by exact prefixLift 2006113
  have htrace : WordTrace (prefixWord ++ tailWord_2006113) baseStart_2006113 baseEnd_2006113 := by
    simpa [prefixWord, tailWord_2006113, baseEnd_2006113] using wordTrace_append hprefix tailTrace_2006113
  have hstable : (prefixWord ++ tailWord_2006113).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006113).length < 2 ^ (prefixWord ++ tailWord_2006113).sum := by decide
  have hdescent : baseEnd_2006113 < baseStart_2006113 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006130 : List Nat := [3, 2, 1, 2, 2, 1, 5, 2, 3]
def baseStart_2006130 : Nat := 118140960795 + 2006130 * 2 ^ 59
def prefixEnd_2006130 : Nat := 4983230072969 + 3 ^ 40 * 2006130 * 2
def baseEnd_2006130 : Nat := 457826197957484995932881

theorem tailTrace_2006130 : CollatzResearch.WordTrace tailWord_2006130 prefixEnd_2006130 457826197957484995932881 := by
  unfold tailWord_2006130
  simp only [CollatzResearch.WordTrace]
  refine ⟨18292393055535276142939961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48779714814760736381173229 18292393055535276142939961)
  ·
    refine ⟨13719294791651457107204971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18292393055535276142939961 13719294791651457107204971)
    ·
      refine ⟨20578942187477185660807457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13719294791651457107204971 20578942187477185660807457)
      ·
        refine ⟨15434206640607889245605593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20578942187477185660807457 15434206640607889245605593)
        ·
          refine ⟨11575654980455916934204195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15434206640607889245605593 11575654980455916934204195)
          ·
            refine ⟨17363482470683875401306293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11575654980455916934204195 17363482470683875401306293)
            ·
              refine ⟨1627826481626613318872465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17363482470683875401306293 1627826481626613318872465)
              ·
                refine ⟨1220869861219959989154349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1627826481626613318872465 1220869861219959989154349)
                ·
                  refine ⟨457826197957484995932881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1220869861219959989154349 457826197957484995932881)
                  ·
                    rfl

theorem cell21_2006130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 5, 2, 3].length) (baseStart_2006130 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2006130 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2006130 prefixEnd_2006130 := by exact prefixLift 2006130
  have htrace : WordTrace (prefixWord ++ tailWord_2006130) baseStart_2006130 baseEnd_2006130 := by
    simpa [prefixWord, tailWord_2006130, baseEnd_2006130] using wordTrace_append hprefix tailTrace_2006130
  have hstable : (prefixWord ++ tailWord_2006130).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006130).length < 2 ^ (prefixWord ++ tailWord_2006130).sum := by decide
  have hdescent : baseEnd_2006130 < baseStart_2006130 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006141 : List Nat := [1, 4, 1, 1, 3, 1, 4, 6]
def baseStart_2006141 : Nat := 118140960795 + 2006141 * 2 ^ 59
def prefixEnd_2006141 : Nat := 4983230072969 + 3 ^ 40 * 2006141 * 2
def baseEnd_2006141 : Nat := 152609569435783807083175

theorem tailTrace_2006141 : CollatzResearch.WordTrace tailWord_2006141 prefixEnd_2006141 152609569435783807083175 := by
  unfold tailWord_2006141
  simp only [CollatzResearch.WordTrace]
  refine ⟨73169973425101253450410277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48779982283400835633606851 73169973425101253450410277)
  ·
    refine ⟨13719370017206485021951927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73169973425101253450410277 13719370017206485021951927)
    ·
      refine ⟨20579055025809727532927891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13719370017206485021951927 20579055025809727532927891)
      ·
        refine ⟨30868582538714591299391837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20579055025809727532927891 30868582538714591299391837)
        ·
          refine ⟨11575718452017971737271939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30868582538714591299391837 11575718452017971737271939)
          ·
            refine ⟨17363577678026957605907909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11575718452017971737271939 17363577678026957605907909)
            ·
              refine ⟨3255670814630054551107733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17363577678026957605907909 3255670814630054551107733)
              ·
                refine ⟨152609569435783807083175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3255670814630054551107733 152609569435783807083175)
                ·
                  rfl

theorem cell21_2006141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 4, 6].length) (baseStart_2006141 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2006141 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2006141 prefixEnd_2006141 := by exact prefixLift 2006141
  have htrace : WordTrace (prefixWord ++ tailWord_2006141) baseStart_2006141 baseEnd_2006141 := by
    simpa [prefixWord, tailWord_2006141, baseEnd_2006141] using wordTrace_append hprefix tailTrace_2006141
  have hstable : (prefixWord ++ tailWord_2006141).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006141).length < 2 ^ (prefixWord ++ tailWord_2006141).sum := by decide
  have hdescent : baseEnd_2006141 < baseStart_2006141 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006155 : List Nat := [1, 1, 1, 1, 4, 1, 1, 6, 5]
def baseStart_2006155 : Nat := 118140960795 + 2006155 * 2 ^ 59
def prefixEnd_2006155 : Nat := 4983230072969 + 3 ^ 40 * 2006155 * 2
def baseEnd_2006155 : Nat := 457831903298090508016163

theorem tailTrace_2006155 : CollatzResearch.WordTrace tailWord_2006155 prefixEnd_2006155 457831903298090508016163 := by
  unfold tailWord_2006155
  simp only [CollatzResearch.WordTrace]
  refine ⟨73170484047050533841419919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48780322698033689227613279 73170484047050533841419919)
  ·
    refine ⟨109755726070575800762129879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73170484047050533841419919 109755726070575800762129879)
    ·
      refine ⟨164633589105863701143194819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109755726070575800762129879 164633589105863701143194819)
      ·
        refine ⟨246950383658795551714792229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164633589105863701143194819 246950383658795551714792229)
        ·
          refine ⟨46303196936024165946523543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 246950383658795551714792229 46303196936024165946523543)
          ·
            refine ⟨69454795404036248919785315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46303196936024165946523543 69454795404036248919785315)
            ·
              refine ⟨104182193106054373379677973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69454795404036248919785315 104182193106054373379677973)
              ·
                refine ⟨4883540301846298752172405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 104182193106054373379677973 4883540301846298752172405)
                ·
                  refine ⟨457831903298090508016163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4883540301846298752172405 457831903298090508016163)
                  ·
                    rfl

theorem cell21_2006155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 6, 5].length) (baseStart_2006155 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2006155 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2006155 prefixEnd_2006155 := by exact prefixLift 2006155
  have htrace : WordTrace (prefixWord ++ tailWord_2006155) baseStart_2006155 baseEnd_2006155 := by
    simpa [prefixWord, tailWord_2006155, baseEnd_2006155] using wordTrace_append hprefix tailTrace_2006155
  have hstable : (prefixWord ++ tailWord_2006155).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006155).length < 2 ^ (prefixWord ++ tailWord_2006155).sum := by decide
  have hdescent : baseEnd_2006155 < baseStart_2006155 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006200 : List Nat := [2, 1, 2, 1, 2, 1, 2, 10]
def baseStart_2006200 : Nat := 118140960795 + 2006200 * 2 ^ 59
def prefixEnd_2006200 : Nat := 4983230072969 + 3 ^ 40 * 2006200 * 2
def baseEnd_2006200 : Nat := 152614057637060143255357

theorem tailTrace_2006200 : CollatzResearch.WordTrace tailWord_2006200 prefixEnd_2006200 152614057637060143255357 := by
  unfold tailWord_2006200
  simp only [CollatzResearch.WordTrace]
  refine ⟨36586062665943753263404027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48781416887925004351205369 36586062665943753263404027)
  ·
    refine ⟨54879093998915629895106041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36586062665943753263404027 54879093998915629895106041)
    ·
      refine ⟨41159320499186722421329531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54879093998915629895106041 41159320499186722421329531)
      ·
        refine ⟨61738980748780083631994297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41159320499186722421329531 61738980748780083631994297)
        ·
          refine ⟨46304235561585062723995723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61738980748780083631994297 46304235561585062723995723)
          ·
            refine ⟨69456353342377594085993585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46304235561585062723995723 69456353342377594085993585)
            ·
              refine ⟨52092265006783195564495189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69456353342377594085993585 52092265006783195564495189)
              ·
                refine ⟨152614057637060143255357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 52092265006783195564495189 152614057637060143255357)
                ·
                  rfl

theorem cell21_2006200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 10].length) (baseStart_2006200 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2006200 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2006200 prefixEnd_2006200 := by exact prefixLift 2006200
  have htrace : WordTrace (prefixWord ++ tailWord_2006200) baseStart_2006200 baseEnd_2006200 := by
    simpa [prefixWord, tailWord_2006200, baseEnd_2006200] using wordTrace_append hprefix tailTrace_2006200
  have hstable : (prefixWord ++ tailWord_2006200).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006200).length < 2 ^ (prefixWord ++ tailWord_2006200).sum := by decide
  have hdescent : baseEnd_2006200 < baseStart_2006200 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006237 : List Nat := [1, 4, 3, 2, 2, 2, 1, 2, 4]
def baseStart_2006237 : Nat := 118140960795 + 2006237 * 2 ^ 59
def prefixEnd_2006237 : Nat := 4983230072969 + 3 ^ 40 * 2006237 * 2
def baseEnd_2006237 : Nat := 457850616815276587649329

theorem tailTrace_2006237 : CollatzResearch.WordTrace tailWord_2006237 prefixEnd_2006237 457850616815276587649329 := by
  unfold tailWord_2006237
  simp only [CollatzResearch.WordTrace]
  refine ⟨73173474832753461845904965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48782316555168974563936643 73173474832753461845904965)
  ·
    refine ⟨13720026531141274096107181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73173474832753461845904965 13720026531141274096107181)
    ·
      refine ⟨5145009949177977786040193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13720026531141274096107181 5145009949177977786040193)
      ·
        refine ⟨3858757461883483339530145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5145009949177977786040193 3858757461883483339530145)
        ·
          refine ⟨2894068096412612504647609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3858757461883483339530145 2894068096412612504647609)
          ·
            refine ⟨2170551072309459378485707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2894068096412612504647609 2170551072309459378485707)
            ·
              refine ⟨3255826608464189067728561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2170551072309459378485707 3255826608464189067728561)
              ·
                refine ⟨2441869956348141800796421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3255826608464189067728561 2441869956348141800796421)
                ·
                  refine ⟨457850616815276587649329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2441869956348141800796421 457850616815276587649329)
                  ·
                    rfl

theorem cell21_2006237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 1, 2, 4].length) (baseStart_2006237 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2006237 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2006237 prefixEnd_2006237 := by exact prefixLift 2006237
  have htrace : WordTrace (prefixWord ++ tailWord_2006237) baseStart_2006237 baseEnd_2006237 := by
    simpa [prefixWord, tailWord_2006237, baseEnd_2006237] using wordTrace_append hprefix tailTrace_2006237
  have hstable : (prefixWord ++ tailWord_2006237).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006237).length < 2 ^ (prefixWord ++ tailWord_2006237).sum := by decide
  have hdescent : baseEnd_2006237 < baseStart_2006237 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006248 : List Nat := [2, 1, 4, 1, 2, 1, 4, 1, 5]
def baseStart_2006248 : Nat := 118140960795 + 2006248 * 2 ^ 59
def prefixEnd_2006248 : Nat := 4983230072969 + 3 ^ 40 * 2006248 * 2
def baseEnd_2006248 : Nat := 457853127165143012965973

theorem tailTrace_2006248 : CollatzResearch.WordTrace tailWord_2006248 prefixEnd_2006248 457853127165143012965973 := by
  unfold tailWord_2006248
  simp only [CollatzResearch.WordTrace]
  refine ⟨36586938017856805362277699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48782584023809073816370265 36586938017856805362277699)
  ·
    refine ⟨54880407026785208043416549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36586938017856805362277699 54880407026785208043416549)
    ·
      refine ⟨10290076317522226508140603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54880407026785208043416549 10290076317522226508140603)
      ·
        refine ⟨15435114476283339762210905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10290076317522226508140603 15435114476283339762210905)
        ·
          refine ⟨11576335857212504821658179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15435114476283339762210905 11576335857212504821658179)
          ·
            refine ⟨17364503785818757232487269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11576335857212504821658179 17364503785818757232487269)
            ·
              refine ⟨3255844459841016981091363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17364503785818757232487269 3255844459841016981091363)
              ·
                refine ⟨4883766689761525471637045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3255844459841016981091363 4883766689761525471637045)
                ·
                  refine ⟨457853127165143012965973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4883766689761525471637045 457853127165143012965973)
                  ·
                    rfl

theorem cell21_2006248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4, 1, 5].length) (baseStart_2006248 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2006248 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2006248 prefixEnd_2006248 := by exact prefixLift 2006248
  have htrace : WordTrace (prefixWord ++ tailWord_2006248) baseStart_2006248 baseEnd_2006248 := by
    simpa [prefixWord, tailWord_2006248, baseEnd_2006248] using wordTrace_append hprefix tailTrace_2006248
  have hstable : (prefixWord ++ tailWord_2006248).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006248).length < 2 ^ (prefixWord ++ tailWord_2006248).sum := by decide
  have hdescent : baseEnd_2006248 < baseStart_2006248 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006324 : List Nat := [2, 5, 1, 1, 1, 1, 2, 1, 7]
def baseStart_2006324 : Nat := 118140960795 + 2006324 * 2 ^ 59
def prefixEnd_2006324 : Nat := 4983230072969 + 3 ^ 40 * 2006324 * 2
def baseEnd_2006324 : Nat := 457870471400583769699151

theorem tailTrace_2006324 : CollatzResearch.WordTrace tailWord_2006324 prefixEnd_2006324 457870471400583769699151 := by
  unfold tailWord_2006324
  simp only [CollatzResearch.WordTrace]
  refine ⟨36588323991719137852161013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48784431988958850469548017 36588323991719137852161013)
  ·
    refine ⟨3430155374223669173640095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36588323991719137852161013 3430155374223669173640095)
    ·
      refine ⟨5145233061335503760460143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3430155374223669173640095 5145233061335503760460143)
      ·
        refine ⟨7717849592003255640690215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5145233061335503760460143 7717849592003255640690215)
        ·
          refine ⟨11576774388004883461035323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7717849592003255640690215 11576774388004883461035323)
          ·
            refine ⟨17365161582007325191552985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11576774388004883461035323 17365161582007325191552985)
            ·
              refine ⟨13023871186505493893664739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17365161582007325191552985 13023871186505493893664739)
              ·
                refine ⟨19535806779758240840497109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13023871186505493893664739 19535806779758240840497109)
                ·
                  refine ⟨457870471400583769699151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19535806779758240840497109 457870471400583769699151)
                  ·
                    rfl

theorem cell21_2006324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_2006324 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2006324 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2006324 prefixEnd_2006324 := by exact prefixLift 2006324
  have htrace : WordTrace (prefixWord ++ tailWord_2006324) baseStart_2006324 baseEnd_2006324 := by
    simpa [prefixWord, tailWord_2006324, baseEnd_2006324] using wordTrace_append hprefix tailTrace_2006324
  have hstable : (prefixWord ++ tailWord_2006324).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006324).length < 2 ^ (prefixWord ++ tailWord_2006324).sum := by decide
  have hdescent : baseEnd_2006324 < baseStart_2006324 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006383 : List Nat := [1, 1, 2, 1, 3, 1, 5, 2, 5]
def baseStart_2006383 : Nat := 118140960795 + 2006383 * 2 ^ 59
def prefixEnd_2006383 : Nat := 4983230072969 + 3 ^ 40 * 2006383 * 2
def baseEnd_2006383 : Nat := 457883936004412778215697

theorem tailTrace_2006383 : CollatzResearch.WordTrace tailWord_2006383 prefixEnd_2006383 457883936004412778215697 := by
  unfold tailWord_2006383
  simp only [CollatzResearch.WordTrace]
  refine ⟨73178799890224528780719803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48785866593483019187146535 73178799890224528780719803)
  ·
    refine ⟨109768199835336793171079705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73178799890224528780719803 109768199835336793171079705)
    ·
      refine ⟨82326149876502594878309779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109768199835336793171079705 82326149876502594878309779)
      ·
        refine ⟨123489224814753892317464669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82326149876502594878309779 123489224814753892317464669)
        ·
          refine ⟨46308459305532709619049251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123489224814753892317464669 46308459305532709619049251)
          ·
            refine ⟨69462688958299064428573877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46308459305532709619049251 69462688958299064428573877)
            ·
              refine ⟨6512127089840537290178801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69462688958299064428573877 6512127089840537290178801)
              ·
                refine ⟨4884095317380402967634101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6512127089840537290178801 4884095317380402967634101)
                ·
                  refine ⟨457883936004412778215697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4884095317380402967634101 457883936004412778215697)
                  ·
                    rfl

theorem cell21_2006383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 2, 5].length) (baseStart_2006383 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2006383 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2006383 prefixEnd_2006383 := by exact prefixLift 2006383
  have htrace : WordTrace (prefixWord ++ tailWord_2006383) baseStart_2006383 baseEnd_2006383 := by
    simpa [prefixWord, tailWord_2006383, baseEnd_2006383] using wordTrace_append hprefix tailTrace_2006383
  have hstable : (prefixWord ++ tailWord_2006383).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006383).length < 2 ^ (prefixWord ++ tailWord_2006383).sum := by decide
  have hdescent : baseEnd_2006383 < baseStart_2006383 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006476 : List Nat := [2, 2, 1, 4, 2, 1, 3, 1, 5]
def baseStart_2006476 : Nat := 118140960795 + 2006476 * 2 ^ 59
def prefixEnd_2006476 : Nat := 4983230072969 + 3 ^ 40 * 2006476 * 2
def baseEnd_2006476 : Nat := 457905159871465283165507

theorem tailTrace_2006476 : CollatzResearch.WordTrace tailWord_2006476 prefixEnd_2006476 457905159871465283165507 := by
  unfold tailWord_2006476
  simp only [CollatzResearch.WordTrace]
  refine ⟨36591095939443802831927641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48788127919258403775903521 36591095939443802831927641)
  ·
    refine ⟨27443321954582852123945731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36591095939443802831927641 27443321954582852123945731)
    ·
      refine ⟨41164982931874278185918597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27443321954582852123945731 41164982931874278185918597)
      ·
        refine ⟨7718434299726427159859737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41164982931874278185918597 7718434299726427159859737)
        ·
          refine ⟨5788825724794820369894803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7718434299726427159859737 5788825724794820369894803)
          ·
            refine ⟨8683238587192230554842205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5788825724794820369894803 8683238587192230554842205)
            ·
              refine ⟨3256214470197086458065827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8683238587192230554842205 3256214470197086458065827)
              ·
                refine ⟨4884321705295629687098741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3256214470197086458065827 4884321705295629687098741)
                ·
                  refine ⟨457905159871465283165507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4884321705295629687098741 457905159871465283165507)
                  ·
                    rfl

theorem cell21_2006476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 3, 1, 5].length) (baseStart_2006476 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2006476 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2006476 prefixEnd_2006476 := by exact prefixLift 2006476
  have htrace : WordTrace (prefixWord ++ tailWord_2006476) baseStart_2006476 baseEnd_2006476 := by
    simpa [prefixWord, tailWord_2006476, baseEnd_2006476] using wordTrace_append hprefix tailTrace_2006476
  have hstable : (prefixWord ++ tailWord_2006476).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006476).length < 2 ^ (prefixWord ++ tailWord_2006476).sum := by decide
  have hdescent : baseEnd_2006476 < baseStart_2006476 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006504 : List Nat := [2, 1, 4, 1, 1, 2, 1, 9]
def baseStart_2006504 : Nat := 118140960795 + 2006504 * 2 ^ 59
def prefixEnd_2006504 : Nat := 4983230072969 + 3 ^ 40 * 2006504 * 2
def baseEnd_2006504 : Nat := 152637183284314485566261

theorem tailTrace_2006504 : CollatzResearch.WordTrace tailWord_2006504 prefixEnd_2006504 152637183284314485566261 := by
  unfold tailWord_2006504
  simp only [CollatzResearch.WordTrace]
  refine ⟨36591606561393083222937283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48788808748524110963916377 36591606561393083222937283)
  ·
    refine ⟨54887409842089624834405925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36591606561393083222937283 54887409842089624834405925)
    ·
      refine ⟨10291389345391804656451111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54887409842089624834405925 10291389345391804656451111)
      ·
        refine ⟨15437084018087706984676667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10291389345391804656451111 15437084018087706984676667)
        ·
          refine ⟨23155626027131560477015001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15437084018087706984676667 23155626027131560477015001)
          ·
            refine ⟨17366719520348670357761251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23155626027131560477015001 17366719520348670357761251)
            ·
              refine ⟨26050079280523005536641877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17366719520348670357761251 26050079280523005536641877)
              ·
                refine ⟨152637183284314485566261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26050079280523005536641877 152637183284314485566261)
                ·
                  rfl

theorem cell21_2006504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 9].length) (baseStart_2006504 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2006504 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2006504 prefixEnd_2006504 := by exact prefixLift 2006504
  have htrace : WordTrace (prefixWord ++ tailWord_2006504) baseStart_2006504 baseEnd_2006504 := by
    simpa [prefixWord, tailWord_2006504, baseEnd_2006504] using wordTrace_append hprefix tailTrace_2006504
  have hstable : (prefixWord ++ tailWord_2006504).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006504).length < 2 ^ (prefixWord ++ tailWord_2006504).sum := by decide
  have hdescent : baseEnd_2006504 < baseStart_2006504 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006552 : List Nat := [2, 1, 2, 3, 4, 1, 1, 2, 5]
def baseStart_2006552 : Nat := 118140960795 + 2006552 * 2 ^ 59
def prefixEnd_2006552 : Nat := 4983230072969 + 3 ^ 40 * 2006552 * 2
def baseEnd_2006552 : Nat := 457922504106906039898685

theorem tailTrace_2006552 : CollatzResearch.WordTrace tailWord_2006552 prefixEnd_2006552 457922504106906039898685 := by
  unfold tailWord_2006552
  simp only [CollatzResearch.WordTrace]
  refine ⟨36592481913306135321810955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48789975884408180429081273 36592481913306135321810955)
  ·
    refine ⟨54888722869959202982716433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36592481913306135321810955 54888722869959202982716433)
    ·
      refine ⟨41166542152469402237037325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54888722869959202982716433 41166542152469402237037325)
      ·
        refine ⟨15437453307176025838888997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41166542152469402237037325 15437453307176025838888997)
        ·
          refine ⟨2894522495095504844791687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15437453307176025838888997 2894522495095504844791687)
          ·
            refine ⟨4341783742643257267187531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2894522495095504844791687 4341783742643257267187531)
            ·
              refine ⟨6512675613964885900781297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4341783742643257267187531 6512675613964885900781297)
              ·
                refine ⟨4884506710473664425585973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6512675613964885900781297 4884506710473664425585973)
                ·
                  refine ⟨457922504106906039898685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4884506710473664425585973 457922504106906039898685)
                  ·
                    rfl

theorem cell21_2006552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 2, 5].length) (baseStart_2006552 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2006552 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2006552 prefixEnd_2006552 := by exact prefixLift 2006552
  have htrace : WordTrace (prefixWord ++ tailWord_2006552) baseStart_2006552 baseEnd_2006552 := by
    simpa [prefixWord, tailWord_2006552, baseEnd_2006552] using wordTrace_append hprefix tailTrace_2006552
  have hstable : (prefixWord ++ tailWord_2006552).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006552).length < 2 ^ (prefixWord ++ tailWord_2006552).sum := by decide
  have hdescent : baseEnd_2006552 < baseStart_2006552 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006583 : List Nat := [1, 1, 3, 1, 2, 6, 1, 2, 4]
def baseStart_2006583 : Nat := 118140960795 + 2006583 * 2 ^ 59
def prefixEnd_2006583 : Nat := 4983230072969 + 3 ^ 40 * 2006583 * 2
def baseEnd_2006583 : Nat := 457929578729256874881955

theorem tailTrace_2006583 : CollatzResearch.WordTrace tailWord_2006583 prefixEnd_2006583 457929578729256874881955 := by
  unfold tailWord_2006583
  simp only [CollatzResearch.WordTrace]
  refine ⟨73186094489499962938000403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48790729659666641958666935 73186094489499962938000403)
  ·
    refine ⟨109779141734249944407000605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73186094489499962938000403 109779141734249944407000605)
    ·
      refine ⟨41167178150343729152625227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109779141734249944407000605 41167178150343729152625227)
      ·
        refine ⟨61750767225515593728937841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41167178150343729152625227 61750767225515593728937841)
        ·
          refine ⟨46313075419136695296703381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61750767225515593728937841 46313075419136695296703381)
          ·
            refine ⟨2170925410272032592032971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 46313075419136695296703381 2170925410272032592032971)
            ·
              refine ⟨3256388115408048888049457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2170925410272032592032971 3256388115408048888049457)
              ·
                refine ⟨2442291086556036666037093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3256388115408048888049457 2442291086556036666037093)
                ·
                  refine ⟨457929578729256874881955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2442291086556036666037093 457929578729256874881955)
                  ·
                    rfl

theorem cell21_2006583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 1, 2, 4].length) (baseStart_2006583 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2006583 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2006583 prefixEnd_2006583 := by exact prefixLift 2006583
  have htrace : WordTrace (prefixWord ++ tailWord_2006583) baseStart_2006583 baseEnd_2006583 := by
    simpa [prefixWord, tailWord_2006583, baseEnd_2006583] using wordTrace_append hprefix tailTrace_2006583
  have hstable : (prefixWord ++ tailWord_2006583).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006583).length < 2 ^ (prefixWord ++ tailWord_2006583).sum := by decide
  have hdescent : baseEnd_2006583 < baseStart_2006583 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006625 : List Nat := [1, 2, 3, 1, 1, 3, 1, 1, 8]
def baseStart_2006625 : Nat := 118140960795 + 2006625 * 2 ^ 59
def prefixEnd_2006625 : Nat := 4983230072969 + 3 ^ 40 * 2006625 * 2
def baseEnd_2006625 : Nat := 457939163701474135181869

theorem tailTrace_2006625 : CollatzResearch.WordTrace tailWord_2006625 prefixEnd_2006625 457939163701474135181869 := by
  unfold tailWord_2006625
  simp only [CollatzResearch.WordTrace]
  refine ⟨73187626355347804111029329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48791750903565202740686219 73187626355347804111029329)
  ·
    refine ⟨54890719766510853083271997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73187626355347804111029329 54890719766510853083271997)
    ·
      refine ⟨20584019912441569906226999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54890719766510853083271997 20584019912441569906226999)
      ·
        refine ⟨30876029868662354859340499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20584019912441569906226999 30876029868662354859340499)
        ·
          refine ⟨46314044802993532289010749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30876029868662354859340499 46314044802993532289010749)
          ·
            refine ⟨17367766801122574608379031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46314044802993532289010749 17367766801122574608379031)
            ·
              refine ⟨26051650201683861912568547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17367766801122574608379031 26051650201683861912568547)
              ·
                refine ⟨39077475302525792868852821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26051650201683861912568547 39077475302525792868852821)
                ·
                  refine ⟨457939163701474135181869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39077475302525792868852821 457939163701474135181869)
                  ·
                    rfl

theorem cell21_2006625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 8].length) (baseStart_2006625 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2006625 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2006625 prefixEnd_2006625 := by exact prefixLift 2006625
  have htrace : WordTrace (prefixWord ++ tailWord_2006625) baseStart_2006625 baseEnd_2006625 := by
    simpa [prefixWord, tailWord_2006625, baseEnd_2006625] using wordTrace_append hprefix tailTrace_2006625
  have hstable : (prefixWord ++ tailWord_2006625).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006625).length < 2 ^ (prefixWord ++ tailWord_2006625).sum := by decide
  have hdescent : baseEnd_2006625 < baseStart_2006625 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006642 : List Nat := [3, 2, 1, 2, 3, 1, 2, 1, 6]
def baseStart_2006642 : Nat := 118140960795 + 2006642 * 2 ^ 59
def prefixEnd_2006642 : Nat := 4983230072969 + 3 ^ 40 * 2006642 * 2
def baseEnd_2006642 : Nat := 457943043333085883398501

theorem tailTrace_2006642 : CollatzResearch.WordTrace tailWord_2006642 prefixEnd_2006642 457943043333085883398501 := by
  unfold tailWord_2006642
  simp only [CollatzResearch.WordTrace]
  refine ⟨18297061599071554003599545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48792164264190810676265453 18297061599071554003599545)
  ·
    refine ⟨13722796199303665502699659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18297061599071554003599545 13722796199303665502699659)
    ·
      refine ⟨20584194298955498254049489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13722796199303665502699659 20584194298955498254049489)
      ·
        refine ⟨15438145724216623690537117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20584194298955498254049489 15438145724216623690537117)
        ·
          refine ⟨5789304646581233883951419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15438145724216623690537117 5789304646581233883951419)
          ·
            refine ⟨8683956969871850825927129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5789304646581233883951419 8683956969871850825927129)
            ·
              refine ⟨6512967727403888119445347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8683956969871850825927129 6512967727403888119445347)
              ·
                refine ⟨9769451591105832179168021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6512967727403888119445347 9769451591105832179168021)
                ·
                  refine ⟨457943043333085883398501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9769451591105832179168021 457943043333085883398501)
                  ·
                    rfl

theorem cell21_2006642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 1, 6].length) (baseStart_2006642 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2006642 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2006642 prefixEnd_2006642 := by exact prefixLift 2006642
  have htrace : WordTrace (prefixWord ++ tailWord_2006642) baseStart_2006642 baseEnd_2006642 := by
    simpa [prefixWord, tailWord_2006642, baseEnd_2006642] using wordTrace_append hprefix tailTrace_2006642
  have hstable : (prefixWord ++ tailWord_2006642).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006642).length < 2 ^ (prefixWord ++ tailWord_2006642).sum := by decide
  have hdescent : baseEnd_2006642 < baseStart_2006642 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006645 : List Nat := [1, 3, 4, 2, 1, 3, 1, 1, 5]
def baseStart_2006645 : Nat := 118140960795 + 2006645 * 2 ^ 59
def prefixEnd_2006645 : Nat := 4983230072969 + 3 ^ 40 * 2006645 * 2
def baseEnd_2006645 : Nat := 457943727973958544848495

theorem tailTrace_2006645 : CollatzResearch.WordTrace tailWord_2006645 prefixEnd_2006645 457943727973958544848495 := by
  unfold tailWord_2006645
  simp only [CollatzResearch.WordTrace]
  refine ⟨73188355815275347526757389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48792237210183565017838259 73188355815275347526757389)
  ·
    refine ⟨27445633430728255322534021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73188355815275347526757389 27445633430728255322534021)
    ·
      refine ⟨5146056268261547872975129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27445633430728255322534021 5146056268261547872975129)
      ·
        refine ⟨3859542201196160904731347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5146056268261547872975129 3859542201196160904731347)
        ·
          refine ⟨5789313301794241357097021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3859542201196160904731347 5789313301794241357097021)
          ·
            refine ⟨2170992488172840508911383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5789313301794241357097021 2170992488172840508911383)
            ·
              refine ⟨3256488732259260763367075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2170992488172840508911383 3256488732259260763367075)
              ·
                refine ⟨4884733098388891145050613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3256488732259260763367075 4884733098388891145050613)
                ·
                  refine ⟨457943727973958544848495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4884733098388891145050613 457943727973958544848495)
                  ·
                    rfl

theorem cell21_2006645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 1, 1, 5].length) (baseStart_2006645 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2006645 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2006645 prefixEnd_2006645 := by exact prefixLift 2006645
  have htrace : WordTrace (prefixWord ++ tailWord_2006645) baseStart_2006645 baseEnd_2006645 := by
    simpa [prefixWord, tailWord_2006645, baseEnd_2006645] using wordTrace_append hprefix tailTrace_2006645
  have hstable : (prefixWord ++ tailWord_2006645).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006645).length < 2 ^ (prefixWord ++ tailWord_2006645).sum := by decide
  have hdescent : baseEnd_2006645 < baseStart_2006645 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006656 : List Nat := [2, 1, 1, 2, 1, 4, 4, 6]
def baseStart_2006656 : Nat := 118140960795 + 2006656 * 2 ^ 59
def prefixEnd_2006656 : Nat := 4983230072969 + 3 ^ 40 * 2006656 * 2
def baseEnd_2006656 : Nat := 152648746107941656721713

theorem tailTrace_2006656 : CollatzResearch.WordTrace tailWord_2006656 prefixEnd_2006656 152648746107941656721713 := by
  unfold tailWord_2006656
  simp only [CollatzResearch.WordTrace]
  refine ⟨36594378509117748202703911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48792504678823664270271881 36594378509117748202703911)
  ·
    refine ⟨54891567763676622304055867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36594378509117748202703911 54891567763676622304055867)
    ·
      refine ⟨82337351645514933456083801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54891567763676622304055867 82337351645514933456083801)
      ·
        refine ⟨61753013734136200092062851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82337351645514933456083801 61753013734136200092062851)
        ·
          refine ⟨92629520601204300138094277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61753013734136200092062851 92629520601204300138094277)
          ·
            refine ⟨17368035112725806275892677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92629520601204300138094277 17368035112725806275892677)
            ·
              refine ⟨3256506583636088676729877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17368035112725806275892677 3256506583636088676729877)
              ·
                refine ⟨152648746107941656721713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3256506583636088676729877 152648746107941656721713)
                ·
                  rfl

theorem cell21_2006656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 4, 6].length) (baseStart_2006656 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2006656 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2006656 prefixEnd_2006656 := by exact prefixLift 2006656
  have htrace : WordTrace (prefixWord ++ tailWord_2006656) baseStart_2006656 baseEnd_2006656 := by
    simpa [prefixWord, tailWord_2006656, baseEnd_2006656] using wordTrace_append hprefix tailTrace_2006656
  have hstable : (prefixWord ++ tailWord_2006656).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006656).length < 2 ^ (prefixWord ++ tailWord_2006656).sum := by decide
  have hdescent : baseEnd_2006656 < baseStart_2006656 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006690 : List Nat := [3, 3, 1, 4, 2, 8]
def baseStart_2006690 : Nat := 118140960795 + 2006690 * 2 ^ 59
def prefixEnd_2006690 : Nat := 4983230072969 + 3 ^ 40 * 2006690 * 2
def baseEnd_2006690 : Nat := 16961259169890683948089

theorem tailTrace_2006690 : CollatzResearch.WordTrace tailWord_2006690 prefixEnd_2006690 16961259169890683948089 := by
  unfold tailWord_2006690
  simp only [CollatzResearch.WordTrace]
  refine ⟨18297499275028080053036381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48793331400074880141430349 18297499275028080053036381)
  ·
    refine ⟨6861562228135530019888643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18297499275028080053036381 6861562228135530019888643)
    ·
      refine ⟨10292343342203295029832965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6861562228135530019888643 10292343342203295029832965)
      ·
        refine ⟨1929814376663117818093681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10292343342203295029832965 1929814376663117818093681)
        ·
          refine ⟨1447360782497338363570261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1929814376663117818093681 1447360782497338363570261)
          ·
            refine ⟨16961259169890683948089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1447360782497338363570261 16961259169890683948089)
            ·
              rfl

theorem cell21_2006690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 8].length) (baseStart_2006690 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2006690 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2006690 prefixEnd_2006690 := by exact prefixLift 2006690
  have htrace : WordTrace (prefixWord ++ tailWord_2006690) baseStart_2006690 baseEnd_2006690 := by
    simpa [prefixWord, tailWord_2006690, baseEnd_2006690] using wordTrace_append hprefix tailTrace_2006690
  have hstable : (prefixWord ++ tailWord_2006690).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006690).length < 2 ^ (prefixWord ++ tailWord_2006690).sum := by decide
  have hdescent : baseEnd_2006690 < baseStart_2006690 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006901 : List Nat := [1, 3, 4, 1, 1, 1, 5, 5]
def baseStart_2006901 : Nat := 118140960795 + 2006901 * 2 ^ 59
def prefixEnd_2006901 : Nat := 4983230072969 + 3 ^ 40 * 2006901 * 2
def baseEnd_2006901 : Nat := 152667383553919662860435

theorem tailTrace_2006901 : CollatzResearch.WordTrace tailWord_2006901 prefixEnd_2006901 152667383553919662860435 := by
  unfold tailWord_2006901
  simp only [CollatzResearch.WordTrace]
  refine ⟨73197692902347903248076557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48798461934898602165384371 73197692902347903248076557)
  ·
    refine ⟨27449134838380463718028709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73197692902347903248076557 27449134838380463718028709)
    ·
      refine ⟨5146712782196336947130383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27449134838380463718028709 5146712782196336947130383)
      ·
        refine ⟨7720069173294505420695575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5146712782196336947130383 7720069173294505420695575)
        ·
          refine ⟨11580103759941758131043363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7720069173294505420695575 11580103759941758131043363)
          ·
            refine ⟨17370155639912637196565045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11580103759941758131043363 17370155639912637196565045)
            ·
              refine ⟨1628452091241809737177973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17370155639912637196565045 1628452091241809737177973)
              ·
                refine ⟨152667383553919662860435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1628452091241809737177973 152667383553919662860435)
                ·
                  rfl

theorem cell21_2006901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 5, 5].length) (baseStart_2006901 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2006901 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2006901 prefixEnd_2006901 := by exact prefixLift 2006901
  have htrace : WordTrace (prefixWord ++ tailWord_2006901) baseStart_2006901 baseEnd_2006901 := by
    simpa [prefixWord, tailWord_2006901, baseEnd_2006901] using wordTrace_append hprefix tailTrace_2006901
  have hstable : (prefixWord ++ tailWord_2006901).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006901).length < 2 ^ (prefixWord ++ tailWord_2006901).sum := by decide
  have hdescent : baseEnd_2006901 < baseStart_2006901 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006932 : List Nat := [2, 4, 2, 1, 1, 3, 2, 1, 5]
def baseStart_2006932 : Nat := 118140960795 + 2006932 * 2 ^ 59
def prefixEnd_2006932 : Nat := 4983230072969 + 3 ^ 40 * 2006932 * 2
def baseEnd_2006932 : Nat := 458009225284109823564575

theorem tailTrace_2006932 : CollatzResearch.WordTrace tailWord_2006932 prefixEnd_2006932 458009225284109823564575 := by
  unfold tailWord_2006932
  simp only [CollatzResearch.WordTrace]
  refine ⟨36599411782617797771227525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48799215710157063694970033 36599411782617797771227525)
  ·
    refine ⟨6862389709240837082105161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36599411782617797771227525 6862389709240837082105161)
    ·
      refine ⟨5146792281930627811578871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6862389709240837082105161 5146792281930627811578871)
      ·
        refine ⟨7720188422895941717368307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5146792281930627811578871 7720188422895941717368307)
        ·
          refine ⟨11580282634343912576052461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7720188422895941717368307 11580282634343912576052461)
          ·
            refine ⟨4342605987878967216019673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11580282634343912576052461 4342605987878967216019673)
            ·
              refine ⟨3256954490909225412014755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4342605987878967216019673 3256954490909225412014755)
              ·
                refine ⟨4885431736363838118022133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3256954490909225412014755 4885431736363838118022133)
                ·
                  refine ⟨458009225284109823564575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4885431736363838118022133 458009225284109823564575)
                  ·
                    rfl

theorem cell21_2006932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 2, 1, 5].length) (baseStart_2006932 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2006932 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2006932 prefixEnd_2006932 := by exact prefixLift 2006932
  have htrace : WordTrace (prefixWord ++ tailWord_2006932) baseStart_2006932 baseEnd_2006932 := by
    simpa [prefixWord, tailWord_2006932, baseEnd_2006932] using wordTrace_append hprefix tailTrace_2006932
  have hstable : (prefixWord ++ tailWord_2006932).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006932).length < 2 ^ (prefixWord ++ tailWord_2006932).sum := by decide
  have hdescent : baseEnd_2006932 < baseStart_2006932 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006952 : List Nat := [2, 1, 6, 2, 2, 1, 2, 5]
def baseStart_2006952 : Nat := 118140960795 + 2006952 * 2 ^ 59
def prefixEnd_2006952 : Nat := 4983230072969 + 3 ^ 40 * 2006952 * 2
def baseEnd_2006952 : Nat := 152671263185531411077067

theorem tailTrace_2006952 : CollatzResearch.WordTrace tailWord_2006952 prefixEnd_2006952 152671263185531411077067 := by
  unfold tailWord_2006952
  simp only [CollatzResearch.WordTrace]
  refine ⟨36599776512581569479091555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48799702016775425972122073 36599776512581569479091555)
  ·
    refine ⟨54899664768872354218637333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36599776512581569479091555 54899664768872354218637333)
    ·
      refine ⟨2573421786040891603998625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 54899664768872354218637333 2573421786040891603998625)
      ·
        refine ⟨1930066339530668702998969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2573421786040891603998625 1930066339530668702998969)
        ·
          refine ⟨1447549754648001527249227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1930066339530668702998969 1447549754648001527249227)
          ·
            refine ⟨2171324631972002290873841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1447549754648001527249227 2171324631972002290873841)
            ·
              refine ⟨1628493473979001718155381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2171324631972002290873841 1628493473979001718155381)
              ·
                refine ⟨152671263185531411077067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1628493473979001718155381 152671263185531411077067)
                ·
                  rfl

theorem cell21_2006952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 2, 5].length) (baseStart_2006952 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2006952 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2006952 prefixEnd_2006952 := by exact prefixLift 2006952
  have htrace : WordTrace (prefixWord ++ tailWord_2006952) baseStart_2006952 baseEnd_2006952 := by
    simpa [prefixWord, tailWord_2006952, baseEnd_2006952] using wordTrace_append hprefix tailTrace_2006952
  have hstable : (prefixWord ++ tailWord_2006952).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006952).length < 2 ^ (prefixWord ++ tailWord_2006952).sum := by decide
  have hdescent : baseEnd_2006952 < baseStart_2006952 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2007171 : List Nat := [1, 1, 1, 3, 3, 3, 1, 8]
def baseStart_2007171 : Nat := 118140960795 + 2007171 * 2 ^ 59
def prefixEnd_2007171 : Nat := 4983230072969 + 3 ^ 40 * 2007171 * 2
def baseEnd_2007171 : Nat := 152687922780099506360251

theorem tailTrace_2007171 : CollatzResearch.WordTrace tailWord_2007171 prefixEnd_2007171 152687922780099506360251 := by
  unfold tailWord_2007171
  simp only [CollatzResearch.WordTrace]
  refine ⟨73207540611369739360405367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48805027074246492906936911 73207540611369739360405367)
  ·
    refine ⟨109811310917054609040608051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73207540611369739360405367 109811310917054609040608051)
    ·
      refine ⟨164716966375581913560912077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109811310917054609040608051 164716966375581913560912077)
      ·
        refine ⟨61768862390843217585342029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164716966375581913560912077 61768862390843217585342029)
        ·
          refine ⟨23163323396566206594503261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61768862390843217585342029 23163323396566206594503261)
          ·
            refine ⟨8686246273712327472938723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23163323396566206594503261 8686246273712327472938723)
            ·
              refine ⟨13029369410568491209408085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8686246273712327472938723 13029369410568491209408085)
              ·
                refine ⟨152687922780099506360251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13029369410568491209408085 152687922780099506360251)
                ·
                  rfl

theorem cell21_2007171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 8].length) (baseStart_2007171 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2007171 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2007171 prefixEnd_2007171 := by exact prefixLift 2007171
  have htrace : WordTrace (prefixWord ++ tailWord_2007171) baseStart_2007171 baseEnd_2007171 := by
    simpa [prefixWord, tailWord_2007171, baseEnd_2007171] using wordTrace_append hprefix tailTrace_2007171
  have hstable : (prefixWord ++ tailWord_2007171).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2007171).length < 2 ^ (prefixWord ++ tailWord_2007171).sum := by decide
  have hdescent : baseEnd_2007171 < baseStart_2007171 := by decide
  rcases family_descends (prefixWord ++ tailWord_2007171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2007253 : List Nat := [1, 3, 2, 4, 2, 1, 2, 3, 3]
def baseStart_2007253 : Nat := 118140960795 + 2007253 * 2 ^ 59
def prefixEnd_2007253 : Nat := 4983230072969 + 3 ^ 40 * 2007253 * 2
def baseEnd_2007253 : Nat := 458082481857484598713919

theorem tailTrace_2007253 : CollatzResearch.WordTrace tailWord_2007253 prefixEnd_2007253 458082481857484598713919 := by
  unfold tailWord_2007253
  simp only [CollatzResearch.WordTrace]
  refine ⟨73210531397072667364890413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48807020931381778243260275 73210531397072667364890413)
  ·
    refine ⟨27453949273902250261833905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73210531397072667364890413 27453949273902250261833905)
    ·
      refine ⟨20590461955426687696375429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27453949273902250261833905 20590461955426687696375429)
      ·
        refine ⟨3860711616642503943070393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20590461955426687696375429 3860711616642503943070393)
        ·
          refine ⟨2895533712481877957302795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3860711616642503943070393 2895533712481877957302795)
          ·
            refine ⟨4343300568722816935954193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2895533712481877957302795 4343300568722816935954193)
            ·
              refine ⟨3257475426542112701965645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4343300568722816935954193 3257475426542112701965645)
              ·
                refine ⟨1221553284953292263237117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3257475426542112701965645 1221553284953292263237117)
                ·
                  refine ⟨458082481857484598713919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1221553284953292263237117 458082481857484598713919)
                  ·
                    rfl

theorem cell21_2007253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 2, 3, 3].length) (baseStart_2007253 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2007253 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2007253 prefixEnd_2007253 := by exact prefixLift 2007253
  have htrace : WordTrace (prefixWord ++ tailWord_2007253) baseStart_2007253 baseEnd_2007253 := by
    simpa [prefixWord, tailWord_2007253, baseEnd_2007253] using wordTrace_append hprefix tailTrace_2007253
  have hstable : (prefixWord ++ tailWord_2007253).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2007253).length < 2 ^ (prefixWord ++ tailWord_2007253).sum := by decide
  have hdescent : baseEnd_2007253 < baseStart_2007253 := by decide
  rcases family_descends (prefixWord ++ tailWord_2007253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2007298 : List Nat := [3, 4, 1, 1, 2, 3, 2, 5]
def baseStart_2007298 : Nat := 118140960795 + 2007298 * 2 ^ 59
def prefixEnd_2007298 : Nat := 4983230072969 + 3 ^ 40 * 2007298 * 2
def baseEnd_2007298 : Nat := 152697583823524840154609

theorem tailTrace_2007298 : CollatzResearch.WordTrace tailWord_2007298 prefixEnd_2007298 152697583823524840154609 := by
  unfold tailWord_2007298
  simp only [CollatzResearch.WordTrace]
  refine ⟨18303043170477410012569637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48808115121273093366852365 18303043170477410012569637)
  ·
    refine ⟨3431820594464514377356807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18303043170477410012569637 3431820594464514377356807)
    ·
      refine ⟨5147730891696771566035211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3431820594464514377356807 5147730891696771566035211)
      ·
        refine ⟨7721596337545157349052817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5147730891696771566035211 7721596337545157349052817)
        ·
          refine ⟨5791197253158868011789613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7721596337545157349052817 5791197253158868011789613)
          ·
            refine ⟨2171698969934575504421105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5791197253158868011789613 2171698969934575504421105)
            ·
              refine ⟨1628774227450931628315829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2171698969934575504421105 1628774227450931628315829)
              ·
                refine ⟨152697583823524840154609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1628774227450931628315829 152697583823524840154609)
                ·
                  rfl

theorem cell21_2007298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 2, 5].length) (baseStart_2007298 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2007298 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2007298 prefixEnd_2007298 := by exact prefixLift 2007298
  have htrace : WordTrace (prefixWord ++ tailWord_2007298) baseStart_2007298 baseEnd_2007298 := by
    simpa [prefixWord, tailWord_2007298, baseEnd_2007298] using wordTrace_append hprefix tailTrace_2007298
  have hstable : (prefixWord ++ tailWord_2007298).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2007298).length < 2 ^ (prefixWord ++ tailWord_2007298).sum := by decide
  have hdescent : baseEnd_2007298 < baseStart_2007298 := by decide
  rcases family_descends (prefixWord ++ tailWord_2007298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2007368 : List Nat := [2, 1, 3, 1, 1, 2, 2, 1, 8]
def baseStart_2007368 : Nat := 118140960795 + 2007368 * 2 ^ 59
def prefixEnd_2007368 : Nat := 4983230072969 + 3 ^ 40 * 2007368 * 2
def baseEnd_2007368 : Nat := 458108726424269954297017

theorem tailTrace_2007368 : CollatzResearch.WordTrace tailWord_2007368 prefixEnd_2007368 458108726424269954297017 := by
  unfold tailWord_2007368
  simp only [CollatzResearch.WordTrace]
  refine ⟨36607362895828021002663379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48809817194437361336884505 36607362895828021002663379)
  ·
    refine ⟨54911044343742031503995069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36607362895828021002663379 54911044343742031503995069)
    ·
      refine ⟨20591641628903261813998151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54911044343742031503995069 20591641628903261813998151)
      ·
        refine ⟨30887462443354892720997227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20591641628903261813998151 30887462443354892720997227)
        ·
          refine ⟨46331193665032339081495841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30887462443354892720997227 46331193665032339081495841)
          ·
            refine ⟨34748395248774254311121881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46331193665032339081495841 34748395248774254311121881)
            ·
              refine ⟨26061296436580690733341411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34748395248774254311121881 26061296436580690733341411)
              ·
                refine ⟨39091944654871036100012117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26061296436580690733341411 39091944654871036100012117)
                ·
                  refine ⟨458108726424269954297017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39091944654871036100012117 458108726424269954297017)
                  ·
                    rfl

theorem cell21_2007368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 8].length) (baseStart_2007368 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2007368 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2007368 prefixEnd_2007368 := by exact prefixLift 2007368
  have htrace : WordTrace (prefixWord ++ tailWord_2007368) baseStart_2007368 baseEnd_2007368 := by
    simpa [prefixWord, tailWord_2007368, baseEnd_2007368] using wordTrace_append hprefix tailTrace_2007368
  have hstable : (prefixWord ++ tailWord_2007368).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2007368).length < 2 ^ (prefixWord ++ tailWord_2007368).sum := by decide
  have hdescent : baseEnd_2007368 < baseStart_2007368 := by decide
  rcases family_descends (prefixWord ++ tailWord_2007368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2007402 : List Nat := [3, 1, 3, 3, 1, 1, 2, 3, 4]
def baseStart_2007402 : Nat := 118140960795 + 2007402 * 2 ^ 59
def prefixEnd_2007402 : Nat := 4983230072969 + 3 ^ 40 * 2007402 * 2
def baseEnd_2007402 : Nat := 458116485687493450730281

theorem tailTrace_2007402 : CollatzResearch.WordTrace tailWord_2007402 prefixEnd_2007402 458116485687493450730281 := by
  unfold tailWord_2007402
  simp only [CollatzResearch.WordTrace]
  refine ⟨18303991468383216453016115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48810643915688577208042973 18303991468383216453016115)
  ·
    refine ⟨27455987202574824679524173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18303991468383216453016115 27455987202574824679524173)
    ·
      refine ⟨10295995200965559254821565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27455987202574824679524173 10295995200965559254821565)
      ·
        refine ⟨3860998200362084720558087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10295995200965559254821565 3860998200362084720558087)
        ·
          refine ⟨5791497300543127080837131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3860998200362084720558087 5791497300543127080837131)
          ·
            refine ⟨8687245950814690621255697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5791497300543127080837131 8687245950814690621255697)
            ·
              refine ⟨6515434463111017965941773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8687245950814690621255697 6515434463111017965941773)
              ·
                refine ⟨2443287923666631737228165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6515434463111017965941773 2443287923666631737228165)
                ·
                  refine ⟨458116485687493450730281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2443287923666631737228165 458116485687493450730281)
                  ·
                    rfl

theorem cell21_2007402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 3, 4].length) (baseStart_2007402 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2007402 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2007402 prefixEnd_2007402 := by exact prefixLift 2007402
  have htrace : WordTrace (prefixWord ++ tailWord_2007402) baseStart_2007402 baseEnd_2007402 := by
    simpa [prefixWord, tailWord_2007402, baseEnd_2007402] using wordTrace_append hprefix tailTrace_2007402
  have hstable : (prefixWord ++ tailWord_2007402).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2007402).length < 2 ^ (prefixWord ++ tailWord_2007402).sum := by decide
  have hdescent : baseEnd_2007402 < baseStart_2007402 := by decide
  rcases family_descends (prefixWord ++ tailWord_2007402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2007447 : List Nat := [1, 1, 3, 3, 1, 1, 4, 4, 3]
def baseStart_2007447 : Nat := 118140960795 + 2007447 * 2 ^ 59
def prefixEnd_2007447 : Nat := 4983230072969 + 3 ^ 40 * 2007447 * 2
def baseEnd_2007447 : Nat := 458126755300583372480189

theorem tailTrace_2007447 : CollatzResearch.WordTrace tailWord_2007447 prefixEnd_2007447 458126755300583372480189 := by
  unfold tailWord_2007447
  simp only [CollatzResearch.WordTrace]
  refine ⟨73217607158369838497452595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48811738105579892331635063 73217607158369838497452595)
  ·
    refine ⟨109826410737554757746178893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73217607158369838497452595 109826410737554757746178893)
    ·
      refine ⟨41184904026583034154817085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109826410737554757746178893 41184904026583034154817085)
      ·
        refine ⟨15444339009968637808056407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41184904026583034154817085 15444339009968637808056407)
        ·
          refine ⟨23166508514952956712084611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15444339009968637808056407 23166508514952956712084611)
          ·
            refine ⟨34749762772429435068126917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23166508514952956712084611 34749762772429435068126917)
            ·
              refine ⟨6515580519830519075273797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34749762772429435068126917 6515580519830519075273797)
              ·
                refine ⟨1221671347468222326613837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6515580519830519075273797 1221671347468222326613837)
                ·
                  refine ⟨458126755300583372480189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1221671347468222326613837 458126755300583372480189)
                  ·
                    rfl

theorem cell21_2007447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 4, 3].length) (baseStart_2007447 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2007447 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2007447 prefixEnd_2007447 := by exact prefixLift 2007447
  have htrace : WordTrace (prefixWord ++ tailWord_2007447) baseStart_2007447 baseEnd_2007447 := by
    simpa [prefixWord, tailWord_2007447, baseEnd_2007447] using wordTrace_append hprefix tailTrace_2007447
  have hstable : (prefixWord ++ tailWord_2007447).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2007447).length < 2 ^ (prefixWord ++ tailWord_2007447).sum := by decide
  have hdescent : baseEnd_2007447 < baseStart_2007447 := by decide
  rcases family_descends (prefixWord ++ tailWord_2007447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2007613 : List Nat := [1, 4, 1, 3, 2, 2, 1, 1, 6]
def baseStart_2007613 : Nat := 118140960795 + 2007613 * 2 ^ 59
def prefixEnd_2007613 : Nat := 4983230072969 + 3 ^ 40 * 2007613 * 2
def baseEnd_2007613 : Nat := 458164638762203972713183

theorem tailTrace_2007613 : CollatzResearch.WordTrace tailWord_2007613 prefixEnd_2007613 458164638762203972713183 := by
  unfold tailWord_2007613
  simp only [CollatzResearch.WordTrace]
  refine ⟨73223661675768448847995493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48815774450512299231996995 73223661675768448847995493)
  ·
    refine ⟨13729436564206584158999155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73223661675768448847995493 13729436564206584158999155)
    ·
      refine ⟨20594154846309876238498733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13729436564206584158999155 20594154846309876238498733)
      ·
        refine ⟨7722808067366203589437025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20594154846309876238498733 7722808067366203589437025)
        ·
          refine ⟨5792106050524652692077769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7722808067366203589437025 5792106050524652692077769)
          ·
            refine ⟨4344079537893489519058327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5792106050524652692077769 4344079537893489519058327)
            ·
              refine ⟨6516119306840234278587491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4344079537893489519058327 6516119306840234278587491)
              ·
                refine ⟨9774178960260351417881237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6516119306840234278587491 9774178960260351417881237)
                ·
                  refine ⟨458164638762203972713183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9774178960260351417881237 458164638762203972713183)
                  ·
                    rfl

theorem cell21_2007613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 1, 6].length) (baseStart_2007613 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2007613 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2007613 prefixEnd_2007613 := by exact prefixLift 2007613
  have htrace : WordTrace (prefixWord ++ tailWord_2007613) baseStart_2007613 baseEnd_2007613 := by
    simpa [prefixWord, tailWord_2007613, baseEnd_2007613] using wordTrace_append hprefix tailTrace_2007613
  have hstable : (prefixWord ++ tailWord_2007613).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2007613).length < 2 ^ (prefixWord ++ tailWord_2007613).sum := by decide
  have hdescent : baseEnd_2007613 < baseStart_2007613 := by decide
  rcases family_descends (prefixWord ++ tailWord_2007613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2007644 : List Nat := [2, 2, 4, 1, 3, 1, 1, 7]
def baseStart_2007644 : Nat := 118140960795 + 2007644 * 2 ^ 59
def prefixEnd_2007644 : Nat := 4983230072969 + 3 ^ 40 * 2007644 * 2
def baseEnd_2007644 : Nat := 152723904461518269232151

theorem tailTrace_2007644 : CollatzResearch.WordTrace tailWord_2007644 prefixEnd_2007644 152723904461518269232151 := by
  unfold tailWord_2007644
  simp only [CollatzResearch.WordTrace]
  refine ⟨36612396169328070571186993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48816528225770760761582657 36612396169328070571186993)
  ·
    refine ⟨27459297126996052928390245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36612396169328070571186993 27459297126996052928390245)
    ·
      refine ⟨5148618211311759924073171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27459297126996052928390245 5148618211311759924073171)
      ·
        refine ⟨7722927316967639886109757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5148618211311759924073171 7722927316967639886109757)
        ·
          refine ⟨2896097743862864957291159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7722927316967639886109757 2896097743862864957291159)
          ·
            refine ⟨4344146615794297435936739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2896097743862864957291159 4344146615794297435936739)
            ·
              refine ⟨6516219923691446153905109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4344146615794297435936739 6516219923691446153905109)
              ·
                refine ⟨152723904461518269232151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6516219923691446153905109 152723904461518269232151)
                ·
                  rfl

theorem cell21_2007644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 7].length) (baseStart_2007644 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2007644 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2007644 prefixEnd_2007644 := by exact prefixLift 2007644
  have htrace : WordTrace (prefixWord ++ tailWord_2007644) baseStart_2007644 baseEnd_2007644 := by
    simpa [prefixWord, tailWord_2007644, baseEnd_2007644] using wordTrace_append hprefix tailTrace_2007644
  have hstable : (prefixWord ++ tailWord_2007644).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2007644).length < 2 ^ (prefixWord ++ tailWord_2007644).sum := by decide
  have hdescent : baseEnd_2007644 < baseStart_2007644 := by decide
  rcases family_descends (prefixWord ++ tailWord_2007644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2007650 : List Nat := [3, 3, 2, 3, 1, 2, 1, 3, 3]
def baseStart_2007650 : Nat := 118140960795 + 2007650 * 2 ^ 59
def prefixEnd_2007650 : Nat := 4983230072969 + 3 ^ 40 * 2007650 * 2
def baseEnd_2007650 : Nat := 458173082666300130596441

theorem tailTrace_2007650 : CollatzResearch.WordTrace tailWord_2007650 prefixEnd_2007650 458173082666300130596441 := by
  unfold tailWord_2007650
  simp only [CollatzResearch.WordTrace]
  refine ⟨18306252794158601041773101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48816674117756269444728269 18306252794158601041773101)
  ·
    refine ⟨6864844797809475390664913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18306252794158601041773101 6864844797809475390664913)
    ·
      refine ⟨5148633598357106542998685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6864844797809475390664913 5148633598357106542998685)
      ·
        refine ⟨1930737599383914953624507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5148633598357106542998685 1930737599383914953624507)
        ·
          refine ⟨2896106399075872430436761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1930737599383914953624507 2896106399075872430436761)
          ·
            refine ⟨2172079799306904322827571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2896106399075872430436761 2172079799306904322827571)
            ·
              refine ⟨3258119698960356484241357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2172079799306904322827571 3258119698960356484241357)
              ·
                refine ⟨1221794887110133681590509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3258119698960356484241357 1221794887110133681590509)
                ·
                  refine ⟨458173082666300130596441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1221794887110133681590509 458173082666300130596441)
                  ·
                    rfl

theorem cell21_2007650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 1, 3, 3].length) (baseStart_2007650 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2007650 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2007650 prefixEnd_2007650 := by exact prefixLift 2007650
  have htrace : WordTrace (prefixWord ++ tailWord_2007650) baseStart_2007650 baseEnd_2007650 := by
    simpa [prefixWord, tailWord_2007650, baseEnd_2007650] using wordTrace_append hprefix tailTrace_2007650
  have hstable : (prefixWord ++ tailWord_2007650).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2007650).length < 2 ^ (prefixWord ++ tailWord_2007650).sum := by decide
  have hdescent : baseEnd_2007650 < baseStart_2007650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2007650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2007726 : List Nat := [4, 1, 4, 1, 1, 3, 2, 2, 3]
def baseStart_2007726 : Nat := 118140960795 + 2007726 * 2 ^ 59
def prefixEnd_2007726 : Nat := 4983230072969 + 3 ^ 40 * 2007726 * 2
def baseEnd_2007726 : Nat := 458190426901740887329619

theorem tailTrace_2007726 : CollatzResearch.WordTrace tailWord_2007726 prefixEnd_2007726 458190426901740887329619 := by
  unfold tailWord_2007726
  simp only [CollatzResearch.WordTrace]
  refine ⟨9153472890544883643357379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48818522082906046097906021 9153472890544883643357379)
  ·
    refine ⟨13730209335817325465036069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9153472890544883643357379 13730209335817325465036069)
    ·
      refine ⟨2574414250465748524694263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13730209335817325465036069 2574414250465748524694263)
      ·
        refine ⟨3861621375698622787041395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2574414250465748524694263 3861621375698622787041395)
        ·
          refine ⟨5792432063547934180562093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3861621375698622787041395 5792432063547934180562093)
          ·
            refine ⟨2172162023830475317710785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5792432063547934180562093 2172162023830475317710785)
            ·
              refine ⟨1629121517872856488283089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2172162023830475317710785 1629121517872856488283089)
              ·
                refine ⟨1221841138404642366212317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1629121517872856488283089 1221841138404642366212317)
                ·
                  refine ⟨458190426901740887329619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1221841138404642366212317 458190426901740887329619)
                  ·
                    rfl

theorem cell21_2007726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 2, 2, 3].length) (baseStart_2007726 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2007726 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2007726 prefixEnd_2007726 := by exact prefixLift 2007726
  have htrace : WordTrace (prefixWord ++ tailWord_2007726) baseStart_2007726 baseEnd_2007726 := by
    simpa [prefixWord, tailWord_2007726, baseEnd_2007726] using wordTrace_append hprefix tailTrace_2007726
  have hstable : (prefixWord ++ tailWord_2007726).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2007726).length < 2 ^ (prefixWord ++ tailWord_2007726).sum := by decide
  have hdescent : baseEnd_2007726 < baseStart_2007726 := by decide
  rcases family_descends (prefixWord ++ tailWord_2007726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2007779 : List Nat := [1, 1, 1, 7, 1, 2, 8]
def baseStart_2007779 : Nat := 118140960795 + 2007779 * 2 ^ 59
def prefixEnd_2007779 : Nat := 4983230072969 + 3 ^ 40 * 2007779 * 2
def baseEnd_2007779 : Nat := 50911391358202730327353

theorem tailTrace_2007779 : CollatzResearch.WordTrace tailWord_2007779 prefixEnd_2007779 50911391358202730327353 := by
  unfold tailWord_2007779
  simp only [CollatzResearch.WordTrace]
  refine ⟨73229716193167059198538391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48819810795444706132358927 73229716193167059198538391)
  ·
    refine ⟨109844574289750588797807587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73229716193167059198538391 109844574289750588797807587)
    ·
      refine ⟨164766861434625883196711381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109844574289750588797807587 164766861434625883196711381)
      ·
        refine ⟨3861723314874044137422923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 164766861434625883196711381 3861723314874044137422923)
        ·
          refine ⟨5792584972311066206134385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3861723314874044137422923 5792584972311066206134385)
          ·
            refine ⟨4344438729233299654600789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5792584972311066206134385 4344438729233299654600789)
            ·
              refine ⟨50911391358202730327353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4344438729233299654600789 50911391358202730327353)
              ·
                rfl

theorem cell21_2007779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 8].length) (baseStart_2007779 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2007779 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2007779 prefixEnd_2007779 := by exact prefixLift 2007779
  have htrace : WordTrace (prefixWord ++ tailWord_2007779) baseStart_2007779 baseEnd_2007779 := by
    simpa [prefixWord, tailWord_2007779, baseEnd_2007779] using wordTrace_append hprefix tailTrace_2007779
  have hstable : (prefixWord ++ tailWord_2007779).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2007779).length < 2 ^ (prefixWord ++ tailWord_2007779).sum := by decide
  have hdescent : baseEnd_2007779 < baseStart_2007779 := by decide
  rcases family_descends (prefixWord ++ tailWord_2007779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2007844 : List Nat := [2, 3, 1, 3, 4, 1, 1, 1, 5]
def baseStart_2007844 : Nat := 118140960795 + 2007844 * 2 ^ 59
def prefixEnd_2007844 : Nat := 4983230072969 + 3 ^ 40 * 2007844 * 2
def baseEnd_2007844 : Nat := 458217356109398904362711

theorem tailTrace_2007844 : CollatzResearch.WordTrace tailWord_2007844 prefixEnd_2007844 458217356109398904362711 := by
  unfold tailWord_2007844
  simp only [CollatzResearch.WordTrace]
  refine ⟨36616043468965787649827293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48821391291954383533103057 36616043468965787649827293)
  ·
    refine ⟨13731016300862170368685235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36616043468965787649827293 13731016300862170368685235)
    ·
      refine ⟨20596524451293255553027853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13731016300862170368685235 20596524451293255553027853)
      ·
        refine ⟨7723696669234970832385445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20596524451293255553027853 7723696669234970832385445)
        ·
          refine ⟨1448193125481557031072271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7723696669234970832385445 1448193125481557031072271)
          ·
            refine ⟨2172289688222335546608407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1448193125481557031072271 2172289688222335546608407)
            ·
              refine ⟨3258434532333503319912611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2172289688222335546608407 3258434532333503319912611)
              ·
                refine ⟨4887651798500254979868917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3258434532333503319912611 4887651798500254979868917)
                ·
                  refine ⟨458217356109398904362711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4887651798500254979868917 458217356109398904362711)
                  ·
                    rfl

theorem cell21_2007844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 1, 1, 5].length) (baseStart_2007844 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2007844 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2007844 prefixEnd_2007844 := by exact prefixLift 2007844
  have htrace : WordTrace (prefixWord ++ tailWord_2007844) baseStart_2007844 baseEnd_2007844 := by
    simpa [prefixWord, tailWord_2007844, baseEnd_2007844] using wordTrace_append hprefix tailTrace_2007844
  have hstable : (prefixWord ++ tailWord_2007844).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2007844).length < 2 ^ (prefixWord ++ tailWord_2007844).sum := by decide
  have hdescent : baseEnd_2007844 < baseStart_2007844 := by decide
  rcases family_descends (prefixWord ++ tailWord_2007844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008072 : List Nat := [2, 1, 3, 2, 1, 5, 2, 2, 3]
def baseStart_2008072 : Nat := 118140960795 + 2008072 * 2 ^ 59
def prefixEnd_2008072 : Nat := 4983230072969 + 3 ^ 40 * 2008072 * 2
def baseEnd_2008072 : Nat := 458269388815721174562245

theorem tailTrace_2008072 : CollatzResearch.WordTrace tailWord_2008072 prefixEnd_2008072 458269388815721174562245 := by
  unfold tailWord_2008072
  simp only [CollatzResearch.WordTrace]
  refine ⟨36620201390552785119477235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48826935187403713492636313 36620201390552785119477235)
  ·
    refine ⟨54930302085829177679215853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36620201390552785119477235 54930302085829177679215853)
    ·
      refine ⟨20598863282185941629705945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54930302085829177679215853 20598863282185941629705945)
      ·
        refine ⟨15449147461639456222279459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20598863282185941629705945 15449147461639456222279459)
        ·
          refine ⟨23173721192459184333419189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15449147461639456222279459 23173721192459184333419189)
          ·
            refine ⟨2172536361793048531258049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23173721192459184333419189 2172536361793048531258049)
            ·
              refine ⟨1629402271344786398443537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2172536361793048531258049 1629402271344786398443537)
              ·
                refine ⟨1222051703508589798832653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1629402271344786398443537 1222051703508589798832653)
                ·
                  refine ⟨458269388815721174562245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1222051703508589798832653 458269388815721174562245)
                  ·
                    rfl

theorem cell21_2008072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 2, 2, 3].length) (baseStart_2008072 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2008072 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2008072 prefixEnd_2008072 := by exact prefixLift 2008072
  have htrace : WordTrace (prefixWord ++ tailWord_2008072) baseStart_2008072 baseEnd_2008072 := by
    simpa [prefixWord, tailWord_2008072, baseEnd_2008072] using wordTrace_append hprefix tailTrace_2008072
  have hstable : (prefixWord ++ tailWord_2008072).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008072).length < 2 ^ (prefixWord ++ tailWord_2008072).sum := by decide
  have hdescent : baseEnd_2008072 < baseStart_2008072 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008097 : List Nat := [1, 2, 3, 2, 3, 1, 1, 1, 7]
def baseStart_2008097 : Nat := 118140960795 + 2008097 * 2 ^ 59
def prefixEnd_2008097 : Nat := 4983230072969 + 3 ^ 40 * 2008097 * 2
def baseEnd_2008097 : Nat := 458275094156326686645527

theorem tailTrace_2008097 : CollatzResearch.WordTrace tailWord_2008097 prefixEnd_2008097 458275094156326686645527 := by
  unfold tailWord_2008097
  simp only [CollatzResearch.WordTrace]
  refine ⟨73241314606014999508614545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48827543070676666339076363 73241314606014999508614545)
  ·
    refine ⟨54930985954511249631460909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73241314606014999508614545 54930985954511249631460909)
    ·
      refine ⟨20599119732941718611797841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54930985954511249631460909 20599119732941718611797841)
      ·
        refine ⟨15449339799706288958848381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20599119732941718611797841 15449339799706288958848381)
        ·
          refine ⟨5793502424889858359568143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15449339799706288958848381 5793502424889858359568143)
          ·
            refine ⟨8690253637334787539352215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5793502424889858359568143 8690253637334787539352215)
            ·
              refine ⟨13035380456002181309028323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8690253637334787539352215 13035380456002181309028323)
              ·
                refine ⟨19553070684003271963542485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13035380456002181309028323 19553070684003271963542485)
                ·
                  refine ⟨458275094156326686645527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19553070684003271963542485 458275094156326686645527)
                  ·
                    rfl

theorem cell21_2008097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 1, 7].length) (baseStart_2008097 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2008097 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2008097 prefixEnd_2008097 := by exact prefixLift 2008097
  have htrace : WordTrace (prefixWord ++ tailWord_2008097) baseStart_2008097 baseEnd_2008097 := by
    simpa [prefixWord, tailWord_2008097, baseEnd_2008097] using wordTrace_append hprefix tailTrace_2008097
  have hstable : (prefixWord ++ tailWord_2008097).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008097).length < 2 ^ (prefixWord ++ tailWord_2008097).sum := by decide
  have hdescent : baseEnd_2008097 < baseStart_2008097 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008100 : List Nat := [2, 3, 1, 4, 1, 2, 3, 5]
def baseStart_2008100 : Nat := 118140960795 + 2008100 * 2 ^ 59
def prefixEnd_2008100 : Nat := 4983230072969 + 3 ^ 40 * 2008100 * 2
def baseEnd_2008100 : Nat := 152758592932399782698507

theorem tailTrace_2008100 : CollatzResearch.WordTrace tailWord_2008100 prefixEnd_2008100 152758592932399782698507 := by
  unfold tailWord_2008100
  simp only [CollatzResearch.WordTrace]
  refine ⟨36620712012502065510486877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48827616016669420680649169 36620712012502065510486877)
  ·
    refine ⟨13732767004688274566432579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36620712012502065510486877 13732767004688274566432579)
    ·
      refine ⟨20599150507032411849648869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13732767004688274566432579 20599150507032411849648869)
      ·
        refine ⟨3862340720068577221809163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20599150507032411849648869 3862340720068577221809163)
        ·
          refine ⟨5793511080102865832713745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3862340720068577221809163 5793511080102865832713745)
          ·
            refine ⟨4345133310077149374535309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5793511080102865832713745 4345133310077149374535309)
            ·
              refine ⟨1629424991278931015450741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4345133310077149374535309 1629424991278931015450741)
              ·
                refine ⟨152758592932399782698507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1629424991278931015450741 152758592932399782698507)
                ·
                  rfl

theorem cell21_2008100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 3, 5].length) (baseStart_2008100 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2008100 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2008100 prefixEnd_2008100 := by exact prefixLift 2008100
  have htrace : WordTrace (prefixWord ++ tailWord_2008100) baseStart_2008100 baseEnd_2008100 := by
    simpa [prefixWord, tailWord_2008100, baseEnd_2008100] using wordTrace_append hprefix tailTrace_2008100
  have hstable : (prefixWord ++ tailWord_2008100).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008100).length < 2 ^ (prefixWord ++ tailWord_2008100).sum := by decide
  have hdescent : baseEnd_2008100 < baseStart_2008100 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008142 : List Nat := [4, 1, 1, 1, 1, 3, 2, 8]
def baseStart_2008142 : Nat := 118140960795 + 2008142 * 2 ^ 59
def prefixEnd_2008142 : Nat := 4983230072969 + 3 ^ 40 * 2008142 * 2
def baseEnd_2008142 : Nat := 152761787923138869465145

theorem tailTrace_2008142 : CollatzResearch.WordTrace tailWord_2008142 prefixEnd_2008142 152761787923138869465145 := by
  unfold tailWord_2008142
  simp only [CollatzResearch.WordTrace]
  refine ⟨9155369486356496524250335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48828637260567981462668453 9155369486356496524250335)
  ·
    refine ⟨13733054229534744786375503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9155369486356496524250335 13733054229534744786375503)
    ·
      refine ⟨20599581344302117179563255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13733054229534744786375503 20599581344302117179563255)
      ·
        refine ⟨30899372016453175769344883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20599581344302117179563255 30899372016453175769344883)
        ·
          refine ⟨46349058024679763654017325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30899372016453175769344883 46349058024679763654017325)
          ·
            refine ⟨17380896759254911370256497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46349058024679763654017325 17380896759254911370256497)
            ·
              refine ⟨13035672569441183527692373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17380896759254911370256497 13035672569441183527692373)
              ·
                refine ⟨152761787923138869465145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13035672569441183527692373 152761787923138869465145)
                ·
                  rfl

theorem cell21_2008142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 8].length) (baseStart_2008142 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2008142 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2008142 prefixEnd_2008142 := by exact prefixLift 2008142
  have htrace : WordTrace (prefixWord ++ tailWord_2008142) baseStart_2008142 baseEnd_2008142 := by
    simpa [prefixWord, tailWord_2008142, baseEnd_2008142] using wordTrace_append hprefix tailTrace_2008142
  have hstable : (prefixWord ++ tailWord_2008142).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008142).length < 2 ^ (prefixWord ++ tailWord_2008142).sum := by decide
  have hdescent : baseEnd_2008142 < baseStart_2008142 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008328 : List Nat := [2, 1, 3, 2, 4, 2, 2, 5]
def baseStart_2008328 : Nat := 118140960795 + 2008328 * 2 ^ 59
def prefixEnd_2008328 : Nat := 4983230072969 + 3 ^ 40 * 2008328 * 2
def baseEnd_2008328 : Nat := 152775937167840539431685

theorem tailTrace_2008328 : CollatzResearch.WordTrace tailWord_2008328 prefixEnd_2008328 152775937167840539431685 := by
  unfold tailWord_2008328
  simp only [CollatzResearch.WordTrace]
  refine ⟨36624869934089062980136819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48833159912118750640182425 36624869934089062980136819)
  ·
    refine ⟨54937304901133594470205229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36624869934089062980136819 54937304901133594470205229)
    ·
      refine ⟨20601489337925097926326961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54937304901133594470205229 20601489337925097926326961)
      ·
        refine ⟨15451117003443823444745221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20601489337925097926326961 15451117003443823444745221)
        ·
          refine ⟨2897084438145716895889729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15451117003443823444745221 2897084438145716895889729)
          ·
            refine ⟨2172813328609287671917297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2897084438145716895889729 2172813328609287671917297)
            ·
              refine ⟨1629609996456965753937973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2172813328609287671917297 1629609996456965753937973)
              ·
                refine ⟨152775937167840539431685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1629609996456965753937973 152775937167840539431685)
                ·
                  rfl

theorem cell21_2008328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 2, 5].length) (baseStart_2008328 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2008328 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2008328 prefixEnd_2008328 := by exact prefixLift 2008328
  have htrace : WordTrace (prefixWord ++ tailWord_2008328) baseStart_2008328 baseEnd_2008328 := by
    simpa [prefixWord, tailWord_2008328, baseEnd_2008328] using wordTrace_append hprefix tailTrace_2008328
  have hstable : (prefixWord ++ tailWord_2008328).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008328).length < 2 ^ (prefixWord ++ tailWord_2008328).sum := by decide
  have hdescent : baseEnd_2008328 < baseStart_2008328 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008356 : List Nat := [2, 3, 1, 3, 1, 1, 2, 4, 4]
def baseStart_2008356 : Nat := 118140960795 + 2008356 * 2 ^ 59
def prefixEnd_2008356 : Nat := 4983230072969 + 3 ^ 40 * 2008356 * 2
def baseEnd_2008356 : Nat := 458334201484999791828331

theorem tailTrace_2008356 : CollatzResearch.WordTrace tailWord_2008356 prefixEnd_2008356 458334201484999791828331 := by
  unfold tailWord_2008356
  simp only [CollatzResearch.WordTrace]
  refine ⟨36625380556038343371146461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48833840741384457828195281 36625380556038343371146461)
  ·
    refine ⟨13734517708514378764179923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36625380556038343371146461 13734517708514378764179923)
    ·
      refine ⟨20601776562771568146269885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13734517708514378764179923 20601776562771568146269885)
      ·
        refine ⟨7725666211039338054851207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20601776562771568146269885 7725666211039338054851207)
        ·
          refine ⟨11588499316559007082276811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7725666211039338054851207 11588499316559007082276811)
          ·
            refine ⟨17382748974838510623415217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11588499316559007082276811 17382748974838510623415217)
            ·
              refine ⟨13037061731128882967561413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17382748974838510623415217 13037061731128882967561413)
              ·
                refine ⟨2444449074586665556417765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13037061731128882967561413 2444449074586665556417765)
                ·
                  refine ⟨458334201484999791828331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2444449074586665556417765 458334201484999791828331)
                  ·
                    rfl

theorem cell21_2008356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 4, 4].length) (baseStart_2008356 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2008356 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2008356 prefixEnd_2008356 := by exact prefixLift 2008356
  have htrace : WordTrace (prefixWord ++ tailWord_2008356) baseStart_2008356 baseEnd_2008356 := by
    simpa [prefixWord, tailWord_2008356, baseEnd_2008356] using wordTrace_append hprefix tailTrace_2008356
  have hstable : (prefixWord ++ tailWord_2008356).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008356).length < 2 ^ (prefixWord ++ tailWord_2008356).sum := by decide
  have hdescent : baseEnd_2008356 < baseStart_2008356 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008370 : List Nat := [3, 2, 1, 1, 4, 1, 1, 8]
def baseStart_2008370 : Nat := 118140960795 + 2008370 * 2 ^ 59
def prefixEnd_2008370 : Nat := 4983230072969 + 3 ^ 40 * 2008370 * 2
def baseEnd_2008370 : Nat := 152779132158579626198323

theorem tailTrace_2008370 : CollatzResearch.WordTrace tailWord_2008370 prefixEnd_2008370 152779132158579626198323 := by
  unfold tailWord_2008370
  simp only [CollatzResearch.WordTrace]
  refine ⟨18312817933506491783325641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48834181156017311422201709 18312817933506491783325641)
  ·
    refine ⟨13734613450129868837494231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18312817933506491783325641 13734613450129868837494231)
    ·
      refine ⟨20601920175194803256241347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13734613450129868837494231 20601920175194803256241347)
      ·
        refine ⟨30902880262792204884362021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20601920175194803256241347 30902880262792204884362021)
        ·
          refine ⟨5794290049273538415817879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30902880262792204884362021 5794290049273538415817879)
          ·
            refine ⟨8691435073910307623726819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5794290049273538415817879 8691435073910307623726819)
            ·
              refine ⟨13037152610865461435590229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8691435073910307623726819 13037152610865461435590229)
              ·
                refine ⟨152779132158579626198323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13037152610865461435590229 152779132158579626198323)
                ·
                  rfl

theorem cell21_2008370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 8].length) (baseStart_2008370 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2008370 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2008370 prefixEnd_2008370 := by exact prefixLift 2008370
  have htrace : WordTrace (prefixWord ++ tailWord_2008370) baseStart_2008370 baseEnd_2008370 := by
    simpa [prefixWord, tailWord_2008370, baseEnd_2008370] using wordTrace_append hprefix tailTrace_2008370
  have hstable : (prefixWord ++ tailWord_2008370).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008370).length < 2 ^ (prefixWord ++ tailWord_2008370).sum := by decide
  have hdescent : baseEnd_2008370 < baseStart_2008370 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008373 : List Nat := [1, 3, 3, 1, 2, 2, 4, 1, 4]
def baseStart_2008373 : Nat := 118140960795 + 2008373 * 2 ^ 59
def prefixEnd_2008373 : Nat := 4983230072969 + 3 ^ 40 * 2008373 * 2
def baseEnd_2008373 : Nat := 458338081116611540044963

theorem tailTrace_2008373 : CollatzResearch.WordTrace tailWord_2008373 prefixEnd_2008373 458338081116611540044963 := by
  unfold tailWord_2008373
  simp only [CollatzResearch.WordTrace]
  refine ⟨73251381153015098645661773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48834254102010065763774515 73251381153015098645661773)
  ·
    refine ⟨27469267932380661992123165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73251381153015098645661773 27469267932380661992123165)
    ·
      refine ⟨10300975474642748247046187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27469267932380661992123165 10300975474642748247046187)
      ·
        refine ⟨15451463211964122370569281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10300975474642748247046187 15451463211964122370569281)
        ·
          refine ⟨11588597408973091777926961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15451463211964122370569281 11588597408973091777926961)
          ·
            refine ⟨8691448056729818833445221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11588597408973091777926961 8691448056729818833445221)
            ·
              refine ⟨1629646510636841031270979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8691448056729818833445221 1629646510636841031270979)
              ·
                refine ⟨2444469765955261546906469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1629646510636841031270979 2444469765955261546906469)
                ·
                  refine ⟨458338081116611540044963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2444469765955261546906469 458338081116611540044963)
                  ·
                    rfl

theorem cell21_2008373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 4, 1, 4].length) (baseStart_2008373 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2008373 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2008373 prefixEnd_2008373 := by exact prefixLift 2008373
  have htrace : WordTrace (prefixWord ++ tailWord_2008373) baseStart_2008373 baseEnd_2008373 := by
    simpa [prefixWord, tailWord_2008373, baseEnd_2008373] using wordTrace_append hprefix tailTrace_2008373
  have hstable : (prefixWord ++ tailWord_2008373).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008373).length < 2 ^ (prefixWord ++ tailWord_2008373).sum := by decide
  have hdescent : baseEnd_2008373 < baseStart_2008373 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008384 : List Nat := [2, 1, 1, 2, 2, 1, 4, 1, 7]
def baseStart_2008384 : Nat := 118140960795 + 2008384 * 2 ^ 59
def prefixEnd_2008384 : Nat := 4983230072969 + 3 ^ 40 * 2008384 * 2
def baseEnd_2008384 : Nat := 458340591466477965361607

theorem tailTrace_2008384 : CollatzResearch.WordTrace tailWord_2008384 prefixEnd_2008384 458340591466477965361607 := by
  unfold tailWord_2008384
  simp only [CollatzResearch.WordTrace]
  refine ⟨36625891177987623762156103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48834521570650165016208137 36625891177987623762156103)
  ·
    refine ⟨54938836766981435643234155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36625891177987623762156103 54938836766981435643234155)
    ·
      refine ⟨82408255150472153464851233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54938836766981435643234155 82408255150472153464851233)
      ·
        refine ⟨61806191362854115098638425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82408255150472153464851233 61806191362854115098638425)
        ·
          refine ⟨46354643522140586323978819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61806191362854115098638425 46354643522140586323978819)
          ·
            refine ⟨69531965283210879485968229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46354643522140586323978819 69531965283210879485968229)
            ·
              refine ⟨13037243490602039903619043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69531965283210879485968229 13037243490602039903619043)
              ·
                refine ⟨19555865235903059855428565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13037243490602039903619043 19555865235903059855428565)
                ·
                  refine ⟨458340591466477965361607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19555865235903059855428565 458340591466477965361607)
                  ·
                    rfl

theorem cell21_2008384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 1, 7].length) (baseStart_2008384 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2008384 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2008384 prefixEnd_2008384 := by exact prefixLift 2008384
  have htrace : WordTrace (prefixWord ++ tailWord_2008384) baseStart_2008384 baseEnd_2008384 := by
    simpa [prefixWord, tailWord_2008384, baseEnd_2008384] using wordTrace_append hprefix tailTrace_2008384
  have hstable : (prefixWord ++ tailWord_2008384).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008384).length < 2 ^ (prefixWord ++ tailWord_2008384).sum := by decide
  have hdescent : baseEnd_2008384 < baseStart_2008384 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008460 : List Nat := [2, 2, 1, 2, 1, 3, 1, 2, 7]
def baseStart_2008460 : Nat := 118140960795 + 2008460 * 2 ^ 59
def prefixEnd_2008460 : Nat := 4983230072969 + 3 ^ 40 * 2008460 * 2
def baseEnd_2008460 : Nat := 458357935701918722094785

theorem tailTrace_2008460 : CollatzResearch.WordTrace tailWord_2008460 prefixEnd_2008460 458357935701918722094785 := by
  unfold tailWord_2008460
  simp only [CollatzResearch.WordTrace]
  refine ⟨36627277151849956252039417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48836369535799941669385889 36627277151849956252039417)
  ·
    refine ⟨27470457863887467189029563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36627277151849956252039417 27470457863887467189029563)
    ·
      refine ⟨41205686795831200783544345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27470457863887467189029563 41205686795831200783544345)
      ·
        refine ⟨30904265096873400587658259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41205686795831200783544345 30904265096873400587658259)
        ·
          refine ⟨46356397645310100881487389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30904265096873400587658259 46356397645310100881487389)
          ·
            refine ⟨17383649116991287830557771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46356397645310100881487389 17383649116991287830557771)
            ·
              refine ⟨26075473675486931745836657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17383649116991287830557771 26075473675486931745836657)
              ·
                refine ⟨19556605256615198809377493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26075473675486931745836657 19556605256615198809377493)
                ·
                  refine ⟨458357935701918722094785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19556605256615198809377493 458357935701918722094785)
                  ·
                    rfl

theorem cell21_2008460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 2, 7].length) (baseStart_2008460 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2008460 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2008460 prefixEnd_2008460 := by exact prefixLift 2008460
  have htrace : WordTrace (prefixWord ++ tailWord_2008460) baseStart_2008460 baseEnd_2008460 := by
    simpa [prefixWord, tailWord_2008460, baseEnd_2008460] using wordTrace_append hprefix tailTrace_2008460
  have hstable : (prefixWord ++ tailWord_2008460).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008460).length < 2 ^ (prefixWord ++ tailWord_2008460).sum := by decide
  have hdescent : baseEnd_2008460 < baseStart_2008460 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008477 : List Nat := [1, 4, 2, 1, 3, 1, 1, 3, 5]
def baseStart_2008477 : Nat := 118140960795 + 2008477 * 2 ^ 59
def prefixEnd_2008477 : Nat := 4983230072969 + 3 ^ 40 * 2008477 * 2
def baseEnd_2008477 : Nat := 458361815333530470311417

theorem tailTrace_2008477 : CollatzResearch.WordTrace tailWord_2008477 prefixEnd_2008477 458361815333530470311417 := by
  unfold tailWord_2008477
  simp only [CollatzResearch.WordTrace]
  refine ⟨73255174344638324407447685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48836782896425549604965123 73255174344638324407447685)
  ·
    refine ⟨13735345189619685826396441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73255174344638324407447685 13735345189619685826396441)
    ·
      refine ⟨10301508892214764369797331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13735345189619685826396441 10301508892214764369797331)
      ·
        refine ⟨15452263338322146554695997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10301508892214764369797331 15452263338322146554695997)
        ·
          refine ⟨5794598751870804958010999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15452263338322146554695997 5794598751870804958010999)
          ·
            refine ⟨8691898127806207437016499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5794598751870804958010999 8691898127806207437016499)
            ·
              refine ⟨13037847191709311155524749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8691898127806207437016499 13037847191709311155524749)
              ·
                refine ⟨4889192696890991683321781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13037847191709311155524749 4889192696890991683321781)
                ·
                  refine ⟨458361815333530470311417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4889192696890991683321781 458361815333530470311417)
                  ·
                    rfl

theorem cell21_2008477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 3, 5].length) (baseStart_2008477 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2008477 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2008477 prefixEnd_2008477 := by exact prefixLift 2008477
  have htrace : WordTrace (prefixWord ++ tailWord_2008477) baseStart_2008477 baseEnd_2008477 := by
    simpa [prefixWord, tailWord_2008477, baseEnd_2008477] using wordTrace_append hprefix tailTrace_2008477
  have hstable : (prefixWord ++ tailWord_2008477).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008477).length < 2 ^ (prefixWord ++ tailWord_2008477).sum := by decide
  have hdescent : baseEnd_2008477 < baseStart_2008477 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008514 : List Nat := [3, 5, 2, 1, 1, 2, 7]
def baseStart_2008514 : Nat := 118140960795 + 2008514 * 2 ^ 59
def prefixEnd_2008514 : Nat := 4983230072969 + 3 ^ 40 * 2008514 * 2
def baseEnd_2008514 : Nat := 50930028804180736466075

theorem tailTrace_2008514 : CollatzResearch.WordTrace tailWord_2008514 prefixEnd_2008514 50930028804180736466075 := by
  unfold tailWord_2008514
  simp only [CollatzResearch.WordTrace]
  refine ⟨18314130961376069931636149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48837682563669519817696397 18314130961376069931636149)
  ·
    refine ⟨1716949777629006556090889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18314130961376069931636149 1716949777629006556090889)
    ·
      refine ⟨1287712333221754917068167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1716949777629006556090889 1287712333221754917068167)
      ·
        refine ⟨1931568499832632375602251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1287712333221754917068167 1931568499832632375602251)
        ·
          refine ⟨2897352749748948563403377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1931568499832632375602251 2897352749748948563403377)
          ·
            refine ⟨2173014562311711422552533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2897352749748948563403377 2173014562311711422552533)
            ·
              refine ⟨50930028804180736466075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2173014562311711422552533 50930028804180736466075)
              ·
                rfl

theorem cell21_2008514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 7].length) (baseStart_2008514 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2008514 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2008514 prefixEnd_2008514 := by exact prefixLift 2008514
  have htrace : WordTrace (prefixWord ++ tailWord_2008514) baseStart_2008514 baseEnd_2008514 := by
    simpa [prefixWord, tailWord_2008514, baseEnd_2008514] using wordTrace_append hprefix tailTrace_2008514
  have hstable : (prefixWord ++ tailWord_2008514).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008514).length < 2 ^ (prefixWord ++ tailWord_2008514).sum := by decide
  have hdescent : baseEnd_2008514 < baseStart_2008514 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008522 : List Nat := [3, 1, 2, 1, 2, 5, 7]
def baseStart_2008522 : Nat := 118140960795 + 2008522 * 2 ^ 59
def prefixEnd_2008522 : Nat := 4983230072969 + 3 ^ 40 * 2008522 * 2
def baseEnd_2008522 : Nat := 50930231660735599117925

theorem tailTrace_2008522 : CollatzResearch.WordTrace tailWord_2008522 prefixEnd_2008522 50930231660735599117925 := by
  unfold tailWord_2008522
  simp only [CollatzResearch.WordTrace]
  refine ⟨18314203907368824273208955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48837877086316864728557213 18314203907368824273208955)
  ·
    refine ⟨27471305861053236409813433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18314203907368824273208955 27471305861053236409813433)
    ·
      refine ⟨20603479395789927307360075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27471305861053236409813433 20603479395789927307360075)
      ·
        refine ⟨30905219093684890961040113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20603479395789927307360075 30905219093684890961040113)
        ·
          refine ⟨23178914320263668220780085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30905219093684890961040113 23178914320263668220780085)
          ·
            refine ⟨2173023217524718895698133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23178914320263668220780085 2173023217524718895698133)
            ·
              refine ⟨50930231660735599117925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2173023217524718895698133 50930231660735599117925)
              ·
                rfl

theorem cell21_2008522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 7].length) (baseStart_2008522 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2008522 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2008522 prefixEnd_2008522 := by exact prefixLift 2008522
  have htrace : WordTrace (prefixWord ++ tailWord_2008522) baseStart_2008522 baseEnd_2008522 := by
    simpa [prefixWord, tailWord_2008522, baseEnd_2008522] using wordTrace_append hprefix tailTrace_2008522
  have hstable : (prefixWord ++ tailWord_2008522).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008522).length < 2 ^ (prefixWord ++ tailWord_2008522).sum := by decide
  have hdescent : baseEnd_2008522 < baseStart_2008522 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008657 : List Nat := [1, 2, 2, 1, 3, 2, 2, 8]
def baseStart_2008657 : Nat := 118140960795 + 2008657 * 2 ^ 59
def prefixEnd_2008657 : Nat := 4983230072969 + 3 ^ 40 * 2008657 * 2
def baseEnd_2008657 : Nat := 152800964595296719103683

theorem tailTrace_2008657 : CollatzResearch.WordTrace tailWord_2008657 prefixEnd_2008657 152800964595296719103683 := by
  unfold tailWord_2008657
  simp only [CollatzResearch.WordTrace]
  refine ⟨73261739483986215149000225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48841159655990810099333483 73261739483986215149000225)
  ·
    refine ⟨54946304612989661361750169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73261739483986215149000225 54946304612989661361750169)
    ·
      refine ⟨41209728459742246021312627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54946304612989661361750169 41209728459742246021312627)
      ·
        refine ⟨61814592689613369031968941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41209728459742246021312627 61814592689613369031968941)
        ·
          refine ⟨23180472258605013386988353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61814592689613369031968941 23180472258605013386988353)
          ·
            refine ⟨17385354193953760040241265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23180472258605013386988353 17385354193953760040241265)
            ·
              refine ⟨13039015645465320030180949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17385354193953760040241265 13039015645465320030180949)
              ·
                refine ⟨152800964595296719103683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13039015645465320030180949 152800964595296719103683)
                ·
                  rfl

theorem cell21_2008657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 8].length) (baseStart_2008657 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2008657 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2008657 prefixEnd_2008657 := by exact prefixLift 2008657
  have htrace : WordTrace (prefixWord ++ tailWord_2008657) baseStart_2008657 baseEnd_2008657 := by
    simpa [prefixWord, tailWord_2008657, baseEnd_2008657] using wordTrace_append hprefix tailTrace_2008657
  have hstable : (prefixWord ++ tailWord_2008657).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008657).length < 2 ^ (prefixWord ++ tailWord_2008657).sum := by decide
  have hdescent : baseEnd_2008657 < baseStart_2008657 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008705 : List Nat := [1, 2, 4, 2, 1, 2, 3, 1, 5]
def baseStart_2008705 : Nat := 118140960795 + 2008705 * 2 ^ 59
def prefixEnd_2008705 : Nat := 4983230072969 + 3 ^ 40 * 2008705 * 2
def baseEnd_2008705 : Nat := 458413848039852740510951

theorem tailTrace_2008705 : CollatzResearch.WordTrace tailWord_2008705 prefixEnd_2008705 458413848039852740510951 := by
  unfold tailWord_2008705
  simp only [CollatzResearch.WordTrace]
  refine ⟨73263490187812319346747569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48842326791874879564498379 73263490187812319346747569)
  ·
    refine ⟨54947617640859239510060677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73263490187812319346747569 54947617640859239510060677)
    ·
      refine ⟨10302678307661107408136377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54947617640859239510060677 10302678307661107408136377)
      ·
        refine ⟨7727008730745830556102283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10302678307661107408136377 7727008730745830556102283)
        ·
          refine ⟨11590513096118745834153425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7727008730745830556102283 11590513096118745834153425)
          ·
            refine ⟨8692884822089059375615069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11590513096118745834153425 8692884822089059375615069)
            ·
              refine ⟨3259831808283397265855651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8692884822089059375615069 3259831808283397265855651)
              ·
                refine ⟨4889747712425095898783477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3259831808283397265855651 4889747712425095898783477)
                ·
                  refine ⟨458413848039852740510951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4889747712425095898783477 458413848039852740510951)
                  ·
                    rfl

theorem cell21_2008705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 3, 1, 5].length) (baseStart_2008705 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2008705 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2008705 prefixEnd_2008705 := by exact prefixLift 2008705
  have htrace : WordTrace (prefixWord ++ tailWord_2008705) baseStart_2008705 baseEnd_2008705 := by
    simpa [prefixWord, tailWord_2008705, baseEnd_2008705] using wordTrace_append hprefix tailTrace_2008705
  have hstable : (prefixWord ++ tailWord_2008705).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008705).length < 2 ^ (prefixWord ++ tailWord_2008705).sum := by decide
  have hdescent : baseEnd_2008705 < baseStart_2008705 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008750 : List Nat := [4, 1, 4, 1, 11]
def baseStart_2008750 : Nat := 118140960795 + 2008750 * 2 ^ 59
def prefixEnd_2008750 : Nat := 4983230072969 + 3 ^ 40 * 2008750 * 2
def baseEnd_2008750 : Nat := 5659557008061020521739

theorem tailTrace_2008750 : CollatzResearch.WordTrace tailWord_2008750 prefixEnd_2008750 5659557008061020521739 := by
  unfold tailWord_2008750
  simp only [CollatzResearch.WordTrace]
  refine ⟨9158141434081161504016963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48843420981766194688090469 9158141434081161504016963)
  ·
    refine ⟨13737212151121742256025445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9158141434081161504016963 13737212151121742256025445)
    ·
      refine ⟨2575727278335326673004771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13737212151121742256025445 2575727278335326673004771)
      ·
        refine ⟨3863590917502990009507157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2575727278335326673004771 3863590917502990009507157)
        ·
          refine ⟨5659557008061020521739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 3863590917502990009507157 5659557008061020521739)
          ·
            rfl

theorem cell21_2008750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 11].length) (baseStart_2008750 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2008750 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2008750 prefixEnd_2008750 := by exact prefixLift 2008750
  have htrace : WordTrace (prefixWord ++ tailWord_2008750) baseStart_2008750 baseEnd_2008750 := by
    simpa [prefixWord, tailWord_2008750, baseEnd_2008750] using wordTrace_append hprefix tailTrace_2008750
  have hstable : (prefixWord ++ tailWord_2008750).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008750).length < 2 ^ (prefixWord ++ tailWord_2008750).sum := by decide
  have hdescent : baseEnd_2008750 < baseStart_2008750 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008840 : List Nat := [2, 1, 3, 2, 2, 1, 1, 4, 5]
def baseStart_2008840 : Nat := 118140960795 + 2008840 * 2 ^ 59
def prefixEnd_2008840 : Nat := 4983230072969 + 3 ^ 40 * 2008840 * 2
def baseEnd_2008840 : Nat := 458444656879122505760675

theorem tailTrace_2008840 : CollatzResearch.WordTrace tailWord_2008840 prefixEnd_2008840 458444656879122505760675 := by
  unfold tailWord_2008840
  simp only [CollatzResearch.WordTrace]
  refine ⟨36634207021161618701455987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48845609361548824935274649 36634207021161618701455987)
  ·
    refine ⟨54951310531742428052183981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36634207021161618701455987 54951310531742428052183981)
    ·
      refine ⟨20606741449403410519568993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54951310531742428052183981 20606741449403410519568993)
      ·
        refine ⟨15455056087052557889676745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20606741449403410519568993 15455056087052557889676745)
        ·
          refine ⟨11591292065289418417257559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15455056087052557889676745 11591292065289418417257559)
          ·
            refine ⟨17386938097934127625886339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11591292065289418417257559 17386938097934127625886339)
            ·
              refine ⟨26080407146901191438829509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17386938097934127625886339 26080407146901191438829509)
              ·
                refine ⟨4890076340043973394780533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26080407146901191438829509 4890076340043973394780533)
                ·
                  refine ⟨458444656879122505760675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4890076340043973394780533 458444656879122505760675)
                  ·
                    rfl

theorem cell21_2008840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 4, 5].length) (baseStart_2008840 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2008840 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2008840 prefixEnd_2008840 := by exact prefixLift 2008840
  have htrace : WordTrace (prefixWord ++ tailWord_2008840) baseStart_2008840 baseEnd_2008840 := by
    simpa [prefixWord, tailWord_2008840, baseEnd_2008840] using wordTrace_append hprefix tailTrace_2008840
  have hstable : (prefixWord ++ tailWord_2008840).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008840).length < 2 ^ (prefixWord ++ tailWord_2008840).sum := by decide
  have hdescent : baseEnd_2008840 < baseStart_2008840 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008888 : List Nat := [2, 1, 2, 1, 3, 3, 4, 1, 4]
def baseStart_2008888 : Nat := 118140960795 + 2008888 * 2 ^ 59
def prefixEnd_2008888 : Nat := 4983230072969 + 3 ^ 40 * 2008888 * 2
def baseEnd_2008888 : Nat := 458455611133085088960577

theorem tailTrace_2008888 : CollatzResearch.WordTrace tailWord_2008888 prefixEnd_2008888 458455611133085088960577 := by
  unfold tailWord_2008888
  simp only [CollatzResearch.WordTrace]
  refine ⟨36635082373074670800329659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48846776497432894400439545 36635082373074670800329659)
  ·
    refine ⟨54952623559612006200494489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36635082373074670800329659 54952623559612006200494489)
    ·
      refine ⟨41214467669709004650370867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54952623559612006200494489 41214467669709004650370867)
      ·
        refine ⟨61821701504563506975556301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41214467669709004650370867 61821701504563506975556301)
        ·
          refine ⟨23183138064211315115833613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61821701504563506975556301 23183138064211315115833613)
          ·
            refine ⟨8693676774079243168437605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23183138064211315115833613 8693676774079243168437605)
            ·
              refine ⟨1630064395139858094082051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8693676774079243168437605 1630064395139858094082051)
              ·
                refine ⟨2445096592709787141123077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1630064395139858094082051 2445096592709787141123077)
                ·
                  refine ⟨458455611133085088960577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2445096592709787141123077 458455611133085088960577)
                  ·
                    rfl

theorem cell21_2008888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 4, 1, 4].length) (baseStart_2008888 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2008888 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2008888 prefixEnd_2008888 := by exact prefixLift 2008888
  have htrace : WordTrace (prefixWord ++ tailWord_2008888) baseStart_2008888 baseEnd_2008888 := by
    simpa [prefixWord, tailWord_2008888, baseEnd_2008888] using wordTrace_append hprefix tailTrace_2008888
  have hstable : (prefixWord ++ tailWord_2008888).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008888).length < 2 ^ (prefixWord ++ tailWord_2008888).sum := by decide
  have hdescent : baseEnd_2008888 < baseStart_2008888 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008950 : List Nat := [5, 1, 1, 3, 2, 1, 1, 2, 5]
def baseStart_2008950 : Nat := 118140960795 + 2008950 * 2 ^ 59
def prefixEnd_2008950 : Nat := 4983230072969 + 3 ^ 40 * 2008950 * 2
def baseEnd_2008950 : Nat := 458469760377786758927117

theorem tailTrace_2008950 : CollatzResearch.WordTrace tailWord_2008950 prefixEnd_2008950 458469760377786758927117 := by
  unfold tailWord_2008950
  simp only [CollatzResearch.WordTrace]
  refine ⟨4579526629495295386838519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48848284047949817459610869 4579526629495295386838519)
  ·
    refine ⟨6869289944242943080257779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4579526629495295386838519 6869289944242943080257779)
    ·
      refine ⟨10303934916364414620386669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6869289944242943080257779 10303934916364414620386669)
      ·
        refine ⟨3863975593636655482645001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10303934916364414620386669 3863975593636655482645001)
        ·
          refine ⟨2897981695227491611983751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3863975593636655482645001 2897981695227491611983751)
          ·
            refine ⟨4346972542841237417975627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2897981695227491611983751 4346972542841237417975627)
            ·
              refine ⟨6520458814261856126963441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4346972542841237417975627 6520458814261856126963441)
              ·
                refine ⟨4890344110696392095222581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6520458814261856126963441 4890344110696392095222581)
                ·
                  refine ⟨458469760377786758927117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4890344110696392095222581 458469760377786758927117)
                  ·
                    rfl

theorem cell21_2008950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 2, 5].length) (baseStart_2008950 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2008950 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2008950 prefixEnd_2008950 := by exact prefixLift 2008950
  have htrace : WordTrace (prefixWord ++ tailWord_2008950) baseStart_2008950 baseEnd_2008950 := by
    simpa [prefixWord, tailWord_2008950, baseEnd_2008950] using wordTrace_append hprefix tailTrace_2008950
  have hstable : (prefixWord ++ tailWord_2008950).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008950).length < 2 ^ (prefixWord ++ tailWord_2008950).sum := by decide
  have hdescent : baseEnd_2008950 < baseStart_2008950 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008978 : List Nat := [3, 2, 3, 2, 1, 2, 8]
def baseStart_2008978 : Nat := 118140960795 + 2008978 * 2 ^ 59
def prefixEnd_2008978 : Nat := 4983230072969 + 3 ^ 40 * 2008978 * 2
def baseEnd_2008978 : Nat := 50941794484362770273377

theorem tailTrace_2008978 : CollatzResearch.WordTrace tailWord_2008978 prefixEnd_2008978 50941794484362770273377 := by
  unfold tailWord_2008978
  simp only [CollatzResearch.WordTrace]
  refine ⟨18318361828955821742858897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48848964877215524647623725 18318361828955821742858897)
  ·
    refine ⟨13738771371716866307144173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18318361828955821742858897 13738771371716866307144173)
    ·
      refine ⟨5152039264393824865179065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13738771371716866307144173 5152039264393824865179065)
      ·
        refine ⟨3864029448295368648884299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5152039264393824865179065 3864029448295368648884299)
        ·
          refine ⟨5796044172443052973326449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3864029448295368648884299 5796044172443052973326449)
          ·
            refine ⟨4347033129332289729994837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5796044172443052973326449 4347033129332289729994837)
            ·
              refine ⟨50941794484362770273377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4347033129332289729994837 50941794484362770273377)
              ·
                rfl

theorem cell21_2008978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 8].length) (baseStart_2008978 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2008978 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2008978 prefixEnd_2008978 := by exact prefixLift 2008978
  have htrace : WordTrace (prefixWord ++ tailWord_2008978) baseStart_2008978 baseEnd_2008978 := by
    simpa [prefixWord, tailWord_2008978, baseEnd_2008978] using wordTrace_append hprefix tailTrace_2008978
  have hstable : (prefixWord ++ tailWord_2008978).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008978).length < 2 ^ (prefixWord ++ tailWord_2008978).sum := by decide
  have hdescent : baseEnd_2008978 < baseStart_2008978 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009099 : List Nat := [1, 1, 1, 1, 6, 1, 4, 2, 4]
def baseStart_2009099 : Nat := 118140960795 + 2009099 * 2 ^ 59
def prefixEnd_2009099 : Nat := 4983230072969 + 3 ^ 40 * 2009099 * 2
def baseEnd_2009099 : Nat := 458503764207795610943479

theorem tailTrace_2009099 : CollatzResearch.WordTrace tailWord_2009099 prefixEnd_2009099 458503764207795610943479 := by
  unfold tailWord_2009099
  simp only [CollatzResearch.WordTrace]
  refine ⟨73277860548384924636590351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48851907032256616424393567 73277860548384924636590351)
  ·
    refine ⟨109916790822577386954885527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73277860548384924636590351 109916790822577386954885527)
    ·
      refine ⟨164875186233866080432328291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109916790822577386954885527 164875186233866080432328291)
      ·
        refine ⟨247312779350799120648492437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164875186233866080432328291 247312779350799120648492437)
        ·
          refine ⟨11592786532068708780398083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 247312779350799120648492437 11592786532068708780398083)
          ·
            refine ⟨17389179798103063170597125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11592786532068708780398083 17389179798103063170597125)
            ·
              refine ⟨3260471212144324344486961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17389179798103063170597125 3260471212144324344486961)
              ·
                refine ⟨2445353409108243258365221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3260471212144324344486961 2445353409108243258365221)
                ·
                  refine ⟨458503764207795610943479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2445353409108243258365221 458503764207795610943479)
                  ·
                    rfl

theorem cell21_2009099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 4, 2, 4].length) (baseStart_2009099 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2009099 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2009099 prefixEnd_2009099 := by exact prefixLift 2009099
  have htrace : WordTrace (prefixWord ++ tailWord_2009099) baseStart_2009099 baseEnd_2009099 := by
    simpa [prefixWord, tailWord_2009099, baseEnd_2009099] using wordTrace_append hprefix tailTrace_2009099
  have hstable : (prefixWord ++ tailWord_2009099).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009099).length < 2 ^ (prefixWord ++ tailWord_2009099).sum := by decide
  have hdescent : baseEnd_2009099 < baseStart_2009099 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009150 : List Nat := [4, 2, 1, 3, 3, 1, 1, 2, 4]
def baseStart_2009150 : Nat := 118140960795 + 2009150 * 2 ^ 59
def prefixEnd_2009150 : Nat := 4983230072969 + 3 ^ 40 * 2009150 * 2
def baseEnd_2009150 : Nat := 458515403102630855593375

theorem tailTrace_2009150 : CollatzResearch.WordTrace tailWord_2009150 prefixEnd_2009150 458515403102630855593375 := by
  unfold tailWord_2009150
  simp only [CollatzResearch.WordTrace]
  refine ⟨9159965083900020043337113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48853147114133440231131269 9159965083900020043337113)
  ·
    refine ⟨6869973812925015032502835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9159965083900020043337113 6869973812925015032502835)
    ·
      refine ⟨10304960719387522548754253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6869973812925015032502835 10304960719387522548754253)
      ·
        refine ⟨3864360269770320955782845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10304960719387522548754253 3864360269770320955782845)
        ·
          refine ⟨1449135101163870358418567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3864360269770320955782845 1449135101163870358418567)
          ·
            refine ⟨2173702651745805537627851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1449135101163870358418567 2173702651745805537627851)
            ·
              refine ⟨3260553977618708306441777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2173702651745805537627851 3260553977618708306441777)
              ·
                refine ⟨2445415483214031229831333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3260553977618708306441777 2445415483214031229831333)
                ·
                  refine ⟨458515403102630855593375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2445415483214031229831333 458515403102630855593375)
                  ·
                    rfl

theorem cell21_2009150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 1, 2, 4].length) (baseStart_2009150 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2009150 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2009150 prefixEnd_2009150 := by exact prefixLift 2009150
  have htrace : WordTrace (prefixWord ++ tailWord_2009150) baseStart_2009150 baseEnd_2009150 := by
    simpa [prefixWord, tailWord_2009150, baseEnd_2009150] using wordTrace_append hprefix tailTrace_2009150
  have hstable : (prefixWord ++ tailWord_2009150).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009150).length < 2 ^ (prefixWord ++ tailWord_2009150).sum := by decide
  have hdescent : baseEnd_2009150 < baseStart_2009150 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009189 : List Nat := [1, 3, 1, 3, 2, 3, 1, 7]
def baseStart_2009189 : Nat := 118140960795 + 2009189 * 2 ^ 59
def prefixEnd_2009189 : Nat := 4983230072969 + 3 ^ 40 * 2009189 * 2
def baseEnd_2009189 : Nat := 152841434477991818147765

theorem tailTrace_2009189 : CollatzResearch.WordTrace tailWord_2009189 prefixEnd_2009189 152841434477991818147765 := by
  unfold tailWord_2009189
  simp only [CollatzResearch.WordTrace]
  refine ⟨73281143118058870007366621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48854095412039246671577747 73281143118058870007366621)
  ·
    refine ⟨27480428669272076252762483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73281143118058870007366621 27480428669272076252762483)
    ·
      refine ⟨41220643003908114379143725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27480428669272076252762483 41220643003908114379143725)
      ·
        refine ⟨15457741126465542892178897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41220643003908114379143725 15457741126465542892178897)
        ·
          refine ⟨11593305844849157169134173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15457741126465542892178897 11593305844849157169134173)
          ·
            refine ⟨4347489691818433938425315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11593305844849157169134173 4347489691818433938425315)
            ·
              refine ⟨6521234537727650907637973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4347489691818433938425315 6521234537727650907637973)
              ·
                refine ⟨152841434477991818147765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6521234537727650907637973 152841434477991818147765)
                ·
                  rfl

theorem cell21_2009189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 7].length) (baseStart_2009189 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2009189 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2009189 prefixEnd_2009189 := by exact prefixLift 2009189
  have htrace : WordTrace (prefixWord ++ tailWord_2009189) baseStart_2009189 baseEnd_2009189 := by
    simpa [prefixWord, tailWord_2009189, baseEnd_2009189] using wordTrace_append hprefix tailTrace_2009189
  have hstable : (prefixWord ++ tailWord_2009189).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009189).length < 2 ^ (prefixWord ++ tailWord_2009189).sum := by decide
  have hdescent : baseEnd_2009189 < baseStart_2009189 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009206 : List Nat := [5, 1, 1, 2, 1, 4, 7]
def baseStart_2009206 : Nat := 118140960795 + 2009206 * 2 ^ 59
def prefixEnd_2009206 : Nat := 4983230072969 + 3 ^ 40 * 2009206 * 2
def baseEnd_2009206 : Nat := 50947575896176355851103

theorem tailTrace_2009206 : CollatzResearch.WordTrace tailWord_2009206 prefixEnd_2009206 50947575896176355851103 := by
  unfold tailWord_2009206
  simp only [CollatzResearch.WordTrace]
  refine ⟨4580110197437330119420967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48854508772664854607156981 4580110197437330119420967)
  ·
    refine ⟨6870165296155995179131451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4580110197437330119420967 6870165296155995179131451)
    ·
      refine ⟨10305247944233992768697177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6870165296155995179131451 10305247944233992768697177)
      ·
        refine ⟨7728935958175494576522883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10305247944233992768697177 7728935958175494576522883)
        ·
          refine ⟨11593403937263241864784325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7728935958175494576522883 11593403937263241864784325)
          ·
            refine ⟨2173763238236857849647061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11593403937263241864784325 2173763238236857849647061)
            ·
              refine ⟨50947575896176355851103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2173763238236857849647061 50947575896176355851103)
              ·
                rfl

theorem cell21_2009206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 7].length) (baseStart_2009206 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2009206 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2009206 prefixEnd_2009206 := by exact prefixLift 2009206
  have htrace : WordTrace (prefixWord ++ tailWord_2009206) baseStart_2009206 baseEnd_2009206 := by
    simpa [prefixWord, tailWord_2009206, baseEnd_2009206] using wordTrace_append hprefix tailTrace_2009206
  have hstable : (prefixWord ++ tailWord_2009206).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009206).length < 2 ^ (prefixWord ++ tailWord_2009206).sum := by decide
  have hdescent : baseEnd_2009206 < baseStart_2009206 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009265 : List Nat := [1, 2, 2, 5, 2, 9]
def baseStart_2009265 : Nat := 118140960795 + 2009265 * 2 ^ 59
def prefixEnd_2009265 : Nat := 4983230072969 + 3 ^ 40 * 2009265 * 2
def baseEnd_2009265 : Nat := 16983023987756155969499

theorem tailTrace_2009265 : CollatzResearch.WordTrace tailWord_2009265 prefixEnd_2009265 16983023987756155969499 := by
  unfold tailWord_2009265
  simp only [CollatzResearch.WordTrace]
  refine ⟨73283915065783534987133249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48855943377189023324755499 73283915065783534987133249)
  ·
    refine ⟨54962936299337651240349937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73283915065783534987133249 54962936299337651240349937)
    ·
      refine ⟨41222202224503238430262453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54962936299337651240349937 41222202224503238430262453)
      ·
        refine ⟨3864581458547178602837105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41222202224503238430262453 3864581458547178602837105)
        ·
          refine ⟨2898436093910383952127829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3864581458547178602837105 2898436093910383952127829)
          ·
            refine ⟨16983023987756155969499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2898436093910383952127829 16983023987756155969499)
            ·
              rfl

theorem cell21_2009265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 9].length) (baseStart_2009265 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2009265 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2009265 prefixEnd_2009265 := by exact prefixLift 2009265
  have htrace : WordTrace (prefixWord ++ tailWord_2009265) baseStart_2009265 baseEnd_2009265 := by
    simpa [prefixWord, tailWord_2009265, baseEnd_2009265] using wordTrace_append hprefix tailTrace_2009265
  have hstable : (prefixWord ++ tailWord_2009265).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009265).length < 2 ^ (prefixWord ++ tailWord_2009265).sum := by decide
  have hdescent : baseEnd_2009265 < baseStart_2009265 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009279 : List Nat := [1, 1, 2, 2, 2, 2, 1, 5, 5]
def baseStart_2009279 : Nat := 118140960795 + 2009279 * 2 ^ 59
def prefixEnd_2009279 : Nat := 4983230072969 + 3 ^ 40 * 2009279 * 2
def baseEnd_2009279 : Nat := 458544842660155297943111

theorem tailTrace_2009279 : CollatzResearch.WordTrace tailWord_2009279 prefixEnd_2009279 458544842660155297943111 := by
  unfold tailWord_2009279
  simp only [CollatzResearch.WordTrace]
  refine ⟨73284425687732815378142891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48856283791821876918761927 73284425687732815378142891)
  ·
    refine ⟨109926638531599223067214337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73284425687732815378142891 109926638531599223067214337)
    ·
      refine ⟨82444978898699417300410753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109926638531599223067214337 82444978898699417300410753)
      ·
        refine ⟨61833734174024562975308065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82444978898699417300410753 61833734174024562975308065)
        ·
          refine ⟨46375300630518422231481049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61833734174024562975308065 46375300630518422231481049)
          ·
            refine ⟨34781475472888816673610787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46375300630518422231481049 34781475472888816673610787)
            ·
              refine ⟨52172213209333225010416181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34781475472888816673610787 52172213209333225010416181)
              ·
                refine ⟨4891144988374989844726517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52172213209333225010416181 4891144988374989844726517)
                ·
                  refine ⟨458544842660155297943111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4891144988374989844726517 458544842660155297943111)
                  ·
                    rfl

theorem cell21_2009279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 5, 5].length) (baseStart_2009279 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2009279 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2009279 prefixEnd_2009279 := by exact prefixLift 2009279
  have htrace : WordTrace (prefixWord ++ tailWord_2009279) baseStart_2009279 baseEnd_2009279 := by
    simpa [prefixWord, tailWord_2009279, baseEnd_2009279] using wordTrace_append hprefix tailTrace_2009279
  have hstable : (prefixWord ++ tailWord_2009279).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009279).length < 2 ^ (prefixWord ++ tailWord_2009279).sum := by decide
  have hdescent : baseEnd_2009279 < baseStart_2009279 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009313 : List Nat := [1, 2, 3, 1, 3, 1, 4, 3, 3]
def baseStart_2009313 : Nat := 118140960795 + 2009313 * 2 ^ 59
def prefixEnd_2009313 : Nat := 4983230072969 + 3 ^ 40 * 2009313 * 2
def baseEnd_2009313 : Nat := 458552601923378794376375

theorem tailTrace_2009313 : CollatzResearch.WordTrace tailWord_2009313 prefixEnd_2009313 458552601923378794376375 := by
  unfold tailWord_2009313
  simp only [CollatzResearch.WordTrace]
  refine ⟨73285665769609639184880593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48857110513073092789920395 73285665769609639184880593)
  ·
    refine ⟨54964249327207229388660445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73285665769609639184880593 54964249327207229388660445)
    ·
      refine ⟨20611593497702711020747667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54964249327207229388660445 20611593497702711020747667)
      ·
        refine ⟨30917390246554066531121501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20611593497702711020747667 30917390246554066531121501)
        ·
          refine ⟨11594021342457774949170563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30917390246554066531121501 11594021342457774949170563)
          ·
            refine ⟨17391032013686662423755845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11594021342457774949170563 17391032013686662423755845)
            ·
              refine ⟨3260818502566249204454221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17391032013686662423755845 3260818502566249204454221)
              ·
                refine ⟨1222806938462343451670333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3260818502566249204454221 1222806938462343451670333)
                ·
                  refine ⟨458552601923378794376375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1222806938462343451670333 458552601923378794376375)
                  ·
                    rfl

theorem cell21_2009313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 4, 3, 3].length) (baseStart_2009313 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2009313 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2009313 prefixEnd_2009313 := by exact prefixLift 2009313
  have htrace : WordTrace (prefixWord ++ tailWord_2009313) baseStart_2009313 baseEnd_2009313 := by
    simpa [prefixWord, tailWord_2009313, baseEnd_2009313] using wordTrace_append hprefix tailTrace_2009313
  have hstable : (prefixWord ++ tailWord_2009313).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009313).length < 2 ^ (prefixWord ++ tailWord_2009313).sum := by decide
  have hdescent : baseEnd_2009313 < baseStart_2009313 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009324 : List Nat := [2, 2, 1, 1, 2, 3, 10]
def baseStart_2009324 : Nat := 118140960795 + 2009324 * 2 ^ 59
def prefixEnd_2009324 : Nat := 4983230072969 + 3 ^ 40 * 2009324 * 2
def baseEnd_2009324 : Nat := 50950568030360579965891

theorem tailTrace_2009324 : CollatzResearch.WordTrace tailWord_2009324 prefixEnd_2009324 50950568030360579965891 := by
  unfold tailWord_2009324
  simp only [CollatzResearch.WordTrace]
  refine ⟨36643033486284894031765513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48857377981713192042354017 36643033486284894031765513)
  ·
    refine ⟨27482275114713670523824135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36643033486284894031765513 27482275114713670523824135)
    ·
      refine ⟨41223412672070505785736203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27482275114713670523824135 41223412672070505785736203)
      ·
        refine ⟨61835119008105758678604305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41223412672070505785736203 61835119008105758678604305)
        ·
          refine ⟨46376339256079319008953229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61835119008105758678604305 46376339256079319008953229)
          ·
            refine ⟨17391127221029744628357461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46376339256079319008953229 17391127221029744628357461)
            ·
              refine ⟨50950568030360579965891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17391127221029744628357461 50950568030360579965891)
              ·
                rfl

theorem cell21_2009324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 10].length) (baseStart_2009324 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2009324 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2009324 prefixEnd_2009324 := by exact prefixLift 2009324
  have htrace : WordTrace (prefixWord ++ tailWord_2009324) baseStart_2009324 baseEnd_2009324 := by
    simpa [prefixWord, tailWord_2009324, baseEnd_2009324] using wordTrace_append hprefix tailTrace_2009324
  have hstable : (prefixWord ++ tailWord_2009324).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009324).length < 2 ^ (prefixWord ++ tailWord_2009324).sum := by decide
  have hdescent : baseEnd_2009324 < baseStart_2009324 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009327 : List Nat := [1, 1, 2, 1, 6, 1, 3, 2, 4]
def baseStart_2009327 : Nat := 118140960795 + 2009327 * 2 ^ 59
def prefixEnd_2009327 : Nat := 4983230072969 + 3 ^ 40 * 2009327 * 2
def baseEnd_2009327 : Nat := 458555796914117881143013

theorem tailTrace_2009327 : CollatzResearch.WordTrace tailWord_2009327 prefixEnd_2009327 458555796914117881143013 := by
  unfold tailWord_2009327
  simp only [CollatzResearch.WordTrace]
  refine ⟨73286176391558919575890235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48857450927705946383926823 73286176391558919575890235)
  ·
    refine ⟨109929264587338379363835353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73286176391558919575890235 109929264587338379363835353)
    ·
      refine ⟨82446948440503784522876515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109929264587338379363835353 82446948440503784522876515)
      ·
        refine ⟨123670422660755676784314773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82446948440503784522876515 123670422660755676784314773)
        ·
          refine ⟨5797051062222922349264755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 123670422660755676784314773 5797051062222922349264755)
          ·
            refine ⟨8695576593334383523897133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5797051062222922349264755 8695576593334383523897133)
            ·
              refine ⟨3260841222500393821461425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8695576593334383523897133 3260841222500393821461425)
              ·
                refine ⟨2445630916875295366096069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3260841222500393821461425 2445630916875295366096069)
                ·
                  refine ⟨458555796914117881143013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2445630916875295366096069 458555796914117881143013)
                  ·
                    rfl

theorem cell21_2009327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 3, 2, 4].length) (baseStart_2009327 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2009327 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2009327 prefixEnd_2009327 := by exact prefixLift 2009327
  have htrace : WordTrace (prefixWord ++ tailWord_2009327) baseStart_2009327 baseEnd_2009327 := by
    simpa [prefixWord, tailWord_2009327, baseEnd_2009327] using wordTrace_append hprefix tailTrace_2009327
  have hstable : (prefixWord ++ tailWord_2009327).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009327).length < 2 ^ (prefixWord ++ tailWord_2009327).sum := by decide
  have hdescent : baseEnd_2009327 < baseStart_2009327 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009355 : List Nat := [1, 1, 1, 1, 5, 2, 1, 4, 5]
def baseStart_2009355 : Nat := 118140960795 + 2009355 * 2 ^ 59
def prefixEnd_2009355 : Nat := 4983230072969 + 3 ^ 40 * 2009355 * 2
def baseEnd_2009355 : Nat := 458562186895596054676289

theorem tailTrace_2009355 : CollatzResearch.WordTrace tailWord_2009355 prefixEnd_2009355 458562186895596054676289 := by
  unfold tailWord_2009355
  simp only [CollatzResearch.WordTrace]
  refine ⟨73287197635457480357909519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48858131756971653571939679 73287197635457480357909519)
  ·
    refine ⟨109930796453186220536864279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73287197635457480357909519 109930796453186220536864279)
    ·
      refine ⟨164896194679779330805296419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109930796453186220536864279 164896194679779330805296419)
      ·
        refine ⟨247344292019668996207944629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164896194679779330805296419 247344292019668996207944629)
        ·
          refine ⟨23188527376843968394494809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 247344292019668996207944629 23188527376843968394494809)
          ·
            refine ⟨17391395532632976295871107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23188527376843968394494809 17391395532632976295871107)
            ·
              refine ⟨26087093298949464443806661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17391395532632976295871107 26087093298949464443806661)
              ·
                refine ⟨4891329993553024583213749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26087093298949464443806661 4891329993553024583213749)
                ·
                  refine ⟨458562186895596054676289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4891329993553024583213749 458562186895596054676289)
                  ·
                    rfl

theorem cell21_2009355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 4, 5].length) (baseStart_2009355 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2009355 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2009355 prefixEnd_2009355 := by exact prefixLift 2009355
  have htrace : WordTrace (prefixWord ++ tailWord_2009355) baseStart_2009355 baseEnd_2009355 := by
    simpa [prefixWord, tailWord_2009355, baseEnd_2009355] using wordTrace_append hprefix tailTrace_2009355
  have hstable : (prefixWord ++ tailWord_2009355).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009355).length < 2 ^ (prefixWord ++ tailWord_2009355).sum := by decide
  have hdescent : baseEnd_2009355 < baseStart_2009355 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009400 : List Nat := [2, 1, 2, 1, 3, 1, 3, 8]
def baseStart_2009400 : Nat := 118140960795 + 2009400 * 2 ^ 59
def prefixEnd_2009400 : Nat := 4983230072969 + 3 ^ 40 * 2009400 * 2
def baseEnd_2009400 : Nat := 152857485502895325475399

theorem tailTrace_2009400 : CollatzResearch.WordTrace tailWord_2009400 prefixEnd_2009400 152857485502895325475399 := by
  unfold tailWord_2009400
  simp only [CollatzResearch.WordTrace]
  refine ⟨36644419460147226521648827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48859225946862968695531769 36644419460147226521648827)
  ·
    refine ⟨54966629190220839782473241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36644419460147226521648827 54966629190220839782473241)
    ·
      refine ⟨41224971892665629836854931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54966629190220839782473241 41224971892665629836854931)
      ·
        refine ⟨61837457838998444755282397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41224971892665629836854931 61837457838998444755282397)
        ·
          refine ⟨23189046689624416783230899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61837457838998444755282397 23189046689624416783230899)
          ·
            refine ⟨34783570034436625174846349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23189046689624416783230899 34783570034436625174846349)
            ·
              refine ⟨13043838762913734440567381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34783570034436625174846349 13043838762913734440567381)
              ·
                refine ⟨152857485502895325475399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13043838762913734440567381 152857485502895325475399)
                ·
                  rfl

theorem cell21_2009400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 8].length) (baseStart_2009400 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2009400 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2009400 prefixEnd_2009400 := by exact prefixLift 2009400
  have htrace : WordTrace (prefixWord ++ tailWord_2009400) baseStart_2009400 baseEnd_2009400 := by
    simpa [prefixWord, tailWord_2009400, baseEnd_2009400] using wordTrace_append hprefix tailTrace_2009400
  have hstable : (prefixWord ++ tailWord_2009400).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009400).length < 2 ^ (prefixWord ++ tailWord_2009400).sum := by decide
  have hdescent : baseEnd_2009400 < baseStart_2009400 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009496 : List Nat := [2, 1, 2, 5, 1, 3, 1, 2, 4]
def baseStart_2009496 : Nat := 118140960795 + 2009496 * 2 ^ 59
def prefixEnd_2009496 : Nat := 4983230072969 + 3 ^ 40 * 2009496 * 2
def baseEnd_2009496 : Nat := 458594365016611142826001

theorem tailTrace_2009496 : CollatzResearch.WordTrace tailWord_2009496 prefixEnd_2009496 458594365016611142826001 := by
  unfold tailWord_2009496
  simp only [CollatzResearch.WordTrace]
  refine ⟨36646170163973330719396171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48861560218631107625861561 36646170163973330719396171)
  ·
    refine ⟨54969255245959996079094257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36646170163973330719396171 54969255245959996079094257)
    ·
      refine ⟨41226941434469997059320693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54969255245959996079094257 41226941434469997059320693)
      ·
        refine ⟨3865025759481562224311315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41226941434469997059320693 3865025759481562224311315)
        ·
          refine ⟨5797538639222343336466973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3865025759481562224311315 5797538639222343336466973)
          ·
            refine ⟨2174076989708378751175115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5797538639222343336466973 2174076989708378751175115)
            ·
              refine ⟨3261115484562568126762673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2174076989708378751175115 3261115484562568126762673)
              ·
                refine ⟨2445836613421926095072005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3261115484562568126762673 2445836613421926095072005)
                ·
                  refine ⟨458594365016611142826001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2445836613421926095072005 458594365016611142826001)
                  ·
                    rfl

theorem cell21_2009496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 1, 2, 4].length) (baseStart_2009496 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2009496 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2009496 prefixEnd_2009496 := by exact prefixLift 2009496
  have htrace : WordTrace (prefixWord ++ tailWord_2009496) baseStart_2009496 baseEnd_2009496 := by
    simpa [prefixWord, tailWord_2009496, baseEnd_2009496] using wordTrace_append hprefix tailTrace_2009496
  have hstable : (prefixWord ++ tailWord_2009496).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009496).length < 2 ^ (prefixWord ++ tailWord_2009496).sum := by decide
  have hdescent : baseEnd_2009496 < baseStart_2009496 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009507 : List Nat := [1, 1, 1, 4, 1, 4, 1, 3, 5]
def baseStart_2009507 : Nat := 118140960795 + 2009507 * 2 ^ 59
def prefixEnd_2009507 : Nat := 4983230072969 + 3 ^ 40 * 2009507 * 2
def baseEnd_2009507 : Nat := 458596875366477568142645

theorem tailTrace_2009507 : CollatzResearch.WordTrace tailWord_2009507 prefixEnd_2009507 458596875366477568142645 := by
  unfold tailWord_2009507
  simp only [CollatzResearch.WordTrace]
  refine ⟨73292741530906810317442775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48861827687271206878295183 73292741530906810317442775)
  ·
    refine ⟨109939112296360215476164163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73292741530906810317442775 109939112296360215476164163)
    ·
      refine ⟨164908668444540323214246245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109939112296360215476164163 164908668444540323214246245)
      ·
        refine ⟨30920375333351310602671171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 164908668444540323214246245 30920375333351310602671171)
        ·
          refine ⟨46380563000026965904006757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30920375333351310602671171 46380563000026965904006757)
          ·
            refine ⟨8696355562505056107001267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46380563000026965904006757 8696355562505056107001267)
            ·
              refine ⟨13044533343757584160501901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8696355562505056107001267 13044533343757584160501901)
              ·
                refine ⟨4891700003909094060188213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13044533343757584160501901 4891700003909094060188213)
                ·
                  refine ⟨458596875366477568142645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4891700003909094060188213 458596875366477568142645)
                  ·
                    rfl

theorem cell21_2009507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 3, 5].length) (baseStart_2009507 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2009507 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2009507 prefixEnd_2009507 := by exact prefixLift 2009507
  have htrace : WordTrace (prefixWord ++ tailWord_2009507) baseStart_2009507 baseEnd_2009507 := by
    simpa [prefixWord, tailWord_2009507, baseEnd_2009507] using wordTrace_append hprefix tailTrace_2009507
  have hstable : (prefixWord ++ tailWord_2009507).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009507).length < 2 ^ (prefixWord ++ tailWord_2009507).sum := by decide
  have hdescent : baseEnd_2009507 < baseStart_2009507 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009606 : List Nat := [6, 2, 1, 1, 1, 2, 2, 2, 4]
def baseStart_2009606 : Nat := 118140960795 + 2009606 * 2 ^ 59
def prefixEnd_2009606 : Nat := 4983230072969 + 3 ^ 40 * 2009606 * 2
def baseEnd_2009606 : Nat := 458619468515275395992443

theorem tailTrace_2009606 : CollatzResearch.WordTrace tailWord_2009606 prefixEnd_2009606 458619468515275395992443 := by
  unfold tailWord_2009606
  simp only [CollatzResearch.WordTrace]
  refine ⟨2290511011173379694540521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 48864234905032100150197781 2290511011173379694540521)
  ·
    refine ⟨1717883258380034770905391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2290511011173379694540521 1717883258380034770905391)
    ·
      refine ⟨2576824887570052156358087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1717883258380034770905391 2576824887570052156358087)
      ·
        refine ⟨3865237331355078234537131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2576824887570052156358087 3865237331355078234537131)
        ·
          refine ⟨5797855997032617351805697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3865237331355078234537131 5797855997032617351805697)
          ·
            refine ⟨4348391997774463013854273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5797855997032617351805697 4348391997774463013854273)
            ·
              refine ⟨3261293998330847260390705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4348391997774463013854273 3261293998330847260390705)
              ·
                refine ⟨2445970498748135445293029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3261293998330847260390705 2445970498748135445293029)
                ·
                  refine ⟨458619468515275395992443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2445970498748135445293029 458619468515275395992443)
                  ·
                    rfl

theorem cell21_2009606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_2009606 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2009606 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2009606 prefixEnd_2009606 := by exact prefixLift 2009606
  have htrace : WordTrace (prefixWord ++ tailWord_2009606) baseStart_2009606 baseEnd_2009606 := by
    simpa [prefixWord, tailWord_2009606, baseEnd_2009606] using wordTrace_append hprefix tailTrace_2009606
  have hstable : (prefixWord ++ tailWord_2009606).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009606).length < 2 ^ (prefixWord ++ tailWord_2009606).sum := by decide
  have hdescent : baseEnd_2009606 < baseStart_2009606 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009662 : List Nat := [4, 2, 1, 4, 1, 1, 8]
def baseStart_2009662 : Nat := 118140960795 + 2009662 * 2 ^ 59
def prefixEnd_2009662 : Nat := 4983230072969 + 3 ^ 40 * 2009662 * 2
def baseEnd_2009662 : Nat := 50959138719803527006555

theorem tailTrace_2009662 : CollatzResearch.WordTrace tailWord_2009662 prefixEnd_2009662 50959138719803527006555 := by
  unfold tailWord_2009662
  simp only [CollatzResearch.WordTrace]
  refine ⟨9162299355668158973666905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48865596563563514526223493 9162299355668158973666905)
  ·
    refine ⟨6871724516751119230250179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9162299355668158973666905 6871724516751119230250179)
    ·
      refine ⟨10307586775126678845375269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6871724516751119230250179 10307586775126678845375269)
      ·
        refine ⟨1932672520336252283507863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10307586775126678845375269 1932672520336252283507863)
        ·
          refine ⟨2899008780504378425261795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1932672520336252283507863 2899008780504378425261795)
          ·
            refine ⟨4348513170756567637892693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2899008780504378425261795 4348513170756567637892693)
            ·
              refine ⟨50959138719803527006555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4348513170756567637892693 50959138719803527006555)
              ·
                rfl

theorem cell21_2009662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 8].length) (baseStart_2009662 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2009662 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2009662 prefixEnd_2009662 := by exact prefixLift 2009662
  have htrace : WordTrace (prefixWord ++ tailWord_2009662) baseStart_2009662 baseEnd_2009662 := by
    simpa [prefixWord, tailWord_2009662, baseEnd_2009662] using wordTrace_append hprefix tailTrace_2009662
  have hstable : (prefixWord ++ tailWord_2009662).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009662).length < 2 ^ (prefixWord ++ tailWord_2009662).sum := by decide
  have hdescent : baseEnd_2009662 < baseStart_2009662 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009676 : List Nat := [2, 2, 1, 3, 1, 2, 1, 6, 3]
def baseStart_2009676 : Nat := 118140960795 + 2009676 * 2 ^ 59
def prefixEnd_2009676 : Nat := 4983230072969 + 3 ^ 40 * 2009676 * 2
def baseEnd_2009676 : Nat := 458635443468970829825633

theorem tailTrace_2009676 : CollatzResearch.WordTrace tailWord_2009676 prefixEnd_2009676 458635443468970829825633 := by
  unfold tailWord_2009676
  simp only [CollatzResearch.WordTrace]
  refine ⟨36649452733647276090172441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48865936978196368120229921 36649452733647276090172441)
  ·
    refine ⟨27487089550235457067629331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36649452733647276090172441 27487089550235457067629331)
    ·
      refine ⟨41230634325353185601443997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27487089550235457067629331 41230634325353185601443997)
      ·
        refine ⟨15461487872007444600541499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41230634325353185601443997 15461487872007444600541499)
        ·
          refine ⟨23192231808011166900812249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15461487872007444600541499 23192231808011166900812249)
          ·
            refine ⟨17394173856008375175609187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23192231808011166900812249 17394173856008375175609187)
            ·
              refine ⟨26091260784012562763413781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17394173856008375175609187 26091260784012562763413781)
              ·
                refine ⟨1223027849250588879535021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 26091260784012562763413781 1223027849250588879535021)
                ·
                  refine ⟨458635443468970829825633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1223027849250588879535021 458635443468970829825633)
                  ·
                    rfl

theorem cell21_2009676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 6, 3].length) (baseStart_2009676 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2009676 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2009676 prefixEnd_2009676 := by exact prefixLift 2009676
  have htrace : WordTrace (prefixWord ++ tailWord_2009676) baseStart_2009676 baseEnd_2009676 := by
    simpa [prefixWord, tailWord_2009676, baseEnd_2009676] using wordTrace_append hprefix tailTrace_2009676
  have hstable : (prefixWord ++ tailWord_2009676).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009676).length < 2 ^ (prefixWord ++ tailWord_2009676).sum := by decide
  have hdescent : baseEnd_2009676 < baseStart_2009676 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009710 : List Nat := [4, 1, 2, 2, 2, 3, 1, 3, 3]
def baseStart_2009710 : Nat := 118140960795 + 2009710 * 2 ^ 59
def prefixEnd_2009710 : Nat := 4983230072969 + 3 ^ 40 * 2009710 * 2
def baseEnd_2009710 : Nat := 458643202732194326258897

theorem tailTrace_2009710 : CollatzResearch.WordTrace tailWord_2009710 prefixEnd_2009710 458643202732194326258897 := by
  unfold tailWord_2009710
  simp only [CollatzResearch.WordTrace]
  refine ⟨9162518193646421998385323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48866763699447583991388389 9162518193646421998385323)
  ·
    refine ⟨13743777290469632997577985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9162518193646421998385323 13743777290469632997577985)
    ·
      refine ⟨10307832967852224748183489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13743777290469632997577985 10307832967852224748183489)
      ·
        refine ⟨7730874725889168561137617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10307832967852224748183489 7730874725889168561137617)
        ·
          refine ⟨5798156044416876420853213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7730874725889168561137617 5798156044416876420853213)
          ·
            refine ⟨2174308516656328657819955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5798156044416876420853213 2174308516656328657819955)
            ·
              refine ⟨3261462774984492986729933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2174308516656328657819955 3261462774984492986729933)
              ·
                refine ⟨1223048540619184870023725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3261462774984492986729933 1223048540619184870023725)
                ·
                  refine ⟨458643202732194326258897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1223048540619184870023725 458643202732194326258897)
                  ·
                    rfl

theorem cell21_2009710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 1, 3, 3].length) (baseStart_2009710 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2009710 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2009710 prefixEnd_2009710 := by exact prefixLift 2009710
  have htrace : WordTrace (prefixWord ++ tailWord_2009710) baseStart_2009710 baseEnd_2009710 := by
    simpa [prefixWord, tailWord_2009710, baseEnd_2009710] using wordTrace_append hprefix tailTrace_2009710
  have hstable : (prefixWord ++ tailWord_2009710).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009710).length < 2 ^ (prefixWord ++ tailWord_2009710).sum := by decide
  have hdescent : baseEnd_2009710 < baseStart_2009710 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009783 : List Nat := [1, 1, 3, 1, 6, 1, 2, 2, 4]
def baseStart_2009783 : Nat := 118140960795 + 2009783 * 2 ^ 59
def prefixEnd_2009783 : Nat := 4983230072969 + 3 ^ 40 * 2009783 * 2
def baseEnd_2009783 : Nat := 458659862326762421542081

theorem tailTrace_2009783 : CollatzResearch.WordTrace tailWord_2009783 prefixEnd_2009783 458659862326762421542081 := by
  unfold tailWord_2009783
  simp only [CollatzResearch.WordTrace]
  refine ⟨73302808077906909454490003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48868538718604606302993335 73302808077906909454490003)
  ·
    refine ⟨109954212116860364181735005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73302808077906909454490003 109954212116860364181735005)
    ·
      refine ⟨41232829543822636568150627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109954212116860364181735005 41232829543822636568150627)
      ·
        refine ⟨61849244315733954852225941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41232829543822636568150627 61849244315733954852225941)
        ·
          refine ⟨2899183327300029133698091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 61849244315733954852225941 2899183327300029133698091)
          ·
            refine ⟨4348774990950043700547137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2899183327300029133698091 4348774990950043700547137)
            ·
              refine ⟨3261581243212532775410353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4348774990950043700547137 3261581243212532775410353)
              ·
                refine ⟨2446185932409399581557765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3261581243212532775410353 2446185932409399581557765)
                ·
                  refine ⟨458659862326762421542081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2446185932409399581557765 458659862326762421542081)
                  ·
                    rfl

theorem cell21_2009783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 2, 2, 4].length) (baseStart_2009783 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2009783 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2009783 prefixEnd_2009783 := by exact prefixLift 2009783
  have htrace : WordTrace (prefixWord ++ tailWord_2009783) baseStart_2009783 baseEnd_2009783 := by
    simpa [prefixWord, tailWord_2009783, baseEnd_2009783] using wordTrace_append hprefix tailTrace_2009783
  have hstable : (prefixWord ++ tailWord_2009783).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009783).length < 2 ^ (prefixWord ++ tailWord_2009783).sum := by decide
  have hdescent : baseEnd_2009783 < baseStart_2009783 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009828 : List Nat := [2, 3, 1, 1, 1, 4, 1, 5, 3]
def baseStart_2009828 : Nat := 118140960795 + 2009828 * 2 ^ 59
def prefixEnd_2009828 : Nat := 4983230072969 + 3 ^ 40 * 2009828 * 2
def baseEnd_2009828 : Nat := 458670131939852343291989

theorem tailTrace_2009828 : CollatzResearch.WordTrace tailWord_2009828 prefixEnd_2009828 458670131939852343291989 := by
  unfold tailWord_2009828
  simp only [CollatzResearch.WordTrace]
  refine ⟨36652224681371941069939069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48869632908495921426585425 36652224681371941069939069)
  ·
    refine ⟨13744584255514477901227151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36652224681371941069939069 13744584255514477901227151)
    ·
      refine ⟨20616876383271716851840727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13744584255514477901227151 20616876383271716851840727)
      ·
        refine ⟨30925314574907575277761091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20616876383271716851840727 30925314574907575277761091)
        ·
          refine ⟨46387971862361362916641637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30925314574907575277761091 46387971862361362916641637)
          ·
            refine ⟨8697744724192755546870307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46387971862361362916641637 8697744724192755546870307)
            ·
              refine ⟨13046617086289133320305461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8697744724192755546870307 13046617086289133320305461)
              ·
                refine ⟨1223120351839606248778637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13046617086289133320305461 1223120351839606248778637)
                ·
                  refine ⟨458670131939852343291989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1223120351839606248778637 458670131939852343291989)
                  ·
                    rfl

theorem cell21_2009828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 5, 3].length) (baseStart_2009828 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2009828 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2009828 prefixEnd_2009828 := by exact prefixLift 2009828
  have htrace : WordTrace (prefixWord ++ tailWord_2009828) baseStart_2009828 baseEnd_2009828 := by
    simpa [prefixWord, tailWord_2009828, baseEnd_2009828] using wordTrace_append hprefix tailTrace_2009828
  have hstable : (prefixWord ++ tailWord_2009828).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009828).length < 2 ^ (prefixWord ++ tailWord_2009828).sum := by decide
  have hdescent : baseEnd_2009828 < baseStart_2009828 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009842 : List Nat := [3, 2, 1, 3, 1, 3, 1, 1, 6]
def baseStart_2009842 : Nat := 118140960795 + 2009842 * 2 ^ 59
def prefixEnd_2009842 : Nat := 4983230072969 + 3 ^ 40 * 2009842 * 2
def baseEnd_2009842 : Nat := 458673326930591430058627

theorem tailTrace_2009842 : CollatzResearch.WordTrace tailWord_2009842 prefixEnd_2009842 458673326930591430058627 := by
  unfold tailWord_2009842
  simp only [CollatzResearch.WordTrace]
  refine ⟨18326239996173290632721945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48869973323128775020591853 18326239996173290632721945)
  ·
    refine ⟨13744679997129967974541459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18326239996173290632721945 13744679997129967974541459)
    ·
      refine ⟨20617019995694951961812189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13744679997129967974541459 20617019995694951961812189)
      ·
        refine ⟨7731382498385606985679571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20617019995694951961812189 7731382498385606985679571)
        ·
          refine ⟨11597073747578410478519357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7731382498385606985679571 11597073747578410478519357)
          ·
            refine ⟨4348902655341903929444759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11597073747578410478519357 4348902655341903929444759)
            ·
              refine ⟨6523353983012855894167139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4348902655341903929444759 6523353983012855894167139)
              ·
                refine ⟨9785030974519283841250709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6523353983012855894167139 9785030974519283841250709)
                ·
                  refine ⟨458673326930591430058627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9785030974519283841250709 458673326930591430058627)
                  ·
                    rfl

theorem cell21_2009842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 1, 6].length) (baseStart_2009842 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2009842 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2009842 prefixEnd_2009842 := by exact prefixLift 2009842
  have htrace : WordTrace (prefixWord ++ tailWord_2009842) baseStart_2009842 baseEnd_2009842 := by
    simpa [prefixWord, tailWord_2009842, baseEnd_2009842] using wordTrace_append hprefix tailTrace_2009842
  have hstable : (prefixWord ++ tailWord_2009842).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009842).length < 2 ^ (prefixWord ++ tailWord_2009842).sum := by decide
  have hdescent : baseEnd_2009842 < baseStart_2009842 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009910 : List Nat := [5, 1, 2, 2, 3, 1, 2, 1, 4]
def baseStart_2009910 : Nat := 118140960795 + 2009910 * 2 ^ 59
def prefixEnd_2009910 : Nat := 4983230072969 + 3 ^ 40 * 2009910 * 2
def baseEnd_2009910 : Nat := 458688845457038422925155

theorem tailTrace_2009910 : CollatzResearch.WordTrace tailWord_2009910 prefixEnd_2009910 458688845457038422925155 := by
  unfold tailWord_2009910
  simp only [CollatzResearch.WordTrace]
  refine ⟨4581715009277925634022699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48871626765631206762908789 4581715009277925634022699)
  ·
    refine ⟨6872572513916888451034049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4581715009277925634022699 6872572513916888451034049)
    ·
      refine ⟨5154429385437666338275537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6872572513916888451034049 5154429385437666338275537)
      ·
        refine ⟨3865822039078249753706653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5154429385437666338275537 3865822039078249753706653)
        ·
          refine ⟨1449683264654343657639995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3865822039078249753706653 1449683264654343657639995)
          ·
            refine ⟨2174524896981515486459993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1449683264654343657639995 2174524896981515486459993)
            ·
              refine ⟨1630893672736136614844995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2174524896981515486459993 1630893672736136614844995)
              ·
                refine ⟨2446340509104204922267493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1630893672736136614844995 2446340509104204922267493)
                ·
                  refine ⟨458688845457038422925155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2446340509104204922267493 458688845457038422925155)
                  ·
                    rfl

theorem cell21_2009910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 2, 1, 4].length) (baseStart_2009910 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2009910 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2009910 prefixEnd_2009910 := by exact prefixLift 2009910
  have htrace : WordTrace (prefixWord ++ tailWord_2009910) baseStart_2009910 baseEnd_2009910 := by
    simpa [prefixWord, tailWord_2009910, baseEnd_2009910] using wordTrace_append hprefix tailTrace_2009910
  have hstable : (prefixWord ++ tailWord_2009910).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009910).length < 2 ^ (prefixWord ++ tailWord_2009910).sum := by decide
  have hdescent : baseEnd_2009910 < baseStart_2009910 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009932 : List Nat := [2, 2, 1, 3, 3, 1, 2, 7]
def baseStart_2009932 : Nat := 118140960795 + 2009932 * 2 ^ 59
def prefixEnd_2009932 : Nat := 4983230072969 + 3 ^ 40 * 2009932 * 2
def baseEnd_2009932 : Nat := 152897955385590424519481

theorem tailTrace_2009932 : CollatzResearch.WordTrace tailWord_2009932 prefixEnd_2009932 152897955385590424519481 := by
  unfold tailWord_2009932
  simp only [CollatzResearch.WordTrace]
  refine ⟨36654121277183553950832025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48872161702911405267776033 36654121277183553950832025)
  ·
    refine ⟨27490590957887665463124019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36654121277183553950832025 27490590957887665463124019)
    ·
      refine ⟨41235886436831498194686029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27490590957887665463124019 41235886436831498194686029)
      ·
        refine ⟨15463457413811811823007261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41235886436831498194686029 15463457413811811823007261)
        ·
          refine ⟨5798796530179429433627723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15463457413811811823007261 5798796530179429433627723)
          ·
            refine ⟨8698194795269144150441585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5798796530179429433627723 8698194795269144150441585)
            ·
              refine ⟨6523646096451858112831189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8698194795269144150441585 6523646096451858112831189)
              ·
                refine ⟨152897955385590424519481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6523646096451858112831189 152897955385590424519481)
                ·
                  rfl

theorem cell21_2009932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 7].length) (baseStart_2009932 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2009932 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2009932 prefixEnd_2009932 := by exact prefixLift 2009932
  have htrace : WordTrace (prefixWord ++ tailWord_2009932) baseStart_2009932 baseEnd_2009932 := by
    simpa [prefixWord, tailWord_2009932, baseEnd_2009932] using wordTrace_append hprefix tailTrace_2009932
  have hstable : (prefixWord ++ tailWord_2009932).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009932).length < 2 ^ (prefixWord ++ tailWord_2009932).sum := by decide
  have hdescent : baseEnd_2009932 < baseStart_2009932 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009966 : List Nat := [4, 1, 2, 3, 2, 2, 1, 6]
def baseStart_2009966 : Nat := 118140960795 + 2009966 * 2 ^ 59
def prefixEnd_2009966 : Nat := 4983230072969 + 3 ^ 40 * 2009966 * 2
def baseEnd_2009966 : Nat := 152900541806664923330569

theorem tailTrace_2009966 : CollatzResearch.WordTrace tailWord_2009966 prefixEnd_2009966 152900541806664923330569 := by
  unfold tailWord_2009966
  simp only [CollatzResearch.WordTrace]
  refine ⟨9163685329530491463550219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48872988424162621138934501 9163685329530491463550219)
  ·
    refine ⟨13745527994295737195325329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9163685329530491463550219 13745527994295737195325329)
    ·
      refine ⟨10309145995721802896493997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13745527994295737195325329 10309145995721802896493997)
      ·
        refine ⟨3865929748395676086185249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10309145995721802896493997 3865929748395676086185249)
        ·
          refine ⟨2899447311296757064638937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3865929748395676086185249 2899447311296757064638937)
          ·
            refine ⟨2174585483472567798479203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2899447311296757064638937 2174585483472567798479203)
            ·
              refine ⟨3261878225208851697718805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2174585483472567798479203 3261878225208851697718805)
              ·
                refine ⟨152900541806664923330569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3261878225208851697718805 152900541806664923330569)
                ·
                  rfl

theorem cell21_2009966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 1, 6].length) (baseStart_2009966 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2009966 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2009966 prefixEnd_2009966 := by exact prefixLift 2009966
  have htrace : WordTrace (prefixWord ++ tailWord_2009966) baseStart_2009966 baseEnd_2009966 := by
    simpa [prefixWord, tailWord_2009966, baseEnd_2009966] using wordTrace_append hprefix tailTrace_2009966
  have hstable : (prefixWord ++ tailWord_2009966).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009966).length < 2 ^ (prefixWord ++ tailWord_2009966).sum := by decide
  have hdescent : baseEnd_2009966 < baseStart_2009966 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2010073 : List Nat := [1, 2, 1, 2, 5, 2, 3, 2, 3]
def baseStart_2010073 : Nat := 118140960795 + 2010073 * 2 ^ 59
def prefixEnd_2010073 : Nat := 4983230072969 + 3 ^ 40 * 2010073 * 2
def baseEnd_2010073 : Nat := 458726044277786361708155

theorem tailTrace_2010073 : CollatzResearch.WordTrace tailWord_2010073 prefixEnd_2010073 458726044277786361708155 := by
  unfold tailWord_2010073
  simp only [CollatzResearch.WordTrace]
  refine ⟨73313385246856288982546873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48875590164570859321697915 73313385246856288982546873)
  ·
    refine ⟨54985038935142216736910155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73313385246856288982546873 54985038935142216736910155)
    ·
      refine ⟨82477558402713325105365233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54985038935142216736910155 82477558402713325105365233)
      ·
        refine ⟨61858168802034993829023925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82477558402713325105365233 61858168802034993829023925)
        ·
          refine ⟨5799203325190780671470993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 61858168802034993829023925 5799203325190780671470993)
          ·
            refine ⟨4349402493893085503603245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5799203325190780671470993 4349402493893085503603245)
            ·
              refine ⟨1631025935209907063851217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4349402493893085503603245 1631025935209907063851217)
              ·
                refine ⟨1223269451407430297888413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1631025935209907063851217 1223269451407430297888413)
                ·
                  refine ⟨458726044277786361708155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1223269451407430297888413 458726044277786361708155)
                  ·
                    rfl

theorem cell21_2010073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 3, 2, 3].length) (baseStart_2010073 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2010073 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2010073 prefixEnd_2010073 := by exact prefixLift 2010073
  have htrace : WordTrace (prefixWord ++ tailWord_2010073) baseStart_2010073 baseEnd_2010073 := by
    simpa [prefixWord, tailWord_2010073, baseEnd_2010073] using wordTrace_append hprefix tailTrace_2010073
  have hstable : (prefixWord ++ tailWord_2010073).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2010073).length < 2 ^ (prefixWord ++ tailWord_2010073).sum := by decide
  have hdescent : baseEnd_2010073 < baseStart_2010073 := by decide
  rcases family_descends (prefixWord ++ tailWord_2010073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2010087 : List Nat := [1, 1, 5, 2, 2, 1, 4, 1, 4]
def baseStart_2010087 : Nat := 118140960795 + 2010087 * 2 ^ 59
def prefixEnd_2010087 : Nat := 4983230072969 + 3 ^ 40 * 2010087 * 2
def baseEnd_2010087 : Nat := 458729239268525448474793

theorem tailTrace_2010087 : CollatzResearch.WordTrace tailWord_2010087 prefixEnd_2010087 458729239268525448474793 := by
  unfold tailWord_2010087
  simp only [CollatzResearch.WordTrace]
  refine ⟨73313895868805569373556515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48875930579203712915704343 73313895868805569373556515)
  ·
    refine ⟨109970843803208354060334773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73313895868805569373556515 109970843803208354060334773)
    ·
      refine ⟨10309766606550783193156385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 109970843803208354060334773 10309766606550783193156385)
      ·
        refine ⟨7732324954913087394867289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10309766606550783193156385 7732324954913087394867289)
        ·
          refine ⟨5799243716184815546150467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7732324954913087394867289 5799243716184815546150467)
          ·
            refine ⟨8698865574277223319225701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5799243716184815546150467 8698865574277223319225701)
            ·
              refine ⟨1631037295176979372354819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8698865574277223319225701 1631037295176979372354819)
              ·
                refine ⟨2446555942765469058532229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1631037295176979372354819 2446555942765469058532229)
                ·
                  refine ⟨458729239268525448474793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2446555942765469058532229 458729239268525448474793)
                  ·
                    rfl

theorem cell21_2010087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 4, 1, 4].length) (baseStart_2010087 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2010087 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2010087 prefixEnd_2010087 := by exact prefixLift 2010087
  have htrace : WordTrace (prefixWord ++ tailWord_2010087) baseStart_2010087 baseEnd_2010087 := by
    simpa [prefixWord, tailWord_2010087, baseEnd_2010087] using wordTrace_append hprefix tailTrace_2010087
  have hstable : (prefixWord ++ tailWord_2010087).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2010087).length < 2 ^ (prefixWord ++ tailWord_2010087).sum := by decide
  have hdescent : baseEnd_2010087 < baseStart_2010087 := by decide
  rcases family_descends (prefixWord ++ tailWord_2010087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2010146 : List Nat := [3, 3, 1, 1, 1, 3, 2, 3, 4]
def baseStart_2010146 : Nat := 118140960795 + 2010146 * 2 ^ 59
def prefixEnd_2010146 : Nat := 4983230072969 + 3 ^ 40 * 2010146 * 2
def baseEnd_2010146 : Nat := 458742703872354456991339

theorem tailTrace_2010146 : CollatzResearch.WordTrace tailWord_2010146 prefixEnd_2010146 458742703872354456991339 := by
  unfold tailWord_2010146
  simp only [CollatzResearch.WordTrace]
  refine ⟨18329011943897955612488573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48877365183727881633302861 18329011943897955612488573)
  ·
    refine ⟨6873379478961733354683215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18329011943897955612488573 6873379478961733354683215)
    ·
      refine ⟨10310069218442600032024823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6873379478961733354683215 10310069218442600032024823)
      ·
        refine ⟨15465103827663900048037235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10310069218442600032024823 15465103827663900048037235)
        ·
          refine ⟨23197655741495850072055853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15465103827663900048037235 23197655741495850072055853)
          ·
            refine ⟨8699120903060943777020945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23197655741495850072055853 8699120903060943777020945)
            ·
              refine ⟨6524340677295707832765709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8699120903060943777020945 6524340677295707832765709)
              ·
                refine ⟨2446627753985890437287141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6524340677295707832765709 2446627753985890437287141)
                ·
                  refine ⟨458742703872354456991339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2446627753985890437287141 458742703872354456991339)
                  ·
                    rfl

theorem cell21_2010146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 3, 4].length) (baseStart_2010146 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2010146 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2010146 prefixEnd_2010146 := by exact prefixLift 2010146
  have htrace : WordTrace (prefixWord ++ tailWord_2010146) baseStart_2010146 baseEnd_2010146 := by
    simpa [prefixWord, tailWord_2010146, baseEnd_2010146] using wordTrace_append hprefix tailTrace_2010146
  have hstable : (prefixWord ++ tailWord_2010146).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2010146).length < 2 ^ (prefixWord ++ tailWord_2010146).sum := by decide
  have hdescent : baseEnd_2010146 < baseStart_2010146 := by decide
  rcases family_descends (prefixWord ++ tailWord_2010146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2010160 : List Nat := [2, 1, 1, 1, 2, 4, 5, 5]
def baseStart_2010160 : Nat := 118140960795 + 2010160 * 2 ^ 59
def prefixEnd_2010160 : Nat := 4983230072969 + 3 ^ 40 * 2010160 * 2
def baseEnd_2010160 : Nat := 152915299621031181252659

theorem tailTrace_2010160 : CollatzResearch.WordTrace tailWord_2010160 prefixEnd_2010160 152915299621031181252659 := by
  unfold tailWord_2010160
  simp only [CollatzResearch.WordTrace]
  refine ⟨36658279198770551420481967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48877705598360735227309289 36658279198770551420481967)
  ·
    refine ⟨54987418798155827130722951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36658279198770551420481967 54987418798155827130722951)
    ·
      refine ⟨82481128197233740696084427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54987418798155827130722951 82481128197233740696084427)
      ·
        refine ⟨123721692295850611044126641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82481128197233740696084427 123721692295850611044126641)
        ·
          refine ⟨92791269221887958283094981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123721692295850611044126641 92791269221887958283094981)
          ·
            refine ⟨17398362979103992178080309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92791269221887958283094981 17398362979103992178080309)
            ·
              refine ⟨1631096529290999266695029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17398362979103992178080309 1631096529290999266695029)
              ·
                refine ⟨152915299621031181252659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1631096529290999266695029 152915299621031181252659)
                ·
                  rfl

theorem cell21_2010160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 5, 5].length) (baseStart_2010160 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2010160 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2010160 prefixEnd_2010160 := by exact prefixLift 2010160
  have htrace : WordTrace (prefixWord ++ tailWord_2010160) baseStart_2010160 baseEnd_2010160 := by
    simpa [prefixWord, tailWord_2010160, baseEnd_2010160] using wordTrace_append hprefix tailTrace_2010160
  have hstable : (prefixWord ++ tailWord_2010160).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2010160).length < 2 ^ (prefixWord ++ tailWord_2010160).sum := by decide
  have hdescent : baseEnd_2010160 < baseStart_2010160 := by decide
  rcases family_descends (prefixWord ++ tailWord_2010160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2010416 : List Nat := [2, 1, 1, 1, 2, 2, 3, 3, 6]
def baseStart_2010416 : Nat := 118140960795 + 2010416 * 2 ^ 59
def prefixEnd_2010416 : Nat := 4983230072969 + 3 ^ 40 * 2010416 * 2
def baseEnd_2010416 : Nat := 458804321550893987490787

theorem tailTrace_2010416 : CollatzResearch.WordTrace tailWord_2010416 prefixEnd_2010416 458804321550893987490787 := by
  unfold tailWord_2010416
  simp only [CollatzResearch.WordTrace]
  refine ⟨36662947742306829281141551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48883930323075772374855401 36662947742306829281141551)
  ·
    refine ⟨54994421613460243921712327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36662947742306829281141551 54994421613460243921712327)
    ·
      refine ⟨82491632420190365882568491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54994421613460243921712327 82491632420190365882568491)
      ·
        refine ⟨123737448630285548823852737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82491632420190365882568491 123737448630285548823852737)
        ·
          refine ⟨92803086472714161617889553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123737448630285548823852737 92803086472714161617889553)
          ·
            refine ⟨69602314854535621213417165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92803086472714161617889553 69602314854535621213417165)
            ·
              refine ⟨26100868070450857955031437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69602314854535621213417165 26100868070450857955031437)
              ·
                refine ⟨9787825526419071733136789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26100868070450857955031437 9787825526419071733136789)
                ·
                  refine ⟨458804321550893987490787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9787825526419071733136789 458804321550893987490787)
                  ·
                    rfl

theorem cell21_2010416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 3, 6].length) (baseStart_2010416 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2010416 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2010416 prefixEnd_2010416 := by exact prefixLift 2010416
  have htrace : WordTrace (prefixWord ++ tailWord_2010416) baseStart_2010416 baseEnd_2010416 := by
    simpa [prefixWord, tailWord_2010416, baseEnd_2010416] using wordTrace_append hprefix tailTrace_2010416
  have hstable : (prefixWord ++ tailWord_2010416).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2010416).length < 2 ^ (prefixWord ++ tailWord_2010416).sum := by decide
  have hdescent : baseEnd_2010416 < baseStart_2010416 := by decide
  rcases family_descends (prefixWord ++ tailWord_2010416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2010419 : List Nat := [1, 1, 1, 2, 5, 4, 1, 1, 5]
def baseStart_2010419 : Nat := 118140960795 + 2010419 * 2 ^ 59
def prefixEnd_2010419 : Nat := 4983230072969 + 3 ^ 40 * 2010419 * 2
def baseEnd_2010419 : Nat := 458805006191766648940781

theorem tailTrace_2010419 : CollatzResearch.WordTrace tailWord_2010419 prefixEnd_2010419 458805006191766648940781 := by
  unfold tailWord_2010419
  simp only [CollatzResearch.WordTrace]
  refine ⟨73326004903602790074642311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48884003269068526716428207 73326004903602790074642311)
  ·
    refine ⟨109989007355404185111963467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73326004903602790074642311 109989007355404185111963467)
    ·
      refine ⟨164983511033106277667945201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109989007355404185111963467 164983511033106277667945201)
      ·
        refine ⟨123737633274829708250958901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164983511033106277667945201 123737633274829708250958901)
        ·
          refine ⟨11600403119515285148527397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 123737633274829708250958901 11600403119515285148527397)
          ·
            refine ⟨2175075584909115965348887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11600403119515285148527397 2175075584909115965348887)
            ·
              refine ⟨3262613377363673948023331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2175075584909115965348887 3262613377363673948023331)
              ·
                refine ⟨4893920066045510922034997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3262613377363673948023331 4893920066045510922034997)
                ·
                  refine ⟨458805006191766648940781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4893920066045510922034997 458805006191766648940781)
                  ·
                    rfl

theorem cell21_2010419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 1, 1, 5].length) (baseStart_2010419 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2010419 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2010419 prefixEnd_2010419 := by exact prefixLift 2010419
  have htrace : WordTrace (prefixWord ++ tailWord_2010419) baseStart_2010419 baseEnd_2010419 := by
    simpa [prefixWord, tailWord_2010419, baseEnd_2010419] using wordTrace_append hprefix tailTrace_2010419
  have hstable : (prefixWord ++ tailWord_2010419).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2010419).length < 2 ^ (prefixWord ++ tailWord_2010419).sum := by decide
  have hdescent : baseEnd_2010419 < baseStart_2010419 := by decide
  rcases family_descends (prefixWord ++ tailWord_2010419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2010422 : List Nat := [5, 1, 2, 3, 1, 1, 2, 6]
def baseStart_2010422 : Nat := 118140960795 + 2010422 * 2 ^ 59
def prefixEnd_2010422 : Nat := 4983230072969 + 3 ^ 40 * 2010422 * 2
def baseEnd_2010422 : Nat := 152935230277546436796925

theorem tailTrace_2010422 : CollatzResearch.WordTrace tailWord_2010422 prefixEnd_2010422 152935230277546436796925 := by
  unfold tailWord_2010422
  simp only [CollatzResearch.WordTrace]
  refine ⟨4582882145161995099187595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48884076215061281058001013 4582882145161995099187595)
  ·
    refine ⟨6874323217742992648781393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4582882145161995099187595 6874323217742992648781393)
    ·
      refine ⟨5155742413307244486586045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6874323217742992648781393 5155742413307244486586045)
      ·
        refine ⟨1933403404990216682469767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5155742413307244486586045 1933403404990216682469767)
        ·
          refine ⟨2900105107485325023704651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1933403404990216682469767 2900105107485325023704651)
          ·
            refine ⟨4350157661227987535556977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2900105107485325023704651 4350157661227987535556977)
            ·
              refine ⟨3262618245920990651667733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4350157661227987535556977 3262618245920990651667733)
              ·
                refine ⟨152935230277546436796925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3262618245920990651667733 152935230277546436796925)
                ·
                  rfl

theorem cell21_2010422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 2, 6].length) (baseStart_2010422 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2010422 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2010422 prefixEnd_2010422 := by exact prefixLift 2010422
  have htrace : WordTrace (prefixWord ++ tailWord_2010422) baseStart_2010422 baseEnd_2010422 := by
    simpa [prefixWord, tailWord_2010422, baseEnd_2010422] using wordTrace_append hprefix tailTrace_2010422
  have hstable : (prefixWord ++ tailWord_2010422).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2010422).length < 2 ^ (prefixWord ++ tailWord_2010422).sum := by decide
  have hdescent : baseEnd_2010422 < baseStart_2010422 := by decide
  rcases family_descends (prefixWord ++ tailWord_2010422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2010498 : List Nat := [3, 4, 2, 1, 1, 2, 3, 5]
def baseStart_2010498 : Nat := 118140960795 + 2010498 * 2 ^ 59
def prefixEnd_2010498 : Nat := 4983230072969 + 3 ^ 40 * 2010498 * 2
def baseEnd_2010498 : Nat := 152941011689360022374651

theorem tailTrace_2010498 : CollatzResearch.WordTrace tailWord_2010498 prefixEnd_2010498 152941011689360022374651 := by
  unfold tailWord_2010498
  simp only [CollatzResearch.WordTrace]
  refine ⟨18332221567579146641692037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48885924180211057711178765 18332221567579146641692037)
  ·
    refine ⟨3437291543921089995317257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18332221567579146641692037 3437291543921089995317257)
    ·
      refine ⟨2577968657940817496487943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3437291543921089995317257 2577968657940817496487943)
      ·
        refine ⟨3866952986911226244731915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2577968657940817496487943 3866952986911226244731915)
        ·
          refine ⟨5800429480366839367097873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3866952986911226244731915 5800429480366839367097873)
          ·
            refine ⟨4350322110275129525323405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5800429480366839367097873 4350322110275129525323405)
            ·
              refine ⟨1631370791353173571996277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4350322110275129525323405 1631370791353173571996277)
              ·
                refine ⟨152941011689360022374651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1631370791353173571996277 152941011689360022374651)
                ·
                  rfl

theorem cell21_2010498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 3, 5].length) (baseStart_2010498 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2010498 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2010498 prefixEnd_2010498 := by exact prefixLift 2010498
  have htrace : WordTrace (prefixWord ++ tailWord_2010498) baseStart_2010498 baseEnd_2010498 := by
    simpa [prefixWord, tailWord_2010498, baseEnd_2010498] using wordTrace_append hprefix tailTrace_2010498
  have hstable : (prefixWord ++ tailWord_2010498).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2010498).length < 2 ^ (prefixWord ++ tailWord_2010498).sum := by decide
  have hdescent : baseEnd_2010498 < baseStart_2010498 := by decide
  rcases family_descends (prefixWord ++ tailWord_2010498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2010568 : List Nat := [2, 1, 3, 1, 3, 1, 1, 1, 8]
def baseStart_2010568 : Nat := 118140960795 + 2010568 * 2 ^ 59
def prefixEnd_2010568 : Nat := 4983230072969 + 3 ^ 40 * 2010568 * 2
def baseEnd_2010568 : Nat := 458839010021775500957143

theorem tailTrace_2010568 : CollatzResearch.WordTrace tailWord_2010568 prefixEnd_2010568 458839010021775500957143 := by
  unfold tailWord_2010568
  simp only [CollatzResearch.WordTrace]
  refine ⟨36665719690031494260908179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48887626253375325681210905 36665719690031494260908179)
  ·
    refine ⟨54998579535047241391362269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36665719690031494260908179 54998579535047241391362269)
    ·
      refine ⟨20624467325642715521760851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54998579535047241391362269 20624467325642715521760851)
      ·
        refine ⟨30936700988464073282641277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20624467325642715521760851 30936700988464073282641277)
        ·
          refine ⟨11601262870674027480990479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30936700988464073282641277 11601262870674027480990479)
          ·
            refine ⟨17401894306011041221485719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11601262870674027480990479 17401894306011041221485719)
            ·
              refine ⟨26102841459016561832228579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17401894306011041221485719 26102841459016561832228579)
              ·
                refine ⟨39154262188524842748342869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26102841459016561832228579 39154262188524842748342869)
                ·
                  refine ⟨458839010021775500957143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39154262188524842748342869 458839010021775500957143)
                  ·
                    rfl

theorem cell21_2010568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 8].length) (baseStart_2010568 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2010568 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2010568 prefixEnd_2010568 := by exact prefixLift 2010568
  have htrace : WordTrace (prefixWord ++ tailWord_2010568) baseStart_2010568 baseEnd_2010568 := by
    simpa [prefixWord, tailWord_2010568, baseEnd_2010568] using wordTrace_append hprefix tailTrace_2010568
  have hstable : (prefixWord ++ tailWord_2010568).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2010568).length < 2 ^ (prefixWord ++ tailWord_2010568).sum := by decide
  have hdescent : baseEnd_2010568 < baseStart_2010568 := by decide
  rcases family_descends (prefixWord ++ tailWord_2010568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2010571 : List Nat := [1, 1, 1, 1, 3, 3, 5, 3, 3]
def baseStart_2010571 : Nat := 118140960795 + 2010571 * 2 ^ 59
def prefixEnd_2010571 : Nat := 4983230072969 + 3 ^ 40 * 2010571 * 2
def baseEnd_2010571 : Nat := 458839694662648162407137

theorem tailTrace_2010571 : CollatzResearch.WordTrace tailWord_2010571 prefixEnd_2010571 458839694662648162407137 := by
  unfold tailWord_2010571
  simp only [CollatzResearch.WordTrace]
  refine ⟨73331548799052120034175567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48887699199368080022783711 73331548799052120034175567)
  ·
    refine ⟨109997323198578180051263351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73331548799052120034175567 109997323198578180051263351)
    ·
      refine ⟨164995984797867270076895027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109997323198578180051263351 164995984797867270076895027)
      ·
        refine ⟨247493977196800905115342541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164995984797867270076895027 247493977196800905115342541)
        ·
          refine ⟨92810241448800339418253453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 247493977196800905115342541 92810241448800339418253453)
          ·
            refine ⟨34803840543300127281845045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92810241448800339418253453 34803840543300127281845045)
            ·
              refine ⟨3262860050934386932672973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34803840543300127281845045 3262860050934386932672973)
              ·
                refine ⟨1223572519100395099752365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3262860050934386932672973 1223572519100395099752365)
                ·
                  refine ⟨458839694662648162407137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1223572519100395099752365 458839694662648162407137)
                  ·
                    rfl

theorem cell21_2010571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 5, 3, 3].length) (baseStart_2010571 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2010571 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2010571 prefixEnd_2010571 := by exact prefixLift 2010571
  have htrace : WordTrace (prefixWord ++ tailWord_2010571) baseStart_2010571 baseEnd_2010571 := by
    simpa [prefixWord, tailWord_2010571, baseEnd_2010571] using wordTrace_append hprefix tailTrace_2010571
  have hstable : (prefixWord ++ tailWord_2010571).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2010571).length < 2 ^ (prefixWord ++ tailWord_2010571).sum := by decide
  have hdescent : baseEnd_2010571 < baseStart_2010571 := by decide
  rcases family_descends (prefixWord ++ tailWord_2010571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2010599 : List Nat := [1, 1, 5, 2, 1, 2, 1, 8]
def baseStart_2010599 : Nat := 118140960795 + 2010599 * 2 ^ 59
def prefixEnd_2010599 : Nat := 4983230072969 + 3 ^ 40 * 2010599 * 2
def baseEnd_2010599 : Nat := 152948694881375445313471

theorem tailTrace_2010599 : CollatzResearch.WordTrace tailWord_2010599 prefixEnd_2010599 152948694881375445313471 := by
  unfold tailWord_2010599
  simp only [CollatzResearch.WordTrace]
  refine ⟨73332570042950680816194851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48888380028633787210796567 73332570042950680816194851)
  ·
    refine ⟨109998855064426021224292277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73332570042950680816194851 109998855064426021224292277)
    ·
      refine ⟨10312392662289939489777401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 109998855064426021224292277 10312392662289939489777401)
      ·
        refine ⟨7734294496717454617333051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10312392662289939489777401 7734294496717454617333051)
        ·
          refine ⟨11601441745076181925999577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7734294496717454617333051 11601441745076181925999577)
          ·
            refine ⟨8701081308807136444499683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11601441745076181925999577 8701081308807136444499683)
            ·
              refine ⟨13051621963210704666749525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8701081308807136444499683 13051621963210704666749525)
              ·
                refine ⟨152948694881375445313471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13051621963210704666749525 152948694881375445313471)
                ·
                  rfl

theorem cell21_2010599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 8].length) (baseStart_2010599 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2010599 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2010599 prefixEnd_2010599 := by exact prefixLift 2010599
  have htrace : WordTrace (prefixWord ++ tailWord_2010599) baseStart_2010599 baseEnd_2010599 := by
    simpa [prefixWord, tailWord_2010599, baseEnd_2010599] using wordTrace_append hprefix tailTrace_2010599
  have hstable : (prefixWord ++ tailWord_2010599).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2010599).length < 2 ^ (prefixWord ++ tailWord_2010599).sum := by decide
  have hdescent : baseEnd_2010599 < baseStart_2010599 := by decide
  rcases family_descends (prefixWord ++ tailWord_2010599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2010602 : List Nat := [3, 1, 3, 1, 4, 1, 1, 3, 4]
def baseStart_2010602 : Nat := 118140960795 + 2010602 * 2 ^ 59
def prefixEnd_2010602 : Nat := 4983230072969 + 3 ^ 40 * 2010602 * 2
def baseEnd_2010602 : Nat := 458846769284998997390407

theorem tailTrace_2010602 : CollatzResearch.WordTrace tailWord_2010602 prefixEnd_2010602 458846769284998997390407 := by
  unfold tailWord_2010602
  simp only [CollatzResearch.WordTrace]
  refine ⟨18333169865484953082138515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48888452974626541552369373 18333169865484953082138515)
  ·
    refine ⟨27499754798227429623207773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18333169865484953082138515 27499754798227429623207773)
    ·
      refine ⟨10312408049335286108702915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27499754798227429623207773 10312408049335286108702915)
      ·
        refine ⟨15468612074002929163054373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10312408049335286108702915 15468612074002929163054373)
        ·
          refine ⟨2900364763875549218072695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15468612074002929163054373 2900364763875549218072695)
          ·
            refine ⟨4350547145813323827109043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2900364763875549218072695 4350547145813323827109043)
            ·
              refine ⟨6525820718719985740663565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4350547145813323827109043 6525820718719985740663565)
              ·
                refine ⟨2447182769519994652748837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6525820718719985740663565 2447182769519994652748837)
                ·
                  refine ⟨458846769284998997390407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2447182769519994652748837 458846769284998997390407)
                  ·
                    rfl

theorem cell21_2010602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 3, 4].length) (baseStart_2010602 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2010602 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2010602 prefixEnd_2010602 := by exact prefixLift 2010602
  have htrace : WordTrace (prefixWord ++ tailWord_2010602) baseStart_2010602 baseEnd_2010602 := by
    simpa [prefixWord, tailWord_2010602, baseEnd_2010602] using wordTrace_append hprefix tailTrace_2010602
  have hstable : (prefixWord ++ tailWord_2010602).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2010602).length < 2 ^ (prefixWord ++ tailWord_2010602).sum := by decide
  have hdescent : baseEnd_2010602 < baseStart_2010602 := by decide
  rcases family_descends (prefixWord ++ tailWord_2010602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2010695 : List Nat := [1, 1, 4, 1, 6, 1, 1, 2, 4]
def baseStart_2010695 : Nat := 118140960795 + 2010695 * 2 ^ 59
def prefixEnd_2010695 : Nat := 4983230072969 + 3 ^ 40 * 2010695 * 2
def baseEnd_2010695 : Nat := 458867993152051502340217

theorem tailTrace_2010695 : CollatzResearch.WordTrace tailWord_2010695 prefixEnd_2010695 458867993152051502340217 := by
  unfold tailWord_2010695
  simp only [CollatzResearch.WordTrace]
  refine ⟨73336071450602889211689539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48890714300401926141126359 73336071450602889211689539)
  ·
    refine ⟨110004107175904333817534309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73336071450602889211689539 110004107175904333817534309)
    ·
      refine ⟨20625770095482062590787683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110004107175904333817534309 20625770095482062590787683)
      ·
        refine ⟨30938655143223093886181525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20625770095482062590787683 30938655143223093886181525)
        ·
          refine ⟨1450249459838582525914759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 30938655143223093886181525 1450249459838582525914759)
          ·
            refine ⟨2175374189757873788872139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1450249459838582525914759 2175374189757873788872139)
            ·
              refine ⟨3263061284636810683308209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2175374189757873788872139 3263061284636810683308209)
              ·
                refine ⟨2447295963477608012481157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3263061284636810683308209 2447295963477608012481157)
                ·
                  refine ⟨458867993152051502340217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2447295963477608012481157 458867993152051502340217)
                  ·
                    rfl

theorem cell21_2010695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 1, 2, 4].length) (baseStart_2010695 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2010695 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2010695 prefixEnd_2010695 := by exact prefixLift 2010695
  have htrace : WordTrace (prefixWord ++ tailWord_2010695) baseStart_2010695 baseEnd_2010695 := by
    simpa [prefixWord, tailWord_2010695, baseEnd_2010695] using wordTrace_append hprefix tailTrace_2010695
  have hstable : (prefixWord ++ tailWord_2010695).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2010695).length < 2 ^ (prefixWord ++ tailWord_2010695).sum := by decide
  have hdescent : baseEnd_2010695 < baseStart_2010695 := by decide
  rcases family_descends (prefixWord ++ tailWord_2010695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2010706 : List Nat := [3, 2, 2, 1, 2, 2, 1, 3, 5]
def baseStart_2010706 : Nat := 118140960795 + 2010706 * 2 ^ 59
def prefixEnd_2010706 : Nat := 4983230072969 + 3 ^ 40 * 2010706 * 2
def baseEnd_2010706 : Nat := 458870503501917927656861

theorem tailTrace_2010706 : CollatzResearch.WordTrace tailWord_2010706 prefixEnd_2010706 458870503501917927656861 := by
  unfold tailWord_2010706
  simp only [CollatzResearch.WordTrace]
  refine ⟨18334118163390759522584993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48890981769042025393559981 18334118163390759522584993)
  ·
    refine ⟨13750588622543069641938745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18334118163390759522584993 13750588622543069641938745)
    ·
      refine ⟨10312941466907302231454059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13750588622543069641938745 10312941466907302231454059)
      ·
        refine ⟨15469412200360953347181089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10312941466907302231454059 15469412200360953347181089)
        ·
          refine ⟨11602059150270715010385817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15469412200360953347181089 11602059150270715010385817)
          ·
            refine ⟨8701544362703036257789363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11602059150270715010385817 8701544362703036257789363)
            ·
              refine ⟨13052316544054554386684045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8701544362703036257789363 13052316544054554386684045)
              ·
                refine ⟨4894618704020457895006517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13052316544054554386684045 4894618704020457895006517)
                ·
                  refine ⟨458870503501917927656861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4894618704020457895006517 458870503501917927656861)
                  ·
                    rfl

theorem cell21_2010706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 3, 5].length) (baseStart_2010706 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2010706 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2010706 prefixEnd_2010706 := by exact prefixLift 2010706
  have htrace : WordTrace (prefixWord ++ tailWord_2010706) baseStart_2010706 baseEnd_2010706 := by
    simpa [prefixWord, tailWord_2010706, baseEnd_2010706] using wordTrace_append hprefix tailTrace_2010706
  have hstable : (prefixWord ++ tailWord_2010706).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2010706).length < 2 ^ (prefixWord ++ tailWord_2010706).sum := by decide
  have hdescent : baseEnd_2010706 < baseStart_2010706 := by decide
  rcases family_descends (prefixWord ++ tailWord_2010706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2010810 : List Nat := [3, 1, 1, 1, 2, 13]
def baseStart_2010810 : Nat := 118140960795 + 2010810 * 2 ^ 59
def prefixEnd_2010810 : Nat := 4983230072969 + 3 ^ 40 * 2010810 * 2
def baseEnd_2010810 : Nat := 16996082878475439182345

theorem tailTrace_2010810 : CollatzResearch.WordTrace tailWord_2010810 prefixEnd_2010810 16996082878475439182345 := by
  unfold tailWord_2010810
  simp only [CollatzResearch.WordTrace]
  refine ⟨18335066461296565963031471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48893510563457509234750589 18335066461296565963031471)
  ·
    refine ⟨27502599691944848944547207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18335066461296565963031471 27502599691944848944547207)
    ·
      refine ⟨41253899537917273416820811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27502599691944848944547207 41253899537917273416820811)
      ·
        refine ⟨61880849306875910125231217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41253899537917273416820811 61880849306875910125231217)
        ·
          refine ⟨46410636980156932593923413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61880849306875910125231217 46410636980156932593923413)
          ·
            refine ⟨16996082878475439182345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 46410636980156932593923413 16996082878475439182345)
            ·
              rfl

theorem cell21_2010810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 13].length) (baseStart_2010810 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2010810 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2010810 prefixEnd_2010810 := by exact prefixLift 2010810
  have htrace : WordTrace (prefixWord ++ tailWord_2010810) baseStart_2010810 baseEnd_2010810 := by
    simpa [prefixWord, tailWord_2010810, baseEnd_2010810] using wordTrace_append hprefix tailTrace_2010810
  have hstable : (prefixWord ++ tailWord_2010810).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2010810).length < 2 ^ (prefixWord ++ tailWord_2010810).sum := by decide
  have hdescent : baseEnd_2010810 < baseStart_2010810 := by decide
  rcases family_descends (prefixWord ++ tailWord_2010810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2010813 : List Nat := [1, 4, 1, 2, 1, 2, 4, 2, 4]
def baseStart_2010813 : Nat := 118140960795 + 2010813 * 2 ^ 59
def prefixEnd_2010813 : Nat := 4983230072969 + 3 ^ 40 * 2010813 * 2
def baseEnd_2010813 : Nat := 458894922359709519373309

theorem tailTrace_2010813 : CollatzResearch.WordTrace tailWord_2010813 prefixEnd_2010813 458894922359709519373309 := by
  unfold tailWord_2010813
  simp only [CollatzResearch.WordTrace]
  refine ⟨73340375264175395364485093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48893583509450263576323395 73340375264175395364485093)
  ·
    refine ⟨13751320362032886630840955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73340375264175395364485093 13751320362032886630840955)
    ·
      refine ⟨20626980543049329946261433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13751320362032886630840955 20626980543049329946261433)
      ·
        refine ⟨15470235407286997459696075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20626980543049329946261433 15470235407286997459696075)
        ·
          refine ⟨23205353110930496189544113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15470235407286997459696075 23205353110930496189544113)
          ·
            refine ⟨17404014833197872142158085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23205353110930496189544113 17404014833197872142158085)
            ·
              refine ⟨3263252781224601026654641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17404014833197872142158085 3263252781224601026654641)
              ·
                refine ⟨2447439585918450769990981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3263252781224601026654641 2447439585918450769990981)
                ·
                  refine ⟨458894922359709519373309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2447439585918450769990981 458894922359709519373309)
                  ·
                    rfl

theorem cell21_2010813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 4, 2, 4].length) (baseStart_2010813 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2010813 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2010813 prefixEnd_2010813 := by exact prefixLift 2010813
  have htrace : WordTrace (prefixWord ++ tailWord_2010813) baseStart_2010813 baseEnd_2010813 := by
    simpa [prefixWord, tailWord_2010813, baseEnd_2010813] using wordTrace_append hprefix tailTrace_2010813
  have hstable : (prefixWord ++ tailWord_2010813).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2010813).length < 2 ^ (prefixWord ++ tailWord_2010813).sum := by decide
  have hdescent : baseEnd_2010813 < baseStart_2010813 := by decide
  rcases family_descends (prefixWord ++ tailWord_2010813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2010841 : List Nat := [1, 2, 1, 2, 3, 3, 1, 1, 7]
def baseStart_2010841 : Nat := 118140960795 + 2010841 * 2 ^ 59
def prefixEnd_2010841 : Nat := 4983230072969 + 3 ^ 40 * 2010841 * 2
def baseEnd_2010841 : Nat := 458901312341187692906585

theorem tailTrace_2010841 : CollatzResearch.WordTrace tailWord_2010841 prefixEnd_2010841 458901312341187692906585 := by
  unfold tailWord_2010841
  simp only [CollatzResearch.WordTrace]
  refine ⟨73341396508073956146504377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48894264338715970764336251 73341396508073956146504377)
  ·
    refine ⟨55006047381055467109878283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73341396508073956146504377 55006047381055467109878283)
    ·
      refine ⟨82509071071583200664817425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55006047381055467109878283 82509071071583200664817425)
      ·
        refine ⟨61881803303687400498613069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82509071071583200664817425 61881803303687400498613069)
        ·
          refine ⟨23205676238882775186979901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61881803303687400498613069 23205676238882775186979901)
          ·
            refine ⟨8702128589581040695117463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23205676238882775186979901 8702128589581040695117463)
            ·
              refine ⟨13053192884371561042676195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8702128589581040695117463 13053192884371561042676195)
              ·
                refine ⟨19579789326557341564014293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13053192884371561042676195 19579789326557341564014293)
                ·
                  refine ⟨458901312341187692906585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19579789326557341564014293 458901312341187692906585)
                  ·
                    rfl

theorem cell21_2010841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 1, 7].length) (baseStart_2010841 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2010841 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2010841 prefixEnd_2010841 := by exact prefixLift 2010841
  have htrace : WordTrace (prefixWord ++ tailWord_2010841) baseStart_2010841 baseEnd_2010841 := by
    simpa [prefixWord, tailWord_2010841, baseEnd_2010841] using wordTrace_append hprefix tailTrace_2010841
  have hstable : (prefixWord ++ tailWord_2010841).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2010841).length < 2 ^ (prefixWord ++ tailWord_2010841).sum := by decide
  have hdescent : baseEnd_2010841 < baseStart_2010841 := by decide
  rcases family_descends (prefixWord ++ tailWord_2010841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2010872 : List Nat := [2, 1, 2, 1, 1, 2, 2, 6, 4]
def baseStart_2010872 : Nat := 118140960795 + 2010872 * 2 ^ 59
def prefixEnd_2010872 : Nat := 4983230072969 + 3 ^ 40 * 2010872 * 2
def baseEnd_2010872 : Nat := 458908386963538527889855

theorem tailTrace_2010872 : CollatzResearch.WordTrace tailWord_2010872 prefixEnd_2010872 458908386963538527889855 := by
  unfold tailWord_2010872
  simp only [CollatzResearch.WordTrace]
  refine ⟨36671263585480824220441435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48895018113974432293921913 36671263585480824220441435)
  ·
    refine ⟨55006895378221236330662153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36671263585480824220441435 55006895378221236330662153)
    ·
      refine ⟨41255171533665927247996615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55006895378221236330662153 41255171533665927247996615)
      ·
        refine ⟨61882757300498890871994923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41255171533665927247996615 61882757300498890871994923)
        ·
          refine ⟨92824135950748336307992385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61882757300498890871994923 92824135950748336307992385)
          ·
            refine ⟨69618101963061252230994289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92824135950748336307992385 69618101963061252230994289)
            ·
              refine ⟨52213576472295939173245717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69618101963061252230994289 52213576472295939173245717)
              ·
                refine ⟨2447511397138872148745893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 52213576472295939173245717 2447511397138872148745893)
                ·
                  refine ⟨458908386963538527889855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2447511397138872148745893 458908386963538527889855)
                  ·
                    rfl

theorem cell21_2010872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 6, 4].length) (baseStart_2010872 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2010872 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2010872 prefixEnd_2010872 := by exact prefixLift 2010872
  have htrace : WordTrace (prefixWord ++ tailWord_2010872) baseStart_2010872 baseEnd_2010872 := by
    simpa [prefixWord, tailWord_2010872, baseEnd_2010872] using wordTrace_append hprefix tailTrace_2010872
  have hstable : (prefixWord ++ tailWord_2010872).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2010872).length < 2 ^ (prefixWord ++ tailWord_2010872).sum := by decide
  have hdescent : baseEnd_2010872 < baseStart_2010872 := by decide
  rcases family_descends (prefixWord ++ tailWord_2010872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2010903 : List Nat := [1, 1, 3, 4, 2, 2, 1, 7]
def baseStart_2010903 : Nat := 118140960795 + 2010903 * 2 ^ 59
def prefixEnd_2010903 : Nat := 4983230072969 + 3 ^ 40 * 2010903 * 2
def baseEnd_2010903 : Nat := 152971820528629787624375

theorem tailTrace_2010903 : CollatzResearch.WordTrace tailWord_2010903 prefixEnd_2010903 152971820528629787624375 := by
  unfold tailWord_2010903
  simp only [CollatzResearch.WordTrace]
  refine ⟨73343657833849340735261363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48895771889232893823507575 73343657833849340735261363)
  ·
    refine ⟨110015486750774011102892045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73343657833849340735261363 110015486750774011102892045)
    ·
      refine ⟨41255807531540254163584517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110015486750774011102892045 41255807531540254163584517)
      ·
        refine ⟨7735463912163797655672097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41255807531540254163584517 7735463912163797655672097)
        ·
          refine ⟨5801597934122848241754073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7735463912163797655672097 5801597934122848241754073)
          ·
            refine ⟨4351198450592136181315555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5801597934122848241754073 4351198450592136181315555)
            ·
              refine ⟨6526797675888204271973333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4351198450592136181315555 6526797675888204271973333)
              ·
                refine ⟨152971820528629787624375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6526797675888204271973333 152971820528629787624375)
                ·
                  rfl

theorem cell21_2010903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 7].length) (baseStart_2010903 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2010903 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2010903 prefixEnd_2010903 := by exact prefixLift 2010903
  have htrace : WordTrace (prefixWord ++ tailWord_2010903) baseStart_2010903 baseEnd_2010903 := by
    simpa [prefixWord, tailWord_2010903, baseEnd_2010903] using wordTrace_append hprefix tailTrace_2010903
  have hstable : (prefixWord ++ tailWord_2010903).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2010903).length < 2 ^ (prefixWord ++ tailWord_2010903).sum := by decide
  have hdescent : baseEnd_2010903 < baseStart_2010903 := by decide
  rcases family_descends (prefixWord ++ tailWord_2010903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2010979 : List Nat := [1, 1, 1, 5, 5, 8]
def baseStart_2010979 : Nat := 118140960795 + 2010979 * 2 ^ 59
def prefixEnd_2010979 : Nat := 4983230072969 + 3 ^ 40 * 2010979 * 2
def baseEnd_2010979 : Nat := 16997511326715930355789

theorem tailTrace_2010979 : CollatzResearch.WordTrace tailWord_2010979 prefixEnd_2010979 16997511326715930355789 := by
  unfold tailWord_2010979
  simp only [CollatzResearch.WordTrace]
  refine ⟨73346429781574005715027991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48897619854382670476685327 73346429781574005715027991)
  ·
    refine ⟨110019644672361008572541987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73346429781574005715027991 110019644672361008572541987)
    ·
      refine ⟨165029467008541512858812981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110019644672361008572541987 165029467008541512858812981)
      ·
        refine ⟨15471512532050766830513717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 165029467008541512858812981 15471512532050766830513717)
        ·
          refine ⟨1450454299879759390360661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15471512532050766830513717 1450454299879759390360661)
          ·
            refine ⟨16997511326715930355789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1450454299879759390360661 16997511326715930355789)
            ·
              rfl

theorem cell21_2010979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 8].length) (baseStart_2010979 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2010979 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2010979 prefixEnd_2010979 := by exact prefixLift 2010979
  have htrace : WordTrace (prefixWord ++ tailWord_2010979) baseStart_2010979 baseEnd_2010979 := by
    simpa [prefixWord, tailWord_2010979, baseEnd_2010979] using wordTrace_append hprefix tailTrace_2010979
  have hstable : (prefixWord ++ tailWord_2010979).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2010979).length < 2 ^ (prefixWord ++ tailWord_2010979).sum := by decide
  have hdescent : baseEnd_2010979 < baseStart_2010979 := by decide
  rcases family_descends (prefixWord ++ tailWord_2010979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2010993 : List Nat := [1, 2, 2, 2, 1, 3, 2, 3, 5]
def baseStart_2010993 : Nat := 118140960795 + 2010993 * 2 ^ 59
def prefixEnd_2010993 : Nat := 4983230072969 + 3 ^ 40 * 2010993 * 2
def baseEnd_2010993 : Nat := 458936000812069206372941

theorem tailTrace_2010993 : CollatzResearch.WordTrace tailWord_2010993 prefixEnd_2010993 458936000812069206372941 := by
  unfold tailWord_2010993
  simp only [CollatzResearch.WordTrace]
  refine ⟨73346940403523286106037633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48897960269015524070691755 73346940403523286106037633)
  ·
    refine ⟨55010205302642464579528225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73346940403523286106037633 55010205302642464579528225)
    ·
      refine ⟨41257653976981848434646169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55010205302642464579528225 41257653976981848434646169)
      ·
        refine ⟨30943240482736386325984627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41257653976981848434646169 30943240482736386325984627)
        ·
          refine ⟨46414860724104579488976941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30943240482736386325984627 46414860724104579488976941)
          ·
            refine ⟨17405572771539217308366353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46414860724104579488976941 17405572771539217308366353)
            ·
              refine ⟨13054179578654412981274765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17405572771539217308366353 13054179578654412981274765)
              ·
                refine ⟨4895317341995404867978037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13054179578654412981274765 4895317341995404867978037)
                ·
                  refine ⟨458936000812069206372941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4895317341995404867978037 458936000812069206372941)
                  ·
                    rfl

theorem cell21_2010993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 3, 5].length) (baseStart_2010993 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2010993 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2010993 prefixEnd_2010993 := by exact prefixLift 2010993
  have htrace : WordTrace (prefixWord ++ tailWord_2010993) baseStart_2010993 baseEnd_2010993 := by
    simpa [prefixWord, tailWord_2010993, baseEnd_2010993] using wordTrace_append hprefix tailTrace_2010993
  have hstable : (prefixWord ++ tailWord_2010993).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2010993).length < 2 ^ (prefixWord ++ tailWord_2010993).sum := by decide
  have hdescent : baseEnd_2010993 < baseStart_2010993 := by decide
  rcases family_descends (prefixWord ++ tailWord_2010993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011007 : List Nat := [1, 1, 2, 2, 1, 1, 3, 2, 8]
def baseStart_2011007 : Nat := 118140960795 + 2011007 * 2 ^ 59
def prefixEnd_2011007 : Nat := 4983230072969 + 3 ^ 40 * 2011007 * 2
def baseEnd_2011007 : Nat := 458939195802808293139579

theorem tailTrace_2011007 : CollatzResearch.WordTrace tailWord_2011007 prefixEnd_2011007 458939195802808293139579 := by
  unfold tailWord_2011007
  simp only [CollatzResearch.WordTrace]
  refine ⟨73347451025472566497047275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48898300683648377664698183 73347451025472566497047275)
  ·
    refine ⟨110021176538208849745570913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73347451025472566497047275 110021176538208849745570913)
    ·
      refine ⟨82515882403656637309178185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110021176538208849745570913 82515882403656637309178185)
      ·
        refine ⟨61886911802742477981883639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82515882403656637309178185 61886911802742477981883639)
        ·
          refine ⟨92830367704113716972825459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61886911802742477981883639 92830367704113716972825459)
          ·
            refine ⟨139245551556170575459238189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92830367704113716972825459 139245551556170575459238189)
            ·
              refine ⟨52217081833563965797214321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139245551556170575459238189 52217081833563965797214321)
              ·
                refine ⟨39162811375172974347910741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52217081833563965797214321 39162811375172974347910741)
                ·
                  refine ⟨458939195802808293139579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39162811375172974347910741 458939195802808293139579)
                  ·
                    rfl

theorem cell21_2011007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 8].length) (baseStart_2011007 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2011007 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2011007 prefixEnd_2011007 := by exact prefixLift 2011007
  have htrace : WordTrace (prefixWord ++ tailWord_2011007) baseStart_2011007 baseEnd_2011007 := by
    simpa [prefixWord, tailWord_2011007, baseEnd_2011007] using wordTrace_append hprefix tailTrace_2011007
  have hstable : (prefixWord ++ tailWord_2011007).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011007).length < 2 ^ (prefixWord ++ tailWord_2011007).sum := by decide
  have hdescent : baseEnd_2011007 < baseStart_2011007 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011041 : List Nat := [1, 2, 3, 4, 2, 1, 1, 1, 6]
def baseStart_2011041 : Nat := 118140960795 + 2011041 * 2 ^ 59
def prefixEnd_2011041 : Nat := 4983230072969 + 3 ^ 40 * 2011041 * 2
def baseEnd_2011041 : Nat := 458946955066031789572843

theorem tailTrace_2011041 : CollatzResearch.WordTrace tailWord_2011041 prefixEnd_2011041 458946955066031789572843 := by
  unfold tailWord_2011041
  simp only [CollatzResearch.WordTrace]
  refine ⟨73348691107349390303784977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48899127404899593535856651 73348691107349390303784977)
  ·
    refine ⟨55011518330512042727838733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73348691107349390303784977 55011518330512042727838733)
    ·
      refine ⟨20629319373942016022939525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55011518330512042727838733 20629319373942016022939525)
      ·
        refine ⟨3867997382614128004301161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20629319373942016022939525 3867997382614128004301161)
        ·
          refine ⟨2900998036960596003225871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3867997382614128004301161 2900998036960596003225871)
          ·
            refine ⟨4351497055440894004838807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2900998036960596003225871 4351497055440894004838807)
            ·
              refine ⟨6527245583161341007258211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4351497055440894004838807 6527245583161341007258211)
              ·
                refine ⟨9790868374742011510887317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6527245583161341007258211 9790868374742011510887317)
                ·
                  refine ⟨458946955066031789572843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9790868374742011510887317 458946955066031789572843)
                  ·
                    rfl

theorem cell21_2011041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 1, 6].length) (baseStart_2011041 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2011041 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2011041 prefixEnd_2011041 := by exact prefixLift 2011041
  have htrace : WordTrace (prefixWord ++ tailWord_2011041) baseStart_2011041 baseEnd_2011041 := by
    simpa [prefixWord, tailWord_2011041, baseEnd_2011041] using wordTrace_append hprefix tailTrace_2011041
  have hstable : (prefixWord ++ tailWord_2011041).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011041).length < 2 ^ (prefixWord ++ tailWord_2011041).sum := by decide
  have hdescent : baseEnd_2011041 < baseStart_2011041 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011083 : List Nat := [1, 1, 1, 1, 3, 4, 1, 1, 8]
def baseStart_2011083 : Nat := 118140960795 + 2011083 * 2 ^ 59
def prefixEnd_2011083 : Nat := 4983230072969 + 3 ^ 40 * 2011083 * 2
def baseEnd_2011083 : Nat := 458956540038249049872757

theorem tailTrace_2011083 : CollatzResearch.WordTrace tailWord_2011083 prefixEnd_2011083 458956540038249049872757 := by
  unfold tailWord_2011083
  simp only [CollatzResearch.WordTrace]
  refine ⟨73350222973197231476813903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48900148648798154317875935 73350222973197231476813903)
  ·
    refine ⟨110025334459795847215220855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73350222973197231476813903 110025334459795847215220855)
    ·
      refine ⟨165038001689693770822831283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110025334459795847215220855 165038001689693770822831283)
      ·
        refine ⟨247557002534540656234246925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165038001689693770822831283 247557002534540656234246925)
        ·
          refine ⟨92833875950452746087842597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 247557002534540656234246925 92833875950452746087842597)
          ·
            refine ⟨17406351740709889891470487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92833875950452746087842597 17406351740709889891470487)
            ·
              refine ⟨26109527611064834837205731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17406351740709889891470487 26109527611064834837205731)
              ·
                refine ⟨39164291416597252255808597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26109527611064834837205731 39164291416597252255808597)
                ·
                  refine ⟨458956540038249049872757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39164291416597252255808597 458956540038249049872757)
                  ·
                    rfl

theorem cell21_2011083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 8].length) (baseStart_2011083 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2011083 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2011083 prefixEnd_2011083 := by exact prefixLift 2011083
  have htrace : WordTrace (prefixWord ++ tailWord_2011083) baseStart_2011083 baseEnd_2011083 := by
    simpa [prefixWord, tailWord_2011083, baseEnd_2011083] using wordTrace_append hprefix tailTrace_2011083
  have hstable : (prefixWord ++ tailWord_2011083).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011083).length < 2 ^ (prefixWord ++ tailWord_2011083).sum := by decide
  have hdescent : baseEnd_2011083 < baseStart_2011083 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011221 : List Nat := [1, 3, 2, 2, 1, 3, 1, 3, 5]
def baseStart_2011221 : Nat := 118140960795 + 2011221 * 2 ^ 59
def prefixEnd_2011221 : Nat := 4983230072969 + 3 ^ 40 * 2011221 * 2
def baseEnd_2011221 : Nat := 458988033518391476572475

theorem tailTrace_2011221 : CollatzResearch.WordTrace tailWord_2011221 prefixEnd_2011221 458988033518391476572475 := by
  unfold tailWord_2011221
  simp only [CollatzResearch.WordTrace]
  refine ⟨73355256246697281045337517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48903504164464854030225011 73355256246697281045337517)
  ·
    refine ⟨27508221092511480392001569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73355256246697281045337517 27508221092511480392001569)
    ·
      refine ⟨20631165819383610294001177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27508221092511480392001569 20631165819383610294001177)
      ·
        refine ⟨15473374364537707720500883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20631165819383610294001177 15473374364537707720500883)
        ·
          refine ⟨23210061546806561580751325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15473374364537707720500883 23210061546806561580751325)
          ·
            refine ⟨8703773080052460592781747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23210061546806561580751325 8703773080052460592781747)
            ·
              refine ⟨13055659620078690889172621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8703773080052460592781747 13055659620078690889172621)
              ·
                refine ⟨4895872357529509083439733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13055659620078690889172621 4895872357529509083439733)
                ·
                  refine ⟨458988033518391476572475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4895872357529509083439733 458988033518391476572475)
                  ·
                    rfl

theorem cell21_2011221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 3, 5].length) (baseStart_2011221 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2011221 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2011221 prefixEnd_2011221 := by exact prefixLift 2011221
  have htrace : WordTrace (prefixWord ++ tailWord_2011221) baseStart_2011221 baseEnd_2011221 := by
    simpa [prefixWord, tailWord_2011221, baseEnd_2011221] using wordTrace_append hprefix tailTrace_2011221
  have hstable : (prefixWord ++ tailWord_2011221).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011221).length < 2 ^ (prefixWord ++ tailWord_2011221).sum := by decide
  have hdescent : baseEnd_2011221 < baseStart_2011221 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011255 : List Nat := [1, 1, 3, 1, 1, 7, 1, 3, 3]
def baseStart_2011255 : Nat := 118140960795 + 2011255 * 2 ^ 59
def prefixEnd_2011255 : Nat := 4983230072969 + 3 ^ 40 * 2011255 * 2
def baseEnd_2011255 : Nat := 458995792781614973005739

theorem tailTrace_2011255 : CollatzResearch.WordTrace tailWord_2011255 prefixEnd_2011255 458995792781614973005739 := by
  unfold tailWord_2011255
  simp only [CollatzResearch.WordTrace]
  refine ⟨73356496328574104852075219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48904330885716069901383479 73356496328574104852075219)
  ·
    refine ⟨110034744492861157278112829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73356496328574104852075219 110034744492861157278112829)
    ·
      refine ⟨41263029184822933979292311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110034744492861157278112829 41263029184822933979292311)
      ·
        refine ⟨61894543777234400968938467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41263029184822933979292311 61894543777234400968938467)
        ·
          refine ⟨92841815665851601453407701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61894543777234400968938467 92841815665851601453407701)
          ·
            refine ⟨2175980054668396909064243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 92841815665851601453407701 2175980054668396909064243)
            ·
              refine ⟨3263970082002595363596365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2175980054668396909064243 3263970082002595363596365)
              ·
                refine ⟨1223988780750973261348637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3263970082002595363596365 1223988780750973261348637)
                ·
                  refine ⟨458995792781614973005739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1223988780750973261348637 458995792781614973005739)
                  ·
                    rfl

theorem cell21_2011255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 1, 3, 3].length) (baseStart_2011255 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2011255 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2011255 prefixEnd_2011255 := by exact prefixLift 2011255
  have htrace : WordTrace (prefixWord ++ tailWord_2011255) baseStart_2011255 baseEnd_2011255 := by
    simpa [prefixWord, tailWord_2011255, baseEnd_2011255] using wordTrace_append hprefix tailTrace_2011255
  have hstable : (prefixWord ++ tailWord_2011255).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011255).length < 2 ^ (prefixWord ++ tailWord_2011255).sum := by decide
  have hdescent : baseEnd_2011255 < baseStart_2011255 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011272 : List Nat := [2, 1, 3, 4, 1, 2, 3, 2, 3]
def baseStart_2011272 : Nat := 118140960795 + 2011272 * 2 ^ 59
def prefixEnd_2011272 : Nat := 4983230072969 + 3 ^ 40 * 2011272 * 2
def baseEnd_2011272 : Nat := 458999672413226721222371

theorem tailTrace_2011272 : CollatzResearch.WordTrace tailWord_2011272 prefixEnd_2011272 458999672413226721222371 := by
  unfold tailWord_2011272
  simp only [CollatzResearch.WordTrace]
  refine ⟨36678558184756258377722035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48904744246341677836962713 36678558184756258377722035)
  ·
    refine ⟨55017837277134387566583053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36678558184756258377722035 55017837277134387566583053)
    ·
      refine ⟨20631688978925395337468645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55017837277134387566583053 20631688978925395337468645)
      ·
        refine ⟨3868441683548511625775371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20631688978925395337468645 3868441683548511625775371)
        ·
          refine ⟨5802662525322767438663057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3868441683548511625775371 5802662525322767438663057)
          ·
            refine ⟨4351996893992075578997293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5802662525322767438663057 4351996893992075578997293)
            ·
              refine ⟨1631998835247028342123985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4351996893992075578997293 1631998835247028342123985)
              ·
                refine ⟨1223999126435271256592989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1631998835247028342123985 1223999126435271256592989)
                ·
                  refine ⟨458999672413226721222371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1223999126435271256592989 458999672413226721222371)
                  ·
                    rfl

theorem cell21_2011272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 3, 2, 3].length) (baseStart_2011272 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2011272 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2011272 prefixEnd_2011272 := by exact prefixLift 2011272
  have htrace : WordTrace (prefixWord ++ tailWord_2011272) baseStart_2011272 baseEnd_2011272 := by
    simpa [prefixWord, tailWord_2011272, baseEnd_2011272] using wordTrace_append hprefix tailTrace_2011272
  have hstable : (prefixWord ++ tailWord_2011272).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011272).length < 2 ^ (prefixWord ++ tailWord_2011272).sum := by decide
  have hdescent : baseEnd_2011272 < baseStart_2011272 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011314 : List Nat := [3, 2, 1, 1, 1, 3, 2, 5, 3]
def baseStart_2011314 : Nat := 118140960795 + 2011314 * 2 ^ 59
def prefixEnd_2011314 : Nat := 4983230072969 + 3 ^ 40 * 2011314 * 2
def baseEnd_2011314 : Nat := 459009257385443981522285

theorem tailTrace_2011314 : CollatzResearch.WordTrace tailWord_2011314 prefixEnd_2011314 459009257385443981522285 := by
  unfold tailWord_2011314
  simp only [CollatzResearch.WordTrace]
  refine ⟨18339662058840089482118249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48905765490240238618981997 18339662058840089482118249)
  ·
    refine ⟨13754746544130067111588687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18339662058840089482118249 13754746544130067111588687)
    ·
      refine ⟨20632119816195100667383031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13754746544130067111588687 20632119816195100667383031)
      ·
        refine ⟨30948179724292651001074547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20632119816195100667383031 30948179724292651001074547)
        ·
          refine ⟨46422269586438976501611821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30948179724292651001074547 46422269586438976501611821)
          ·
            refine ⟨17408351094914616188104433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46422269586438976501611821 17408351094914616188104433)
            ·
              refine ⟨13056263321185962141078325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17408351094914616188104433 13056263321185962141078325)
              ·
                refine ⟨1224024686361183950726093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13056263321185962141078325 1224024686361183950726093)
                ·
                  refine ⟨459009257385443981522285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1224024686361183950726093 459009257385443981522285)
                  ·
                    rfl

theorem cell21_2011314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 5, 3].length) (baseStart_2011314 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2011314 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2011314 prefixEnd_2011314 := by exact prefixLift 2011314
  have htrace : WordTrace (prefixWord ++ tailWord_2011314) baseStart_2011314 baseEnd_2011314 := by
    simpa [prefixWord, tailWord_2011314, baseEnd_2011314] using wordTrace_append hprefix tailTrace_2011314
  have hstable : (prefixWord ++ tailWord_2011314).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011314).length < 2 ^ (prefixWord ++ tailWord_2011314).sum := by decide
  have hdescent : baseEnd_2011314 < baseStart_2011314 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011328 : List Nat := [2, 1, 1, 2, 5, 1, 1, 4, 4]
def baseStart_2011328 : Nat := 118140960795 + 2011328 * 2 ^ 59
def prefixEnd_2011328 : Nat := 4983230072969 + 3 ^ 40 * 2011328 * 2
def baseEnd_2011328 : Nat := 459012452376183068288923

theorem tailTrace_2011328 : CollatzResearch.WordTrace tailWord_2011328 prefixEnd_2011328 459012452376183068288923 := by
  unfold tailWord_2011328
  simp only [CollatzResearch.WordTrace]
  refine ⟨36679579428654819159741319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48906105904873092212988425 36679579428654819159741319)
  ·
    refine ⟨55019369142982228739611979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36679579428654819159741319 55019369142982228739611979)
    ·
      refine ⟨82529053714473343109417969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55019369142982228739611979 82529053714473343109417969)
      ·
        refine ⟨61896790285855007332063477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82529053714473343109417969 61896790285855007332063477)
        ·
          refine ⟨5802824089298906937380951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 61896790285855007332063477 5802824089298906937380951)
          ·
            refine ⟨8704236133948360406071427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5802824089298906937380951 8704236133948360406071427)
            ·
              refine ⟨13056354200922540609107141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8704236133948360406071427 13056354200922540609107141)
              ·
                refine ⟨2448066412672976364207589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13056354200922540609107141 2448066412672976364207589)
                ·
                  refine ⟨459012452376183068288923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2448066412672976364207589 459012452376183068288923)
                  ·
                    rfl

theorem cell21_2011328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 4, 4].length) (baseStart_2011328 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2011328 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2011328 prefixEnd_2011328 := by exact prefixLift 2011328
  have htrace : WordTrace (prefixWord ++ tailWord_2011328) baseStart_2011328 baseEnd_2011328 := by
    simpa [prefixWord, tailWord_2011328, baseEnd_2011328] using wordTrace_append hprefix tailTrace_2011328
  have hstable : (prefixWord ++ tailWord_2011328).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011328).length < 2 ^ (prefixWord ++ tailWord_2011328).sum := by decide
  have hdescent : baseEnd_2011328 < baseStart_2011328 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011390 : List Nat := [4, 2, 2, 1, 1, 1, 4, 1, 5]
def baseStart_2011390 : Nat := 118140960795 + 2011390 * 2 ^ 59
def prefixEnd_2011390 : Nat := 4983230072969 + 3 ^ 40 * 2011390 * 2
def baseEnd_2011390 : Nat := 459026601620884738255463

theorem tailTrace_2011390 : CollatzResearch.WordTrace tailWord_2011390 prefixEnd_2011390 459026601620884738255463 := by
  unfold tailWord_2011390
  simp only [CollatzResearch.WordTrace]
  refine ⟨9170177522885627863529953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48907613455390015272159749 9170177522885627863529953)
  ·
    refine ⟨6877633142164220897647465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9170177522885627863529953 6877633142164220897647465)
    ·
      refine ⟨5158224856623165673235599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6877633142164220897647465 5158224856623165673235599)
      ·
        refine ⟨7737337284934748509853399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5158224856623165673235599 7737337284934748509853399)
        ·
          refine ⟨11606005927402122764780099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7737337284934748509853399 11606005927402122764780099)
          ·
            refine ⟨17409008891103184147170149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11606005927402122764780099 17409008891103184147170149)
            ·
              refine ⟨3264189167081847027594403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17409008891103184147170149 3264189167081847027594403)
              ·
                refine ⟨4896283750622770541391605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3264189167081847027594403 4896283750622770541391605)
                ·
                  refine ⟨459026601620884738255463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4896283750622770541391605 459026601620884738255463)
                  ·
                    rfl

theorem cell21_2011390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 4, 1, 5].length) (baseStart_2011390 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2011390 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2011390 prefixEnd_2011390 := by exact prefixLift 2011390
  have htrace : WordTrace (prefixWord ++ tailWord_2011390) baseStart_2011390 baseEnd_2011390 := by
    simpa [prefixWord, tailWord_2011390, baseEnd_2011390] using wordTrace_append hprefix tailTrace_2011390
  have hstable : (prefixWord ++ tailWord_2011390).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011390).length < 2 ^ (prefixWord ++ tailWord_2011390).sum := by decide
  have hdescent : baseEnd_2011390 < baseStart_2011390 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011486 : List Nat := [4, 4, 2, 1, 2, 8]
def baseStart_2011486 : Nat := 118140960795 + 2011486 * 2 ^ 59
def prefixEnd_2011486 : Nat := 4983230072969 + 3 ^ 40 * 2011486 * 2
def baseEnd_2011486 : Nat := 17001796671437403876121

theorem tailTrace_2011486 : CollatzResearch.WordTrace tailWord_2011486 prefixEnd_2011486 17001796671437403876121 := by
  unfold tailWord_2011486
  simp only [CollatzResearch.WordTrace]
  refine ⟨9170615198842153912966789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48909947727158154202489541 9170615198842153912966789)
  ·
    refine ⟨1719490349782903858681273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9170615198842153912966789 1719490349782903858681273)
    ·
      refine ⟨1289617762337177894010955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1719490349782903858681273 1289617762337177894010955)
      ·
        refine ⟨1934426643505766841016433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1289617762337177894010955 1934426643505766841016433)
        ·
          refine ⟨1450819982629325130762325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1934426643505766841016433 1450819982629325130762325)
          ·
            refine ⟨17001796671437403876121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1450819982629325130762325 17001796671437403876121)
            ·
              rfl

theorem cell21_2011486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 8].length) (baseStart_2011486 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2011486 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2011486 prefixEnd_2011486 := by exact prefixLift 2011486
  have htrace : WordTrace (prefixWord ++ tailWord_2011486) baseStart_2011486 baseEnd_2011486 := by
    simpa [prefixWord, tailWord_2011486, baseEnd_2011486] using wordTrace_append hprefix tailTrace_2011486
  have hstable : (prefixWord ++ tailWord_2011486).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011486).length < 2 ^ (prefixWord ++ tailWord_2011486).sum := by decide
  have hdescent : baseEnd_2011486 < baseStart_2011486 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011500 : List Nat := [2, 2, 1, 1, 6, 2, 2, 2, 3]
def baseStart_2011500 : Nat := 118140960795 + 2011500 * 2 ^ 59
def prefixEnd_2011500 : Nat := 4983230072969 + 3 ^ 40 * 2011500 * 2
def baseEnd_2011500 : Nat := 459051705119548991421905

theorem tailTrace_2011500 : CollatzResearch.WordTrace tailWord_2011500 prefixEnd_2011500 459051705119548991421905 := by
  unfold tailWord_2011500
  simp only [CollatzResearch.WordTrace]
  refine ⟨36682716106343255847371977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48910288141791007796495969 36682716106343255847371977)
  ·
    refine ⟨27512037079757441885528983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36682716106343255847371977 27512037079757441885528983)
    ·
      refine ⟨41268055619636162828293475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27512037079757441885528983 41268055619636162828293475)
      ·
        refine ⟨61902083429454244242440213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41268055619636162828293475 61902083429454244242440213)
        ·
          refine ⟨2901660160755667698864385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 61902083429454244242440213 2901660160755667698864385)
          ·
            refine ⟨2176245120566750774148289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2901660160755667698864385 2176245120566750774148289)
            ·
              refine ⟨1632183840425063080611217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2176245120566750774148289 1632183840425063080611217)
              ·
                refine ⟨1224137880318797310458413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1632183840425063080611217 1224137880318797310458413)
                ·
                  refine ⟨459051705119548991421905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1224137880318797310458413 459051705119548991421905)
                  ·
                    rfl

theorem cell21_2011500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 2, 2, 3].length) (baseStart_2011500 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2011500 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2011500 prefixEnd_2011500 := by exact prefixLift 2011500
  have htrace : WordTrace (prefixWord ++ tailWord_2011500) baseStart_2011500 baseEnd_2011500 := by
    simpa [prefixWord, tailWord_2011500, baseEnd_2011500] using wordTrace_append hprefix tailTrace_2011500
  have hstable : (prefixWord ++ tailWord_2011500).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011500).length < 2 ^ (prefixWord ++ tailWord_2011500).sum := by decide
  have hdescent : baseEnd_2011500 < baseStart_2011500 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011556 : List Nat := [2, 3, 1, 2, 1, 1, 5, 2, 4]
def baseStart_2011556 : Nat := 118140960795 + 2011556 * 2 ^ 59
def prefixEnd_2011556 : Nat := 4983230072969 + 3 ^ 40 * 2011556 * 2
def baseEnd_2011556 : Nat := 459064485082505338488457

theorem tailTrace_2011556 : CollatzResearch.WordTrace tailWord_2011556 prefixEnd_2011556 459064485082505338488457 := by
  unfold tailWord_2011556
  simp only [CollatzResearch.WordTrace]
  refine ⟨36683737350241816629391261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48911649800322422172521681 36683737350241816629391261)
  ·
    refine ⟨13756401506340681236021723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36683737350241816629391261 13756401506340681236021723)
    ·
      refine ⟨20634602259511021854032585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13756401506340681236021723 20634602259511021854032585)
      ·
        refine ⟨15475951694633266390524439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20634602259511021854032585 15475951694633266390524439)
        ·
          refine ⟨23213927541949899585786659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15475951694633266390524439 23213927541949899585786659)
          ·
            refine ⟨34820891312924849378679989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23213927541949899585786659 34820891312924849378679989)
            ·
              refine ⟨3264458560586704629251249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34820891312924849378679989 3264458560586704629251249)
              ·
                refine ⟨2448343920440028471938437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3264458560586704629251249 2448343920440028471938437)
                ·
                  refine ⟨459064485082505338488457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2448343920440028471938437 459064485082505338488457)
                  ·
                    rfl

theorem cell21_2011556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5, 2, 4].length) (baseStart_2011556 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2011556 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2011556 prefixEnd_2011556 := by exact prefixLift 2011556
  have htrace : WordTrace (prefixWord ++ tailWord_2011556) baseStart_2011556 baseEnd_2011556 := by
    simpa [prefixWord, tailWord_2011556, baseEnd_2011556] using wordTrace_append hprefix tailTrace_2011556
  have hstable : (prefixWord ++ tailWord_2011556).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011556).length < 2 ^ (prefixWord ++ tailWord_2011556).sum := by decide
  have hdescent : baseEnd_2011556 < baseStart_2011556 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011615 : List Nat := [1, 1, 2, 3, 3, 2, 2, 1, 6]
def baseStart_2011615 : Nat := 118140960795 + 2011615 * 2 ^ 59
def prefixEnd_2011615 : Nat := 4983230072969 + 3 ^ 40 * 2011615 * 2
def baseEnd_2011615 : Nat := 459077949686334347005003

theorem tailTrace_2011615 : CollatzResearch.WordTrace tailWord_2011615 prefixEnd_2011615 459077949686334347005003 := by
  unfold tailWord_2011615
  simp only [CollatzResearch.WordTrace]
  refine ⟨73369626607269886335180299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48913084404846590890120199 73369626607269886335180299)
  ·
    refine ⟨110054439910904829502770449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73369626607269886335180299 110054439910904829502770449)
    ·
      refine ⟨82540829933178622127077837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110054439910904829502770449 82540829933178622127077837)
      ·
        refine ⟨30952811224941983297654189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82540829933178622127077837 30952811224941983297654189)
        ·
          refine ⟨11607304209353243736620321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30952811224941983297654189 11607304209353243736620321)
          ·
            refine ⟨8705478157014932802465241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11607304209353243736620321 8705478157014932802465241)
            ·
              refine ⟨6529108617761199601848931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8705478157014932802465241 6529108617761199601848931)
              ·
                refine ⟨9793662926641799402773397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6529108617761199601848931 9793662926641799402773397)
                ·
                  refine ⟨459077949686334347005003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9793662926641799402773397 459077949686334347005003)
                  ·
                    rfl

theorem cell21_2011615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 1, 6].length) (baseStart_2011615 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2011615 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2011615 prefixEnd_2011615 := by exact prefixLift 2011615
  have htrace : WordTrace (prefixWord ++ tailWord_2011615) baseStart_2011615 baseEnd_2011615 := by
    simpa [prefixWord, tailWord_2011615, baseEnd_2011615] using wordTrace_append hprefix tailTrace_2011615
  have hstable : (prefixWord ++ tailWord_2011615).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011615).length < 2 ^ (prefixWord ++ tailWord_2011615).sum := by decide
  have hdescent : baseEnd_2011615 < baseStart_2011615 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011680 : List Nat := [2, 1, 1, 6, 3, 1, 1, 6]
def baseStart_2011680 : Nat := 118140960795 + 2011680 * 2 ^ 59
def prefixEnd_2011680 : Nat := 4983230072969 + 3 ^ 40 * 2011680 * 2
def baseEnd_2011680 : Nat := 153030927857302892807179

theorem tailTrace_2011680 : CollatzResearch.WordTrace tailWord_2011680 prefixEnd_2011680 153030927857302892807179 := by
  unfold tailWord_2011680
  simp only [CollatzResearch.WordTrace]
  refine ⟨36685998676017201218148247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48914664901356268290864329 36685998676017201218148247)
  ·
    refine ⟨55028998014025801827222371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36685998676017201218148247 55028998014025801827222371)
    ·
      refine ⟨82543497021038702740833557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55028998014025801827222371 82543497021038702740833557)
      ·
        refine ⟨3869226422861189190976573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 82543497021038702740833557 3869226422861189190976573)
        ·
          refine ⟨1450959908572945946616215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3869226422861189190976573 1450959908572945946616215)
          ·
            refine ⟨2176439862859418919924323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1450959908572945946616215 2176439862859418919924323)
            ·
              refine ⟨3264659794289128379886485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2176439862859418919924323 3264659794289128379886485)
              ·
                refine ⟨153030927857302892807179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3264659794289128379886485 153030927857302892807179)
                ·
                  rfl

theorem cell21_2011680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 1, 6].length) (baseStart_2011680 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2011680 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2011680 prefixEnd_2011680 := by exact prefixLift 2011680
  have htrace : WordTrace (prefixWord ++ tailWord_2011680) baseStart_2011680 baseEnd_2011680 := by
    simpa [prefixWord, tailWord_2011680, baseEnd_2011680] using wordTrace_append hprefix tailTrace_2011680
  have hstable : (prefixWord ++ tailWord_2011680).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011680).length < 2 ^ (prefixWord ++ tailWord_2011680).sum := by decide
  have hdescent : baseEnd_2011680 < baseStart_2011680 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011694 : List Nat := [4, 1, 3, 1, 3, 1, 1, 2, 5]
def baseStart_2011694 : Nat := 118140960795 + 2011694 * 2 ^ 59
def prefixEnd_2011694 : Nat := 4983230072969 + 3 ^ 40 * 2011694 * 2
def baseEnd_2011694 : Nat := 459095978562647765188175

theorem tailTrace_2011694 : CollatzResearch.WordTrace tailWord_2011694 prefixEnd_2011694 459095978562647765188175 := by
  unfold tailWord_2011694
  simp only [CollatzResearch.WordTrace]
  refine ⟨9171563496747960353413267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48915005315989121884870757 9171563496747960353413267)
  ·
    refine ⟨13757345245121940530119901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9171563496747960353413267 13757345245121940530119901)
    ·
      refine ⟨5159004466920727698794963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13757345245121940530119901 5159004466920727698794963)
      ·
        refine ⟨7738506700381091548192445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5159004466920727698794963 7738506700381091548192445)
        ·
          refine ⟨2901940012642909330572167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7738506700381091548192445 2901940012642909330572167)
          ·
            refine ⟨4352910018964363995858251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2901940012642909330572167 4352910018964363995858251)
            ·
              refine ⟨6529365028446545993787377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4352910018964363995858251 6529365028446545993787377)
              ·
                refine ⟨4897023771334909495340533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6529365028446545993787377 4897023771334909495340533)
                ·
                  refine ⟨459095978562647765188175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4897023771334909495340533 459095978562647765188175)
                  ·
                    rfl

theorem cell21_2011694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 2, 5].length) (baseStart_2011694 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2011694 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2011694 prefixEnd_2011694 := by exact prefixLift 2011694
  have htrace : WordTrace (prefixWord ++ tailWord_2011694) baseStart_2011694 baseEnd_2011694 := by
    simpa [prefixWord, tailWord_2011694, baseEnd_2011694] using wordTrace_append hprefix tailTrace_2011694
  have hstable : (prefixWord ++ tailWord_2011694).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011694).length < 2 ^ (prefixWord ++ tailWord_2011694).sum := by decide
  have hdescent : baseEnd_2011694 < baseStart_2011694 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
