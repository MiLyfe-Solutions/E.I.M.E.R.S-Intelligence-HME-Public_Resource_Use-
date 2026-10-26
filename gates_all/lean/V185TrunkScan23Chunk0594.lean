import V185TrunkScan23Chunk0593

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3511691 : List Nat := [1, 1, 1, 1, 4, 3, 4, 1, 1, 3, 3]
def baseStart_3511691 : Nat := 118140960795 + 3511691 * 2 ^ 59
def prefixEnd_3511691 : Nat := 4983230072969 + 3 ^ 40 * 3511691 * 2
def baseEnd_3511691 : Nat := 1803185393068125226512533

theorem tailTrace_3511691 : CollatzResearch.WordTrace tailWord_3511691 prefixEnd_3511691 1803185393068125226512533 := by
  unfold tailWord_3511691
  simp only [CollatzResearch.WordTrace]
  refine ⟨128081893120750730919446927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85387928747167153946297951 128081893120750730919446927)
  ·
    refine ⟨192122839681126096379170391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128081893120750730919446927 192122839681126096379170391)
    ·
      refine ⟨288184259521689144568755587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192122839681126096379170391 288184259521689144568755587)
      ·
        refine ⟨432276389282533716853133381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288184259521689144568755587 432276389282533716853133381)
        ·
          refine ⟨81051822990475071909962509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 432276389282533716853133381 81051822990475071909962509)
          ·
            refine ⟨30394433621428151966235941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81051822990475071909962509 30394433621428151966235941)
            ·
              refine ⟨5698956304017778493669239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30394433621428151966235941 5698956304017778493669239)
              ·
                refine ⟨8548434456026667740503859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5698956304017778493669239 8548434456026667740503859)
                ·
                  refine ⟨12822651684040001610755789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8548434456026667740503859 12822651684040001610755789)
                  ·
                    refine ⟨4808494381515000604033421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12822651684040001610755789 4808494381515000604033421)
                    ·
                      refine ⟨1803185393068125226512533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4808494381515000604033421 1803185393068125226512533)
                      ·
                        rfl

theorem cell23_3511691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 4, 1, 1, 3, 3].length) (baseStart_3511691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3511691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3511691 prefixEnd_3511691 := by exact prefixLift 3511691
  have htrace : WordTrace (prefixWord ++ tailWord_3511691) baseStart_3511691 baseEnd_3511691 := by
    simpa [prefixWord, tailWord_3511691, baseEnd_3511691] using wordTrace_append hprefix tailTrace_3511691
  have hstable : (prefixWord ++ tailWord_3511691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3511691).length < 2 ^ (prefixWord ++ tailWord_3511691).sum := by decide
  have hdescent : baseEnd_3511691 < baseStart_3511691 := by decide
  rcases family_descends (prefixWord ++ tailWord_3511691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3511724 : List Nat := [2, 2, 1, 1, 1, 1, 5, 2, 2, 6]
def baseStart_3511724 : Nat := 118140960795 + 3511724 * 2 ^ 59
def prefixEnd_3511724 : Nat := 4983230072969 + 3 ^ 40 * 3511724 * 2
def baseEnd_3511724 : Nat := 601067445976574532466627

theorem tailTrace_3511724 : CollatzResearch.WordTrace tailWord_3511724 prefixEnd_3511724 601067445976574532466627 := by
  unfold tailWord_3511724
  simp only [CollatzResearch.WordTrace]
  refine ⟨64041548364815588777699113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85388731153087451703598817 64041548364815588777699113)
  ·
    refine ⟨48031161273611691583274335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64041548364815588777699113 48031161273611691583274335)
    ·
      refine ⟨72046741910417537374911503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48031161273611691583274335 72046741910417537374911503)
      ·
        refine ⟨108070112865626306062367255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72046741910417537374911503 108070112865626306062367255)
        ·
          refine ⟨162105169298439459093550883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108070112865626306062367255 162105169298439459093550883)
          ·
            refine ⟨243157753947659188640326325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162105169298439459093550883 243157753947659188640326325)
            ·
              refine ⟨22796039432593048935030593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 243157753947659188640326325 22796039432593048935030593)
              ·
                refine ⟨17097029574444786701272945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22796039432593048935030593 17097029574444786701272945)
                ·
                  refine ⟨12822772180833590025954709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17097029574444786701272945 12822772180833590025954709)
                  ·
                    refine ⟨601067445976574532466627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12822772180833590025954709 601067445976574532466627)
                    ·
                      rfl

theorem cell23_3511724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 6].length) (baseStart_3511724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3511724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3511724 prefixEnd_3511724 := by exact prefixLift 3511724
  have htrace : WordTrace (prefixWord ++ tailWord_3511724) baseStart_3511724 baseEnd_3511724 := by
    simpa [prefixWord, tailWord_3511724, baseEnd_3511724] using wordTrace_append hprefix tailTrace_3511724
  have hstable : (prefixWord ++ tailWord_3511724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3511724).length < 2 ^ (prefixWord ++ tailWord_3511724).sum := by decide
  have hdescent : baseEnd_3511724 < baseStart_3511724 := by decide
  rcases family_descends (prefixWord ++ tailWord_3511724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3511725 : List Nat := [1, 5, 2, 2, 1, 2, 1, 1, 4, 1, 3]
def baseStart_3511725 : Nat := 118140960795 + 3511725 * 2 ^ 59
def prefixEnd_3511725 : Nat := 4983230072969 + 3 ^ 40 * 3511725 * 2
def baseEnd_3511725 : Nat := 1803202851410378093487377

theorem tailTrace_3511725 : CollatzResearch.WordTrace tailWord_3511725 prefixEnd_3511725 1803202851410378093487377 := by
  unfold tailWord_3511725
  simp only [CollatzResearch.WordTrace]
  refine ⟨128083133202627554726184629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85388755468418369817456419 128083133202627554726184629)
  ·
    refine ⟨12007793737746333255579809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 128083133202627554726184629 12007793737746333255579809)
    ·
      refine ⟨9005845303309749941684857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12007793737746333255579809 9005845303309749941684857)
      ·
        refine ⟨6754383977482312456263643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9005845303309749941684857 6754383977482312456263643)
        ·
          refine ⟨10131575966223468684395465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6754383977482312456263643 10131575966223468684395465)
          ·
            refine ⟨7598681974667601513296599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10131575966223468684395465 7598681974667601513296599)
            ·
              refine ⟨11398022962001402269944899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7598681974667601513296599 11398022962001402269944899)
              ·
                refine ⟨17097034443002103404917349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11398022962001402269944899 17097034443002103404917349)
                ·
                  refine ⟨3205693958062894388422003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17097034443002103404917349 3205693958062894388422003)
                  ·
                    refine ⟨4808540937094341582633005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3205693958062894388422003 4808540937094341582633005)
                    ·
                      refine ⟨1803202851410378093487377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4808540937094341582633005 1803202851410378093487377)
                      ·
                        rfl

theorem cell23_3511725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_3511725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3511725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3511725 prefixEnd_3511725 := by exact prefixLift 3511725
  have htrace : WordTrace (prefixWord ++ tailWord_3511725) baseStart_3511725 baseEnd_3511725 := by
    simpa [prefixWord, tailWord_3511725, baseEnd_3511725] using wordTrace_append hprefix tailTrace_3511725
  have hstable : (prefixWord ++ tailWord_3511725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3511725).length < 2 ^ (prefixWord ++ tailWord_3511725).sum := by decide
  have hdescent : baseEnd_3511725 < baseStart_3511725 := by decide
  rcases family_descends (prefixWord ++ tailWord_3511725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3511731 : List Nat := [1, 1, 1, 2, 3, 1, 1, 4, 3, 4, 2]
def baseStart_3511731 : Nat := 118140960795 + 3511731 * 2 ^ 59
def prefixEnd_3511731 : Nat := 4983230072969 + 3 ^ 40 * 3511731 * 2
def baseEnd_3511731 : Nat := 1803205932294305070012349

theorem tailTrace_3511731 : CollatzResearch.WordTrace tailWord_3511731 prefixEnd_3511731 1803205932294305070012349 := by
  unfold tailWord_3511731
  simp only [CollatzResearch.WordTrace]
  refine ⟨128083352040605817750903047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85388901360403878500602031 128083352040605817750903047)
  ·
    refine ⟨192125028060908726626354571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128083352040605817750903047 192125028060908726626354571)
    ·
      refine ⟨288187542091363089939531857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192125028060908726626354571 288187542091363089939531857)
      ·
        refine ⟨216140656568522317454648893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 288187542091363089939531857 216140656568522317454648893)
        ·
          refine ⟨81052746213195869045493335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 216140656568522317454648893 81052746213195869045493335)
          ·
            refine ⟨121579119319793803568240003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81052746213195869045493335 121579119319793803568240003)
            ·
              refine ⟨182368678979690705352360005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121579119319793803568240003 182368678979690705352360005)
              ·
                refine ⟨34194127308692007253567501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 182368678979690705352360005 34194127308692007253567501)
                ·
                  refine ⟨12822797740759502720087813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34194127308692007253567501 12822797740759502720087813)
                  ·
                    refine ⟨2404274576392406760016465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12822797740759502720087813 2404274576392406760016465)
                    ·
                      refine ⟨1803205932294305070012349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2404274576392406760016465 1803205932294305070012349)
                      ·
                        rfl

theorem cell23_3511731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 4, 3, 4, 2].length) (baseStart_3511731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3511731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3511731 prefixEnd_3511731 := by exact prefixLift 3511731
  have htrace : WordTrace (prefixWord ++ tailWord_3511731) baseStart_3511731 baseEnd_3511731 := by
    simpa [prefixWord, tailWord_3511731, baseEnd_3511731] using wordTrace_append hprefix tailTrace_3511731
  have hstable : (prefixWord ++ tailWord_3511731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3511731).length < 2 ^ (prefixWord ++ tailWord_3511731).sum := by decide
  have hdescent : baseEnd_3511731 < baseStart_3511731 := by decide
  rcases family_descends (prefixWord ++ tailWord_3511731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3511746 : List Nat := [3, 5, 2, 1, 1, 1, 2, 2, 1, 2, 3]
def baseStart_3511746 : Nat := 118140960795 + 3511746 * 2 ^ 59
def prefixEnd_3511746 : Nat := 4983230072969 + 3 ^ 40 * 3511746 * 2
def baseEnd_3511746 : Nat := 1803213634504122511324781

theorem tailTrace_3511746 : CollatzResearch.WordTrace tailWord_3511746 prefixEnd_3511746 1803213634504122511324781 := by
  unfold tailWord_3511746
  simp only [CollatzResearch.WordTrace]
  refine ⟨32020974783887868828174773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85389266090367650208466061 32020974783887868828174773)
  ·
    refine ⟨3001966385989487702641385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32020974783887868828174773 3001966385989487702641385)
    ·
      refine ⟨2251474789492115776981039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3001966385989487702641385 2251474789492115776981039)
      ·
        refine ⟨3377212184238173665471559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2251474789492115776981039 3377212184238173665471559)
        ·
          refine ⟨5065818276357260498207339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3377212184238173665471559 5065818276357260498207339)
          ·
            refine ⟨7598727414535890747311009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5065818276357260498207339 7598727414535890747311009)
            ·
              refine ⟨5699045560901918060483257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7598727414535890747311009 5699045560901918060483257)
              ·
                refine ⟨4274284170676438545362443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5699045560901918060483257 4274284170676438545362443)
                ·
                  refine ⟨6411426256014657818043665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4274284170676438545362443 6411426256014657818043665)
                  ·
                    refine ⟨4808569692010993363532749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6411426256014657818043665 4808569692010993363532749)
                    ·
                      refine ⟨1803213634504122511324781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4808569692010993363532749 1803213634504122511324781)
                      ·
                        rfl

theorem cell23_3511746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_3511746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3511746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3511746 prefixEnd_3511746 := by exact prefixLift 3511746
  have htrace : WordTrace (prefixWord ++ tailWord_3511746) baseStart_3511746 baseEnd_3511746 := by
    simpa [prefixWord, tailWord_3511746, baseEnd_3511746] using wordTrace_append hprefix tailTrace_3511746
  have hstable : (prefixWord ++ tailWord_3511746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3511746).length < 2 ^ (prefixWord ++ tailWord_3511746).sum := by decide
  have hdescent : baseEnd_3511746 < baseStart_3511746 := by decide
  rcases family_descends (prefixWord ++ tailWord_3511746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3511818 : List Nat := [3, 1, 2, 2, 2, 3, 2, 1, 2, 5]
def baseStart_3511818 : Nat := 118140960795 + 3511818 * 2 ^ 59
def prefixEnd_3511818 : Nat := 4983230072969 + 3 ^ 40 * 3511818 * 2
def baseEnd_3511818 : Nat := 601083535037082076541483

theorem tailTrace_3511818 : CollatzResearch.WordTrace tailWord_3511818 prefixEnd_3511818 601083535037082076541483 := by
  unfold tailWord_3511818
  simp only [CollatzResearch.WordTrace]
  refine ⟨32021631297822657902330027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85391016794193754406213405 32021631297822657902330027)
  ·
    refine ⟨48032446946733986853495041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32021631297822657902330027 48032446946733986853495041)
    ·
      refine ⟨36024335210050490140121281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48032446946733986853495041 36024335210050490140121281)
      ·
        refine ⟨27018251407537867605090961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36024335210050490140121281 27018251407537867605090961)
        ·
          refine ⟨20263688555653400703818221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27018251407537867605090961 20263688555653400703818221)
          ·
            refine ⟨7598883208370025263931833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20263688555653400703818221 7598883208370025263931833)
            ·
              refine ⟨5699162406277518947948875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7598883208370025263931833 5699162406277518947948875)
              ·
                refine ⟨8548743609416278421923313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5699162406277518947948875 8548743609416278421923313)
                ·
                  refine ⟨6411557707062208816442485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8548743609416278421923313 6411557707062208816442485)
                  ·
                    refine ⟨601083535037082076541483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6411557707062208816442485 601083535037082076541483)
                    ·
                      rfl

theorem cell23_3511818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 2, 1, 2, 5].length) (baseStart_3511818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3511818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3511818 prefixEnd_3511818 := by exact prefixLift 3511818
  have htrace : WordTrace (prefixWord ++ tailWord_3511818) baseStart_3511818 baseEnd_3511818 := by
    simpa [prefixWord, tailWord_3511818, baseEnd_3511818] using wordTrace_append hprefix tailTrace_3511818
  have hstable : (prefixWord ++ tailWord_3511818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3511818).length < 2 ^ (prefixWord ++ tailWord_3511818).sum := by decide
  have hdescent : baseEnd_3511818 < baseStart_3511818 := by decide
  rcases family_descends (prefixWord ++ tailWord_3511818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3511888 : List Nat := [2, 1, 1, 1, 1, 3, 3, 2, 5, 1, 3]
def baseStart_3511888 : Nat := 118140960795 + 3511888 * 2 ^ 59
def prefixEnd_3511888 : Nat := 4983230072969 + 3 ^ 40 * 3511888 * 2
def baseEnd_3511888 : Nat := 1803286548757060955749127

theorem tailTrace_3511888 : CollatzResearch.WordTrace tailWord_3511888 prefixEnd_3511888 1803286548757060955749127 := by
  unfold tailWord_3511888
  simp only [CollatzResearch.WordTrace]
  refine ⟨64044539150518516782184159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85392718867358022376245545 64044539150518516782184159)
  ·
    refine ⟨96066808725777775173276239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64044539150518516782184159 96066808725777775173276239)
    ·
      refine ⟨144100213088666662759914359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96066808725777775173276239 144100213088666662759914359)
      ·
        refine ⟨216150319632999994139871539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144100213088666662759914359 216150319632999994139871539)
        ·
          refine ⟨324225479449499991209807309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216150319632999994139871539 324225479449499991209807309)
          ·
            refine ⟨121584554793562496703677741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 324225479449499991209807309 121584554793562496703677741)
            ·
              refine ⟨45594208047585936263879153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 121584554793562496703677741 45594208047585936263879153)
              ·
                refine ⟨34195656035689452197909365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45594208047585936263879153 34195656035689452197909365)
                ·
                  refine ⟨3205842753345886143554003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34195656035689452197909365 3205842753345886143554003)
                  ·
                    refine ⟨4808764130018829215331005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3205842753345886143554003 4808764130018829215331005)
                    ·
                      refine ⟨1803286548757060955749127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4808764130018829215331005 1803286548757060955749127)
                      ·
                        rfl

theorem cell23_3511888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 2, 5, 1, 3].length) (baseStart_3511888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3511888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3511888 prefixEnd_3511888 := by exact prefixLift 3511888
  have htrace : WordTrace (prefixWord ++ tailWord_3511888) baseStart_3511888 baseEnd_3511888 := by
    simpa [prefixWord, tailWord_3511888, baseEnd_3511888] using wordTrace_append hprefix tailTrace_3511888
  have hstable : (prefixWord ++ tailWord_3511888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3511888).length < 2 ^ (prefixWord ++ tailWord_3511888).sum := by decide
  have hdescent : baseEnd_3511888 < baseStart_3511888 := by decide
  rcases family_descends (prefixWord ++ tailWord_3511888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3511905 : List Nat := [1, 2, 3, 1, 1, 3, 4, 1, 3, 1, 3]
def baseStart_3511905 : Nat := 118140960795 + 3511905 * 2 ^ 59
def prefixEnd_3511905 : Nat := 4983230072969 + 3 ^ 40 * 3511905 * 2
def baseEnd_3511905 : Nat := 1803295277928187389236549

theorem tailTrace_3511905 : CollatzResearch.WordTrace tailWord_3511905 prefixEnd_3511905 1803295277928187389236549 := by
  unfold tailWord_3511905
  simp only [CollatzResearch.WordTrace]
  refine ⟨128089698341975445467737169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85393132227983630311824779 128089698341975445467737169)
  ·
    refine ⟨96067273756481584100802877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128089698341975445467737169 96067273756481584100802877)
    ·
      refine ⟨36025227658680594037801079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96067273756481584100802877 36025227658680594037801079)
      ·
        refine ⟨54037841488020891056701619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36025227658680594037801079 54037841488020891056701619)
        ·
          refine ⟨81056762232031336585052429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54037841488020891056701619 81056762232031336585052429)
          ·
            refine ⟨30396285837011751219394661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81056762232031336585052429 30396285837011751219394661)
            ·
              refine ⟨5699303594439703353636499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30396285837011751219394661 5699303594439703353636499)
              ·
                refine ⟨8548955391659555030454749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5699303594439703353636499 8548955391659555030454749)
                ·
                  refine ⟨3205858271872333136420531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8548955391659555030454749 3205858271872333136420531)
                  ·
                    refine ⟨4808787407808499704630797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3205858271872333136420531 4808787407808499704630797)
                    ·
                      refine ⟨1803295277928187389236549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4808787407808499704630797 1803295277928187389236549)
                      ·
                        rfl

theorem cell23_3511905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 4, 1, 3, 1, 3].length) (baseStart_3511905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3511905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3511905 prefixEnd_3511905 := by exact prefixLift 3511905
  have htrace : WordTrace (prefixWord ++ tailWord_3511905) baseStart_3511905 baseEnd_3511905 := by
    simpa [prefixWord, tailWord_3511905, baseEnd_3511905] using wordTrace_append hprefix tailTrace_3511905
  have hstable : (prefixWord ++ tailWord_3511905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3511905).length < 2 ^ (prefixWord ++ tailWord_3511905).sum := by decide
  have hdescent : baseEnd_3511905 < baseStart_3511905 := by decide
  rcases family_descends (prefixWord ++ tailWord_3511905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3511925 : List Nat := [1, 3, 4, 2, 1, 1, 1, 4, 1, 5]
def baseStart_3511925 : Nat := 118140960795 + 3511925 * 2 ^ 59
def prefixEnd_3511925 : Nat := 4983230072969 + 3 ^ 40 * 3511925 * 2
def baseEnd_3511925 : Nat := 601101849180425770328819

theorem tailTrace_3511925 : CollatzResearch.WordTrace tailWord_3511925 prefixEnd_3511925 601101849180425770328819 := by
  unfold tailWord_3511925
  simp only [CollatzResearch.WordTrace]
  refine ⟨128090427801902988883465229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85393618534601992588976819 128090427801902988883465229)
  ·
    refine ⟨48033910425713620831299461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128090427801902988883465229 48033910425713620831299461)
    ·
      refine ⟨9006358204821303905868649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48033910425713620831299461 9006358204821303905868649)
      ·
        refine ⟨6754768653615977929401487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9006358204821303905868649 6754768653615977929401487)
        ·
          refine ⟨10132152980423966894102231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6754768653615977929401487 10132152980423966894102231)
          ·
            refine ⟨15198229470635950341153347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10132152980423966894102231 15198229470635950341153347)
            ·
              refine ⟨22797344205953925511730021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15198229470635950341153347 22797344205953925511730021)
              ·
                refine ⟨4274502038616361033449379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22797344205953925511730021 4274502038616361033449379)
                ·
                  refine ⟨6411753057924541550174069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4274502038616361033449379 6411753057924541550174069)
                  ·
                    refine ⟨601101849180425770328819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6411753057924541550174069 601101849180425770328819)
                    ·
                      rfl

theorem cell23_3511925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 4, 1, 5].length) (baseStart_3511925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3511925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3511925 prefixEnd_3511925 := by exact prefixLift 3511925
  have htrace : WordTrace (prefixWord ++ tailWord_3511925) baseStart_3511925 baseEnd_3511925 := by
    simpa [prefixWord, tailWord_3511925, baseEnd_3511925] using wordTrace_append hprefix tailTrace_3511925
  have hstable : (prefixWord ++ tailWord_3511925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3511925).length < 2 ^ (prefixWord ++ tailWord_3511925).sum := by decide
  have hdescent : baseEnd_3511925 < baseStart_3511925 := by decide
  rcases family_descends (prefixWord ++ tailWord_3511925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3511931 : List Nat := [1, 1, 1, 1, 1, 4, 3, 2, 3, 1, 5]
def baseStart_3511931 : Nat := 118140960795 + 3511931 * 2 ^ 59
def prefixEnd_3511931 : Nat := 4983230072969 + 3 ^ 40 * 3511931 * 2
def baseEnd_3511931 : Nat := 1803308628425204287511429

theorem tailTrace_3511931 : CollatzResearch.WordTrace tailWord_3511931 prefixEnd_3511931 1803308628425204287511429 := by
  unfold tailWord_3511931
  simp only [CollatzResearch.WordTrace]
  refine ⟨128090646639881251908183647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85393764426587501272122431 128090646639881251908183647)
  ·
    refine ⟨192135969959821877862275471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128090646639881251908183647 192135969959821877862275471)
    ·
      refine ⟨288203954939732816793413207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192135969959821877862275471 288203954939732816793413207)
      ·
        refine ⟨432305932409599225190119811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288203954939732816793413207 432305932409599225190119811)
        ·
          refine ⟨648458898614398837785179717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 432305932409599225190119811 648458898614398837785179717)
          ·
            refine ⟨121586043490199782084721197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 648458898614398837785179717 121586043490199782084721197)
            ·
              refine ⟨45594766308824918281770449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 121586043490199782084721197 45594766308824918281770449)
              ·
                refine ⟨34196074731618688711327837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45594766308824918281770449 34196074731618688711327837)
                ·
                  refine ⟨12823528024357008266747939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34196074731618688711327837 12823528024357008266747939)
                  ·
                    refine ⟨19235292036535512400121909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12823528024357008266747939 19235292036535512400121909)
                    ·
                      refine ⟨1803308628425204287511429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19235292036535512400121909 1803308628425204287511429)
                      ·
                        rfl

theorem cell23_3511931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 2, 3, 1, 5].length) (baseStart_3511931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3511931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3511931 prefixEnd_3511931 := by exact prefixLift 3511931
  have htrace : WordTrace (prefixWord ++ tailWord_3511931) baseStart_3511931 baseEnd_3511931 := by
    simpa [prefixWord, tailWord_3511931, baseEnd_3511931] using wordTrace_append hprefix tailTrace_3511931
  have hstable : (prefixWord ++ tailWord_3511931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3511931).length < 2 ^ (prefixWord ++ tailWord_3511931).sum := by decide
  have hdescent : baseEnd_3511931 < baseStart_3511931 := by decide
  rcases family_descends (prefixWord ++ tailWord_3511931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3511945 : List Nat := [1, 2, 1, 1, 4, 1, 2, 2, 5, 2, 2]
def baseStart_3511945 : Nat := 118140960795 + 3511945 * 2 ^ 59
def prefixEnd_3511945 : Nat := 4983230072969 + 3 ^ 40 * 3511945 * 2
def baseEnd_3511945 : Nat := 1803315817154367232736365

theorem tailTrace_3511945 : CollatzResearch.WordTrace tailWord_3511945 prefixEnd_3511945 1803315817154367232736365 := by
  unfold tailWord_3511945
  simp only [CollatzResearch.WordTrace]
  refine ⟨128091157261830532299193289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85394104841220354866128859 128091157261830532299193289)
  ·
    refine ⟨96068367946372899224394967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128091157261830532299193289 96068367946372899224394967)
    ·
      refine ⟨144102551919559348836592451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96068367946372899224394967 144102551919559348836592451)
      ·
        refine ⟨216153827879339023254888677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144102551919559348836592451 216153827879339023254888677)
        ·
          refine ⟨40528842727376066860291627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 216153827879339023254888677 40528842727376066860291627)
          ·
            refine ⟨60793264091064100290437441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40528842727376066860291627 60793264091064100290437441)
            ·
              refine ⟨45594948068298075217828081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60793264091064100290437441 45594948068298075217828081)
              ·
                refine ⟨34196211051223556413371061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45594948068298075217828081 34196211051223556413371061)
                ·
                  refine ⟨3205894786052208413753537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34196211051223556413371061 3205894786052208413753537)
                  ·
                    refine ⟨2404421089539156310315153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3205894786052208413753537 2404421089539156310315153)
                    ·
                      refine ⟨1803315817154367232736365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2404421089539156310315153 1803315817154367232736365)
                      ·
                        rfl

theorem cell23_3511945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 2, 5, 2, 2].length) (baseStart_3511945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3511945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3511945 prefixEnd_3511945 := by exact prefixLift 3511945
  have htrace : WordTrace (prefixWord ++ tailWord_3511945) baseStart_3511945 baseEnd_3511945 := by
    simpa [prefixWord, tailWord_3511945, baseEnd_3511945] using wordTrace_append hprefix tailTrace_3511945
  have hstable : (prefixWord ++ tailWord_3511945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3511945).length < 2 ^ (prefixWord ++ tailWord_3511945).sum := by decide
  have hdescent : baseEnd_3511945 < baseStart_3511945 := by decide
  rcases family_descends (prefixWord ++ tailWord_3511945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3511948 : List Nat := [2, 2, 1, 2, 1, 1, 6, 1, 1, 1, 5]
def baseStart_3511948 : Nat := 118140960795 + 3511948 * 2 ^ 59
def prefixEnd_3511948 : Nat := 4983230072969 + 3 ^ 40 * 3511948 * 2
def baseEnd_3511948 : Nat := 1803317357596330720998851

theorem tailTrace_3511948 : CollatzResearch.WordTrace tailWord_3511948 prefixEnd_3511948 1803317357596330720998851 := by
  unfold tailWord_3511948
  simp only [CollatzResearch.WordTrace]
  refine ⟨64045633340409831905776249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85394177787213109207701665 64045633340409831905776249)
  ·
    refine ⟨48034225005307373929332187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64045633340409831905776249 48034225005307373929332187)
    ·
      refine ⟨72051337507961060893998281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48034225005307373929332187 72051337507961060893998281)
      ·
        refine ⟨54038503130970795670498711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72051337507961060893998281 54038503130970795670498711)
        ·
          refine ⟨81057754696456193505748067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54038503130970795670498711 81057754696456193505748067)
          ·
            refine ⟨121586632044684290258622101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81057754696456193505748067 121586632044684290258622101)
            ·
              refine ⟨5699373377094576105872911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 121586632044684290258622101 5699373377094576105872911)
              ·
                refine ⟨8549060065641864158809367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5699373377094576105872911 8549060065641864158809367)
                ·
                  refine ⟨12823590098462796238214051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8549060065641864158809367 12823590098462796238214051)
                  ·
                    refine ⟨19235385147694194357321077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12823590098462796238214051 19235385147694194357321077)
                    ·
                      refine ⟨1803317357596330720998851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19235385147694194357321077 1803317357596330720998851)
                      ·
                        rfl

theorem cell23_3511948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 6, 1, 1, 1, 5].length) (baseStart_3511948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3511948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3511948 prefixEnd_3511948 := by exact prefixLift 3511948
  have htrace : WordTrace (prefixWord ++ tailWord_3511948) baseStart_3511948 baseEnd_3511948 := by
    simpa [prefixWord, tailWord_3511948, baseEnd_3511948] using wordTrace_append hprefix tailTrace_3511948
  have hstable : (prefixWord ++ tailWord_3511948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3511948).length < 2 ^ (prefixWord ++ tailWord_3511948).sum := by decide
  have hdescent : baseEnd_3511948 < baseStart_3511948 := by decide
  rcases family_descends (prefixWord ++ tailWord_3511948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3511956 : List Nat := [2, 4, 2, 2, 3, 1, 1, 1, 3, 1, 3]
def baseStart_3511956 : Nat := 118140960795 + 3511956 * 2 ^ 59
def prefixEnd_3511956 : Nat := 4983230072969 + 3 ^ 40 * 3511956 * 2
def baseEnd_3511956 : Nat := 1803321465441566689698815

theorem tailTrace_3511956 : CollatzResearch.WordTrace tailWord_3511956 prefixEnd_3511956 1803321465441566689698815 := by
  unfold tailWord_3511956
  simp only [CollatzResearch.WordTrace]
  refine ⟨64045779232395340588921861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85394372309860454118562481 64045779232395340588921861)
  ·
    refine ⟨12008583606074126360422849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64045779232395340588921861 12008583606074126360422849)
    ·
      refine ⟨9006437704555594770317137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12008583606074126360422849 9006437704555594770317137)
      ·
        refine ⟨6754828278416696077737853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9006437704555594770317137 6754828278416696077737853)
        ·
          refine ⟨2533060604406261029151695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6754828278416696077737853 2533060604406261029151695)
          ·
            refine ⟨3799590906609391543727543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2533060604406261029151695 3799590906609391543727543)
            ·
              refine ⟨5699386359914087315591315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3799590906609391543727543 5699386359914087315591315)
              ·
                refine ⟨8549079539871130973386973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5699386359914087315591315 8549079539871130973386973)
                ·
                  refine ⟨3205904827451674115020115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8549079539871130973386973 3205904827451674115020115)
                  ·
                    refine ⟨4808857241177511172530173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3205904827451674115020115 4808857241177511172530173)
                    ·
                      refine ⟨1803321465441566689698815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4808857241177511172530173 1803321465441566689698815)
                      ·
                        rfl

theorem cell23_3511956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 1, 1, 3, 1, 3].length) (baseStart_3511956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3511956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3511956 prefixEnd_3511956 := by exact prefixLift 3511956
  have htrace : WordTrace (prefixWord ++ tailWord_3511956) baseStart_3511956 baseEnd_3511956 := by
    simpa [prefixWord, tailWord_3511956, baseEnd_3511956] using wordTrace_append hprefix tailTrace_3511956
  have hstable : (prefixWord ++ tailWord_3511956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3511956).length < 2 ^ (prefixWord ++ tailWord_3511956).sum := by decide
  have hdescent : baseEnd_3511956 < baseStart_3511956 := by decide
  rcases family_descends (prefixWord ++ tailWord_3511956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3511968 : List Nat := [2, 1, 1, 4, 3, 2, 2, 8]
def baseStart_3511968 : Nat := 118140960795 + 3511968 * 2 ^ 59
def prefixEnd_3511968 : Nat := 4983230072969 + 3 ^ 40 * 3511968 * 2
def baseEnd_3511968 : Nat := 66789912118867431212917

theorem tailTrace_3511968 : CollatzResearch.WordTrace tailWord_3511968 prefixEnd_3511968 66789912118867431212917 := by
  unfold tailWord_3511968
  simp only [CollatzResearch.WordTrace]
  refine ⟨64045998070373603613640279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85394664093831471484853705 64045998070373603613640279)
  ·
    refine ⟨96068997105560405420460419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64045998070373603613640279 96068997105560405420460419)
    ·
      refine ⟨144103495658340608130690629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96068997105560405420460419 144103495658340608130690629)
      ·
        refine ⟨27019405435938864024504493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 144103495658340608130690629 27019405435938864024504493)
        ·
          refine ⟨10132277038477074009189185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27019405435938864024504493 10132277038477074009189185)
          ·
            refine ⟨7599207778857805506891889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10132277038477074009189185 7599207778857805506891889)
            ·
              refine ⟨5699405834143354130168917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7599207778857805506891889 5699405834143354130168917)
              ·
                refine ⟨66789912118867431212917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5699405834143354130168917 66789912118867431212917)
                ·
                  rfl

theorem cell23_3511968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2, 8].length) (baseStart_3511968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3511968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3511968 prefixEnd_3511968 := by exact prefixLift 3511968
  have htrace : WordTrace (prefixWord ++ tailWord_3511968) baseStart_3511968 baseEnd_3511968 := by
    simpa [prefixWord, tailWord_3511968, baseEnd_3511968] using wordTrace_append hprefix tailTrace_3511968
  have hstable : (prefixWord ++ tailWord_3511968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3511968).length < 2 ^ (prefixWord ++ tailWord_3511968).sum := by decide
  have hdescent : baseEnd_3511968 < baseStart_3511968 := by decide
  rcases family_descends (prefixWord ++ tailWord_3511968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3511971 : List Nat := [1, 1, 1, 4, 1, 1, 3, 1, 2, 2, 6]
def baseStart_3511971 : Nat := 118140960795 + 3511971 * 2 ^ 59
def prefixEnd_3511971 : Nat := 4983230072969 + 3 ^ 40 * 3511971 * 2
def baseEnd_3511971 : Nat := 1803329167651384131011245

theorem tailTrace_3511971 : CollatzResearch.WordTrace tailWord_3511971 prefixEnd_3511971 1803329167651384131011245 := by
  unfold tailWord_3511971
  simp only [CollatzResearch.WordTrace]
  refine ⟨128092105559736338739639767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85394737039824225826426511 128092105559736338739639767)
  ·
    refine ⟨192138158339604508109459651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128092105559736338739639767 192138158339604508109459651)
    ·
      refine ⟨288207237509406762164189477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192138158339604508109459651 288207237509406762164189477)
      ·
        refine ⟨54038857033013767905785527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 288207237509406762164189477 54038857033013767905785527)
        ·
          refine ⟨81058285549520651858678291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54038857033013767905785527 81058285549520651858678291)
          ·
            refine ⟨121587428324280977788017437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81058285549520651858678291 121587428324280977788017437)
            ·
              refine ⟨45595285621605366670506539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 121587428324280977788017437 45595285621605366670506539)
              ·
                refine ⟨68392928432408050005759809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45595285621605366670506539 68392928432408050005759809)
                ·
                  refine ⟨51294696324306037504319857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68392928432408050005759809 51294696324306037504319857)
                  ·
                    refine ⟨38471022243229528128239893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51294696324306037504319857 38471022243229528128239893)
                    ·
                      refine ⟨1803329167651384131011245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38471022243229528128239893 1803329167651384131011245)
                      ·
                        rfl

theorem cell23_3511971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 2, 2, 6].length) (baseStart_3511971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3511971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3511971 prefixEnd_3511971 := by exact prefixLift 3511971
  have htrace : WordTrace (prefixWord ++ tailWord_3511971) baseStart_3511971 baseEnd_3511971 := by
    simpa [prefixWord, tailWord_3511971, baseEnd_3511971] using wordTrace_append hprefix tailTrace_3511971
  have hstable : (prefixWord ++ tailWord_3511971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3511971).length < 2 ^ (prefixWord ++ tailWord_3511971).sum := by decide
  have hdescent : baseEnd_3511971 < baseStart_3511971 := by decide
  rcases family_descends (prefixWord ++ tailWord_3511971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3511972 : List Nat := [2, 3, 1, 2, 2, 2, 4, 1, 2, 4]
def baseStart_3511972 : Nat := 118140960795 + 3511972 * 2 ^ 59
def prefixEnd_3511972 : Nat := 4983230072969 + 3 ^ 40 * 3511972 * 2
def baseEnd_3511972 : Nat := 601109893710679542366247

theorem tailTrace_3511972 : CollatzResearch.WordTrace tailWord_3511972 prefixEnd_3511972 601109893710679542366247 := by
  unfold tailWord_3511972
  simp only [CollatzResearch.WordTrace]
  refine ⟨64046071016366357955213085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85394761355155143940284113 64046071016366357955213085)
  ·
    refine ⟨24017276631137384233204907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64046071016366357955213085 24017276631137384233204907)
    ·
      refine ⟨36025914946706076349807361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24017276631137384233204907 36025914946706076349807361)
      ·
        refine ⟨27019436210029557262355521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36025914946706076349807361 27019436210029557262355521)
        ·
          refine ⟨20264577157522167946766641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27019436210029557262355521 20264577157522167946766641)
          ·
            refine ⟨15198432868141625960074981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20264577157522167946766641 15198432868141625960074981)
            ·
              refine ⟨2849706162776554867514059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15198432868141625960074981 2849706162776554867514059)
              ·
                refine ⟨4274559244164832301271089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2849706162776554867514059 4274559244164832301271089)
                ·
                  refine ⟨3205919433123624225953317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4274559244164832301271089 3205919433123624225953317)
                  ·
                    refine ⟨601109893710679542366247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3205919433123624225953317 601109893710679542366247)
                    ·
                      rfl

theorem cell23_3511972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 4, 1, 2, 4].length) (baseStart_3511972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3511972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3511972 prefixEnd_3511972 := by exact prefixLift 3511972
  have htrace : WordTrace (prefixWord ++ tailWord_3511972) baseStart_3511972 baseEnd_3511972 := by
    simpa [prefixWord, tailWord_3511972, baseEnd_3511972] using wordTrace_append hprefix tailTrace_3511972
  have hstable : (prefixWord ++ tailWord_3511972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3511972).length < 2 ^ (prefixWord ++ tailWord_3511972).sum := by decide
  have hdescent : baseEnd_3511972 < baseStart_3511972 := by decide
  rcases family_descends (prefixWord ++ tailWord_3511972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3511976 : List Nat := [2, 1, 7, 1, 1, 2, 1, 2, 1, 5]
def baseStart_3511976 : Nat := 118140960795 + 3511976 * 2 ^ 59
def prefixEnd_3511976 : Nat := 4983230072969 + 3 ^ 40 * 3511976 * 2
def baseEnd_3511976 : Nat := 601110578351552203816241

theorem tailTrace_3511976 : CollatzResearch.WordTrace tailWord_3511976 prefixEnd_3511976 601110578351552203816241 := by
  unfold tailWord_3511976
  simp only [CollatzResearch.WordTrace]
  refine ⟨64046143962359112296785891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85394858616478816395714521 64046143962359112296785891)
  ·
    refine ⟨96069215943538668445178837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64046143962359112296785891 96069215943538668445178837)
    ·
      refine ⟨2251622248676687541683879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 96069215943538668445178837 2251622248676687541683879)
      ·
        refine ⟨3377433373015031312525819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2251622248676687541683879 3377433373015031312525819)
        ·
          refine ⟨5066150059522546968788729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3377433373015031312525819 5066150059522546968788729)
          ·
            refine ⟨3799612544641910226591547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5066150059522546968788729 3799612544641910226591547)
            ·
              refine ⟨5699418816962865339887321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3799612544641910226591547 5699418816962865339887321)
              ·
                refine ⟨4274564112722149004915491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5699418816962865339887321 4274564112722149004915491)
                ·
                  refine ⟨6411846169083223507373237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4274564112722149004915491 6411846169083223507373237)
                  ·
                    refine ⟨601110578351552203816241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6411846169083223507373237 601110578351552203816241)
                    ·
                      rfl

theorem cell23_3511976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_3511976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3511976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3511976 prefixEnd_3511976 := by exact prefixLift 3511976
  have htrace : WordTrace (prefixWord ++ tailWord_3511976) baseStart_3511976 baseEnd_3511976 := by
    simpa [prefixWord, tailWord_3511976, baseEnd_3511976] using wordTrace_append hprefix tailTrace_3511976
  have hstable : (prefixWord ++ tailWord_3511976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3511976).length < 2 ^ (prefixWord ++ tailWord_3511976).sum := by decide
  have hdescent : baseEnd_3511976 < baseStart_3511976 := by decide
  rcases family_descends (prefixWord ++ tailWord_3511976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3512002 : List Nat := [3, 5, 1, 2, 1, 11]
def baseStart_3512002 : Nat := 118140960795 + 3512002 * 2 ^ 59
def prefixEnd_3512002 : Nat := 4983230072969 + 3 ^ 40 * 3512002 * 2
def baseEnd_3512002 : Nat := 7421173191570672879521

theorem tailTrace_3512002 : CollatzResearch.WordTrace tailWord_3512002 prefixEnd_3512002 7421173191570672879521 := by
  unfold tailWord_3512002
  simp only [CollatzResearch.WordTrace]
  refine ⟨32023309055656007758504565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85395490815082687356012173 32023309055656007758504565)
  ·
    refine ⟨3002185223967750727359803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32023309055656007758504565 3002185223967750727359803)
    ·
      refine ⟨4503277835951626091039705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3002185223967750727359803 4503277835951626091039705)
      ·
        refine ⟨3377458376963719568279779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4503277835951626091039705 3377458376963719568279779)
        ·
          refine ⟨5066187565445579352419669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3377458376963719568279779 5066187565445579352419669)
          ·
            refine ⟨7421173191570672879521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 5066187565445579352419669 7421173191570672879521)
            ·
              rfl

theorem cell23_3512002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 11].length) (baseStart_3512002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3512002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3512002 prefixEnd_3512002 := by exact prefixLift 3512002
  have htrace : WordTrace (prefixWord ++ tailWord_3512002) baseStart_3512002 baseEnd_3512002 := by
    simpa [prefixWord, tailWord_3512002, baseEnd_3512002] using wordTrace_append hprefix tailTrace_3512002
  have hstable : (prefixWord ++ tailWord_3512002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3512002).length < 2 ^ (prefixWord ++ tailWord_3512002).sum := by decide
  have hdescent : baseEnd_3512002 < baseStart_3512002 := by decide
  rcases family_descends (prefixWord ++ tailWord_3512002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3512006 : List Nat := [6, 1, 2, 1, 1, 2, 2, 2, 2, 4]
def baseStart_3512006 : Nat := 118140960795 + 3512006 * 2 ^ 59
def prefixEnd_3512006 : Nat := 4983230072969 + 3 ^ 40 * 3512006 * 2
def baseEnd_3512006 : Nat := 601115713158097164691195

theorem tailTrace_3512006 : CollatzResearch.WordTrace tailWord_3512006 prefixEnd_3512006 601115713158097164691195 := by
  unfold tailWord_3512006
  simp only [CollatzResearch.WordTrace]
  refine ⟨4002918191081548116161371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 85395588076406359811442581 4002918191081548116161371)
  ·
    refine ⟨6004377286622322174242057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4002918191081548116161371 6004377286622322174242057)
    ·
      refine ⟨4503282964966741630681543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6004377286622322174242057 4503282964966741630681543)
      ·
        refine ⟨6754924447450112446022315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4503282964966741630681543 6754924447450112446022315)
        ·
          refine ⟨10132386671175168669033473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6754924447450112446022315 10132386671175168669033473)
          ·
            refine ⟨7599290003381376501775105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10132386671175168669033473 7599290003381376501775105)
            ·
              refine ⟨5699467502536032376331329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7599290003381376501775105 5699467502536032376331329)
              ·
                refine ⟨4274600626902024282248497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5699467502536032376331329 4274600626902024282248497)
                ·
                  refine ⟨3205950470176518211686373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4274600626902024282248497 3205950470176518211686373)
                  ·
                    refine ⟨601115713158097164691195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3205950470176518211686373 601115713158097164691195)
                    ·
                      rfl

theorem cell23_3512006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_3512006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3512006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3512006 prefixEnd_3512006 := by exact prefixLift 3512006
  have htrace : WordTrace (prefixWord ++ tailWord_3512006) baseStart_3512006 baseEnd_3512006 := by
    simpa [prefixWord, tailWord_3512006, baseEnd_3512006] using wordTrace_append hprefix tailTrace_3512006
  have hstable : (prefixWord ++ tailWord_3512006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3512006).length < 2 ^ (prefixWord ++ tailWord_3512006).sum := by decide
  have hdescent : baseEnd_3512006 < baseStart_3512006 := by decide
  rcases family_descends (prefixWord ++ tailWord_3512006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3512011 : List Nat := [1, 1, 1, 1, 3, 2, 1, 2, 3, 8]
def baseStart_3512011 : Nat := 118140960795 + 3512011 * 2 ^ 59
def prefixEnd_3512011 : Nat := 4983230072969 + 3 ^ 40 * 3512011 * 2
def baseEnd_3512011 : Nat := 601116568959187991503687

theorem tailTrace_3512011 : CollatzResearch.WordTrace tailWord_3512011 prefixEnd_3512011 601116568959187991503687 := by
  unfold tailWord_3512011
  simp only [CollatzResearch.WordTrace]
  refine ⟨128093564479591425571095887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85395709653060950380730591 128093564479591425571095887)
  ·
    refine ⟨192140346719387138356643831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128093564479591425571095887 192140346719387138356643831)
    ·
      refine ⟨288210520079080707534965747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192140346719387138356643831 288210520079080707534965747)
      ·
        refine ⟨432315780118621061302448621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288210520079080707534965747 432315780118621061302448621)
        ·
          refine ⟨162118417544482897988418233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 432315780118621061302448621 162118417544482897988418233)
          ·
            refine ⟨121588813158362173491313675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162118417544482897988418233 121588813158362173491313675)
            ·
              refine ⟨182383219737543260236970513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121588813158362173491313675 182383219737543260236970513)
              ·
                refine ⟨136787414803157445177727885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 182383219737543260236970513 136787414803157445177727885)
                ·
                  refine ⟨51295280551184041941647957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 136787414803157445177727885 51295280551184041941647957)
                  ·
                    refine ⟨601116568959187991503687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 51295280551184041941647957 601116568959187991503687)
                    ·
                      rfl

theorem cell23_3512011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 3, 8].length) (baseStart_3512011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3512011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3512011 prefixEnd_3512011 := by exact prefixLift 3512011
  have htrace : WordTrace (prefixWord ++ tailWord_3512011) baseStart_3512011 baseEnd_3512011 := by
    simpa [prefixWord, tailWord_3512011, baseEnd_3512011] using wordTrace_append hprefix tailTrace_3512011
  have hstable : (prefixWord ++ tailWord_3512011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3512011).length < 2 ^ (prefixWord ++ tailWord_3512011).sum := by decide
  have hdescent : baseEnd_3512011 < baseStart_3512011 := by decide
  rcases family_descends (prefixWord ++ tailWord_3512011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3512013 : List Nat := [1, 6, 2, 1, 1, 2, 1, 4, 1, 2, 2]
def baseStart_3512013 : Nat := 118140960795 + 3512013 * 2 ^ 59
def prefixEnd_3512013 : Nat := 4983230072969 + 3 ^ 40 * 3512013 * 2
def baseEnd_3512013 : Nat := 1803350733838872966686053

theorem tailTrace_3512013 : CollatzResearch.WordTrace tailWord_3512013 prefixEnd_3512013 1803350733838872966686053 := by
  unfold tailWord_3512013
  simp only [CollatzResearch.WordTrace]
  refine ⟨128093637425584179912668693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85395758283722786608445795 128093637425584179912668693)
  ·
    refine ⟨6004389254324258433406345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 128093637425584179912668693 6004389254324258433406345)
    ·
      refine ⟨4503291940743193825054759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6004389254324258433406345 4503291940743193825054759)
      ·
        refine ⟨6754937911114790737582139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4503291940743193825054759 6754937911114790737582139)
        ·
          refine ⟨10132406866672186106373209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6754937911114790737582139 10132406866672186106373209)
          ·
            refine ⟨7599305150004139579779907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10132406866672186106373209 7599305150004139579779907)
            ·
              refine ⟨11398957725006209369669861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7599305150004139579779907 11398957725006209369669861)
              ·
                refine ⟨2137304573438664256813099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11398957725006209369669861 2137304573438664256813099)
                ·
                  refine ⟨3205956860157996385219649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2137304573438664256813099 3205956860157996385219649)
                  ·
                    refine ⟨2404467645118497288914737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3205956860157996385219649 2404467645118497288914737)
                    ·
                      refine ⟨1803350733838872966686053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2404467645118497288914737 1803350733838872966686053)
                      ·
                        rfl

theorem cell23_3512013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 4, 1, 2, 2].length) (baseStart_3512013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3512013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3512013 prefixEnd_3512013 := by exact prefixLift 3512013
  have htrace : WordTrace (prefixWord ++ tailWord_3512013) baseStart_3512013 baseEnd_3512013 := by
    simpa [prefixWord, tailWord_3512013, baseEnd_3512013] using wordTrace_append hprefix tailTrace_3512013
  have hstable : (prefixWord ++ tailWord_3512013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3512013).length < 2 ^ (prefixWord ++ tailWord_3512013).sum := by decide
  have hdescent : baseEnd_3512013 < baseStart_3512013 := by decide
  rcases family_descends (prefixWord ++ tailWord_3512013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3512029 : List Nat := [1, 4, 3, 3, 1, 1, 2, 1, 1, 3, 3]
def baseStart_3512029 : Nat := 118140960795 + 3512029 * 2 ^ 59
def prefixEnd_3512029 : Nat := 4983230072969 + 3 ^ 40 * 3512029 * 2
def baseEnd_3512029 : Nat := 1803358949529344904085979

theorem tailTrace_3512029 : CollatzResearch.WordTrace tailWord_3512029 prefixEnd_3512029 1803358949529344904085979 := by
  unfold tailWord_3512029
  simp only [CollatzResearch.WordTrace]
  refine ⟨128094220993526214645251141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85396147329017476430167427 128094220993526214645251141)
  ·
    refine ⟨24017666436286165245984589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128094220993526214645251141 24017666436286165245984589)
    ·
      refine ⟨9006624913607311967244221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24017666436286165245984589 9006624913607311967244221)
      ·
        refine ⟨3377484342602741987716583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9006624913607311967244221 3377484342602741987716583)
        ·
          refine ⟨5066226513904112981574875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3377484342602741987716583 5066226513904112981574875)
          ·
            refine ⟨7599339770856169472362313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5066226513904112981574875 7599339770856169472362313)
            ·
              refine ⟨5699504828142127104271735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7599339770856169472362313 5699504828142127104271735)
              ·
                refine ⟨8549257242213190656407603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5699504828142127104271735 8549257242213190656407603)
                ·
                  refine ⟨12823885863319785984611405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8549257242213190656407603 12823885863319785984611405)
                  ·
                    refine ⟨4808957198744919744229277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12823885863319785984611405 4808957198744919744229277)
                    ·
                      refine ⟨1803358949529344904085979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4808957198744919744229277 1803358949529344904085979)
                      ·
                        rfl

theorem cell23_3512029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_3512029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3512029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3512029 prefixEnd_3512029 := by exact prefixLift 3512029
  have htrace : WordTrace (prefixWord ++ tailWord_3512029) baseStart_3512029 baseEnd_3512029 := by
    simpa [prefixWord, tailWord_3512029, baseEnd_3512029] using wordTrace_append hprefix tailTrace_3512029
  have hstable : (prefixWord ++ tailWord_3512029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3512029).length < 2 ^ (prefixWord ++ tailWord_3512029).sum := by decide
  have hdescent : baseEnd_3512029 < baseStart_3512029 := by decide
  rcases family_descends (prefixWord ++ tailWord_3512029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3512075 : List Nat := [1, 1, 1, 1, 5, 1, 4, 4, 5]
def baseStart_3512075 : Nat := 118140960795 + 3512075 * 2 ^ 59
def prefixEnd_3512075 : Nat := 4983230072969 + 3 ^ 40 * 3512075 * 2
def baseEnd_3512075 : Nat := 200375841071050191567863

theorem tailTrace_3512075 : CollatzResearch.WordTrace tailWord_3512075 prefixEnd_3512075 200375841071050191567863 := by
  unfold tailWord_3512075
  simp only [CollatzResearch.WordTrace]
  refine ⟨128095898751359564501425679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85397265834239709667617119 128095898751359564501425679)
  ·
    refine ⟨192143848127039346752138519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128095898751359564501425679 192143848127039346752138519)
    ·
      refine ⟨288215772190559020128207779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192143848127039346752138519 288215772190559020128207779)
      ·
        refine ⟨432323658285838530192311669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288215772190559020128207779 432323658285838530192311669)
        ·
          refine ⟨40530342964297362205529219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 432323658285838530192311669 40530342964297362205529219)
          ·
            refine ⟨60795514446446043308293829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40530342964297362205529219 60795514446446043308293829)
            ·
              refine ⟨11399158958708633120305093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60795514446446043308293829 11399158958708633120305093)
              ·
                refine ⟨2137342304757868710057205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11399158958708633120305093 2137342304757868710057205)
                ·
                  refine ⟨200375841071050191567863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2137342304757868710057205 200375841071050191567863)
                  ·
                    rfl

theorem cell23_3512075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 4, 5].length) (baseStart_3512075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3512075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3512075 prefixEnd_3512075 := by exact prefixLift 3512075
  have htrace : WordTrace (prefixWord ++ tailWord_3512075) baseStart_3512075 baseEnd_3512075 := by
    simpa [prefixWord, tailWord_3512075, baseEnd_3512075] using wordTrace_append hprefix tailTrace_3512075
  have hstable : (prefixWord ++ tailWord_3512075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3512075).length < 2 ^ (prefixWord ++ tailWord_3512075).sum := by decide
  have hdescent : baseEnd_3512075 < baseStart_3512075 := by decide
  rcases family_descends (prefixWord ++ tailWord_3512075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3512082 : List Nat := [3, 2, 4, 1, 1, 1, 2, 1, 2, 2, 4]
def baseStart_3512082 : Nat := 118140960795 + 3512082 * 2 ^ 59
def prefixEnd_3512082 : Nat := 4983230072969 + 3 ^ 40 * 3512082 * 2
def baseEnd_3512082 : Nat := 1803386164004033196723235

theorem tailTrace_3512082 : CollatzResearch.WordTrace tailWord_3512082 prefixEnd_3512082 1803386164004033196723235 := by
  unfold tailWord_3512082
  simp only [CollatzResearch.WordTrace]
  refine ⟨32024038515583551174232625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85397436041556136464620333 32024038515583551174232625)
  ·
    refine ⟨24018028886687663380674469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32024038515583551174232625 24018028886687663380674469)
    ·
      refine ⟨4503380416253936883876463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24018028886687663380674469 4503380416253936883876463)
      ·
        refine ⟨6755070624380905325814695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4503380416253936883876463 6755070624380905325814695)
        ·
          refine ⟨10132605936571357988722043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6755070624380905325814695 10132605936571357988722043)
          ·
            refine ⟨15198908904857036983083065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10132605936571357988722043 15198908904857036983083065)
            ·
              refine ⟨11399181678642777737312299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15198908904857036983083065 11399181678642777737312299)
              ·
                refine ⟨17098772517964166605968449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11399181678642777737312299 17098772517964166605968449)
                ·
                  refine ⟨12824079388473124954476337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17098772517964166605968449 12824079388473124954476337)
                  ·
                    refine ⟨9618059541354843715857253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12824079388473124954476337 9618059541354843715857253)
                    ·
                      refine ⟨1803386164004033196723235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9618059541354843715857253 1803386164004033196723235)
                      ·
                        rfl

theorem cell23_3512082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_3512082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3512082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3512082 prefixEnd_3512082 := by exact prefixLift 3512082
  have htrace : WordTrace (prefixWord ++ tailWord_3512082) baseStart_3512082 baseEnd_3512082 := by
    simpa [prefixWord, tailWord_3512082, baseEnd_3512082] using wordTrace_append hprefix tailTrace_3512082
  have hstable : (prefixWord ++ tailWord_3512082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3512082).length < 2 ^ (prefixWord ++ tailWord_3512082).sum := by decide
  have hdescent : baseEnd_3512082 < baseStart_3512082 := by decide
  rcases family_descends (prefixWord ++ tailWord_3512082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3512085 : List Nat := [1, 3, 2, 1, 2, 3, 2, 1, 2, 3, 3]
def baseStart_3512085 : Nat := 118140960795 + 3512085 * 2 ^ 59
def prefixEnd_3512085 : Nat := 4983230072969 + 3 ^ 40 * 3512085 * 2
def baseEnd_3512085 : Nat := 1803387704445996684985721

theorem tailTrace_3512085 : CollatzResearch.WordTrace tailWord_3512085 prefixEnd_3512085 1803387704445996684985721 := by
  unfold tailWord_3512085
  simp only [CollatzResearch.WordTrace]
  refine ⟨128096263481323336209289709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85397508987548890806193139 128096263481323336209289709)
  ·
    refine ⟨48036098805496251078483641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128096263481323336209289709 48036098805496251078483641)
    ·
      refine ⟨36027074104122188308862731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48036098805496251078483641 36027074104122188308862731)
      ·
        refine ⟨54040611156183282463294097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36027074104122188308862731 54040611156183282463294097)
        ·
          refine ⟨40530458367137461847470573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54040611156183282463294097 40530458367137461847470573)
          ·
            refine ⟨15198921887676548192801465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40530458367137461847470573 15198921887676548192801465)
            ·
              refine ⟨11399191415757411144601099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15198921887676548192801465 11399191415757411144601099)
              ·
                refine ⟨17098787123636116716901649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11399191415757411144601099 17098787123636116716901649)
                ·
                  refine ⟨12824090342727087537676237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17098787123636116716901649 12824090342727087537676237)
                  ·
                    refine ⟨4809033878522657826628589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12824090342727087537676237 4809033878522657826628589)
                    ·
                      refine ⟨1803387704445996684985721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4809033878522657826628589 1803387704445996684985721)
                      ·
                        rfl

theorem cell23_3512085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 1, 2, 3, 3].length) (baseStart_3512085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3512085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3512085 prefixEnd_3512085 := by exact prefixLift 3512085
  have htrace : WordTrace (prefixWord ++ tailWord_3512085) baseStart_3512085 baseEnd_3512085 := by
    simpa [prefixWord, tailWord_3512085, baseEnd_3512085] using wordTrace_append hprefix tailTrace_3512085
  have hstable : (prefixWord ++ tailWord_3512085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3512085).length < 2 ^ (prefixWord ++ tailWord_3512085).sum := by decide
  have hdescent : baseEnd_3512085 < baseStart_3512085 := by decide
  rcases family_descends (prefixWord ++ tailWord_3512085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3512088 : List Nat := [2, 1, 2, 3, 1, 1, 3, 2, 1, 7]
def baseStart_3512088 : Nat := 118140960795 + 3512088 * 2 ^ 59
def prefixEnd_3512088 : Nat := 4983230072969 + 3 ^ 40 * 3512088 * 2
def baseEnd_3512088 : Nat := 601129748295986724416069

theorem tailTrace_3512088 : CollatzResearch.WordTrace tailWord_3512088 prefixEnd_3512088 601129748295986724416069 := by
  unfold tailWord_3512088
  simp only [CollatzResearch.WordTrace]
  refine ⟨64048186450156233860824459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85397581933541645147765945 64048186450156233860824459)
  ·
    refine ⟨96072279675234350791236689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64048186450156233860824459 96072279675234350791236689)
    ·
      refine ⟨72054209756425763093427517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96072279675234350791236689 72054209756425763093427517)
      ·
        refine ⟨27020328658659661160035319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72054209756425763093427517 27020328658659661160035319)
        ·
          refine ⟨40530492987989491740052979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27020328658659661160035319 40530492987989491740052979)
          ·
            refine ⟨60795739481984237610079469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40530492987989491740052979 60795739481984237610079469)
            ·
              refine ⟨22798402305744089103779801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60795739481984237610079469 22798402305744089103779801)
              ·
                refine ⟨17098801729308066827834851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22798402305744089103779801 17098801729308066827834851)
                ·
                  refine ⟨25648202593962100241752277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17098801729308066827834851 25648202593962100241752277)
                  ·
                    refine ⟨601129748295986724416069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25648202593962100241752277 601129748295986724416069)
                    ·
                      rfl

theorem cell23_3512088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 2, 1, 7].length) (baseStart_3512088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3512088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3512088 prefixEnd_3512088 := by exact prefixLift 3512088
  have htrace : WordTrace (prefixWord ++ tailWord_3512088) baseStart_3512088 baseEnd_3512088 := by
    simpa [prefixWord, tailWord_3512088, baseEnd_3512088] using wordTrace_append hprefix tailTrace_3512088
  have hstable : (prefixWord ++ tailWord_3512088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3512088).length < 2 ^ (prefixWord ++ tailWord_3512088).sum := by decide
  have hdescent : baseEnd_3512088 < baseStart_3512088 := by decide
  rcases family_descends (prefixWord ++ tailWord_3512088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3512192 : List Nat := [2, 1, 1, 2, 1, 2, 4, 3, 3, 1, 3]
def baseStart_3512192 : Nat := 118140960795 + 3512192 * 2 ^ 59
def prefixEnd_3512192 : Nat := 4983230072969 + 3 ^ 40 * 3512192 * 2
def baseEnd_3512192 : Nat := 1803442646876027766347729

theorem tailTrace_3512192 : CollatzResearch.WordTrace tailWord_3512192 prefixEnd_3512192 1803442646876027766347729 := by
  unfold tailWord_3512192
  simp only [CollatzResearch.WordTrace]
  refine ⟨64050083045967846741717415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85400110727957128988956553 64050083045967846741717415)
  ·
    refine ⟨96075124568951770112576123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64050083045967846741717415 96075124568951770112576123)
    ·
      refine ⟨144112686853427655168864185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96075124568951770112576123 144112686853427655168864185)
      ·
        refine ⟨108084515140070741376648139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144112686853427655168864185 108084515140070741376648139)
        ·
          refine ⟨162126772710106112064972209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108084515140070741376648139 162126772710106112064972209)
          ·
            refine ⟨121595079532579584048729157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162126772710106112064972209 121595079532579584048729157)
            ·
              refine ⟨22799077412358672009136717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 121595079532579584048729157 22799077412358672009136717)
              ·
                refine ⟨8549654029634502003426269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22799077412358672009136717 8549654029634502003426269)
                ·
                  refine ⟨3206120261112938251284851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8549654029634502003426269 3206120261112938251284851)
                  ·
                    refine ⟨4809180391669407376927277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3206120261112938251284851 4809180391669407376927277)
                    ·
                      refine ⟨1803442646876027766347729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4809180391669407376927277 1803442646876027766347729)
                      ·
                        rfl

theorem cell23_3512192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 3, 3, 1, 3].length) (baseStart_3512192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3512192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3512192 prefixEnd_3512192 := by exact prefixLift 3512192
  have htrace : WordTrace (prefixWord ++ tailWord_3512192) baseStart_3512192 baseEnd_3512192 := by
    simpa [prefixWord, tailWord_3512192, baseEnd_3512192] using wordTrace_append hprefix tailTrace_3512192
  have hstable : (prefixWord ++ tailWord_3512192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3512192).length < 2 ^ (prefixWord ++ tailWord_3512192).sum := by decide
  have hdescent : baseEnd_3512192 < baseStart_3512192 := by decide
  rcases family_descends (prefixWord ++ tailWord_3512192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3512195 : List Nat := [1, 1, 1, 3, 4, 2, 1, 2, 3, 5]
def baseStart_3512195 : Nat := 118140960795 + 3512195 * 2 ^ 59
def prefixEnd_3512195 : Nat := 4983230072969 + 3 ^ 40 * 3512195 * 2
def baseEnd_3512195 : Nat := 601148062439330418203405

theorem tailTrace_3512195 : CollatzResearch.WordTrace tailWord_3512195 prefixEnd_3512195 601148062439330418203405 := by
  unfold tailWord_3512195
  simp only [CollatzResearch.WordTrace]
  refine ⟨128100275510924824995794039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85400183673949883330529359 128100275510924824995794039)
  ·
    refine ⟨192150413266387237493691059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128100275510924824995794039 192150413266387237493691059)
    ·
      refine ⟨288225619899580856240536589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192150413266387237493691059 288225619899580856240536589)
      ·
        refine ⟨108084607462342821090201221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 288225619899580856240536589 108084607462342821090201221)
        ·
          refine ⟨20265863899189278954412729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108084607462342821090201221 20265863899189278954412729)
          ·
            refine ⟨15199397924391959215809547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20265863899189278954412729 15199397924391959215809547)
            ·
              refine ⟨22799096886587938823714321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15199397924391959215809547 22799096886587938823714321)
              ·
                refine ⟨17099322664940954117785741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22799096886587938823714321 17099322664940954117785741)
                ·
                  refine ⟨6412245999352857794169653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17099322664940954117785741 6412245999352857794169653)
                  ·
                    refine ⟨601148062439330418203405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6412245999352857794169653 601148062439330418203405)
                    ·
                      rfl

theorem cell23_3512195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 2, 3, 5].length) (baseStart_3512195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3512195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3512195 prefixEnd_3512195 := by exact prefixLift 3512195
  have htrace : WordTrace (prefixWord ++ tailWord_3512195) baseStart_3512195 baseEnd_3512195 := by
    simpa [prefixWord, tailWord_3512195, baseEnd_3512195] using wordTrace_append hprefix tailTrace_3512195
  have hstable : (prefixWord ++ tailWord_3512195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3512195).length < 2 ^ (prefixWord ++ tailWord_3512195).sum := by decide
  have hdescent : baseEnd_3512195 < baseStart_3512195 := by decide
  rcases family_descends (prefixWord ++ tailWord_3512195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3512212 : List Nat := [2, 4, 2, 1, 1, 2, 2, 1, 3, 5]
def baseStart_3512212 : Nat := 118140960795 + 3512212 * 2 ^ 59
def prefixEnd_3512212 : Nat := 4983230072969 + 3 ^ 40 * 3512212 * 2
def baseEnd_3512212 : Nat := 601150972163039229365879

theorem tailTrace_3512212 : CollatzResearch.WordTrace tailWord_3512212 prefixEnd_3512212 601150972163039229365879 := by
  unfold tailWord_3512212
  simp only [CollatzResearch.WordTrace]
  refine ⟨64050447775931618449581445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85400597034575491266108593 64050447775931618449581445)
  ·
    refine ⟨12009458957987178459296521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64050447775931618449581445 12009458957987178459296521)
    ·
      refine ⟨9007094218490383844472391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12009458957987178459296521 9007094218490383844472391)
      ·
        refine ⟨13510641327735575766708587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9007094218490383844472391 13510641327735575766708587)
        ·
          refine ⟨20265961991603363650062881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13510641327735575766708587 20265961991603363650062881)
          ·
            refine ⟨15199471493702522737547161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20265961991603363650062881 15199471493702522737547161)
            ·
              refine ⟨11399603620276892053160371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15199471493702522737547161 11399603620276892053160371)
              ·
                refine ⟨17099405430415338079740557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11399603620276892053160371 17099405430415338079740557)
                ·
                  refine ⟨6412277036405751779902709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17099405430415338079740557 6412277036405751779902709)
                  ·
                    refine ⟨601150972163039229365879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6412277036405751779902709 601150972163039229365879)
                    ·
                      rfl

theorem cell23_3512212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 1, 3, 5].length) (baseStart_3512212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3512212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3512212 prefixEnd_3512212 := by exact prefixLift 3512212
  have htrace : WordTrace (prefixWord ++ tailWord_3512212) baseStart_3512212 baseEnd_3512212 := by
    simpa [prefixWord, tailWord_3512212, baseEnd_3512212] using wordTrace_append hprefix tailTrace_3512212
  have hstable : (prefixWord ++ tailWord_3512212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3512212).length < 2 ^ (prefixWord ++ tailWord_3512212).sum := by decide
  have hdescent : baseEnd_3512212 < baseStart_3512212 := by decide
  rcases family_descends (prefixWord ++ tailWord_3512212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3512310 : List Nat := [5, 1, 1, 1, 5, 1, 2, 1, 2, 4]
def baseStart_3512310 : Nat := 118140960795 + 3512310 * 2 ^ 59
def prefixEnd_3512310 : Nat := 4983230072969 + 3 ^ 40 * 3512310 * 2
def baseEnd_3512310 : Nat := 601167745864419434890729

theorem tailTrace_3512310 : CollatzResearch.WordTrace tailWord_3512310 prefixEnd_3512310 601167745864419434890729 := by
  unfold tailWord_3512310
  simp only [CollatzResearch.WordTrace]
  refine ⟨8006529369094262477264399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 85402979937005466424153589 8006529369094262477264399)
  ·
    refine ⟨12009794053641393715896599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8006529369094262477264399 12009794053641393715896599)
    ·
      refine ⟨18014691080462090573844899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12009794053641393715896599 18014691080462090573844899)
      ·
        refine ⟨27022036620693135860767349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18014691080462090573844899 27022036620693135860767349)
        ·
          refine ⟨2533315933189981486946939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27022036620693135860767349 2533315933189981486946939)
          ·
            refine ⟨3799973899784972230420409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2533315933189981486946939 3799973899784972230420409)
            ·
              refine ⟨2849980424838729172815307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3799973899784972230420409 2849980424838729172815307)
              ·
                refine ⟨4274970637258093759222961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2849980424838729172815307 4274970637258093759222961)
                ·
                  refine ⟨3206227977943570319417221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4274970637258093759222961 3206227977943570319417221)
                  ·
                    refine ⟨601167745864419434890729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3206227977943570319417221 601167745864419434890729)
                    ·
                      rfl

theorem cell23_3512310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 2, 1, 2, 4].length) (baseStart_3512310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3512310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3512310 prefixEnd_3512310 := by exact prefixLift 3512310
  have htrace : WordTrace (prefixWord ++ tailWord_3512310) baseStart_3512310 baseEnd_3512310 := by
    simpa [prefixWord, tailWord_3512310, baseEnd_3512310] using wordTrace_append hprefix tailTrace_3512310
  have hstable : (prefixWord ++ tailWord_3512310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3512310).length < 2 ^ (prefixWord ++ tailWord_3512310).sum := by decide
  have hdescent : baseEnd_3512310 < baseStart_3512310 := by decide
  rcases family_descends (prefixWord ++ tailWord_3512310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3512315 : List Nat := [1, 1, 1, 1, 1, 3, 4, 3, 2, 6]
def baseStart_3512315 : Nat := 118140960795 + 3512315 * 2 ^ 59
def prefixEnd_3512315 : Nat := 4983230072969 + 3 ^ 40 * 3512315 * 2
def baseEnd_3512315 : Nat := 601168601665510261703221

theorem tailTrace_3512315 : CollatzResearch.WordTrace tailWord_3512315 prefixEnd_3512315 601168601665510261703221 := by
  unfold tailWord_3512315
  simp only [CollatzResearch.WordTrace]
  refine ⟨128104652270490085490162399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85403101513660056993441599 128104652270490085490162399)
  ·
    refine ⟨192156978405735128235243599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128104652270490085490162399 192156978405735128235243599)
    ·
      refine ⟨288235467608602692352865399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192156978405735128235243599 288235467608602692352865399)
      ·
        refine ⟨432353201412904038529298099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288235467608602692352865399 432353201412904038529298099)
        ·
          refine ⟨648529802119356057793947149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 432353201412904038529298099 648529802119356057793947149)
          ·
            refine ⟨243198675794758521672730181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 648529802119356057793947149 243198675794758521672730181)
            ·
              refine ⟨45599751711517222813636909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 243198675794758521672730181 45599751711517222813636909)
              ·
                refine ⟨17099906891818958555113841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45599751711517222813636909 17099906891818958555113841)
                ·
                  refine ⟨12824930168864218916335381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17099906891818958555113841 12824930168864218916335381)
                  ·
                    refine ⟨601168601665510261703221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12824930168864218916335381 601168601665510261703221)
                    ·
                      rfl

theorem cell23_3512315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 3, 2, 6].length) (baseStart_3512315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3512315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3512315 prefixEnd_3512315 := by exact prefixLift 3512315
  have htrace : WordTrace (prefixWord ++ tailWord_3512315) baseStart_3512315 baseEnd_3512315 := by
    simpa [prefixWord, tailWord_3512315, baseEnd_3512315] using wordTrace_append hprefix tailTrace_3512315
  have hstable : (prefixWord ++ tailWord_3512315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3512315).length < 2 ^ (prefixWord ++ tailWord_3512315).sum := by decide
  have hdescent : baseEnd_3512315 < baseStart_3512315 := by decide
  rcases family_descends (prefixWord ++ tailWord_3512315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3512339 : List Nat := [1, 1, 1, 2, 1, 4, 2, 1, 6, 2, 2]
def baseStart_3512339 : Nat := 118140960795 + 3512339 * 2 ^ 59
def prefixEnd_3512339 : Nat := 4983230072969 + 3 ^ 40 * 3512339 * 2
def baseEnd_3512339 : Nat := 1803518128532238691209553

theorem tailTrace_3512339 : CollatzResearch.WordTrace tailWord_3512339 prefixEnd_3512339 1803518128532238691209553 := by
  unfold tailWord_3512339
  simp only [CollatzResearch.WordTrace]
  refine ⟨128105527622403137589036071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85403685081602091726024047 128105527622403137589036071)
  ·
    refine ⟨192158291433604706383554107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128105527622403137589036071 192158291433604706383554107)
    ·
      refine ⟨288237437150407059575331161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192158291433604706383554107 288237437150407059575331161)
      ·
        refine ⟨216178077862805294681498371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 288237437150407059575331161 216178077862805294681498371)
        ·
          refine ⟨324267116794207942022247557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216178077862805294681498371 324267116794207942022247557)
          ·
            refine ⟨60800084398913989129171417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 324267116794207942022247557 60800084398913989129171417)
            ·
              refine ⟨45600063299185491846878563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60800084398913989129171417 45600063299185491846878563)
              ·
                refine ⟨68400094948778237770317845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45600063299185491846878563 68400094948778237770317845)
                ·
                  refine ⟨3206254450723979895483649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 68400094948778237770317845 3206254450723979895483649)
                  ·
                    refine ⟨2404690838042984921612737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3206254450723979895483649 2404690838042984921612737)
                    ·
                      refine ⟨1803518128532238691209553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2404690838042984921612737 1803518128532238691209553)
                      ·
                        rfl

theorem cell23_3512339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 6, 2, 2].length) (baseStart_3512339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3512339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3512339 prefixEnd_3512339 := by exact prefixLift 3512339
  have htrace : WordTrace (prefixWord ++ tailWord_3512339) baseStart_3512339 baseEnd_3512339 := by
    simpa [prefixWord, tailWord_3512339, baseEnd_3512339] using wordTrace_append hprefix tailTrace_3512339
  have hstable : (prefixWord ++ tailWord_3512339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3512339).length < 2 ^ (prefixWord ++ tailWord_3512339).sum := by decide
  have hdescent : baseEnd_3512339 < baseStart_3512339 := by decide
  rcases family_descends (prefixWord ++ tailWord_3512339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3512392 : List Nat := [2, 1, 3, 1, 1, 1, 2, 5, 2, 5]
def baseStart_3512392 : Nat := 118140960795 + 3512392 * 2 ^ 59
def prefixEnd_3512392 : Nat := 4983230072969 + 3 ^ 40 * 3512392 * 2
def baseEnd_3512392 : Nat := 601181781002308994615603

theorem tailTrace_3512392 : CollatzResearch.WordTrace tailWord_3512392 prefixEnd_3512392 601181781002308994615603 := by
  unfold tailWord_3512392
  simp only [CollatzResearch.WordTrace]
  refine ⟨64053730345605563820357715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85404973794140751760476953 64053730345605563820357715)
  ·
    refine ⟨96080595518408345730536573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64053730345605563820357715 96080595518408345730536573)
    ·
      refine ⟨36030223319403129648951215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96080595518408345730536573 36030223319403129648951215)
      ·
        refine ⟨54045334979104694473426823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36030223319403129648951215 54045334979104694473426823)
        ·
          refine ⟨81068002468657041710140235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54045334979104694473426823 81068002468657041710140235)
          ·
            refine ⟨121602003702985562565210353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81068002468657041710140235 121602003702985562565210353)
            ·
              refine ⟨91201502777239171923907765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121602003702985562565210353 91201502777239171923907765)
              ·
                refine ⟨8550140885366172367866353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 91201502777239171923907765 8550140885366172367866353)
                ·
                  refine ⟨6412605664024629275899765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8550140885366172367866353 6412605664024629275899765)
                  ·
                    refine ⟨601181781002308994615603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6412605664024629275899765 601181781002308994615603)
                    ·
                      rfl

theorem cell23_3512392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 5, 2, 5].length) (baseStart_3512392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3512392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3512392 prefixEnd_3512392 := by exact prefixLift 3512392
  have htrace : WordTrace (prefixWord ++ tailWord_3512392) baseStart_3512392 baseEnd_3512392 := by
    simpa [prefixWord, tailWord_3512392, baseEnd_3512392] using wordTrace_append hprefix tailTrace_3512392
  have hstable : (prefixWord ++ tailWord_3512392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3512392).length < 2 ^ (prefixWord ++ tailWord_3512392).sum := by decide
  have hdescent : baseEnd_3512392 < baseStart_3512392 := by decide
  rcases family_descends (prefixWord ++ tailWord_3512392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3512439 : List Nat := [1, 1, 3, 1, 1, 5, 2, 2, 3, 4]
def baseStart_3512439 : Nat := 118140960795 + 3512439 * 2 ^ 59
def prefixEnd_3512439 : Nat := 4983230072969 + 3 ^ 40 * 3512439 * 2
def baseEnd_3512439 : Nat := 601189825532562766653031

theorem tailTrace_3512439 : CollatzResearch.WordTrace tailWord_3512439 prefixEnd_3512439 601189825532562766653031 := by
  unfold tailWord_3512439
  simp only [CollatzResearch.WordTrace]
  refine ⟨128109174922040854667676371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85406116614693903111784247 128109174922040854667676371)
  ·
    refine ⟨192163762383061282001514557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128109174922040854667676371 192163762383061282001514557)
    ·
      refine ⟨72061410893647980750567959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192163762383061282001514557 72061410893647980750567959)
      ·
        refine ⟨108092116340471971125851939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72061410893647980750567959 108092116340471971125851939)
        ·
          refine ⟨162138174510707956688777909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108092116340471971125851939 162138174510707956688777909)
          ·
            refine ⟨15200453860378870939572929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 162138174510707956688777909 15200453860378870939572929)
            ·
              refine ⟨11400340395284153204679697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15200453860378870939572929 11400340395284153204679697)
              ·
                refine ⟨8550255296463114903509773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11400340395284153204679697 8550255296463114903509773)
                ·
                  refine ⟨3206345736173668088816165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8550255296463114903509773 3206345736173668088816165)
                  ·
                    refine ⟨601189825532562766653031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3206345736173668088816165 601189825532562766653031)
                    ·
                      rfl

theorem cell23_3512439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 2, 3, 4].length) (baseStart_3512439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3512439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3512439 prefixEnd_3512439 := by exact prefixLift 3512439
  have htrace : WordTrace (prefixWord ++ tailWord_3512439) baseStart_3512439 baseEnd_3512439 := by
    simpa [prefixWord, tailWord_3512439, baseEnd_3512439] using wordTrace_append hprefix tailTrace_3512439
  have hstable : (prefixWord ++ tailWord_3512439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3512439).length < 2 ^ (prefixWord ++ tailWord_3512439).sum := by decide
  have hdescent : baseEnd_3512439 < baseStart_3512439 := by decide
  rcases family_descends (prefixWord ++ tailWord_3512439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3512452 : List Nat := [2, 3, 2, 1, 2, 1, 1, 1, 10]
def baseStart_3512452 : Nat := 118140960795 + 3512452 * 2 ^ 59
def prefixEnd_3512452 : Nat := 4983230072969 + 3 ^ 40 * 3512452 * 2
def baseEnd_3512452 : Nat := 200397350205132972121837

theorem tailTrace_3512452 : CollatzResearch.WordTrace tailWord_3512452 prefixEnd_3512452 200397350205132972121837 := by
  unfold tailWord_3512452
  simp only [CollatzResearch.WordTrace]
  refine ⟨64054824535496878943949805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85406432713995838591933073 64054824535496878943949805)
  ·
    refine ⟨24020559200811329603981177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64054824535496878943949805 24020559200811329603981177)
    ·
      refine ⟨18015419400608497202985883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24020559200811329603981177 18015419400608497202985883)
      ·
        refine ⟨27023129100912745804478825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18015419400608497202985883 27023129100912745804478825)
        ·
          refine ⟨20267346825684559353359119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27023129100912745804478825 20267346825684559353359119)
          ·
            refine ⟨30401020238526839030038679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20267346825684559353359119 30401020238526839030038679)
            ·
              refine ⟨45601530357790258545058019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30401020238526839030038679 45601530357790258545058019)
              ·
                refine ⟨68402295536685387817587029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45601530357790258545058019 68402295536685387817587029)
                ·
                  refine ⟨200397350205132972121837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 68402295536685387817587029 200397350205132972121837)
                  ·
                    rfl

theorem cell23_3512452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 10].length) (baseStart_3512452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3512452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3512452 prefixEnd_3512452 := by exact prefixLift 3512452
  have htrace : WordTrace (prefixWord ++ tailWord_3512452) baseStart_3512452 baseEnd_3512452 := by
    simpa [prefixWord, tailWord_3512452, baseEnd_3512452] using wordTrace_append hprefix tailTrace_3512452
  have hstable : (prefixWord ++ tailWord_3512452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3512452).length < 2 ^ (prefixWord ++ tailWord_3512452).sum := by decide
  have hdescent : baseEnd_3512452 < baseStart_3512452 := by decide
  rcases family_descends (prefixWord ++ tailWord_3512452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3512466 : List Nat := [3, 2, 3, 1, 1, 1, 3, 2, 2, 2, 3]
def baseStart_3512466 : Nat := 118140960795 + 3512466 * 2 ^ 59
def prefixEnd_3512466 : Nat := 4983230072969 + 3 ^ 40 * 3512466 * 2
def baseEnd_3512466 : Nat := 1803583340575359694321469

theorem tailTrace_3512466 : CollatzResearch.WordTrace tailWord_3512466 prefixEnd_3512466 1803583340575359694321469 := by
  unfold tailWord_3512466
  simp only [CollatzResearch.WordTrace]
  refine ⟨32027539923235759569727313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85406773128628692185939501 32027539923235759569727313)
  ·
    refine ⟨24020654942426819677295485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32027539923235759569727313 24020654942426819677295485)
    ·
      refine ⟨9007745603410057378985807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24020654942426819677295485 9007745603410057378985807)
      ·
        refine ⟨13511618405115086068478711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9007745603410057378985807 13511618405115086068478711)
        ·
          refine ⟨20267427607672629102718067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13511618405115086068478711 20267427607672629102718067)
          ·
            refine ⟨30401141411508943654077101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20267427607672629102718067 30401141411508943654077101)
            ·
              refine ⟨11400428029315853870278913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30401141411508943654077101 11400428029315853870278913)
              ·
                refine ⟨8550321021986890402709185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11400428029315853870278913 8550321021986890402709185)
                ·
                  refine ⟨6412740766490167802031889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8550321021986890402709185 6412740766490167802031889)
                  ·
                    refine ⟨4809555574867625851523917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6412740766490167802031889 4809555574867625851523917)
                    ·
                      refine ⟨1803583340575359694321469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4809555574867625851523917 1803583340575359694321469)
                      ·
                        rfl

theorem cell23_3512466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 2, 2, 2, 3].length) (baseStart_3512466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3512466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3512466 prefixEnd_3512466 := by exact prefixLift 3512466
  have htrace : WordTrace (prefixWord ++ tailWord_3512466) baseStart_3512466 baseEnd_3512466 := by
    simpa [prefixWord, tailWord_3512466, baseEnd_3512466] using wordTrace_append hprefix tailTrace_3512466
  have hstable : (prefixWord ++ tailWord_3512466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3512466).length < 2 ^ (prefixWord ++ tailWord_3512466).sum := by decide
  have hdescent : baseEnd_3512466 < baseStart_3512466 := by decide
  rcases family_descends (prefixWord ++ tailWord_3512466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3512506 : List Nat := [3, 1, 1, 1, 2, 2, 3, 3, 2, 3, 2]
def baseStart_3512506 : Nat := 118140960795 + 3512506 * 2 ^ 59
def prefixEnd_3512506 : Nat := 4983230072969 + 3 ^ 40 * 3512506 * 2
def baseEnd_3512506 : Nat := 1803603879801539537821285

theorem tailTrace_3512506 : CollatzResearch.WordTrace tailWord_3512506 prefixEnd_3512506 1803603879801539537821285 := by
  unfold tailWord_3512506
  simp only [CollatzResearch.WordTrace]
  refine ⟨32027904653199531277591343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85407745741865416740243581 32027904653199531277591343)
  ·
    refine ⟨48041856979799296916387015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32027904653199531277591343 48041856979799296916387015)
    ·
      refine ⟨72062785469698945374580523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48041856979799296916387015 72062785469698945374580523)
      ·
        refine ⟨108094178204548418061870785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72062785469698945374580523 108094178204548418061870785)
        ·
          refine ⟨81070633653411313546403089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108094178204548418061870785 81070633653411313546403089)
          ·
            refine ⟨60802975240058485159802317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81070633653411313546403089 60802975240058485159802317)
            ·
              refine ⟨22801115715021931934925869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60802975240058485159802317 22801115715021931934925869)
              ·
                refine ⟨8550418393133224475597201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22801115715021931934925869 8550418393133224475597201)
                ·
                  refine ⟨6412813794849918356697901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8550418393133224475597201 6412813794849918356697901)
                  ·
                    refine ⟨2404805173068719383761713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6412813794849918356697901 2404805173068719383761713)
                    ·
                      refine ⟨1803603879801539537821285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2404805173068719383761713 1803603879801539537821285)
                      ·
                        rfl

theorem cell23_3512506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 3, 2, 3, 2].length) (baseStart_3512506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3512506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3512506 prefixEnd_3512506 := by exact prefixLift 3512506
  have htrace : WordTrace (prefixWord ++ tailWord_3512506) baseStart_3512506 baseEnd_3512506 := by
    simpa [prefixWord, tailWord_3512506, baseEnd_3512506] using wordTrace_append hprefix tailTrace_3512506
  have hstable : (prefixWord ++ tailWord_3512506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3512506).length < 2 ^ (prefixWord ++ tailWord_3512506).sum := by decide
  have hdescent : baseEnd_3512506 < baseStart_3512506 := by decide
  rcases family_descends (prefixWord ++ tailWord_3512506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3512524 : List Nat := [2, 2, 1, 6, 2, 1, 2, 2, 1, 4]
def baseStart_3512524 : Nat := 118140960795 + 3512524 * 2 ^ 59
def prefixEnd_3512524 : Nat := 4983230072969 + 3 ^ 40 * 3512524 * 2
def baseEnd_3512524 : Nat := 601204374151106822465401

theorem tailTrace_3512524 : CollatzResearch.WordTrace tailWord_3512524 prefixEnd_3512524 601204374151106822465401 := by
  unfold tailWord_3512524
  simp only [CollatzResearch.WordTrace]
  refine ⟨64056137563366457092260313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85408183417821942789680417 64056137563366457092260313)
  ·
    refine ⟨48042103172524842819195235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64056137563366457092260313 48042103172524842819195235)
    ·
      refine ⟨72063154758787264228792853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48042103172524842819195235 72063154758787264228792853)
      ·
        refine ⟨3377960379318153010724665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 72063154758787264228792853 3377960379318153010724665)
        ·
          refine ⟨2533470284488614758043499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3377960379318153010724665 2533470284488614758043499)
          ·
            refine ⟨3800205426732922137065249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2533470284488614758043499 3800205426732922137065249)
            ·
              refine ⟨2850154070049691602798937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3800205426732922137065249 2850154070049691602798937)
              ·
                refine ⟨2137615552537268702099203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2850154070049691602798937 2137615552537268702099203)
                ·
                  refine ⟨3206423328805903053148805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2137615552537268702099203 3206423328805903053148805)
                  ·
                    refine ⟨601204374151106822465401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3206423328805903053148805 601204374151106822465401)
                    ·
                      rfl

theorem cell23_3512524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 2, 2, 1, 4].length) (baseStart_3512524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3512524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3512524 prefixEnd_3512524 := by exact prefixLift 3512524
  have htrace : WordTrace (prefixWord ++ tailWord_3512524) baseStart_3512524 baseEnd_3512524 := by
    simpa [prefixWord, tailWord_3512524, baseEnd_3512524] using wordTrace_append hprefix tailTrace_3512524
  have hstable : (prefixWord ++ tailWord_3512524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3512524).length < 2 ^ (prefixWord ++ tailWord_3512524).sum := by decide
  have hdescent : baseEnd_3512524 < baseStart_3512524 := by decide
  rcases family_descends (prefixWord ++ tailWord_3512524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3512529 : List Nat := [1, 2, 2, 1, 2, 2, 2, 3, 4, 4]
def baseStart_3512529 : Nat := 118140960795 + 3512529 * 2 ^ 59
def prefixEnd_3512529 : Nat := 4983230072969 + 3 ^ 40 * 3512529 * 2
def baseEnd_3512529 : Nat := 601205229952197649277893

theorem tailTrace_3512529 : CollatzResearch.WordTrace tailWord_3512529 prefixEnd_3512529 601205229952197649277893 := by
  unfold tailWord_3512529
  simp only [CollatzResearch.WordTrace]
  refine ⟨128112457491714800038452641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85408304994476533358968427 128112457491714800038452641)
  ·
    refine ⟨96084343118786100028839481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128112457491714800038452641 96084343118786100028839481)
    ·
      refine ⟨72063257339089575021629611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96084343118786100028839481 72063257339089575021629611)
      ·
        refine ⟨108094886008634362532444417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72063257339089575021629611 108094886008634362532444417)
        ·
          refine ⟨81071164506475771899333313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108094886008634362532444417 81071164506475771899333313)
          ·
            refine ⟨60803373379856828924499985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81071164506475771899333313 60803373379856828924499985)
            ·
              refine ⟨45602530034892621693374989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60803373379856828924499985 45602530034892621693374989)
              ·
                refine ⟨17100948763084733135015621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45602530034892621693374989 17100948763084733135015621)
                ·
                  refine ⟨3206427893078387462815429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17100948763084733135015621 3206427893078387462815429)
                  ·
                    refine ⟨601205229952197649277893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3206427893078387462815429 601205229952197649277893)
                    ·
                      rfl

theorem cell23_3512529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 3, 4, 4].length) (baseStart_3512529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3512529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3512529 prefixEnd_3512529 := by exact prefixLift 3512529
  have htrace : WordTrace (prefixWord ++ tailWord_3512529) baseStart_3512529 baseEnd_3512529 := by
    simpa [prefixWord, tailWord_3512529, baseEnd_3512529] using wordTrace_append hprefix tailTrace_3512529
  have hstable : (prefixWord ++ tailWord_3512529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3512529).length < 2 ^ (prefixWord ++ tailWord_3512529).sum := by decide
  have hdescent : baseEnd_3512529 < baseStart_3512529 := by decide
  rcases family_descends (prefixWord ++ tailWord_3512529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3512530 : List Nat := [3, 2, 2, 2, 1, 3, 1, 4, 1, 1, 3]
def baseStart_3512530 : Nat := 118140960795 + 3512530 * 2 ^ 59
def prefixEnd_3512530 : Nat := 4983230072969 + 3 ^ 40 * 3512530 * 2
def baseEnd_3512530 : Nat := 1803616203337247443921175

theorem tailTrace_3512530 : CollatzResearch.WordTrace tailWord_3512530 prefixEnd_3512530 1803616203337247443921175 := by
  unfold tailWord_3512530
  simp only [CollatzResearch.WordTrace]
  refine ⟨32028123491177794302309761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85408329309807451472826029 32028123491177794302309761)
  ·
    refine ⟨24021092618383345726732321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32028123491177794302309761 24021092618383345726732321)
    ·
      refine ⟨18015819463787509295049241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24021092618383345726732321 18015819463787509295049241)
      ·
        refine ⟨13511864597840631971286931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18015819463787509295049241 13511864597840631971286931)
        ·
          refine ⟨20267796896760947956930397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13511864597840631971286931 20267796896760947956930397)
          ·
            refine ⟨7600423836285355483848899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20267796896760947956930397 7600423836285355483848899)
            ·
              refine ⟨11400635754428033225773349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7600423836285355483848899 11400635754428033225773349)
              ·
                refine ⟨2137619203955256229832503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11400635754428033225773349 2137619203955256229832503)
                ·
                  refine ⟨3206428805932884344748755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2137619203955256229832503 3206428805932884344748755)
                  ·
                    refine ⟨4809643208899326517123133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3206428805932884344748755 4809643208899326517123133)
                    ·
                      refine ⟨1803616203337247443921175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4809643208899326517123133 1803616203337247443921175)
                      ·
                        rfl

theorem cell23_3512530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 4, 1, 1, 3].length) (baseStart_3512530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3512530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3512530 prefixEnd_3512530 := by exact prefixLift 3512530
  have htrace : WordTrace (prefixWord ++ tailWord_3512530) baseStart_3512530 baseEnd_3512530 := by
    simpa [prefixWord, tailWord_3512530, baseEnd_3512530] using wordTrace_append hprefix tailTrace_3512530
  have hstable : (prefixWord ++ tailWord_3512530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3512530).length < 2 ^ (prefixWord ++ tailWord_3512530).sum := by decide
  have hdescent : baseEnd_3512530 < baseStart_3512530 := by decide
  rcases family_descends (prefixWord ++ tailWord_3512530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3512539 : List Nat := [1, 1, 1, 1, 1, 1, 1, 8, 3, 2, 3]
def baseStart_3512539 : Nat := 118140960795 + 3512539 * 2 ^ 59
def prefixEnd_3512539 : Nat := 4983230072969 + 3 ^ 40 * 3512539 * 2
def baseEnd_3512539 : Nat := 1803620824663137908708633

theorem tailTrace_3512539 : CollatzResearch.WordTrace tailWord_3512539 prefixEnd_3512539 1803620824663137908708633 := by
  unfold tailWord_3512539
  simp only [CollatzResearch.WordTrace]
  refine ⟨128112822221678571746316671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85408548147785714497544447 128112822221678571746316671)
  ·
    refine ⟨192169233332517857619475007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128112822221678571746316671 192169233332517857619475007)
    ·
      refine ⟨288253849998776786429212511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192169233332517857619475007 288253849998776786429212511)
      ·
        refine ⟨432380774998165179643818767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288253849998776786429212511 432380774998165179643818767)
        ·
          refine ⟨648571162497247769465728151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 432380774998165179643818767 648571162497247769465728151)
          ·
            refine ⟨972856743745871654198592227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 648571162497247769465728151 972856743745871654198592227)
            ·
              refine ⟨1459285115618807481297888341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 972856743745871654198592227 1459285115618807481297888341)
              ·
                refine ⟨17100997448657900171459629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1459285115618807481297888341 17100997448657900171459629)
                ·
                  refine ⟨6412874043246712564297361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17100997448657900171459629 6412874043246712564297361)
                  ·
                    refine ⟨4809655532435034423223021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6412874043246712564297361 4809655532435034423223021)
                    ·
                      refine ⟨1803620824663137908708633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4809655532435034423223021 1803620824663137908708633)
                      ·
                        rfl

theorem cell23_3512539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 8, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 8, 3, 2, 3].length) (baseStart_3512539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3512539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3512539 prefixEnd_3512539 := by exact prefixLift 3512539
  have htrace : WordTrace (prefixWord ++ tailWord_3512539) baseStart_3512539 baseEnd_3512539 := by
    simpa [prefixWord, tailWord_3512539, baseEnd_3512539] using wordTrace_append hprefix tailTrace_3512539
  have hstable : (prefixWord ++ tailWord_3512539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3512539).length < 2 ^ (prefixWord ++ tailWord_3512539).sum := by decide
  have hdescent : baseEnd_3512539 < baseStart_3512539 := by decide
  rcases family_descends (prefixWord ++ tailWord_3512539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3512556 : List Nat := [2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 3]
def baseStart_3512556 : Nat := 118140960795 + 3512556 * 2 ^ 59
def prefixEnd_3512556 : Nat := 4983230072969 + 3 ^ 40 * 3512556 * 2
def baseEnd_3512556 : Nat := 1803629553834264342196055

theorem tailTrace_3512556 : CollatzResearch.WordTrace tailWord_3512556 prefixEnd_3512556 1803629553834264342196055 := by
  unfold tailWord_3512556
  simp only [CollatzResearch.WordTrace]
  refine ⟨64056721131308491824842761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85408961508411322433123681 64056721131308491824842761)
  ·
    refine ⟨48042540848481368868632071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64056721131308491824842761 48042540848481368868632071)
    ·
      refine ⟨72063811272722053302948107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48042540848481368868632071 72063811272722053302948107)
      ·
        refine ⟨108095716909083079954422161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72063811272722053302948107 108095716909083079954422161)
        ·
          refine ⟨81071787681812309965816621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108095716909083079954422161 81071787681812309965816621)
          ·
            refine ⟨30401920380679616237181233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81071787681812309965816621 30401920380679616237181233)
            ·
              refine ⟨22801440285509712177885925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30401920380679616237181233 22801440285509712177885925)
              ·
                refine ⟨4275270053533071033353611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22801440285509712177885925 4275270053533071033353611)
                ·
                  refine ⟨6412905080299606550030417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4275270053533071033353611 6412905080299606550030417)
                  ·
                    refine ⟨4809678810224704912522813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6412905080299606550030417 4809678810224704912522813)
                    ·
                      refine ⟨1803629553834264342196055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4809678810224704912522813 1803629553834264342196055)
                      ·
                        rfl

theorem cell23_3512556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 3].length) (baseStart_3512556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3512556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3512556 prefixEnd_3512556 := by exact prefixLift 3512556
  have htrace : WordTrace (prefixWord ++ tailWord_3512556) baseStart_3512556 baseEnd_3512556 := by
    simpa [prefixWord, tailWord_3512556, baseEnd_3512556] using wordTrace_append hprefix tailTrace_3512556
  have hstable : (prefixWord ++ tailWord_3512556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3512556).length < 2 ^ (prefixWord ++ tailWord_3512556).sum := by decide
  have hdescent : baseEnd_3512556 < baseStart_3512556 := by decide
  rcases family_descends (prefixWord ++ tailWord_3512556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3512557 : List Nat := [1, 5, 1, 2, 4, 1, 1, 1, 2, 3, 2]
def baseStart_3512557 : Nat := 118140960795 + 3512557 * 2 ^ 59
def prefixEnd_3512557 : Nat := 4983230072969 + 3 ^ 40 * 3512557 * 2
def baseEnd_3512557 : Nat := 1803630067314918838283551

theorem tailTrace_3512557 : CollatzResearch.WordTrace tailWord_3512557 prefixEnd_3512557 1803630067314918838283551 := by
  unfold tailWord_3512557
  simp only [CollatzResearch.WordTrace]
  refine ⟨128113478735613360820471925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85408985823742240546981283 128113478735613360820471925)
  ·
    refine ⟨12010638631463752576919243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 128113478735613360820471925 12010638631463752576919243)
    ·
      refine ⟨18015957947195628865378865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12010638631463752576919243 18015957947195628865378865)
      ·
        refine ⟨13511968460396721649034149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18015957947195628865378865 13511968460396721649034149)
        ·
          refine ⟨2533494086324385309193903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13511968460396721649034149 2533494086324385309193903)
          ·
            refine ⟨3800241129486577963790855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2533494086324385309193903 3800241129486577963790855)
            ·
              refine ⟨5700361694229866945686283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3800241129486577963790855 5700361694229866945686283)
              ·
                refine ⟨8550542541344800418529425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5700361694229866945686283 8550542541344800418529425)
                ·
                  refine ⟨6412906906008600313897069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8550542541344800418529425 6412906906008600313897069)
                  ·
                    refine ⟨2404840089753225117711401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6412906906008600313897069 2404840089753225117711401)
                    ·
                      refine ⟨1803630067314918838283551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2404840089753225117711401 1803630067314918838283551)
                      ·
                        rfl

theorem cell23_3512557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 1, 1, 2, 3, 2].length) (baseStart_3512557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3512557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3512557 prefixEnd_3512557 := by exact prefixLift 3512557
  have htrace : WordTrace (prefixWord ++ tailWord_3512557) baseStart_3512557 baseEnd_3512557 := by
    simpa [prefixWord, tailWord_3512557, baseEnd_3512557] using wordTrace_append hprefix tailTrace_3512557
  have hstable : (prefixWord ++ tailWord_3512557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3512557).length < 2 ^ (prefixWord ++ tailWord_3512557).sum := by decide
  have hdescent : baseEnd_3512557 < baseStart_3512557 := by decide
  rcases family_descends (prefixWord ++ tailWord_3512557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3512566 : List Nat := [5, 1, 1, 1, 1, 1, 4, 2, 1, 2, 4]
def baseStart_3512566 : Nat := 118140960795 + 3512566 * 2 ^ 59
def prefixEnd_3512566 : Nat := 4983230072969 + 3 ^ 40 * 3512566 * 2
def baseEnd_3512566 : Nat := 1803634688640809303071009

theorem tailTrace_3512566 : CollatzResearch.WordTrace tailWord_3512566 prefixEnd_3512566 1803634688640809303071009 := by
  unfold tailWord_3512566
  simp only [CollatzResearch.WordTrace]
  refine ⟨8007112937036297209846847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 85409204661720503571699701 8007112937036297209846847)
  ·
    refine ⟨12010669405554445814770271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8007112937036297209846847 12010669405554445814770271)
    ·
      refine ⟨18016004108331668722155407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12010669405554445814770271 18016004108331668722155407)
      ·
        refine ⟨27024006162497503083233111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18016004108331668722155407 27024006162497503083233111)
        ·
          refine ⟨40536009243746254624849667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27024006162497503083233111 40536009243746254624849667)
          ·
            refine ⟨60804013865619381937274501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40536009243746254624849667 60804013865619381937274501)
            ·
              refine ⟨11400752599803634113238969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60804013865619381937274501 11400752599803634113238969)
              ·
                refine ⟨8550564449852725584929227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11400752599803634113238969 8550564449852725584929227)
                ·
                  refine ⟨12825846674779088377393841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8550564449852725584929227 12825846674779088377393841)
                  ·
                    refine ⟨9619385006084316283045381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12825846674779088377393841 9619385006084316283045381)
                    ·
                      refine ⟨1803634688640809303071009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9619385006084316283045381 1803634688640809303071009)
                      ·
                        rfl

theorem cell23_3512566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 2, 1, 2, 4].length) (baseStart_3512566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3512566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3512566 prefixEnd_3512566 := by exact prefixLift 3512566
  have htrace : WordTrace (prefixWord ++ tailWord_3512566) baseStart_3512566 baseEnd_3512566 := by
    simpa [prefixWord, tailWord_3512566, baseEnd_3512566] using wordTrace_append hprefix tailTrace_3512566
  have hstable : (prefixWord ++ tailWord_3512566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3512566).length < 2 ^ (prefixWord ++ tailWord_3512566).sum := by decide
  have hdescent : baseEnd_3512566 < baseStart_3512566 := by decide
  rcases family_descends (prefixWord ++ tailWord_3512566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3512569 : List Nat := [1, 2, 1, 3, 1, 1, 2, 3, 3, 3, 3]
def baseStart_3512569 : Nat := 118140960795 + 3512569 * 2 ^ 59
def prefixEnd_3512569 : Nat := 4983230072969 + 3 ^ 40 * 3512569 * 2
def baseEnd_3512569 : Nat := 1803636229082772791333495

theorem tailTrace_3512569 : CollatzResearch.WordTrace tailWord_3512569 prefixEnd_3512569 1803636229082772791333495 := by
  unfold tailWord_3512569
  simp only [CollatzResearch.WordTrace]
  refine ⟨128113916411569886869908761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85409277607713257913272507 128113916411569886869908761)
  ·
    refine ⟨96085437308677415152431571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128113916411569886869908761 96085437308677415152431571)
    ·
      refine ⟨144128155963016122728647357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96085437308677415152431571 144128155963016122728647357)
      ·
        refine ⟨54048058486131046023242759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144128155963016122728647357 54048058486131046023242759)
        ·
          refine ⟨81072087729196569034864139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54048058486131046023242759 81072087729196569034864139)
          ·
            refine ⟨121608131593794853552296209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81072087729196569034864139 121608131593794853552296209)
            ·
              refine ⟨91206098695346140164222157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121608131593794853552296209 91206098695346140164222157)
              ·
                refine ⟨34202287010754802561583309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91206098695346140164222157 34202287010754802561583309)
                ·
                  refine ⟨12825857629033050960593741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34202287010754802561583309 12825857629033050960593741)
                  ·
                    refine ⟨4809696610887394110222653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12825857629033050960593741 4809696610887394110222653)
                    ·
                      refine ⟨1803636229082772791333495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4809696610887394110222653 1803636229082772791333495)
                      ·
                        rfl

theorem cell23_3512569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 3, 3, 3, 3].length) (baseStart_3512569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3512569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3512569 prefixEnd_3512569 := by exact prefixLift 3512569
  have htrace : WordTrace (prefixWord ++ tailWord_3512569) baseStart_3512569 baseEnd_3512569 := by
    simpa [prefixWord, tailWord_3512569, baseEnd_3512569] using wordTrace_append hprefix tailTrace_3512569
  have hstable : (prefixWord ++ tailWord_3512569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3512569).length < 2 ^ (prefixWord ++ tailWord_3512569).sum := by decide
  have hdescent : baseEnd_3512569 < baseStart_3512569 := by decide
  rcases family_descends (prefixWord ++ tailWord_3512569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3512570 : List Nat := [3, 1, 1, 1, 1, 5, 1, 5, 1, 2, 2]
def baseStart_3512570 : Nat := 118140960795 + 3512570 * 2 ^ 59
def prefixEnd_3512570 : Nat := 4983230072969 + 3 ^ 40 * 3512570 * 2
def baseEnd_3512570 : Nat := 1803636742563427287420991

theorem tailTrace_3512570 : CollatzResearch.WordTrace tailWord_3512570 prefixEnd_3512570 1803636742563427287420991 := by
  unfold tailWord_3512570
  simp only [CollatzResearch.WordTrace]
  refine ⟨32028488221141566010173791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85409301923044176027130109 32028488221141566010173791)
  ·
    refine ⟨48042732331712349015260687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32028488221141566010173791 48042732331712349015260687)
    ·
      refine ⟨72064098497568523522891031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48042732331712349015260687 72064098497568523522891031)
      ·
        refine ⟨108096147746352785284336547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72064098497568523522891031 108096147746352785284336547)
        ·
          refine ⟨162144221619529177926504821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108096147746352785284336547 162144221619529177926504821)
          ·
            refine ⟨15201020776830860430609827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 162144221619529177926504821 15201020776830860430609827)
            ·
              refine ⟨22801531165246290645914741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15201020776830860430609827 22801531165246290645914741)
              ·
                refine ⟨2137643546741839748054507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22801531165246290645914741 2137643546741839748054507)
                ·
                  refine ⟨3206465320112759622081761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2137643546741839748054507 3206465320112759622081761)
                  ·
                    refine ⟨2404848990084569716561321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3206465320112759622081761 2404848990084569716561321)
                    ·
                      refine ⟨1803636742563427287420991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2404848990084569716561321 1803636742563427287420991)
                      ·
                        rfl

theorem cell23_3512570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 5, 1, 2, 2].length) (baseStart_3512570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3512570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3512570 prefixEnd_3512570 := by exact prefixLift 3512570
  have htrace : WordTrace (prefixWord ++ tailWord_3512570) baseStart_3512570 baseEnd_3512570 := by
    simpa [prefixWord, tailWord_3512570, baseEnd_3512570] using wordTrace_append hprefix tailTrace_3512570
  have hstable : (prefixWord ++ tailWord_3512570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3512570).length < 2 ^ (prefixWord ++ tailWord_3512570).sum := by decide
  have hdescent : baseEnd_3512570 < baseStart_3512570 := by decide
  rcases family_descends (prefixWord ++ tailWord_3512570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3512580 : List Nat := [2, 3, 2, 2, 3, 2, 1, 2, 2, 4]
def baseStart_3512580 : Nat := 118140960795 + 3512580 * 2 ^ 59
def prefixEnd_3512580 : Nat := 4983230072969 + 3 ^ 40 * 3512580 * 2
def baseEnd_3512580 : Nat := 601213959123324082765315

theorem tailTrace_3512580 : CollatzResearch.WordTrace tailWord_3512580 prefixEnd_3512580 601213959123324082765315 := by
  unfold tailWord_3512580
  simp only [CollatzResearch.WordTrace]
  refine ⟨64057158807265017874279597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85409545076353357165706129 64057158807265017874279597)
  ·
    refine ⟨24021434552724381702854849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64057158807265017874279597 24021434552724381702854849)
    ·
      refine ⟨18016075914543286277141137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24021434552724381702854849 18016075914543286277141137)
      ·
        refine ⟨13512056935907464707855853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18016075914543286277141137 13512056935907464707855853)
        ·
          refine ⟨5067021350965299265445945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13512056935907464707855853 5067021350965299265445945)
          ·
            refine ⟨3800266013223974449084459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5067021350965299265445945 3800266013223974449084459)
            ·
              refine ⟨5700399019835961673626689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3800266013223974449084459 5700399019835961673626689)
              ·
                refine ⟨4275299264876971255220017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5700399019835961673626689 4275299264876971255220017)
                ·
                  refine ⟨3206474448657728441415013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4275299264876971255220017 3206474448657728441415013)
                  ·
                    refine ⟨601213959123324082765315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3206474448657728441415013 601213959123324082765315)
                    ·
                      rfl

theorem cell23_3512580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 1, 2, 2, 4].length) (baseStart_3512580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3512580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3512580 prefixEnd_3512580 := by exact prefixLift 3512580
  have htrace : WordTrace (prefixWord ++ tailWord_3512580) baseStart_3512580 baseEnd_3512580 := by
    simpa [prefixWord, tailWord_3512580, baseEnd_3512580] using wordTrace_append hprefix tailTrace_3512580
  have hstable : (prefixWord ++ tailWord_3512580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3512580).length < 2 ^ (prefixWord ++ tailWord_3512580).sum := by decide
  have hdescent : baseEnd_3512580 < baseStart_3512580 := by decide
  rcases family_descends (prefixWord ++ tailWord_3512580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3512609 : List Nat := [1, 2, 3, 2, 1, 1, 2, 2, 2, 3, 4]
def baseStart_3512609 : Nat := 118140960795 + 3512609 * 2 ^ 59
def prefixEnd_3512609 : Nat := 4983230072969 + 3 ^ 40 * 3512609 * 2
def baseEnd_3512609 : Nat := 1803656768308952634833311

theorem tailTrace_3512609 : CollatzResearch.WordTrace tailWord_3512609 prefixEnd_3512609 1803656768308952634833311 := by
  unfold tailWord_3512609
  simp only [CollatzResearch.WordTrace]
  refine ⟨128115375331424973701364881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85410250220949982467576587 128115375331424973701364881)
  ·
    refine ⟨96086531498568730276023661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128115375331424973701364881 96086531498568730276023661)
    ·
      refine ⟨36032449311963273853508873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96086531498568730276023661 36032449311963273853508873)
      ·
        refine ⟨27024336983972455390131655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36032449311963273853508873 27024336983972455390131655)
        ·
          refine ⟨40536505475958683085197483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27024336983972455390131655 40536505475958683085197483)
          ·
            refine ⟨60804758213938024627796225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40536505475958683085197483 60804758213938024627796225)
            ·
              refine ⟨45603568660453518470847169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60804758213938024627796225 45603568660453518470847169)
              ·
                refine ⟨34202676495340138853135377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45603568660453518470847169 34202676495340138853135377)
                ·
                  refine ⟨25652007371505104139851533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34202676495340138853135377 25652007371505104139851533)
                  ·
                    refine ⟨9619502764314414052444325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25652007371505104139851533 9619502764314414052444325)
                    ·
                      refine ⟨1803656768308952634833311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9619502764314414052444325 1803656768308952634833311)
                      ·
                        rfl

theorem cell23_3512609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 2, 2, 3, 4].length) (baseStart_3512609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3512609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3512609 prefixEnd_3512609 := by exact prefixLift 3512609
  have htrace : WordTrace (prefixWord ++ tailWord_3512609) baseStart_3512609 baseEnd_3512609 := by
    simpa [prefixWord, tailWord_3512609, baseEnd_3512609] using wordTrace_append hprefix tailTrace_3512609
  have hstable : (prefixWord ++ tailWord_3512609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3512609).length < 2 ^ (prefixWord ++ tailWord_3512609).sum := by decide
  have hdescent : baseEnd_3512609 < baseStart_3512609 := by decide
  rcases family_descends (prefixWord ++ tailWord_3512609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3512621 : List Nat := [1, 5, 3, 1, 2, 2, 1, 3, 1, 2, 2]
def baseStart_3512621 : Nat := 118140960795 + 3512621 * 2 ^ 59
def prefixEnd_3512621 : Nat := 4983230072969 + 3 ^ 40 * 3512621 * 2
def baseEnd_3512621 : Nat := 1803662930076806587883257

theorem tailTrace_3512621 : CollatzResearch.WordTrace tailWord_3512621 prefixEnd_3512621 1803662930076806587883257 := by
  unfold tailWord_3512621
  simp only [CollatzResearch.WordTrace]
  refine ⟨128115813007381499750801717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85410542004920999833867811 128115813007381499750801717)
  ·
    refine ⟨12010857469442015601637661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 128115813007381499750801717 12010857469442015601637661)
    ·
      refine ⟨4504071551040755850614123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12010857469442015601637661 4504071551040755850614123)
      ·
        refine ⟨6756107326561133775921185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4504071551040755850614123 6756107326561133775921185)
        ·
          refine ⟨5067080494920850331940889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6756107326561133775921185 5067080494920850331940889)
          ·
            refine ⟨3800310371190637748955667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5067080494920850331940889 3800310371190637748955667)
            ·
              refine ⟨5700465556785956623433501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3800310371190637748955667 5700465556785956623433501)
              ·
                refine ⟨2137674583794733733787563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5700465556785956623433501 2137674583794733733787563)
                ·
                  refine ⟨3206511875692100600681345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2137674583794733733787563 3206511875692100600681345)
                  ·
                    refine ⟨2404883906769075450511009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3206511875692100600681345 2404883906769075450511009)
                    ·
                      refine ⟨1803662930076806587883257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2404883906769075450511009 1803662930076806587883257)
                      ·
                        rfl

theorem cell23_3512621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 1, 3, 1, 2, 2].length) (baseStart_3512621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3512621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3512621 prefixEnd_3512621 := by exact prefixLift 3512621
  have htrace : WordTrace (prefixWord ++ tailWord_3512621) baseStart_3512621 baseEnd_3512621 := by
    simpa [prefixWord, tailWord_3512621, baseEnd_3512621] using wordTrace_append hprefix tailTrace_3512621
  have hstable : (prefixWord ++ tailWord_3512621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3512621).length < 2 ^ (prefixWord ++ tailWord_3512621).sum := by decide
  have hdescent : baseEnd_3512621 < baseStart_3512621 := by decide
  rcases family_descends (prefixWord ++ tailWord_3512621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3512643 : List Nat := [1, 1, 1, 3, 1, 3, 4, 1, 4, 2, 2]
def baseStart_3512643 : Nat := 118140960795 + 3512643 * 2 ^ 59
def prefixEnd_3512643 : Nat := 4983230072969 + 3 ^ 40 * 3512643 * 2
def baseEnd_3512643 : Nat := 1803674226651205501808155

theorem tailTrace_3512643 : CollatzResearch.WordTrace tailWord_3512643 prefixEnd_3512643 1803674226651205501808155 := by
  unfold tailWord_3512643
  simp only [CollatzResearch.WordTrace]
  refine ⟨128116615413301797508102583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85411076942201198338735055 128116615413301797508102583)
  ·
    refine ⟨192174923119952696262153875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128116615413301797508102583 192174923119952696262153875)
    ·
      refine ⟨288262384679929044393230813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192174923119952696262153875 288262384679929044393230813)
      ·
        refine ⟨108098394254973391647461555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 288262384679929044393230813 108098394254973391647461555)
        ·
          refine ⟨162147591382460087471192333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108098394254973391647461555 162147591382460087471192333)
          ·
            refine ⟨60805346768422532801697125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 162147591382460087471192333 60805346768422532801697125)
            ·
              refine ⟨11401002519079224900318211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60805346768422532801697125 11401002519079224900318211)
              ·
                refine ⟨17101503778618837350477317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11401002519079224900318211 17101503778618837350477317)
                ·
                  refine ⟨3206531958491032003214497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17101503778618837350477317 3206531958491032003214497)
                  ·
                    refine ⟨2404898968868274002410873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3206531958491032003214497 2404898968868274002410873)
                    ·
                      refine ⟨1803674226651205501808155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2404898968868274002410873 1803674226651205501808155)
                      ·
                        rfl

theorem cell23_3512643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 1, 4, 2, 2].length) (baseStart_3512643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3512643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3512643 prefixEnd_3512643 := by exact prefixLift 3512643
  have htrace : WordTrace (prefixWord ++ tailWord_3512643) baseStart_3512643 baseEnd_3512643 := by
    simpa [prefixWord, tailWord_3512643, baseEnd_3512643] using wordTrace_append hprefix tailTrace_3512643
  have hstable : (prefixWord ++ tailWord_3512643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3512643).length < 2 ^ (prefixWord ++ tailWord_3512643).sum := by decide
  have hdescent : baseEnd_3512643 < baseStart_3512643 := by decide
  rcases family_descends (prefixWord ++ tailWord_3512643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3512709 : List Nat := [1, 3, 1, 1, 3, 1, 1, 2, 2, 8]
def baseStart_3512709 : Nat := 118140960795 + 3512709 * 2 ^ 59
def prefixEnd_3512709 : Nat := 4983230072969 + 3 ^ 40 * 3512709 * 2
def baseEnd_3512709 : Nat := 601236038791467414527617

theorem tailTrace_3512709 : CollatzResearch.WordTrace tailWord_3512709 prefixEnd_3512709 601236038791467414527617 := by
  unfold tailWord_3512709
  simp only [CollatzResearch.WordTrace]
  refine ⟨128119022631062690780005181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85412681754041793853336787 128119022631062690780005181)
  ·
    refine ⟨48044633486648509042501943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128119022631062690780005181 48044633486648509042501943)
    ·
      refine ⟨72066950229972763563752915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48044633486648509042501943 72066950229972763563752915)
      ·
        refine ⟨108100425344959145345629373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72066950229972763563752915 108100425344959145345629373)
        ·
          refine ⟨40537659504359679504611015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108100425344959145345629373 40537659504359679504611015)
          ·
            refine ⟨60806489256539519256916523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40537659504359679504611015 60806489256539519256916523)
            ·
              refine ⟨91209733884809278885374785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60806489256539519256916523 91209733884809278885374785)
              ·
                refine ⟨68407300413606959164031089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91209733884809278885374785 68407300413606959164031089)
                ·
                  refine ⟨51305475310205219373023317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68407300413606959164031089 51305475310205219373023317)
                  ·
                    refine ⟨601236038791467414527617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 51305475310205219373023317 601236038791467414527617)
                    ·
                      rfl

theorem cell23_3512709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 2, 8].length) (baseStart_3512709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3512709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3512709 prefixEnd_3512709 := by exact prefixLift 3512709
  have htrace : WordTrace (prefixWord ++ tailWord_3512709) baseStart_3512709 baseEnd_3512709 := by
    simpa [prefixWord, tailWord_3512709, baseEnd_3512709] using wordTrace_append hprefix tailTrace_3512709
  have hstable : (prefixWord ++ tailWord_3512709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3512709).length < 2 ^ (prefixWord ++ tailWord_3512709).sum := by decide
  have hdescent : baseEnd_3512709 < baseStart_3512709 := by decide
  rcases family_descends (prefixWord ++ tailWord_3512709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3512733 : List Nat := [1, 4, 2, 1, 4, 1, 1, 1, 1, 3, 4]
def baseStart_3512733 : Nat := 118140960795 + 3512733 * 2 ^ 59
def prefixEnd_3512733 : Nat := 4983230072969 + 3 ^ 40 * 3512733 * 2
def baseEnd_3512733 : Nat := 1803720439910110149682741

theorem tailTrace_3512733 : CollatzResearch.WordTrace tailWord_3512733 prefixEnd_3512733 1803720439910110149682741 := by
  unfold tailWord_3512733
  simp only [CollatzResearch.WordTrace]
  refine ⟨128119897982975742878878853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85413265321983828585919235 128119897982975742878878853)
  ·
    refine ⟨24022480871807951789789785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128119897982975742878878853 24022480871807951789789785)
    ·
      refine ⟨18016860653855963842342339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24022480871807951789789785 18016860653855963842342339)
      ·
        refine ⟨27025290980783945763513509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18016860653855963842342339 27025290980783945763513509)
        ·
          refine ⟨5067242058896989830658783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27025290980783945763513509 5067242058896989830658783)
          ·
            refine ⟨7600863088345484745988175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5067242058896989830658783 7600863088345484745988175)
            ·
              refine ⟨11401294632518227118982263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7600863088345484745988175 11401294632518227118982263)
              ·
                refine ⟨17101941948777340678473395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11401294632518227118982263 17101941948777340678473395)
                ·
                  refine ⟨25652912923166011017710093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17101941948777340678473395 25652912923166011017710093)
                  ·
                    refine ⟨9619842346187254131641285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25652912923166011017710093 9619842346187254131641285)
                    ·
                      refine ⟨1803720439910110149682741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9619842346187254131641285 1803720439910110149682741)
                      ·
                        rfl

theorem cell23_3512733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 1, 1, 3, 4].length) (baseStart_3512733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3512733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3512733 prefixEnd_3512733 := by exact prefixLift 3512733
  have htrace : WordTrace (prefixWord ++ tailWord_3512733) baseStart_3512733 baseEnd_3512733 := by
    simpa [prefixWord, tailWord_3512733, baseEnd_3512733] using wordTrace_append hprefix tailTrace_3512733
  have hstable : (prefixWord ++ tailWord_3512733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3512733).length < 2 ^ (prefixWord ++ tailWord_3512733).sum := by decide
  have hdescent : baseEnd_3512733 < baseStart_3512733 := by decide
  rcases family_descends (prefixWord ++ tailWord_3512733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3512793 : List Nat := [1, 2, 1, 2, 4, 1, 1, 3, 1, 5, 2]
def baseStart_3512793 : Nat := 118140960795 + 3512793 * 2 ^ 59
def prefixEnd_3512793 : Nat := 4983230072969 + 3 ^ 40 * 3512793 * 2
def baseEnd_3512793 : Nat := 1803751248749379914932465

theorem tailTrace_3512793 : CollatzResearch.WordTrace tailWord_3512793 prefixEnd_3512793 1803751248749379914932465 := by
  unfold tailWord_3512793
  simp only [CollatzResearch.WordTrace]
  refine ⟨128122086362758373126063033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85414724241838915417375355 128122086362758373126063033)
  ·
    refine ⟨96091564772068779844547275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128122086362758373126063033 96091564772068779844547275)
    ·
      refine ⟨144137347158103169766820913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96091564772068779844547275 144137347158103169766820913)
      ·
        refine ⟨108103010368577377325115685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144137347158103169766820913 108103010368577377325115685)
        ·
          refine ⟨20269314444108258248459191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108103010368577377325115685 20269314444108258248459191)
          ·
            refine ⟨30403971666162387372688787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20269314444108258248459191 30403971666162387372688787)
            ·
              refine ⟨45605957499243581059033181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30403971666162387372688787 45605957499243581059033181)
              ·
                refine ⟨17102234062216342897137443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45605957499243581059033181 17102234062216342897137443)
                ·
                  refine ⟨25653351093324514345706165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17102234062216342897137443 25653351093324514345706165)
                  ·
                    refine ⟨2405001664999173219909953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25653351093324514345706165 2405001664999173219909953)
                    ·
                      refine ⟨1803751248749379914932465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2405001664999173219909953 1803751248749379914932465)
                      ·
                        rfl

theorem cell23_3512793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 3, 1, 5, 2].length) (baseStart_3512793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3512793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3512793 prefixEnd_3512793 := by exact prefixLift 3512793
  have htrace : WordTrace (prefixWord ++ tailWord_3512793) baseStart_3512793 baseEnd_3512793 := by
    simpa [prefixWord, tailWord_3512793, baseEnd_3512793] using wordTrace_append hprefix tailTrace_3512793
  have hstable : (prefixWord ++ tailWord_3512793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3512793).length < 2 ^ (prefixWord ++ tailWord_3512793).sum := by decide
  have hdescent : baseEnd_3512793 < baseStart_3512793 := by decide
  rcases family_descends (prefixWord ++ tailWord_3512793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3512810 : List Nat := [3, 1, 3, 1, 3, 1, 1, 1, 4, 3, 2]
def baseStart_3512810 : Nat := 118140960795 + 3512810 * 2 ^ 59
def prefixEnd_3512810 : Nat := 4983230072969 + 3 ^ 40 * 3512810 * 2
def baseEnd_3512810 : Nat := 1803759977920506348419887

theorem tailTrace_3512810 : CollatzResearch.WordTrace tailWord_3512810 prefixEnd_3512810 1803759977920506348419887 := by
  unfold tailWord_3512810
  simp only [CollatzResearch.WordTrace]
  refine ⟨32030676600924196257357971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85415137602464523352954589 32030676600924196257357971)
  ·
    refine ⟨48046014901386294386036957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32030676600924196257357971 48046014901386294386036957)
    ·
      refine ⟨18017255588019860394763859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48046014901386294386036957 18017255588019860394763859)
      ·
        refine ⟨27025883382029790592145789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18017255588019860394763859 27025883382029790592145789)
        ·
          refine ⟨10134706268261171472054671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27025883382029790592145789 10134706268261171472054671)
          ·
            refine ⟨15202059402391757208082007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10134706268261171472054671 15202059402391757208082007)
            ·
              refine ⟨22803089103587635812123011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15202059402391757208082007 22803089103587635812123011)
              ·
                refine ⟨34204633655381453718184517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22803089103587635812123011 34204633655381453718184517)
                ·
                  refine ⟨6413368810384022572159597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34204633655381453718184517 6413368810384022572159597)
                  ·
                    refine ⟨2405013303894008464559849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6413368810384022572159597 2405013303894008464559849)
                    ·
                      refine ⟨1803759977920506348419887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2405013303894008464559849 1803759977920506348419887)
                      ·
                        rfl

theorem cell23_3512810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 4, 3, 2].length) (baseStart_3512810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3512810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3512810 prefixEnd_3512810 := by exact prefixLift 3512810
  have htrace : WordTrace (prefixWord ++ tailWord_3512810) baseStart_3512810 baseEnd_3512810 := by
    simpa [prefixWord, tailWord_3512810, baseEnd_3512810] using wordTrace_append hprefix tailTrace_3512810
  have hstable : (prefixWord ++ tailWord_3512810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3512810).length < 2 ^ (prefixWord ++ tailWord_3512810).sum := by decide
  have hdescent : baseEnd_3512810 < baseStart_3512810 := by decide
  rcases family_descends (prefixWord ++ tailWord_3512810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3512826 : List Nat := [3, 1, 1, 1, 1, 2, 2, 3, 3, 1, 5]
def baseStart_3512826 : Nat := 118140960795 + 3512826 * 2 ^ 59
def prefixEnd_3512826 : Nat := 4983230072969 + 3 ^ 40 * 3512826 * 2
def baseEnd_3512826 : Nat := 1803768193610978285819813

theorem tailTrace_3512826 : CollatzResearch.WordTrace tailWord_3512826 prefixEnd_3512826 1803768193610978285819813 := by
  unfold tailWord_3512826
  simp only [CollatzResearch.WordTrace]
  refine ⟨32030822492909704940503583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85415526647759213174676221 32030822492909704940503583)
  ·
    refine ⟨48046233739364557410755375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32030822492909704940503583 48046233739364557410755375)
    ·
      refine ⟨72069350609046836116133063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48046233739364557410755375 72069350609046836116133063)
      ·
        refine ⟨108104025913570254174199595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72069350609046836116133063 108104025913570254174199595)
        ·
          refine ⟨162156038870355381261299393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108104025913570254174199595 162156038870355381261299393)
          ·
            refine ⟨121617029152766535945974545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162156038870355381261299393 121617029152766535945974545)
            ·
              refine ⟨91212771864574901959480909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121617029152766535945974545 91212771864574901959480909)
              ·
                refine ⟨34204789449215588234805341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91212771864574901959480909 34204789449215588234805341)
                ·
                  refine ⟨12826796043455845588052003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34204789449215588234805341 12826796043455845588052003)
                  ·
                    refine ⟨19240194065183768382078005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12826796043455845588052003 19240194065183768382078005)
                    ·
                      refine ⟨1803768193610978285819813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19240194065183768382078005 1803768193610978285819813)
                      ·
                        rfl

theorem cell23_3512826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 3, 3, 1, 5].length) (baseStart_3512826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3512826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3512826 prefixEnd_3512826 := by exact prefixLift 3512826
  have htrace : WordTrace (prefixWord ++ tailWord_3512826) baseStart_3512826 baseEnd_3512826 := by
    simpa [prefixWord, tailWord_3512826, baseEnd_3512826] using wordTrace_append hprefix tailTrace_3512826
  have hstable : (prefixWord ++ tailWord_3512826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3512826).length < 2 ^ (prefixWord ++ tailWord_3512826).sum := by decide
  have hdescent : baseEnd_3512826 < baseStart_3512826 := by decide
  rcases family_descends (prefixWord ++ tailWord_3512826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3512840 : List Nat := [2, 1, 3, 2, 1, 1, 1, 3, 5, 2, 2]
def baseStart_3512840 : Nat := 118140960795 + 3512840 * 2 ^ 59
def prefixEnd_3512840 : Nat := 4983230072969 + 3 ^ 40 * 3512840 * 2
def baseEnd_3512840 : Nat := 1803775382340141231044749

theorem tailTrace_3512840 : CollatzResearch.WordTrace tailWord_3512840 prefixEnd_3512840 1803775382340141231044749 := by
  unfold tailWord_3512840
  simp only [CollatzResearch.WordTrace]
  refine ⟨64061900296794050076511987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85415867062392066768682649 64061900296794050076511987)
  ·
    refine ⟨96092850445191075114767981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64061900296794050076511987 96092850445191075114767981)
    ·
      refine ⟨36034818916946653168037993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96092850445191075114767981 36034818916946653168037993)
      ·
        refine ⟨27026114187709989876028495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36034818916946653168037993 27026114187709989876028495)
        ·
          refine ⟨40539171281564984814042743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27026114187709989876028495 40539171281564984814042743)
          ·
            refine ⟨60808756922347477221064115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40539171281564984814042743 60808756922347477221064115)
            ·
              refine ⟨91213135383521215831596173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60808756922347477221064115 91213135383521215831596173)
              ·
                refine ⟨34204925768820455936848565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91213135383521215831596173 34204925768820455936848565)
                ·
                  refine ⟨3206711790826917744079553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34204925768820455936848565 3206711790826917744079553)
                  ·
                    refine ⟨2405033843120188308059665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3206711790826917744079553 2405033843120188308059665)
                    ·
                      refine ⟨1803775382340141231044749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2405033843120188308059665 1803775382340141231044749)
                      ·
                        rfl

theorem cell23_3512840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 3, 5, 2, 2].length) (baseStart_3512840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3512840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3512840 prefixEnd_3512840 := by exact prefixLift 3512840
  have htrace : WordTrace (prefixWord ++ tailWord_3512840) baseStart_3512840 baseEnd_3512840 := by
    simpa [prefixWord, tailWord_3512840, baseEnd_3512840] using wordTrace_append hprefix tailTrace_3512840
  have hstable : (prefixWord ++ tailWord_3512840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3512840).length < 2 ^ (prefixWord ++ tailWord_3512840).sum := by decide
  have hdescent : baseEnd_3512840 < baseStart_3512840 := by decide
  rcases family_descends (prefixWord ++ tailWord_3512840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3512853 : List Nat := [1, 3, 2, 1, 3, 1, 3, 2, 1, 2, 4]
def baseStart_3512853 : Nat := 118140960795 + 3512853 * 2 ^ 59
def prefixEnd_3512853 : Nat := 4983230072969 + 3 ^ 40 * 3512853 * 2
def baseEnd_3512853 : Nat := 1803782057588649680182189

theorem tailTrace_3512853 : CollatzResearch.WordTrace tailWord_3512853 prefixEnd_3512853 1803782057588649680182189 := by
  unfold tailWord_3512853
  simp only [CollatzResearch.WordTrace]
  refine ⟨128124274742541003373247213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85416183161694002248831475 128124274742541003373247213)
  ·
    refine ⟨48046603028452876264967705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128124274742541003373247213 48046603028452876264967705)
    ·
      refine ⟨36034952271339657198725779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48046603028452876264967705 36034952271339657198725779)
      ·
        refine ⟨54052428407009485798088669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36034952271339657198725779 54052428407009485798088669)
        ·
          refine ⟨20269660652628557174283251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54052428407009485798088669 20269660652628557174283251)
          ·
            refine ⟨30404490978942835761424877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20269660652628557174283251 30404490978942835761424877)
            ·
              refine ⟨11401684117103563410534329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30404490978942835761424877 11401684117103563410534329)
              ·
                refine ⟨8551263087827672557900747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11401684117103563410534329 8551263087827672557900747)
                ·
                  refine ⟨12826894631741508836851121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8551263087827672557900747 12826894631741508836851121)
                  ·
                    refine ⟨9620170973806131627638341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12826894631741508836851121 9620170973806131627638341)
                    ·
                      refine ⟨1803782057588649680182189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9620170973806131627638341 1803782057588649680182189)
                      ·
                        rfl

theorem cell23_3512853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 2, 1, 2, 4].length) (baseStart_3512853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3512853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3512853 prefixEnd_3512853 := by exact prefixLift 3512853
  have htrace : WordTrace (prefixWord ++ tailWord_3512853) baseStart_3512853 baseEnd_3512853 := by
    simpa [prefixWord, tailWord_3512853, baseEnd_3512853] using wordTrace_append hprefix tailTrace_3512853
  have hstable : (prefixWord ++ tailWord_3512853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3512853).length < 2 ^ (prefixWord ++ tailWord_3512853).sum := by decide
  have hdescent : baseEnd_3512853 < baseStart_3512853 := by decide
  rcases family_descends (prefixWord ++ tailWord_3512853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3512860 : List Nat := [2, 2, 3, 1, 2, 4, 1, 1, 1, 1, 5]
def baseStart_3512860 : Nat := 118140960795 + 3512860 * 2 ^ 59
def prefixEnd_3512860 : Nat := 4983230072969 + 3 ^ 40 * 3512860 * 2
def baseEnd_3512860 : Nat := 1803785651953231152794657

theorem tailTrace_3512860 : CollatzResearch.WordTrace tailWord_3512860 prefixEnd_3512860 1803785651953231152794657 := by
  unfold tailWord_3512860
  simp only [CollatzResearch.WordTrace]
  refine ⟨64062265026757821784376017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85416353369010429045834689 64062265026757821784376017)
  ·
    refine ⟨48046698770068366338282013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64062265026757821784376017 48046698770068366338282013)
    ·
      refine ⟨18017512038775637376855755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48046698770068366338282013 18017512038775637376855755)
      ·
        refine ⟨27026268058163456065283633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18017512038775637376855755 27026268058163456065283633)
        ·
          refine ⟨20269701043622592048962725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27026268058163456065283633 20269701043622592048962725)
          ·
            refine ⟨3800568945679236009180511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20269701043622592048962725 3800568945679236009180511)
            ·
              refine ⟨5700853418518854013770767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3800568945679236009180511 5700853418518854013770767)
              ·
                refine ⟨8551280127778281020656151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5700853418518854013770767 8551280127778281020656151)
                ·
                  refine ⟨12826920191667421530984227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8551280127778281020656151 12826920191667421530984227)
                  ·
                    refine ⟨19240380287501132296476341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12826920191667421530984227 19240380287501132296476341)
                    ·
                      refine ⟨1803785651953231152794657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19240380287501132296476341 1803785651953231152794657)
                      ·
                        rfl

theorem cell23_3512860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 1, 1, 1, 1, 5].length) (baseStart_3512860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3512860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3512860 prefixEnd_3512860 := by exact prefixLift 3512860
  have htrace : WordTrace (prefixWord ++ tailWord_3512860) baseStart_3512860 baseEnd_3512860 := by
    simpa [prefixWord, tailWord_3512860, baseEnd_3512860] using wordTrace_append hprefix tailTrace_3512860
  have hstable : (prefixWord ++ tailWord_3512860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3512860).length < 2 ^ (prefixWord ++ tailWord_3512860).sum := by decide
  have hdescent : baseEnd_3512860 < baseStart_3512860 := by decide
  rcases family_descends (prefixWord ++ tailWord_3512860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3512868 : List Nat := [2, 3, 1, 5, 1, 2, 2, 2, 1, 1, 3]
def baseStart_3512868 : Nat := 118140960795 + 3512868 * 2 ^ 59
def prefixEnd_3512868 : Nat := 4983230072969 + 3 ^ 40 * 3512868 * 2
def baseEnd_3512868 : Nat := 1803789759798467121494621

theorem tailTrace_3512868 : CollatzResearch.WordTrace tailWord_3512868 prefixEnd_3512868 1803789759798467121494621 := by
  unfold tailWord_3512868
  simp only [CollatzResearch.WordTrace]
  refine ⟨64062410918743330467521629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85416547891657773956695505 64062410918743330467521629)
  ·
    refine ⟨24023404094528748925320611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64062410918743330467521629 24023404094528748925320611)
    ·
      refine ⟨36035106141793123387980917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24023404094528748925320611 36035106141793123387980917)
      ·
        refine ⟨3378291200793105317623211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36035106141793123387980917 3378291200793105317623211)
        ·
          refine ⟨5067436801189657976434817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3378291200793105317623211 5067436801189657976434817)
          ·
            refine ⟨3800577600892243482326113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5067436801189657976434817 3800577600892243482326113)
            ·
              refine ⟨2850433200669182611744585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3800577600892243482326113 2850433200669182611744585)
              ·
                refine ⟨2137824900501886958808439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2850433200669182611744585 2137824900501886958808439)
                ·
                  refine ⟨3206737350752830438212659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2137824900501886958808439 3206737350752830438212659)
                  ·
                    refine ⟨4810106026129245657318989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3206737350752830438212659 4810106026129245657318989)
                    ·
                      refine ⟨1803789759798467121494621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4810106026129245657318989 1803789759798467121494621)
                      ·
                        rfl

theorem cell23_3512868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_3512868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3512868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3512868 prefixEnd_3512868 := by exact prefixLift 3512868
  have htrace : WordTrace (prefixWord ++ tailWord_3512868) baseStart_3512868 baseEnd_3512868 := by
    simpa [prefixWord, tailWord_3512868, baseEnd_3512868] using wordTrace_append hprefix tailTrace_3512868
  have hstable : (prefixWord ++ tailWord_3512868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3512868).length < 2 ^ (prefixWord ++ tailWord_3512868).sum := by decide
  have hdescent : baseEnd_3512868 < baseStart_3512868 := by decide
  rcases family_descends (prefixWord ++ tailWord_3512868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3512890 : List Nat := [3, 1, 1, 1, 3, 4, 2, 1, 1, 3, 3]
def baseStart_3512890 : Nat := 118140960795 + 3512890 * 2 ^ 59
def prefixEnd_3512890 : Nat := 4983230072969 + 3 ^ 40 * 3512890 * 2
def baseEnd_3512890 : Nat := 1803801056372866035419519

theorem tailTrace_3512890 : CollatzResearch.WordTrace tailWord_3512890 prefixEnd_3512890 1803801056372866035419519 := by
  unfold tailWord_3512890
  simp only [CollatzResearch.WordTrace]
  refine ⟨32031406060851739673086031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85417082828937972461562749 32031406060851739673086031)
  ·
    refine ⟨48047109091277609509629047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32031406060851739673086031 48047109091277609509629047)
    ·
      refine ⟨72070663636916414264443571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48047109091277609509629047 72070663636916414264443571)
      ·
        refine ⟨108105995455374621396665357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72070663636916414264443571 108105995455374621396665357)
        ·
          refine ⟨40539748295765483023749509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108105995455374621396665357 40539748295765483023749509)
          ·
            refine ⟨7601202805456028066953033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40539748295765483023749509 7601202805456028066953033)
            ·
              refine ⟨5700902104092021050214775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7601202805456028066953033 5700902104092021050214775)
              ·
                refine ⟨8551353156138031575322163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5700902104092021050214775 8551353156138031575322163)
                ·
                  refine ⟨12827029734207047362983245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8551353156138031575322163 12827029734207047362983245)
                  ·
                    refine ⟨4810136150327642761118717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12827029734207047362983245 4810136150327642761118717)
                    ·
                      refine ⟨1803801056372866035419519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4810136150327642761118717 1803801056372866035419519)
                      ·
                        rfl

theorem cell23_3512890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 2, 1, 1, 3, 3].length) (baseStart_3512890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3512890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3512890 prefixEnd_3512890 := by exact prefixLift 3512890
  have htrace : WordTrace (prefixWord ++ tailWord_3512890) baseStart_3512890 baseEnd_3512890 := by
    simpa [prefixWord, tailWord_3512890, baseEnd_3512890] using wordTrace_append hprefix tailTrace_3512890
  have hstable : (prefixWord ++ tailWord_3512890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3512890).length < 2 ^ (prefixWord ++ tailWord_3512890).sum := by decide
  have hdescent : baseEnd_3512890 < baseStart_3512890 := by decide
  rcases family_descends (prefixWord ++ tailWord_3512890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3512943 : List Nat := [1, 1, 2, 1, 3, 2, 4, 1, 2, 2, 4]
def baseStart_3512943 : Nat := 118140960795 + 3512943 * 2 ^ 59
def prefixEnd_3512943 : Nat := 4983230072969 + 3 ^ 40 * 3512943 * 2
def baseEnd_3512943 : Nat := 1803828270847554328056775

theorem tailTrace_3512943 : CollatzResearch.WordTrace tailWord_3512943 prefixEnd_3512943 1803828270847554328056775 := by
  unfold tailWord_3512943
  simp only [CollatzResearch.WordTrace]
  refine ⟨128127557312214948744023483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85418371541476632496015655 128127557312214948744023483)
  ·
    refine ⟨192191335968322423116035225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128127557312214948744023483 192191335968322423116035225)
    ·
      refine ⟨144143501976241817337026419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192191335968322423116035225 144143501976241817337026419)
      ·
        refine ⟨216215252964362726005539629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144143501976241817337026419 216215252964362726005539629)
        ·
          refine ⟨81080719861636022252077361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 216215252964362726005539629 81080719861636022252077361)
          ·
            refine ⟨60810539896227016689058021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81080719861636022252077361 60810539896227016689058021)
            ·
              refine ⟨11401976230542565629198379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60810539896227016689058021 11401976230542565629198379)
              ·
                refine ⟨17102964345813848443797569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11401976230542565629198379 17102964345813848443797569)
                ·
                  refine ⟨12827223259360386332848177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17102964345813848443797569 12827223259360386332848177)
                  ·
                    refine ⟨9620417444520289749636133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12827223259360386332848177 9620417444520289749636133)
                    ·
                      refine ⟨1803828270847554328056775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9620417444520289749636133 1803828270847554328056775)
                      ·
                        rfl

theorem cell23_3512943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 1, 2, 2, 4].length) (baseStart_3512943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3512943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3512943 prefixEnd_3512943 := by exact prefixLift 3512943
  have htrace : WordTrace (prefixWord ++ tailWord_3512943) baseStart_3512943 baseEnd_3512943 := by
    simpa [prefixWord, tailWord_3512943, baseEnd_3512943] using wordTrace_append hprefix tailTrace_3512943
  have hstable : (prefixWord ++ tailWord_3512943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3512943).length < 2 ^ (prefixWord ++ tailWord_3512943).sum := by decide
  have hdescent : baseEnd_3512943 < baseStart_3512943 := by decide
  rcases family_descends (prefixWord ++ tailWord_3512943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3512953 : List Nat := [1, 2, 1, 3, 3, 2, 2, 2, 7]
def baseStart_3512953 : Nat := 118140960795 + 3512953 * 2 ^ 59
def prefixEnd_3512953 : Nat := 4983230072969 + 3 ^ 40 * 3512953 * 2
def baseEnd_3512953 : Nat := 200425933961566587659081

theorem tailTrace_3512953 : CollatzResearch.WordTrace tailWord_3512953 prefixEnd_3512953 200425933961566587659081 := by
  unfold tailWord_3512953
  simp only [CollatzResearch.WordTrace]
  refine ⟨128127922042178720451887513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85418614694785813634591675 128127922042178720451887513)
  ·
    refine ⟨96095941531634040338915635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128127922042178720451887513 96095941531634040338915635)
    ·
      refine ⟨144143912297451060508373453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96095941531634040338915635 144143912297451060508373453)
      ·
        refine ⟨54053967111544147690640045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144143912297451060508373453 54053967111544147690640045)
        ·
          refine ⟨20270237666829055383990017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54053967111544147690640045 20270237666829055383990017)
          ·
            refine ⟨15202678250121791537992513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20270237666829055383990017 15202678250121791537992513)
            ·
              refine ⟨11402008687591343653494385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15202678250121791537992513 11402008687591343653494385)
              ·
                refine ⟨8551506515693507740120789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11402008687591343653494385 8551506515693507740120789)
                ·
                  refine ⟨200425933961566587659081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8551506515693507740120789 200425933961566587659081)
                  ·
                    rfl

theorem cell23_3512953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 2, 7].length) (baseStart_3512953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3512953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3512953 prefixEnd_3512953 := by exact prefixLift 3512953
  have htrace : WordTrace (prefixWord ++ tailWord_3512953) baseStart_3512953 baseEnd_3512953 := by
    simpa [prefixWord, tailWord_3512953, baseEnd_3512953] using wordTrace_append hprefix tailTrace_3512953
  have hstable : (prefixWord ++ tailWord_3512953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3512953).length < 2 ^ (prefixWord ++ tailWord_3512953).sum := by decide
  have hdescent : baseEnd_3512953 < baseStart_3512953 := by decide
  rcases family_descends (prefixWord ++ tailWord_3512953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3512963 : List Nat := [1, 1, 1, 3, 3, 1, 2, 2, 1, 5, 3]
def baseStart_3512963 : Nat := 118140960795 + 3512963 * 2 ^ 59
def prefixEnd_3512963 : Nat := 4983230072969 + 3 ^ 40 * 3512963 * 2
def baseEnd_3512963 : Nat := 1803838540460644249806683

theorem tailTrace_3512963 : CollatzResearch.WordTrace tailWord_3512963 prefixEnd_3512963 1803838540460644249806683 := by
  unfold tailWord_3512963
  simp only [CollatzResearch.WordTrace]
  refine ⟨128128286772142492159751543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85418857848094994773167695 128128286772142492159751543)
  ·
    refine ⟨192192430158213738239627315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128128286772142492159751543 192192430158213738239627315)
    ·
      refine ⟨288288645237320607359440973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192192430158213738239627315 288288645237320607359440973)
      ·
        refine ⟨108108241963995227759790365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 288288645237320607359440973 108108241963995227759790365)
        ·
          refine ⟨40540590736498210409921387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108108241963995227759790365 40540590736498210409921387)
          ·
            refine ⟨60810886104747315614882081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40540590736498210409921387 60810886104747315614882081)
            ·
              refine ⟨45608164578560486711161561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60810886104747315614882081 45608164578560486711161561)
              ·
                refine ⟨34206123433920365033371171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45608164578560486711161561 34206123433920365033371171)
                ·
                  refine ⟨51309185150880547550056757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34206123433920365033371171 51309185150880547550056757)
                  ·
                    refine ⟨4810236107895051332817821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51309185150880547550056757 4810236107895051332817821)
                    ·
                      refine ⟨1803838540460644249806683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4810236107895051332817821 1803838540460644249806683)
                      ·
                        rfl

theorem cell23_3512963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 2, 1, 5, 3].length) (baseStart_3512963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3512963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3512963 prefixEnd_3512963 := by exact prefixLift 3512963
  have htrace : WordTrace (prefixWord ++ tailWord_3512963) baseStart_3512963 baseEnd_3512963 := by
    simpa [prefixWord, tailWord_3512963, baseEnd_3512963] using wordTrace_append hprefix tailTrace_3512963
  have hstable : (prefixWord ++ tailWord_3512963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3512963).length < 2 ^ (prefixWord ++ tailWord_3512963).sum := by decide
  have hdescent : baseEnd_3512963 < baseStart_3512963 := by decide
  rcases family_descends (prefixWord ++ tailWord_3512963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3513060 : List Nat := [2, 3, 1, 1, 1, 4, 2, 3, 6]
def baseStart_3513060 : Nat := 118140960795 + 3513060 * 2 ^ 59
def prefixEnd_3513060 : Nat := 4983230072969 + 3 ^ 40 * 3513060 * 2
def baseEnd_3513060 : Nat := 200432038676014485588193

theorem tailTrace_3513060 : CollatzResearch.WordTrace tailWord_3513060 prefixEnd_3513060 200432038676014485588193 := by
  unfold tailWord_3513060
  simp only [CollatzResearch.WordTrace]
  refine ⟨64065912326395538863016317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85421216435194051817355089 64065912326395538863016317)
  ·
    refine ⟨24024717122398327073631119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64065912326395538863016317 24024717122398327073631119)
    ·
      refine ⟨36037075683597490610446679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24024717122398327073631119 36037075683597490610446679)
      ·
        refine ⟨54055613525396235915670019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36037075683597490610446679 54055613525396235915670019)
        ·
          refine ⟨81083420288094353873505029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54055613525396235915670019 81083420288094353873505029)
          ·
            refine ⟨15203141304017691351282193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81083420288094353873505029 15203141304017691351282193)
            ·
              refine ⟨11402355978013268513461645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15203141304017691351282193 11402355978013268513461645)
              ·
                refine ⟨4275883491754975692548117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11402355978013268513461645 4275883491754975692548117)
                ·
                  refine ⟨200432038676014485588193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4275883491754975692548117 200432038676014485588193)
                  ·
                    rfl

theorem cell23_3513060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 3, 6].length) (baseStart_3513060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3513060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3513060 prefixEnd_3513060 := by exact prefixLift 3513060
  have htrace : WordTrace (prefixWord ++ tailWord_3513060) baseStart_3513060 baseEnd_3513060 := by
    simpa [prefixWord, tailWord_3513060, baseEnd_3513060] using wordTrace_append hprefix tailTrace_3513060
  have hstable : (prefixWord ++ tailWord_3513060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3513060).length < 2 ^ (prefixWord ++ tailWord_3513060).sum := by decide
  have hdescent : baseEnd_3513060 < baseStart_3513060 := by decide
  rcases family_descends (prefixWord ++ tailWord_3513060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3513074 : List Nat := [3, 2, 1, 3, 1, 4, 1, 1, 2, 2, 3]
def baseStart_3513074 : Nat := 118140960795 + 3513074 * 2 ^ 59
def prefixEnd_3513074 : Nat := 4983230072969 + 3 ^ 40 * 3513074 * 2
def baseEnd_3513074 : Nat := 1803895536813293315518673

theorem tailTrace_3513074 : CollatzResearch.WordTrace tailWord_3513074 prefixEnd_3513074 1803895536813293315518673 := by
  unfold tailWord_3513074
  simp only [CollatzResearch.WordTrace]
  refine ⟨32033083818685089529260569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85421556849826905411361517 32033083818685089529260569)
  ·
    refine ⟨24024812864013817146945427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32033083818685089529260569 24024812864013817146945427)
    ·
      refine ⟨36037219296020725720418141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24024812864013817146945427 36037219296020725720418141)
      ·
        refine ⟨13513957236007772145156803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36037219296020725720418141 13513957236007772145156803)
        ·
          refine ⟨20270935854011658217735205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13513957236007772145156803 20270935854011658217735205)
          ·
            refine ⟨3800800472627185915825351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20270935854011658217735205 3800800472627185915825351)
            ·
              refine ⟨5701200708940778873738027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3800800472627185915825351 5701200708940778873738027)
              ·
                refine ⟨8551801063411168310607041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5701200708940778873738027 8551801063411168310607041)
                ·
                  refine ⟨6413850797558376232955281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8551801063411168310607041 6413850797558376232955281)
                  ·
                    refine ⟨4810388098168782174716461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6413850797558376232955281 4810388098168782174716461)
                    ·
                      refine ⟨1803895536813293315518673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4810388098168782174716461 1803895536813293315518673)
                      ·
                        rfl

theorem cell23_3513074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 1, 1, 2, 2, 3].length) (baseStart_3513074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3513074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3513074 prefixEnd_3513074 := by exact prefixLift 3513074
  have htrace : WordTrace (prefixWord ++ tailWord_3513074) baseStart_3513074 baseEnd_3513074 := by
    simpa [prefixWord, tailWord_3513074, baseEnd_3513074] using wordTrace_append hprefix tailTrace_3513074
  have hstable : (prefixWord ++ tailWord_3513074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3513074).length < 2 ^ (prefixWord ++ tailWord_3513074).sum := by decide
  have hdescent : baseEnd_3513074 < baseStart_3513074 := by decide
  rcases family_descends (prefixWord ++ tailWord_3513074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3513097 : List Nat := [1, 2, 1, 1, 3, 2, 2, 4, 2, 3, 2]
def baseStart_3513097 : Nat := 118140960795 + 3513097 * 2 ^ 59
def prefixEnd_3513097 : Nat := 4983230072969 + 3 ^ 40 * 3513097 * 2
def baseEnd_3513097 : Nat := 1803907346868346725531067

theorem tailTrace_3513097 : CollatzResearch.WordTrace tailWord_3513097 prefixEnd_3513097 1803907346868346725531067 := by
  unfold tailWord_3513097
  simp only [CollatzResearch.WordTrace]
  refine ⟨128133174153657033045129545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85422116102438022030086363 128133174153657033045129545)
  ·
    refine ⟨96099880615242774783847159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128133174153657033045129545 96099880615242774783847159)
    ·
      refine ⟨144149820922864162175770739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96099880615242774783847159 144149820922864162175770739)
      ·
        refine ⟨216224731384296243263656109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144149820922864162175770739 216224731384296243263656109)
        ·
          refine ⟨81084274269111091223871041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 216224731384296243263656109 81084274269111091223871041)
          ·
            refine ⟨60813205701833318417903281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81084274269111091223871041 60813205701833318417903281)
            ·
              refine ⟨45609904276374988813427461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60813205701833318417903281 45609904276374988813427461)
              ·
                refine ⟨8551857051820310402517649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45609904276374988813427461 8551857051820310402517649)
                ·
                  refine ⟨6413892788865232801888237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8551857051820310402517649 6413892788865232801888237)
                  ·
                    refine ⟨2405209795824462300708089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6413892788865232801888237 2405209795824462300708089)
                    ·
                      refine ⟨1803907346868346725531067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2405209795824462300708089 1803907346868346725531067)
                      ·
                        rfl

theorem cell23_3513097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 4, 2, 3, 2].length) (baseStart_3513097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3513097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3513097 prefixEnd_3513097 := by exact prefixLift 3513097
  have htrace : WordTrace (prefixWord ++ tailWord_3513097) baseStart_3513097 baseEnd_3513097 := by
    simpa [prefixWord, tailWord_3513097, baseEnd_3513097] using wordTrace_append hprefix tailTrace_3513097
  have hstable : (prefixWord ++ tailWord_3513097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3513097).length < 2 ^ (prefixWord ++ tailWord_3513097).sum := by decide
  have hdescent : baseEnd_3513097 < baseStart_3513097 := by decide
  rcases family_descends (prefixWord ++ tailWord_3513097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3513124 : List Nat := [2, 3, 1, 3, 3, 1, 2, 2, 1, 5]
def baseStart_3513124 : Nat := 118140960795 + 3513124 * 2 ^ 59
def prefixEnd_3513124 : Nat := 4983230072969 + 3 ^ 40 * 3513124 * 2
def baseEnd_3513124 : Nat := 601307070282006039964481

theorem tailTrace_3513124 : CollatzResearch.WordTrace tailWord_3513124 prefixEnd_3513124 601307070282006039964481 := by
  unfold tailWord_3513124
  simp only [CollatzResearch.WordTrace]
  refine ⟨64067079462279608328181213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85422772616372811104241617 64067079462279608328181213)
  ·
    refine ⟨24025154798354853123067955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64067079462279608328181213 24025154798354853123067955)
    ·
      refine ⟨36037732197532279684601933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24025154798354853123067955 36037732197532279684601933)
      ·
        refine ⟨13514149574074604881725725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36037732197532279684601933 13514149574074604881725725)
        ·
          refine ⟨5067806090277976830647147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13514149574074604881725725 5067806090277976830647147)
          ·
            refine ⟨7601709135416965245970721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5067806090277976830647147 7601709135416965245970721)
            ·
              refine ⟨5701281851562723934478041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7601709135416965245970721 5701281851562723934478041)
              ·
                refine ⟨4275961388672042950858531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5701281851562723934478041 4275961388672042950858531)
                ·
                  refine ⟨6413942083008064426287797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4275961388672042950858531 6413942083008064426287797)
                  ·
                    refine ⟨601307070282006039964481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6413942083008064426287797 601307070282006039964481)
                    ·
                      rfl

theorem cell23_3513124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 2, 2, 1, 5].length) (baseStart_3513124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3513124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3513124 prefixEnd_3513124 := by exact prefixLift 3513124
  have htrace : WordTrace (prefixWord ++ tailWord_3513124) baseStart_3513124 baseEnd_3513124 := by
    simpa [prefixWord, tailWord_3513124, baseEnd_3513124] using wordTrace_append hprefix tailTrace_3513124
  have hstable : (prefixWord ++ tailWord_3513124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3513124).length < 2 ^ (prefixWord ++ tailWord_3513124).sum := by decide
  have hdescent : baseEnd_3513124 < baseStart_3513124 := by decide
  rcases family_descends (prefixWord ++ tailWord_3513124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3513161 : List Nat := [1, 2, 1, 1, 2, 7, 1, 1, 3, 2, 2]
def baseStart_3513161 : Nat := 118140960795 + 3513161 * 2 ^ 59
def prefixEnd_3513161 : Nat := 4983230072969 + 3 ^ 40 * 3513161 * 2
def baseEnd_3513161 : Nat := 1803940209630234475130773

theorem tailTrace_3513161 : CollatzResearch.WordTrace tailWord_3513161 prefixEnd_3513161 1803940209630234475130773 := by
  unfold tailWord_3513161
  simp only [CollatzResearch.WordTrace]
  refine ⟨128135508425425171975459337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85423672283616781316972891 128135508425425171975459337)
  ·
    refine ⟨96101631319068878981594503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128135508425425171975459337 96101631319068878981594503)
    ·
      refine ⟨144152446978603318472391755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96101631319068878981594503 144152446978603318472391755)
      ·
        refine ⟨216228670467904977708587633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144152446978603318472391755 216228670467904977708587633)
        ·
          refine ⟨162171502850928733281440725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216228670467904977708587633 162171502850928733281440725)
          ·
            refine ⟨3800894598068642186283767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 162171502850928733281440725 3800894598068642186283767)
            ·
              refine ⟨5701341897102963279425651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3800894598068642186283767 5701341897102963279425651)
              ·
                refine ⟨8552012845654444919138477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5701341897102963279425651 8552012845654444919138477)
                ·
                  refine ⟨3207004817120416844676929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8552012845654444919138477 3207004817120416844676929)
                  ·
                    refine ⟨2405253612840312633507697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3207004817120416844676929 2405253612840312633507697)
                    ·
                      refine ⟨1803940209630234475130773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2405253612840312633507697 1803940209630234475130773)
                      ·
                        rfl

theorem cell23_3513161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 1, 1, 3, 2, 2].length) (baseStart_3513161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3513161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3513161 prefixEnd_3513161 := by exact prefixLift 3513161
  have htrace : WordTrace (prefixWord ++ tailWord_3513161) baseStart_3513161 baseEnd_3513161 := by
    simpa [prefixWord, tailWord_3513161, baseEnd_3513161] using wordTrace_append hprefix tailTrace_3513161
  have hstable : (prefixWord ++ tailWord_3513161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3513161).length < 2 ^ (prefixWord ++ tailWord_3513161).sum := by decide
  have hdescent : baseEnd_3513161 < baseStart_3513161 := by decide
  rcases family_descends (prefixWord ++ tailWord_3513161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3513170 : List Nat := [3, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6]
def baseStart_3513170 : Nat := 118140960795 + 3513170 * 2 ^ 59
def prefixEnd_3513170 : Nat := 4983230072969 + 3 ^ 40 * 3513170 * 2
def baseEnd_3513170 : Nat := 1803944830956124939918231

theorem tailTrace_3513170 : CollatzResearch.WordTrace tailWord_3513170 prefixEnd_3513170 1803944830956124939918231 := by
  unfold tailWord_3513170
  simp only [CollatzResearch.WordTrace]
  refine ⟨32033959170598141628134241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85423891121595044341691309 32033959170598141628134241)
  ·
    refine ⟨24025469377948606221100681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32033959170598141628134241 24025469377948606221100681)
    ·
      refine ⟨18019102033461454665825511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24025469377948606221100681 18019102033461454665825511)
      ·
        refine ⟨27028653050192181998738267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18019102033461454665825511 27028653050192181998738267)
        ·
          refine ⟨40542979575288272998107401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27028653050192181998738267 40542979575288272998107401)
          ·
            refine ⟨30407234681466204748580551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40542979575288272998107401 30407234681466204748580551)
            ·
              refine ⟨45610852022199307122870827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30407234681466204748580551 45610852022199307122870827)
              ·
                refine ⟨68416278033298960684306241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45610852022199307122870827 68416278033298960684306241)
                ·
                  refine ⟨51312208524974220513229681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68416278033298960684306241 51312208524974220513229681)
                  ·
                    refine ⟨38484156393730665384922261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51312208524974220513229681 38484156393730665384922261)
                    ·
                      refine ⟨1803944830956124939918231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38484156393730665384922261 1803944830956124939918231)
                      ·
                        rfl

theorem cell23_3513170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6].length) (baseStart_3513170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3513170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3513170 prefixEnd_3513170 := by exact prefixLift 3513170
  have htrace : WordTrace (prefixWord ++ tailWord_3513170) baseStart_3513170 baseEnd_3513170 := by
    simpa [prefixWord, tailWord_3513170, baseEnd_3513170] using wordTrace_append hprefix tailTrace_3513170
  have hstable : (prefixWord ++ tailWord_3513170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3513170).length < 2 ^ (prefixWord ++ tailWord_3513170).sum := by decide
  have hdescent : baseEnd_3513170 < baseStart_3513170 := by decide
  rcases family_descends (prefixWord ++ tailWord_3513170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3513198 : List Nat := [4, 1, 2, 3, 2, 1, 3, 1, 1, 2, 3]
def baseStart_3513198 : Nat := 118140960795 + 3513198 * 2 ^ 59
def prefixEnd_3513198 : Nat := 4983230072969 + 3 ^ 40 * 3513198 * 2
def baseEnd_3513198 : Nat := 1803959208414450830368103

theorem tailTrace_3513198 : CollatzResearch.WordTrace tailWord_3513198 prefixEnd_3513198 1803959208414450830368103 := by
  unfold tailWord_3513198
  simp only [CollatzResearch.WordTrace]
  refine ⟨16017107240786390911819531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85424571950860751529704165 16017107240786390911819531)
  ·
    refine ⟨24025660861179586367729297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16017107240786390911819531 24025660861179586367729297)
    ·
      refine ⟨18019245645884689775796973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24025660861179586367729297 18019245645884689775796973)
      ·
        refine ⟨6757217117206758665923865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18019245645884689775796973 6757217117206758665923865)
        ·
          refine ⟨5067912837905068999442899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6757217117206758665923865 5067912837905068999442899)
          ·
            refine ⟨7601869256857603499164349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5067912837905068999442899 7601869256857603499164349)
            ·
              refine ⟨2850700971321601312186631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7601869256857603499164349 2850700971321601312186631)
              ·
                refine ⟨4276051456982401968279947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2850700971321601312186631 4276051456982401968279947)
                ·
                  refine ⟨6414077185473602952419921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4276051456982401968279947 6414077185473602952419921)
                  ·
                    refine ⟨4810557889105202214314941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6414077185473602952419921 4810557889105202214314941)
                    ·
                      refine ⟨1803959208414450830368103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4810557889105202214314941 1803959208414450830368103)
                      ·
                        rfl

theorem cell23_3513198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 3, 1, 1, 2, 3].length) (baseStart_3513198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3513198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3513198 prefixEnd_3513198 := by exact prefixLift 3513198
  have htrace : WordTrace (prefixWord ++ tailWord_3513198) baseStart_3513198 baseEnd_3513198 := by
    simpa [prefixWord, tailWord_3513198, baseEnd_3513198] using wordTrace_append hprefix tailTrace_3513198
  have hstable : (prefixWord ++ tailWord_3513198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3513198).length < 2 ^ (prefixWord ++ tailWord_3513198).sum := by decide
  have hdescent : baseEnd_3513198 < baseStart_3513198 := by decide
  rcases family_descends (prefixWord ++ tailWord_3513198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3513210 : List Nat := [3, 1, 1, 1, 1, 1, 3, 4, 2, 6]
def baseStart_3513210 : Nat := 118140960795 + 3513210 * 2 ^ 59
def prefixEnd_3513210 : Nat := 4983230072969 + 3 ^ 40 * 3513210 * 2
def baseEnd_3513210 : Nat := 601321790060768261139349

theorem tailTrace_3513210 : CollatzResearch.WordTrace tailWord_3513210 prefixEnd_3513210 601321790060768261139349 := by
  unfold tailWord_3513210
  simp only [CollatzResearch.WordTrace]
  refine ⟨32034323900561913335998271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85424863734831768895995389 32034323900561913335998271)
  ·
    refine ⟨48051485850842870003997407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32034323900561913335998271 48051485850842870003997407)
    ·
      refine ⟨72077228776264305005996111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48051485850842870003997407 72077228776264305005996111)
      ·
        refine ⟨108115843164396457508994167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72077228776264305005996111 108115843164396457508994167)
        ·
          refine ⟨162173764746594686263491251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108115843164396457508994167 162173764746594686263491251)
          ·
            refine ⟨243260647119892029395236877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162173764746594686263491251 243260647119892029395236877)
            ·
              refine ⟨91222742669959511023213829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 243260647119892029395236877 91222742669959511023213829)
              ·
                refine ⟨17104264250617408316852593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91222742669959511023213829 17104264250617408316852593)
                ·
                  refine ⟨12828198187963056237639445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17104264250617408316852593 12828198187963056237639445)
                  ·
                    refine ⟨601321790060768261139349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12828198187963056237639445 601321790060768261139349)
                    ·
                      rfl

theorem cell23_3513210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 4, 2, 6].length) (baseStart_3513210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3513210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3513210 prefixEnd_3513210 := by exact prefixLift 3513210
  have htrace : WordTrace (prefixWord ++ tailWord_3513210) baseStart_3513210 baseEnd_3513210 := by
    simpa [prefixWord, tailWord_3513210, baseEnd_3513210] using wordTrace_append hprefix tailTrace_3513210
  have hstable : (prefixWord ++ tailWord_3513210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3513210).length < 2 ^ (prefixWord ++ tailWord_3513210).sum := by decide
  have hdescent : baseEnd_3513210 < baseStart_3513210 := by decide
  rcases family_descends (prefixWord ++ tailWord_3513210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3513218 : List Nat := [3, 4, 2, 2, 2, 1, 1, 8]
def baseStart_3513218 : Nat := 118140960795 + 3513218 * 2 ^ 59
def prefixEnd_3513218 : Nat := 4983230072969 + 3 ^ 40 * 3513218 * 2
def baseEnd_3513218 : Nat := 66813684371390398226593

theorem tailTrace_3513218 : CollatzResearch.WordTrace tailWord_3513218 prefixEnd_3513218 66813684371390398226593 := by
  unfold tailWord_3513218
  simp only [CollatzResearch.WordTrace]
  refine ⟨32034396846554667677571077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85425058257479113806856205 32034396846554667677571077)
  ·
    refine ⟨6006449408729000189544577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32034396846554667677571077 6006449408729000189544577)
    ·
      refine ⟨4504837056546750142158433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6006449408729000189544577 4504837056546750142158433)
      ·
        refine ⟨3378627792410062606618825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4504837056546750142158433 3378627792410062606618825)
        ·
          refine ⟨2533970844307546954964119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3378627792410062606618825 2533970844307546954964119)
          ·
            refine ⟨3800956266461320432446179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2533970844307546954964119 3800956266461320432446179)
            ·
              refine ⟨5701434399691980648669269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3800956266461320432446179 5701434399691980648669269)
              ·
                refine ⟨66813684371390398226593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5701434399691980648669269 66813684371390398226593)
                ·
                  rfl

theorem cell23_3513218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 1, 8].length) (baseStart_3513218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3513218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3513218 prefixEnd_3513218 := by exact prefixLift 3513218
  have htrace : WordTrace (prefixWord ++ tailWord_3513218) baseStart_3513218 baseEnd_3513218 := by
    simpa [prefixWord, tailWord_3513218, baseEnd_3513218] using wordTrace_append hprefix tailTrace_3513218
  have hstable : (prefixWord ++ tailWord_3513218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3513218).length < 2 ^ (prefixWord ++ tailWord_3513218).sum := by decide
  have hdescent : baseEnd_3513218 < baseStart_3513218 := by decide
  rcases family_descends (prefixWord ++ tailWord_3513218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3513255 : List Nat := [1, 1, 6, 1, 3, 2, 2, 1, 1, 3, 2]
def baseStart_3513255 : Nat := 118140960795 + 3513255 * 2 ^ 59
def prefixEnd_3513255 : Nat := 4983230072969 + 3 ^ 40 * 3513255 * 2
def baseEnd_3513255 : Nat := 1803988476811757107355341

theorem tailTrace_3513255 : CollatzResearch.WordTrace tailWord_3513255 prefixEnd_3513255 1803988476811757107355341 := by
  unfold tailWord_3513255
  simp only [CollatzResearch.WordTrace]
  refine ⟨128138936887084626029381219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85425957924723084019587479 128138936887084626029381219)
  ·
    refine ⟨192208405330626939044071829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128138936887084626029381219 192208405330626939044071829)
    ·
      refine ⟨9009768999873137767690867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 192208405330626939044071829 9009768999873137767690867)
      ·
        refine ⟨13514653499809706651536301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9009768999873137767690867 13514653499809706651536301)
        ·
          refine ⟨5067995062428639994326113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13514653499809706651536301 5067995062428639994326113)
          ·
            refine ⟨3800996296821479995744585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5067995062428639994326113 3800996296821479995744585)
            ·
              refine ⟨2850747222616109996808439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3800996296821479995744585 2850747222616109996808439)
              ·
                refine ⟨4276120833924164995212659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2850747222616109996808439 4276120833924164995212659)
                ·
                  refine ⟨6414181250886247492818989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4276120833924164995212659 6414181250886247492818989)
                  ·
                    refine ⟨2405317969082342809807121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6414181250886247492818989 2405317969082342809807121)
                    ·
                      refine ⟨1803988476811757107355341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2405317969082342809807121 1803988476811757107355341)
                      ·
                        rfl

theorem cell23_3513255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 2, 1, 1, 3, 2].length) (baseStart_3513255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3513255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3513255 prefixEnd_3513255 := by exact prefixLift 3513255
  have htrace : WordTrace (prefixWord ++ tailWord_3513255) baseStart_3513255 baseEnd_3513255 := by
    simpa [prefixWord, tailWord_3513255, baseEnd_3513255] using wordTrace_append hprefix tailTrace_3513255
  have hstable : (prefixWord ++ tailWord_3513255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3513255).length < 2 ^ (prefixWord ++ tailWord_3513255).sum := by decide
  have hdescent : baseEnd_3513255 < baseStart_3513255 := by decide
  rcases family_descends (prefixWord ++ tailWord_3513255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3513417 : List Nat := [1, 2, 1, 1, 2, 2, 2, 1, 5, 1, 5]
def baseStart_3513417 : Nat := 118140960795 + 3513417 * 2 ^ 59
def prefixEnd_3513417 : Nat := 4983230072969 + 3 ^ 40 * 3513417 * 2
def baseEnd_3513417 : Nat := 1804071660677785473529595

theorem tailTrace_3513417 : CollatzResearch.WordTrace tailWord_3513417 prefixEnd_3513417 1804071660677785473529595 := by
  unfold tailWord_3513417
  simp only [CollatzResearch.WordTrace]
  refine ⟨128144845512497727696778505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85429897008331818464519003 128144845512497727696778505)
  ·
    refine ⟨96108634134373295772583879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128144845512497727696778505 96108634134373295772583879)
    ·
      refine ⟨144162951201559943658875819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96108634134373295772583879 144162951201559943658875819)
      ·
        refine ⟨216244426802339915488313729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144162951201559943658875819 216244426802339915488313729)
        ·
          refine ⟨162183320101754936616235297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216244426802339915488313729 162183320101754936616235297)
          ·
            refine ⟨121637490076316202462176473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162183320101754936616235297 121637490076316202462176473)
            ·
              refine ⟨91228117557237151846632355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121637490076316202462176473 91228117557237151846632355)
              ·
                refine ⟨136842176335855727769948533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91228117557237151846632355 136842176335855727769948533)
                ·
                  refine ⟨12828954031486474478432675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 136842176335855727769948533 12828954031486474478432675)
                  ·
                    refine ⟨19243431047229711717649013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12828954031486474478432675 19243431047229711717649013)
                    ·
                      refine ⟨1804071660677785473529595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19243431047229711717649013 1804071660677785473529595)
                      ·
                        rfl

theorem cell23_3513417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 5, 1, 5].length) (baseStart_3513417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3513417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3513417 prefixEnd_3513417 := by exact prefixLift 3513417
  have htrace : WordTrace (prefixWord ++ tailWord_3513417) baseStart_3513417 baseEnd_3513417 := by
    simpa [prefixWord, tailWord_3513417, baseEnd_3513417] using wordTrace_append hprefix tailTrace_3513417
  have hstable : (prefixWord ++ tailWord_3513417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3513417).length < 2 ^ (prefixWord ++ tailWord_3513417).sum := by decide
  have hdescent : baseEnd_3513417 < baseStart_3513417 := by decide
  rcases family_descends (prefixWord ++ tailWord_3513417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3513431 : List Nat := [1, 1, 3, 2, 2, 1, 1, 1, 7, 2, 2]
def baseStart_3513431 : Nat := 118140960795 + 3513431 * 2 ^ 59
def prefixEnd_3513431 : Nat := 4983230072969 + 3 ^ 40 * 3513431 * 2
def baseEnd_3513431 : Nat := 1804078849406948418754531

theorem tailTrace_3513431 : CollatzResearch.WordTrace tailWord_3513431 prefixEnd_3513431 1804078849406948418754531 := by
  unfold tailWord_3513431
  simp only [CollatzResearch.WordTrace]
  refine ⟨128145356134447008087788147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85430237422964672058525431 128145356134447008087788147)
  ·
    refine ⟨192218034201670512131682221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128145356134447008087788147 192218034201670512131682221)
    ·
      refine ⟨72081762825626442049380833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192218034201670512131682221 72081762825626442049380833)
      ·
        refine ⟨54061322119219831537035625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72081762825626442049380833 54061322119219831537035625)
        ·
          refine ⟨40545991589414873652776719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54061322119219831537035625 40545991589414873652776719)
          ·
            refine ⟨60818987384122310479165079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40545991589414873652776719 60818987384122310479165079)
            ·
              refine ⟨91228481076183465718747619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60818987384122310479165079 91228481076183465718747619)
              ·
                refine ⟨136842721614275198578121429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91228481076183465718747619 136842721614275198578121429)
                ·
                  refine ⟨3207251287834574966674721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 136842721614275198578121429 3207251287834574966674721)
                  ·
                    refine ⟨2405438465875931225006041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3207251287834574966674721 2405438465875931225006041)
                    ·
                      refine ⟨1804078849406948418754531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2405438465875931225006041 1804078849406948418754531)
                      ·
                        rfl

theorem cell23_3513431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 7, 2, 2].length) (baseStart_3513431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3513431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3513431 prefixEnd_3513431 := by exact prefixLift 3513431
  have htrace : WordTrace (prefixWord ++ tailWord_3513431) baseStart_3513431 baseEnd_3513431 := by
    simpa [prefixWord, tailWord_3513431, baseEnd_3513431] using wordTrace_append hprefix tailTrace_3513431
  have hstable : (prefixWord ++ tailWord_3513431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3513431).length < 2 ^ (prefixWord ++ tailWord_3513431).sum := by decide
  have hdescent : baseEnd_3513431 < baseStart_3513431 := by decide
  rcases family_descends (prefixWord ++ tailWord_3513431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3513434 : List Nat := [3, 1, 1, 2, 1, 1, 2, 2, 5, 2, 3]
def baseStart_3513434 : Nat := 118140960795 + 3513434 * 2 ^ 59
def prefixEnd_3513434 : Nat := 4983230072969 + 3 ^ 40 * 3513434 * 2
def baseEnd_3513434 : Nat := 1804080389848911907017017

theorem tailTrace_3513434 : CollatzResearch.WordTrace tailWord_3513434 prefixEnd_3513434 1804080389848911907017017 := by
  unfold tailWord_3513434
  simp only [CollatzResearch.WordTrace]
  refine ⟨32036366388359034900036839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85430310368957426400098237 32036366388359034900036839)
  ·
    refine ⟨48054549582538552350055259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32036366388359034900036839 48054549582538552350055259)
    ·
      refine ⟨72081824373807828525082889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48054549582538552350055259 72081824373807828525082889)
      ·
        refine ⟨54061368280355871393812167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72081824373807828525082889 54061368280355871393812167)
        ·
          refine ⟨81092052420533807090718251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54061368280355871393812167 81092052420533807090718251)
          ·
            refine ⟨121638078630800710636077377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81092052420533807090718251 121638078630800710636077377)
            ·
              refine ⟨91228558973100532977058033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121638078630800710636077377 91228558973100532977058033)
              ·
                refine ⟨68421419229825399732793525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91228558973100532977058033 68421419229825399732793525)
                ·
                  refine ⟨6414508052796131224949393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68421419229825399732793525 6414508052796131224949393)
                  ·
                    refine ⟨4810881039597098418712045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6414508052796131224949393 4810881039597098418712045)
                    ·
                      refine ⟨1804080389848911907017017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4810881039597098418712045 1804080389848911907017017)
                      ·
                        rfl

theorem cell23_3513434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 5, 2, 3].length) (baseStart_3513434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3513434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3513434 prefixEnd_3513434 := by exact prefixLift 3513434
  have htrace : WordTrace (prefixWord ++ tailWord_3513434) baseStart_3513434 baseEnd_3513434 := by
    simpa [prefixWord, tailWord_3513434, baseEnd_3513434] using wordTrace_append hprefix tailTrace_3513434
  have hstable : (prefixWord ++ tailWord_3513434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3513434).length < 2 ^ (prefixWord ++ tailWord_3513434).sum := by decide
  have hdescent : baseEnd_3513434 < baseStart_3513434 := by decide
  rcases family_descends (prefixWord ++ tailWord_3513434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3513441 : List Nat := [1, 2, 3, 1, 1, 2, 5, 2, 2, 4]
def baseStart_3513441 : Nat := 118140960795 + 3513441 * 2 ^ 59
def prefixEnd_3513441 : Nat := 4983230072969 + 3 ^ 40 * 3513441 * 2
def baseEnd_3513441 : Nat := 601361328071164459876495

theorem tailTrace_3513441 : CollatzResearch.WordTrace tailWord_3513441 prefixEnd_3513441 601361328071164459876495 := by
  unfold tailWord_3513441
  simp only [CollatzResearch.WordTrace]
  refine ⟨128145720864410779795652177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85430480576273853197101451 128145720864410779795652177)
  ·
    refine ⟨96109290648308084846739133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128145720864410779795652177 96109290648308084846739133)
    ·
      refine ⟨36040983993115531817527175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96109290648308084846739133 36040983993115531817527175)
      ·
        refine ⟨54061475989673297726290763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36040983993115531817527175 54061475989673297726290763)
        ·
          refine ⟨81092213984509946589436145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54061475989673297726290763 81092213984509946589436145)
          ·
            refine ⟨60819160488382459942077109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81092213984509946589436145 60819160488382459942077109)
            ·
              refine ⟨5701796295785855619569729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60819160488382459942077109 5701796295785855619569729)
              ·
                refine ⟨4276347221839391714677297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5701796295785855619569729 4276347221839391714677297)
                ·
                  refine ⟨3207260416379543786007973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4276347221839391714677297 3207260416379543786007973)
                  ·
                    refine ⟨601361328071164459876495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3207260416379543786007973 601361328071164459876495)
                    ·
                      rfl

theorem cell23_3513441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 5, 2, 2, 4].length) (baseStart_3513441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3513441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3513441 prefixEnd_3513441 := by exact prefixLift 3513441
  have htrace : WordTrace (prefixWord ++ tailWord_3513441) baseStart_3513441 baseEnd_3513441 := by
    simpa [prefixWord, tailWord_3513441, baseEnd_3513441] using wordTrace_append hprefix tailTrace_3513441
  have hstable : (prefixWord ++ tailWord_3513441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3513441).length < 2 ^ (prefixWord ++ tailWord_3513441).sum := by decide
  have hdescent : baseEnd_3513441 < baseStart_3513441 := by decide
  rcases family_descends (prefixWord ++ tailWord_3513441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3513457 : List Nat := [1, 2, 2, 2, 1, 1, 2, 1, 1, 4, 6]
def baseStart_3513457 : Nat := 118140960795 + 3513457 * 2 ^ 59
def prefixEnd_3513457 : Nat := 4983230072969 + 3 ^ 40 * 3513457 * 2
def baseEnd_3513457 : Nat := 1804092199903965317029411

theorem tailTrace_3513457 : CollatzResearch.WordTrace tailWord_3513457 prefixEnd_3513457 1804092199903965317029411 := by
  unfold tailWord_3513457
  simp only [CollatzResearch.WordTrace]
  refine ⟨128146304432352814528234625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85430869621568543018823083 128146304432352814528234625)
  ·
    refine ⟨96109728324264610896175969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128146304432352814528234625 96109728324264610896175969)
    ·
      refine ⟨72082296243198458172131977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96109728324264610896175969 72082296243198458172131977)
      ·
        refine ⟨54061722182398843629098983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72082296243198458172131977 54061722182398843629098983)
        ·
          refine ⟨81092583273598265443648475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54061722182398843629098983 81092583273598265443648475)
          ·
            refine ⟨121638874910397398165472713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81092583273598265443648475 121638874910397398165472713)
            ·
              refine ⟨91229156182798048624104535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121638874910397398165472713 91229156182798048624104535)
              ·
                refine ⟨136843734274197072936156803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91229156182798048624104535 136843734274197072936156803)
                ·
                  refine ⟨205265601411295609404235205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 136843734274197072936156803 205265601411295609404235205)
                  ·
                    refine ⟨38487300264617926763294101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 205265601411295609404235205 38487300264617926763294101)
                    ·
                      refine ⟨1804092199903965317029411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38487300264617926763294101 1804092199903965317029411)
                      ·
                        rfl

theorem cell23_3513457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 4, 6].length) (baseStart_3513457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3513457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3513457 prefixEnd_3513457 := by exact prefixLift 3513457
  have htrace : WordTrace (prefixWord ++ tailWord_3513457) baseStart_3513457 baseEnd_3513457 := by
    simpa [prefixWord, tailWord_3513457, baseEnd_3513457] using wordTrace_append hprefix tailTrace_3513457
  have hstable : (prefixWord ++ tailWord_3513457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3513457).length < 2 ^ (prefixWord ++ tailWord_3513457).sum := by decide
  have hdescent : baseEnd_3513457 < baseStart_3513457 := by decide
  rcases family_descends (prefixWord ++ tailWord_3513457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3513458 : List Nat := [3, 2, 1, 2, 2, 1, 5, 1, 2, 4]
def baseStart_3513458 : Nat := 118140960795 + 3513458 * 2 ^ 59
def prefixEnd_3513458 : Nat := 4983230072969 + 3 ^ 40 * 3513458 * 2
def baseEnd_3513458 : Nat := 601364237794873271038969

theorem tailTrace_3513458 : CollatzResearch.WordTrace tailWord_3513458 prefixEnd_3513458 601364237794873271038969 := by
  unfold tailWord_3513458
  simp only [CollatzResearch.WordTrace]
  refine ⟨32036585226337297924755257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85430893936899461132680685 32036585226337297924755257)
  ·
    refine ⟨24027438919752973443566443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32036585226337297924755257 24027438919752973443566443)
    ·
      refine ⟨36041158379629460165349665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24027438919752973443566443 36041158379629460165349665)
      ·
        refine ⟨27030868784722095124012249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36041158379629460165349665 27030868784722095124012249)
        ·
          refine ⟨20273151588541571343009187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27030868784722095124012249 20273151588541571343009187)
          ·
            refine ⟨30409727382812357014513781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20273151588541571343009187 30409727382812357014513781)
            ·
              refine ⟨2850911942138658470110667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30409727382812357014513781 2850911942138658470110667)
              ·
                refine ⟨4276367913207987705166001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2850911942138658470110667 4276367913207987705166001)
                ·
                  refine ⟨3207275934905990778874501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4276367913207987705166001 3207275934905990778874501)
                  ·
                    refine ⟨601364237794873271038969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3207275934905990778874501 601364237794873271038969)
                    ·
                      rfl

theorem cell23_3513458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 5, 1, 2, 4].length) (baseStart_3513458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3513458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3513458 prefixEnd_3513458 := by exact prefixLift 3513458
  have htrace : WordTrace (prefixWord ++ tailWord_3513458) baseStart_3513458 baseEnd_3513458 := by
    simpa [prefixWord, tailWord_3513458, baseEnd_3513458] using wordTrace_append hprefix tailTrace_3513458
  have hstable : (prefixWord ++ tailWord_3513458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3513458).length < 2 ^ (prefixWord ++ tailWord_3513458).sum := by decide
  have hdescent : baseEnd_3513458 < baseStart_3513458 := by decide
  rcases family_descends (prefixWord ++ tailWord_3513458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3513467 : List Nat := [1, 1, 1, 1, 1, 4, 1, 4, 2, 7]
def baseStart_3513467 : Nat := 118140960795 + 3513467 * 2 ^ 59
def prefixEnd_3513467 : Nat := 4983230072969 + 3 ^ 40 * 3513467 * 2
def baseEnd_3513467 : Nat := 601365778236836759301455

theorem tailTrace_3513467 : CollatzResearch.WordTrace tailWord_3513467 prefixEnd_3513467 601365778236836759301455 := by
  unfold tailWord_3513467
  simp only [CollatzResearch.WordTrace]
  refine ⟨128146669162316586236098655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85431112774877724157399103 128146669162316586236098655)
  ·
    refine ⟨192220003743474879354147983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128146669162316586236098655 192220003743474879354147983)
    ·
      refine ⟨288330005615212319031221975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192220003743474879354147983 288330005615212319031221975)
      ·
        refine ⟨432495008422818478546832963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288330005615212319031221975 432495008422818478546832963)
        ·
          refine ⟨648742512634227717820249445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 432495008422818478546832963 648742512634227717820249445)
          ·
            refine ⟨121639221118917697091296771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 648742512634227717820249445 121639221118917697091296771)
            ·
              refine ⟨182458831678376545636945157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121639221118917697091296771 182458831678376545636945157)
              ·
                refine ⟨34211030939695602306927217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 182458831678376545636945157 34211030939695602306927217)
                ·
                  refine ⟨25658273204771701730195413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34211030939695602306927217 25658273204771701730195413)
                  ·
                    refine ⟨601365778236836759301455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25658273204771701730195413 601365778236836759301455)
                    ·
                      rfl

theorem cell23_3513467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 4, 2, 7].length) (baseStart_3513467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3513467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3513467 prefixEnd_3513467 := by exact prefixLift 3513467
  have htrace : WordTrace (prefixWord ++ tailWord_3513467) baseStart_3513467 baseEnd_3513467 := by
    simpa [prefixWord, tailWord_3513467, baseEnd_3513467] using wordTrace_append hprefix tailTrace_3513467
  have hstable : (prefixWord ++ tailWord_3513467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3513467).length < 2 ^ (prefixWord ++ tailWord_3513467).sum := by decide
  have hdescent : baseEnd_3513467 < baseStart_3513467 := by decide
  rcases family_descends (prefixWord ++ tailWord_3513467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3513481 : List Nat := [1, 2, 1, 1, 4, 3, 1, 2, 4, 1, 3]
def baseStart_3513481 : Nat := 118140960795 + 3513481 * 2 ^ 59
def prefixEnd_3513481 : Nat := 4983230072969 + 3 ^ 40 * 3513481 * 2
def baseEnd_3513481 : Nat := 1804104523439673223129301

theorem tailTrace_3513481 : CollatzResearch.WordTrace tailWord_3513481 prefixEnd_3513481 1804104523439673223129301 := by
  unfold tailWord_3513481
  simp only [CollatzResearch.WordTrace]
  refine ⟨128147179784265866627108297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85431453189510577751405531 128147179784265866627108297)
  ·
    refine ⟨96110384838199399970331223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128147179784265866627108297 96110384838199399970331223)
    ·
      refine ⟨144165577257299099955496835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96110384838199399970331223 144165577257299099955496835)
      ·
        refine ⟨216248365885948649933245253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144165577257299099955496835 216248365885948649933245253)
        ·
          refine ⟨40546568603615371862483485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 216248365885948649933245253 40546568603615371862483485)
          ·
            refine ⟨15204963226355764448431307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40546568603615371862483485 15204963226355764448431307)
            ·
              refine ⟨22807444839533646672646961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15204963226355764448431307 22807444839533646672646961)
              ·
                refine ⟨17105583629650235004485221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22807444839533646672646961 17105583629650235004485221)
                ·
                  refine ⟨3207296930559419063340979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17105583629650235004485221 3207296930559419063340979)
                  ·
                    refine ⟨4810945395839128595011469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3207296930559419063340979 4810945395839128595011469)
                    ·
                      refine ⟨1804104523439673223129301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4810945395839128595011469 1804104523439673223129301)
                      ·
                        rfl

theorem cell23_3513481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 2, 4, 1, 3].length) (baseStart_3513481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3513481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3513481 prefixEnd_3513481 := by exact prefixLift 3513481
  have htrace : WordTrace (prefixWord ++ tailWord_3513481) baseStart_3513481 baseEnd_3513481 := by
    simpa [prefixWord, tailWord_3513481, baseEnd_3513481] using wordTrace_append hprefix tailTrace_3513481
  have hstable : (prefixWord ++ tailWord_3513481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3513481).length < 2 ^ (prefixWord ++ tailWord_3513481).sum := by decide
  have hdescent : baseEnd_3513481 < baseStart_3513481 := by decide
  rcases family_descends (prefixWord ++ tailWord_3513481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3513498 : List Nat := [3, 1, 1, 5, 1, 1, 2, 1, 4, 1, 3]
def baseStart_3513498 : Nat := 118140960795 + 3513498 * 2 ^ 59
def prefixEnd_3513498 : Nat := 4983230072969 + 3 ^ 40 * 3513498 * 2
def baseEnd_3513498 : Nat := 1804113252610799656616723

theorem tailTrace_3513498 : CollatzResearch.WordTrace tailWord_3513498 prefixEnd_3513498 1804113252610799656616723 := by
  unfold tailWord_3513498
  simp only [CollatzResearch.WordTrace]
  refine ⟨32036949956301069632619287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85431866550136185686984765 32036949956301069632619287)
  ·
    refine ⟨48055424934451604448928931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32036949956301069632619287 48055424934451604448928931)
    ·
      refine ⟨72083137401677406673393397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48055424934451604448928931 72083137401677406673393397)
      ·
        refine ⟨6757794131407256875630631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 72083137401677406673393397 6757794131407256875630631)
        ·
          refine ⟨10136691197110885313445947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6757794131407256875630631 10136691197110885313445947)
          ·
            refine ⟨15205036795666327970168921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10136691197110885313445947 15205036795666327970168921)
            ·
              refine ⟨11403777596749745977626691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15205036795666327970168921 11403777596749745977626691)
              ·
                refine ⟨17105666395124618966440037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11403777596749745977626691 17105666395124618966440037)
                ·
                  refine ⟨3207312449085866056207507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17105666395124618966440037 3207312449085866056207507)
                  ·
                    refine ⟨4810968673628799084311261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3207312449085866056207507 4810968673628799084311261)
                    ·
                      refine ⟨1804113252610799656616723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4810968673628799084311261 1804113252610799656616723)
                      ·
                        rfl

theorem cell23_3513498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_3513498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3513498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3513498 prefixEnd_3513498 := by exact prefixLift 3513498
  have htrace : WordTrace (prefixWord ++ tailWord_3513498) baseStart_3513498 baseEnd_3513498 := by
    simpa [prefixWord, tailWord_3513498, baseEnd_3513498] using wordTrace_append hprefix tailTrace_3513498
  have hstable : (prefixWord ++ tailWord_3513498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3513498).length < 2 ^ (prefixWord ++ tailWord_3513498).sum := by decide
  have hdescent : baseEnd_3513498 < baseStart_3513498 := by decide
  rcases family_descends (prefixWord ++ tailWord_3513498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3513504 : List Nat := [2, 1, 1, 4, 2, 1, 2, 1, 2, 3, 4]
def baseStart_3513504 : Nat := 118140960795 + 3513504 * 2 ^ 59
def prefixEnd_3513504 : Nat := 4983230072969 + 3 ^ 40 * 3513504 * 2
def baseEnd_3513504 : Nat := 1804116333494726633141695

theorem tailTrace_3513504 : CollatzResearch.WordTrace tailWord_3513504 prefixEnd_3513504 1804116333494726633141695 := by
  unfold tailWord_3513504
  simp only [CollatzResearch.WordTrace]
  refine ⟨64074009331591270777597783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85432012442121694370130377 64074009331591270777597783)
  ·
    refine ⟨96111013997386906166396675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64074009331591270777597783 96111013997386906166396675)
    ·
      refine ⟨144166520996080359249595013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96111013997386906166396675 144166520996080359249595013)
      ·
        refine ⟨27031222686765067359299065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 144166520996080359249595013 27031222686765067359299065)
        ·
          refine ⟨20273417015073800519474299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27031222686765067359299065 20273417015073800519474299)
          ·
            refine ⟨30410125522610700779211449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20273417015073800519474299 30410125522610700779211449)
            ·
              refine ⟨22807594141958025584408587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30410125522610700779211449 22807594141958025584408587)
              ·
                refine ⟨34211391212937038376612881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22807594141958025584408587 34211391212937038376612881)
                ·
                  refine ⟨25658543409702778782459661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34211391212937038376612881 25658543409702778782459661)
                  ·
                    refine ⟨9621953778638542043422373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25658543409702778782459661 9621953778638542043422373)
                    ·
                      refine ⟨1804116333494726633141695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9621953778638542043422373 1804116333494726633141695)
                      ·
                        rfl

theorem cell23_3513504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 1, 2, 3, 4].length) (baseStart_3513504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3513504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3513504 prefixEnd_3513504 := by exact prefixLift 3513504
  have htrace : WordTrace (prefixWord ++ tailWord_3513504) baseStart_3513504 baseEnd_3513504 := by
    simpa [prefixWord, tailWord_3513504, baseEnd_3513504] using wordTrace_append hprefix tailTrace_3513504
  have hstable : (prefixWord ++ tailWord_3513504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3513504).length < 2 ^ (prefixWord ++ tailWord_3513504).sum := by decide
  have hdescent : baseEnd_3513504 < baseStart_3513504 := by decide
  rcases family_descends (prefixWord ++ tailWord_3513504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3513549 : List Nat := [1, 6, 2, 2, 1, 1, 2, 2, 2, 1, 3]
def baseStart_3513549 : Nat := 118140960795 + 3513549 * 2 ^ 59
def prefixEnd_3513549 : Nat := 4983230072969 + 3 ^ 40 * 3513549 * 2
def baseEnd_3513549 : Nat := 1804139440124178957078989

theorem tailTrace_3513549 : CollatzResearch.WordTrace tailWord_3513549 prefixEnd_3513549 1804139440124178957078989 := by
  unfold tailWord_3513549
  simp only [CollatzResearch.WordTrace]
  refine ⟨128149659948019514240583701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85433106632013009493722467 128149659948019514240583701)
  ·
    refine ⟨6007015310063414730027361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 128149659948019514240583701 6007015310063414730027361)
    ·
      refine ⟨4505261482547561047520521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6007015310063414730027361 4505261482547561047520521)
      ·
        refine ⟨3378946111910670785640391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4505261482547561047520521 3378946111910670785640391)
        ·
          refine ⟨5068419167866006178460587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3378946111910670785640391 5068419167866006178460587)
          ·
            refine ⟨7602628751799009267690881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5068419167866006178460587 7602628751799009267690881)
            ·
              refine ⟨5701971563849256950768161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7602628751799009267690881 5701971563849256950768161)
              ·
                refine ⟨4276478672886942713076121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5701971563849256950768161 4276478672886942713076121)
                ·
                  refine ⟨3207359004665207034807091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4276478672886942713076121 3207359004665207034807091)
                  ·
                    refine ⟨4811038506997810552210637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3207359004665207034807091 4811038506997810552210637)
                    ·
                      refine ⟨1804139440124178957078989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4811038506997810552210637 1804139440124178957078989)
                      ·
                        rfl

theorem cell23_3513549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_3513549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3513549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3513549 prefixEnd_3513549 := by exact prefixLift 3513549
  have htrace : WordTrace (prefixWord ++ tailWord_3513549) baseStart_3513549 baseEnd_3513549 := by
    simpa [prefixWord, tailWord_3513549, baseEnd_3513549] using wordTrace_append hprefix tailTrace_3513549
  have hstable : (prefixWord ++ tailWord_3513549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3513549).length < 2 ^ (prefixWord ++ tailWord_3513549).sum := by decide
  have hdescent : baseEnd_3513549 < baseStart_3513549 := by decide
  rcases family_descends (prefixWord ++ tailWord_3513549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3513628 : List Nat := [2, 2, 3, 1, 1, 1, 4, 1, 2, 4, 2]
def baseStart_3513628 : Nat := 118140960795 + 3513628 * 2 ^ 59
def prefixEnd_3513628 : Nat := 4983230072969 + 3 ^ 40 * 3513628 * 2
def baseEnd_3513628 : Nat := 1804180005095884147991125

theorem tailTrace_3513628 : CollatzResearch.WordTrace tailWord_3513628 prefixEnd_3513628 1804180005095884147991125 := by
  unfold tailWord_3513628
  simp only [CollatzResearch.WordTrace]
  refine ⟨64076270657366655366354769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85435027543155540488473025 64076270657366655366354769)
  ·
    refine ⟨48057202993024991524766077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64076270657366655366354769 48057202993024991524766077)
    ·
      refine ⟨18021451122384371821787279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48057202993024991524766077 18021451122384371821787279)
      ·
        refine ⟨27032176683576557732680919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18021451122384371821787279 27032176683576557732680919)
        ·
          refine ⟨40548265025364836599021379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27032176683576557732680919 40548265025364836599021379)
          ·
            refine ⟨60822397538047254898532069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40548265025364836599021379 60822397538047254898532069)
            ·
              refine ⟨11404199538383860293474763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60822397538047254898532069 11404199538383860293474763)
              ·
                refine ⟨17106299307575790440212145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11404199538383860293474763 17106299307575790440212145)
                ·
                  refine ⟨12829724480681842830159109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17106299307575790440212145 12829724480681842830159109)
                  ·
                    refine ⟨2405573340127845530654833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12829724480681842830159109 2405573340127845530654833)
                    ·
                      refine ⟨1804180005095884147991125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2405573340127845530654833 1804180005095884147991125)
                      ·
                        rfl

theorem cell23_3513628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 1, 2, 4, 2].length) (baseStart_3513628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3513628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3513628 prefixEnd_3513628 := by exact prefixLift 3513628
  have htrace : WordTrace (prefixWord ++ tailWord_3513628) baseStart_3513628 baseEnd_3513628 := by
    simpa [prefixWord, tailWord_3513628, baseEnd_3513628] using wordTrace_append hprefix tailTrace_3513628
  have hstable : (prefixWord ++ tailWord_3513628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3513628).length < 2 ^ (prefixWord ++ tailWord_3513628).sum := by decide
  have hdescent : baseEnd_3513628 < baseStart_3513628 := by decide
  rcases family_descends (prefixWord ++ tailWord_3513628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3513665 : List Nat := [1, 2, 5, 2, 1, 2, 1, 2, 2, 2, 3]
def baseStart_3513665 : Nat := 118140960795 + 3513665 * 2 ^ 59
def prefixEnd_3513665 : Nat := 4983230072969 + 3 ^ 40 * 3513665 * 2
def baseEnd_3513665 : Nat := 1804199003880100503228455

theorem tailTrace_3513665 : CollatzResearch.WordTrace tailWord_3513665 prefixEnd_3513665 1804199003880100503228455 := by
  unfold tailWord_3513665
  simp only [CollatzResearch.WordTrace]
  refine ⟨128153890815599266051806449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85435927210399510701204299 128153890815599266051806449)
  ·
    refine ⟨96115418111699449538854837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128153890815599266051806449 96115418111699449538854837)
    ·
      refine ⟨9010820447971823394267641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 96115418111699449538854837 9010820447971823394267641)
      ·
        refine ⟨6758115335978867545700731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9010820447971823394267641 6758115335978867545700731)
        ·
          refine ⟨10137173003968301318551097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6758115335978867545700731 10137173003968301318551097)
          ·
            refine ⟨7602879752976225988913323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10137173003968301318551097 7602879752976225988913323)
            ·
              refine ⟨11404319629464338983369985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7602879752976225988913323 11404319629464338983369985)
              ·
                refine ⟨8553239722098254237527489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11404319629464338983369985 8553239722098254237527489)
                ·
                  refine ⟨6414929791573690678145617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8553239722098254237527489 6414929791573690678145617)
                  ·
                    refine ⟨4811197343680268008609213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6414929791573690678145617 4811197343680268008609213)
                    ·
                      refine ⟨1804199003880100503228455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4811197343680268008609213 1804199003880100503228455)
                      ·
                        rfl

theorem cell23_3513665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_3513665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3513665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3513665 prefixEnd_3513665 := by exact prefixLift 3513665
  have htrace : WordTrace (prefixWord ++ tailWord_3513665) baseStart_3513665 baseEnd_3513665 := by
    simpa [prefixWord, tailWord_3513665, baseEnd_3513665] using wordTrace_append hprefix tailTrace_3513665
  have hstable : (prefixWord ++ tailWord_3513665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3513665).length < 2 ^ (prefixWord ++ tailWord_3513665).sum := by decide
  have hdescent : baseEnd_3513665 < baseStart_3513665 := by decide
  rcases family_descends (prefixWord ++ tailWord_3513665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3513668 : List Nat := [2, 3, 4, 1, 1, 1, 2, 1, 8]
def baseStart_3513668 : Nat := 118140960795 + 3513668 * 2 ^ 59
def prefixEnd_3513668 : Nat := 4983230072969 + 3 ^ 40 * 3513668 * 2
def baseEnd_3513668 : Nat := 200466727146895999054549

theorem tailTrace_3513668 : CollatzResearch.WordTrace tailWord_3513668 prefixEnd_3513668 200466727146895999054549 := by
  unfold tailWord_3513668
  simp only [CollatzResearch.WordTrace]
  refine ⟨64077000117294198782082829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85436000156392265042777105 64077000117294198782082829)
  ·
    refine ⟨24028875043985324543281061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64077000117294198782082829 24028875043985324543281061)
    ·
      refine ⟨4505414070747248351865199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24028875043985324543281061 4505414070747248351865199)
      ·
        refine ⟨6758121106120872527797799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4505414070747248351865199 6758121106120872527797799)
        ·
          refine ⟨10137181659181308791696699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6758121106120872527797799 10137181659181308791696699)
          ·
            refine ⟨15205772488771963187545049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10137181659181308791696699 15205772488771963187545049)
            ·
              refine ⟨11404329366578972390658787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15205772488771963187545049 11404329366578972390658787)
              ·
                refine ⟨17106494049868458585988181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11404329366578972390658787 17106494049868458585988181)
                ·
                  refine ⟨200466727146895999054549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17106494049868458585988181 200466727146895999054549)
                  ·
                    rfl

theorem cell23_3513668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 1, 8].length) (baseStart_3513668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3513668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3513668 prefixEnd_3513668 := by exact prefixLift 3513668
  have htrace : WordTrace (prefixWord ++ tailWord_3513668) baseStart_3513668 baseEnd_3513668 := by
    simpa [prefixWord, tailWord_3513668, baseEnd_3513668] using wordTrace_append hprefix tailTrace_3513668
  have hstable : (prefixWord ++ tailWord_3513668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3513668).length < 2 ^ (prefixWord ++ tailWord_3513668).sum := by decide
  have hdescent : baseEnd_3513668 < baseStart_3513668 := by decide
  rcases family_descends (prefixWord ++ tailWord_3513668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3513681 : List Nat := [1, 2, 2, 1, 4, 1, 2, 2, 3, 5]
def baseStart_3513681 : Nat := 118140960795 + 3513681 * 2 ^ 59
def prefixEnd_3513681 : Nat := 4983230072969 + 3 ^ 40 * 3513681 * 2
def baseEnd_3513681 : Nat := 601402406523524146876127

theorem tailTrace_3513681 : CollatzResearch.WordTrace tailWord_3513681 prefixEnd_3513681 601402406523524146876127 := by
  unfold tailWord_3513681
  simp only [CollatzResearch.WordTrace]
  refine ⟨128154474383541300784388897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85436316255694200522925931 128154474383541300784388897)
  ·
    refine ⟨96115855787655975588291673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128154474383541300784388897 96115855787655975588291673)
    ·
      refine ⟨72086891840741981691218755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96115855787655975588291673 72086891840741981691218755)
      ·
        refine ⟨108130337761112972536828133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72086891840741981691218755 108130337761112972536828133)
        ·
          refine ⟨20274438330208682350655275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108130337761112972536828133 20274438330208682350655275)
          ·
            refine ⟨30411657495313023525982913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20274438330208682350655275 30411657495313023525982913)
            ·
              refine ⟨22808743121484767644487185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30411657495313023525982913 22808743121484767644487185)
              ·
                refine ⟨17106557341113575733365389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22808743121484767644487185 17106557341113575733365389)
                ·
                  refine ⟨6414959002917590900012021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17106557341113575733365389 6414959002917590900012021)
                  ·
                    refine ⟨601402406523524146876127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6414959002917590900012021 601402406523524146876127)
                    ·
                      rfl

theorem cell23_3513681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 2, 3, 5].length) (baseStart_3513681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3513681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3513681 prefixEnd_3513681 := by exact prefixLift 3513681
  have htrace : WordTrace (prefixWord ++ tailWord_3513681) baseStart_3513681 baseEnd_3513681 := by
    simpa [prefixWord, tailWord_3513681, baseEnd_3513681] using wordTrace_append hprefix tailTrace_3513681
  have hstable : (prefixWord ++ tailWord_3513681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3513681).length < 2 ^ (prefixWord ++ tailWord_3513681).sum := by decide
  have hdescent : baseEnd_3513681 < baseStart_3513681 := by decide
  rcases family_descends (prefixWord ++ tailWord_3513681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3513685 : List Nat := [1, 3, 2, 2, 3, 3, 2, 1, 6]
def baseStart_3513685 : Nat := 118140960795 + 3513685 * 2 ^ 59
def prefixEnd_3513685 : Nat := 4983230072969 + 3 ^ 40 * 3513685 * 2
def baseEnd_3513685 : Nat := 200467697054798936108707

theorem tailTrace_3513685 : CollatzResearch.WordTrace tailWord_3513685 prefixEnd_3513685 200467697054798936108707 := by
  unfold tailWord_3513685
  simp only [CollatzResearch.WordTrace]
  refine ⟨128154620275526809467534509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85436413517017872978356339 128154620275526809467534509)
  ·
    refine ⟨48057982603322553550325441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128154620275526809467534509 48057982603322553550325441)
    ·
      refine ⟨36043486952491915162744081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48057982603322553550325441 36043486952491915162744081)
      ·
        refine ⟨27032615214368936372058061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36043486952491915162744081 27032615214368936372058061)
        ·
          refine ⟨10137230705388351139521773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27032615214368936372058061 10137230705388351139521773)
          ·
            refine ⟨3801461514520631677320665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10137230705388351139521773 3801461514520631677320665)
            ·
              refine ⟨2851096135890473757990499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3801461514520631677320665 2851096135890473757990499)
              ·
                refine ⟨4276644203835710636985749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2851096135890473757990499 4276644203835710636985749)
                ·
                  refine ⟨200467697054798936108707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4276644203835710636985749 200467697054798936108707)
                  ·
                    rfl

theorem cell23_3513685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 2, 1, 6].length) (baseStart_3513685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3513685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3513685 prefixEnd_3513685 := by exact prefixLift 3513685
  have htrace : WordTrace (prefixWord ++ tailWord_3513685) baseStart_3513685 baseEnd_3513685 := by
    simpa [prefixWord, tailWord_3513685, baseEnd_3513685] using wordTrace_append hprefix tailTrace_3513685
  have hstable : (prefixWord ++ tailWord_3513685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3513685).length < 2 ^ (prefixWord ++ tailWord_3513685).sum := by decide
  have hdescent : baseEnd_3513685 < baseStart_3513685 := by decide
  rcases family_descends (prefixWord ++ tailWord_3513685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3513688 : List Nat := [2, 1, 2, 2, 1, 1, 3, 2, 4, 3, 2]
def baseStart_3513688 : Nat := 118140960795 + 3513688 * 2 ^ 59
def prefixEnd_3513688 : Nat := 4983230072969 + 3 ^ 40 * 3513688 * 2
def baseEnd_3513688 : Nat := 1804210813935153913240849

theorem tailTrace_3513688 : CollatzResearch.WordTrace tailWord_3513688 prefixEnd_3513688 1804210813935153913240849 := by
  unfold tailWord_3513688
  simp only [CollatzResearch.WordTrace]
  refine ⟨64077364847257970489946859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85436486463010627319929145 64077364847257970489946859)
  ·
    refine ⟨96116047270886955734920289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64077364847257970489946859 96116047270886955734920289)
    ·
      refine ⟨72087035453165216801190217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96116047270886955734920289 72087035453165216801190217)
      ·
        refine ⟨54065276589873912600892663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72087035453165216801190217 54065276589873912600892663)
        ·
          refine ⟨81097914884810868901338995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54065276589873912600892663 81097914884810868901338995)
          ·
            refine ⟨121646872327216303352008493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81097914884810868901338995 121646872327216303352008493)
            ·
              refine ⟨45617577122706113757003185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 121646872327216303352008493 45617577122706113757003185)
              ·
                refine ⟨34213182842029585317752389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45617577122706113757003185 34213182842029585317752389)
                ·
                  refine ⟨6414971782880547247078573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34213182842029585317752389 6414971782880547247078573)
                  ·
                    refine ⟨2405614418580205217654465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6414971782880547247078573 2405614418580205217654465)
                    ·
                      refine ⟨1804210813935153913240849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2405614418580205217654465 1804210813935153913240849)
                      ·
                        rfl

theorem cell23_3513688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 2, 4, 3, 2].length) (baseStart_3513688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3513688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3513688 prefixEnd_3513688 := by exact prefixLift 3513688
  have htrace : WordTrace (prefixWord ++ tailWord_3513688) baseStart_3513688 baseEnd_3513688 := by
    simpa [prefixWord, tailWord_3513688, baseEnd_3513688] using wordTrace_append hprefix tailTrace_3513688
  have hstable : (prefixWord ++ tailWord_3513688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3513688).length < 2 ^ (prefixWord ++ tailWord_3513688).sum := by decide
  have hdescent : baseEnd_3513688 < baseStart_3513688 := by decide
  rcases family_descends (prefixWord ++ tailWord_3513688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3513698 : List Nat := [3, 3, 2, 1, 1, 1, 3, 1, 3, 5]
def baseStart_3513698 : Nat := 118140960795 + 3513698 * 2 ^ 59
def prefixEnd_3513698 : Nat := 4983230072969 + 3 ^ 40 * 3513698 * 2
def baseEnd_3513698 : Nat := 601405316247232958038601

theorem tailTrace_3513698 : CollatzResearch.WordTrace tailWord_3513698 prefixEnd_3513698 601405316247232958038601 := by
  unfold tailWord_3513698
  simp only [CollatzResearch.WordTrace]
  refine ⟨32038773606119928171939437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85436729616319808458505165 32038773606119928171939437)
  ·
    refine ⟨12014540102294973064477289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32038773606119928171939437 12014540102294973064477289)
    ·
      refine ⟨9010905076721229798357967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12014540102294973064477289 9010905076721229798357967)
      ·
        refine ⟨13516357615081844697536951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9010905076721229798357967 13516357615081844697536951)
        ·
          refine ⟨20274536422622767046305427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13516357615081844697536951 20274536422622767046305427)
          ·
            refine ⟨30411804633934150569458141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20274536422622767046305427 30411804633934150569458141)
            ·
              refine ⟨11404426737725306463546803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30411804633934150569458141 11404426737725306463546803)
              ·
                refine ⟨17106640106587959695320205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11404426737725306463546803 17106640106587959695320205)
                ·
                  refine ⟨6414990039970484885745077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17106640106587959695320205 6414990039970484885745077)
                  ·
                    refine ⟨601405316247232958038601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6414990039970484885745077 601405316247232958038601)
                    ·
                      rfl

theorem cell23_3513698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 1, 3, 5].length) (baseStart_3513698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3513698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3513698 prefixEnd_3513698 := by exact prefixLift 3513698
  have htrace : WordTrace (prefixWord ++ tailWord_3513698) baseStart_3513698 baseEnd_3513698 := by
    simpa [prefixWord, tailWord_3513698, baseEnd_3513698] using wordTrace_append hprefix tailTrace_3513698
  have hstable : (prefixWord ++ tailWord_3513698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3513698).length < 2 ^ (prefixWord ++ tailWord_3513698).sum := by decide
  have hdescent : baseEnd_3513698 < baseStart_3513698 := by decide
  rcases family_descends (prefixWord ++ tailWord_3513698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3513711 : List Nat := [1, 1, 2, 1, 3, 1, 5, 2, 1, 6]
def baseStart_3513711 : Nat := 118140960795 + 3513711 * 2 ^ 59
def prefixEnd_3513711 : Nat := 4983230072969 + 3 ^ 40 * 3513711 * 2
def baseEnd_3513711 : Nat := 601407541330069107751081

theorem tailTrace_3513711 : CollatzResearch.WordTrace tailWord_3513711 prefixEnd_3513711 601407541330069107751081 := by
  unfold tailWord_3513711
  simp only [CollatzResearch.WordTrace]
  refine ⟨128155568573432615907980987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85437045715621743938653991 128155568573432615907980987)
  ·
    refine ⟨192233352860148923861971481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128155568573432615907980987 192233352860148923861971481)
    ·
      refine ⟨144175014645111692896478611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192233352860148923861971481 144175014645111692896478611)
      ·
        refine ⟨216262521967667539344717917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144175014645111692896478611 216262521967667539344717917)
        ·
          refine ⟨81098445737875327254269219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 216262521967667539344717917 81098445737875327254269219)
          ·
            refine ⟨121647668606812990881403829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81098445737875327254269219 121647668606812990881403829)
            ·
              refine ⟨11404468931888717895131609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 121647668606812990881403829 11404468931888717895131609)
              ·
                refine ⟨8553351698916538421348707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11404468931888717895131609 8553351698916538421348707)
                ·
                  refine ⟨12830027548374807632023061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8553351698916538421348707 12830027548374807632023061)
                  ·
                    refine ⟨601407541330069107751081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12830027548374807632023061 601407541330069107751081)
                    ·
                      rfl

theorem cell23_3513711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 2, 1, 6].length) (baseStart_3513711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3513711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3513711 prefixEnd_3513711 := by exact prefixLift 3513711
  have htrace : WordTrace (prefixWord ++ tailWord_3513711) baseStart_3513711 baseEnd_3513711 := by
    simpa [prefixWord, tailWord_3513711, baseEnd_3513711] using wordTrace_append hprefix tailTrace_3513711
  have hstable : (prefixWord ++ tailWord_3513711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3513711).length < 2 ^ (prefixWord ++ tailWord_3513711).sum := by decide
  have hdescent : baseEnd_3513711 < baseStart_3513711 := by decide
  rcases family_descends (prefixWord ++ tailWord_3513711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3513729 : List Nat := [1, 2, 4, 3, 2, 1, 1, 4, 1, 1, 3]
def baseStart_3513729 : Nat := 118140960795 + 3513729 * 2 ^ 59
def prefixEnd_3513729 : Nat := 4983230072969 + 3 ^ 40 * 3513729 * 2
def baseEnd_3513729 : Nat := 1804231866641988252828161

theorem tailTrace_3513729 : CollatzResearch.WordTrace tailWord_3513729 prefixEnd_3513729 1804231866641988252828161 := by
  unfold tailWord_3513729
  simp only [CollatzResearch.WordTrace]
  refine ⟨128156225087367404982136241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85437483391578269988090827 128156225087367404982136241)
  ·
    refine ⟨96117168815525553736602181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128156225087367404982136241 96117168815525553736602181)
    ·
      refine ⟨18021969152911041325612909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96117168815525553736602181 18021969152911041325612909)
      ·
        refine ⟨6758238432341640497104841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18021969152911041325612909 6758238432341640497104841)
        ·
          refine ⟨5068678824256230372828631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6758238432341640497104841 5068678824256230372828631)
          ·
            refine ⟨7603018236384345559242947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5068678824256230372828631 7603018236384345559242947)
            ·
              refine ⟨11404527354576518338864421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7603018236384345559242947 11404527354576518338864421)
              ·
                refine ⟨2138348878983097188537079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11404527354576518338864421 2138348878983097188537079)
                ·
                  refine ⟨3207523318474645782805619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2138348878983097188537079 3207523318474645782805619)
                  ·
                    refine ⟨4811284977711968674208429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3207523318474645782805619 4811284977711968674208429)
                    ·
                      refine ⟨1804231866641988252828161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4811284977711968674208429 1804231866641988252828161)
                      ·
                        rfl

theorem cell23_3513729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 4, 1, 1, 3].length) (baseStart_3513729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3513729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3513729 prefixEnd_3513729 := by exact prefixLift 3513729
  have htrace : WordTrace (prefixWord ++ tailWord_3513729) baseStart_3513729 baseEnd_3513729 := by
    simpa [prefixWord, tailWord_3513729, baseEnd_3513729] using wordTrace_append hprefix tailTrace_3513729
  have hstable : (prefixWord ++ tailWord_3513729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3513729).length < 2 ^ (prefixWord ++ tailWord_3513729).sum := by decide
  have hdescent : baseEnd_3513729 < baseStart_3513729 := by decide
  rcases family_descends (prefixWord ++ tailWord_3513729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3513756 : List Nat := [2, 2, 3, 4, 2, 1, 1, 1, 2, 3, 2]
def baseStart_3513756 : Nat := 118140960795 + 3513756 * 2 ^ 59
def prefixEnd_3513756 : Nat := 4983230072969 + 3 ^ 40 * 3513756 * 2
def baseEnd_3513756 : Nat := 1804245730619659647190537

theorem tailTrace_3513756 : CollatzResearch.WordTrace tailWord_3513756 prefixEnd_3513756 1804245730619659647190537 := by
  unfold tailWord_3513756
  simp only [CollatzResearch.WordTrace]
  refine ⟨64078604929134794296684561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85438139905513059062246081 64078604929134794296684561)
  ·
    refine ⟨48058953696851095722513421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64078604929134794296684561 48058953696851095722513421)
    ·
      refine ⟨18022107636319160895942533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48058953696851095722513421 18022107636319160895942533)
      ·
        refine ⟨3379145181809842667989225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18022107636319160895942533 3379145181809842667989225)
        ·
          refine ⟨2534358886357382000991919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3379145181809842667989225 2534358886357382000991919)
          ·
            refine ⟨3801538329536073001487879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2534358886357382000991919 3801538329536073001487879)
            ·
              refine ⟨5702307494304109502231819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3801538329536073001487879 5702307494304109502231819)
              ·
                refine ⟨8553461241456164253347729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5702307494304109502231819 8553461241456164253347729)
                ·
                  refine ⟨6415095931092123190010797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8553461241456164253347729 6415095931092123190010797)
                  ·
                    refine ⟨2405660974159546196254049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6415095931092123190010797 2405660974159546196254049)
                    ·
                      refine ⟨1804245730619659647190537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2405660974159546196254049 1804245730619659647190537)
                      ·
                        rfl

theorem cell23_3513756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_3513756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3513756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3513756 prefixEnd_3513756 := by exact prefixLift 3513756
  have htrace : WordTrace (prefixWord ++ tailWord_3513756) baseStart_3513756 baseEnd_3513756 := by
    simpa [prefixWord, tailWord_3513756, baseEnd_3513756] using wordTrace_append hprefix tailTrace_3513756
  have hstable : (prefixWord ++ tailWord_3513756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3513756).length < 2 ^ (prefixWord ++ tailWord_3513756).sum := by decide
  have hdescent : baseEnd_3513756 < baseStart_3513756 := by decide
  rcases family_descends (prefixWord ++ tailWord_3513756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3513791 : List Nat := [1, 1, 2, 2, 2, 1, 1, 3, 1, 5, 4]
def baseStart_3513791 : Nat := 118140960795 + 3513791 * 2 ^ 59
def prefixEnd_3513791 : Nat := 4983230072969 + 3 ^ 40 * 3513791 * 2
def baseEnd_3513791 : Nat := 1804263702442567010252875

theorem tailTrace_3513791 : CollatzResearch.WordTrace tailWord_3513791 prefixEnd_3513791 1804263702442567010252875 := by
  unfold tailWord_3513791
  simp only [CollatzResearch.WordTrace]
  refine ⟨128158486413142789570893227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85438990942095193047262151 128158486413142789570893227)
  ·
    refine ⟨192237729619714184356339841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128158486413142789570893227 192237729619714184356339841)
    ·
      refine ⟨144178297214785638267254881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192237729619714184356339841 144178297214785638267254881)
      ·
        refine ⟨108133722911089228700441161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144178297214785638267254881 108133722911089228700441161)
        ·
          refine ⟨81100292183316921525330871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108133722911089228700441161 81100292183316921525330871)
          ·
            refine ⟨121650438274975382287996307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81100292183316921525330871 121650438274975382287996307)
            ·
              refine ⟨182475657412463073431994461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121650438274975382287996307 182475657412463073431994461)
              ·
                refine ⟨68428371529673652536997923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 182475657412463073431994461 68428371529673652536997923)
                ·
                  refine ⟨102642557294510478805496885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68428371529673652536997923 102642557294510478805496885)
                  ·
                    refine ⟨9622739746360357388015333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 102642557294510478805496885 9622739746360357388015333)
                    ·
                      refine ⟨1804263702442567010252875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9622739746360357388015333 1804263702442567010252875)
                      ·
                        rfl

theorem cell23_3513791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 5, 4].length) (baseStart_3513791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3513791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3513791 prefixEnd_3513791 := by exact prefixLift 3513791
  have htrace : WordTrace (prefixWord ++ tailWord_3513791) baseStart_3513791 baseEnd_3513791 := by
    simpa [prefixWord, tailWord_3513791, baseEnd_3513791] using wordTrace_append hprefix tailTrace_3513791
  have hstable : (prefixWord ++ tailWord_3513791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3513791).length < 2 ^ (prefixWord ++ tailWord_3513791).sum := by decide
  have hdescent : baseEnd_3513791 < baseStart_3513791 := by decide
  rcases family_descends (prefixWord ++ tailWord_3513791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3513848 : List Nat := [2, 1, 2, 1, 1, 5, 3, 1, 7]
def baseStart_3513848 : Nat := 118140960795 + 3513848 * 2 ^ 59
def prefixEnd_3513848 : Nat := 4983230072969 + 3 ^ 40 * 3513848 * 2
def baseEnd_3513848 : Nat := 200476996759985920804457

theorem tailTrace_3513848 : CollatzResearch.WordTrace tailWord_3513848 prefixEnd_3513848 200476996759985920804457 := by
  unfold tailWord_3513848
  simp only [CollatzResearch.WordTrace]
  refine ⟨64080282686968144152859099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85440376915957525537145465 64080282686968144152859099)
  ·
    refine ⟨96120424030452216229288649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64080282686968144152859099 96120424030452216229288649)
    ·
      refine ⟨72090318022839162171966487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96120424030452216229288649 72090318022839162171966487)
      ·
        refine ⟨108135477034258743257949731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72090318022839162171966487 108135477034258743257949731)
        ·
          refine ⟨162203215551388114886924597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108135477034258743257949731 162203215551388114886924597)
          ·
            refine ⟨15206551457942635770649181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 162203215551388114886924597 15206551457942635770649181)
            ·
              refine ⟨5702456796728488413993443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15206551457942635770649181 5702456796728488413993443)
              ·
                refine ⟨8553685195092732620990165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5702456796728488413993443 8553685195092732620990165)
                ·
                  refine ⟨200476996759985920804457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8553685195092732620990165 200476996759985920804457)
                  ·
                    rfl

theorem cell23_3513848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 3, 1, 7].length) (baseStart_3513848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3513848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3513848 prefixEnd_3513848 := by exact prefixLift 3513848
  have htrace : WordTrace (prefixWord ++ tailWord_3513848) baseStart_3513848 baseEnd_3513848 := by
    simpa [prefixWord, tailWord_3513848, baseEnd_3513848] using wordTrace_append hprefix tailTrace_3513848
  have hstable : (prefixWord ++ tailWord_3513848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3513848).length < 2 ^ (prefixWord ++ tailWord_3513848).sum := by decide
  have hdescent : baseEnd_3513848 < baseStart_3513848 := by decide
  rcases family_descends (prefixWord ++ tailWord_3513848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3513902 : List Nat := [4, 1, 3, 1, 2, 1, 1, 1, 2, 5, 2]
def baseStart_3513902 : Nat := 118140960795 + 3513902 * 2 ^ 59
def prefixEnd_3513902 : Nat := 4983230072969 + 3 ^ 40 * 3513902 * 2
def baseEnd_3513902 : Nat := 1804320698795216075964865

theorem tailTrace_3513902 : CollatzResearch.WordTrace tailWord_3513902 prefixEnd_3513902 1804320698795216075964865 := by
  unfold tailWord_3513902
  simp only [CollatzResearch.WordTrace]
  refine ⟨16020316864467581941022995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85441689943827103685455973 16020316864467581941022995)
  ·
    refine ⟨24030475296701372911534493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16020316864467581941022995 24030475296701372911534493)
    ·
      refine ⟨9011428236263014841825435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24030475296701372911534493 9011428236263014841825435)
      ·
        refine ⟨13517142354394522262738153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9011428236263014841825435 13517142354394522262738153)
        ·
          refine ⟨10137856765795891697053615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13517142354394522262738153 10137856765795891697053615)
          ·
            refine ⟨15206785148693837545580423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10137856765795891697053615 15206785148693837545580423)
            ·
              refine ⟨22810177723040756318370635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15206785148693837545580423 22810177723040756318370635)
              ·
                refine ⟨34215266584561134477555953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22810177723040756318370635 34215266584561134477555953)
                ·
                  refine ⟨25661449938420850858166965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34215266584561134477555953 25661449938420850858166965)
                  ·
                    refine ⟨2405760931726954767953153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25661449938420850858166965 2405760931726954767953153)
                    ·
                      refine ⟨1804320698795216075964865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2405760931726954767953153 1804320698795216075964865)
                      ·
                        rfl

theorem cell23_3513902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 1, 2, 5, 2].length) (baseStart_3513902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3513902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3513902 prefixEnd_3513902 := by exact prefixLift 3513902
  have htrace : WordTrace (prefixWord ++ tailWord_3513902) baseStart_3513902 baseEnd_3513902 := by
    simpa [prefixWord, tailWord_3513902, baseEnd_3513902] using wordTrace_append hprefix tailTrace_3513902
  have hstable : (prefixWord ++ tailWord_3513902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3513902).length < 2 ^ (prefixWord ++ tailWord_3513902).sum := by decide
  have hdescent : baseEnd_3513902 < baseStart_3513902 := by decide
  rcases family_descends (prefixWord ++ tailWord_3513902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3513925 : List Nat := [1, 3, 1, 1, 1, 4, 3, 2, 3, 4]
def baseStart_3513925 : Nat := 118140960795 + 3513925 * 2 ^ 59
def prefixEnd_3513925 : Nat := 4983230072969 + 3 ^ 40 * 3513925 * 2
def baseEnd_3513925 : Nat := 601444169616756495325753

theorem tailTrace_3513925 : CollatzResearch.WordTrace tailWord_3513925 prefixEnd_3513925 601444169616756495325753 := by
  unfold tailWord_3513925
  simp only [CollatzResearch.WordTrace]
  refine ⟨128163373794657330456271229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85442249196438220304180819 128163373794657330456271229)
  ·
    refine ⟨48061265172996498921101711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128163373794657330456271229 48061265172996498921101711)
    ·
      refine ⟨72091897759494748381652567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48061265172996498921101711 72091897759494748381652567)
      ·
        refine ⟨108137846639242122572478851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72091897759494748381652567 108137846639242122572478851)
        ·
          refine ⟨162206769958863183858718277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108137846639242122572478851 162206769958863183858718277)
          ·
            refine ⟨30413769367286846973509677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 162206769958863183858718277 30413769367286846973509677)
            ·
              refine ⟨11405163512732567615066129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30413769367286846973509677 11405163512732567615066129)
              ·
                refine ⟨8553872634549425711299597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11405163512732567615066129 8553872634549425711299597)
                ·
                  refine ⟨3207702237956034641737349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8553872634549425711299597 3207702237956034641737349)
                  ·
                    refine ⟨601444169616756495325753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3207702237956034641737349 601444169616756495325753)
                    ·
                      rfl

theorem cell23_3513925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 2, 3, 4].length) (baseStart_3513925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3513925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3513925 prefixEnd_3513925 := by exact prefixLift 3513925
  have htrace : WordTrace (prefixWord ++ tailWord_3513925) baseStart_3513925 baseEnd_3513925 := by
    simpa [prefixWord, tailWord_3513925, baseEnd_3513925] using wordTrace_append hprefix tailTrace_3513925
  have hstable : (prefixWord ++ tailWord_3513925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3513925).length < 2 ^ (prefixWord ++ tailWord_3513925).sum := by decide
  have hdescent : baseEnd_3513925 < baseStart_3513925 := by decide
  rcases family_descends (prefixWord ++ tailWord_3513925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3513932 : List Nat := [2, 2, 1, 3, 1, 5, 1, 1, 2, 1, 4]
def baseStart_3513932 : Nat := 118140960795 + 3513932 * 2 ^ 59
def prefixEnd_3513932 : Nat := 4983230072969 + 3 ^ 40 * 3513932 * 2
def baseEnd_3513932 : Nat := 1804336103214850958589727

theorem tailTrace_3513932 : CollatzResearch.WordTrace tailWord_3513932 prefixEnd_3513932 1804336103214850958589727 := by
  unfold tailWord_3513932
  simp only [CollatzResearch.WordTrace]
  refine ⟨64081814552815985325888025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85442419403754647101184033 64081814552815985325888025)
  ·
    refine ⟨48061360914611988994416019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64081814552815985325888025 48061360914611988994416019)
    ·
      refine ⟨72092041371917983491624029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48061360914611988994416019 72092041371917983491624029)
      ·
        refine ⟨27034515514469243809359011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72092041371917983491624029 27034515514469243809359011)
        ·
          refine ⟨40551773271703865714038517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27034515514469243809359011 40551773271703865714038517)
          ·
            refine ⟨3801728744222237410691111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40551773271703865714038517 3801728744222237410691111)
            ·
              refine ⟨5702593116333356116036667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3801728744222237410691111 5702593116333356116036667)
              ·
                refine ⟨8553889674500034174055001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5702593116333356116036667 8553889674500034174055001)
                ·
                  refine ⟨6415417255875025630541251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8553889674500034174055001 6415417255875025630541251)
                  ·
                    refine ⟨9623125883812538445811877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6415417255875025630541251 9623125883812538445811877)
                    ·
                      refine ⟨1804336103214850958589727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9623125883812538445811877 1804336103214850958589727)
                      ·
                        rfl

theorem cell23_3513932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 1, 1, 2, 1, 4].length) (baseStart_3513932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3513932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3513932 prefixEnd_3513932 := by exact prefixLift 3513932
  have htrace : WordTrace (prefixWord ++ tailWord_3513932) baseStart_3513932 baseEnd_3513932 := by
    simpa [prefixWord, tailWord_3513932, baseEnd_3513932] using wordTrace_append hprefix tailTrace_3513932
  have hstable : (prefixWord ++ tailWord_3513932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3513932).length < 2 ^ (prefixWord ++ tailWord_3513932).sum := by decide
  have hdescent : baseEnd_3513932 < baseStart_3513932 := by decide
  rcases family_descends (prefixWord ++ tailWord_3513932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3513955 : List Nat := [1, 1, 1, 5, 1, 3, 3, 2, 6]
def baseStart_3513955 : Nat := 118140960795 + 3513955 * 2 ^ 59
def prefixEnd_3513955 : Nat := 4983230072969 + 3 ^ 40 * 3513955 * 2
def baseEnd_3513955 : Nat := 200483101474433818733569

theorem tailTrace_3513955 : CollatzResearch.WordTrace tailWord_3513955 prefixEnd_3513955 200483101474433818733569 := by
  unfold tailWord_3513955
  simp only [CollatzResearch.WordTrace]
  refine ⟨128164467984548645579863319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85442978656365763719908879 128164467984548645579863319)
  ·
    refine ⟨192246701976822968369794979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128164467984548645579863319 192246701976822968369794979)
    ·
      refine ⟨288370052965234452554692469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192246701976822968369794979 288370052965234452554692469)
      ·
        refine ⟨27034692465490729927002419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 288370052965234452554692469 27034692465490729927002419)
        ·
          refine ⟨40552038698236094890503629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27034692465490729927002419 40552038698236094890503629)
          ·
            refine ⟨15207014511838535583938861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40552038698236094890503629 15207014511838535583938861)
            ·
              refine ⟨5702630441939450843977073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15207014511838535583938861 5702630441939450843977073)
              ·
                refine ⟨4276972831454588132982805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5702630441939450843977073 4276972831454588132982805)
                ·
                  refine ⟨200483101474433818733569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4276972831454588132982805 200483101474433818733569)
                  ·
                    rfl

theorem cell23_3513955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 3, 2, 6].length) (baseStart_3513955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3513955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3513955 prefixEnd_3513955 := by exact prefixLift 3513955
  have htrace : WordTrace (prefixWord ++ tailWord_3513955) baseStart_3513955 baseEnd_3513955 := by
    simpa [prefixWord, tailWord_3513955, baseEnd_3513955] using wordTrace_append hprefix tailTrace_3513955
  have hstable : (prefixWord ++ tailWord_3513955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3513955).length < 2 ^ (prefixWord ++ tailWord_3513955).sum := by decide
  have hdescent : baseEnd_3513955 < baseStart_3513955 := by decide
  rcases family_descends (prefixWord ++ tailWord_3513955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3514035 : List Nat := [1, 1, 1, 2, 3, 3, 2, 3, 1, 2, 4]
def baseStart_3514035 : Nat := 118140960795 + 3514035 * 2 ^ 59
def prefixEnd_3514035 : Nat := 4983230072969 + 3 ^ 40 * 3514035 * 2
def baseEnd_3514035 : Nat := 1804388991722264055601753

theorem tailTrace_3514035 : CollatzResearch.WordTrace tailWord_3514035 prefixEnd_3514035 1804388991722264055601753 := by
  unfold tailWord_3514035
  simp only [CollatzResearch.WordTrace]
  refine ⟨128167385824258819242775559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85444923882839212828517039 128167385824258819242775559)
  ·
    refine ⟨192251078736388228864163339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128167385824258819242775559 192251078736388228864163339)
    ·
      refine ⟨288376618104582343296245009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192251078736388228864163339 288376618104582343296245009)
      ·
        refine ⟨216282463578436757472183757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 288376618104582343296245009 216282463578436757472183757)
        ·
          refine ⟨81105923841913784052068909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 216282463578436757472183757 81105923841913784052068909)
          ·
            refine ⟨30414721440717669019525841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81105923841913784052068909 30414721440717669019525841)
            ·
              refine ⟨22811041080538251764644381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30414721440717669019525841 22811041080538251764644381)
              ·
                refine ⟨8554140405201844411741643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22811041080538251764644381 8554140405201844411741643)
                ·
                  refine ⟨12831210607802766617612465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8554140405201844411741643 12831210607802766617612465)
                  ·
                    refine ⟨9623407955852074963209349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12831210607802766617612465 9623407955852074963209349)
                    ·
                      refine ⟨1804388991722264055601753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9623407955852074963209349 1804388991722264055601753)
                      ·
                        rfl

theorem cell23_3514035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 3, 1, 2, 4].length) (baseStart_3514035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3514035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3514035 prefixEnd_3514035 := by exact prefixLift 3514035
  have htrace : WordTrace (prefixWord ++ tailWord_3514035) baseStart_3514035 baseEnd_3514035 := by
    simpa [prefixWord, tailWord_3514035, baseEnd_3514035] using wordTrace_append hprefix tailTrace_3514035
  have hstable : (prefixWord ++ tailWord_3514035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3514035).length < 2 ^ (prefixWord ++ tailWord_3514035).sum := by decide
  have hdescent : baseEnd_3514035 < baseStart_3514035 := by decide
  rcases family_descends (prefixWord ++ tailWord_3514035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3514039 : List Nat := [1, 1, 3, 1, 5, 3, 1, 2, 1, 1, 4]
def baseStart_3514039 : Nat := 118140960795 + 3514039 * 2 ^ 59
def prefixEnd_3514039 : Nat := 4983230072969 + 3 ^ 40 * 3514039 * 2
def baseEnd_3514039 : Nat := 1804391045644882039951735

theorem tailTrace_3514039 : CollatzResearch.WordTrace tailWord_3514039 prefixEnd_3514039 1804391045644882039951735 := by
  unfold tailWord_3514039
  simp only [CollatzResearch.WordTrace]
  refine ⟨128167531716244327925921171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85445021144162885283947447 128167531716244327925921171)
  ·
    refine ⟨192251297574366491888881757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128167531716244327925921171 192251297574366491888881757)
    ·
      refine ⟨72094236590387434458330659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192251297574366491888881757 72094236590387434458330659)
      ·
        refine ⟨108141354885581151687495989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72094236590387434458330659 108141354885581151687495989)
        ·
          refine ⟨10138252020523232970702749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 108141354885581151687495989 10138252020523232970702749)
          ·
            refine ⟨3801844507696212364013531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10138252020523232970702749 3801844507696212364013531)
            ·
              refine ⟨5702766761544318546020297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3801844507696212364013531 5702766761544318546020297)
              ·
                refine ⟨4277075071158238909515223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5702766761544318546020297 4277075071158238909515223)
                ·
                  refine ⟨6415612606737358364272835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4277075071158238909515223 6415612606737358364272835)
                  ·
                    refine ⟨9623418910106037546409253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6415612606737358364272835 9623418910106037546409253)
                    ·
                      refine ⟨1804391045644882039951735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9623418910106037546409253 1804391045644882039951735)
                      ·
                        rfl

theorem cell23_3514039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 1, 2, 1, 1, 4].length) (baseStart_3514039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3514039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3514039 prefixEnd_3514039 := by exact prefixLift 3514039
  have htrace : WordTrace (prefixWord ++ tailWord_3514039) baseStart_3514039 baseEnd_3514039 := by
    simpa [prefixWord, tailWord_3514039, baseEnd_3514039] using wordTrace_append hprefix tailTrace_3514039
  have hstable : (prefixWord ++ tailWord_3514039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3514039).length < 2 ^ (prefixWord ++ tailWord_3514039).sum := by decide
  have hdescent : baseEnd_3514039 < baseStart_3514039 := by decide
  rcases family_descends (prefixWord ++ tailWord_3514039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3514042 : List Nat := [3, 1, 1, 1, 2, 5, 1, 1, 3, 2, 3]
def baseStart_3514042 : Nat := 118140960795 + 3514042 * 2 ^ 59
def prefixEnd_3514042 : Nat := 4983230072969 + 3 ^ 40 * 3514042 * 2
def baseEnd_3514042 : Nat := 1804392586086845528214221

theorem tailTrace_3514042 : CollatzResearch.WordTrace tailWord_3514042 prefixEnd_3514042 1804392586086845528214221 := by
  unfold tailWord_3514042
  simp only [CollatzResearch.WordTrace]
  refine ⟨32041910283808364859570095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85445094090155639625520253 32041910283808364859570095)
  ·
    refine ⟨48062865425712547289355143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32041910283808364859570095 48062865425712547289355143)
    ·
      refine ⟨72094298138568820934032715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48062865425712547289355143 72094298138568820934032715)
      ·
        refine ⟨108141447207853231401049073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72094298138568820934032715 108141447207853231401049073)
        ·
          refine ⟨81106085405889923550786805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108141447207853231401049073 81106085405889923550786805)
          ·
            refine ⟨7603695506802180332886263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 81106085405889923550786805 7603695506802180332886263)
            ·
              refine ⟨11405543260203270499329395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7603695506802180332886263 11405543260203270499329395)
              ·
                refine ⟨17108314890304905748994093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11405543260203270499329395 17108314890304905748994093)
                ·
                  refine ⟨6415618083864339655872785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17108314890304905748994093 6415618083864339655872785)
                  ·
                    refine ⟨4811713562898254741904589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6415618083864339655872785 4811713562898254741904589)
                    ·
                      refine ⟨1804392586086845528214221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4811713562898254741904589 1804392586086845528214221)
                      ·
                        rfl

theorem cell23_3514042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 1, 3, 2, 3].length) (baseStart_3514042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3514042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3514042 prefixEnd_3514042 := by exact prefixLift 3514042
  have htrace : WordTrace (prefixWord ++ tailWord_3514042) baseStart_3514042 baseEnd_3514042 := by
    simpa [prefixWord, tailWord_3514042, baseEnd_3514042] using wordTrace_append hprefix tailTrace_3514042
  have hstable : (prefixWord ++ tailWord_3514042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3514042).length < 2 ^ (prefixWord ++ tailWord_3514042).sum := by decide
  have hdescent : baseEnd_3514042 < baseStart_3514042 := by decide
  rcases family_descends (prefixWord ++ tailWord_3514042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3514052 : List Nat := [2, 3, 3, 1, 1, 1, 3, 2, 1, 2, 4]
def baseStart_3514052 : Nat := 118140960795 + 3514052 * 2 ^ 59
def prefixEnd_3514052 : Nat := 4983230072969 + 3 ^ 40 * 3514052 * 2
def baseEnd_3514052 : Nat := 1804397720893390489089175

theorem tailTrace_3514052 : CollatzResearch.WordTrace tailWord_3514052 prefixEnd_3514052 1804397720893390489089175 := by
  unfold tailWord_3514052
  simp only [CollatzResearch.WordTrace]
  refine ⟨64084002932598615573072205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85445337243464820764096273 64084002932598615573072205)
  ·
    refine ⟨24031501099724480839902077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64084002932598615573072205 24031501099724480839902077)
    ·
      refine ⟨9011812912396680314963279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24031501099724480839902077 9011812912396680314963279)
      ·
        refine ⟨13517719368595020472444919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9011812912396680314963279 13517719368595020472444919)
        ·
          refine ⟨20276579052892530708667379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13517719368595020472444919 20276579052892530708667379)
          ·
            refine ⟨30414868579338796063001069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20276579052892530708667379 30414868579338796063001069)
            ·
              refine ⟨11405575717252048523625401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30414868579338796063001069 11405575717252048523625401)
              ·
                refine ⟨8554181787939036392719051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11405575717252048523625401 8554181787939036392719051)
                ·
                  refine ⟨12831272681908554589078577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8554181787939036392719051 12831272681908554589078577)
                  ·
                    refine ⟨9623454511431415941808933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12831272681908554589078577 9623454511431415941808933)
                    ·
                      refine ⟨1804397720893390489089175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9623454511431415941808933 1804397720893390489089175)
                      ·
                        rfl

theorem cell23_3514052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_3514052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3514052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3514052 prefixEnd_3514052 := by exact prefixLift 3514052
  have htrace : WordTrace (prefixWord ++ tailWord_3514052) baseStart_3514052 baseEnd_3514052 := by
    simpa [prefixWord, tailWord_3514052, baseEnd_3514052] using wordTrace_append hprefix tailTrace_3514052
  have hstable : (prefixWord ++ tailWord_3514052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3514052).length < 2 ^ (prefixWord ++ tailWord_3514052).sum := by decide
  have hdescent : baseEnd_3514052 < baseStart_3514052 := by decide
  rcases family_descends (prefixWord ++ tailWord_3514052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3514056 : List Nat := [2, 1, 3, 1, 2, 2, 2, 5, 1, 2, 2]
def baseStart_3514056 : Nat := 118140960795 + 3514056 * 2 ^ 59
def prefixEnd_3514056 : Nat := 4983230072969 + 3 ^ 40 * 3514056 * 2
def baseEnd_3514056 : Nat := 1804399774816008473439157

theorem tailTrace_3514056 : CollatzResearch.WordTrace tailWord_3514056 prefixEnd_3514056 1804399774816008473439157 := by
  unfold tailWord_3514056
  simp only [CollatzResearch.WordTrace]
  refine ⟨64084075878591369914645011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85445434504788493219526681 64084075878591369914645011)
  ·
    refine ⟨96126113817887054871967517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64084075878591369914645011 96126113817887054871967517)
    ·
      refine ⟨36047292681707645576987819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96126113817887054871967517 36047292681707645576987819)
      ·
        refine ⟨54070939022561468365481729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36047292681707645576987819 54070939022561468365481729)
        ·
          refine ⟨40553204266921101274111297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54070939022561468365481729 40553204266921101274111297)
          ·
            refine ⟨30414903200190825955583473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40553204266921101274111297 30414903200190825955583473)
            ·
              refine ⟨22811177400143119466687605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30414903200190825955583473 22811177400143119466687605)
              ·
                refine ⟨2138547881263417450001963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22811177400143119466687605 2138547881263417450001963)
                ·
                  refine ⟨3207821821895126175002945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2138547881263417450001963 3207821821895126175002945)
                  ·
                    refine ⟨2405866366421344631252209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3207821821895126175002945 2405866366421344631252209)
                    ·
                      refine ⟨1804399774816008473439157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2405866366421344631252209 1804399774816008473439157)
                      ·
                        rfl

theorem cell23_3514056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 5, 1, 2, 2].length) (baseStart_3514056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3514056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3514056 prefixEnd_3514056 := by exact prefixLift 3514056
  have htrace : WordTrace (prefixWord ++ tailWord_3514056) baseStart_3514056 baseEnd_3514056 := by
    simpa [prefixWord, tailWord_3514056, baseEnd_3514056] using wordTrace_append hprefix tailTrace_3514056
  have hstable : (prefixWord ++ tailWord_3514056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3514056).length < 2 ^ (prefixWord ++ tailWord_3514056).sum := by decide
  have hdescent : baseEnd_3514056 < baseStart_3514056 := by decide
  rcases family_descends (prefixWord ++ tailWord_3514056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3514073 : List Nat := [1, 2, 1, 2, 3, 3, 4, 2, 1, 2, 2]
def baseStart_3514073 : Nat := 118140960795 + 3514073 * 2 ^ 59
def prefixEnd_3514073 : Nat := 4983230072969 + 3 ^ 40 * 3514073 * 2
def baseEnd_3514073 : Nat := 1804408503987134906926579

theorem tailTrace_3514073 : CollatzResearch.WordTrace tailWord_3514073 prefixEnd_3514073 1804408503987134906926579 := by
  unfold tailWord_3514073
  simp only [CollatzResearch.WordTrace]
  refine ⟨128168771798121151732658873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85445847865414101155105915 128168771798121151732658873)
  ·
    refine ⟨96126578848590863799494155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128168771798121151732658873 96126578848590863799494155)
    ·
      refine ⟨144189868272886295699241233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96126578848590863799494155 144189868272886295699241233)
      ·
        refine ⟨108142401204664721774430925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144189868272886295699241233 108142401204664721774430925)
        ·
          refine ⟨40553400451749270665411597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108142401204664721774430925 40553400451749270665411597)
          ·
            refine ⟨15207525169405976499529349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40553400451749270665411597 15207525169405976499529349)
            ·
              refine ⟨2851410969263620593661753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15207525169405976499529349 2851410969263620593661753)
              ·
                refine ⟨2138558226947715445246315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2851410969263620593661753 2138558226947715445246315)
                ·
                  refine ⟨3207837340421573167869473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2138558226947715445246315 3207837340421573167869473)
                  ·
                    refine ⟨2405878005316179875902105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3207837340421573167869473 2405878005316179875902105)
                    ·
                      refine ⟨1804408503987134906926579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2405878005316179875902105 1804408503987134906926579)
                      ·
                        rfl

theorem cell23_3514073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 4, 2, 1, 2, 2].length) (baseStart_3514073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3514073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3514073 prefixEnd_3514073 := by exact prefixLift 3514073
  have htrace : WordTrace (prefixWord ++ tailWord_3514073) baseStart_3514073 baseEnd_3514073 := by
    simpa [prefixWord, tailWord_3514073, baseEnd_3514073] using wordTrace_append hprefix tailTrace_3514073
  have hstable : (prefixWord ++ tailWord_3514073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3514073).length < 2 ^ (prefixWord ++ tailWord_3514073).sum := by decide
  have hdescent : baseEnd_3514073 < baseStart_3514073 := by decide
  rcases family_descends (prefixWord ++ tailWord_3514073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3514095 : List Nat := [1, 1, 2, 1, 5, 1, 1, 2, 2, 3, 4]
def baseStart_3514095 : Nat := 118140960795 + 3514095 * 2 ^ 59
def prefixEnd_3514095 : Nat := 4983230072969 + 3 ^ 40 * 3514095 * 2
def baseEnd_3514095 : Nat := 1804419800561533820851477

theorem tailTrace_3514095 : CollatzResearch.WordTrace tailWord_3514095 prefixEnd_3514095 1804419800561533820851477 := by
  unfold tailWord_3514095
  simp only [CollatzResearch.WordTrace]
  refine ⟨128169574204041449489959739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85446382802694299659973159 128169574204041449489959739)
  ·
    refine ⟨192254361306062174234939609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128169574204041449489959739 192254361306062174234939609)
    ·
      refine ⟨144190770979546630676204707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192254361306062174234939609 144190770979546630676204707)
      ·
        refine ⟨216286156469319946014307061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144190770979546630676204707 216286156469319946014307061)
        ·
          refine ⟨20276827168998744938841287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 216286156469319946014307061 20276827168998744938841287)
          ·
            refine ⟨30415240753498117408261931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20276827168998744938841287 30415240753498117408261931)
            ·
              refine ⟨45622861130247176112392897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30415240753498117408261931 45622861130247176112392897)
              ·
                refine ⟨34217145847685382084294673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45622861130247176112392897 34217145847685382084294673)
                ·
                  refine ⟨25662859385764036563221005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34217145847685382084294673 25662859385764036563221005)
                  ·
                    refine ⟨9623572269661513711207877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25662859385764036563221005 9623572269661513711207877)
                    ·
                      refine ⟨1804419800561533820851477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9623572269661513711207877 1804419800561533820851477)
                      ·
                        rfl

theorem cell23_3514095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 2, 2, 3, 4].length) (baseStart_3514095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3514095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3514095 prefixEnd_3514095 := by exact prefixLift 3514095
  have htrace : WordTrace (prefixWord ++ tailWord_3514095) baseStart_3514095 baseEnd_3514095 := by
    simpa [prefixWord, tailWord_3514095, baseEnd_3514095] using wordTrace_append hprefix tailTrace_3514095
  have hstable : (prefixWord ++ tailWord_3514095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3514095).length < 2 ^ (prefixWord ++ tailWord_3514095).sum := by decide
  have hdescent : baseEnd_3514095 < baseStart_3514095 := by decide
  rcases family_descends (prefixWord ++ tailWord_3514095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3514110 : List Nat := [4, 2, 2, 1, 4, 1, 2, 1, 1, 2, 3]
def baseStart_3514110 : Nat := 118140960795 + 3514110 * 2 ^ 59
def prefixEnd_3514110 : Nat := 4983230072969 + 3 ^ 40 * 3514110 * 2
def baseEnd_3514110 : Nat := 1804427502771351262163909

theorem tailTrace_3514110 : CollatzResearch.WordTrace tailWord_3514110 prefixEnd_3514110 1804427502771351262163909 := by
  unfold tailWord_3514110
  simp only [CollatzResearch.WordTrace]
  refine ⟨16021265162373388381469473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85446747532658071367837189 16021265162373388381469473)
  ·
    refine ⟨12015948871780041286102105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16021265162373388381469473 12015948871780041286102105)
    ·
      refine ⟨9011961653835030964576579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12015948871780041286102105 9011961653835030964576579)
      ·
        refine ⟨13517942480752546446864869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9011961653835030964576579 13517942480752546446864869)
        ·
          refine ⟨2534614215141102458787163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13517942480752546446864869 2534614215141102458787163)
          ·
            refine ⟨3801921322711653688180745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2534614215141102458787163 3801921322711653688180745)
            ·
              refine ⟨2851440992033740266135559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3801921322711653688180745 2851440992033740266135559)
              ·
                refine ⟨4277161488050610399203339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2851440992033740266135559 4277161488050610399203339)
                ·
                  refine ⟨6415742232075915598805009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4277161488050610399203339 6415742232075915598805009)
                  ·
                    refine ⟨4811806674056936699103757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6415742232075915598805009 4811806674056936699103757)
                    ·
                      refine ⟨1804427502771351262163909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4811806674056936699103757 1804427502771351262163909)
                      ·
                        rfl

theorem cell23_3514110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 2, 1, 1, 2, 3].length) (baseStart_3514110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3514110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3514110 prefixEnd_3514110 := by exact prefixLift 3514110
  have htrace : WordTrace (prefixWord ++ tailWord_3514110) baseStart_3514110 baseEnd_3514110 := by
    simpa [prefixWord, tailWord_3514110, baseEnd_3514110] using wordTrace_append hprefix tailTrace_3514110
  have hstable : (prefixWord ++ tailWord_3514110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3514110).length < 2 ^ (prefixWord ++ tailWord_3514110).sum := by decide
  have hdescent : baseEnd_3514110 < baseStart_3514110 := by decide
  rcases family_descends (prefixWord ++ tailWord_3514110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3514115 : List Nat := [1, 1, 1, 3, 2, 2, 2, 3, 2, 1, 5]
def baseStart_3514115 : Nat := 118140960795 + 3514115 * 2 ^ 59
def prefixEnd_3514115 : Nat := 4983230072969 + 3 ^ 40 * 3514115 * 2
def baseEnd_3514115 : Nat := 1804430070174623742601385

theorem tailTrace_3514115 : CollatzResearch.WordTrace tailWord_3514115 prefixEnd_3514115 1804430070174623742601385 := by
  unfold tailWord_3514115
  simp only [CollatzResearch.WordTrace]
  refine ⟨128170303663968992905687799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85446869109312661937125199 128170303663968992905687799)
  ·
    refine ⟨192255455495953489358531699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128170303663968992905687799 192255455495953489358531699)
    ·
      refine ⟨288383183243930234037797549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192255455495953489358531699 288383183243930234037797549)
      ·
        refine ⟨108143693716473837764174081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 288383183243930234037797549 108143693716473837764174081)
        ·
          refine ⟨81107770287355378323130561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108143693716473837764174081 81107770287355378323130561)
          ·
            refine ⟨60830827715516533742347921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81107770287355378323130561 60830827715516533742347921)
            ·
              refine ⟨45623120786637400306760941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60830827715516533742347921 45623120786637400306760941)
              ·
                refine ⟨17108670294989025115035353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45623120786637400306760941 17108670294989025115035353)
                ·
                  refine ⟨12831502721241768836276515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17108670294989025115035353 12831502721241768836276515)
                  ·
                    refine ⟨19247254081862653254414773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12831502721241768836276515 19247254081862653254414773)
                    ·
                      refine ⟨1804430070174623742601385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19247254081862653254414773 1804430070174623742601385)
                      ·
                        rfl

theorem cell23_3514115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 3, 2, 1, 5].length) (baseStart_3514115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3514115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3514115 prefixEnd_3514115 := by exact prefixLift 3514115
  have htrace : WordTrace (prefixWord ++ tailWord_3514115) baseStart_3514115 baseEnd_3514115 := by
    simpa [prefixWord, tailWord_3514115, baseEnd_3514115] using wordTrace_append hprefix tailTrace_3514115
  have hstable : (prefixWord ++ tailWord_3514115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3514115).length < 2 ^ (prefixWord ++ tailWord_3514115).sum := by decide
  have hdescent : baseEnd_3514115 < baseStart_3514115 := by decide
  rcases family_descends (prefixWord ++ tailWord_3514115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3514116 : List Nat := [2, 3, 2, 2, 1, 3, 1, 3, 1, 3, 2]
def baseStart_3514116 : Nat := 118140960795 + 3514116 * 2 ^ 59
def prefixEnd_3514116 : Nat := 4983230072969 + 3 ^ 40 * 3514116 * 2
def baseEnd_3514116 : Nat := 1804430583655278238688881

theorem tailTrace_3514116 : CollatzResearch.WordTrace tailWord_3514116 prefixEnd_3514116 1804430583655278238688881 := by
  unfold tailWord_3514116
  simp only [CollatzResearch.WordTrace]
  refine ⟨64085170068482685038237101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85446893424643580050982801 64085170068482685038237101)
  ·
    refine ⟨24031938775681006889338913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64085170068482685038237101 24031938775681006889338913)
    ·
      refine ⟨18023954081760755167004185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24031938775681006889338913 18023954081760755167004185)
      ·
        refine ⟨13517965561320566375253139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18023954081760755167004185 13517965561320566375253139)
        ·
          refine ⟨20276948341980849562879709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13517965561320566375253139 20276948341980849562879709)
          ·
            refine ⟨7603855628242818586079891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20276948341980849562879709 7603855628242818586079891)
            ·
              refine ⟨11405783442364227879119837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7603855628242818586079891 11405783442364227879119837)
              ·
                refine ⟨4277168790886585454669939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11405783442364227879119837 4277168790886585454669939)
                ·
                  refine ⟨6415753186329878182004909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4277168790886585454669939 6415753186329878182004909)
                  ·
                    refine ⟨2405907444873704318251841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6415753186329878182004909 2405907444873704318251841)
                    ·
                      refine ⟨1804430583655278238688881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2405907444873704318251841 1804430583655278238688881)
                      ·
                        rfl

theorem cell23_3514116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 3, 1, 3, 2].length) (baseStart_3514116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3514116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3514116 prefixEnd_3514116 := by exact prefixLift 3514116
  have htrace : WordTrace (prefixWord ++ tailWord_3514116) baseStart_3514116 baseEnd_3514116 := by
    simpa [prefixWord, tailWord_3514116, baseEnd_3514116] using wordTrace_append hprefix tailTrace_3514116
  have hstable : (prefixWord ++ tailWord_3514116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3514116).length < 2 ^ (prefixWord ++ tailWord_3514116).sum := by decide
  have hdescent : baseEnd_3514116 < baseStart_3514116 := by decide
  rcases family_descends (prefixWord ++ tailWord_3514116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3514152 : List Nat := [2, 1, 5, 1, 1, 2, 2, 2, 7]
def baseStart_3514152 : Nat := 118140960795 + 3514152 * 2 ^ 59
def prefixEnd_3514152 : Nat := 4983230072969 + 3 ^ 40 * 3514152 * 2
def baseEnd_3514152 : Nat := 200494340995426677537635

theorem tailTrace_3514152 : CollatzResearch.WordTrace tailWord_3514152 prefixEnd_3514152 200494340995426677537635 := by
  unfold tailWord_3514152
  simp only [CollatzResearch.WordTrace]
  refine ⟨64085826582417474112392355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85447768776556632149856473 64085826582417474112392355)
  ·
    refine ⟨96128739873626211168588533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64085826582417474112392355 96128739873626211168588533)
    ·
      refine ⟨9012069363152457297055175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 96128739873626211168588533 9012069363152457297055175)
      ·
        refine ⟨13518104044728685945582763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9012069363152457297055175 13518104044728685945582763)
        ·
          refine ⟨20277156067093028918374145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13518104044728685945582763 20277156067093028918374145)
          ·
            refine ⟨15207867050319771688780609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20277156067093028918374145 15207867050319771688780609)
            ·
              refine ⟨11405900287739828766585457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15207867050319771688780609 11405900287739828766585457)
              ·
                refine ⟨8554425215804871574939093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11405900287739828766585457 8554425215804871574939093)
                ·
                  refine ⟨200494340995426677537635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8554425215804871574939093 200494340995426677537635)
                  ·
                    rfl

theorem cell23_3514152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 2, 7].length) (baseStart_3514152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3514152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3514152 prefixEnd_3514152 := by exact prefixLift 3514152
  have htrace : WordTrace (prefixWord ++ tailWord_3514152) baseStart_3514152 baseEnd_3514152 := by
    simpa [prefixWord, tailWord_3514152, baseEnd_3514152] using wordTrace_append hprefix tailTrace_3514152
  have hstable : (prefixWord ++ tailWord_3514152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3514152).length < 2 ^ (prefixWord ++ tailWord_3514152).sum := by decide
  have hdescent : baseEnd_3514152 < baseStart_3514152 := by decide
  rcases family_descends (prefixWord ++ tailWord_3514152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3514202 : List Nat := [3, 1, 1, 2, 1, 3, 1, 2, 4, 1, 4]
def baseStart_3514202 : Nat := 118140960795 + 3514202 * 2 ^ 59
def prefixEnd_3514202 : Nat := 4983230072969 + 3 ^ 40 * 3514202 * 2
def baseEnd_3514202 : Nat := 1804474742991564902213485

theorem tailTrace_3514202 : CollatzResearch.WordTrace tailWord_3514202 prefixEnd_3514202 1804474742991564902213485 := by
  unfold tailWord_3514202
  simp only [CollatzResearch.WordTrace]
  refine ⟨32043369203663451691026215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85448984543102537842736573 32043369203663451691026215)
  ·
    refine ⟨48065053805495177536539323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32043369203663451691026215 48065053805495177536539323)
    ·
      refine ⟨72097580708242766304808985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48065053805495177536539323 72097580708242766304808985)
      ·
        refine ⟨54073185531182074728606739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72097580708242766304808985 54073185531182074728606739)
        ·
          refine ⟨81109778296773112092910109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54073185531182074728606739 81109778296773112092910109)
          ·
            refine ⟨30416166861289917034841291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81109778296773112092910109 30416166861289917034841291)
            ·
              refine ⟨45624250291934875552261937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30416166861289917034841291 45624250291934875552261937)
              ·
                refine ⟨34218187718951156664196453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45624250291934875552261937 34218187718951156664196453)
                ·
                  refine ⟨6415910197303341874536835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34218187718951156664196453 6415910197303341874536835)
                  ·
                    refine ⟨9623865295955012811805253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6415910197303341874536835 9623865295955012811805253)
                    ·
                      refine ⟨1804474742991564902213485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9623865295955012811805253 1804474742991564902213485)
                      ·
                        rfl

theorem cell23_3514202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 2, 4, 1, 4].length) (baseStart_3514202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3514202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3514202 prefixEnd_3514202 := by exact prefixLift 3514202
  have htrace : WordTrace (prefixWord ++ tailWord_3514202) baseStart_3514202 baseEnd_3514202 := by
    simpa [prefixWord, tailWord_3514202, baseEnd_3514202] using wordTrace_append hprefix tailTrace_3514202
  have hstable : (prefixWord ++ tailWord_3514202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3514202).length < 2 ^ (prefixWord ++ tailWord_3514202).sum := by decide
  have hdescent : baseEnd_3514202 < baseStart_3514202 := by decide
  rcases family_descends (prefixWord ++ tailWord_3514202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3514252 : List Nat := [2, 2, 1, 2, 1, 2, 1, 2, 2, 5, 3]
def baseStart_3514252 : Nat := 118140960795 + 3514252 * 2 ^ 59
def prefixEnd_3514252 : Nat := 4983230072969 + 3 ^ 40 * 3514252 * 2
def baseEnd_3514252 : Nat := 1804500417024289706588255

theorem tailTrace_3514252 : CollatzResearch.WordTrace tailWord_3514252 prefixEnd_3514252 1804500417024289706588255 := by
  unfold tailWord_3514252
  simp only [CollatzResearch.WordTrace]
  refine ⟨64087650232236332651712505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85450200309648443535616673 64087650232236332651712505)
  ·
    refine ⟨48065737674177249488784379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64087650232236332651712505 48065737674177249488784379)
    ·
      refine ⟨72098606511265874233176569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48065737674177249488784379 72098606511265874233176569)
      ·
        refine ⟨54073954883449405674882427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72098606511265874233176569 54073954883449405674882427)
        ·
          refine ⟨81110932325174108512323641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54073954883449405674882427 81110932325174108512323641)
          ·
            refine ⟨60833199243880581384242731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81110932325174108512323641 60833199243880581384242731)
            ·
              refine ⟨91249798865820872076364097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60833199243880581384242731 91249798865820872076364097)
              ·
                refine ⟨68437349149365654057273073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91249798865820872076364097 68437349149365654057273073)
                ·
                  refine ⟨51328011862024240542954805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68437349149365654057273073 51328011862024240542954805)
                  ·
                    refine ⟨4812001112064772550902013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51328011862024240542954805 4812001112064772550902013)
                    ·
                      refine ⟨1804500417024289706588255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4812001112064772550902013 1804500417024289706588255)
                      ·
                        rfl

theorem cell23_3514252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 5, 3].length) (baseStart_3514252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3514252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3514252 prefixEnd_3514252 := by exact prefixLift 3514252
  have htrace : WordTrace (prefixWord ++ tailWord_3514252) baseStart_3514252 baseEnd_3514252 := by
    simpa [prefixWord, tailWord_3514252, baseEnd_3514252] using wordTrace_append hprefix tailTrace_3514252
  have hstable : (prefixWord ++ tailWord_3514252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3514252).length < 2 ^ (prefixWord ++ tailWord_3514252).sum := by decide
  have hdescent : baseEnd_3514252 < baseStart_3514252 := by decide
  rcases family_descends (prefixWord ++ tailWord_3514252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3514270 : List Nat := [4, 3, 1, 3, 1, 2, 1, 1, 2, 1, 4]
def baseStart_3514270 : Nat := 118140960795 + 3514270 * 2 ^ 59
def prefixEnd_3514270 : Nat := 4983230072969 + 3 ^ 40 * 3514270 * 2
def baseEnd_3514270 : Nat := 1804509659676070636163173

theorem tailTrace_3514270 : CollatzResearch.WordTrace tailWord_3514270 prefixEnd_3514270 1804509659676070636163173 := by
  unfold tailWord_3514270
  simp only [CollatzResearch.WordTrace]
  refine ⟨16021994622300931797197533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85450637985604969585053509 16021994622300931797197533)
  ·
    refine ⟨6008247983362849423949075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16021994622300931797197533 6008247983362849423949075)
    ·
      refine ⟨9012371975044274135923613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6008247983362849423949075 9012371975044274135923613)
      ·
        refine ⟨3379639490641602800971355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9012371975044274135923613 3379639490641602800971355)
        ·
          refine ⟨5069459235962404201457033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3379639490641602800971355 5069459235962404201457033)
          ·
            refine ⟨3802094426971803151092775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5069459235962404201457033 3802094426971803151092775)
            ·
              refine ⟨5703141640457704726639163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3802094426971803151092775 5703141640457704726639163)
              ·
                refine ⟨8554712460686557089958745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5703141640457704726639163 8554712460686557089958745)
                ·
                  refine ⟨6416034345514917817469059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8554712460686557089958745 6416034345514917817469059)
                  ·
                    refine ⟨9624051518272376726203589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6416034345514917817469059 9624051518272376726203589)
                    ·
                      refine ⟨1804509659676070636163173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9624051518272376726203589 1804509659676070636163173)
                      ·
                        rfl

theorem cell23_3514270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_3514270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3514270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3514270 prefixEnd_3514270 := by exact prefixLift 3514270
  have htrace : WordTrace (prefixWord ++ tailWord_3514270) baseStart_3514270 baseEnd_3514270 := by
    simpa [prefixWord, tailWord_3514270, baseEnd_3514270] using wordTrace_append hprefix tailTrace_3514270
  have hstable : (prefixWord ++ tailWord_3514270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3514270).length < 2 ^ (prefixWord ++ tailWord_3514270).sum := by decide
  have hdescent : baseEnd_3514270 < baseStart_3514270 := by decide
  rcases family_descends (prefixWord ++ tailWord_3514270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3514273 : List Nat := [1, 2, 3, 4, 2, 2, 1, 1, 2, 2, 3]
def baseStart_3514273 : Nat := 118140960795 + 3514273 * 2 ^ 59
def prefixEnd_3514273 : Nat := 4983230072969 + 3 ^ 40 * 3514273 * 2
def baseEnd_3514273 : Nat := 1804511200118034124425659

theorem tailTrace_3514273 : CollatzResearch.WordTrace tailWord_3514273 prefixEnd_3514273 1804511200118034124425659 := by
  unfold tailWord_3514273
  simp only [CollatzResearch.WordTrace]
  refine ⟨128176066397396585889939473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85450710931597723926626315 128176066397396585889939473)
  ·
    refine ⟨96132049798047439417454605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128176066397396585889939473 96132049798047439417454605)
    ·
      refine ⟨36049518674267789781545477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96132049798047439417454605 36049518674267789781545477)
      ·
        refine ⟨6759284751425210584039777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36049518674267789781545477 6759284751425210584039777)
        ·
          refine ⟨5069463563568907938029833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6759284751425210584039777 5069463563568907938029833)
          ·
            refine ⟨3802097672676680953522375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5069463563568907938029833 3802097672676680953522375)
            ·
              refine ⟨5703146509015021430283563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3802097672676680953522375 5703146509015021430283563)
              ·
                refine ⟨8554719763522532145425345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5703146509015021430283563 8554719763522532145425345)
                ·
                  refine ⟨6416039822641899109069009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8554719763522532145425345 6416039822641899109069009)
                  ·
                    refine ⟨4812029866981424331801757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6416039822641899109069009 4812029866981424331801757)
                    ·
                      refine ⟨1804511200118034124425659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4812029866981424331801757 1804511200118034124425659)
                      ·
                        rfl

theorem cell23_3514273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_3514273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3514273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3514273 prefixEnd_3514273 := by exact prefixLift 3514273
  have htrace : WordTrace (prefixWord ++ tailWord_3514273) baseStart_3514273 baseEnd_3514273 := by
    simpa [prefixWord, tailWord_3514273, baseEnd_3514273] using wordTrace_append hprefix tailTrace_3514273
  have hstable : (prefixWord ++ tailWord_3514273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3514273).length < 2 ^ (prefixWord ++ tailWord_3514273).sum := by decide
  have hdescent : baseEnd_3514273 < baseStart_3514273 := by decide
  rcases family_descends (prefixWord ++ tailWord_3514273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3514346 : List Nat := [3, 1, 3, 1, 2, 1, 1, 5, 1, 2, 3]
def baseStart_3514346 : Nat := 118140960795 + 3514346 * 2 ^ 59
def prefixEnd_3514346 : Nat := 4983230072969 + 3 ^ 40 * 3514346 * 2
def baseEnd_3514346 : Nat := 1804548684205812338812823

theorem tailTrace_3514346 : CollatzResearch.WordTrace tailWord_3514346 prefixEnd_3514346 1804548684205812338812823 := by
  unfold tailWord_3514346
  simp only [CollatzResearch.WordTrace]
  refine ⟨32044682231533029839336723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85452485950754746238231261 32044682231533029839336723)
  ·
    refine ⟨48067023347299544759005085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32044682231533029839336723 48067023347299544759005085)
    ·
      refine ⟨18025133755237329284626907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48067023347299544759005085 18025133755237329284626907)
      ·
        refine ⟨27037700632855993926940361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18025133755237329284626907 27037700632855993926940361)
        ·
          refine ⟨20278275474641995445205271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27037700632855993926940361 20278275474641995445205271)
          ·
            refine ⟨30417413211962993167807907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20278275474641995445205271 30417413211962993167807907)
            ·
              refine ⟨45626119817944489751711861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30417413211962993167807907 45626119817944489751711861)
              ·
                refine ⟨4277448732932295914222987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45626119817944489751711861 4277448732932295914222987)
                ·
                  refine ⟨6416173099398443871334481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4277448732932295914222987 6416173099398443871334481)
                  ·
                    refine ⟨4812129824548832903500861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6416173099398443871334481 4812129824548832903500861)
                    ·
                      refine ⟨1804548684205812338812823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4812129824548832903500861 1804548684205812338812823)
                      ·
                        rfl

theorem cell23_3514346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 5, 1, 2, 3].length) (baseStart_3514346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3514346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3514346 prefixEnd_3514346 := by exact prefixLift 3514346
  have htrace : WordTrace (prefixWord ++ tailWord_3514346) baseStart_3514346 baseEnd_3514346 := by
    simpa [prefixWord, tailWord_3514346, baseEnd_3514346] using wordTrace_append hprefix tailTrace_3514346
  have hstable : (prefixWord ++ tailWord_3514346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3514346).length < 2 ^ (prefixWord ++ tailWord_3514346).sum := by decide
  have hdescent : baseEnd_3514346 < baseStart_3514346 := by decide
  rcases family_descends (prefixWord ++ tailWord_3514346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3514366 : List Nat := [4, 2, 2, 2, 1, 2, 2, 8]
def baseStart_3514366 : Nat := 118140960795 + 3514366 * 2 ^ 59
def prefixEnd_3514366 : Nat := 4983230072969 + 3 ^ 40 * 3514366 * 2
def baseEnd_3514366 : Nat := 66835516808107491131953

theorem tailTrace_3514366 : CollatzResearch.WordTrace tailWord_3514366 prefixEnd_3514366 66835516808107491131953 := by
  unfold tailWord_3514366
  simp only [CollatzResearch.WordTrace]
  refine ⟨16022432298257457846634369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85452972257373108515383301 16022432298257457846634369)
  ·
    refine ⟨12016824223693093384975777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16022432298257457846634369 12016824223693093384975777)
    ·
      refine ⟨9012618167769820038731833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12016824223693093384975777 9012618167769820038731833)
      ·
        refine ⟨6759463625827365029048875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9012618167769820038731833 6759463625827365029048875)
        ·
          refine ⟨10139195438741047543573313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6759463625827365029048875 10139195438741047543573313)
          ·
            refine ⟨7604396579055785657679985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10139195438741047543573313 7604396579055785657679985)
            ·
              refine ⟨5703297434291839243259989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7604396579055785657679985 5703297434291839243259989)
              ·
                refine ⟨66835516808107491131953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5703297434291839243259989 66835516808107491131953)
                ·
                  rfl

theorem cell23_3514366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 2, 8].length) (baseStart_3514366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3514366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3514366 prefixEnd_3514366 := by exact prefixLift 3514366
  have htrace : WordTrace (prefixWord ++ tailWord_3514366) baseStart_3514366 baseEnd_3514366 := by
    simpa [prefixWord, tailWord_3514366, baseEnd_3514366] using wordTrace_append hprefix tailTrace_3514366
  have hstable : (prefixWord ++ tailWord_3514366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3514366).length < 2 ^ (prefixWord ++ tailWord_3514366).sum := by decide
  have hdescent : baseEnd_3514366 < baseStart_3514366 := by decide
  rcases family_descends (prefixWord ++ tailWord_3514366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3514374 : List Nat := [6, 2, 1, 2, 1, 2, 1, 2, 1, 5]
def baseStart_3514374 : Nat := 118140960795 + 3514374 * 2 ^ 59
def prefixEnd_3514374 : Nat := 4983230072969 + 3 ^ 40 * 3514374 * 2
def baseEnd_3514374 : Nat := 601521020554712743087565

theorem tailTrace_3514374 : CollatzResearch.WordTrace tailWord_3514374 prefixEnd_3514374 601521020554712743087565 := by
  unfold tailWord_3514374
  simp only [CollatzResearch.WordTrace]
  refine ⟨4005617192813458754355193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 85453166780020453426244117 4005617192813458754355193)
  ·
    refine ⟨3004212894610094065766395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4005617192813458754355193 3004212894610094065766395)
    ·
      refine ⟨4506319341915141098649593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3004212894610094065766395 4506319341915141098649593)
      ·
        refine ⟨3379739506436355823987195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4506319341915141098649593 3379739506436355823987195)
        ·
          refine ⟨5069609259654533735980793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3379739506436355823987195 5069609259654533735980793)
          ·
            refine ⟨3802206944740900301985595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5069609259654533735980793 3802206944740900301985595)
            ·
              refine ⟨5703310417111350452978393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3802206944740900301985595 5703310417111350452978393)
              ·
                refine ⟨4277482812833512839733795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5703310417111350452978393 4277482812833512839733795)
                ·
                  refine ⟨6416224219250269259600693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4277482812833512839733795 6416224219250269259600693)
                  ·
                    refine ⟨601521020554712743087565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6416224219250269259600693 601521020554712743087565)
                    ·
                      rfl

theorem cell23_3514374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_3514374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3514374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3514374 prefixEnd_3514374 := by exact prefixLift 3514374
  have htrace : WordTrace (prefixWord ++ tailWord_3514374) baseStart_3514374 baseEnd_3514374 := by
    simpa [prefixWord, tailWord_3514374, baseEnd_3514374] using wordTrace_append hprefix tailTrace_3514374
  have hstable : (prefixWord ++ tailWord_3514374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3514374).length < 2 ^ (prefixWord ++ tailWord_3514374).sum := by decide
  have hdescent : baseEnd_3514374 < baseStart_3514374 := by decide
  rcases family_descends (prefixWord ++ tailWord_3514374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3514410 : List Nat := [3, 1, 4, 1, 2, 2, 2, 2, 2, 1, 3]
def baseStart_3514410 : Nat := 118140960795 + 3514410 * 2 ^ 59
def prefixEnd_3514410 : Nat := 4983230072969 + 3 ^ 40 * 3514410 * 2
def baseEnd_3514410 : Nat := 1804581546967700088412529

theorem tailTrace_3514410 : CollatzResearch.WordTrace tailWord_3514410 prefixEnd_3514410 1804581546967700088412529 := by
  unfold tailWord_3514410
  simp only [CollatzResearch.WordTrace]
  refine ⟨32045265799475064571919171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85454042131933505525117789 32045265799475064571919171)
  ·
    refine ⟨48067898699212596857878757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32045265799475064571919171 48067898699212596857878757)
    ·
      refine ⟨9012731006102361910852267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48067898699212596857878757 9012731006102361910852267)
      ·
        refine ⟨13519096509153542866278401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9012731006102361910852267 13519096509153542866278401)
        ·
          refine ⟨10139322381865157149708801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13519096509153542866278401 10139322381865157149708801)
          ·
            refine ⟨7604491786398867862281601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10139322381865157149708801 7604491786398867862281601)
            ·
              refine ⟨5703368839799150896711201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7604491786398867862281601 5703368839799150896711201)
              ·
                refine ⟨4277526629849363172533401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5703368839799150896711201 4277526629849363172533401)
                ·
                  refine ⟨3208144972387022379400051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4277526629849363172533401 3208144972387022379400051)
                  ·
                    refine ⟨4812217458580533569100077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3208144972387022379400051 4812217458580533569100077)
                    ·
                      refine ⟨1804581546967700088412529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4812217458580533569100077 1804581546967700088412529)
                      ·
                        rfl

theorem cell23_3514410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 2, 2, 2, 1, 3].length) (baseStart_3514410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3514410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3514410 prefixEnd_3514410 := by exact prefixLift 3514410
  have htrace : WordTrace (prefixWord ++ tailWord_3514410) baseStart_3514410 baseEnd_3514410 := by
    simpa [prefixWord, tailWord_3514410, baseEnd_3514410] using wordTrace_append hprefix tailTrace_3514410
  have hstable : (prefixWord ++ tailWord_3514410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3514410).length < 2 ^ (prefixWord ++ tailWord_3514410).sum := by decide
  have hdescent : baseEnd_3514410 < baseStart_3514410 := by decide
  rcases family_descends (prefixWord ++ tailWord_3514410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3514419 : List Nat := [1, 1, 1, 2, 4, 1, 3, 1, 2, 4, 3]
def baseStart_3514419 : Nat := 118140960795 + 3514419 * 2 ^ 59
def prefixEnd_3514419 : Nat := 4983230072969 + 3 ^ 40 * 3514419 * 2
def baseEnd_3514419 : Nat := 1804586168293590553199987

theorem tailTrace_3514419 : CollatzResearch.WordTrace tailWord_3514419 prefixEnd_3514419 1804586168293590553199987 := by
  unfold tailWord_3514419
  simp only [CollatzResearch.WordTrace]
  refine ⟨128181391454867652824754311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85454260969911768549836207 128181391454867652824754311)
  ·
    refine ⟨192272087182301479237131467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128181391454867652824754311 192272087182301479237131467)
    ·
      refine ⟨288408130773452218855697201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192272087182301479237131467 288408130773452218855697201)
      ·
        refine ⟨216306098080089164141772901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 288408130773452218855697201 216306098080089164141772901)
        ·
          refine ⟨40557393390016718276582419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 216306098080089164141772901 40557393390016718276582419)
          ·
            refine ⟨60836090085025077414873629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40557393390016718276582419 60836090085025077414873629)
            ·
              refine ⟨22813533781884404030577611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60836090085025077414873629 22813533781884404030577611)
              ·
                refine ⟨34220300672826606045866417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22813533781884404030577611 34220300672826606045866417)
                ·
                  refine ⟨25665225504619954534399813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34220300672826606045866417 25665225504619954534399813)
                  ·
                    refine ⟨4812229782116241475199965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25665225504619954534399813 4812229782116241475199965)
                    ·
                      refine ⟨1804586168293590553199987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4812229782116241475199965 1804586168293590553199987)
                      ·
                        rfl

theorem cell23_3514419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 1, 2, 4, 3].length) (baseStart_3514419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3514419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3514419 prefixEnd_3514419 := by exact prefixLift 3514419
  have htrace : WordTrace (prefixWord ++ tailWord_3514419) baseStart_3514419 baseEnd_3514419 := by
    simpa [prefixWord, tailWord_3514419, baseEnd_3514419] using wordTrace_append hprefix tailTrace_3514419
  have hstable : (prefixWord ++ tailWord_3514419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3514419).length < 2 ^ (prefixWord ++ tailWord_3514419).sum := by decide
  have hdescent : baseEnd_3514419 < baseStart_3514419 := by decide
  rcases family_descends (prefixWord ++ tailWord_3514419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3514433 : List Nat := [1, 2, 5, 1, 2, 1, 1, 3, 1, 4, 2]
def baseStart_3514433 : Nat := 118140960795 + 3514433 * 2 ^ 59
def prefixEnd_3514433 : Nat := 4983230072969 + 3 ^ 40 * 3514433 * 2
def baseEnd_3514433 : Nat := 1804593357022753498424923

theorem tailTrace_3514433 : CollatzResearch.WordTrace tailWord_3514433 prefixEnd_3514433 1804593357022753498424923 := by
  unfold tailWord_3514433
  simp only [CollatzResearch.WordTrace]
  refine ⟨128181902076816933215763953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85454601384544622143842635 128181902076816933215763953)
  ·
    refine ⟨96136426557612699911822965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128181902076816933215763953 96136426557612699911822965)
    ·
      refine ⟨9012789989776190616733403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 96136426557612699911822965 9012789989776190616733403)
      ·
        refine ⟨13519184984664285925100105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9012789989776190616733403 13519184984664285925100105)
        ·
          refine ⟨10139388738498214443825079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13519184984664285925100105 10139388738498214443825079)
          ·
            refine ⟨15209083107747321665737619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10139388738498214443825079 15209083107747321665737619)
            ·
              refine ⟨22813624661620982498606429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15209083107747321665737619 22813624661620982498606429)
              ·
                refine ⟨8555109248107868436977411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22813624661620982498606429 8555109248107868436977411)
                ·
                  refine ⟨12832663872161802655466117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8555109248107868436977411 12832663872161802655466117)
                  ·
                    refine ⟨2406124476030337997899897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12832663872161802655466117 2406124476030337997899897)
                    ·
                      refine ⟨1804593357022753498424923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2406124476030337997899897 1804593357022753498424923)
                      ·
                        rfl

theorem cell23_3514433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 3, 1, 4, 2].length) (baseStart_3514433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3514433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3514433 prefixEnd_3514433 := by exact prefixLift 3514433
  have htrace : WordTrace (prefixWord ++ tailWord_3514433) baseStart_3514433 baseEnd_3514433 := by
    simpa [prefixWord, tailWord_3514433, baseEnd_3514433] using wordTrace_append hprefix tailTrace_3514433
  have hstable : (prefixWord ++ tailWord_3514433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3514433).length < 2 ^ (prefixWord ++ tailWord_3514433).sum := by decide
  have hdescent : baseEnd_3514433 < baseStart_3514433 := by decide
  rcases family_descends (prefixWord ++ tailWord_3514433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3514439 : List Nat := [1, 1, 4, 1, 3, 1, 3, 2, 7]
def baseStart_3514439 : Nat := 118140960795 + 3514439 * 2 ^ 59
def prefixEnd_3514439 : Nat := 4983230072969 + 3 ^ 40 * 3514439 * 2
def baseEnd_3514439 : Nat := 200510715322964497216655

theorem tailTrace_3514439 : CollatzResearch.WordTrace tailWord_3514439 prefixEnd_3514439 200510715322964497216655 := by
  unfold tailWord_3514439
  simp only [CollatzResearch.WordTrace]
  refine ⟨128182120914795196240482371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85454747276530130826988247 128182120914795196240482371)
  ·
    refine ⟨192273181372192794360723557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128182120914795196240482371 192273181372192794360723557)
    ·
      refine ⟨36051221507286148942635667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 192273181372192794360723557 36051221507286148942635667)
      ·
        refine ⟨54076832260929223413953501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36051221507286148942635667 54076832260929223413953501)
        ·
          refine ⟨20278812097848458780232563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54076832260929223413953501 20278812097848458780232563)
          ·
            refine ⟨30418218146772688170348845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20278812097848458780232563 30418218146772688170348845)
            ·
              refine ⟨11406831805039758063880817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30418218146772688170348845 11406831805039758063880817)
              ·
                refine ⟨8555123853779818547910613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11406831805039758063880817 8555123853779818547910613)
                ·
                  refine ⟨200510715322964497216655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8555123853779818547910613 200510715322964497216655)
                  ·
                    rfl

theorem cell23_3514439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 2, 7].length) (baseStart_3514439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3514439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3514439 prefixEnd_3514439 := by exact prefixLift 3514439
  have htrace : WordTrace (prefixWord ++ tailWord_3514439) baseStart_3514439 baseEnd_3514439 := by
    simpa [prefixWord, tailWord_3514439, baseEnd_3514439] using wordTrace_append hprefix tailTrace_3514439
  have hstable : (prefixWord ++ tailWord_3514439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3514439).length < 2 ^ (prefixWord ++ tailWord_3514439).sum := by decide
  have hdescent : baseEnd_3514439 < baseStart_3514439 := by decide
  rcases family_descends (prefixWord ++ tailWord_3514439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3514449 : List Nat := [1, 2, 2, 1, 3, 1, 1, 1, 3, 5, 3]
def baseStart_3514449 : Nat := 118140960795 + 3514449 * 2 ^ 59
def prefixEnd_3514449 : Nat := 4983230072969 + 3 ^ 40 * 3514449 * 2
def baseEnd_3514449 : Nat := 1804601572713225435824849

theorem tailTrace_3514449 : CollatzResearch.WordTrace tailWord_3514449 prefixEnd_3514449 1804601572713225435824849 := by
  unfold tailWord_3514449
  simp only [CollatzResearch.WordTrace]
  refine ⟨128182485644758967948346401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85454990429839311965564267 128182485644758967948346401)
  ·
    refine ⟨96136864233569225961259801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128182485644758967948346401 96136864233569225961259801)
    ·
      refine ⟨72102648175176919470944851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96136864233569225961259801 72102648175176919470944851)
      ·
        refine ⟨108153972262765379206417277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72102648175176919470944851 108153972262765379206417277)
        ·
          refine ⟨40557739598537017202406479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108153972262765379206417277 40557739598537017202406479)
          ·
            refine ⟨60836609397805525803609719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40557739598537017202406479 60836609397805525803609719)
            ·
              refine ⟨91254914096708288705414579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60836609397805525803609719 91254914096708288705414579)
              ·
                refine ⟨136882371145062433058121869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91254914096708288705414579 136882371145062433058121869)
                ·
                  refine ⟨51330889179398412396795701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 136882371145062433058121869 51330889179398412396795701)
                  ·
                    refine ⟨4812270860568601162199597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51330889179398412396795701 4812270860568601162199597)
                    ·
                      refine ⟨1804601572713225435824849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4812270860568601162199597 1804601572713225435824849)
                      ·
                        rfl

theorem cell23_3514449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 3, 5, 3].length) (baseStart_3514449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3514449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3514449 prefixEnd_3514449 := by exact prefixLift 3514449
  have htrace : WordTrace (prefixWord ++ tailWord_3514449) baseStart_3514449 baseEnd_3514449 := by
    simpa [prefixWord, tailWord_3514449, baseEnd_3514449] using wordTrace_append hprefix tailTrace_3514449
  have hstable : (prefixWord ++ tailWord_3514449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3514449).length < 2 ^ (prefixWord ++ tailWord_3514449).sum := by decide
  have hdescent : baseEnd_3514449 < baseStart_3514449 := by decide
  rcases family_descends (prefixWord ++ tailWord_3514449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3514454 : List Nat := [5, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2]
def baseStart_3514454 : Nat := 118140960795 + 3514454 * 2 ^ 59
def prefixEnd_3514454 : Nat := 4983230072969 + 3 ^ 40 * 3514454 * 2
def baseEnd_3514454 : Nat := 1804604140116497916262327

theorem tailTrace_3514454 : CollatzResearch.WordTrace tailWord_3514454 prefixEnd_3514454 1804604140116497916262327 := by
  unfold tailWord_3514454
  simp only [CollatzResearch.WordTrace]
  refine ⟨8011416750608803362642401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 85455112006493902534852277 8011416750608803362642401)
  ·
    refine ⟨6008562562956602521981801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8011416750608803362642401 6008562562956602521981801)
    ·
      refine ⟨4506421922217451891486351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6008562562956602521981801 4506421922217451891486351)
      ·
        refine ⟨6759632883326177837229527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4506421922217451891486351 6759632883326177837229527)
        ·
          refine ⟨10139449324989266755844291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6759632883326177837229527 10139449324989266755844291)
          ·
            refine ⟨15209173987483900133766437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10139449324989266755844291 15209173987483900133766437)
            ·
              refine ⟨2851720122653231275081207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15209173987483900133766437 2851720122653231275081207)
              ·
                refine ⟨4277580183979846912621811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2851720122653231275081207 4277580183979846912621811)
                ·
                  refine ⟨6416370275969770368932717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4277580183979846912621811 6416370275969770368932717)
                  ·
                    refine ⟨2406138853488663888349769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6416370275969770368932717 2406138853488663888349769)
                    ·
                      refine ⟨1804604140116497916262327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2406138853488663888349769 1804604140116497916262327)
                      ·
                        rfl

theorem cell23_3514454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2].length) (baseStart_3514454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3514454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3514454 prefixEnd_3514454 := by exact prefixLift 3514454
  have htrace : WordTrace (prefixWord ++ tailWord_3514454) baseStart_3514454 baseEnd_3514454 := by
    simpa [prefixWord, tailWord_3514454, baseEnd_3514454] using wordTrace_append hprefix tailTrace_3514454
  have hstable : (prefixWord ++ tailWord_3514454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3514454).length < 2 ^ (prefixWord ++ tailWord_3514454).sum := by decide
  have hdescent : baseEnd_3514454 < baseStart_3514454 := by decide
  rcases family_descends (prefixWord ++ tailWord_3514454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3514456 : List Nat := [2, 1, 2, 2, 1, 4, 1, 5, 5]
def baseStart_3514456 : Nat := 118140960795 + 3514456 * 2 ^ 59
def prefixEnd_3514456 : Nat := 4983230072969 + 3 ^ 40 * 3514456 * 2
def baseEnd_3514456 : Nat := 200511685230867434270813

theorem tailTrace_3514456 : CollatzResearch.WordTrace tailWord_3514456 prefixEnd_3514456 200511685230867434270813 := by
  unfold tailWord_3514456
  simp only [CollatzResearch.WordTrace]
  refine ⟨64091370477866804071925611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85455160637155738762567481 64091370477866804071925611)
  ·
    refine ⟨96137055716800206107888417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64091370477866804071925611 96137055716800206107888417)
    ·
      refine ⟨72102791787600154580916313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96137055716800206107888417 72102791787600154580916313)
      ·
        refine ⟨54077093840700115935687235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72102791787600154580916313 54077093840700115935687235)
        ·
          refine ⟨81115640761050173903530853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54077093840700115935687235 81115640761050173903530853)
          ·
            refine ⟨15209182642696907606912035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81115640761050173903530853 15209182642696907606912035)
            ·
              refine ⟨22813773964045361410368053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15209182642696907606912035 22813773964045361410368053)
              ·
                refine ⟨2138791309129252632222005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22813773964045361410368053 2138791309129252632222005)
                ·
                  refine ⟨200511685230867434270813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2138791309129252632222005 200511685230867434270813)
                  ·
                    rfl

theorem cell23_3514456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 5, 5].length) (baseStart_3514456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3514456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3514456 prefixEnd_3514456 := by exact prefixLift 3514456
  have htrace : WordTrace (prefixWord ++ tailWord_3514456) baseStart_3514456 baseEnd_3514456 := by
    simpa [prefixWord, tailWord_3514456, baseEnd_3514456] using wordTrace_append hprefix tailTrace_3514456
  have hstable : (prefixWord ++ tailWord_3514456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3514456).length < 2 ^ (prefixWord ++ tailWord_3514456).sum := by decide
  have hdescent : baseEnd_3514456 < baseStart_3514456 := by decide
  rcases family_descends (prefixWord ++ tailWord_3514456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3514486 : List Nat := [5, 1, 1, 2, 1, 2, 1, 2, 1, 7]
def baseStart_3514486 : Nat := 118140960795 + 3514486 * 2 ^ 59
def prefixEnd_3514486 : Nat := 4983230072969 + 3 ^ 40 * 3514486 * 2
def baseEnd_3514486 : Nat := 601540190499147263687393

theorem tailTrace_3514486 : CollatzResearch.WordTrace tailWord_3514486 prefixEnd_3514486 601540190499147263687393 := by
  unfold tailWord_3514486
  simp only [CollatzResearch.WordTrace]
  refine ⟨8011489696601557704215207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 85455890097083282178295541 8011489696601557704215207)
  ·
    refine ⟨12017234544902336556322811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8011489696601557704215207 12017234544902336556322811)
    ·
      refine ⟨18025851817353504834484217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12017234544902336556322811 18025851817353504834484217)
      ·
        refine ⟨13519388863015128625863163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18025851817353504834484217 13519388863015128625863163)
        ·
          refine ⟨20279083294522692938794745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13519388863015128625863163 20279083294522692938794745)
          ·
            refine ⟨15209312470892019704096059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20279083294522692938794745 15209312470892019704096059)
            ·
              refine ⟨22813968706338029556144089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15209312470892019704096059 22813968706338029556144089)
              ·
                refine ⟨17110476529753522167108067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22813968706338029556144089 17110476529753522167108067)
                ·
                  refine ⟨25665714794630283250662101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17110476529753522167108067 25665714794630283250662101)
                  ·
                    refine ⟨601540190499147263687393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25665714794630283250662101 601540190499147263687393)
                    ·
                      rfl

theorem cell23_3514486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 2, 1, 7].length) (baseStart_3514486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3514486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3514486 prefixEnd_3514486 := by exact prefixLift 3514486
  have htrace : WordTrace (prefixWord ++ tailWord_3514486) baseStart_3514486 baseEnd_3514486 := by
    simpa [prefixWord, tailWord_3514486, baseEnd_3514486] using wordTrace_append hprefix tailTrace_3514486
  have hstable : (prefixWord ++ tailWord_3514486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3514486).length < 2 ^ (prefixWord ++ tailWord_3514486).sum := by decide
  have hdescent : baseEnd_3514486 < baseStart_3514486 := by decide
  rcases family_descends (prefixWord ++ tailWord_3514486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3514506 : List Nat := [3, 1, 2, 3, 1, 2, 2, 1, 1, 3, 4]
def baseStart_3514506 : Nat := 118140960795 + 3514506 * 2 ^ 59
def prefixEnd_3514506 : Nat := 4983230072969 + 3 ^ 40 * 3514506 * 2
def baseEnd_3514506 : Nat := 1804630841110531712812087

theorem tailTrace_3514506 : CollatzResearch.WordTrace tailWord_3514506 prefixEnd_3514506 1804630841110531712812087 := by
  unfold tailWord_3514506
  simp only [CollatzResearch.WordTrace]
  refine ⟨32046141151388116670792843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85456376403701644455447581 32046141151388116670792843)
  ·
    refine ⟨48069211727082175006189265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32046141151388116670792843 48069211727082175006189265)
    ·
      refine ⟨36051908795311631254641949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48069211727082175006189265 36051908795311631254641949)
      ·
        refine ⟨13519465798241861720490731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36051908795311631254641949 13519465798241861720490731)
        ·
          refine ⟨20279198697362792580736097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13519465798241861720490731 20279198697362792580736097)
          ·
            refine ⟨15209399023022094435552073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20279198697362792580736097 15209399023022094435552073)
            ·
              refine ⟨11407049267266570826664055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15209399023022094435552073 11407049267266570826664055)
              ·
                refine ⟨17110573900899856239996083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11407049267266570826664055 17110573900899856239996083)
                ·
                  refine ⟨25665860851349784359994125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17110573900899856239996083 25665860851349784359994125)
                  ·
                    refine ⟨9624697819256169134997797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25665860851349784359994125 9624697819256169134997797)
                    ·
                      refine ⟨1804630841110531712812087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9624697819256169134997797 1804630841110531712812087)
                      ·
                        rfl

theorem cell23_3514506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_3514506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3514506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3514506 prefixEnd_3514506 := by exact prefixLift 3514506
  have htrace : WordTrace (prefixWord ++ tailWord_3514506) baseStart_3514506 baseEnd_3514506 := by
    simpa [prefixWord, tailWord_3514506, baseEnd_3514506] using wordTrace_append hprefix tailTrace_3514506
  have hstable : (prefixWord ++ tailWord_3514506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3514506).length < 2 ^ (prefixWord ++ tailWord_3514506).sum := by decide
  have hdescent : baseEnd_3514506 < baseStart_3514506 := by decide
  rcases family_descends (prefixWord ++ tailWord_3514506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3514546 : List Nat := [3, 2, 1, 1, 1, 3, 3, 3, 6]
def baseStart_3514546 : Nat := 118140960795 + 3514546 * 2 ^ 59
def prefixEnd_3514546 : Nat := 4983230072969 + 3 ^ 40 * 3514546 * 2
def baseEnd_3514546 : Nat := 200516820037412395145767

theorem tailTrace_3514546 : CollatzResearch.WordTrace tailWord_3514546 prefixEnd_3514546 200516820037412395145767 := by
  unfold tailWord_3514546
  simp only [CollatzResearch.WordTrace]
  refine ⟨32046505881351888378656873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85457349016938369009751661 32046505881351888378656873)
  ·
    refine ⟨24034879411013916283992655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32046505881351888378656873 24034879411013916283992655)
    ·
      refine ⟨36052319116520874425988983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24034879411013916283992655 36052319116520874425988983)
      ·
        refine ⟨54078478674781311638983475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36052319116520874425988983 54078478674781311638983475)
        ·
          refine ⟨81117718012171967458475213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54078478674781311638983475 81117718012171967458475213)
          ·
            refine ⟨30419144254564487796928205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81117718012171967458475213 30419144254564487796928205)
            ·
              refine ⟨11407179095461682923848077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30419144254564487796928205 11407179095461682923848077)
              ·
                refine ⟨4277692160798131096443029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11407179095461682923848077 4277692160798131096443029)
                ·
                  refine ⟨200516820037412395145767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4277692160798131096443029 200516820037412395145767)
                  ·
                    rfl

theorem cell23_3514546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 3, 6].length) (baseStart_3514546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3514546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3514546 prefixEnd_3514546 := by exact prefixLift 3514546
  have htrace : WordTrace (prefixWord ++ tailWord_3514546) baseStart_3514546 baseEnd_3514546 := by
    simpa [prefixWord, tailWord_3514546, baseEnd_3514546] using wordTrace_append hprefix tailTrace_3514546
  have hstable : (prefixWord ++ tailWord_3514546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3514546).length < 2 ^ (prefixWord ++ tailWord_3514546).sum := by decide
  have hdescent : baseEnd_3514546 < baseStart_3514546 := by decide
  rcases family_descends (prefixWord ++ tailWord_3514546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3514569 : List Nat := [1, 2, 1, 1, 2, 1, 1, 3, 2, 4, 5]
def baseStart_3514569 : Nat := 118140960795 + 3514569 * 2 ^ 59
def prefixEnd_3514569 : Nat := 4983230072969 + 3 ^ 40 * 3514569 * 2
def baseEnd_3514569 : Nat := 1804663190391764966324297

theorem tailTrace_3514569 : CollatzResearch.WordTrace tailWord_3514569 prefixEnd_3514569 1804663190391764966324297 := by
  unfold tailWord_3514569
  simp only [CollatzResearch.WordTrace]
  refine ⟨128186862404324228442714761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85457908269549485628476507 128186862404324228442714761)
  ·
    refine ⟨96140146803243171332036071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128186862404324228442714761 96140146803243171332036071)
    ·
      refine ⟨144210220204864756998054107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96140146803243171332036071 144210220204864756998054107)
      ·
        refine ⟨216315330307297135497081161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144210220204864756998054107 216315330307297135497081161)
        ·
          refine ⟨162236497730472851622810871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216315330307297135497081161 162236497730472851622810871)
          ·
            refine ⟨243354746595709277434216307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162236497730472851622810871 243354746595709277434216307)
            ·
              refine ⟨365032119893563916151324461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 243354746595709277434216307 365032119893563916151324461)
              ·
                refine ⟨136887044960086468556746673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 365032119893563916151324461 136887044960086468556746673)
                ·
                  refine ⟨102665283720064851417560005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 136887044960086468556746673 102665283720064851417560005)
                  ·
                    refine ⟨19249740697512159640792501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 102665283720064851417560005 19249740697512159640792501)
                    ·
                      refine ⟨1804663190391764966324297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19249740697512159640792501 1804663190391764966324297)
                      ·
                        rfl

theorem cell23_3514569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 4, 5].length) (baseStart_3514569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3514569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3514569 prefixEnd_3514569 := by exact prefixLift 3514569
  have htrace : WordTrace (prefixWord ++ tailWord_3514569) baseStart_3514569 baseEnd_3514569 := by
    simpa [prefixWord, tailWord_3514569, baseEnd_3514569] using wordTrace_append hprefix tailTrace_3514569
  have hstable : (prefixWord ++ tailWord_3514569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3514569).length < 2 ^ (prefixWord ++ tailWord_3514569).sum := by decide
  have hdescent : baseEnd_3514569 < baseStart_3514569 := by decide
  rcases family_descends (prefixWord ++ tailWord_3514569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3514647 : List Nat := [1, 1, 3, 4, 1, 3, 2, 1, 3, 2, 2]
def baseStart_3514647 : Nat := 118140960795 + 3514647 * 2 ^ 59
def prefixEnd_3514647 : Nat := 4983230072969 + 3 ^ 40 * 3514647 * 2
def baseEnd_3514647 : Nat := 1804703241882815661148939

theorem tailTrace_3514647 : CollatzResearch.WordTrace tailWord_3514647 prefixEnd_3514647 1804703241882815661148939 := by
  unfold tailWord_3514647
  simp only [CollatzResearch.WordTrace]
  refine ⟨128189707298041647764054195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85459804865361098509369463 128189707298041647764054195)
  ·
    refine ⟨192284560947062471646081293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128189707298041647764054195 192284560947062471646081293)
    ·
      refine ⟨72106710355148426867280485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192284560947062471646081293 72106710355148426867280485)
      ·
        refine ⟨13520008191590330037615091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72106710355148426867280485 13520008191590330037615091)
        ·
          refine ⟨20280012287385495056422637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13520008191590330037615091 20280012287385495056422637)
          ·
            refine ⟨7605004607769560646158489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20280012287385495056422637 7605004607769560646158489)
            ·
              refine ⟨5703753455827170484618867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7605004607769560646158489 5703753455827170484618867)
              ·
                refine ⟨8555630183740755726928301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5703753455827170484618867 8555630183740755726928301)
                ·
                  refine ⟨3208361318902783397598113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8555630183740755726928301 3208361318902783397598113)
                  ·
                    refine ⟨2406270989177087548198585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3208361318902783397598113 2406270989177087548198585)
                    ·
                      refine ⟨1804703241882815661148939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2406270989177087548198585 1804703241882815661148939)
                      ·
                        rfl

theorem cell23_3514647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 2, 1, 3, 2, 2].length) (baseStart_3514647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3514647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3514647 prefixEnd_3514647 := by exact prefixLift 3514647
  have htrace : WordTrace (prefixWord ++ tailWord_3514647) baseStart_3514647 baseEnd_3514647 := by
    simpa [prefixWord, tailWord_3514647, baseEnd_3514647] using wordTrace_append hprefix tailTrace_3514647
  have hstable : (prefixWord ++ tailWord_3514647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3514647).length < 2 ^ (prefixWord ++ tailWord_3514647).sum := by decide
  have hdescent : baseEnd_3514647 < baseStart_3514647 := by decide
  rcases family_descends (prefixWord ++ tailWord_3514647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3514660 : List Nat := [2, 3, 1, 3, 1, 4, 1, 1, 1, 2, 4]
def baseStart_3514660 : Nat := 118140960795 + 3514660 * 2 ^ 59
def prefixEnd_3514660 : Nat := 4983230072969 + 3 ^ 40 * 3514660 * 2
def baseEnd_3514660 : Nat := 1804709917131324110286379

theorem tailTrace_3514660 : CollatzResearch.WordTrace tailWord_3514660 prefixEnd_3514660 1804709917131324110286379 := by
  unfold tailWord_3514660
  simp only [CollatzResearch.WordTrace]
  refine ⟨64095090723497275492138717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85460120964663033989518289 64095090723497275492138717)
  ·
    refine ⟨24035659021311478309552019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64095090723497275492138717 24035659021311478309552019)
    ·
      refine ⟨36053488531967217464328029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24035659021311478309552019 36053488531967217464328029)
      ·
        refine ⟨13520058199487706549123011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36053488531967217464328029 13520058199487706549123011)
        ·
          refine ⟨20280087299231559823684517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13520058199487706549123011 20280087299231559823684517)
          ·
            refine ⟨3802516368605917466940847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20280087299231559823684517 3802516368605917466940847)
            ·
              refine ⟨5703774552908876200411271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3802516368605917466940847 5703774552908876200411271)
              ·
                refine ⟨8555661829363314300616907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5703774552908876200411271 8555661829363314300616907)
                ·
                  refine ⟨12833492744044971450925361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8555661829363314300616907 12833492744044971450925361)
                  ·
                    refine ⟨9625119558033728588194021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12833492744044971450925361 9625119558033728588194021)
                    ·
                      refine ⟨1804709917131324110286379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9625119558033728588194021 1804709917131324110286379)
                      ·
                        rfl

theorem cell23_3514660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 1, 1, 1, 2, 4].length) (baseStart_3514660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3514660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3514660 prefixEnd_3514660 := by exact prefixLift 3514660
  have htrace : WordTrace (prefixWord ++ tailWord_3514660) baseStart_3514660 baseEnd_3514660 := by
    simpa [prefixWord, tailWord_3514660, baseEnd_3514660] using wordTrace_append hprefix tailTrace_3514660
  have hstable : (prefixWord ++ tailWord_3514660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3514660).length < 2 ^ (prefixWord ++ tailWord_3514660).sum := by decide
  have hdescent : baseEnd_3514660 < baseStart_3514660 := by decide
  rcases family_descends (prefixWord ++ tailWord_3514660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3514670 : List Nat := [4, 1, 3, 3, 1, 1, 1, 9]
def baseStart_3514670 : Nat := 118140960795 + 3514670 * 2 ^ 59
def prefixEnd_3514670 : Nat := 4983230072969 + 3 ^ 40 * 3514670 * 2
def baseEnd_3514670 : Nat := 66841298219921076709679

theorem tailTrace_3514670 : CollatzResearch.WordTrace tailWord_3514670 prefixEnd_3514670 66841298219921076709679 := by
  unfold tailWord_3514670
  simp only [CollatzResearch.WordTrace]
  refine ⟨16023818272119790336517683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85460364117972215128094309 16023818272119790336517683)
  ·
    refine ⟨24035727408179685504776525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16023818272119790336517683 24035727408179685504776525)
    ·
      refine ⟨9013397778067382064291197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24035727408179685504776525 9013397778067382064291197)
      ·
        refine ⟨3380024166775268274109199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9013397778067382064291197 3380024166775268274109199)
        ·
          refine ⟨5070036250162902411163799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3380024166775268274109199 5070036250162902411163799)
          ·
            refine ⟨7605054375244353616745699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5070036250162902411163799 7605054375244353616745699)
            ·
              refine ⟨11407581562866530425118549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7605054375244353616745699 11407581562866530425118549)
              ·
                refine ⟨66841298219921076709679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11407581562866530425118549 66841298219921076709679)
                ·
                  rfl

theorem cell23_3514670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 9].length) (baseStart_3514670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3514670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3514670 prefixEnd_3514670 := by exact prefixLift 3514670
  have htrace : WordTrace (prefixWord ++ tailWord_3514670) baseStart_3514670 baseEnd_3514670 := by
    simpa [prefixWord, tailWord_3514670, baseEnd_3514670] using wordTrace_append hprefix tailTrace_3514670
  have hstable : (prefixWord ++ tailWord_3514670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3514670).length < 2 ^ (prefixWord ++ tailWord_3514670).sum := by decide
  have hdescent : baseEnd_3514670 < baseStart_3514670 := by decide
  rcases family_descends (prefixWord ++ tailWord_3514670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3514681 : List Nat := [1, 2, 1, 6, 1, 3, 1, 3, 1, 2, 2]
def baseStart_3514681 : Nat := 118140960795 + 3514681 * 2 ^ 59
def prefixEnd_3514681 : Nat := 4983230072969 + 3 ^ 40 * 3514681 * 2
def baseEnd_3514681 : Nat := 1804720700225068528123783

theorem tailTrace_3514681 : CollatzResearch.WordTrace tailWord_3514681 prefixEnd_3514681 1804720700225068528123783 := by
  unfold tailWord_3514681
  simp only [CollatzResearch.WordTrace]
  refine ⟨128190947379918471570791897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85460631586612314380527931 128190947379918471570791897)
  ·
    refine ⟨96143210534938853678093923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128190947379918471570791897 96143210534938853678093923)
    ·
      refine ⟨144214815802408280517140885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96143210534938853678093923 144214815802408280517140885)
      ·
        refine ⟨6760069490737888149240979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 144214815802408280517140885 6760069490737888149240979)
        ·
          refine ⟨10140104236106832223861469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6760069490737888149240979 10140104236106832223861469)
          ·
            refine ⟨3802539088540062083948051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10140104236106832223861469 3802539088540062083948051)
            ·
              refine ⟨5703808632810093125922077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3802539088540062083948051 5703808632810093125922077)
              ·
                refine ⟨2138928237303784922220779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5703808632810093125922077 2138928237303784922220779)
                ·
                  refine ⟨3208392355955677383331169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2138928237303784922220779 3208392355955677383331169)
                  ·
                    refine ⟨2406294266966758037498377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3208392355955677383331169 2406294266966758037498377)
                    ·
                      refine ⟨1804720700225068528123783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2406294266966758037498377 1804720700225068528123783)
                      ·
                        rfl

theorem cell23_3514681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 1, 3, 1, 2, 2].length) (baseStart_3514681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3514681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3514681 prefixEnd_3514681 := by exact prefixLift 3514681
  have htrace : WordTrace (prefixWord ++ tailWord_3514681) baseStart_3514681 baseEnd_3514681 := by
    simpa [prefixWord, tailWord_3514681, baseEnd_3514681] using wordTrace_append hprefix tailTrace_3514681
  have hstable : (prefixWord ++ tailWord_3514681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3514681).length < 2 ^ (prefixWord ++ tailWord_3514681).sum := by decide
  have hdescent : baseEnd_3514681 < baseStart_3514681 := by decide
  rcases family_descends (prefixWord ++ tailWord_3514681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3514696 : List Nat := [2, 1, 3, 1, 1, 2, 2, 1, 4, 6]
def baseStart_3514696 : Nat := 118140960795 + 3514696 * 2 ^ 59
def prefixEnd_3514696 : Nat := 4983230072969 + 3 ^ 40 * 3514696 * 2
def baseEnd_3514696 : Nat := 601576134144961989812071

theorem tailTrace_3514696 : CollatzResearch.WordTrace tailWord_3514696 prefixEnd_3514696 601576134144961989812071 := by
  unfold tailWord_3514696
  simp only [CollatzResearch.WordTrace]
  refine ⟨64095747237432064566293971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85460996316576086088391961 64095747237432064566293971)
  ·
    refine ⟨96143620856148096849440957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64095747237432064566293971 96143620856148096849440957)
    ·
      refine ⟨36053857821055536318540359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96143620856148096849440957 36053857821055536318540359)
      ·
        refine ⟨54080786731583304477810539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36053857821055536318540359 54080786731583304477810539)
        ·
          refine ⟨81121180097374956716715809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54080786731583304477810539 81121180097374956716715809)
          ·
            refine ⟨60840885073031217537536857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81121180097374956716715809 60840885073031217537536857)
            ·
              refine ⟨45630663804773413153152643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60840885073031217537536857 45630663804773413153152643)
              ·
                refine ⟨68445995707160119729728965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45630663804773413153152643 68445995707160119729728965)
                ·
                  refine ⟨12833624195092522449324181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68445995707160119729728965 12833624195092522449324181)
                  ·
                    refine ⟨601576134144961989812071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12833624195092522449324181 601576134144961989812071)
                    ·
                      rfl

theorem cell23_3514696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 4, 6].length) (baseStart_3514696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3514696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3514696 prefixEnd_3514696 := by exact prefixLift 3514696
  have htrace : WordTrace (prefixWord ++ tailWord_3514696) baseStart_3514696 baseEnd_3514696 := by
    simpa [prefixWord, tailWord_3514696, baseEnd_3514696] using wordTrace_append hprefix tailTrace_3514696
  have hstable : (prefixWord ++ tailWord_3514696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3514696).length < 2 ^ (prefixWord ++ tailWord_3514696).sum := by decide
  have hdescent : baseEnd_3514696 < baseStart_3514696 := by decide
  rcases family_descends (prefixWord ++ tailWord_3514696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3514703 : List Nat := [1, 1, 2, 1, 1, 2, 1, 3, 5, 4, 2]
def baseStart_3514703 : Nat := 118140960795 + 3514703 * 2 ^ 59
def prefixEnd_3514703 : Nat := 4983230072969 + 3 ^ 40 * 3514703 * 2
def baseEnd_3514703 : Nat := 1804731996799467442048681

theorem tailTrace_3514703 : CollatzResearch.WordTrace tailWord_3514703 prefixEnd_3514703 1804731996799467442048681 := by
  unfold tailWord_3514703
  simp only [CollatzResearch.WordTrace]
  refine ⟨128191749785838769328092763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85461166523892512885395175 128191749785838769328092763)
  ·
    refine ⟨192287624678758153992139145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128191749785838769328092763 192287624678758153992139145)
    ·
      refine ⟨144215718509068615494104359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192287624678758153992139145 144215718509068615494104359)
      ·
        refine ⟨216323577763602923241156539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144215718509068615494104359 216323577763602923241156539)
        ·
          refine ⟨324485366645404384861734809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216323577763602923241156539 324485366645404384861734809)
          ·
            refine ⟨243364024984053288646301107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 324485366645404384861734809 243364024984053288646301107)
            ·
              refine ⟨365046037476079932969451661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 243364024984053288646301107 365046037476079932969451661)
              ·
                refine ⟨136892264053529974863544373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 365046037476079932969451661 136892264053529974863544373)
                ·
                  refine ⟨12833649755018435143457285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 136892264053529974863544373 12833649755018435143457285)
                  ·
                    refine ⟨2406309329065956589398241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12833649755018435143457285 2406309329065956589398241)
                    ·
                      refine ⟨1804731996799467442048681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2406309329065956589398241 1804731996799467442048681)
                      ·
                        rfl

theorem cell23_3514703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 5, 4, 2].length) (baseStart_3514703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3514703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3514703 prefixEnd_3514703 := by exact prefixLift 3514703
  have htrace : WordTrace (prefixWord ++ tailWord_3514703) baseStart_3514703 baseEnd_3514703 := by
    simpa [prefixWord, tailWord_3514703, baseEnd_3514703] using wordTrace_append hprefix tailTrace_3514703
  have hstable : (prefixWord ++ tailWord_3514703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3514703).length < 2 ^ (prefixWord ++ tailWord_3514703).sum := by decide
  have hdescent : baseEnd_3514703 < baseStart_3514703 := by decide
  rcases family_descends (prefixWord ++ tailWord_3514703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3514746 : List Nat := [3, 1, 1, 1, 1, 1, 2, 1, 2, 4, 6]
def baseStart_3514746 : Nat := 118140960795 + 3514746 * 2 ^ 59
def prefixEnd_3514746 : Nat := 4983230072969 + 3 ^ 40 * 3514746 * 2
def baseEnd_3514746 : Nat := 1804754076467610773810983

theorem tailTrace_3514746 : CollatzResearch.WordTrace tailWord_3514746 prefixEnd_3514746 1804754076467610773810983 := by
  unfold tailWord_3514746
  simp only [CollatzResearch.WordTrace]
  refine ⟨32048329531170746917977023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85462212083121991781272061 32048329531170746917977023)
  ·
    refine ⟨48072494296756120376965535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32048329531170746917977023 48072494296756120376965535)
    ·
      refine ⟨72108741445134180565448303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48072494296756120376965535 72108741445134180565448303)
      ·
        refine ⟨108163112167701270848172455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72108741445134180565448303 108163112167701270848172455)
        ·
          refine ⟨162244668251551906272258683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108163112167701270848172455 162244668251551906272258683)
          ·
            refine ⟨243367002377327859408388025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162244668251551906272258683 243367002377327859408388025)
            ·
              refine ⟨182525251782995894556291019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 243367002377327859408388025 182525251782995894556291019)
              ·
                refine ⟨273787877674493841834436529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 182525251782995894556291019 273787877674493841834436529)
                ·
                  refine ⟨205340908255870381375827397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 273787877674493841834436529 205340908255870381375827397)
                  ·
                    refine ⟨38501420297975696507967637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 205340908255870381375827397 38501420297975696507967637)
                    ·
                      refine ⟨1804754076467610773810983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38501420297975696507967637 1804754076467610773810983)
                      ·
                        rfl

theorem cell23_3514746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 2, 4, 6].length) (baseStart_3514746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3514746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3514746 prefixEnd_3514746 := by exact prefixLift 3514746
  have htrace : WordTrace (prefixWord ++ tailWord_3514746) baseStart_3514746 baseEnd_3514746 := by
    simpa [prefixWord, tailWord_3514746, baseEnd_3514746] using wordTrace_append hprefix tailTrace_3514746
  have hstable : (prefixWord ++ tailWord_3514746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3514746).length < 2 ^ (prefixWord ++ tailWord_3514746).sum := by decide
  have hdescent : baseEnd_3514746 < baseStart_3514746 := by decide
  rcases family_descends (prefixWord ++ tailWord_3514746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3514760 : List Nat := [2, 1, 3, 3, 1, 1, 3, 4, 5]
def baseStart_3514760 : Nat := 118140960795 + 3514760 * 2 ^ 59
def prefixEnd_3514760 : Nat := 4983230072969 + 3 ^ 40 * 3514760 * 2
def baseEnd_3514760 : Nat := 200529029466308191003991

theorem tailTrace_3514760 : CollatzResearch.WordTrace tailWord_3514760 prefixEnd_3514760 200529029466308191003991 := by
  unfold tailWord_3514760
  simp only [CollatzResearch.WordTrace]
  refine ⟨64096914373316134031458867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85462552497754845375278489 64096914373316134031458867)
  ·
    refine ⟨96145371559974201047188301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64096914373316134031458867 96145371559974201047188301)
    ·
      refine ⟨36054514334990325392695613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96145371559974201047188301 36054514334990325392695613)
      ·
        refine ⟨13520442875621372022260855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36054514334990325392695613 13520442875621372022260855)
        ·
          refine ⟨20280664313432058033391283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13520442875621372022260855 20280664313432058033391283)
          ·
            refine ⟨30420996470148087050086925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20280664313432058033391283 30420996470148087050086925)
            ·
              refine ⟨11407873676305532643782597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30420996470148087050086925 11407873676305532643782597)
              ·
                refine ⟨2138976314307287370709237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11407873676305532643782597 2138976314307287370709237)
                ·
                  refine ⟨200529029466308191003991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2138976314307287370709237 200529029466308191003991)
                  ·
                    rfl

theorem cell23_3514760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 4, 5].length) (baseStart_3514760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3514760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3514760 prefixEnd_3514760 := by exact prefixLift 3514760
  have htrace : WordTrace (prefixWord ++ tailWord_3514760) baseStart_3514760 baseEnd_3514760 := by
    simpa [prefixWord, tailWord_3514760, baseEnd_3514760] using wordTrace_append hprefix tailTrace_3514760
  have hstable : (prefixWord ++ tailWord_3514760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3514760).length < 2 ^ (prefixWord ++ tailWord_3514760).sum := by decide
  have hdescent : baseEnd_3514760 < baseStart_3514760 := by decide
  rcases family_descends (prefixWord ++ tailWord_3514760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3514833 : List Nat := [1, 2, 2, 1, 2, 1, 1, 7, 6]
def baseStart_3514833 : Nat := 118140960795 + 3514833 * 2 ^ 59
def prefixEnd_3514833 : Nat := 4983230072969 + 3 ^ 40 * 3514833 * 2
def baseEnd_3514833 : Nat := 200533194364950214824787

theorem tailTrace_3514833 : CollatzResearch.WordTrace tailWord_3514833 prefixEnd_3514833 200533194364950214824787 := by
  unfold tailWord_3514833
  simp only [CollatzResearch.WordTrace]
  refine ⟨128196491275367801530325153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85464327516911867686883435 128196491275367801530325153)
  ·
    refine ⟨96147368456525851147743865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128196491275367801530325153 96147368456525851147743865)
    ·
      refine ⟨72110526342394388360807899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96147368456525851147743865 72110526342394388360807899)
      ·
        refine ⟨108165789513591582541211849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72110526342394388360807899 108165789513591582541211849)
        ·
          refine ⟨81124342135193686905908887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108165789513591582541211849 81124342135193686905908887)
          ·
            refine ⟨121686513202790530358863331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81124342135193686905908887 121686513202790530358863331)
            ·
              refine ⟨182529769804185795538294997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121686513202790530358863331 182529769804185795538294997)
              ·
                refine ⟨4278041479785604582928789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 182529769804185795538294997 4278041479785604582928789)
                ·
                  refine ⟨200533194364950214824787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4278041479785604582928789 200533194364950214824787)
                  ·
                    rfl

theorem cell23_3514833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 7, 6].length) (baseStart_3514833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3514833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3514833 prefixEnd_3514833 := by exact prefixLift 3514833
  have htrace : WordTrace (prefixWord ++ tailWord_3514833) baseStart_3514833 baseEnd_3514833 := by
    simpa [prefixWord, tailWord_3514833, baseEnd_3514833] using wordTrace_append hprefix tailTrace_3514833
  have hstable : (prefixWord ++ tailWord_3514833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3514833).length < 2 ^ (prefixWord ++ tailWord_3514833).sum := by decide
  have hdescent : baseEnd_3514833 < baseStart_3514833 := by decide
  rcases family_descends (prefixWord ++ tailWord_3514833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3514863 : List Nat := [1, 1, 2, 1, 4, 1, 1, 2, 5, 5]
def baseStart_3514863 : Nat := 118140960795 + 3514863 * 2 ^ 59
def prefixEnd_3514863 : Nat := 4983230072969 + 3 ^ 40 * 3514863 * 2
def baseEnd_3514863 : Nat := 601604717901395605349315

theorem tailTrace_3514863 : CollatzResearch.WordTrace tailWord_3514863 prefixEnd_3514863 601604717901395605349315 := by
  unfold tailWord_3514863
  simp only [CollatzResearch.WordTrace]
  refine ⟨128197585465259116653917243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85465056976839411102611495 128197585465259116653917243)
  ·
    refine ⟨192296378197888674980875865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128197585465259116653917243 192296378197888674980875865)
    ·
      refine ⟨144222283648416506235656899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192296378197888674980875865 144222283648416506235656899)
      ·
        refine ⟨216333425472624759353485349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144222283648416506235656899 216333425472624759353485349)
        ·
          refine ⟨40562517276117142378778503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 216333425472624759353485349 40562517276117142378778503)
          ·
            refine ⟨60843775914175713568167755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40562517276117142378778503 60843775914175713568167755)
            ·
              refine ⟨91265663871263570352251633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60843775914175713568167755 91265663871263570352251633)
              ·
                refine ⟨68449247903447677764188725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91265663871263570352251633 68449247903447677764188725)
                ·
                  refine ⟨6417116990948219790392693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68449247903447677764188725 6417116990948219790392693)
                  ·
                    refine ⟨601604717901395605349315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6417116990948219790392693 601604717901395605349315)
                    ·
                      rfl

theorem cell23_3514863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 5, 5].length) (baseStart_3514863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3514863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3514863 prefixEnd_3514863 := by exact prefixLift 3514863
  have htrace : WordTrace (prefixWord ++ tailWord_3514863) baseStart_3514863 baseEnd_3514863 := by
    simpa [prefixWord, tailWord_3514863, baseEnd_3514863] using wordTrace_append hprefix tailTrace_3514863
  have hstable : (prefixWord ++ tailWord_3514863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3514863).length < 2 ^ (prefixWord ++ tailWord_3514863).sum := by decide
  have hdescent : baseEnd_3514863 < baseStart_3514863 := by decide
  rcases family_descends (prefixWord ++ tailWord_3514863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3514884 : List Nat := [2, 3, 2, 3, 1, 3, 2, 1, 6]
def baseStart_3514884 : Nat := 118140960795 + 3514884 * 2 ^ 59
def prefixEnd_3514884 : Nat := 4983230072969 + 3 ^ 40 * 3514884 * 2
def baseEnd_3514884 : Nat := 200536104088659025987261

theorem tailTrace_3514884 : CollatzResearch.WordTrace tailWord_3514884 prefixEnd_3514884 200536104088659025987261 := by
  unfold tailWord_3514884
  simp only [CollatzResearch.WordTrace]
  refine ⟨64099175699091518620215853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85465567598788691493621137 64099175699091518620215853)
  ·
    refine ⟨24037190887159319482580945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64099175699091518620215853 24037190887159319482580945)
    ·
      refine ⟨18027893165369489611935709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24037190887159319482580945 18027893165369489611935709)
      ·
        refine ⟨6760459937013558604475891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18027893165369489611935709 6760459937013558604475891)
        ·
          refine ⟨10140689905520337906713837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6760459937013558604475891 10140689905520337906713837)
          ·
            refine ⟨3802758714570126715017689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10140689905520337906713837 3802758714570126715017689)
            ·
              refine ⟨2852069035927595036263267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3802758714570126715017689 2852069035927595036263267)
              ·
                refine ⟨4278103553891392554394901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2852069035927595036263267 4278103553891392554394901)
                ·
                  refine ⟨200536104088659025987261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4278103553891392554394901 200536104088659025987261)
                  ·
                    rfl

theorem cell23_3514884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 2, 1, 6].length) (baseStart_3514884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3514884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3514884 prefixEnd_3514884 := by exact prefixLift 3514884
  have htrace : WordTrace (prefixWord ++ tailWord_3514884) baseStart_3514884 baseEnd_3514884 := by
    simpa [prefixWord, tailWord_3514884, baseEnd_3514884] using wordTrace_append hprefix tailTrace_3514884
  have hstable : (prefixWord ++ tailWord_3514884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3514884).length < 2 ^ (prefixWord ++ tailWord_3514884).sum := by decide
  have hdescent : baseEnd_3514884 < baseStart_3514884 := by decide
  rcases family_descends (prefixWord ++ tailWord_3514884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3514904 : List Nat := [2, 1, 2, 3, 3, 2, 2, 1, 2, 3, 2]
def baseStart_3514904 : Nat := 118140960795 + 3514904 * 2 ^ 59
def prefixEnd_3514904 : Nat := 4983230072969 + 3 ^ 40 * 3514904 * 2
def baseEnd_3514904 : Nat := 1804835206411021155635257

theorem tailTrace_3514904 : CollatzResearch.WordTrace tailWord_3514904 prefixEnd_3514904 1804835206411021155635257 := by
  unfold tailWord_3514904
  simp only [CollatzResearch.WordTrace]
  refine ⟨64099540429055290328079883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85466053905407053770773177 64099540429055290328079883)
  ·
    refine ⟨96149310643582935492119825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64099540429055290328079883 96149310643582935492119825)
    ·
      refine ⟨72111982982687201619089869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96149310643582935492119825 72111982982687201619089869)
      ·
        refine ⟨27041993618507700607158701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72111982982687201619089869 27041993618507700607158701)
        ·
          refine ⟨10140747606940387727684513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27041993618507700607158701 10140747606940387727684513)
          ·
            refine ⟨7605560705205290795763385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10140747606940387727684513 7605560705205290795763385)
            ·
              refine ⟨5704170528903968096822539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7605560705205290795763385 5704170528903968096822539)
              ·
                refine ⟨8556255793355952145233809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5704170528903968096822539 8556255793355952145233809)
                ·
                  refine ⟨6417191845016964108925357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8556255793355952145233809 6417191845016964108925357)
                  ·
                    refine ⟨2406446941881361540847009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6417191845016964108925357 2406446941881361540847009)
                    ·
                      refine ⟨1804835206411021155635257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2406446941881361540847009 1804835206411021155635257)
                      ·
                        rfl

theorem cell23_3514904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 2, 1, 2, 3, 2].length) (baseStart_3514904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3514904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3514904 prefixEnd_3514904 := by exact prefixLift 3514904
  have htrace : WordTrace (prefixWord ++ tailWord_3514904) baseStart_3514904 baseEnd_3514904 := by
    simpa [prefixWord, tailWord_3514904, baseEnd_3514904] using wordTrace_append hprefix tailTrace_3514904
  have hstable : (prefixWord ++ tailWord_3514904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3514904).length < 2 ^ (prefixWord ++ tailWord_3514904).sum := by decide
  have hdescent : baseEnd_3514904 < baseStart_3514904 := by decide
  rcases family_descends (prefixWord ++ tailWord_3514904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3514940 : List Nat := [2, 2, 2, 2, 3, 1, 3, 8]
def baseStart_3514940 : Nat := 118140960795 + 3514940 * 2 ^ 59
def prefixEnd_3514940 : Nat := 4983230072969 + 3 ^ 40 * 3514940 * 2
def baseEnd_3514940 : Nat := 66846433026466037584633

theorem tailTrace_3514940 : CollatzResearch.WordTrace tailWord_3514940 prefixEnd_3514940 66846433026466037584633 := by
  unfold tailWord_3514940
  simp only [CollatzResearch.WordTrace]
  refine ⟨64100196942990079402235137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85466929257320105869646849 64100196942990079402235137)
  ·
    refine ⟨48075147707242559551676353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64100196942990079402235137 48075147707242559551676353)
    ·
      refine ⟨36056360780431919663757265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48075147707242559551676353 36056360780431919663757265)
      ·
        refine ⟨27042270585323939747817949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36056360780431919663757265 27042270585323939747817949)
        ·
          refine ⟨10140851469496477405431731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27042270585323939747817949 10140851469496477405431731)
          ·
            refine ⟨15211277204244716108147597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10140851469496477405431731 15211277204244716108147597)
            ·
              refine ⟨5704228951591768540555349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15211277204244716108147597 5704228951591768540555349)
              ·
                refine ⟨66846433026466037584633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5704228951591768540555349 66846433026466037584633)
                ·
                  rfl

theorem cell23_3514940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 3, 8].length) (baseStart_3514940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3514940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3514940 prefixEnd_3514940 := by exact prefixLift 3514940
  have htrace : WordTrace (prefixWord ++ tailWord_3514940) baseStart_3514940 baseEnd_3514940 := by
    simpa [prefixWord, tailWord_3514940, baseEnd_3514940] using wordTrace_append hprefix tailTrace_3514940
  have hstable : (prefixWord ++ tailWord_3514940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3514940).length < 2 ^ (prefixWord ++ tailWord_3514940).sum := by decide
  have hdescent : baseEnd_3514940 < baseStart_3514940 := by decide
  rcases family_descends (prefixWord ++ tailWord_3514940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3514967 : List Nat := [1, 1, 3, 2, 2, 2, 2, 2, 4, 1, 3]
def baseStart_3514967 : Nat := 118140960795 + 3514967 * 2 ^ 59
def prefixEnd_3514967 : Nat := 4983230072969 + 3 ^ 40 * 3514967 * 2
def baseEnd_3514967 : Nat := 1804867555692254409147467

theorem tailTrace_3514967 : CollatzResearch.WordTrace tailWord_3514967 prefixEnd_3514967 1804867555692254409147467 := by
  unfold tailWord_3514967
  simp only [CollatzResearch.WordTrace]
  refine ⟨128201378656882342415703155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85467585771254894943802103 128201378656882342415703155)
  ·
    refine ⟨192302067985323513623554733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128201378656882342415703155 192302067985323513623554733)
    ·
      refine ⟨72113275494496317608833025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192302067985323513623554733 72113275494496317608833025)
      ·
        refine ⟨54084956620872238206624769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72113275494496317608833025 54084956620872238206624769)
        ·
          refine ⟨40563717465654178654968577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54084956620872238206624769 40563717465654178654968577)
          ·
            refine ⟨30422788099240633991226433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40563717465654178654968577 30422788099240633991226433)
            ·
              refine ⟨22817091074430475493419825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30422788099240633991226433 22817091074430475493419825)
              ·
                refine ⟨17112818305822856620064869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22817091074430475493419825 17112818305822856620064869)
                ·
                  refine ⟨3208653432341785616262163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17112818305822856620064869 3208653432341785616262163)
                  ·
                    refine ⟨4812980148512678424393245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3208653432341785616262163 4812980148512678424393245)
                    ·
                      refine ⟨1804867555692254409147467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4812980148512678424393245 1804867555692254409147467)
                      ·
                        rfl

theorem cell23_3514967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 2, 4, 1, 3].length) (baseStart_3514967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3514967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3514967 prefixEnd_3514967 := by exact prefixLift 3514967
  have htrace : WordTrace (prefixWord ++ tailWord_3514967) baseStart_3514967 baseEnd_3514967 := by
    simpa [prefixWord, tailWord_3514967, baseEnd_3514967] using wordTrace_append hprefix tailTrace_3514967
  have hstable : (prefixWord ++ tailWord_3514967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3514967).length < 2 ^ (prefixWord ++ tailWord_3514967).sum := by decide
  have hdescent : baseEnd_3514967 < baseStart_3514967 := by decide
  rcases family_descends (prefixWord ++ tailWord_3514967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3514978 : List Nat := [3, 3, 2, 3, 1, 2, 1, 2, 2, 4]
def baseStart_3514978 : Nat := 118140960795 + 3514978 * 2 ^ 59
def prefixEnd_3514978 : Nat := 4983230072969 + 3 ^ 40 * 3514978 * 2
def baseEnd_3514978 : Nat := 601624401326484622036639

theorem tailTrace_3514978 : CollatzResearch.WordTrace tailWord_3514978 prefixEnd_3514978 601624401326484622036639 := by
  unfold tailWord_3514978
  simp only [CollatzResearch.WordTrace]
  refine ⟨32050444964960622823588397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85467853239894994196235725 32050444964960622823588397)
  ·
    refine ⟨12018916861860233558845649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32050444964960622823588397 12018916861860233558845649)
    ·
      refine ⟨9014187646395175169134237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12018916861860233558845649 9014187646395175169134237)
      ·
        refine ⟨3380320367398190688425339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9014187646395175169134237 3380320367398190688425339)
        ·
          refine ⟨5070480551097286032638009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3380320367398190688425339 5070480551097286032638009)
          ·
            refine ⟨3802860413322964524478507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5070480551097286032638009 3802860413322964524478507)
            ·
              refine ⟨5704290619984446786717761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3802860413322964524478507 5704290619984446786717761)
              ·
                refine ⟨4278217964988335090038321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5704290619984446786717761 4278217964988335090038321)
                ·
                  refine ⟨3208663473741251317528741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4278217964988335090038321 3208663473741251317528741)
                  ·
                    refine ⟨601624401326484622036639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3208663473741251317528741 601624401326484622036639)
                    ·
                      rfl

theorem cell23_3514978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 1, 2, 2, 4].length) (baseStart_3514978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3514978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3514978 prefixEnd_3514978 := by exact prefixLift 3514978
  have htrace : WordTrace (prefixWord ++ tailWord_3514978) baseStart_3514978 baseEnd_3514978 := by
    simpa [prefixWord, tailWord_3514978, baseEnd_3514978] using wordTrace_append hprefix tailTrace_3514978
  have hstable : (prefixWord ++ tailWord_3514978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3514978).length < 2 ^ (prefixWord ++ tailWord_3514978).sum := by decide
  have hdescent : baseEnd_3514978 < baseStart_3514978 := by decide
  rcases family_descends (prefixWord ++ tailWord_3514978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3515001 : List Nat := [1, 2, 1, 3, 3, 3, 3, 1, 2, 1, 3]
def baseStart_3515001 : Nat := 118140960795 + 3515001 * 2 ^ 59
def prefixEnd_3515001 : Nat := 4983230072969 + 3 ^ 40 * 3515001 * 2
def baseEnd_3515001 : Nat := 1804885014034507276122311

theorem tailTrace_3515001 : CollatzResearch.WordTrace tailWord_3515001 prefixEnd_3515001 1804885014034507276122311 := by
  unfold tailWord_3515001
  simp only [CollatzResearch.WordTrace]
  refine ⟨128202618738759166222440857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85468412492506110814960571 128202618738759166222440857)
  ·
    refine ⟨96151964054069374666830643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128202618738759166222440857 96151964054069374666830643)
    ·
      refine ⟨144227946081104062000245965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96151964054069374666830643 144227946081104062000245965)
      ·
        refine ⟨54085479780414023250092237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144227946081104062000245965 54085479780414023250092237)
        ·
          refine ⟨20282054917655258718784589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54085479780414023250092237 20282054917655258718784589)
          ·
            refine ⟨7605770594120722019544221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20282054917655258718784589 7605770594120722019544221)
            ·
              refine ⟨2852163972795270757329083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7605770594120722019544221 2852163972795270757329083)
              ·
                refine ⟨4278245959192906135993625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2852163972795270757329083 4278245959192906135993625)
                ·
                  refine ⟨3208684469394679601995219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4278245959192906135993625 3208684469394679601995219)
                  ·
                    refine ⟨4813026704092019402992829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3208684469394679601995219 4813026704092019402992829)
                    ·
                      refine ⟨1804885014034507276122311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4813026704092019402992829 1804885014034507276122311)
                      ·
                        rfl

theorem cell23_3515001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 3, 1, 2, 1, 3].length) (baseStart_3515001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3515001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3515001 prefixEnd_3515001 := by exact prefixLift 3515001
  have htrace : WordTrace (prefixWord ++ tailWord_3515001) baseStart_3515001 baseEnd_3515001 := by
    simpa [prefixWord, tailWord_3515001, baseEnd_3515001] using wordTrace_append hprefix tailTrace_3515001
  have hstable : (prefixWord ++ tailWord_3515001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3515001).length < 2 ^ (prefixWord ++ tailWord_3515001).sum := by decide
  have hdescent : baseEnd_3515001 < baseStart_3515001 := by decide
  rcases family_descends (prefixWord ++ tailWord_3515001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3515007 : List Nat := [1, 1, 2, 2, 1, 1, 1, 7, 1, 4, 2]
def baseStart_3515007 : Nat := 118140960795 + 3515007 * 2 ^ 59
def prefixEnd_3515007 : Nat := 4983230072969 + 3 ^ 40 * 3515007 * 2
def baseEnd_3515007 : Nat := 1804888094918434252647283

theorem tailTrace_3515007 : CollatzResearch.WordTrace tailWord_3515007 prefixEnd_3515007 1804888094918434252647283 := by
  unfold tailWord_3515007
  simp only [CollatzResearch.WordTrace]
  refine ⟨128202837576737429247159275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85468558384491619498106183 128202837576737429247159275)
  ·
    refine ⟨192304256365106143870738913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128202837576737429247159275 192304256365106143870738913)
    ·
      refine ⟨144228192273829607903054185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192304256365106143870738913 144228192273829607903054185)
      ·
        refine ⟨108171144205372205927290639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144228192273829607903054185 108171144205372205927290639)
        ·
          refine ⟨162256716308058308890935959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108171144205372205927290639 162256716308058308890935959)
          ·
            refine ⟨243385074462087463336403939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162256716308058308890935959 243385074462087463336403939)
            ·
              refine ⟨365077611693131195004605909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 243385074462087463336403939 365077611693131195004605909)
              ·
                refine ⟨8556506524057762382920451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 365077611693131195004605909 8556506524057762382920451)
                ·
                  refine ⟨12834759786086643574380677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8556506524057762382920451 12834759786086643574380677)
                  ·
                    refine ⟨2406517459891245670196377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12834759786086643574380677 2406517459891245670196377)
                    ·
                      refine ⟨1804888094918434252647283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2406517459891245670196377 1804888094918434252647283)
                      ·
                        rfl

theorem cell23_3515007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 7, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 7, 1, 4, 2].length) (baseStart_3515007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3515007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3515007 prefixEnd_3515007 := by exact prefixLift 3515007
  have htrace : WordTrace (prefixWord ++ tailWord_3515007) baseStart_3515007 baseEnd_3515007 := by
    simpa [prefixWord, tailWord_3515007, baseEnd_3515007] using wordTrace_append hprefix tailTrace_3515007
  have hstable : (prefixWord ++ tailWord_3515007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3515007).length < 2 ^ (prefixWord ++ tailWord_3515007).sum := by decide
  have hdescent : baseEnd_3515007 < baseStart_3515007 := by decide
  rcases family_descends (prefixWord ++ tailWord_3515007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3515020 : List Nat := [2, 2, 1, 2, 1, 1, 2, 2, 4, 2, 4]
def baseStart_3515020 : Nat := 118140960795 + 3515020 * 2 ^ 59
def prefixEnd_3515020 : Nat := 4983230072969 + 3 ^ 40 * 3515020 * 2
def baseEnd_3515020 : Nat := 1804894770166942701784723

theorem tailTrace_3515020 : CollatzResearch.WordTrace tailWord_3515020 prefixEnd_3515020 1804894770166942701784723 := by
  unfold tailWord_3515020
  simp only [CollatzResearch.WordTrace]
  refine ⟨64101655862845166233691257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85468874483793554978255009 64101655862845166233691257)
  ·
    refine ⟨48076241897133874675268443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64101655862845166233691257 48076241897133874675268443)
    ·
      refine ⟨72114362845700812012902665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48076241897133874675268443 72114362845700812012902665)
      ·
        refine ⟨54085772134275609009676999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72114362845700812012902665 54085772134275609009676999)
        ·
          refine ⟨81128658201413413514515499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54085772134275609009676999 81128658201413413514515499)
          ·
            refine ⟨121692987302120120271773249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81128658201413413514515499 121692987302120120271773249)
            ·
              refine ⟨91269740476590090203829937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121692987302120120271773249 91269740476590090203829937)
              ·
                refine ⟨68452305357442567652872453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91269740476590090203829937 68452305357442567652872453)
                ·
                  refine ⟨12834807254520481434913585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68452305357442567652872453 12834807254520481434913585)
                  ·
                    refine ⟨9626105440890361076185189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12834807254520481434913585 9626105440890361076185189)
                    ·
                      refine ⟨1804894770166942701784723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9626105440890361076185189 1804894770166942701784723)
                      ·
                        rfl

theorem cell23_3515020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 4, 2, 4].length) (baseStart_3515020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3515020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3515020 prefixEnd_3515020 := by exact prefixLift 3515020
  have htrace : WordTrace (prefixWord ++ tailWord_3515020) baseStart_3515020 baseEnd_3515020 := by
    simpa [prefixWord, tailWord_3515020, baseEnd_3515020] using wordTrace_append hprefix tailTrace_3515020
  have hstable : (prefixWord ++ tailWord_3515020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3515020).length < 2 ^ (prefixWord ++ tailWord_3515020).sum := by decide
  have hdescent : baseEnd_3515020 < baseStart_3515020 := by decide
  rcases family_descends (prefixWord ++ tailWord_3515020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3515062 : List Nat := [5, 1, 3, 1, 3, 1, 1, 2, 1, 3, 2]
def baseStart_3515062 : Nat := 118140960795 + 3515062 * 2 ^ 59
def prefixEnd_3515062 : Nat := 4983230072969 + 3 ^ 40 * 3515062 * 2
def baseEnd_3515062 : Nat := 1804916336354431537459531

theorem tailTrace_3515062 : CollatzResearch.WordTrace tailWord_3515062 prefixEnd_3515062 1804916336354431537459531 := by
  unfold tailWord_3515062
  simp only [CollatzResearch.WordTrace]
  refine ⟨8012802724471135852525715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 85469895727692115760274293 8012802724471135852525715)
  ·
    refine ⟨12019204086706703778788573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8012802724471135852525715 12019204086706703778788573)
    ·
      refine ⟨4507201532515013917045715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12019204086706703778788573 4507201532515013917045715)
      ·
        refine ⟨6760802298772520875568573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4507201532515013917045715 6760802298772520875568573)
        ·
          refine ⟨2535300862039695328338215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6760802298772520875568573 2535300862039695328338215)
          ·
            refine ⟨3802951293059542992507323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2535300862039695328338215 3802951293059542992507323)
            ·
              refine ⟨5704426939589314488760985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3802951293059542992507323 5704426939589314488760985)
              ·
                refine ⟨4278320204691985866570739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5704426939589314488760985 4278320204691985866570739)
                ·
                  refine ⟨6417480307037978799856109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4278320204691985866570739 6417480307037978799856109)
                  ·
                    refine ⟨2406555115139242049946041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6417480307037978799856109 2406555115139242049946041)
                    ·
                      refine ⟨1804916336354431537459531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2406555115139242049946041 1804916336354431537459531)
                      ·
                        rfl

theorem cell23_3515062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 1, 2, 1, 3, 2].length) (baseStart_3515062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3515062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3515062 prefixEnd_3515062 := by exact prefixLift 3515062
  have htrace : WordTrace (prefixWord ++ tailWord_3515062) baseStart_3515062 baseEnd_3515062 := by
    simpa [prefixWord, tailWord_3515062, baseEnd_3515062] using wordTrace_append hprefix tailTrace_3515062
  have hstable : (prefixWord ++ tailWord_3515062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3515062).length < 2 ^ (prefixWord ++ tailWord_3515062).sum := by decide
  have hdescent : baseEnd_3515062 < baseStart_3515062 := by decide
  rcases family_descends (prefixWord ++ tailWord_3515062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3515097 : List Nat := [1, 2, 1, 2, 3, 2, 1, 4, 2, 1, 4]
def baseStart_3515097 : Nat := 118140960795 + 3515097 * 2 ^ 59
def prefixEnd_3515097 : Nat := 4983230072969 + 3 ^ 40 * 3515097 * 2
def baseEnd_3515097 : Nat := 1804934308177338900521869

theorem tailTrace_3515097 : CollatzResearch.WordTrace tailWord_3515097 prefixEnd_3515097 1804934308177338900521869 := by
  unfold tailWord_3515097
  simp only [CollatzResearch.WordTrace]
  refine ⟨128206120146411374617935545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85470746764274249745290363 128206120146411374617935545)
  ·
    refine ⟨96154590109808530963451659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128206120146411374617935545 96154590109808530963451659)
    ·
      refine ⟨144231885164712796445177489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96154590109808530963451659 144231885164712796445177489)
      ·
        refine ⟨108173913873534597333883117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144231885164712796445177489 108173913873534597333883117)
        ·
          refine ⟨40565217702575474000206169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108173913873534597333883117 40565217702575474000206169)
          ·
            refine ⟨30423913276931605500154627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40565217702575474000206169 30423913276931605500154627)
            ·
              refine ⟨45635869915397408250231941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30423913276931605500154627 45635869915397408250231941)
              ·
                refine ⟨8556725609137014046918489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45635869915397408250231941 8556725609137014046918489)
                ·
                  refine ⟨6417544206852760535188867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8556725609137014046918489 6417544206852760535188867)
                  ·
                    refine ⟨9626316310279140802783301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6417544206852760535188867 9626316310279140802783301)
                    ·
                      refine ⟨1804934308177338900521869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9626316310279140802783301 1804934308177338900521869)
                      ·
                        rfl

theorem cell23_3515097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 4, 2, 1, 4].length) (baseStart_3515097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3515097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3515097 prefixEnd_3515097 := by exact prefixLift 3515097
  have htrace : WordTrace (prefixWord ++ tailWord_3515097) baseStart_3515097 baseEnd_3515097 := by
    simpa [prefixWord, tailWord_3515097, baseEnd_3515097] using wordTrace_append hprefix tailTrace_3515097
  have hstable : (prefixWord ++ tailWord_3515097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3515097).length < 2 ^ (prefixWord ++ tailWord_3515097).sum := by decide
  have hdescent : baseEnd_3515097 < baseStart_3515097 := by decide
  rcases family_descends (prefixWord ++ tailWord_3515097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3515266 : List Nat := [3, 4, 2, 2, 1, 2, 2, 2, 1, 1, 3]
def baseStart_3515266 : Nat := 118140960795 + 3515266 * 2 ^ 59
def prefixEnd_3515266 : Nat := 4983230072969 + 3 ^ 40 * 3515266 * 2
def baseEnd_3515266 : Nat := 1805021086407948739308593

theorem tailTrace_3515266 : CollatzResearch.WordTrace tailWord_3515266 prefixEnd_3515266 1805021086407948739308593 := by
  unfold tailWord_3515266
  simp only [CollatzResearch.WordTrace]
  refine ⟨32053071020699779120209413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85474856055199410987225101 32053071020699779120209413)
  ·
    refine ⟨6009950816381208585039265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32053071020699779120209413 6009950816381208585039265)
    ·
      refine ⟨4507463112285906438779449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6009950816381208585039265 4507463112285906438779449)
      ·
        refine ⟨3380597334214429829084587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4507463112285906438779449 3380597334214429829084587)
        ·
          refine ⟨5070896001321644743626881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3380597334214429829084587 5070896001321644743626881)
          ·
            refine ⟨3803172000991233557720161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5070896001321644743626881 3803172000991233557720161)
            ·
              refine ⟨2852379000743425168290121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3803172000991233557720161 2852379000743425168290121)
              ·
                refine ⟨2139284250557568876217591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2852379000743425168290121 2139284250557568876217591)
                ·
                  refine ⟨3208926375836353314326387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2139284250557568876217591 3208926375836353314326387)
                  ·
                    refine ⟨4813389563754529971489581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3208926375836353314326387 4813389563754529971489581)
                    ·
                      refine ⟨1805021086407948739308593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4813389563754529971489581 1805021086407948739308593)
                      ·
                        rfl

theorem cell23_3515266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_3515266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3515266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3515266 prefixEnd_3515266 := by exact prefixLift 3515266
  have htrace : WordTrace (prefixWord ++ tailWord_3515266) baseStart_3515266 baseEnd_3515266 := by
    simpa [prefixWord, tailWord_3515266, baseEnd_3515266] using wordTrace_append hprefix tailTrace_3515266
  have hstable : (prefixWord ++ tailWord_3515266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3515266).length < 2 ^ (prefixWord ++ tailWord_3515266).sum := by decide
  have hdescent : baseEnd_3515266 < baseStart_3515266 := by decide
  rcases family_descends (prefixWord ++ tailWord_3515266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3515272 : List Nat := [2, 1, 3, 3, 2, 1, 4, 2, 1, 2, 2]
def baseStart_3515272 : Nat := 118140960795 + 3515272 * 2 ^ 59
def prefixEnd_3515272 : Nat := 4983230072969 + 3 ^ 40 * 3515272 * 2
def baseEnd_3515272 : Nat := 1805024167291875715833565

theorem tailTrace_3515272 : CollatzResearch.WordTrace tailWord_3515272 prefixEnd_3515272 1805024167291875715833565 := by
  unfold tailWord_3515272
  simp only [CollatzResearch.WordTrace]
  refine ⟨64106251460388689752778035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85475001947184919670370713 64106251460388689752778035)
  ·
    refine ⟨96159377190583034629167053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64106251460388689752778035 96159377190583034629167053)
    ·
      refine ⟨36059766446468637985937645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96159377190583034629167053 36059766446468637985937645)
      ·
        refine ⟨13522412417425739244726617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36059766446468637985937645 13522412417425739244726617)
        ·
          refine ⟨10141809313069304433544963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13522412417425739244726617 10141809313069304433544963)
          ·
            refine ⟨15212713969603956650317445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10141809313069304433544963 15212713969603956650317445)
            ·
              refine ⟨2852383869300741871934521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15212713969603956650317445 2852383869300741871934521)
              ·
                refine ⟨2139287901975556403950891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2852383869300741871934521 2139287901975556403950891)
                ·
                  refine ⟨3208931852963334605926337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2139287901975556403950891 3208931852963334605926337)
                  ·
                    refine ⟨2406698889722500954444753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3208931852963334605926337 2406698889722500954444753)
                    ·
                      refine ⟨1805024167291875715833565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2406698889722500954444753 1805024167291875715833565)
                      ·
                        rfl

theorem cell23_3515272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 4, 2, 1, 2, 2].length) (baseStart_3515272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3515272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3515272 prefixEnd_3515272 := by exact prefixLift 3515272
  have htrace : WordTrace (prefixWord ++ tailWord_3515272) baseStart_3515272 baseEnd_3515272 := by
    simpa [prefixWord, tailWord_3515272, baseEnd_3515272] using wordTrace_append hprefix tailTrace_3515272
  have hstable : (prefixWord ++ tailWord_3515272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3515272).length < 2 ^ (prefixWord ++ tailWord_3515272).sum := by decide
  have hdescent : baseEnd_3515272 < baseStart_3515272 := by decide
  rcases family_descends (prefixWord ++ tailWord_3515272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3515274 : List Nat := [3, 1, 2, 4, 1, 1, 1, 1, 2, 7]
def baseStart_3515274 : Nat := 118140960795 + 3515274 * 2 ^ 59
def prefixEnd_3515274 : Nat := 4983230072969 + 3 ^ 40 * 3515274 * 2
def baseEnd_3515274 : Nat := 601675064751061569336185

theorem tailTrace_3515274 : CollatzResearch.WordTrace tailWord_3515274 prefixEnd_3515274 601675064751061569336185 := by
  unfold tailWord_3515274
  simp only [CollatzResearch.WordTrace]
  refine ⟨32053143966692533461782219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85475050577846755898085917 32053143966692533461782219)
  ·
    refine ⟨48079715950038800192673329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32053143966692533461782219 48079715950038800192673329)
    ·
      refine ⟨36059786962529100144504997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48079715950038800192673329 36059786962529100144504997)
      ·
        refine ⟨6761210055474206277094687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36059786962529100144504997 6761210055474206277094687)
        ·
          refine ⟨10141815083211309415642031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6761210055474206277094687 10141815083211309415642031)
          ·
            refine ⟨15212722624816964123463047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10141815083211309415642031 15212722624816964123463047)
            ·
              refine ⟨22819083937225446185194571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15212722624816964123463047 22819083937225446185194571)
              ·
                refine ⟨34228625905838169277791857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22819083937225446185194571 34228625905838169277791857)
                ·
                  refine ⟨25671469429378626958343893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34228625905838169277791857 25671469429378626958343893)
                  ·
                    refine ⟨601675064751061569336185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25671469429378626958343893 601675064751061569336185)
                    ·
                      rfl

theorem cell23_3515274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 1, 2, 7].length) (baseStart_3515274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3515274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3515274 prefixEnd_3515274 := by exact prefixLift 3515274
  have htrace : WordTrace (prefixWord ++ tailWord_3515274) baseStart_3515274 baseEnd_3515274 := by
    simpa [prefixWord, tailWord_3515274, baseEnd_3515274] using wordTrace_append hprefix tailTrace_3515274
  have hstable : (prefixWord ++ tailWord_3515274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3515274).length < 2 ^ (prefixWord ++ tailWord_3515274).sum := by decide
  have hdescent : baseEnd_3515274 < baseStart_3515274 := by decide
  rcases family_descends (prefixWord ++ tailWord_3515274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3515298 : List Nat := [3, 3, 1, 2, 2, 1, 2, 1, 3, 3, 2]
def baseStart_3515298 : Nat := 118140960795 + 3515298 * 2 ^ 59
def prefixEnd_3515298 : Nat := 4983230072969 + 3 ^ 40 * 3515298 * 2
def baseEnd_3515298 : Nat := 1805037517788892614108445

theorem tailTrace_3515298 : CollatzResearch.WordTrace tailWord_3515298 prefixEnd_3515298 1805037517788892614108445 := by
  unfold tailWord_3515298
  simp only [CollatzResearch.WordTrace]
  refine ⟨32053362804670796486500637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85475634145788790630668365 32053362804670796486500637)
  ·
    refine ⟨12020011051751548682437739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32053362804670796486500637 12020011051751548682437739)
    ·
      refine ⟨18030016577627323023656609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12020011051751548682437739 18030016577627323023656609)
      ·
        refine ⟨13522512433220492267742457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18030016577627323023656609 13522512433220492267742457)
        ·
          refine ⟨10141884324915369200806843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13522512433220492267742457 10141884324915369200806843)
          ·
            refine ⟨15212826487373053801210265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10141884324915369200806843 15212826487373053801210265)
            ·
              refine ⟨11409619865529790350907699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15212826487373053801210265 11409619865529790350907699)
              ·
                refine ⟨17114429798294685526361549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11409619865529790350907699 17114429798294685526361549)
                ·
                  refine ⟨6417911174360507072385581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17114429798294685526361549 6417911174360507072385581)
                  ·
                    refine ⟨2406716690385190152144593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6417911174360507072385581 2406716690385190152144593)
                    ·
                      refine ⟨1805037517788892614108445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2406716690385190152144593 1805037517788892614108445)
                      ·
                        rfl

theorem cell23_3515298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 1, 3, 3, 2].length) (baseStart_3515298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3515298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3515298 prefixEnd_3515298 := by exact prefixLift 3515298
  have htrace : WordTrace (prefixWord ++ tailWord_3515298) baseStart_3515298 baseEnd_3515298 := by
    simpa [prefixWord, tailWord_3515298, baseEnd_3515298] using wordTrace_append hprefix tailTrace_3515298
  have hstable : (prefixWord ++ tailWord_3515298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3515298).length < 2 ^ (prefixWord ++ tailWord_3515298).sum := by decide
  have hdescent : baseEnd_3515298 < baseStart_3515298 := by decide
  rcases family_descends (prefixWord ++ tailWord_3515298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3515309 : List Nat := [1, 5, 2, 3, 2, 1, 2, 1, 1, 2, 3]
def baseStart_3515309 : Nat := 118140960795 + 3515309 * 2 ^ 59
def prefixEnd_3515309 : Nat := 4983230072969 + 3 ^ 40 * 3515309 * 2
def baseEnd_3515309 : Nat := 1805043166076092071070895

theorem tailTrace_3515309 : CollatzResearch.WordTrace tailWord_3515309 prefixEnd_3515309 1805043166076092071070895 := by
  unfold tailWord_3515309
  simp only [CollatzResearch.WordTrace]
  refine ⟨128213852421643334824652981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85475901614428889883101987 128213852421643334824652981)
  ·
    refine ⟨12020048664529062639811217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 128213852421643334824652981 12020048664529062639811217)
    ·
      refine ⟨9015036498396796979858413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12020048664529062639811217 9015036498396796979858413)
      ·
        refine ⟨3380638686898798867446905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9015036498396796979858413 3380638686898798867446905)
        ·
          refine ⟨2535479015174099150585179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3380638686898798867446905 2535479015174099150585179)
          ·
            refine ⟨3803218522761148725877769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2535479015174099150585179 3803218522761148725877769)
            ·
              refine ⟨2852413892070861544408327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3803218522761148725877769 2852413892070861544408327)
              ·
                refine ⟨4278620838106292316612491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2852413892070861544408327 4278620838106292316612491)
                ·
                  refine ⟨6417931257159438474918737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4278620838106292316612491 6417931257159438474918737)
                  ·
                    refine ⟨4813448442869578856189053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6417931257159438474918737 4813448442869578856189053)
                    ·
                      refine ⟨1805043166076092071070895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4813448442869578856189053 1805043166076092071070895)
                      ·
                        rfl

theorem cell23_3515309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_3515309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3515309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3515309 prefixEnd_3515309 := by exact prefixLift 3515309
  have htrace : WordTrace (prefixWord ++ tailWord_3515309) baseStart_3515309 baseEnd_3515309 := by
    simpa [prefixWord, tailWord_3515309, baseEnd_3515309] using wordTrace_append hprefix tailTrace_3515309
  have hstable : (prefixWord ++ tailWord_3515309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3515309).length < 2 ^ (prefixWord ++ tailWord_3515309).sum := by decide
  have hdescent : baseEnd_3515309 < baseStart_3515309 := by decide
  rcases family_descends (prefixWord ++ tailWord_3515309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3515327 : List Nat := [1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 9]
def baseStart_3515327 : Nat := 118140960795 + 3515327 * 2 ^ 59
def prefixEnd_3515327 : Nat := 4983230072969 + 3 ^ 40 * 3515327 * 2
def baseEnd_3515327 : Nat := 1805052408727873000645811

theorem tailTrace_3515327 : CollatzResearch.WordTrace tailWord_3515327 prefixEnd_3515327 1805052408727873000645811 := by
  unfold tailWord_3515327
  simp only [CollatzResearch.WordTrace]
  refine ⟨128214508935578123898808235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85476339290385415932538823 128214508935578123898808235)
  ·
    refine ⟨192321763403367185848212353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128214508935578123898808235 192321763403367185848212353)
    ·
      refine ⟨144241322552525389386159265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192321763403367185848212353 144241322552525389386159265)
      ·
        refine ⟨108180991914394042039619449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144241322552525389386159265 108180991914394042039619449)
        ·
          refine ⟨81135743935795531529714587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108180991914394042039619449 81135743935795531529714587)
          ·
            refine ⟨121703615903693297294571881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81135743935795531529714587 121703615903693297294571881)
            ·
              refine ⟨91277711927769972970928911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121703615903693297294571881 91277711927769972970928911)
              ·
                refine ⟨136916567891654959456393367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91277711927769972970928911 136916567891654959456393367)
                ·
                  refine ⟨205374851837482439184590051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 136916567891654959456393367 205374851837482439184590051)
                  ·
                    refine ⟨308062277756223658776885077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 205374851837482439184590051 308062277756223658776885077)
                    ·
                      refine ⟨1805052408727873000645811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 308062277756223658776885077 1805052408727873000645811)
                      ·
                        rfl

theorem cell23_3515327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 9].length) (baseStart_3515327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3515327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3515327 prefixEnd_3515327 := by exact prefixLift 3515327
  have htrace : WordTrace (prefixWord ++ tailWord_3515327) baseStart_3515327 baseEnd_3515327 := by
    simpa [prefixWord, tailWord_3515327, baseEnd_3515327] using wordTrace_append hprefix tailTrace_3515327
  have hstable : (prefixWord ++ tailWord_3515327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3515327).length < 2 ^ (prefixWord ++ tailWord_3515327).sum := by decide
  have hdescent : baseEnd_3515327 < baseStart_3515327 := by decide
  rcases family_descends (prefixWord ++ tailWord_3515327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3515328 : List Nat := [2, 1, 1, 2, 3, 4, 1, 1, 4, 2, 2]
def baseStart_3515328 : Nat := 118140960795 + 3515328 * 2 ^ 59
def prefixEnd_3515328 : Nat := 4983230072969 + 3 ^ 40 * 3515328 * 2
def baseEnd_3515328 : Nat := 1805052922208527496733307

theorem tailTrace_3515328 : CollatzResearch.WordTrace tailWord_3515328 prefixEnd_3515328 1805052922208527496733307 := by
  unfold tailWord_3515328
  simp only [CollatzResearch.WordTrace]
  refine ⟨64107272704287250534797319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85476363605716334046396425 64107272704287250534797319)
  ·
    refine ⟨96160909056430875802195979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64107272704287250534797319 96160909056430875802195979)
    ·
      refine ⟨144241363584646313703293969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96160909056430875802195979 144241363584646313703293969)
      ·
        refine ⟨108181022688484735277470477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144241363584646313703293969 108181022688484735277470477)
        ·
          refine ⟨40567883508181775729051429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108181022688484735277470477 40567883508181775729051429)
          ·
            refine ⟨7606478157784082949197143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40567883508181775729051429 7606478157784082949197143)
            ·
              refine ⟨11409717236676124423795715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7606478157784082949197143 11409717236676124423795715)
              ·
                refine ⟨17114575855014186635693573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11409717236676124423795715 17114575855014186635693573)
                ·
                  refine ⟨3208982972815159994192545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17114575855014186635693573 3208982972815159994192545)
                  ·
                    refine ⟨2406737229611369995644409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3208982972815159994192545 2406737229611369995644409)
                    ·
                      refine ⟨1805052922208527496733307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2406737229611369995644409 1805052922208527496733307)
                      ·
                        rfl

theorem cell23_3515328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 1, 4, 2, 2].length) (baseStart_3515328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3515328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3515328 prefixEnd_3515328 := by exact prefixLift 3515328
  have htrace : WordTrace (prefixWord ++ tailWord_3515328) baseStart_3515328 baseEnd_3515328 := by
    simpa [prefixWord, tailWord_3515328, baseEnd_3515328] using wordTrace_append hprefix tailTrace_3515328
  have hstable : (prefixWord ++ tailWord_3515328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3515328).length < 2 ^ (prefixWord ++ tailWord_3515328).sum := by decide
  have hdescent : baseEnd_3515328 < baseStart_3515328 := by decide
  rcases family_descends (prefixWord ++ tailWord_3515328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3515337 : List Nat := [1, 2, 1, 1, 2, 1, 2, 1, 1, 3, 8]
def baseStart_3515337 : Nat := 118140960795 + 3515337 * 2 ^ 59
def prefixEnd_3515337 : Nat := 4983230072969 + 3 ^ 40 * 3515337 * 2
def baseEnd_3515337 : Nat := 1805057543534417961520765

theorem tailTrace_3515337 : CollatzResearch.WordTrace tailWord_3515337 prefixEnd_3515337 1805057543534417961520765 := by
  unfold tailWord_3515337
  simp only [CollatzResearch.WordTrace]
  refine ⟨128214873665541895606672265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85476582443694597071114843 128214873665541895606672265)
  ·
    refine ⟨96161155249156421705004199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128214873665541895606672265 96161155249156421705004199)
    ·
      refine ⟨144241732873734632557506299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96161155249156421705004199 144241732873734632557506299)
      ·
        refine ⟨216362599310601948836259449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144241732873734632557506299 216362599310601948836259449)
        ·
          refine ⟨162271949482951461627194587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216362599310601948836259449 162271949482951461627194587)
          ·
            refine ⟨243407924224427192440791881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162271949482951461627194587 243407924224427192440791881)
            ·
              refine ⟨182555943168320394330593911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 243407924224427192440791881 182555943168320394330593911)
              ·
                refine ⟨273833914752480591495890867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 182555943168320394330593911 273833914752480591495890867)
                ·
                  refine ⟨410750872128720887243836301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 273833914752480591495890867 410750872128720887243836301)
                  ·
                    refine ⟨154031577048270332716438613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 410750872128720887243836301 154031577048270332716438613)
                    ·
                      refine ⟨1805057543534417961520765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 154031577048270332716438613 1805057543534417961520765)
                      ·
                        rfl

theorem cell23_3515337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 3, 8].length) (baseStart_3515337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3515337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3515337 prefixEnd_3515337 := by exact prefixLift 3515337
  have htrace : WordTrace (prefixWord ++ tailWord_3515337) baseStart_3515337 baseEnd_3515337 := by
    simpa [prefixWord, tailWord_3515337, baseEnd_3515337] using wordTrace_append hprefix tailTrace_3515337
  have hstable : (prefixWord ++ tailWord_3515337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3515337).length < 2 ^ (prefixWord ++ tailWord_3515337).sum := by decide
  have hdescent : baseEnd_3515337 < baseStart_3515337 := by decide
  rcases family_descends (prefixWord ++ tailWord_3515337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3515345 : List Nat := [1, 2, 2, 1, 2, 1, 7, 1, 2, 2, 2]
def baseStart_3515345 : Nat := 118140960795 + 3515345 * 2 ^ 59
def prefixEnd_3515345 : Nat := 4983230072969 + 3 ^ 40 * 3515345 * 2
def baseEnd_3515345 : Nat := 1805061651379653930220729

theorem tailTrace_3515345 : CollatzResearch.WordTrace tailWord_3515345 prefixEnd_3515345 1805061651379653930220729 := by
  unfold tailWord_3515345
  simp only [CollatzResearch.WordTrace]
  refine ⟨128215165449512912972963489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85476776966341941981975659 128215165449512912972963489)
  ·
    refine ⟨96161374087134684729722617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128215165449512912972963489 96161374087134684729722617)
    ·
      refine ⟨72121030565351013547291963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96161374087134684729722617 72121030565351013547291963)
      ·
        refine ⟨108181545848026520320937945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72121030565351013547291963 108181545848026520320937945)
        ·
          refine ⟨81136159386019890240703459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108181545848026520320937945 81136159386019890240703459)
          ·
            refine ⟨121704239079029835361055189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81136159386019890240703459 121704239079029835361055189)
            ·
              refine ⟨2852443103414761766274731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 121704239079029835361055189 2852443103414761766274731)
              ·
                refine ⟨4278664655122142649412097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2852443103414761766274731 4278664655122142649412097)
                ·
                  refine ⟨3208998491341606987059073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4278664655122142649412097 3208998491341606987059073)
                  ·
                    refine ⟨2406748868506205240294305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3208998491341606987059073 2406748868506205240294305)
                    ·
                      refine ⟨1805061651379653930220729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2406748868506205240294305 1805061651379653930220729)
                      ·
                        rfl

theorem cell23_3515345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 7, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 7, 1, 2, 2, 2].length) (baseStart_3515345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3515345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3515345 prefixEnd_3515345 := by exact prefixLift 3515345
  have htrace : WordTrace (prefixWord ++ tailWord_3515345) baseStart_3515345 baseEnd_3515345 := by
    simpa [prefixWord, tailWord_3515345, baseEnd_3515345] using wordTrace_append hprefix tailTrace_3515345
  have hstable : (prefixWord ++ tailWord_3515345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3515345).length < 2 ^ (prefixWord ++ tailWord_3515345).sum := by decide
  have hdescent : baseEnd_3515345 < baseStart_3515345 := by decide
  rcases family_descends (prefixWord ++ tailWord_3515345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3515401 : List Nat := [1, 2, 1, 1, 3, 1, 1, 5, 2, 4, 2]
def baseStart_3515401 : Nat := 118140960795 + 3515401 * 2 ^ 59
def prefixEnd_3515401 : Nat := 4983230072969 + 3 ^ 40 * 3515401 * 2
def baseEnd_3515401 : Nat := 1805090406296305711120471

theorem tailTrace_3515401 : CollatzResearch.WordTrace tailWord_3515401 prefixEnd_3515401 1805090406296305711120471 := by
  unfold tailWord_3515401
  simp only [CollatzResearch.WordTrace]
  refine ⟨128217207937310034537002057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85478138624873356358001371 128217207937310034537002057)
  ·
    refine ⟨96162905952982525902751543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128217207937310034537002057 96162905952982525902751543)
    ·
      refine ⟨144244358929473788854127315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96162905952982525902751543 144244358929473788854127315)
      ·
        refine ⟨216366538394210683281190973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144244358929473788854127315 216366538394210683281190973)
        ·
          refine ⟨81137451897829006230446615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 216366538394210683281190973 81137451897829006230446615)
          ·
            refine ⟨121706177846743509345669923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81137451897829006230446615 121706177846743509345669923)
            ·
              refine ⟨182559266770115264018504885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121706177846743509345669923 182559266770115264018504885)
              ·
                refine ⟨17114931259698306001734833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 182559266770115264018504885 17114931259698306001734833)
                ·
                  refine ⟨12836198444773729501301125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17114931259698306001734833 12836198444773729501301125)
                  ·
                    refine ⟨2406787208395074281493961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12836198444773729501301125 2406787208395074281493961)
                    ·
                      refine ⟨1805090406296305711120471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2406787208395074281493961 1805090406296305711120471)
                      ·
                        rfl

theorem cell23_3515401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 5, 2, 4, 2].length) (baseStart_3515401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3515401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3515401 prefixEnd_3515401 := by exact prefixLift 3515401
  have htrace : WordTrace (prefixWord ++ tailWord_3515401) baseStart_3515401 baseEnd_3515401 := by
    simpa [prefixWord, tailWord_3515401, baseEnd_3515401] using wordTrace_append hprefix tailTrace_3515401
  have hstable : (prefixWord ++ tailWord_3515401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3515401).length < 2 ^ (prefixWord ++ tailWord_3515401).sum := by decide
  have hdescent : baseEnd_3515401 < baseStart_3515401 := by decide
  rcases family_descends (prefixWord ++ tailWord_3515401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3515438 : List Nat := [4, 1, 3, 1, 1, 1, 1, 4, 2, 2, 3]
def baseStart_3515438 : Nat := 118140960795 + 3515438 * 2 ^ 59
def prefixEnd_3515438 : Nat := 4983230072969 + 3 ^ 40 * 3515438 * 2
def baseEnd_3515438 : Nat := 1805109405080522066357801

theorem tailTrace_3515438 : CollatzResearch.WordTrace tailWord_3515438 prefixEnd_3515438 1805109405080522066357801 := by
  unfold tailWord_3515438
  simp only [CollatzResearch.WordTrace]
  refine ⟨16027319679771998732012371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85479038292117326570732645 16027319679771998732012371)
  ·
    refine ⟨24040979519657998098018557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16027319679771998732012371 24040979519657998098018557)
    ·
      refine ⟨9015367319871749286756959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24040979519657998098018557 9015367319871749286756959)
      ·
        refine ⟨13523050979807623930135439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9015367319871749286756959 13523050979807623930135439)
        ·
          refine ⟨20284576469711435895203159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13523050979807623930135439 20284576469711435895203159)
          ·
            refine ⟨30426864704567153842804739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20284576469711435895203159 30426864704567153842804739)
            ·
              refine ⟨45640297056850730764207109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30426864704567153842804739 45640297056850730764207109)
              ·
                refine ⟨8557555698159512018288833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45640297056850730764207109 8557555698159512018288833)
                ·
                  refine ⟨6418166773619634013716625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8557555698159512018288833 6418166773619634013716625)
                  ·
                    refine ⟨4813625080214725510287469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6418166773619634013716625 4813625080214725510287469)
                    ·
                      refine ⟨1805109405080522066357801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4813625080214725510287469 1805109405080522066357801)
                      ·
                        rfl

theorem cell23_3515438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 4, 2, 2, 3].length) (baseStart_3515438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3515438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3515438 prefixEnd_3515438 := by exact prefixLift 3515438
  have htrace : WordTrace (prefixWord ++ tailWord_3515438) baseStart_3515438 baseEnd_3515438 := by
    simpa [prefixWord, tailWord_3515438, baseEnd_3515438] using wordTrace_append hprefix tailTrace_3515438
  have hstable : (prefixWord ++ tailWord_3515438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3515438).length < 2 ^ (prefixWord ++ tailWord_3515438).sum := by decide
  have hdescent : baseEnd_3515438 < baseStart_3515438 := by decide
  rcases family_descends (prefixWord ++ tailWord_3515438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3515441 : List Nat := [1, 2, 2, 3, 1, 2, 4, 2, 6]
def baseStart_3515441 : Nat := 118140960795 + 3515441 * 2 ^ 59
def prefixEnd_3515441 : Nat := 4983230072969 + 3 ^ 40 * 3515441 * 2
def baseEnd_3515441 : Nat := 200567882835831728291143

theorem tailTrace_3515441 : CollatzResearch.WordTrace tailWord_3515441 prefixEnd_3515441 200567882835831728291143 := by
  unfold tailWord_3515441
  simp only [CollatzResearch.WordTrace]
  refine ⟨128218666857165121368458177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85479111238110080912305451 128218666857165121368458177)
  ·
    refine ⟨96164000142873841026343633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128218666857165121368458177 96164000142873841026343633)
    ·
      refine ⟨72123000107155380769757725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96164000142873841026343633 72123000107155380769757725)
      ·
        refine ⟨27046125040183267788659147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72123000107155380769757725 27046125040183267788659147)
        ·
          refine ⟨40569187560274901682988721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27046125040183267788659147 40569187560274901682988721)
          ·
            refine ⟨30426890670206176262241541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40569187560274901682988721 30426890670206176262241541)
            ·
              refine ⟨5705042000663658049170289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30426890670206176262241541 5705042000663658049170289)
              ·
                refine ⟨4278781500497743536877717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5705042000663658049170289 4278781500497743536877717)
                ·
                  refine ⟨200567882835831728291143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4278781500497743536877717 200567882835831728291143)
                  ·
                    rfl

theorem cell23_3515441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4, 2, 6].length) (baseStart_3515441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3515441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3515441 prefixEnd_3515441 := by exact prefixLift 3515441
  have htrace : WordTrace (prefixWord ++ tailWord_3515441) baseStart_3515441 baseEnd_3515441 := by
    simpa [prefixWord, tailWord_3515441, baseEnd_3515441] using wordTrace_append hprefix tailTrace_3515441
  have hstable : (prefixWord ++ tailWord_3515441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3515441).length < 2 ^ (prefixWord ++ tailWord_3515441).sum := by decide
  have hdescent : baseEnd_3515441 < baseStart_3515441 := by decide
  rcases family_descends (prefixWord ++ tailWord_3515441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3515464 : List Nat := [2, 1, 3, 1, 1, 1, 3, 1, 2, 1, 7]
def baseStart_3515464 : Nat := 118140960795 + 3515464 * 2 ^ 59
def prefixEnd_3515464 : Nat := 4983230072969 + 3 ^ 40 * 3515464 * 2
def baseEnd_3515464 : Nat := 1805122755577538964632681

theorem tailTrace_3515464 : CollatzResearch.WordTrace tailWord_3515464 prefixEnd_3515464 1805122755577538964632681 := by
  unfold tailWord_3515464
  simp only [CollatzResearch.WordTrace]
  refine ⟨64109752868040898148272723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85479670490721197531030297 64109752868040898148272723)
  ·
    refine ⟨96164629302061347222409085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64109752868040898148272723 96164629302061347222409085)
    ·
      refine ⟨36061735988273005208403407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96164629302061347222409085 36061735988273005208403407)
      ·
        refine ⟨54092603982409507812605111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36061735988273005208403407 54092603982409507812605111)
        ·
          refine ⟨81138905973614261718907667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54092603982409507812605111 81138905973614261718907667)
          ·
            refine ⟨121708358960421392578361501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81138905973614261718907667 121708358960421392578361501)
            ·
              refine ⟨45640634610158022216885563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 121708358960421392578361501 45640634610158022216885563)
              ·
                refine ⟨68460951915237033325328345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45640634610158022216885563 68460951915237033325328345)
                ·
                  refine ⟨51345713936427774993996259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68460951915237033325328345 51345713936427774993996259)
                  ·
                    refine ⟨77018570904641662490994389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51345713936427774993996259 77018570904641662490994389)
                    ·
                      refine ⟨1805122755577538964632681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 77018570904641662490994389 1805122755577538964632681)
                      ·
                        rfl

theorem cell23_3515464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 2, 1, 7].length) (baseStart_3515464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3515464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3515464 prefixEnd_3515464 := by exact prefixLift 3515464
  have htrace : WordTrace (prefixWord ++ tailWord_3515464) baseStart_3515464 baseEnd_3515464 := by
    simpa [prefixWord, tailWord_3515464, baseEnd_3515464] using wordTrace_append hprefix tailTrace_3515464
  have hstable : (prefixWord ++ tailWord_3515464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3515464).length < 2 ^ (prefixWord ++ tailWord_3515464).sum := by decide
  have hdescent : baseEnd_3515464 < baseStart_3515464 := by decide
  rcases family_descends (prefixWord ++ tailWord_3515464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3515502 : List Nat := [4, 1, 2, 2, 1, 2, 2, 4, 1, 1, 3]
def baseStart_3515502 : Nat := 118140960795 + 3515502 * 2 ^ 59
def prefixEnd_3515502 : Nat := 4983230072969 + 3 ^ 40 * 3515502 * 2
def baseEnd_3515502 : Nat := 1805142267842409815957507

theorem tailTrace_3515502 : CollatzResearch.WordTrace tailWord_3515502 prefixEnd_3515502 1805142267842409815957507 := by
  unfold tailWord_3515502
  simp only [CollatzResearch.WordTrace]
  refine ⟨16027611463743016098303595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85480594473296085857619173 16027611463743016098303595)
  ·
    refine ⟨24041417195614524147455393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16027611463743016098303595 24041417195614524147455393)
    ·
      refine ⟨18031062896710893110591545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24041417195614524147455393 18031062896710893110591545)
      ·
        refine ⟨13523297172533169832943659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18031062896710893110591545 13523297172533169832943659)
        ·
          refine ⟨20284945758799754749415489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13523297172533169832943659 20284945758799754749415489)
          ·
            refine ⟨15213709319099816062061617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20284945758799754749415489 15213709319099816062061617)
            ·
              refine ⟨11410281989324862046546213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15213709319099816062061617 11410281989324862046546213)
              ·
                refine ⟨2139427872998411633727415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11410281989324862046546213 2139427872998411633727415)
                ·
                  refine ⟨3209141809497617450591123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2139427872998411633727415 3209141809497617450591123)
                  ·
                    refine ⟨4813712714246426175886685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3209141809497617450591123 4813712714246426175886685)
                    ·
                      refine ⟨1805142267842409815957507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4813712714246426175886685 1805142267842409815957507)
                      ·
                        rfl

theorem cell23_3515502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 4, 1, 1, 3].length) (baseStart_3515502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3515502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3515502 prefixEnd_3515502 := by exact prefixLift 3515502
  have htrace : WordTrace (prefixWord ++ tailWord_3515502) baseStart_3515502 baseEnd_3515502 := by
    simpa [prefixWord, tailWord_3515502, baseEnd_3515502] using wordTrace_append hprefix tailTrace_3515502
  have hstable : (prefixWord ++ tailWord_3515502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3515502).length < 2 ^ (prefixWord ++ tailWord_3515502).sum := by decide
  have hdescent : baseEnd_3515502 < baseStart_3515502 := by decide
  rcases family_descends (prefixWord ++ tailWord_3515502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3515511 : List Nat := [1, 1, 3, 1, 1, 4, 3, 2, 1, 1, 5]
def baseStart_3515511 : Nat := 118140960795 + 3515511 * 2 ^ 59
def prefixEnd_3515511 : Nat := 4983230072969 + 3 ^ 40 * 3515511 * 2
def baseEnd_3515511 : Nat := 1805146889168300280744965

theorem tailTrace_3515511 : CollatzResearch.WordTrace tailWord_3515511 prefixEnd_3515511 1805146889168300280744965 := by
  unfold tailWord_3515511
  simp only [CollatzResearch.WordTrace]
  refine ⟨128221219966911523323506387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85480813311274348882337591 128221219966911523323506387)
  ·
    refine ⟨192331829950367284985259581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128221219966911523323506387 192331829950367284985259581)
    ·
      refine ⟨72124436231387731869472343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192331829950367284985259581 72124436231387731869472343)
      ·
        refine ⟨108186654347081597804208515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72124436231387731869472343 108186654347081597804208515)
        ·
          refine ⟨162279981520622396706312773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108186654347081597804208515 162279981520622396706312773)
          ·
            refine ⟨30427496535116699382433645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 162279981520622396706312773 30427496535116699382433645)
            ·
              refine ⟨11410311200668762268412617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30427496535116699382433645 11410311200668762268412617)
              ·
                refine ⟨8557733400501571701309463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11410311200668762268412617 8557733400501571701309463)
                ·
                  refine ⟨12836600100752357551964195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8557733400501571701309463 12836600100752357551964195)
                  ·
                    refine ⟨19254900151128536327946293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12836600100752357551964195 19254900151128536327946293)
                    ·
                      refine ⟨1805146889168300280744965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19254900151128536327946293 1805146889168300280744965)
                      ·
                        rfl

theorem cell23_3515511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 2, 1, 1, 5].length) (baseStart_3515511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3515511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3515511 prefixEnd_3515511 := by exact prefixLift 3515511
  have htrace : WordTrace (prefixWord ++ tailWord_3515511) baseStart_3515511 baseEnd_3515511 := by
    simpa [prefixWord, tailWord_3515511, baseEnd_3515511] using wordTrace_append hprefix tailTrace_3515511
  have hstable : (prefixWord ++ tailWord_3515511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3515511).length < 2 ^ (prefixWord ++ tailWord_3515511).sum := by decide
  have hdescent : baseEnd_3515511 < baseStart_3515511 := by decide
  rcases family_descends (prefixWord ++ tailWord_3515511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3515525 : List Nat := [1, 3, 1, 1, 6, 1, 2, 2, 1, 1, 4]
def baseStart_3515525 : Nat := 118140960795 + 3515525 * 2 ^ 59
def prefixEnd_3515525 : Nat := 4983230072969 + 3 ^ 40 * 3515525 * 2
def baseEnd_3515525 : Nat := 1805154077897463225969901

theorem tailTrace_3515525 : CollatzResearch.WordTrace tailWord_3515525 prefixEnd_3515525 1805154077897463225969901 := by
  unfold tailWord_3515525
  simp only [CollatzResearch.WordTrace]
  refine ⟨128221730588860803714516029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85481153725907202476344019 128221730588860803714516029)
  ·
    refine ⟨48083148970822801392943511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128221730588860803714516029 48083148970822801392943511)
    ·
      refine ⟨72124723456234202089415267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48083148970822801392943511 72124723456234202089415267)
      ·
        refine ⟨108187085184351303134122901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72124723456234202089415267 108187085184351303134122901)
        ·
          refine ⟨5071269618016467334412011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 108187085184351303134122901 5071269618016467334412011)
          ·
            refine ⟨7606904427024701001618017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5071269618016467334412011 7606904427024701001618017)
            ·
              refine ⟨5705178320268525751213513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7606904427024701001618017 5705178320268525751213513)
              ·
                refine ⟨4278883740201394313410135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5705178320268525751213513 4278883740201394313410135)
                ·
                  refine ⟨6418325610302091470115203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4278883740201394313410135 6418325610302091470115203)
                  ·
                    refine ⟨9627488415453137205172805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6418325610302091470115203 9627488415453137205172805)
                    ·
                      refine ⟨1805154077897463225969901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9627488415453137205172805 1805154077897463225969901)
                      ·
                        rfl

theorem cell23_3515525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 2, 2, 1, 1, 4].length) (baseStart_3515525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3515525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3515525 prefixEnd_3515525 := by exact prefixLift 3515525
  have htrace : WordTrace (prefixWord ++ tailWord_3515525) baseStart_3515525 baseEnd_3515525 := by
    simpa [prefixWord, tailWord_3515525, baseEnd_3515525] using wordTrace_append hprefix tailTrace_3515525
  have hstable : (prefixWord ++ tailWord_3515525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3515525).length < 2 ^ (prefixWord ++ tailWord_3515525).sum := by decide
  have hdescent : baseEnd_3515525 < baseStart_3515525 := by decide
  rcases family_descends (prefixWord ++ tailWord_3515525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3515559 : List Nat := [1, 1, 6, 2, 1, 3, 1, 1, 3, 2, 2]
def baseStart_3515559 : Nat := 118140960795 + 3515559 * 2 ^ 59
def prefixEnd_3515559 : Nat := 4983230072969 + 3 ^ 40 * 3515559 * 2
def baseEnd_3515559 : Nat := 1805171536239716092944745

theorem tailTrace_3515559 : CollatzResearch.WordTrace tailWord_3515559 prefixEnd_3515559 1805171536239716092944745 := by
  unfold tailWord_3515559
  simp only [CollatzResearch.WordTrace]
  refine ⟨128222970670737627521253731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85481980447158418347502487 128222970670737627521253731)
  ·
    refine ⟨192334456006106441281880597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128222970670737627521253731 192334456006106441281880597)
    ·
      refine ⟨9015677625286239435088153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 192334456006106441281880597 9015677625286239435088153)
      ·
        refine ⟨6761758218964679576316115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9015677625286239435088153 6761758218964679576316115)
        ·
          refine ⟨10142637328447019364474173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6761758218964679576316115 10142637328447019364474173)
          ·
            refine ⟨3803488998167632261677815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10142637328447019364474173 3803488998167632261677815)
            ·
              refine ⟨5705233497251448392516723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3803488998167632261677815 5705233497251448392516723)
              ·
                refine ⟨8557850245877172588775085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5705233497251448392516723 8557850245877172588775085)
                ·
                  refine ⟨3209193842203939720790657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8557850245877172588775085 3209193842203939720790657)
                  ·
                    refine ⟨2406895381652954790592993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3209193842203939720790657 2406895381652954790592993)
                    ·
                      refine ⟨1805171536239716092944745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2406895381652954790592993 1805171536239716092944745)
                      ·
                        rfl

theorem cell23_3515559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 1, 1, 3, 2, 2].length) (baseStart_3515559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3515559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3515559 prefixEnd_3515559 := by exact prefixLift 3515559
  have htrace : WordTrace (prefixWord ++ tailWord_3515559) baseStart_3515559 baseEnd_3515559 := by
    simpa [prefixWord, tailWord_3515559, baseEnd_3515559] using wordTrace_append hprefix tailTrace_3515559
  have hstable : (prefixWord ++ tailWord_3515559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3515559).length < 2 ^ (prefixWord ++ tailWord_3515559).sum := by decide
  have hdescent : baseEnd_3515559 < baseStart_3515559 := by decide
  rcases family_descends (prefixWord ++ tailWord_3515559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3515568 : List Nat := [2, 1, 1, 1, 2, 1, 2, 3, 5, 3, 2]
def baseStart_3515568 : Nat := 118140960795 + 3515568 * 2 ^ 59
def prefixEnd_3515568 : Nat := 4983230072969 + 3 ^ 40 * 3515568 * 2
def baseEnd_3515568 : Nat := 1805176157565606557732203

theorem tailTrace_3515568 : CollatzResearch.WordTrace tailWord_3515568 prefixEnd_3515568 1805176157565606557732203 := by
  unfold tailWord_3515568
  simp only [CollatzResearch.WordTrace]
  refine ⟨64111649463852511029165679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85482199285136681372220905 64111649463852511029165679)
  ·
    refine ⟨96167474195778766543748519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64111649463852511029165679 96167474195778766543748519)
    ·
      refine ⟨144251211293668149815622779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96167474195778766543748519 144251211293668149815622779)
      ·
        refine ⟨216376816940502224723434169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144251211293668149815622779 216376816940502224723434169)
        ·
          refine ⟨162282612705376668542575627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216376816940502224723434169 162282612705376668542575627)
          ·
            refine ⟨243423919058065002813863441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162282612705376668542575627 243423919058065002813863441)
            ·
              refine ⟨182567939293548752110397581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 243423919058065002813863441 182567939293548752110397581)
              ·
                refine ⟨68462977235080782041399093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 182567939293548752110397581 68462977235080782041399093)
                ·
                  refine ⟨6418404115788823316381165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68462977235080782041399093 6418404115788823316381165)
                  ·
                    refine ⟨2406901543420808743642937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6418404115788823316381165 2406901543420808743642937)
                    ·
                      refine ⟨1805176157565606557732203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2406901543420808743642937 1805176157565606557732203)
                      ·
                        rfl

theorem cell23_3515568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 5, 3, 2].length) (baseStart_3515568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3515568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3515568 prefixEnd_3515568 := by exact prefixLift 3515568
  have htrace : WordTrace (prefixWord ++ tailWord_3515568) baseStart_3515568 baseEnd_3515568 := by
    simpa [prefixWord, tailWord_3515568, baseEnd_3515568] using wordTrace_append hprefix tailTrace_3515568
  have hstable : (prefixWord ++ tailWord_3515568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3515568).length < 2 ^ (prefixWord ++ tailWord_3515568).sum := by decide
  have hdescent : baseEnd_3515568 < baseStart_3515568 := by decide
  rcases family_descends (prefixWord ++ tailWord_3515568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3515575 : List Nat := [1, 1, 3, 1, 4, 1, 3, 3, 2, 1, 3]
def baseStart_3515575 : Nat := 118140960795 + 3515575 * 2 ^ 59
def prefixEnd_3515575 : Nat := 4983230072969 + 3 ^ 40 * 3515575 * 2
def baseEnd_3515575 : Nat := 1805179751930188030344671

theorem tailTrace_3515575 : CollatzResearch.WordTrace tailWord_3515575 prefixEnd_3515575 1805179751930188030344671 := by
  unfold tailWord_3515575
  simp only [CollatzResearch.WordTrace]
  refine ⟨128223554238679662253836179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85482369492453108169224119 128223554238679662253836179)
  ·
    refine ⟨192335331358019493380754269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128223554238679662253836179 192335331358019493380754269)
    ·
      refine ⟨72125749259257310017782851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192335331358019493380754269 72125749259257310017782851)
      ·
        refine ⟨108188623888885965026674277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72125749259257310017782851 108188623888885965026674277)
        ·
          refine ⟨20285366979166118442501427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108188623888885965026674277 20285366979166118442501427)
          ·
            refine ⟨30428050468749177663752141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20285366979166118442501427 30428050468749177663752141)
            ·
              refine ⟨11410518925780941623907053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30428050468749177663752141 11410518925780941623907053)
              ·
                refine ⟨4278944597167853108965145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11410518925780941623907053 4278944597167853108965145)
                ·
                  refine ⟨3209208447875889831723859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4278944597167853108965145 3209208447875889831723859)
                  ·
                    refine ⟨4813812671813834747585789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3209208447875889831723859 4813812671813834747585789)
                    ·
                      refine ⟨1805179751930188030344671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4813812671813834747585789 1805179751930188030344671)
                      ·
                        rfl

theorem cell23_3515575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 3, 2, 1, 3].length) (baseStart_3515575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3515575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3515575 prefixEnd_3515575 := by exact prefixLift 3515575
  have htrace : WordTrace (prefixWord ++ tailWord_3515575) baseStart_3515575 baseEnd_3515575 := by
    simpa [prefixWord, tailWord_3515575, baseEnd_3515575] using wordTrace_append hprefix tailTrace_3515575
  have hstable : (prefixWord ++ tailWord_3515575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3515575).length < 2 ^ (prefixWord ++ tailWord_3515575).sum := by decide
  have hdescent : baseEnd_3515575 < baseStart_3515575 := by decide
  rcases family_descends (prefixWord ++ tailWord_3515575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3515615 : List Nat := [1, 1, 2, 3, 2, 1, 2, 3, 4, 2, 2]
def baseStart_3515615 : Nat := 118140960795 + 3515615 * 2 ^ 59
def prefixEnd_3515615 : Nat := 4983230072969 + 3 ^ 40 * 3515615 * 2
def baseEnd_3515615 : Nat := 1805200291156367873844487

theorem tailTrace_3515615 : CollatzResearch.WordTrace tailWord_3515615 prefixEnd_3515615 1805200291156367873844487 := by
  unfold tailWord_3515615
  simp only [CollatzResearch.WordTrace]
  refine ⟨128225013158534749085292299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85483342105689832723528199 128225013158534749085292299)
  ·
    refine ⟨192337519737802123627938449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128225013158534749085292299 192337519737802123627938449)
    ·
      refine ⟨144253139803351592720953837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192337519737802123627938449 144253139803351592720953837)
      ·
        refine ⟨54094927426256847270357689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144253139803351592720953837 54094927426256847270357689)
        ·
          refine ⟨40571195569692635452768267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54094927426256847270357689 40571195569692635452768267)
          ·
            refine ⟨60856793354538953179152401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40571195569692635452768267 60856793354538953179152401)
            ·
              refine ⟨45642595015904214884364301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60856793354538953179152401 45642595015904214884364301)
              ·
                refine ⟨17115973130964080581636613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45642595015904214884364301 17115973130964080581636613)
                ·
                  refine ⟨3209244962055765109056865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17115973130964080581636613 3209244962055765109056865)
                  ·
                    refine ⟨2406933721541823831792649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3209244962055765109056865 2406933721541823831792649)
                    ·
                      refine ⟨1805200291156367873844487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2406933721541823831792649 1805200291156367873844487)
                      ·
                        rfl

theorem cell23_3515615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 3, 4, 2, 2].length) (baseStart_3515615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3515615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3515615 prefixEnd_3515615 := by exact prefixLift 3515615
  have htrace : WordTrace (prefixWord ++ tailWord_3515615) baseStart_3515615 baseEnd_3515615 := by
    simpa [prefixWord, tailWord_3515615, baseEnd_3515615] using wordTrace_append hprefix tailTrace_3515615
  have hstable : (prefixWord ++ tailWord_3515615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3515615).length < 2 ^ (prefixWord ++ tailWord_3515615).sum := by decide
  have hdescent : baseEnd_3515615 < baseStart_3515615 := by decide
  rcases family_descends (prefixWord ++ tailWord_3515615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3515628 : List Nat := [2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 4]
def baseStart_3515628 : Nat := 118140960795 + 3515628 * 2 ^ 59
def prefixEnd_3515628 : Nat := 4983230072969 + 3 ^ 40 * 3515628 * 2
def baseEnd_3515628 : Nat := 1805206966404876322981927

theorem tailTrace_3515628 : CollatzResearch.WordTrace tailWord_3515628 prefixEnd_3515628 1805206966404876322981927 := by
  unfold tailWord_3515628
  simp only [CollatzResearch.WordTrace]
  refine ⟨64112743653743826152757769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85483658204991768203677025 64112743653743826152757769)
  ·
    refine ⟨48084557740307869614568327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64112743653743826152757769 48084557740307869614568327)
    ·
      refine ⟨72126836610461804421852491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48084557740307869614568327 72126836610461804421852491)
      ·
        refine ⟨108190254915692706632778737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72126836610461804421852491 108190254915692706632778737)
        ·
          refine ⟨81142691186769529974584053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108190254915692706632778737 81142691186769529974584053)
          ·
            refine ⟨7607127298759643435117255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 81142691186769529974584053 7607127298759643435117255)
            ·
              refine ⟨11410690948139465152675883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7607127298759643435117255 11410690948139465152675883)
              ·
                refine ⟨17116036422209197729013825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11410690948139465152675883 17116036422209197729013825)
                ·
                  refine ⟨12837027316656898296760369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17116036422209197729013825 12837027316656898296760369)
                  ·
                    refine ⟨9627770487492673722570277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12837027316656898296760369 9627770487492673722570277)
                    ·
                      refine ⟨1805206966404876322981927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9627770487492673722570277 1805206966404876322981927)
                      ·
                        rfl

theorem cell23_3515628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 4].length) (baseStart_3515628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3515628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3515628 prefixEnd_3515628 := by exact prefixLift 3515628
  have htrace : WordTrace (prefixWord ++ tailWord_3515628) baseStart_3515628 baseEnd_3515628 := by
    simpa [prefixWord, tailWord_3515628, baseEnd_3515628] using wordTrace_append hprefix tailTrace_3515628
  have hstable : (prefixWord ++ tailWord_3515628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3515628).length < 2 ^ (prefixWord ++ tailWord_3515628).sum := by decide
  have hdescent : baseEnd_3515628 < baseStart_3515628 := by decide
  rcases family_descends (prefixWord ++ tailWord_3515628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3515666 : List Nat := [3, 2, 4, 2, 1, 1, 1, 1, 4, 2, 2]
def baseStart_3515666 : Nat := 118140960795 + 3515666 * 2 ^ 59
def prefixEnd_3515666 : Nat := 4983230072969 + 3 ^ 40 * 3515666 * 2
def baseEnd_3515666 : Nat := 1805226478669747174306753

theorem tailTrace_3515666 : CollatzResearch.WordTrace tailWord_3515666 prefixEnd_3515666 1805226478669747174306753 := by
  unfold tailWord_3515666
  simp only [CollatzResearch.WordTrace]
  refine ⟨32056718320337496198849713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85484582187566656530265901 32056718320337496198849713)
  ·
    refine ⟨24042538740253122149137285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32056718320337496198849713 24042538740253122149137285)
    ·
      refine ⟨4507976013797460402963241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24042538740253122149137285 4507976013797460402963241)
      ·
        refine ⟨3380982010348095302222431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4507976013797460402963241 3380982010348095302222431)
        ·
          refine ⟨5071473015522142953333647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3380982010348095302222431 5071473015522142953333647)
          ·
            refine ⟨7607209523283214430000471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5071473015522142953333647 7607209523283214430000471)
            ·
              refine ⟨11410814284924821645000707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7607209523283214430000471 11410814284924821645000707)
              ·
                refine ⟨17116221427387232467501061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11410814284924821645000707 17116221427387232467501061)
                ·
                  refine ⟨3209291517635106087656449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17116221427387232467501061 3209291517635106087656449)
                  ·
                    refine ⟨2406968638226329565742337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3209291517635106087656449 2406968638226329565742337)
                    ·
                      refine ⟨1805226478669747174306753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2406968638226329565742337 1805226478669747174306753)
                      ·
                        rfl

theorem cell23_3515666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_3515666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3515666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3515666 prefixEnd_3515666 := by exact prefixLift 3515666
  have htrace : WordTrace (prefixWord ++ tailWord_3515666) baseStart_3515666 baseEnd_3515666 := by
    simpa [prefixWord, tailWord_3515666, baseEnd_3515666] using wordTrace_append hprefix tailTrace_3515666
  have hstable : (prefixWord ++ tailWord_3515666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3515666).length < 2 ^ (prefixWord ++ tailWord_3515666).sum := by decide
  have hdescent : baseEnd_3515666 < baseStart_3515666 := by decide
  rcases family_descends (prefixWord ++ tailWord_3515666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3515691 : List Nat := [1, 1, 1, 1, 2, 1, 2, 1, 3, 5, 5]
def baseStart_3515691 : Nat := 118140960795 + 3515691 * 2 ^ 59
def prefixEnd_3515691 : Nat := 4983230072969 + 3 ^ 40 * 3515691 * 2
def baseEnd_3515691 : Nat := 1805239315686109576494137

theorem tailTrace_3515691 : CollatzResearch.WordTrace tailWord_3515691 prefixEnd_3515691 1805239315686109576494137 := by
  unfold tailWord_3515691
  simp only [CollatzResearch.WordTrace]
  refine ⟨128227785106259414065058927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85485190070839609376705951 128227785106259414065058927)
  ·
    refine ⟨192341677659389121097588391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128227785106259414065058927 192341677659389121097588391)
    ·
      refine ⟨288512516489083681646382587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192341677659389121097588391 288512516489083681646382587)
      ·
        refine ⟨432768774733625522469573881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288512516489083681646382587 432768774733625522469573881)
        ·
          refine ⟨324576581050219141852180411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 432768774733625522469573881 324576581050219141852180411)
          ·
            refine ⟨486864871575328712778270617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 324576581050219141852180411 486864871575328712778270617)
            ·
              refine ⟨365148653681496534583702963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 486864871575328712778270617 365148653681496534583702963)
              ·
                refine ⟨547722980522244801875554445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 365148653681496534583702963 547722980522244801875554445)
                ·
                  refine ⟨205396117695841800703332917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 547722980522244801875554445 205396117695841800703332917)
                  ·
                    refine ⟨19255886033985168815937461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 205396117695841800703332917 19255886033985168815937461)
                    ·
                      refine ⟨1805239315686109576494137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19255886033985168815937461 1805239315686109576494137)
                      ·
                        rfl

theorem cell23_3515691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 5, 5].length) (baseStart_3515691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3515691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3515691 prefixEnd_3515691 := by exact prefixLift 3515691
  have htrace : WordTrace (prefixWord ++ tailWord_3515691) baseStart_3515691 baseEnd_3515691 := by
    simpa [prefixWord, tailWord_3515691, baseEnd_3515691] using wordTrace_append hprefix tailTrace_3515691
  have hstable : (prefixWord ++ tailWord_3515691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3515691).length < 2 ^ (prefixWord ++ tailWord_3515691).sum := by decide
  have hdescent : baseEnd_3515691 < baseStart_3515691 := by decide
  rcases family_descends (prefixWord ++ tailWord_3515691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3515728 : List Nat := [2, 1, 1, 1, 1, 5, 2, 4, 6]
def baseStart_3515728 : Nat := 118140960795 + 3515728 * 2 ^ 59
def prefixEnd_3515728 : Nat := 4983230072969 + 3 ^ 40 * 3515728 * 2
def baseEnd_3515728 : Nat := 200584257163369547970163

theorem tailTrace_3515728 : CollatzResearch.WordTrace tailWord_3515728 prefixEnd_3515728 200584257163369547970163 := by
  unfold tailWord_3515728
  simp only [CollatzResearch.WordTrace]
  refine ⟨64114567303562684692077919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85486089738083579589437225 64114567303562684692077919)
  ·
    refine ⟨96171850955344027038116879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64114567303562684692077919 96171850955344027038116879)
    ·
      refine ⟨144257776433016040557175319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96171850955344027038116879 144257776433016040557175319)
      ·
        refine ⟨216386664649524060835762979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144257776433016040557175319 216386664649524060835762979)
        ·
          refine ⟨324579996974286091253644469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216386664649524060835762979 324579996974286091253644469)
          ·
            refine ⟨30429374716339321055029169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 324579996974286091253644469 30429374716339321055029169)
            ·
              refine ⟨22822031037254490791271877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30429374716339321055029169 22822031037254490791271877)
              ·
                refine ⟨4279130819485217023363477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22822031037254490791271877 4279130819485217023363477)
                ·
                  refine ⟨200584257163369547970163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4279130819485217023363477 200584257163369547970163)
                  ·
                    rfl

theorem cell23_3515728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 4, 6].length) (baseStart_3515728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3515728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3515728 prefixEnd_3515728 := by exact prefixLift 3515728
  have htrace : WordTrace (prefixWord ++ tailWord_3515728) baseStart_3515728 baseEnd_3515728 := by
    simpa [prefixWord, tailWord_3515728, baseEnd_3515728] using wordTrace_append hprefix tailTrace_3515728
  have hstable : (prefixWord ++ tailWord_3515728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3515728).length < 2 ^ (prefixWord ++ tailWord_3515728).sum := by decide
  have hdescent : baseEnd_3515728 < baseStart_3515728 := by decide
  rcases family_descends (prefixWord ++ tailWord_3515728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3515734 : List Nat := [5, 2, 3, 1, 2, 1, 2, 1, 2, 2, 2]
def baseStart_3515734 : Nat := 118140960795 + 3515734 * 2 ^ 59
def prefixEnd_3515734 : Nat := 4983230072969 + 3 ^ 40 * 3515734 * 2
def baseEnd_3515734 : Nat := 1805261395354252908256441

theorem tailTrace_3515734 : CollatzResearch.WordTrace tailWord_3515734 prefixEnd_3515734 1805261395354252908256441 := by
  unfold tailWord_3515734
  simp only [CollatzResearch.WordTrace]
  refine ⟨8014334590318977025554641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 85486235630069088272582837 8014334590318977025554641)
  ·
    refine ⟨6010750942739232769165981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8014334590318977025554641 6010750942739232769165981)
    ·
      refine ⟨2254031603527212288437243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6010750942739232769165981 2254031603527212288437243)
      ·
        refine ⟨3381047405290818432655865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2254031603527212288437243 3381047405290818432655865)
        ·
          refine ⟨2535785553968113824491899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3381047405290818432655865 2535785553968113824491899)
          ·
            refine ⟨3803678330952170736737849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2535785553968113824491899 3803678330952170736737849)
            ·
              refine ⟨2852758748214128052553387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3803678330952170736737849 2852758748214128052553387)
              ·
                refine ⟨4279138122321192078830081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2852758748214128052553387 4279138122321192078830081)
                ·
                  refine ⟨3209353591740894059122561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4279138122321192078830081 3209353591740894059122561)
                  ·
                    refine ⟨2407015193805670544341921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3209353591740894059122561 2407015193805670544341921)
                    ·
                      refine ⟨1805261395354252908256441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2407015193805670544341921 1805261395354252908256441)
                      ·
                        rfl

theorem cell23_3515734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_3515734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3515734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3515734 prefixEnd_3515734 := by exact prefixLift 3515734
  have htrace : WordTrace (prefixWord ++ tailWord_3515734) baseStart_3515734 baseEnd_3515734 := by
    simpa [prefixWord, tailWord_3515734, baseEnd_3515734] using wordTrace_append hprefix tailTrace_3515734
  have hstable : (prefixWord ++ tailWord_3515734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3515734).length < 2 ^ (prefixWord ++ tailWord_3515734).sum := by decide
  have hdescent : baseEnd_3515734 < baseStart_3515734 := by decide
  rcases family_descends (prefixWord ++ tailWord_3515734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3515788 : List Nat := [2, 2, 1, 2, 1, 3, 1, 2, 3, 6]
def baseStart_3515788 : Nat := 118140960795 + 3515788 * 2 ^ 59
def prefixEnd_3515788 : Nat := 4983230072969 + 3 ^ 40 * 3515788 * 2
def baseEnd_3515788 : Nat := 601763041103198565660397

theorem tailTrace_3515788 : CollatzResearch.WordTrace tailWord_3515788 prefixEnd_3515788 601763041103198565660397 := by
  unfold tailWord_3515788
  simp only [CollatzResearch.WordTrace]
  refine ⟨64115661493453999815670009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85487548657938666420893345 64115661493453999815670009)
  ·
    refine ⟨48086746120090499861752507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64115661493453999815670009 48086746120090499861752507)
    ·
      refine ⟨72130119180135749792628761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48086746120090499861752507 72130119180135749792628761)
      ·
        refine ⟨54097589385101812344471571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72130119180135749792628761 54097589385101812344471571)
        ·
          refine ⟨81146384077652718516707357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54097589385101812344471571 81146384077652718516707357)
          ·
            refine ⟨30429894029119769443765259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81146384077652718516707357 30429894029119769443765259)
            ·
              refine ⟨45644841043679654165647889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30429894029119769443765259 45644841043679654165647889)
              ·
                refine ⟨34233630782759740624235917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45644841043679654165647889 34233630782759740624235917)
                ·
                  refine ⟨12837611543534902734088469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34233630782759740624235917 12837611543534902734088469)
                  ·
                    refine ⟨601763041103198565660397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12837611543534902734088469 601763041103198565660397)
                    ·
                      rfl

theorem cell23_3515788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 2, 3, 6].length) (baseStart_3515788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3515788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3515788 prefixEnd_3515788 := by exact prefixLift 3515788
  have htrace : WordTrace (prefixWord ++ tailWord_3515788) baseStart_3515788 baseEnd_3515788 := by
    simpa [prefixWord, tailWord_3515788, baseEnd_3515788] using wordTrace_append hprefix tailTrace_3515788
  have hstable : (prefixWord ++ tailWord_3515788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3515788).length < 2 ^ (prefixWord ++ tailWord_3515788).sum := by decide
  have hdescent : baseEnd_3515788 < baseStart_3515788 := by decide
  rcases family_descends (prefixWord ++ tailWord_3515788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3515805 : List Nat := [1, 4, 2, 1, 3, 1, 1, 3, 1, 6]
def baseStart_3515805 : Nat := 118140960795 + 3515805 * 2 ^ 59
def prefixEnd_3515805 : Nat := 4983230072969 + 3 ^ 40 * 3515805 * 2
def baseEnd_3515805 : Nat := 601765950826907376822871

theorem tailTrace_3515805 : CollatzResearch.WordTrace tailWord_3515805 prefixEnd_3515805 601765950826907376822871 := by
  unfold tailWord_3515805
  simp only [CollatzResearch.WordTrace]
  refine ⟨128231943027846411534708869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85487962018564274356472579 128231943027846411534708869)
  ·
    refine ⟨24043489317721202162757913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128231943027846411534708869 24043489317721202162757913)
    ·
      refine ⟨18032616988290901622068435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24043489317721202162757913 18032616988290901622068435)
      ·
        refine ⟨27048925482436352433102653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18032616988290901622068435 27048925482436352433102653)
        ·
          refine ⟨10143347055913632162413495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27048925482436352433102653 10143347055913632162413495)
          ·
            refine ⟨15215020583870448243620243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10143347055913632162413495 15215020583870448243620243)
            ·
              refine ⟨22822530875805672365430365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15215020583870448243620243 22822530875805672365430365)
              ·
                refine ⟨8558449078427127137036387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22822530875805672365430365 8558449078427127137036387)
                ·
                  refine ⟨12837673617640690705554581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8558449078427127137036387 12837673617640690705554581)
                  ·
                    refine ⟨601765950826907376822871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12837673617640690705554581 601765950826907376822871)
                    ·
                      rfl

theorem cell23_3515805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 3, 1, 6].length) (baseStart_3515805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3515805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3515805 prefixEnd_3515805 := by exact prefixLift 3515805
  have htrace : WordTrace (prefixWord ++ tailWord_3515805) baseStart_3515805 baseEnd_3515805 := by
    simpa [prefixWord, tailWord_3515805, baseEnd_3515805] using wordTrace_append hprefix tailTrace_3515805
  have hstable : (prefixWord ++ tailWord_3515805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3515805).length < 2 ^ (prefixWord ++ tailWord_3515805).sum := by decide
  have hdescent : baseEnd_3515805 < baseStart_3515805 := by decide
  rcases family_descends (prefixWord ++ tailWord_3515805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3515806 : List Nat := [4, 3, 1, 2, 2, 1, 1, 2, 3, 1, 3]
def baseStart_3515806 : Nat := 118140960795 + 3515806 * 2 ^ 59
def prefixEnd_3515806 : Nat := 4983230072969 + 3 ^ 40 * 3515806 * 2
def baseEnd_3515806 : Nat := 1805298365961376626556109

theorem tailTrace_3515806 : CollatzResearch.WordTrace tailWord_3515806 prefixEnd_3515806 1805298365961376626556109 := by
  unfold tailWord_3515806
  simp only [CollatzResearch.WordTrace]
  refine ⟨16028997437605348588186909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85487986333895192470330181 16028997437605348588186909)
  ·
    refine ⟨6010874039102005720570091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16028997437605348588186909 6010874039102005720570091)
    ·
      refine ⟨9016311058653008580855137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6010874039102005720570091 9016311058653008580855137)
      ·
        refine ⟨6762233293989756435641353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9016311058653008580855137 6762233293989756435641353)
        ·
          refine ⟨5071674970492317326731015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6762233293989756435641353 5071674970492317326731015)
          ·
            refine ⟨7607512455738475990096523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5071674970492317326731015 7607512455738475990096523)
            ·
              refine ⟨11411268683607713985144785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7607512455738475990096523 11411268683607713985144785)
              ·
                refine ⟨8558451512705785488858589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11411268683607713985144785 8558451512705785488858589)
                ·
                  refine ⟨3209419317264669558321971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8558451512705785488858589 3209419317264669558321971)
                  ·
                    refine ⟨4814128975897004337482957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3209419317264669558321971 4814128975897004337482957)
                    ·
                      refine ⟨1805298365961376626556109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4814128975897004337482957 1805298365961376626556109)
                      ·
                        rfl

theorem cell23_3515806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_3515806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3515806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3515806 prefixEnd_3515806 := by exact prefixLift 3515806
  have htrace : WordTrace (prefixWord ++ tailWord_3515806) baseStart_3515806 baseEnd_3515806 := by
    simpa [prefixWord, tailWord_3515806, baseEnd_3515806] using wordTrace_append hprefix tailTrace_3515806
  have hstable : (prefixWord ++ tailWord_3515806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3515806).length < 2 ^ (prefixWord ++ tailWord_3515806).sum := by decide
  have hdescent : baseEnd_3515806 < baseStart_3515806 := by decide
  rcases family_descends (prefixWord ++ tailWord_3515806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3515825 : List Nat := [1, 2, 2, 4, 1, 1, 1, 4, 1, 2, 4]
def baseStart_3515825 : Nat := 118140960795 + 3515825 * 2 ^ 59
def prefixEnd_3515825 : Nat := 4983230072969 + 3 ^ 40 * 3515825 * 2
def baseEnd_3515825 : Nat := 1805308122093812052218521

theorem tailTrace_3515825 : CollatzResearch.WordTrace tailWord_3515825 prefixEnd_3515825 1805308122093812052218521 := by
  unfold tailWord_3515825
  simp only [CollatzResearch.WordTrace]
  refine ⟨128232672487773954950436929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85488448325182636633624619 128232672487773954950436929)
  ·
    refine ⟨96174504365830466212827697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128232672487773954950436929 96174504365830466212827697)
    ·
      refine ⟨72130878274372849659620773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96174504365830466212827697 72130878274372849659620773)
      ·
        refine ⟨13524539676444909311178895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72130878274372849659620773 13524539676444909311178895)
        ·
          refine ⟨20286809514667363966768343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13524539676444909311178895 20286809514667363966768343)
          ·
            refine ⟨30430214272001045950152515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20286809514667363966768343 30430214272001045950152515)
            ·
              refine ⟨45645321408001568925228773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30430214272001045950152515 45645321408001568925228773)
              ·
                refine ⟨8558497764000294173480395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45645321408001568925228773 8558497764000294173480395)
                ·
                  refine ⟨12837746646000441260220593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8558497764000294173480395 12837746646000441260220593)
                  ·
                    refine ⟨9628309984500330945165445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12837746646000441260220593 9628309984500330945165445)
                    ·
                      refine ⟨1805308122093812052218521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9628309984500330945165445 1805308122093812052218521)
                      ·
                        rfl

theorem cell23_3515825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_3515825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3515825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3515825 prefixEnd_3515825 := by exact prefixLift 3515825
  have htrace : WordTrace (prefixWord ++ tailWord_3515825) baseStart_3515825 baseEnd_3515825 := by
    simpa [prefixWord, tailWord_3515825, baseEnd_3515825] using wordTrace_append hprefix tailTrace_3515825
  have hstable : (prefixWord ++ tailWord_3515825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3515825).length < 2 ^ (prefixWord ++ tailWord_3515825).sum := by decide
  have hdescent : baseEnd_3515825 < baseStart_3515825 := by decide
  rcases family_descends (prefixWord ++ tailWord_3515825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3515829 : List Nat := [1, 3, 3, 2, 2, 1, 4, 1, 1, 1, 4]
def baseStart_3515829 : Nat := 118140960795 + 3515829 * 2 ^ 59
def prefixEnd_3515829 : Nat := 4983230072969 + 3 ^ 40 * 3515829 * 2
def baseEnd_3515829 : Nat := 1805310176016430036568503

theorem tailTrace_3515829 : CollatzResearch.WordTrace tailWord_3515829 prefixEnd_3515829 1805310176016430036568503 := by
  unfold tailWord_3515829
  simp only [CollatzResearch.WordTrace]
  refine ⟨128232818379759463633582541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85488545586506309089055027 128232818379759463633582541)
  ·
    refine ⟨48087306892409798862593453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128232818379759463633582541 48087306892409798862593453)
    ·
      refine ⟨18032740084653674573472545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48087306892409798862593453 18032740084653674573472545)
      ·
        refine ⟨13524555063490255930104409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18032740084653674573472545 13524555063490255930104409)
        ·
          refine ⟨10143416297617691947578307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13524555063490255930104409 10143416297617691947578307)
          ·
            refine ⟨15215124446426537921367461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10143416297617691947578307 15215124446426537921367461)
            ·
              refine ⟨2852835833704975860256399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15215124446426537921367461 2852835833704975860256399)
              ·
                refine ⟨4279253750557463790384599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2852835833704975860256399 4279253750557463790384599)
                ·
                  refine ⟨6418880625836195685576899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4279253750557463790384599 6418880625836195685576899)
                  ·
                    refine ⟨9628320938754293528365349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6418880625836195685576899 9628320938754293528365349)
                    ·
                      refine ⟨1805310176016430036568503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9628320938754293528365349 1805310176016430036568503)
                      ·
                        rfl

theorem cell23_3515829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 4, 1, 1, 1, 4].length) (baseStart_3515829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3515829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3515829 prefixEnd_3515829 := by exact prefixLift 3515829
  have htrace : WordTrace (prefixWord ++ tailWord_3515829) baseStart_3515829 baseEnd_3515829 := by
    simpa [prefixWord, tailWord_3515829, baseEnd_3515829] using wordTrace_append hprefix tailTrace_3515829
  have hstable : (prefixWord ++ tailWord_3515829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3515829).length < 2 ^ (prefixWord ++ tailWord_3515829).sum := by decide
  have hdescent : baseEnd_3515829 < baseStart_3515829 := by decide
  rcases family_descends (prefixWord ++ tailWord_3515829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3515875 : List Nat := [1, 1, 1, 6, 2, 1, 1, 1, 2, 2, 5]
def baseStart_3515875 : Nat := 118140960795 + 3515875 * 2 ^ 59
def prefixEnd_3515875 : Nat := 4983230072969 + 3 ^ 40 * 3515875 * 2
def baseEnd_3515875 : Nat := 1805333796126536856593291

theorem tailTrace_3515875 : CollatzResearch.WordTrace tailWord_3515875 prefixEnd_3515875 1805333796126536856593291 := by
  unfold tailWord_3515875
  simp only [CollatzResearch.WordTrace]
  refine ⟨128234496137592813489757079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85489664091728542326504719 128234496137592813489757079)
  ·
    refine ⟨192351744206389220234635619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128234496137592813489757079 192351744206389220234635619)
    ·
      refine ⟨288527616309583830351953429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192351744206389220234635619 288527616309583830351953429)
      ·
        refine ⟨13524732014511742047747817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 288527616309583830351953429 13524732014511742047747817)
        ·
          refine ⟨10143549010883806535810863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13524732014511742047747817 10143549010883806535810863)
          ·
            refine ⟨15215323516325709803716295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10143549010883806535810863 15215323516325709803716295)
            ·
              refine ⟨22822985274488564705574443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15215323516325709803716295 22822985274488564705574443)
              ·
                refine ⟨34234477911732847058361665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22822985274488564705574443 34234477911732847058361665)
                ·
                  refine ⟨25675858433799635293771249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34234477911732847058361665 25675858433799635293771249)
                  ·
                    refine ⟨19256893825349726470328437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25675858433799635293771249 19256893825349726470328437)
                    ·
                      refine ⟨1805333796126536856593291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19256893825349726470328437 1805333796126536856593291)
                      ·
                        rfl

theorem cell23_3515875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_3515875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3515875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3515875 prefixEnd_3515875 := by exact prefixLift 3515875
  have htrace : WordTrace (prefixWord ++ tailWord_3515875) baseStart_3515875 baseEnd_3515875 := by
    simpa [prefixWord, tailWord_3515875, baseEnd_3515875] using wordTrace_append hprefix tailTrace_3515875
  have hstable : (prefixWord ++ tailWord_3515875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3515875).length < 2 ^ (prefixWord ++ tailWord_3515875).sum := by decide
  have hdescent : baseEnd_3515875 < baseStart_3515875 := by decide
  rcases family_descends (prefixWord ++ tailWord_3515875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3515889 : List Nat := [1, 2, 2, 2, 3, 2, 2, 3, 1, 3, 2]
def baseStart_3515889 : Nat := 118140960795 + 3515889 * 2 ^ 59
def prefixEnd_3515889 : Nat := 4983230072969 + 3 ^ 40 * 3515889 * 2
def baseEnd_3515889 : Nat := 1805340984855699801818227

theorem tailTrace_3515889 : CollatzResearch.WordTrace tailWord_3515889 prefixEnd_3515889 1805340984855699801818227 := by
  unfold tailWord_3515889
  simp only [CollatzResearch.WordTrace]
  refine ⟨128235006759542093880766721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85490004506361395920511147 128235006759542093880766721)
  ·
    refine ⟨96176255069656570410575041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128235006759542093880766721 96176255069656570410575041)
    ·
      refine ⟨72132191302242427807931281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96176255069656570410575041 72132191302242427807931281)
      ·
        refine ⟨54099143476681820855948461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72132191302242427807931281 54099143476681820855948461)
        ·
          refine ⟨20287178803755682820980673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54099143476681820855948461 20287178803755682820980673)
          ·
            refine ⟨15215384102816762115735505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20287178803755682820980673 15215384102816762115735505)
            ·
              refine ⟨11411538077112571586801629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15215384102816762115735505 11411538077112571586801629)
              ·
                refine ⟨4279326778917214345050611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11411538077112571586801629 4279326778917214345050611)
                ·
                  refine ⟨6418990168375821517575917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4279326778917214345050611 6418990168375821517575917)
                  ·
                    refine ⟨2407121313140933069090969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6418990168375821517575917 2407121313140933069090969)
                    ·
                      refine ⟨1805340984855699801818227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2407121313140933069090969 1805340984855699801818227)
                      ·
                        rfl

theorem cell23_3515889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 3, 1, 3, 2].length) (baseStart_3515889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3515889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3515889 prefixEnd_3515889 := by exact prefixLift 3515889
  have htrace : WordTrace (prefixWord ++ tailWord_3515889) baseStart_3515889 baseEnd_3515889 := by
    simpa [prefixWord, tailWord_3515889, baseEnd_3515889] using wordTrace_append hprefix tailTrace_3515889
  have hstable : (prefixWord ++ tailWord_3515889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3515889).length < 2 ^ (prefixWord ++ tailWord_3515889).sum := by decide
  have hdescent : baseEnd_3515889 < baseStart_3515889 := by decide
  rcases family_descends (prefixWord ++ tailWord_3515889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3515959 : List Nat := [1, 1, 3, 1, 2, 4, 4, 2, 5]
def baseStart_3515959 : Nat := 118140960795 + 3515959 * 2 ^ 59
def prefixEnd_3515959 : Nat := 4983230072969 + 3 ^ 40 * 3515959 * 2
def baseEnd_3515959 : Nat := 200597436500168280882545

theorem tailTrace_3515959 : CollatzResearch.WordTrace tailWord_3515959 prefixEnd_3515959 200597436500168280882545 := by
  unfold tailWord_3515959
  simp only [CollatzResearch.WordTrace]
  refine ⟨128237559869288495835814931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85491706579525663890543287 128237559869288495835814931)
  ·
    refine ⟨192356339803932743753722397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128237559869288495835814931 192356339803932743753722397)
    ·
      refine ⟨72133627426474778907645899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192356339803932743753722397 72133627426474778907645899)
      ·
        refine ⟨108200441139712168361468849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72133627426474778907645899 108200441139712168361468849)
        ·
          refine ⟨81150330854784126271101637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108200441139712168361468849 81150330854784126271101637)
          ·
            refine ⟨15215687035272023675831557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81150330854784126271101637 15215687035272023675831557)
            ·
              refine ⟨2852941319113504439218417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15215687035272023675831557 2852941319113504439218417)
              ·
                refine ⟨2139705989335128329413813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2852941319113504439218417 2139705989335128329413813)
                ·
                  refine ⟨200597436500168280882545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2139705989335128329413813 200597436500168280882545)
                  ·
                    rfl

theorem cell23_3515959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 4, 2, 5].length) (baseStart_3515959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3515959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3515959 prefixEnd_3515959 := by exact prefixLift 3515959
  have htrace : WordTrace (prefixWord ++ tailWord_3515959) baseStart_3515959 baseEnd_3515959 := by
    simpa [prefixWord, tailWord_3515959, baseEnd_3515959] using wordTrace_append hprefix tailTrace_3515959
  have hstable : (prefixWord ++ tailWord_3515959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3515959).length < 2 ^ (prefixWord ++ tailWord_3515959).sum := by decide
  have hdescent : baseEnd_3515959 < baseStart_3515959 := by decide
  rcases family_descends (prefixWord ++ tailWord_3515959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3515962 : List Nat := [3, 1, 1, 1, 3, 2, 1, 1, 1, 7, 2]
def baseStart_3515962 : Nat := 118140960795 + 3515962 * 2 ^ 59
def prefixEnd_3515962 : Nat := 4983230072969 + 3 ^ 40 * 3515962 * 2
def baseEnd_3515962 : Nat := 1805378468943478016205391

theorem tailTrace_3515962 : CollatzResearch.WordTrace tailWord_3515962 prefixEnd_3515962 1805378468943478016205391 := by
  unfold tailWord_3515962
  simp only [CollatzResearch.WordTrace]
  refine ⟨32059417322069406837043535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85491779525518418232116093 32059417322069406837043535)
  ·
    refine ⟨48089125983104110255565303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32059417322069406837043535 48089125983104110255565303)
    ·
      refine ⟨72133688974656165383347955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48089125983104110255565303 72133688974656165383347955)
      ·
        refine ⟨108200533461984248075021933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72133688974656165383347955 108200533461984248075021933)
        ·
          refine ⟨40575200048244093028133225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108200533461984248075021933 40575200048244093028133225)
          ·
            refine ⟨30431400036183069771099919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40575200048244093028133225 30431400036183069771099919)
            ·
              refine ⟨45647100054274604656649879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30431400036183069771099919 45647100054274604656649879)
              ·
                refine ⟨68470650081411906984974819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45647100054274604656649879 68470650081411906984974819)
                ·
                  refine ⟨102705975122117860477462229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68470650081411906984974819 102705975122117860477462229)
                  ·
                    refine ⟨2407171291924637354940521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 102705975122117860477462229 2407171291924637354940521)
                    ·
                      refine ⟨1805378468943478016205391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2407171291924637354940521 1805378468943478016205391)
                      ·
                        rfl

theorem cell23_3515962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 1, 7, 2].length) (baseStart_3515962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3515962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3515962 prefixEnd_3515962 := by exact prefixLift 3515962
  have htrace : WordTrace (prefixWord ++ tailWord_3515962) baseStart_3515962 baseEnd_3515962 := by
    simpa [prefixWord, tailWord_3515962, baseEnd_3515962] using wordTrace_append hprefix tailTrace_3515962
  have hstable : (prefixWord ++ tailWord_3515962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3515962).length < 2 ^ (prefixWord ++ tailWord_3515962).sum := by decide
  have hdescent : baseEnd_3515962 < baseStart_3515962 := by decide
  rcases family_descends (prefixWord ++ tailWord_3515962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3515992 : List Nat := [2, 1, 2, 2, 1, 2, 1, 1, 3, 6, 2]
def baseStart_3515992 : Nat := 118140960795 + 3515992 * 2 ^ 59
def prefixEnd_3515992 : Nat := 4983230072969 + 3 ^ 40 * 3515992 * 2
def baseEnd_3515992 : Nat := 1805393873363112898830253

theorem tailTrace_3515992 : CollatzResearch.WordTrace tailWord_3515992 prefixEnd_3515992 1805393873363112898830253 := by
  unfold tailWord_3515992
  simp only [CollatzResearch.WordTrace]
  refine ⟨64119381739084471235883115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85492508985445961647844153 64119381739084471235883115)
  ·
    refine ⟨96179072608626706853824673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64119381739084471235883115 96179072608626706853824673)
    ·
      refine ⟨72134304456470030140368505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96179072608626706853824673 72134304456470030140368505)
      ·
        refine ⟨54100728342352522605276379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72134304456470030140368505 54100728342352522605276379)
        ·
          refine ⟨81151092513528783907914569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54100728342352522605276379 81151092513528783907914569)
          ·
            refine ⟨60863319385146587930935927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81151092513528783907914569 60863319385146587930935927)
            ·
              refine ⟨91294979077719881896403891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60863319385146587930935927 91294979077719881896403891)
              ·
                refine ⟨136942468616579822844605837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91294979077719881896403891 136942468616579822844605837)
                ·
                  refine ⟨51353425731217433566727189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 136942468616579822844605837 51353425731217433566727189)
                  ·
                    refine ⟨2407191831150817198440337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 51353425731217433566727189 2407191831150817198440337)
                    ·
                      refine ⟨1805393873363112898830253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2407191831150817198440337 1805393873363112898830253)
                      ·
                        rfl

theorem cell23_3515992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 3, 6, 2].length) (baseStart_3515992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3515992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3515992 prefixEnd_3515992 := by exact prefixLift 3515992
  have htrace : WordTrace (prefixWord ++ tailWord_3515992) baseStart_3515992 baseEnd_3515992 := by
    simpa [prefixWord, tailWord_3515992, baseEnd_3515992] using wordTrace_append hprefix tailTrace_3515992
  have hstable : (prefixWord ++ tailWord_3515992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3515992).length < 2 ^ (prefixWord ++ tailWord_3515992).sum := by decide
  have hdescent : baseEnd_3515992 < baseStart_3515992 := by decide
  rcases family_descends (prefixWord ++ tailWord_3515992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3516012 : List Nat := [2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 3]
def baseStart_3516012 : Nat := 118140960795 + 3516012 * 2 ^ 59
def prefixEnd_3516012 : Nat := 4983230072969 + 3 ^ 40 * 3516012 * 2
def baseEnd_3516012 : Nat := 1805404142976202820580161

theorem tailTrace_3516012 : CollatzResearch.WordTrace tailWord_3516012 prefixEnd_3516012 1805404142976202820580161 := by
  unfold tailWord_3516012
  simp only [CollatzResearch.WordTrace]
  refine ⟨64119746469048242943747145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85492995292064323924996193 64119746469048242943747145)
  ·
    refine ⟨48089809851786182207810359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64119746469048242943747145 48089809851786182207810359)
    ·
      refine ⟨72134714777679273311715539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48089809851786182207810359 72134714777679273311715539)
      ·
        refine ⟨108202072166518909967573309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72134714777679273311715539 108202072166518909967573309)
        ·
          refine ⟨40575777062444591237839991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108202072166518909967573309 40575777062444591237839991)
          ·
            refine ⟨60863665593666886856759987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40575777062444591237839991 60863665593666886856759987)
            ·
              refine ⟨91295498390500330285139981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60863665593666886856759987 91295498390500330285139981)
              ·
                refine ⟨34235811896437623856927493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91295498390500330285139981 34235811896437623856927493)
                ·
                  refine ⟨6419214730582054473173905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34235811896437623856927493 6419214730582054473173905)
                  ·
                    refine ⟨4814411047936540854880429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6419214730582054473173905 4814411047936540854880429)
                    ·
                      refine ⟨1805404142976202820580161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4814411047936540854880429 1805404142976202820580161)
                      ·
                        rfl

theorem cell23_3516012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 3].length) (baseStart_3516012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3516012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3516012 prefixEnd_3516012 := by exact prefixLift 3516012
  have htrace : WordTrace (prefixWord ++ tailWord_3516012) baseStart_3516012 baseEnd_3516012 := by
    simpa [prefixWord, tailWord_3516012, baseEnd_3516012] using wordTrace_append hprefix tailTrace_3516012
  have hstable : (prefixWord ++ tailWord_3516012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3516012).length < 2 ^ (prefixWord ++ tailWord_3516012).sum := by decide
  have hdescent : baseEnd_3516012 < baseStart_3516012 := by decide
  rcases family_descends (prefixWord ++ tailWord_3516012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3516035 : List Nat := [1, 1, 1, 3, 3, 1, 1, 1, 3, 2, 6]
def baseStart_3516035 : Nat := 118140960795 + 3516035 * 2 ^ 59
def prefixEnd_3516035 : Nat := 4983230072969 + 3 ^ 40 * 3516035 * 2
def baseEnd_3516035 : Nat := 1805415953031256230592555

theorem tailTrace_3516035 : CollatzResearch.WordTrace tailWord_3516035 prefixEnd_3516035 1805415953031256230592555 := by
  unfold tailWord_3516035
  simp only [CollatzResearch.WordTrace]
  refine ⟨128240331817013160815581559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85493554544675440543721039 128240331817013160815581559)
  ·
    refine ⟨192360497725519741223372339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128240331817013160815581559 192360497725519741223372339)
    ·
      refine ⟨288540746588279611835058509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192360497725519741223372339 288540746588279611835058509)
      ·
        refine ⟨108202779970604854438146941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 288540746588279611835058509 108202779970604854438146941)
        ·
          refine ⟨40576042488976820414305103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108202779970604854438146941 40576042488976820414305103)
          ·
            refine ⟨60864063733465230621457655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40576042488976820414305103 60864063733465230621457655)
            ·
              refine ⟨91296095600197845932186483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60864063733465230621457655 91296095600197845932186483)
              ·
                refine ⟨136944143400296768898279725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91296095600197845932186483 136944143400296768898279725)
                ·
                  refine ⟨51354053775111288336854897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 136944143400296768898279725 51354053775111288336854897)
                  ·
                    refine ⟨38515540331333466252641173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51354053775111288336854897 38515540331333466252641173)
                    ·
                      refine ⟨1805415953031256230592555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38515540331333466252641173 1805415953031256230592555)
                      ·
                        rfl

theorem cell23_3516035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 3, 2, 6].length) (baseStart_3516035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3516035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3516035 prefixEnd_3516035 := by exact prefixLift 3516035
  have htrace : WordTrace (prefixWord ++ tailWord_3516035) baseStart_3516035 baseEnd_3516035 := by
    simpa [prefixWord, tailWord_3516035, baseEnd_3516035] using wordTrace_append hprefix tailTrace_3516035
  have hstable : (prefixWord ++ tailWord_3516035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3516035).length < 2 ^ (prefixWord ++ tailWord_3516035).sum := by decide
  have hdescent : baseEnd_3516035 < baseStart_3516035 := by decide
  rcases family_descends (prefixWord ++ tailWord_3516035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3516069 : List Nat := [1, 3, 1, 2, 1, 2, 3, 1, 4, 3, 2]
def baseStart_3516069 : Nat := 118140960795 + 3516069 * 2 ^ 59
def prefixEnd_3516069 : Nat := 4983230072969 + 3 ^ 40 * 3516069 * 2
def baseEnd_3516069 : Nat := 1805433411373509097567399

theorem tailTrace_3516069 : CollatzResearch.WordTrace tailWord_3516069 prefixEnd_3516069 1805433411373509097567399 := by
  unfold tailWord_3516069
  simp only [CollatzResearch.WordTrace]
  refine ⟨128241571898889984622319261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85494381265926656414879507 128241571898889984622319261)
  ·
    refine ⟨48090589462083744233369723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128241571898889984622319261 48090589462083744233369723)
    ·
      refine ⟨72135884193125616350054585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48090589462083744233369723 72135884193125616350054585)
      ·
        refine ⟨54101913144844212262540939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72135884193125616350054585 54101913144844212262540939)
        ·
          refine ⟨81152869717266318393811409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54101913144844212262540939 81152869717266318393811409)
          ·
            refine ⟨60864652287949738795358557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81152869717266318393811409 60864652287949738795358557)
            ·
              refine ⟨22824244607981152048259459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60864652287949738795358557 22824244607981152048259459)
              ·
                refine ⟨34236366911971728072389189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22824244607981152048259459 34236366911971728072389189)
                ·
                  refine ⟨6419318795994699013572973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34236366911971728072389189 6419318795994699013572973)
                  ·
                    refine ⟨2407244548498012130089865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6419318795994699013572973 2407244548498012130089865)
                    ·
                      refine ⟨1805433411373509097567399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2407244548498012130089865 1805433411373509097567399)
                      ·
                        rfl

theorem cell23_3516069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 1, 4, 3, 2].length) (baseStart_3516069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3516069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3516069 prefixEnd_3516069 := by exact prefixLift 3516069
  have htrace : WordTrace (prefixWord ++ tailWord_3516069) baseStart_3516069 baseEnd_3516069 := by
    simpa [prefixWord, tailWord_3516069, baseEnd_3516069] using wordTrace_append hprefix tailTrace_3516069
  have hstable : (prefixWord ++ tailWord_3516069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3516069).length < 2 ^ (prefixWord ++ tailWord_3516069).sum := by decide
  have hdescent : baseEnd_3516069 < baseStart_3516069 := by decide
  rcases family_descends (prefixWord ++ tailWord_3516069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3516167 : List Nat := [1, 1, 4, 4, 2, 1, 2, 3, 1, 2, 2]
def baseStart_3516167 : Nat := 118140960795 + 3516167 * 2 ^ 59
def prefixEnd_3516167 : Nat := 4983230072969 + 3 ^ 40 * 3516167 * 2
def baseEnd_3516167 : Nat := 1805483732477649714141949

theorem tailTrace_3516167 : CollatzResearch.WordTrace tailWord_3516167 prefixEnd_3516167 1805483732477649714141949 := by
  unfold tailWord_3516167
  simp only [CollatzResearch.WordTrace]
  refine ⟨128245146252534947359386755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85496764168356631572924503 128245146252534947359386755)
  ·
    refine ⟨192367719378802421039080133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128245146252534947359386755 192367719378802421039080133)
    ·
      refine ⟨36068947383525453944827525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 192367719378802421039080133 36068947383525453944827525)
      ·
        refine ⟨6762927634411022614655161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36068947383525453944827525 6762927634411022614655161)
        ·
          refine ⟨5072195725808266960991371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6762927634411022614655161 5072195725808266960991371)
          ·
            refine ⟨7608293588712400441487057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5072195725808266960991371 7608293588712400441487057)
            ·
              refine ⟨5706220191534300331115293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7608293588712400441487057 5706220191534300331115293)
              ·
                refine ⟨2139832571825362624168235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5706220191534300331115293 2139832571825362624168235)
                ·
                  refine ⟨3209748857738043936252353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2139832571825362624168235 3209748857738043936252353)
                  ·
                    refine ⟨2407311643303532952189265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3209748857738043936252353 2407311643303532952189265)
                    ·
                      refine ⟨1805483732477649714141949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2407311643303532952189265 1805483732477649714141949)
                      ·
                        rfl

theorem cell23_3516167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 2, 3, 1, 2, 2].length) (baseStart_3516167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3516167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3516167 prefixEnd_3516167 := by exact prefixLift 3516167
  have htrace : WordTrace (prefixWord ++ tailWord_3516167) baseStart_3516167 baseEnd_3516167 := by
    simpa [prefixWord, tailWord_3516167, baseEnd_3516167] using wordTrace_append hprefix tailTrace_3516167
  have hstable : (prefixWord ++ tailWord_3516167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3516167).length < 2 ^ (prefixWord ++ tailWord_3516167).sum := by decide
  have hdescent : baseEnd_3516167 < baseStart_3516167 := by decide
  rcases family_descends (prefixWord ++ tailWord_3516167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3516183 : List Nat := [1, 1, 3, 4, 2, 1, 3, 2, 2, 1, 3]
def baseStart_3516183 : Nat := 118140960795 + 3516183 * 2 ^ 59
def prefixEnd_3516183 : Nat := 4983230072969 + 3 ^ 40 * 3516183 * 2
def baseEnd_3516183 : Nat := 1805491948168121651541875

theorem tailTrace_3516183 : CollatzResearch.WordTrace tailWord_3516183 prefixEnd_3516183 1805491948168121651541875 := by
  unfold tailWord_3516183
  simp only [CollatzResearch.WordTrace]
  refine ⟨128245729820476982091969203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85497153213651321394646135 128245729820476982091969203)
  ·
    refine ⟨192368594730715473137953805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128245729820476982091969203 192368594730715473137953805)
    ·
      refine ⟨72138223024018302426732677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192368594730715473137953805 72138223024018302426732677)
      ·
        refine ⟨13525916817003431705012377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72138223024018302426732677 13525916817003431705012377)
        ·
          refine ⟨10144437612752573778759283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13525916817003431705012377 10144437612752573778759283)
          ·
            refine ⟨15216656419128860668138925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10144437612752573778759283 15216656419128860668138925)
            ·
              refine ⟨5706246157173322750552097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15216656419128860668138925 5706246157173322750552097)
              ·
                refine ⟨4279684617879992062914073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5706246157173322750552097 4279684617879992062914073)
                ·
                  refine ⟨3209763463409994047185555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4279684617879992062914073 3209763463409994047185555)
                  ·
                    refine ⟨4814645195114991070778333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3209763463409994047185555 4814645195114991070778333)
                    ·
                      refine ⟨1805491948168121651541875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4814645195114991070778333 1805491948168121651541875)
                      ·
                        rfl

theorem cell23_3516183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 3, 2, 2, 1, 3].length) (baseStart_3516183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3516183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3516183 prefixEnd_3516183 := by exact prefixLift 3516183
  have htrace : WordTrace (prefixWord ++ tailWord_3516183) baseStart_3516183 baseEnd_3516183 := by
    simpa [prefixWord, tailWord_3516183, baseEnd_3516183] using wordTrace_append hprefix tailTrace_3516183
  have hstable : (prefixWord ++ tailWord_3516183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3516183).length < 2 ^ (prefixWord ++ tailWord_3516183).sum := by decide
  have hdescent : baseEnd_3516183 < baseStart_3516183 := by decide
  rcases family_descends (prefixWord ++ tailWord_3516183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3516200 : List Nat := [2, 1, 5, 1, 1, 3, 3, 1, 2, 1, 3]
def baseStart_3516200 : Nat := 118140960795 + 3516200 * 2 ^ 59
def prefixEnd_3516200 : Nat := 4983230072969 + 3 ^ 40 * 3516200 * 2
def baseEnd_3516200 : Nat := 1805500677339248085029297

theorem tailTrace_3516200 : CollatzResearch.WordTrace tailWord_3516200 prefixEnd_3516200 1805500677339248085029297 := by
  unfold tailWord_3516200
  simp only [CollatzResearch.WordTrace]
  refine ⟨64123174930707696997669027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85497566574276929330225369 64123174930707696997669027)
  ·
    refine ⟨96184762396061545496503541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64123174930707696997669027 96184762396061545496503541)
    ·
      refine ⟨9017321474630769890297207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 96184762396061545496503541 9017321474630769890297207)
      ·
        refine ⟨13525982211946154835445811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9017321474630769890297207 13525982211946154835445811)
        ·
          refine ⟨20288973317919232253168717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13525982211946154835445811 20288973317919232253168717)
          ·
            refine ⟨7608364994219712094938269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20288973317919232253168717 7608364994219712094938269)
            ·
              refine ⟨2853136872832392035601851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7608364994219712094938269 2853136872832392035601851)
              ·
                refine ⟨4279705309248588053402777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2853136872832392035601851 4279705309248588053402777)
                ·
                  refine ⟨3209778981936441040052083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4279705309248588053402777 3209778981936441040052083)
                  ·
                    refine ⟨4814668472904661560078125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3209778981936441040052083 4814668472904661560078125)
                    ·
                      refine ⟨1805500677339248085029297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4814668472904661560078125 1805500677339248085029297)
                      ·
                        rfl

theorem cell23_3516200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 3, 1, 2, 1, 3].length) (baseStart_3516200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3516200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3516200 prefixEnd_3516200 := by exact prefixLift 3516200
  have htrace : WordTrace (prefixWord ++ tailWord_3516200) baseStart_3516200 baseEnd_3516200 := by
    simpa [prefixWord, tailWord_3516200, baseEnd_3516200] using wordTrace_append hprefix tailTrace_3516200
  have hstable : (prefixWord ++ tailWord_3516200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3516200).length < 2 ^ (prefixWord ++ tailWord_3516200).sum := by decide
  have hdescent : baseEnd_3516200 < baseStart_3516200 := by decide
  rcases family_descends (prefixWord ++ tailWord_3516200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3516299 : List Nat := [1, 1, 1, 1, 4, 2, 1, 2, 3, 4, 3]
def baseStart_3516299 : Nat := 118140960795 + 3516299 * 2 ^ 59
def prefixEnd_3516299 : Nat := 4983230072969 + 3 ^ 40 * 3516299 * 2
def baseEnd_3516299 : Nat := 1805551511924043197691341

theorem tailTrace_3516299 : CollatzResearch.WordTrace tailWord_3516299 prefixEnd_3516299 1805551511924043197691341 := by
  unfold tailWord_3516299
  simp only [CollatzResearch.WordTrace]
  refine ⟨128249960688056733903191951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85499973792037822602127967 128249960688056733903191951)
  ·
    refine ⟨192374941032085100854787927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128249960688056733903191951 192374941032085100854787927)
    ·
      refine ⟨288562411548127651282181891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192374941032085100854787927 288562411548127651282181891)
      ·
        refine ⟨432843617322191476923272837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288562411548127651282181891 432843617322191476923272837)
        ·
          refine ⟨81158178247910901923113657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 432843617322191476923272837 81158178247910901923113657)
          ·
            refine ⟨60868633685933176442335243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81158178247910901923113657 60868633685933176442335243)
            ·
              refine ⟨91302950528899764663502865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60868633685933176442335243 91302950528899764663502865)
              ·
                refine ⟨68477212896674823497627149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91302950528899764663502865 68477212896674823497627149)
                ·
                  refine ⟨25678954836253058811610181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68477212896674823497627149 25678954836253058811610181)
                  ·
                    refine ⟨4814804031797448527176909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25678954836253058811610181 4814804031797448527176909)
                    ·
                      refine ⟨1805551511924043197691341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4814804031797448527176909 1805551511924043197691341)
                      ·
                        rfl

theorem cell23_3516299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 3, 4, 3].length) (baseStart_3516299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3516299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3516299 prefixEnd_3516299 := by exact prefixLift 3516299
  have htrace : WordTrace (prefixWord ++ tailWord_3516299) baseStart_3516299 baseEnd_3516299 := by
    simpa [prefixWord, tailWord_3516299, baseEnd_3516299] using wordTrace_append hprefix tailTrace_3516299
  have hstable : (prefixWord ++ tailWord_3516299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3516299).length < 2 ^ (prefixWord ++ tailWord_3516299).sum := by decide
  have hdescent : baseEnd_3516299 < baseStart_3516299 := by decide
  rcases family_descends (prefixWord ++ tailWord_3516299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3516329 : List Nat := [1, 2, 1, 1, 1, 1, 4, 1, 1, 7, 3]
def baseStart_3516329 : Nat := 118140960795 + 3516329 * 2 ^ 59
def prefixEnd_3516329 : Nat := 4983230072969 + 3 ^ 40 * 3516329 * 2
def baseEnd_3516329 : Nat := 1805566916343678080316203

theorem tailTrace_3516329 : CollatzResearch.WordTrace tailWord_3516329 prefixEnd_3516329 1805566916343678080316203 := by
  unfold tailWord_3516329
  simp only [CollatzResearch.WordTrace]
  refine ⟨128251054877948049026784041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85500703251965366017856027 128251054877948049026784041)
  ·
    refine ⟨96188291158461036770088031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128251054877948049026784041 96188291158461036770088031)
    ·
      refine ⟨144282436737691555155132047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96188291158461036770088031 144282436737691555155132047)
      ·
        refine ⟨216423655106537332732698071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144282436737691555155132047 216423655106537332732698071)
        ·
          refine ⟨324635482659805999099047107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216423655106537332732698071 324635482659805999099047107)
          ·
            refine ⟨486953223989708998648570661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 324635482659805999099047107 486953223989708998648570661)
            ·
              refine ⟨91303729498070437246606999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 486953223989708998648570661 91303729498070437246606999)
              ·
                refine ⟨136955594247105655869910499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91303729498070437246606999 136955594247105655869910499)
                ·
                  refine ⟨205433391370658483804865749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 136955594247105655869910499 205433391370658483804865749)
                  ·
                    refine ⟨4814845110249808214176541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 205433391370658483804865749 4814845110249808214176541)
                    ·
                      refine ⟨1805566916343678080316203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4814845110249808214176541 1805566916343678080316203)
                      ·
                        rfl

theorem cell23_3516329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 7, 3].length) (baseStart_3516329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3516329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3516329 prefixEnd_3516329 := by exact prefixLift 3516329
  have htrace : WordTrace (prefixWord ++ tailWord_3516329) baseStart_3516329 baseEnd_3516329 := by
    simpa [prefixWord, tailWord_3516329, baseEnd_3516329] using wordTrace_append hprefix tailTrace_3516329
  have hstable : (prefixWord ++ tailWord_3516329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3516329).length < 2 ^ (prefixWord ++ tailWord_3516329).sum := by decide
  have hdescent : baseEnd_3516329 < baseStart_3516329 := by decide
  rcases family_descends (prefixWord ++ tailWord_3516329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3516363 : List Nat := [1, 1, 1, 1, 3, 4, 4, 1, 3, 1, 3]
def baseStart_3516363 : Nat := 118140960795 + 3516363 * 2 ^ 59
def prefixEnd_3516363 : Nat := 4983230072969 + 3 ^ 40 * 3516363 * 2
def baseEnd_3516363 : Nat := 1805584374685930947291047

theorem tailTrace_3516363 : CollatzResearch.WordTrace tailWord_3516363 prefixEnd_3516363 1805584374685930947291047 := by
  unfold tailWord_3516363
  simp only [CollatzResearch.WordTrace]
  refine ⟨128252294959824872833521743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85501529973216581889014495 128252294959824872833521743)
  ·
    refine ⟨192378442439737309250282615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128252294959824872833521743 192378442439737309250282615)
    ·
      refine ⟨288567663659605963875423923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192378442439737309250282615 288567663659605963875423923)
      ·
        refine ⟨432851495489408945813135885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288567663659605963875423923 432851495489408945813135885)
        ·
          refine ⟨162319310808528354679925957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 432851495489408945813135885 162319310808528354679925957)
          ·
            refine ⟨30434870776599066502486117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 162319310808528354679925957 30434870776599066502486117)
            ·
              refine ⟨5706538270612324969216147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30434870776599066502486117 5706538270612324969216147)
              ·
                refine ⟨8559807405918487453824221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5706538270612324969216147 8559807405918487453824221)
                ·
                  refine ⟨3209927777219432795184083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8559807405918487453824221 3209927777219432795184083)
                  ·
                    refine ⟨4814891665829149192776125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3209927777219432795184083 4814891665829149192776125)
                    ·
                      refine ⟨1805584374685930947291047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4814891665829149192776125 1805584374685930947291047)
                      ·
                        rfl

theorem cell23_3516363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 4, 1, 3, 1, 3].length) (baseStart_3516363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3516363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3516363 prefixEnd_3516363 := by exact prefixLift 3516363
  have htrace : WordTrace (prefixWord ++ tailWord_3516363) baseStart_3516363 baseEnd_3516363 := by
    simpa [prefixWord, tailWord_3516363, baseEnd_3516363] using wordTrace_append hprefix tailTrace_3516363
  have hstable : (prefixWord ++ tailWord_3516363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3516363).length < 2 ^ (prefixWord ++ tailWord_3516363).sum := by decide
  have hdescent : baseEnd_3516363 < baseStart_3516363 := by decide
  rcases family_descends (prefixWord ++ tailWord_3516363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3516369 : List Nat := [1, 2, 2, 1, 2, 1, 2, 1, 2, 5, 4]
def baseStart_3516369 : Nat := 118140960795 + 3516369 * 2 ^ 59
def prefixEnd_3516369 : Nat := 4983230072969 + 3 ^ 40 * 3516369 * 2
def baseEnd_3516369 : Nat := 1805587455569857923816019

theorem tailTrace_3516369 : CollatzResearch.WordTrace tailWord_3516369 prefixEnd_3516369 1805587455569857923816019 := by
  unfold tailWord_3516369
  simp only [CollatzResearch.WordTrace]
  refine ⟨128252513797803135858240161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85501675865202090572160107 128252513797803135858240161)
  ·
    refine ⟨96189385348352351893680121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128252513797803135858240161 96189385348352351893680121)
    ·
      refine ⟨72142039011264263920260091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96189385348352351893680121 72142039011264263920260091)
      ·
        refine ⟨108213058516896395880390137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72142039011264263920260091 108213058516896395880390137)
        ·
          refine ⟨81159793887672296910292603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108213058516896395880390137 81159793887672296910292603)
          ·
            refine ⟨121739690831508445365438905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81159793887672296910292603 121739690831508445365438905)
            ·
              refine ⟨91304768123631334024079179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121739690831508445365438905 91304768123631334024079179)
              ·
                refine ⟨136957152185447001036118769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91304768123631334024079179 136957152185447001036118769)
                ·
                  refine ⟨102717864139085250777089077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 136957152185447001036118769 102717864139085250777089077)
                  ·
                    refine ⟨9629799763039242260352101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 102717864139085250777089077 9629799763039242260352101)
                    ·
                      refine ⟨1805587455569857923816019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9629799763039242260352101 1805587455569857923816019)
                      ·
                        rfl

theorem cell23_3516369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 5, 4].length) (baseStart_3516369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3516369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3516369 prefixEnd_3516369 := by exact prefixLift 3516369
  have htrace : WordTrace (prefixWord ++ tailWord_3516369) baseStart_3516369 baseEnd_3516369 := by
    simpa [prefixWord, tailWord_3516369, baseEnd_3516369] using wordTrace_append hprefix tailTrace_3516369
  have hstable : (prefixWord ++ tailWord_3516369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3516369).length < 2 ^ (prefixWord ++ tailWord_3516369).sum := by decide
  have hdescent : baseEnd_3516369 < baseStart_3516369 := by decide
  rcases family_descends (prefixWord ++ tailWord_3516369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3516370 : List Nat := [3, 2, 2, 3, 2, 1, 3, 1, 6]
def baseStart_3516370 : Nat := 118140960795 + 3516370 * 2 ^ 59
def prefixEnd_3516370 : Nat := 4983230072969 + 3 ^ 40 * 3516370 * 2
def baseEnd_3516370 : Nat := 200620885450056935544835

theorem tailTrace_3516370 : CollatzResearch.WordTrace tailWord_3516370 prefixEnd_3516370 200620885450056935544835 := by
  unfold tailWord_3516370
  simp only [CollatzResearch.WordTrace]
  refine ⟨32063137567699878257256641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85501700180533008686017709 32063137567699878257256641)
  ·
    refine ⟨24047353175774908692942481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32063137567699878257256641 24047353175774908692942481)
    ·
      refine ⟨18035514881831181519706861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24047353175774908692942481 18035514881831181519706861)
      ·
        refine ⟨6763318080686693069890073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18035514881831181519706861 6763318080686693069890073)
        ·
          refine ⟨5072488560515019802417555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6763318080686693069890073 5072488560515019802417555)
          ·
            refine ⟨7608732840772529703626333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5072488560515019802417555 7608732840772529703626333)
            ·
              refine ⟨2853274815289698638859875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7608732840772529703626333 2853274815289698638859875)
              ·
                refine ⟨4279912222934547958289813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2853274815289698638859875 4279912222934547958289813)
                ·
                  refine ⟨200620885450056935544835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4279912222934547958289813 200620885450056935544835)
                  ·
                    rfl

theorem cell23_3516370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 3, 1, 6].length) (baseStart_3516370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3516370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3516370 prefixEnd_3516370 := by exact prefixLift 3516370
  have htrace : WordTrace (prefixWord ++ tailWord_3516370) baseStart_3516370 baseEnd_3516370 := by
    simpa [prefixWord, tailWord_3516370, baseEnd_3516370] using wordTrace_append hprefix tailTrace_3516370
  have hstable : (prefixWord ++ tailWord_3516370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3516370).length < 2 ^ (prefixWord ++ tailWord_3516370).sum := by decide
  have hdescent : baseEnd_3516370 < baseStart_3516370 := by decide
  rcases family_descends (prefixWord ++ tailWord_3516370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3516373 : List Nat := [1, 3, 2, 3, 2, 1, 1, 2, 1, 5, 2]
def baseStart_3516373 : Nat := 118140960795 + 3516373 * 2 ^ 59
def prefixEnd_3516373 : Nat := 4983230072969 + 3 ^ 40 * 3516373 * 2
def baseEnd_3516373 : Nat := 1805589509492475908166001

theorem tailTrace_3516373 : CollatzResearch.WordTrace tailWord_3516373 prefixEnd_3516373 1805589509492475908166001 := by
  unfold tailWord_3516373
  simp only [CollatzResearch.WordTrace]
  refine ⟨128252659689788644541385773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85501773126525763027590515 128252659689788644541385773)
  ·
    refine ⟨48094747383670741703019665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128252659689788644541385773 48094747383670741703019665)
    ·
      refine ⟨36071060537753056277264749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48094747383670741703019665 36071060537753056277264749)
      ·
        refine ⟨13526647701657396103974281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36071060537753056277264749 13526647701657396103974281)
        ·
          refine ⟨10144985776243047077980711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13526647701657396103974281 10144985776243047077980711)
          ·
            refine ⟨15217478664364570616971067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10144985776243047077980711 15217478664364570616971067)
            ·
              refine ⟨22826217996546855925456601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15217478664364570616971067 22826217996546855925456601)
              ·
                refine ⟨17119663497410141944092451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22826217996546855925456601 17119663497410141944092451)
                ·
                  refine ⟨25679495246115212916138677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17119663497410141944092451 25679495246115212916138677)
                  ·
                    refine ⟨2407452679323301210888001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25679495246115212916138677 2407452679323301210888001)
                    ·
                      refine ⟨1805589509492475908166001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2407452679323301210888001 1805589509492475908166001)
                      ·
                        rfl

theorem cell23_3516373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 2, 1, 5, 2].length) (baseStart_3516373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3516373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3516373 prefixEnd_3516373 := by exact prefixLift 3516373
  have htrace : WordTrace (prefixWord ++ tailWord_3516373) baseStart_3516373 baseEnd_3516373 := by
    simpa [prefixWord, tailWord_3516373, baseEnd_3516373] using wordTrace_append hprefix tailTrace_3516373
  have hstable : (prefixWord ++ tailWord_3516373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3516373).length < 2 ^ (prefixWord ++ tailWord_3516373).sum := by decide
  have hdescent : baseEnd_3516373 < baseStart_3516373 := by decide
  rcases family_descends (prefixWord ++ tailWord_3516373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3516383 : List Nat := [1, 1, 2, 3, 4, 2, 2, 2, 1, 5]
def baseStart_3516383 : Nat := 118140960795 + 3516383 * 2 ^ 59
def prefixEnd_3516383 : Nat := 4983230072969 + 3 ^ 40 * 3516383 * 2
def baseEnd_3516383 : Nat := 601864881433006956346985

theorem tailTrace_3516383 : CollatzResearch.WordTrace tailWord_3516383 prefixEnd_3516383 601864881433006956346985 := by
  unfold tailWord_3516383
  simp only [CollatzResearch.WordTrace]
  refine ⟨128253024419752416249249803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85502016279834944166166535 128253024419752416249249803)
  ·
    refine ⟨192379536629628624373874705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128253024419752416249249803 192379536629628624373874705)
    ·
      refine ⟨144284652472221468280406029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192379536629628624373874705 144284652472221468280406029)
      ·
        refine ⟨54106744677083050605152261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144284652472221468280406029 54106744677083050605152261)
        ·
          refine ⟨10145014626953071988466049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54106744677083050605152261 10145014626953071988466049)
          ·
            refine ⟨7608760970214803991349537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10145014626953071988466049 7608760970214803991349537)
            ·
              refine ⟨5706570727661102993512153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7608760970214803991349537 5706570727661102993512153)
              ·
                refine ⟨4279928045745827245134115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5706570727661102993512153 4279928045745827245134115)
                ·
                  refine ⟨6419892068618740867701173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4279928045745827245134115 6419892068618740867701173)
                  ·
                    refine ⟨601864881433006956346985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6419892068618740867701173 601864881433006956346985)
                    ·
                      rfl

theorem cell23_3516383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 2, 2, 1, 5].length) (baseStart_3516383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3516383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3516383 prefixEnd_3516383 := by exact prefixLift 3516383
  have htrace : WordTrace (prefixWord ++ tailWord_3516383) baseStart_3516383 baseEnd_3516383 := by
    simpa [prefixWord, tailWord_3516383, baseEnd_3516383] using wordTrace_append hprefix tailTrace_3516383
  have hstable : (prefixWord ++ tailWord_3516383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3516383).length < 2 ^ (prefixWord ++ tailWord_3516383).sum := by decide
  have hdescent : baseEnd_3516383 < baseStart_3516383 := by decide
  rcases family_descends (prefixWord ++ tailWord_3516383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3516403 : List Nat := [1, 1, 1, 2, 2, 2, 1, 4, 5, 2, 2]
def baseStart_3516403 : Nat := 118140960795 + 3516403 * 2 ^ 59
def prefixEnd_3516403 : Nat := 4983230072969 + 3 ^ 40 * 3516403 * 2
def baseEnd_3516403 : Nat := 1805604913912110790790863

theorem tailTrace_3516403 : CollatzResearch.WordTrace tailWord_3516403 prefixEnd_3516403 1805604913912110790790863 := by
  unfold tailWord_3516403
  simp only [CollatzResearch.WordTrace]
  refine ⟨128253753879679959664977863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85502502586453306443318575 128253753879679959664977863)
  ·
    refine ⟨192380630819519939497466795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128253753879679959664977863 192380630819519939497466795)
    ·
      refine ⟨288570946229279909246200193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192380630819519939497466795 288570946229279909246200193)
      ·
        refine ⟨216428209671959931934650145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 288570946229279909246200193 216428209671959931934650145)
        ·
          refine ⟨162321157253969948950987609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216428209671959931934650145 162321157253969948950987609)
          ·
            refine ⟨121740867940477461713240707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162321157253969948950987609 121740867940477461713240707)
            ·
              refine ⟨182611301910716192569861061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121740867940477461713240707 182611301910716192569861061)
              ·
                refine ⟨34239619108259286106848949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 182611301910716192569861061 34239619108259286106848949)
                ·
                  refine ⟨3209964291399308072517089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34239619108259286106848949 3209964291399308072517089)
                  ·
                    refine ⟨2407473218549481054387817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3209964291399308072517089 2407473218549481054387817)
                    ·
                      refine ⟨1805604913912110790790863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2407473218549481054387817 1805604913912110790790863)
                      ·
                        rfl

theorem cell23_3516403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 4, 5, 2, 2].length) (baseStart_3516403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3516403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3516403 prefixEnd_3516403 := by exact prefixLift 3516403
  have htrace : WordTrace (prefixWord ++ tailWord_3516403) baseStart_3516403 baseEnd_3516403 := by
    simpa [prefixWord, tailWord_3516403, baseEnd_3516403] using wordTrace_append hprefix tailTrace_3516403
  have hstable : (prefixWord ++ tailWord_3516403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3516403).length < 2 ^ (prefixWord ++ tailWord_3516403).sum := by decide
  have hdescent : baseEnd_3516403 < baseStart_3516403 := by decide
  rcases family_descends (prefixWord ++ tailWord_3516403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3516409 : List Nat := [1, 2, 1, 3, 1, 4, 11]
def baseStart_3516409 : Nat := 118140960795 + 3516409 * 2 ^ 59
def prefixEnd_3516409 : Nat := 4983230072969 + 3 ^ 40 * 3516409 * 2
def baseEnd_3516409 : Nat := 22291456725877009473035

theorem tailTrace_3516409 : CollatzResearch.WordTrace tailWord_3516409 prefixEnd_3516409 22291456725877009473035 := by
  unfold tailWord_3516409
  simp only [CollatzResearch.WordTrace]
  refine ⟨128253972717658222689696281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85502648478438815126464187 128253972717658222689696281)
  ·
    refine ⟨96190479538243667017272211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128253972717658222689696281 96190479538243667017272211)
    ·
      refine ⟨144285719307365500525908317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96190479538243667017272211 144285719307365500525908317)
      ·
        refine ⟨54107144740262062697215619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144285719307365500525908317 54107144740262062697215619)
        ·
          refine ⟨81160717110393094045823429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54107144740262062697215619 81160717110393094045823429)
          ·
            refine ⟨15217634458198705133591893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81160717110393094045823429 15217634458198705133591893)
            ·
              refine ⟨22291456725877009473035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 15217634458198705133591893 22291456725877009473035)
              ·
                rfl

theorem cell23_3516409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 11].length) (baseStart_3516409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3516409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3516409 prefixEnd_3516409 := by exact prefixLift 3516409
  have htrace : WordTrace (prefixWord ++ tailWord_3516409) baseStart_3516409 baseEnd_3516409 := by
    simpa [prefixWord, tailWord_3516409, baseEnd_3516409] using wordTrace_append hprefix tailTrace_3516409
  have hstable : (prefixWord ++ tailWord_3516409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3516409).length < 2 ^ (prefixWord ++ tailWord_3516409).sum := by decide
  have hdescent : baseEnd_3516409 < baseStart_3516409 := by decide
  rcases family_descends (prefixWord ++ tailWord_3516409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3516437 : List Nat := [1, 3, 2, 1, 6, 1, 1, 2, 1, 1, 4]
def baseStart_3516437 : Nat := 118140960795 + 3516437 * 2 ^ 59
def prefixEnd_3516437 : Nat := 4983230072969 + 3 ^ 40 * 3516437 * 2
def baseEnd_3516437 : Nat := 1805622372254363657765707

theorem tailTrace_3516437 : CollatzResearch.WordTrace tailWord_3516437 prefixEnd_3516437 1805622372254363657765707 := by
  unfold tailWord_3516437
  simp only [CollatzResearch.WordTrace]
  refine ⟨128254993961556783471715565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85503329307704522314477043 128254993961556783471715565)
  ·
    refine ⟨48095622735583793801893337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128254993961556783471715565 48095622735583793801893337)
    ·
      refine ⟨36071717051687845351420003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48095622735583793801893337 36071717051687845351420003)
      ·
        refine ⟨54107575577531768027130005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36071717051687845351420003 54107575577531768027130005)
        ·
          refine ⟨2536292605196801626271719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 54107575577531768027130005 2536292605196801626271719)
          ·
            refine ⟨3804438907795202439407579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2536292605196801626271719 3804438907795202439407579)
            ·
              refine ⟨5706658361692803659111369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3804438907795202439407579 5706658361692803659111369)
              ·
                refine ⟨4279993771269602744333527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5706658361692803659111369 4279993771269602744333527)
                ·
                  refine ⟨6419990656904404116500291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4279993771269602744333527 6419990656904404116500291)
                  ·
                    refine ⟨9629985985356606174750437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6419990656904404116500291 9629985985356606174750437)
                    ·
                      refine ⟨1805622372254363657765707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9629985985356606174750437 1805622372254363657765707)
                      ·
                        rfl

theorem cell23_3516437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 1, 2, 1, 1, 4].length) (baseStart_3516437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3516437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3516437 prefixEnd_3516437 := by exact prefixLift 3516437
  have htrace : WordTrace (prefixWord ++ tailWord_3516437) baseStart_3516437 baseEnd_3516437 := by
    simpa [prefixWord, tailWord_3516437, baseEnd_3516437] using wordTrace_append hprefix tailTrace_3516437
  have hstable : (prefixWord ++ tailWord_3516437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3516437).length < 2 ^ (prefixWord ++ tailWord_3516437).sum := by decide
  have hdescent : baseEnd_3516437 < baseStart_3516437 := by decide
  rcases family_descends (prefixWord ++ tailWord_3516437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3516453 : List Nat := [1, 3, 1, 2, 2, 4, 1, 2, 1, 3, 3]
def baseStart_3516453 : Nat := 118140960795 + 3516453 * 2 ^ 59
def prefixEnd_3516453 : Nat := 4983230072969 + 3 ^ 40 * 3516453 * 2
def baseEnd_3516453 : Nat := 1805630587944835595165633

theorem tailTrace_3516453 : CollatzResearch.WordTrace tailWord_3516453 prefixEnd_3516453 1805630587944835595165633 := by
  unfold tailWord_3516453
  simp only [CollatzResearch.WordTrace]
  refine ⟨128255577529498818204298013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85503718352999212136198675 128255577529498818204298013)
  ·
    refine ⟨48095841573562056826611755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128255577529498818204298013 48095841573562056826611755)
    ·
      refine ⟨72143762360343085239917633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48095841573562056826611755 72143762360343085239917633)
      ·
        refine ⟨54107821770257313929938225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72143762360343085239917633 54107821770257313929938225)
        ·
          refine ⟨40580866327692985447453669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54107821770257313929938225 40580866327692985447453669)
          ·
            refine ⟨7608912436442434771397563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40580866327692985447453669 7608912436442434771397563)
            ·
              refine ⟨11413368654663652157096345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7608912436442434771397563 11413368654663652157096345)
              ·
                refine ⟨8560026490997739117822259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11413368654663652157096345 8560026490997739117822259)
                ·
                  refine ⟨12840039736496608676733389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8560026490997739117822259 12840039736496608676733389)
                  ·
                    refine ⟨4815014901186228253775021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12840039736496608676733389 4815014901186228253775021)
                    ·
                      refine ⟨1805630587944835595165633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4815014901186228253775021 1805630587944835595165633)
                      ·
                        rfl

theorem cell23_3516453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 2, 1, 3, 3].length) (baseStart_3516453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3516453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3516453 prefixEnd_3516453 := by exact prefixLift 3516453
  have htrace : WordTrace (prefixWord ++ tailWord_3516453) baseStart_3516453 baseEnd_3516453 := by
    simpa [prefixWord, tailWord_3516453, baseEnd_3516453] using wordTrace_append hprefix tailTrace_3516453
  have hstable : (prefixWord ++ tailWord_3516453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3516453).length < 2 ^ (prefixWord ++ tailWord_3516453).sum := by decide
  have hdescent : baseEnd_3516453 < baseStart_3516453 := by decide
  rcases family_descends (prefixWord ++ tailWord_3516453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3516476 : List Nat := [2, 2, 2, 2, 2, 1, 1, 1, 1, 5, 4]
def baseStart_3516476 : Nat := 118140960795 + 3516476 * 2 ^ 59
def prefixEnd_3516476 : Nat := 4983230072969 + 3 ^ 40 * 3516476 * 2
def baseEnd_3516476 : Nat := 1805642397999889005178027

theorem tailTrace_3516476 : CollatzResearch.WordTrace tailWord_3516476 prefixEnd_3516476 1805642397999889005178027 := by
  unfold tailWord_3516476
  simp only [CollatzResearch.WordTrace]
  refine ⟨64128208204207746566192641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85504277605610328754923521 64128208204207746566192641)
  ·
    refine ⟨48096156153155809924644481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64128208204207746566192641 48096156153155809924644481)
    ·
      refine ⟨36072117114866857443483361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48096156153155809924644481 36072117114866857443483361)
      ·
        refine ⟨27054087836150143082612521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36072117114866857443483361 27054087836150143082612521)
        ·
          refine ⟨20290565877112607311959391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27054087836150143082612521 20290565877112607311959391)
          ·
            refine ⟨30435848815668910967939087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20290565877112607311959391 30435848815668910967939087)
            ·
              refine ⟨45653773223503366451908631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30435848815668910967939087 45653773223503366451908631)
              ·
                refine ⟨68480659835255049677862947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45653773223503366451908631 68480659835255049677862947)
                ·
                  refine ⟨102720989752882574516794421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68480659835255049677862947 102720989752882574516794421)
                  ·
                    refine ⟨9630092789332741360949477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 102720989752882574516794421 9630092789332741360949477)
                    ·
                      refine ⟨1805642397999889005178027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9630092789332741360949477 1805642397999889005178027)
                      ·
                        rfl

theorem cell23_3516476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 1, 5, 4].length) (baseStart_3516476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3516476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3516476 prefixEnd_3516476 := by exact prefixLift 3516476
  have htrace : WordTrace (prefixWord ++ tailWord_3516476) baseStart_3516476 baseEnd_3516476 := by
    simpa [prefixWord, tailWord_3516476, baseEnd_3516476] using wordTrace_append hprefix tailTrace_3516476
  have hstable : (prefixWord ++ tailWord_3516476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3516476).length < 2 ^ (prefixWord ++ tailWord_3516476).sum := by decide
  have hdescent : baseEnd_3516476 < baseStart_3516476 := by decide
  rcases family_descends (prefixWord ++ tailWord_3516476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3516493 : List Nat := [1, 6, 1, 1, 1, 1, 1, 2, 2, 3, 4]
def baseStart_3516493 : Nat := 118140960795 + 3516493 * 2 ^ 59
def prefixEnd_3516493 : Nat := 4983230072969 + 3 ^ 40 * 3516493 * 2
def baseEnd_3516493 : Nat := 1805651127171015438665449

theorem tailTrace_3516493 : CollatzResearch.WordTrace tailWord_3516493 prefixEnd_3516493 1805651127171015438665449 := by
  unfold tailWord_3516493
  simp only [CollatzResearch.WordTrace]
  refine ⟨128257036449353905035754133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85504690966235936690502755 128257036449353905035754133)
  ·
    refine ⟨6012048583563464298550975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 128257036449353905035754133 6012048583563464298550975)
    ·
      refine ⟨9018072875345196447826463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6012048583563464298550975 9018072875345196447826463)
      ·
        refine ⟨13527109313017794671739695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9018072875345196447826463 13527109313017794671739695)
        ·
          refine ⟨20290663969526692007609543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13527109313017794671739695 20290663969526692007609543)
          ·
            refine ⟨30435995954290038011414315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20290663969526692007609543 30435995954290038011414315)
            ·
              refine ⟨45653993931435057017121473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30435995954290038011414315 45653993931435057017121473)
              ·
                refine ⟨34240495448576292762841105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45653993931435057017121473 34240495448576292762841105)
                ·
                  refine ⟨25680371586432219572130829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34240495448576292762841105 25680371586432219572130829)
                  ·
                    refine ⟨9630139344912082339549061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25680371586432219572130829 9630139344912082339549061)
                    ·
                      refine ⟨1805651127171015438665449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9630139344912082339549061 1805651127171015438665449)
                      ·
                        rfl

theorem cell23_3516493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_3516493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3516493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3516493 prefixEnd_3516493 := by exact prefixLift 3516493
  have htrace : WordTrace (prefixWord ++ tailWord_3516493) baseStart_3516493 baseEnd_3516493 := by
    simpa [prefixWord, tailWord_3516493, baseEnd_3516493] using wordTrace_append hprefix tailTrace_3516493
  have hstable : (prefixWord ++ tailWord_3516493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3516493).length < 2 ^ (prefixWord ++ tailWord_3516493).sum := by decide
  have hdescent : baseEnd_3516493 < baseStart_3516493 := by decide
  rcases family_descends (prefixWord ++ tailWord_3516493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3516506 : List Nat := [3, 1, 1, 2, 1, 1, 3, 2, 1, 4, 4]
def baseStart_3516506 : Nat := 118140960795 + 3516506 * 2 ^ 59
def prefixEnd_3516506 : Nat := 4983230072969 + 3 ^ 40 * 3516506 * 2
def baseEnd_3516506 : Nat := 1805657802419523887802889

theorem tailTrace_3516506 : CollatzResearch.WordTrace tailWord_3516506 prefixEnd_3516506 1805657802419523887802889 := by
  unfold tailWord_3516506
  simp only [CollatzResearch.WordTrace]
  refine ⟨32064377649576702063994343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85505007065537872170651581 32064377649576702063994343)
  ·
    refine ⟨48096566474365053095991515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32064377649576702063994343 48096566474365053095991515)
    ·
      refine ⟨72144849711547579643987273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48096566474365053095991515 72144849711547579643987273)
      ·
        refine ⟨54108637283660684732990455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72144849711547579643987273 54108637283660684732990455)
        ·
          refine ⟨81162955925491027099485683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54108637283660684732990455 81162955925491027099485683)
          ·
            refine ⟨121744433888236540649228525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81162955925491027099485683 121744433888236540649228525)
            ·
              refine ⟨45654162708088702743460697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 121744433888236540649228525 45654162708088702743460697)
              ·
                refine ⟨34240622031066527057595523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45654162708088702743460697 34240622031066527057595523)
                ·
                  refine ⟨51360933046599790586393285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34240622031066527057595523 51360933046599790586393285)
                  ·
                    refine ⟨9630174946237460734948741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51360933046599790586393285 9630174946237460734948741)
                    ·
                      refine ⟨1805657802419523887802889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9630174946237460734948741 1805657802419523887802889)
                      ·
                        rfl

theorem cell23_3516506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 2, 1, 4, 4].length) (baseStart_3516506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3516506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3516506 prefixEnd_3516506 := by exact prefixLift 3516506
  have htrace : WordTrace (prefixWord ++ tailWord_3516506) baseStart_3516506 baseEnd_3516506 := by
    simpa [prefixWord, tailWord_3516506, baseEnd_3516506] using wordTrace_append hprefix tailTrace_3516506
  have hstable : (prefixWord ++ tailWord_3516506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3516506).length < 2 ^ (prefixWord ++ tailWord_3516506).sum := by decide
  have hdescent : baseEnd_3516506 < baseStart_3516506 := by decide
  rcases family_descends (prefixWord ++ tailWord_3516506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3516514 : List Nat := [3, 3, 2, 2, 2, 1, 1, 3, 1, 3, 2]
def baseStart_3516514 : Nat := 118140960795 + 3516514 * 2 ^ 59
def prefixEnd_3516514 : Nat := 4983230072969 + 3 ^ 40 * 3516514 * 2
def baseEnd_3516514 : Nat := 1805661910264759856502853

theorem tailTrace_3516514 : CollatzResearch.WordTrace tailWord_3516514 prefixEnd_3516514 1805661910264759856502853 := by
  unfold tailWord_3516514
  simp only [CollatzResearch.WordTrace]
  refine ⟨32064450595569456405567149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85505201588185217081512397 32064450595569456405567149)
  ·
    refine ⟨12024168973338546152087681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32064450595569456405567149 12024168973338546152087681)
    ·
      refine ⟨9018126730003909614065761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12024168973338546152087681 9018126730003909614065761)
      ·
        refine ⟨6763595047502932210549321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9018126730003909614065761 6763595047502932210549321)
        ·
          refine ⟨5072696285627199157911991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6763595047502932210549321 5072696285627199157911991)
          ·
            refine ⟨7609044428440798736867987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5072696285627199157911991 7609044428440798736867987)
            ·
              refine ⟨11413566642661198105301981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7609044428440798736867987 11413566642661198105301981)
              ·
                refine ⟨4280087490997949289488243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11413566642661198105301981 4280087490997949289488243)
                ·
                  refine ⟨6420131236496923934232365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4280087490997949289488243 6420131236496923934232365)
                  ·
                    refine ⟨2407549213686346475337137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6420131236496923934232365 2407549213686346475337137)
                    ·
                      refine ⟨1805661910264759856502853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2407549213686346475337137 1805661910264759856502853)
                      ·
                        rfl

theorem cell23_3516514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 3, 1, 3, 2].length) (baseStart_3516514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3516514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3516514 prefixEnd_3516514 := by exact prefixLift 3516514
  have htrace : WordTrace (prefixWord ++ tailWord_3516514) baseStart_3516514 baseEnd_3516514 := by
    simpa [prefixWord, tailWord_3516514, baseEnd_3516514] using wordTrace_append hprefix tailTrace_3516514
  have hstable : (prefixWord ++ tailWord_3516514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3516514).length < 2 ^ (prefixWord ++ tailWord_3516514).sum := by decide
  have hdescent : baseEnd_3516514 < baseStart_3516514 := by decide
  rcases family_descends (prefixWord ++ tailWord_3516514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3516527 : List Nat := [1, 1, 2, 1, 3, 4, 3, 2, 2, 2, 2]
def baseStart_3516527 : Nat := 118140960795 + 3516527 * 2 ^ 59
def prefixEnd_3516527 : Nat := 4983230072969 + 3 ^ 40 * 3516527 * 2
def baseEnd_3516527 : Nat := 1805668585513268305640293

theorem tailTrace_3516527 : CollatzResearch.WordTrace tailWord_3516527 prefixEnd_3516527 1805668585513268305640293 := by
  unfold tailWord_3516527
  simp only [CollatzResearch.WordTrace]
  refine ⟨128258276531230728842491835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85505517687487152561661223 128258276531230728842491835)
  ·
    refine ⟨192387414796846093263737753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128258276531230728842491835 192387414796846093263737753)
    ·
      refine ⟨144290561097634569947803315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192387414796846093263737753 144290561097634569947803315)
      ·
        refine ⟨216435841646451854921704973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144290561097634569947803315 216435841646451854921704973)
        ·
          refine ⟨81163440617419445595639365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 216435841646451854921704973 81163440617419445595639365)
          ·
            refine ⟨15218145115766146049182381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81163440617419445595639365 15218145115766146049182381)
            ·
              refine ⟨5706804418412304768443393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15218145115766146049182381 5706804418412304768443393)
              ·
                refine ⟨4280103313809228576332545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5706804418412304768443393 4280103313809228576332545)
                ·
                  refine ⟨3210077485356921432249409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4280103313809228576332545 3210077485356921432249409)
                  ·
                    refine ⟨2407558114017691074187057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3210077485356921432249409 2407558114017691074187057)
                    ·
                      refine ⟨1805668585513268305640293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2407558114017691074187057 1805668585513268305640293)
                      ·
                        rfl

theorem cell23_3516527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 3, 2, 2, 2, 2].length) (baseStart_3516527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3516527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3516527 prefixEnd_3516527 := by exact prefixLift 3516527
  have htrace : WordTrace (prefixWord ++ tailWord_3516527) baseStart_3516527 baseEnd_3516527 := by
    simpa [prefixWord, tailWord_3516527, baseEnd_3516527] using wordTrace_append hprefix tailTrace_3516527
  have hstable : (prefixWord ++ tailWord_3516527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3516527).length < 2 ^ (prefixWord ++ tailWord_3516527).sum := by decide
  have hdescent : baseEnd_3516527 < baseStart_3516527 := by decide
  rcases family_descends (prefixWord ++ tailWord_3516527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3516556 : List Nat := [2, 2, 1, 2, 1, 1, 1, 1, 5, 2, 5]
def baseStart_3516556 : Nat := 118140960795 + 3516556 * 2 ^ 59
def prefixEnd_3516556 : Nat := 4983230072969 + 3 ^ 40 * 3516556 * 2
def baseEnd_3516556 : Nat := 1805683476452248692177659

theorem tailTrace_3516556 : CollatzResearch.WordTrace tailWord_3516556 prefixEnd_3516556 1805683476452248692177659 := by
  unfold tailWord_3516556
  simp only [CollatzResearch.WordTrace]
  refine ⟨64129667124062833397648761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85506222832083777863531681 64129667124062833397648761)
  ·
    refine ⟨48097250343047125048236571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64129667124062833397648761 48097250343047125048236571)
    ·
      refine ⟨72145875514570687572354857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48097250343047125048236571 72145875514570687572354857)
      ·
        refine ⟨54109406635928015679266143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72145875514570687572354857 54109406635928015679266143)
        ·
          refine ⟨81164109953892023518899215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54109406635928015679266143 81164109953892023518899215)
          ·
            refine ⟨121746164930838035278348823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81164109953892023518899215 121746164930838035278348823)
            ·
              refine ⟨182619247396257052917523235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121746164930838035278348823 182619247396257052917523235)
              ·
                refine ⟨273928871094385579376284853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 182619247396257052917523235 273928871094385579376284853)
                ·
                  refine ⟨25680831665098648066526705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 273928871094385579376284853 25680831665098648066526705)
                  ·
                    refine ⟨19260623748823986049895029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25680831665098648066526705 19260623748823986049895029)
                    ·
                      refine ⟨1805683476452248692177659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19260623748823986049895029 1805683476452248692177659)
                      ·
                        rfl

theorem cell23_3516556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 5, 2, 5].length) (baseStart_3516556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3516556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3516556 prefixEnd_3516556 := by exact prefixLift 3516556
  have htrace : WordTrace (prefixWord ++ tailWord_3516556) baseStart_3516556 baseEnd_3516556 := by
    simpa [prefixWord, tailWord_3516556, baseEnd_3516556] using wordTrace_append hprefix tailTrace_3516556
  have hstable : (prefixWord ++ tailWord_3516556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3516556).length < 2 ^ (prefixWord ++ tailWord_3516556).sum := by decide
  have hdescent : baseEnd_3516556 < baseStart_3516556 := by decide
  rcases family_descends (prefixWord ++ tailWord_3516556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3516567 : List Nat := [1, 1, 3, 3, 4, 2, 1, 3, 5]
def baseStart_3516567 : Nat := 118140960795 + 3516567 * 2 ^ 59
def prefixEnd_3516567 : Nat := 4983230072969 + 3 ^ 40 * 3516567 * 2
def baseEnd_3516567 : Nat := 200632124971049794348901

theorem tailTrace_3516567 : CollatzResearch.WordTrace tailWord_3516567 prefixEnd_3516567 200632124971049794348901 := by
  unfold tailWord_3516567
  simp only [CollatzResearch.WordTrace]
  refine ⟨128259735451085815673947955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85506490300723877115965303 128259735451085815673947955)
  ·
    refine ⟨192389603176628723510921933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128259735451085815673947955 192389603176628723510921933)
    ·
      refine ⟨72146101191235771316595725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192389603176628723510921933 72146101191235771316595725)
      ·
        refine ⟨27054787946713414243723397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72146101191235771316595725 27054787946713414243723397)
        ·
          refine ⟨5072772740008765170698137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27054787946713414243723397 5072772740008765170698137)
          ·
            refine ⟨3804579555006573878023603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5072772740008765170698137 3804579555006573878023603)
            ·
              refine ⟨5706869332509860817035405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3804579555006573878023603 5706869332509860817035405)
              ·
                refine ⟨2140075999691197806388277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5706869332509860817035405 2140075999691197806388277)
                ·
                  refine ⟨200632124971049794348901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2140075999691197806388277 200632124971049794348901)
                  ·
                    rfl

theorem cell23_3516567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 1, 3, 5].length) (baseStart_3516567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3516567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3516567 prefixEnd_3516567 := by exact prefixLift 3516567
  have htrace : WordTrace (prefixWord ++ tailWord_3516567) baseStart_3516567 baseEnd_3516567 := by
    simpa [prefixWord, tailWord_3516567, baseEnd_3516567] using wordTrace_append hprefix tailTrace_3516567
  have hstable : (prefixWord ++ tailWord_3516567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3516567).length < 2 ^ (prefixWord ++ tailWord_3516567).sum := by decide
  have hdescent : baseEnd_3516567 < baseStart_3516567 := by decide
  rcases family_descends (prefixWord ++ tailWord_3516567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3516580 : List Nat := [2, 3, 1, 2, 4, 1, 1, 2, 2, 5]
def baseStart_3516580 : Nat := 118140960795 + 3516580 * 2 ^ 59
def prefixEnd_3516580 : Nat := 4983230072969 + 3 ^ 40 * 3516580 * 2
def baseEnd_3516580 : Nat := 601898599995985532759183

theorem tailTrace_3516580 : CollatzResearch.WordTrace tailWord_3516580 prefixEnd_3516580 601898599995985532759183 := by
  unfold tailWord_3516580
  simp only [CollatzResearch.WordTrace]
  refine ⟨64130104800019359447085597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85506806400025812596114129 64130104800019359447085597)
  ·
    refine ⟨24048789300007259792657099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64130104800019359447085597 24048789300007259792657099)
    ·
      refine ⟨36073183950010889688985649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24048789300007259792657099 36073183950010889688985649)
      ·
        refine ⟨27054887962508167266739237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36073183950010889688985649 27054887962508167266739237)
        ·
          refine ⟨5072791492970281362513607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27054887962508167266739237 5072791492970281362513607)
          ·
            refine ⟨7609187239455422043770411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5072791492970281362513607 7609187239455422043770411)
            ·
              refine ⟨11413780859183133065655617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7609187239455422043770411 11413780859183133065655617)
              ·
                refine ⟨8560335644387349799241713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11413780859183133065655617 8560335644387349799241713)
                ·
                  refine ⟨6420251733290512349431285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8560335644387349799241713 6420251733290512349431285)
                  ·
                    refine ⟨601898599995985532759183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6420251733290512349431285 601898599995985532759183)
                    ·
                      rfl

theorem cell23_3516580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 2, 2, 5].length) (baseStart_3516580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3516580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3516580 prefixEnd_3516580 := by exact prefixLift 3516580
  have htrace : WordTrace (prefixWord ++ tailWord_3516580) baseStart_3516580 baseEnd_3516580 := by
    simpa [prefixWord, tailWord_3516580, baseEnd_3516580] using wordTrace_append hprefix tailTrace_3516580
  have hstable : (prefixWord ++ tailWord_3516580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3516580).length < 2 ^ (prefixWord ++ tailWord_3516580).sum := by decide
  have hdescent : baseEnd_3516580 < baseStart_3516580 := by decide
  rcases family_descends (prefixWord ++ tailWord_3516580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3516603 : List Nat := [1, 1, 1, 1, 1, 2, 5, 2, 4, 2, 3]
def baseStart_3516603 : Nat := 118140960795 + 3516603 * 2 ^ 59
def prefixEnd_3516603 : Nat := 4983230072969 + 3 ^ 40 * 3516603 * 2
def baseEnd_3516603 : Nat := 1805707610043010008289943

theorem tailTrace_3516603 : CollatzResearch.WordTrace tailWord_3516603 prefixEnd_3516603 1805707610043010008289943 := by
  unfold tailWord_3516603
  simp only [CollatzResearch.WordTrace]
  refine ⟨128261048478955393822258463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85507365652636929214838975 128261048478955393822258463)
  ·
    refine ⟨192391572718433090733387695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128261048478955393822258463 192391572718433090733387695)
    ·
      refine ⟨288587359077649636100081543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192391572718433090733387695 288587359077649636100081543)
      ·
        refine ⟨432881038616474454150122315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288587359077649636100081543 432881038616474454150122315)
        ·
          refine ⟨649321557924711681225183473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 432881038616474454150122315 649321557924711681225183473)
          ·
            refine ⟨486991168443533760918887605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 649321557924711681225183473 486991168443533760918887605)
            ·
              refine ⟨45655422041581290086145713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 486991168443533760918887605 45655422041581290086145713)
              ·
                refine ⟨34241566531185967564609285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45655422041581290086145713 34241566531185967564609285)
                ·
                  refine ⟨6420293724597368918364241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34241566531185967564609285 6420293724597368918364241)
                  ·
                    refine ⟨4815220293448026688773181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6420293724597368918364241 4815220293448026688773181)
                    ·
                      refine ⟨1805707610043010008289943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4815220293448026688773181 1805707610043010008289943)
                      ·
                        rfl

theorem cell23_3516603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 2, 4, 2, 3].length) (baseStart_3516603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3516603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3516603 prefixEnd_3516603 := by exact prefixLift 3516603
  have htrace : WordTrace (prefixWord ++ tailWord_3516603) baseStart_3516603 baseEnd_3516603 := by
    simpa [prefixWord, tailWord_3516603, baseEnd_3516603] using wordTrace_append hprefix tailTrace_3516603
  have hstable : (prefixWord ++ tailWord_3516603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3516603).length < 2 ^ (prefixWord ++ tailWord_3516603).sum := by decide
  have hdescent : baseEnd_3516603 < baseStart_3516603 := by decide
  rcases family_descends (prefixWord ++ tailWord_3516603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3516637 : List Nat := [1, 4, 3, 2, 1, 1, 2, 2, 2, 2, 3]
def baseStart_3516637 : Nat := 118140960795 + 3516637 * 2 ^ 59
def prefixEnd_3516637 : Nat := 4983230072969 + 3 ^ 40 * 3516637 * 2
def baseEnd_3516637 : Nat := 1805725068385262875264787

theorem tailTrace_3516637 : CollatzResearch.WordTrace tailWord_3516637 prefixEnd_3516637 1805725068385262875264787 := by
  unfold tailWord_3516637
  simp only [CollatzResearch.WordTrace]
  refine ⟨128262288560832217628996165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85508192373888145085997443 128262288560832217628996165)
  ·
    refine ⟨24049179105156040805436781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128262288560832217628996165 24049179105156040805436781)
    ·
      refine ⟨9018442164433515302038793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24049179105156040805436781 9018442164433515302038793)
      ·
        refine ⟨6763831623325136476529095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9018442164433515302038793 6763831623325136476529095)
        ·
          refine ⟨10145747434987704714793643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6763831623325136476529095 10145747434987704714793643)
          ·
            refine ⟨15218621152481557072190465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10145747434987704714793643 15218621152481557072190465)
            ·
              refine ⟨11413965864361167804142849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15218621152481557072190465 11413965864361167804142849)
              ·
                refine ⟨8560474398270875853107137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11413965864361167804142849 8560474398270875853107137)
                ·
                  refine ⟨6420355798703156889830353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8560474398270875853107137 6420355798703156889830353)
                  ·
                    refine ⟨4815266849027367667372765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6420355798703156889830353 4815266849027367667372765)
                    ·
                      refine ⟨1805725068385262875264787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4815266849027367667372765 1805725068385262875264787)
                      ·
                        rfl

theorem cell23_3516637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_3516637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3516637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3516637 prefixEnd_3516637 := by exact prefixLift 3516637
  have htrace : WordTrace (prefixWord ++ tailWord_3516637) baseStart_3516637 baseEnd_3516637 := by
    simpa [prefixWord, tailWord_3516637, baseEnd_3516637] using wordTrace_append hprefix tailTrace_3516637
  have hstable : (prefixWord ++ tailWord_3516637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3516637).length < 2 ^ (prefixWord ++ tailWord_3516637).sum := by decide
  have hdescent : baseEnd_3516637 < baseStart_3516637 := by decide
  rcases family_descends (prefixWord ++ tailWord_3516637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3516670 : List Nat := [4, 2, 2, 1, 1, 1, 1, 3, 3, 5]
def baseStart_3516670 : Nat := 118140960795 + 3516670 * 2 ^ 59
def prefixEnd_3516670 : Nat := 4983230072969 + 3 ^ 40 * 3516670 * 2
def baseEnd_3516670 : Nat := 601914004415620415384045

theorem tailTrace_3516670 : CollatzResearch.WordTrace tailWord_3516670 prefixEnd_3516670 601914004415620415384045 := by
  unfold tailWord_3516670
  simp only [CollatzResearch.WordTrace]
  refine ⟨16032936521214083033118433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85508994779808442843298309 16032936521214083033118433)
  ·
    refine ⟨12024702390910562274838825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16032936521214083033118433 12024702390910562274838825)
    ·
      refine ⟨9018526793182921706129119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12024702390910562274838825 9018526793182921706129119)
      ·
        refine ⟨13527790189774382559193679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9018526793182921706129119 13527790189774382559193679)
        ·
          refine ⟨20291685284661573838790519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13527790189774382559193679 20291685284661573838790519)
          ·
            refine ⟨30437527926992360758185779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20291685284661573838790519 30437527926992360758185779)
            ·
              refine ⟨45656291890488541137278669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30437527926992360758185779 45656291890488541137278669)
              ·
                refine ⟨17121109458933202926479501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45656291890488541137278669 17121109458933202926479501)
                ·
                  refine ⟨6420416047099951097429813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17121109458933202926479501 6420416047099951097429813)
                  ·
                    refine ⟨601914004415620415384045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6420416047099951097429813 601914004415620415384045)
                    ·
                      rfl

theorem cell23_3516670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 3, 3, 5].length) (baseStart_3516670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3516670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3516670 prefixEnd_3516670 := by exact prefixLift 3516670
  have htrace : WordTrace (prefixWord ++ tailWord_3516670) baseStart_3516670 baseEnd_3516670 := by
    simpa [prefixWord, tailWord_3516670, baseEnd_3516670] using wordTrace_append hprefix tailTrace_3516670
  have hstable : (prefixWord ++ tailWord_3516670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3516670).length < 2 ^ (prefixWord ++ tailWord_3516670).sum := by decide
  have hdescent : baseEnd_3516670 < baseStart_3516670 := by decide
  rcases family_descends (prefixWord ++ tailWord_3516670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3516683 : List Nat := [1, 1, 1, 1, 5, 2, 1, 4, 1, 6]
def baseStart_3516683 : Nat := 118140960795 + 3516683 * 2 ^ 59
def prefixEnd_3516683 : Nat := 4983230072969 + 3 ^ 40 * 3516683 * 2
def baseEnd_3516683 : Nat := 601916229498456565096525

theorem tailTrace_3516683 : CollatzResearch.WordTrace tailWord_3516683 prefixEnd_3516683 601916229498456565096525 := by
  unfold tailWord_3516683
  simp only [CollatzResearch.WordTrace]
  refine ⟨128263966318665567485170703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85509310879110378323447135 128263966318665567485170703)
  ·
    refine ⟨192395949477998351227756055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128263966318665567485170703 192395949477998351227756055)
    ·
      refine ⟨288593924216997526841634083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192395949477998351227756055 288593924216997526841634083)
      ·
        refine ⟨432890886325496290262451125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288593924216997526841634083 432890886325496290262451125)
        ·
          refine ⟨40583520593015277212104793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 432890886325496290262451125 40583520593015277212104793)
          ·
            refine ⟨30437640444761457909078595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40583520593015277212104793 30437640444761457909078595)
            ·
              refine ⟨45656460667142186863617893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30437640444761457909078595 45656460667142186863617893)
              ·
                refine ⟨8560586375089160036928355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45656460667142186863617893 8560586375089160036928355)
                ·
                  refine ⟨12840879562633740055392533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8560586375089160036928355 12840879562633740055392533)
                  ·
                    refine ⟨601916229498456565096525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12840879562633740055392533 601916229498456565096525)
                    ·
                      rfl

theorem cell23_3516683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 4, 1, 6].length) (baseStart_3516683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3516683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3516683 prefixEnd_3516683 := by exact prefixLift 3516683
  have htrace : WordTrace (prefixWord ++ tailWord_3516683) baseStart_3516683 baseEnd_3516683 := by
    simpa [prefixWord, tailWord_3516683, baseEnd_3516683] using wordTrace_append hprefix tailTrace_3516683
  have hstable : (prefixWord ++ tailWord_3516683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3516683).length < 2 ^ (prefixWord ++ tailWord_3516683).sum := by decide
  have hdescent : baseEnd_3516683 < baseStart_3516683 := by decide
  rcases family_descends (prefixWord ++ tailWord_3516683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3516684 : List Nat := [2, 2, 1, 2, 2, 2, 4, 3, 1, 1, 3]
def baseStart_3516684 : Nat := 118140960795 + 3516684 * 2 ^ 59
def prefixEnd_3516684 : Nat := 4983230072969 + 3 ^ 40 * 3516684 * 2
def baseEnd_3516684 : Nat := 1805749201976024191377071

theorem tailTrace_3516684 : CollatzResearch.WordTrace tailWord_3516684 prefixEnd_3516684 1805749201976024191377071 := by
  unfold tailWord_3516684
  simp only [CollatzResearch.WordTrace]
  refine ⟨64132001395830972327978553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85509335194441296437304737 64132001395830972327978553)
  ·
    refine ⟨48099001046873229245983915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64132001395830972327978553 48099001046873229245983915)
    ·
      refine ⟨72148501570309843868975873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48099001046873229245983915 72148501570309843868975873)
      ·
        refine ⟨54111376177732382901731905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72148501570309843868975873 54111376177732382901731905)
        ·
          refine ⟨40583532133299287176298929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54111376177732382901731905 40583532133299287176298929)
          ·
            refine ⟨30437649099974465382224197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40583532133299287176298929 30437649099974465382224197)
            ·
              refine ⟨5707059206245212259167037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30437649099974465382224197 5707059206245212259167037)
              ·
                refine ⟨2140147202341954597187639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5707059206245212259167037 2140147202341954597187639)
                ·
                  refine ⟨3210220803512931895781459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2140147202341954597187639 3210220803512931895781459)
                  ·
                    refine ⟨4815331205269397843672189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3210220803512931895781459 4815331205269397843672189)
                    ·
                      refine ⟨1805749201976024191377071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4815331205269397843672189 1805749201976024191377071)
                      ·
                        rfl

theorem cell23_3516684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 4, 3, 1, 1, 3].length) (baseStart_3516684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3516684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3516684 prefixEnd_3516684 := by exact prefixLift 3516684
  have htrace : WordTrace (prefixWord ++ tailWord_3516684) baseStart_3516684 baseEnd_3516684 := by
    simpa [prefixWord, tailWord_3516684, baseEnd_3516684] using wordTrace_append hprefix tailTrace_3516684
  have hstable : (prefixWord ++ tailWord_3516684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3516684).length < 2 ^ (prefixWord ++ tailWord_3516684).sum := by decide
  have hdescent : baseEnd_3516684 < baseStart_3516684 := by decide
  rcases family_descends (prefixWord ++ tailWord_3516684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3516724 : List Nat := [2, 5, 1, 1, 1, 3, 2, 2, 1, 1, 4]
def baseStart_3516724 : Nat := 118140960795 + 3516724 * 2 ^ 59
def prefixEnd_3516724 : Nat := 4983230072969 + 3 ^ 40 * 3516724 * 2
def baseEnd_3516724 : Nat := 1805769741202204034876887

theorem tailTrace_3516724 : CollatzResearch.WordTrace tailWord_3516724 prefixEnd_3516724 1805769741202204034876887 := by
  unfold tailWord_3516724
  simp only [CollatzResearch.WordTrace]
  refine ⟨64132730855758515743706613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85510307807678020991608817 64132730855758515743706613)
  ·
    refine ⟨6012443517727360850972495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 64132730855758515743706613 6012443517727360850972495)
    ·
      refine ⟨9018665276591041276458743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6012443517727360850972495 9018665276591041276458743)
      ·
        refine ⟨13527997914886561914688115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9018665276591041276458743 13527997914886561914688115)
        ·
          refine ⟨20291996872329842872032173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13527997914886561914688115 20291996872329842872032173)
          ·
            refine ⟨7609498827123691077012065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20291996872329842872032173 7609498827123691077012065)
            ·
              refine ⟨5707124120342768307759049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7609498827123691077012065 5707124120342768307759049)
              ·
                refine ⟨4280343090257076230819287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5707124120342768307759049 4280343090257076230819287)
                ·
                  refine ⟨6420514635385614346228931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4280343090257076230819287 6420514635385614346228931)
                  ·
                    refine ⟨9630771953078421519343397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6420514635385614346228931 9630771953078421519343397)
                    ·
                      refine ⟨1805769741202204034876887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9630771953078421519343397 1805769741202204034876887)
                      ·
                        rfl

theorem cell23_3516724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 2, 2, 1, 1, 4].length) (baseStart_3516724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3516724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3516724 prefixEnd_3516724 := by exact prefixLift 3516724
  have htrace : WordTrace (prefixWord ++ tailWord_3516724) baseStart_3516724 baseEnd_3516724 := by
    simpa [prefixWord, tailWord_3516724, baseEnd_3516724] using wordTrace_append hprefix tailTrace_3516724
  have hstable : (prefixWord ++ tailWord_3516724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3516724).length < 2 ^ (prefixWord ++ tailWord_3516724).sum := by decide
  have hdescent : baseEnd_3516724 < baseStart_3516724 := by decide
  rcases family_descends (prefixWord ++ tailWord_3516724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3516730 : List Nat := [3, 1, 1, 1, 4, 2, 4, 7]
def baseStart_3516730 : Nat := 118140960795 + 3516730 * 2 ^ 59
def prefixEnd_3516730 : Nat := 4983230072969 + 3 ^ 40 * 3516730 * 2
def baseEnd_3516730 : Nat := 66880474892078926348217

theorem tailTrace_3516730 : CollatzResearch.WordTrace tailWord_3516730 prefixEnd_3516730 66880474892078926348217 := by
  unfold tailWord_3516730
  simp only [CollatzResearch.WordTrace]
  refine ⟨32066420137373823628032911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85510453699663529674754429 32066420137373823628032911)
  ·
    refine ⟨48099630206060735442049367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32066420137373823628032911 48099630206060735442049367)
    ·
      refine ⟨72149445309091103163074051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48099630206060735442049367 72149445309091103163074051)
      ·
        refine ⟨108224167963636654744611077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72149445309091103163074051 108224167963636654744611077)
        ·
          refine ⟨20292031493181872764614577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108224167963636654744611077 20292031493181872764614577)
          ·
            refine ⟨15219023619886404573460933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20292031493181872764614577 15219023619886404573460933)
            ·
              refine ⟨2853566928728700857523925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15219023619886404573460933 2853566928728700857523925)
              ·
                refine ⟨66880474892078926348217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2853566928728700857523925 66880474892078926348217)
                ·
                  rfl

theorem cell23_3516730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 4, 7].length) (baseStart_3516730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3516730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3516730 prefixEnd_3516730 := by exact prefixLift 3516730
  have htrace : WordTrace (prefixWord ++ tailWord_3516730) baseStart_3516730 baseEnd_3516730 := by
    simpa [prefixWord, tailWord_3516730, baseEnd_3516730] using wordTrace_append hprefix tailTrace_3516730
  have hstable : (prefixWord ++ tailWord_3516730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3516730).length < 2 ^ (prefixWord ++ tailWord_3516730).sum := by decide
  have hdescent : baseEnd_3516730 < baseStart_3516730 := by decide
  rcases family_descends (prefixWord ++ tailWord_3516730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3516784 : List Nat := [2, 1, 1, 1, 4, 3, 3, 2, 1, 3, 2]
def baseStart_3516784 : Nat := 118140960795 + 3516784 * 2 ^ 59
def prefixEnd_3516784 : Nat := 4983230072969 + 3 ^ 40 * 3516784 * 2
def baseEnd_3516784 : Nat := 1805800550041473800126611

theorem tailTrace_3516784 : CollatzResearch.WordTrace tailWord_3516784 prefixEnd_3516784 1805800550041473800126611 := by
  unfold tailWord_3516784
  simp only [CollatzResearch.WordTrace]
  refine ⟨64133825045649830867298703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85511766727533107823064937 64133825045649830867298703)
  ·
    refine ⟨96200737568474746300948055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64133825045649830867298703 96200737568474746300948055)
    ·
      refine ⟨144301106352712119451422083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96200737568474746300948055 144301106352712119451422083)
      ·
        refine ⟨216451659529068179177133125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144301106352712119451422083 216451659529068179177133125)
        ·
          refine ⟨40584686161700283595712461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 216451659529068179177133125 40584686161700283595712461)
          ·
            refine ⟨15219257310637606348392173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40584686161700283595712461 15219257310637606348392173)
            ·
              refine ⟨5707221491489102380647065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15219257310637606348392173 5707221491489102380647065)
              ·
                refine ⟨4280416118616826785485299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5707221491489102380647065 4280416118616826785485299)
                ·
                  refine ⟨6420624177925240178227949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4280416118616826785485299 6420624177925240178227949)
                  ·
                    refine ⟨2407734066721965066835481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6420624177925240178227949 2407734066721965066835481)
                    ·
                      refine ⟨1805800550041473800126611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2407734066721965066835481 1805800550041473800126611)
                      ·
                        rfl

theorem cell23_3516784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 3, 2, 1, 3, 2].length) (baseStart_3516784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3516784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3516784 prefixEnd_3516784 := by exact prefixLift 3516784
  have htrace : WordTrace (prefixWord ++ tailWord_3516784) baseStart_3516784 baseEnd_3516784 := by
    simpa [prefixWord, tailWord_3516784, baseEnd_3516784] using wordTrace_append hprefix tailTrace_3516784
  have hstable : (prefixWord ++ tailWord_3516784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3516784).length < 2 ^ (prefixWord ++ tailWord_3516784).sum := by decide
  have hdescent : baseEnd_3516784 < baseStart_3516784 := by decide
  rcases family_descends (prefixWord ++ tailWord_3516784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3516797 : List Nat := [1, 4, 1, 1, 2, 3, 1, 1, 3, 4, 2]
def baseStart_3516797 : Nat := 118140960795 + 3516797 * 2 ^ 59
def prefixEnd_3516797 : Nat := 4983230072969 + 3 ^ 40 * 3516797 * 2
def baseEnd_3516797 : Nat := 1805807225289982249264051

theorem tailTrace_3516797 : CollatzResearch.WordTrace tailWord_3516797 prefixEnd_3516797 1805807225289982249264051 := by
  unfold tailWord_3516797
  simp only [CollatzResearch.WordTrace]
  refine ⟨128268124240252564954820645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85512082826835043303213763 128268124240252564954820645)
  ·
    refine ⟨24050273295047355929028871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128268124240252564954820645 24050273295047355929028871)
    ·
      refine ⟨36075409942571033893543307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24050273295047355929028871 36075409942571033893543307)
      ·
        refine ⟨54113114913856550840314961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36075409942571033893543307 54113114913856550840314961)
        ·
          refine ⟨40584836185392413130236221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54113114913856550840314961 40584836185392413130236221)
          ·
            refine ⟨15219313569522154923838583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40584836185392413130236221 15219313569522154923838583)
            ·
              refine ⟨22828970354283232385757875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15219313569522154923838583 22828970354283232385757875)
              ·
                refine ⟨34243455531424848578636813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22828970354283232385757875 34243455531424848578636813)
                ·
                  refine ⟨12841295824284318216988805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34243455531424848578636813 12841295824284318216988805)
                  ·
                    refine ⟨2407742967053309665685401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12841295824284318216988805 2407742967053309665685401)
                    ·
                      refine ⟨1805807225289982249264051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2407742967053309665685401 1805807225289982249264051)
                      ·
                        rfl

theorem cell23_3516797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 1, 3, 4, 2].length) (baseStart_3516797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3516797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3516797 prefixEnd_3516797 := by exact prefixLift 3516797
  have htrace : WordTrace (prefixWord ++ tailWord_3516797) baseStart_3516797 baseEnd_3516797 := by
    simpa [prefixWord, tailWord_3516797, baseEnd_3516797] using wordTrace_append hprefix tailTrace_3516797
  have hstable : (prefixWord ++ tailWord_3516797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3516797).length < 2 ^ (prefixWord ++ tailWord_3516797).sum := by decide
  have hdescent : baseEnd_3516797 < baseStart_3516797 := by decide
  rcases family_descends (prefixWord ++ tailWord_3516797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3516850 : List Nat := [3, 2, 1, 1, 1, 1, 5, 1, 1, 7]
def baseStart_3516850 : Nat := 118140960795 + 3516850 * 2 ^ 59
def prefixEnd_3516850 : Nat := 4983230072969 + 3 ^ 40 * 3516850 * 2
def baseEnd_3516850 : Nat := 601944813254890180633769

theorem tailTrace_3516850 : CollatzResearch.WordTrace tailWord_3516850 prefixEnd_3516850 601944813254890180633769 := by
  unfold tailWord_3516850
  simp only [CollatzResearch.WordTrace]
  refine ⟨32067514327265138751625001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85513371539373703337666669 32067514327265138751625001)
  ·
    refine ⟨24050635745448854063718751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32067514327265138751625001 24050635745448854063718751)
    ·
      refine ⟨36075953618173281095578127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24050635745448854063718751 36075953618173281095578127)
      ·
        refine ⟨54113930427259921643367191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36075953618173281095578127 54113930427259921643367191)
        ·
          refine ⟨81170895640889882465050787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54113930427259921643367191 81170895640889882465050787)
          ·
            refine ⟨121756343461334823697576181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81170895640889882465050787 121756343461334823697576181)
            ·
              refine ⟨11414657199500139721647767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 121756343461334823697576181 11414657199500139721647767)
              ·
                refine ⟨17121985799250209582471651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11414657199500139721647767 17121985799250209582471651)
                ·
                  refine ⟨25682978698875314373707477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17121985799250209582471651 25682978698875314373707477)
                  ·
                    refine ⟨601944813254890180633769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25682978698875314373707477 601944813254890180633769)
                    ·
                      rfl

theorem cell23_3516850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 1, 1, 7].length) (baseStart_3516850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3516850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3516850 prefixEnd_3516850 := by exact prefixLift 3516850
  have htrace : WordTrace (prefixWord ++ tailWord_3516850) baseStart_3516850 baseEnd_3516850 := by
    simpa [prefixWord, tailWord_3516850, baseEnd_3516850] using wordTrace_append hprefix tailTrace_3516850
  have hstable : (prefixWord ++ tailWord_3516850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3516850).length < 2 ^ (prefixWord ++ tailWord_3516850).sum := by decide
  have hdescent : baseEnd_3516850 < baseStart_3516850 := by decide
  rcases family_descends (prefixWord ++ tailWord_3516850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3516852 : List Nat := [2, 5, 2, 2, 1, 2, 2, 1, 1, 3, 2]
def baseStart_3516852 : Nat := 118140960795 + 3516852 * 2 ^ 59
def prefixEnd_3516852 : Nat := 4983230072969 + 3 ^ 40 * 3516852 * 2
def baseEnd_3516852 : Nat := 1805835466725979534076299

theorem tailTrace_3516852 : CollatzResearch.WordTrace tailWord_3516852 prefixEnd_3516852 1805835466725979534076299 := by
  unfold tailWord_3516852
  simp only [CollatzResearch.WordTrace]
  refine ⟨64135065127526654674036405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85513420170035539565381873 64135065127526654674036405)
  ·
    refine ⟨6012662355705623875690913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 64135065127526654674036405 6012662355705623875690913)
    ·
      refine ⟨4509496766779217906768185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6012662355705623875690913 4509496766779217906768185)
      ·
        refine ⟨3382122575084413430076139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4509496766779217906768185 3382122575084413430076139)
        ·
          refine ⟨5073183862626620145114209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3382122575084413430076139 5073183862626620145114209)
          ·
            refine ⟨3804887896969965108835657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5073183862626620145114209 3804887896969965108835657)
            ·
              refine ⟨2853665922727473831626743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3804887896969965108835657 2853665922727473831626743)
              ·
                refine ⟨4280498884091210747440115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2853665922727473831626743 4280498884091210747440115)
                ·
                  refine ⟨6420748326136816121160173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4280498884091210747440115 6420748326136816121160173)
                  ·
                    refine ⟨2407780622301306045435065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6420748326136816121160173 2407780622301306045435065)
                    ·
                      refine ⟨1805835466725979534076299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2407780622301306045435065 1805835466725979534076299)
                      ·
                        rfl

theorem cell23_3516852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_3516852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3516852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3516852 prefixEnd_3516852 := by exact prefixLift 3516852
  have htrace : WordTrace (prefixWord ++ tailWord_3516852) baseStart_3516852 baseEnd_3516852 := by
    simpa [prefixWord, tailWord_3516852, baseEnd_3516852] using wordTrace_append hprefix tailTrace_3516852
  have hstable : (prefixWord ++ tailWord_3516852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3516852).length < 2 ^ (prefixWord ++ tailWord_3516852).sum := by decide
  have hdescent : baseEnd_3516852 < baseStart_3516852 := by decide
  rcases family_descends (prefixWord ++ tailWord_3516852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3516865 : List Nat := [1, 2, 7, 1, 1, 1, 1, 1, 4, 2, 2]
def baseStart_3516865 : Nat := 118140960795 + 3516865 * 2 ^ 59
def prefixEnd_3516865 : Nat := 4983230072969 + 3 ^ 40 * 3516865 * 2
def baseEnd_3516865 : Nat := 1805842141974487983213739

theorem tailTrace_3516865 : CollatzResearch.WordTrace tailWord_3516865 prefixEnd_3516865 1805842141974487983213739 := by
  unfold tailWord_3516865
  simp only [CollatzResearch.WordTrace]
  refine ⟨128270604404006212568296049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85513736269337475045530699 128270604404006212568296049)
  ·
    refine ⟨96202953303004659426222037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128270604404006212568296049 96202953303004659426222037)
    ·
      refine ⟨2254756718039171705302079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 96202953303004659426222037 2254756718039171705302079)
      ·
        refine ⟨3382135077058757557953119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2254756718039171705302079 3382135077058757557953119)
        ·
          refine ⟨5073202615588136336929679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3382135077058757557953119 5073202615588136336929679)
          ·
            refine ⟨7609803923382204505394519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5073202615588136336929679 7609803923382204505394519)
            ·
              refine ⟨11414705885073306758091779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7609803923382204505394519 11414705885073306758091779)
              ·
                refine ⟨17122058827609960137137669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11414705885073306758091779 17122058827609960137137669)
                ·
                  refine ⟨3210386030176867525713313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17122058827609960137137669 3210386030176867525713313)
                  ·
                    refine ⟨2407789522632650644284985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3210386030176867525713313 2407789522632650644284985)
                    ·
                      refine ⟨1805842141974487983213739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2407789522632650644284985 1805842141974487983213739)
                      ·
                        rfl

theorem cell23_3516865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_3516865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3516865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3516865 prefixEnd_3516865 := by exact prefixLift 3516865
  have htrace : WordTrace (prefixWord ++ tailWord_3516865) baseStart_3516865 baseEnd_3516865 := by
    simpa [prefixWord, tailWord_3516865, baseEnd_3516865] using wordTrace_append hprefix tailTrace_3516865
  have hstable : (prefixWord ++ tailWord_3516865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3516865).length < 2 ^ (prefixWord ++ tailWord_3516865).sum := by decide
  have hdescent : baseEnd_3516865 < baseStart_3516865 := by decide
  rcases family_descends (prefixWord ++ tailWord_3516865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3516897 : List Nat := [1, 2, 3, 1, 2, 2, 1, 4, 3, 4]
def baseStart_3516897 : Nat := 118140960795 + 3516897 * 2 ^ 59
def prefixEnd_3516897 : Nat := 4983230072969 + 3 ^ 40 * 3516897 * 2
def baseEnd_3516897 : Nat := 601952857785143952671197

theorem tailTrace_3516897 : CollatzResearch.WordTrace tailWord_3516897 prefixEnd_3516897 601952857785143952671197 := by
  unfold tailWord_3516897
  simp only [CollatzResearch.WordTrace]
  refine ⟨128271771539890282033460945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85514514359926854688973963 128271771539890282033460945)
  ·
    refine ⟨96203828654917711525095709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128271771539890282033460945 96203828654917711525095709)
    ·
      refine ⟨36076435745594141821910891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96203828654917711525095709 36076435745594141821910891)
      ·
        refine ⟨54114653618391212732866337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36076435745594141821910891 54114653618391212732866337)
        ·
          refine ⟨40585990213793409549649753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54114653618391212732866337 40585990213793409549649753)
          ·
            refine ⟨30439492660345057162237315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40585990213793409549649753 30439492660345057162237315)
            ·
              refine ⟨45659238990517585743355973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30439492660345057162237315 45659238990517585743355973)
              ·
                refine ⟨8561107310722047326879245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45659238990517585743355973 8561107310722047326879245)
                ·
                  refine ⟨3210415241520767747579717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8561107310722047326879245 3210415241520767747579717)
                  ·
                    refine ⟨601952857785143952671197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3210415241520767747579717 601952857785143952671197)
                    ·
                      rfl

theorem cell23_3516897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 4, 3, 4].length) (baseStart_3516897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3516897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3516897 prefixEnd_3516897 := by exact prefixLift 3516897
  have htrace : WordTrace (prefixWord ++ tailWord_3516897) baseStart_3516897 baseEnd_3516897 := by
    simpa [prefixWord, tailWord_3516897, baseEnd_3516897] using wordTrace_append hprefix tailTrace_3516897
  have hstable : (prefixWord ++ tailWord_3516897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3516897).length < 2 ^ (prefixWord ++ tailWord_3516897).sum := by decide
  have hdescent : baseEnd_3516897 < baseStart_3516897 := by decide
  rcases family_descends (prefixWord ++ tailWord_3516897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3516907 : List Nat := [1, 1, 1, 1, 2, 3, 4, 3, 2, 2, 3]
def baseStart_3516907 : Nat := 118140960795 + 3516907 * 2 ^ 59
def prefixEnd_3516907 : Nat := 4983230072969 + 3 ^ 40 * 3516907 * 2
def baseEnd_3516907 : Nat := 1805863708161976818888545

theorem tailTrace_3516907 : CollatzResearch.WordTrace tailWord_3516907 prefixEnd_3516907 1805863708161976818888545 := by
  unfold tailWord_3516907
  simp only [CollatzResearch.WordTrace]
  refine ⟨128272136269854053741324975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85514757513236035827549983 128272136269854053741324975)
  ·
    refine ⟨192408204404781080611987463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128272136269854053741324975 192408204404781080611987463)
    ·
      refine ⟨288612306607171620917981195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192408204404781080611987463 288612306607171620917981195)
      ·
        refine ⟨432918459910757431376971793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288612306607171620917981195 432918459910757431376971793)
        ·
          refine ⟨324688844933068073532728845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 432918459910757431376971793 324688844933068073532728845)
          ·
            refine ⟨121758316849900527574773317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 324688844933068073532728845 121758316849900527574773317)
            ·
              refine ⟨22829684409356348920269997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 121758316849900527574773317 22829684409356348920269997)
              ·
                refine ⟨8561131653508630845101249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22829684409356348920269997 8561131653508630845101249)
                ·
                  refine ⟨6420848740131473133825937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8561131653508630845101249 6420848740131473133825937)
                  ·
                    refine ⟨4815636555098604850369453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6420848740131473133825937 4815636555098604850369453)
                    ·
                      refine ⟨1805863708161976818888545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4815636555098604850369453 1805863708161976818888545)
                      ·
                        rfl

theorem cell23_3516907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 3, 2, 2, 3].length) (baseStart_3516907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3516907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3516907 prefixEnd_3516907 := by exact prefixLift 3516907
  have htrace : WordTrace (prefixWord ++ tailWord_3516907) baseStart_3516907 baseEnd_3516907 := by
    simpa [prefixWord, tailWord_3516907, baseEnd_3516907] using wordTrace_append hprefix tailTrace_3516907
  have hstable : (prefixWord ++ tailWord_3516907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3516907).length < 2 ^ (prefixWord ++ tailWord_3516907).sum := by decide
  have hdescent : baseEnd_3516907 < baseStart_3516907 := by decide
  rcases family_descends (prefixWord ++ tailWord_3516907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3516931 : List Nat := [1, 1, 1, 3, 2, 1, 7, 2, 1, 4]
def baseStart_3516931 : Nat := 118140960795 + 3516931 * 2 ^ 59
def prefixEnd_3516931 : Nat := 4983230072969 + 3 ^ 40 * 3516931 * 2
def baseEnd_3516931 : Nat := 601958677232561574996145

theorem tailTrace_3516931 : CollatzResearch.WordTrace tailWord_3516931 prefixEnd_3516931 601958677232561574996145 := by
  unfold tailWord_3516931
  simp only [CollatzResearch.WordTrace]
  refine ⟨128273011621767105840198647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85515341081178070560132431 128273011621767105840198647)
  ·
    refine ⟨192409517432650658760297971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128273011621767105840198647 192409517432650658760297971)
    ·
      refine ⟨288614276148975988140446957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192409517432650658760297971 288614276148975988140446957)
      ·
        refine ⟨108230353555865995552667609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 288614276148975988140446957 108230353555865995552667609)
        ·
          refine ⟨81172765166899496664500707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108230353555865995552667609 81172765166899496664500707)
          ·
            refine ⟨121759147750349244996751061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81172765166899496664500707 121759147750349244996751061)
            ·
              refine ⟨2853730025398810429611353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 121759147750349244996751061 2853730025398810429611353)
              ·
                refine ⟨2140297519049107822208515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2853730025398810429611353 2140297519049107822208515)
                ·
                  refine ⟨3210446278573661733312773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2140297519049107822208515 3210446278573661733312773)
                  ·
                    refine ⟨601958677232561574996145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3210446278573661733312773 601958677232561574996145)
                    ·
                      rfl

theorem cell23_3516931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 7, 2, 1, 4].length) (baseStart_3516931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3516931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3516931 prefixEnd_3516931 := by exact prefixLift 3516931
  have htrace : WordTrace (prefixWord ++ tailWord_3516931) baseStart_3516931 baseEnd_3516931 := by
    simpa [prefixWord, tailWord_3516931, baseEnd_3516931] using wordTrace_append hprefix tailTrace_3516931
  have hstable : (prefixWord ++ tailWord_3516931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3516931).length < 2 ^ (prefixWord ++ tailWord_3516931).sum := by decide
  have hdescent : baseEnd_3516931 < baseStart_3516931 := by decide
  rcases family_descends (prefixWord ++ tailWord_3516931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3516954 : List Nat := [3, 1, 1, 3, 1, 1, 2, 4, 3, 1, 3]
def baseStart_3516954 : Nat := 118140960795 + 3516954 * 2 ^ 59
def prefixEnd_3516954 : Nat := 4983230072969 + 3 ^ 40 * 3516954 * 2
def baseEnd_3516954 : Nat := 1805887841752738135000829

theorem tailTrace_3516954 : CollatzResearch.WordTrace tailWord_3516954 prefixEnd_3516954 1805887841752738135000829 := by
  unfold tailWord_3516954
  simp only [CollatzResearch.WordTrace]
  refine ⟨32068462625170945192071479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85515900333789187178857277 32068462625170945192071479)
  ·
    refine ⟨48102693937756417788107219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32068462625170945192071479 48102693937756417788107219)
    ·
      refine ⟨72154040906634626682160829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48102693937756417788107219 72154040906634626682160829)
      ·
        refine ⟨27057765339987985005810311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72154040906634626682160829 27057765339987985005810311)
        ·
          refine ⟨40586648009981977508715467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27057765339987985005810311 40586648009981977508715467)
          ·
            refine ⟨60879972014972966263073201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40586648009981977508715467 60879972014972966263073201)
            ·
              refine ⟨45659979011229724697304901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60879972014972966263073201 45659979011229724697304901)
              ·
                refine ⟨8561246064605573380744669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45659979011229724697304901 8561246064605573380744669)
                ·
                  refine ⟨3210467274227090017779251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8561246064605573380744669 3210467274227090017779251)
                  ·
                    refine ⟨4815700911340635026668877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3210467274227090017779251 4815700911340635026668877)
                    ·
                      refine ⟨1805887841752738135000829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4815700911340635026668877 1805887841752738135000829)
                      ·
                        rfl

theorem cell23_3516954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 4, 3, 1, 3].length) (baseStart_3516954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3516954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3516954 prefixEnd_3516954 := by exact prefixLift 3516954
  have htrace : WordTrace (prefixWord ++ tailWord_3516954) baseStart_3516954 baseEnd_3516954 := by
    simpa [prefixWord, tailWord_3516954, baseEnd_3516954] using wordTrace_append hprefix tailTrace_3516954
  have hstable : (prefixWord ++ tailWord_3516954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3516954).length < 2 ^ (prefixWord ++ tailWord_3516954).sum := by decide
  have hdescent : baseEnd_3516954 < baseStart_3516954 := by decide
  rcases family_descends (prefixWord ++ tailWord_3516954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3516988 : List Nat := [2, 2, 2, 2, 3, 2, 1, 4, 1, 1, 3]
def baseStart_3516988 : Nat := 118140960795 + 3516988 * 2 ^ 59
def prefixEnd_3516988 : Nat := 4983230072969 + 3 ^ 40 * 3516988 * 2
def baseEnd_3516988 : Nat := 1805905300094991001975673

theorem tailTrace_3516988 : CollatzResearch.WordTrace tailWord_3516988 prefixEnd_3516988 1805905300094991001975673 := by
  unfold tailWord_3516988
  simp only [CollatzResearch.WordTrace]
  refine ⟨64137545291280302287511809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85516727055040403050015745 64137545291280302287511809)
  ·
    refine ⟨48103158968460226715633857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64137545291280302287511809 48103158968460226715633857)
    ·
      refine ⟨36077369226345170036725393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48103158968460226715633857 36077369226345170036725393)
      ·
        refine ⟨27058026919758877527544045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36077369226345170036725393 27058026919758877527544045)
        ·
          refine ⟨10146760094909579072829017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27058026919758877527544045 10146760094909579072829017)
          ·
            refine ⟨7610070071182184304621763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10146760094909579072829017 7610070071182184304621763)
            ·
              refine ⟨11415105106773276456932645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7610070071182184304621763 11415105106773276456932645)
              ·
                refine ⟨2140332207519989335674871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11415105106773276456932645 2140332207519989335674871)
                ·
                  refine ⟨3210498311279984003512307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2140332207519989335674871 3210498311279984003512307)
                  ·
                    refine ⟨4815747466919976005268461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3210498311279984003512307 4815747466919976005268461)
                    ·
                      refine ⟨1805905300094991001975673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4815747466919976005268461 1805905300094991001975673)
                      ·
                        rfl

theorem cell23_3516988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 4, 1, 1, 3].length) (baseStart_3516988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3516988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3516988 prefixEnd_3516988 := by exact prefixLift 3516988
  have htrace : WordTrace (prefixWord ++ tailWord_3516988) baseStart_3516988 baseEnd_3516988 := by
    simpa [prefixWord, tailWord_3516988, baseEnd_3516988] using wordTrace_append hprefix tailTrace_3516988
  have hstable : (prefixWord ++ tailWord_3516988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3516988).length < 2 ^ (prefixWord ++ tailWord_3516988).sum := by decide
  have hdescent : baseEnd_3516988 < baseStart_3516988 := by decide
  rcases family_descends (prefixWord ++ tailWord_3516988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3517004 : List Nat := [2, 2, 1, 3, 1, 2, 1, 5, 2, 4]
def baseStart_3517004 : Nat := 118140960795 + 3517004 * 2 ^ 59
def prefixEnd_3517004 : Nat := 4983230072969 + 3 ^ 40 * 3517004 * 2
def baseEnd_3517004 : Nat := 601971171928487646458533

theorem tailTrace_3517004 : CollatzResearch.WordTrace tailWord_3517004 prefixEnd_3517004 601971171928487646458533 := by
  unfold tailWord_3517004
  simp only [CollatzResearch.WordTrace]
  refine ⟨64137837075251319653803033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85517116100335092871737377 64137837075251319653803033)
  ·
    refine ⟨48103377806438489740352275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64137837075251319653803033 48103377806438489740352275)
    ·
      refine ⟨72155066709657734610528413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48103377806438489740352275 72155066709657734610528413)
      ·
        refine ⟨27058150016121650478948155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72155066709657734610528413 27058150016121650478948155)
        ·
          refine ⟨40587225024182475718422233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27058150016121650478948155 40587225024182475718422233)
          ·
            refine ⟨30440418768136856788816675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40587225024182475718422233 30440418768136856788816675)
            ·
              refine ⟨45660628152205285183225013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30440418768136856788816675 45660628152205285183225013)
              ·
                refine ⟨4280683889269245485927345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45660628152205285183225013 4280683889269245485927345)
                ·
                  refine ⟨3210512916951934114445509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4280683889269245485927345 3210512916951934114445509)
                  ·
                    refine ⟨601971171928487646458533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3210512916951934114445509 601971171928487646458533)
                    ·
                      rfl

theorem cell23_3517004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 5, 2, 4].length) (baseStart_3517004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3517004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3517004 prefixEnd_3517004 := by exact prefixLift 3517004
  have htrace : WordTrace (prefixWord ++ tailWord_3517004) baseStart_3517004 baseEnd_3517004 := by
    simpa [prefixWord, tailWord_3517004, baseEnd_3517004] using wordTrace_append hprefix tailTrace_3517004
  have hstable : (prefixWord ++ tailWord_3517004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3517004).length < 2 ^ (prefixWord ++ tailWord_3517004).sum := by decide
  have hdescent : baseEnd_3517004 < baseStart_3517004 := by decide
  rcases family_descends (prefixWord ++ tailWord_3517004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3517007 : List Nat := [1, 1, 2, 1, 1, 2, 5, 3, 1, 2, 4]
def baseStart_3517007 : Nat := 118140960795 + 3517007 * 2 ^ 59
def prefixEnd_3517007 : Nat := 4983230072969 + 3 ^ 40 * 3517007 * 2
def baseEnd_3517007 : Nat := 1805915056227426427638085

theorem tailTrace_3517007 : CollatzResearch.WordTrace tailWord_3517007 prefixEnd_3517007 1805915056227426427638085 := by
  unfold tailWord_3517007
  simp only [CollatzResearch.WordTrace]
  refine ⟨128275783569491770819965275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85517189046327847213310183 128275783569491770819965275)
  ·
    refine ⟨192413675354237656229947913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128275783569491770819965275 192413675354237656229947913)
    ·
      refine ⟨144310256515678242172460935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192413675354237656229947913 144310256515678242172460935)
      ·
        refine ⟨216465384773517363258691403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144310256515678242172460935 216465384773517363258691403)
        ·
          refine ⟨324698077160276044888037105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216465384773517363258691403 324698077160276044888037105)
          ·
            refine ⟨243523557870207033666027829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 324698077160276044888037105 243523557870207033666027829)
            ·
              refine ⟨22830333550331909406190109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 243523557870207033666027829 22830333550331909406190109)
              ·
                refine ⟨8561375081374466027321291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22830333550331909406190109 8561375081374466027321291)
                ·
                  refine ⟨12842062622061699040981937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8561375081374466027321291 12842062622061699040981937)
                  ·
                    refine ⟨9631546966546274280736453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12842062622061699040981937 9631546966546274280736453)
                    ·
                      refine ⟨1805915056227426427638085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9631546966546274280736453 1805915056227426427638085)
                      ·
                        rfl

theorem cell23_3517007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 3, 1, 2, 4].length) (baseStart_3517007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3517007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3517007 prefixEnd_3517007 := by exact prefixLift 3517007
  have htrace : WordTrace (prefixWord ++ tailWord_3517007) baseStart_3517007 baseEnd_3517007 := by
    simpa [prefixWord, tailWord_3517007, baseEnd_3517007] using wordTrace_append hprefix tailTrace_3517007
  have hstable : (prefixWord ++ tailWord_3517007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3517007).length < 2 ^ (prefixWord ++ tailWord_3517007).sum := by decide
  have hdescent : baseEnd_3517007 < baseStart_3517007 := by decide
  rcases family_descends (prefixWord ++ tailWord_3517007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3517038 : List Nat := [4, 1, 2, 2, 2, 3, 1, 2, 2, 4]
def baseStart_3517038 : Nat := 118140960795 + 3517038 * 2 ^ 59
def prefixEnd_3517038 : Nat := 4983230072969 + 3 ^ 40 * 3517038 * 2
def baseEnd_3517038 : Nat := 601976991375905268783481

theorem tailTrace_3517038 : CollatzResearch.WordTrace tailWord_3517038 prefixEnd_3517038 601976991375905268783481 := by
  unfold tailWord_3517038
  simp only [CollatzResearch.WordTrace]
  refine ⟨16034614279047432889292971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85517942821586308742895845 16034614279047432889292971)
  ·
    refine ⟨24051921418571149333939457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16034614279047432889292971 24051921418571149333939457)
    ·
      refine ⟨18038941063928362000454593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24051921418571149333939457 18038941063928362000454593)
      ·
        refine ⟨13529205797946271500340945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18038941063928362000454593 13529205797946271500340945)
        ·
          refine ⟨10146904348459703625255709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13529205797946271500340945 10146904348459703625255709)
          ·
            refine ⟨3805089130672388859470891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10146904348459703625255709 3805089130672388859470891)
            ·
              refine ⟨5707633696008583289206337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3805089130672388859470891 5707633696008583289206337)
              ·
                refine ⟨4280725272006437466904753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5707633696008583289206337 4280725272006437466904753)
                ·
                  refine ⟨3210543954004828100178565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4280725272006437466904753 3210543954004828100178565)
                  ·
                    refine ⟨601976991375905268783481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3210543954004828100178565 601976991375905268783481)
                    ·
                      rfl

theorem cell23_3517038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 1, 2, 2, 4].length) (baseStart_3517038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3517038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3517038 prefixEnd_3517038 := by exact prefixLift 3517038
  have htrace : WordTrace (prefixWord ++ tailWord_3517038) baseStart_3517038 baseEnd_3517038 := by
    simpa [prefixWord, tailWord_3517038, baseEnd_3517038] using wordTrace_append hprefix tailTrace_3517038
  have hstable : (prefixWord ++ tailWord_3517038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3517038).length < 2 ^ (prefixWord ++ tailWord_3517038).sum := by decide
  have hdescent : baseEnd_3517038 < baseStart_3517038 := by decide
  rcases family_descends (prefixWord ++ tailWord_3517038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3517045 : List Nat := [1, 3, 4, 2, 2, 1, 2, 1, 3, 2, 2]
def baseStart_3517045 : Nat := 118140960795 + 3517045 * 2 ^ 59
def prefixEnd_3517045 : Nat := 4983230072969 + 3 ^ 40 * 3517045 * 2
def baseEnd_3517045 : Nat := 1805934568492297278962911

theorem tailTrace_3517045 : CollatzResearch.WordTrace tailWord_3517045 prefixEnd_3517045 1805934568492297278962911 := by
  unfold tailWord_3517045
  simp only [CollatzResearch.WordTrace]
  refine ⟨128277169543354103309848589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85518113028902735539899059 128277169543354103309848589)
  ·
    refine ⟨48103938578757788741193221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128277169543354103309848589 48103938578757788741193221)
    ·
      refine ⟨9019488483517085388973729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48103938578757788741193221 9019488483517085388973729)
      ·
        refine ⟨6764616362637814041730297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9019488483517085388973729 6764616362637814041730297)
        ·
          refine ⟨5073462271978360531297723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6764616362637814041730297 5073462271978360531297723)
          ·
            refine ⟨7610193407967540796946585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5073462271978360531297723 7610193407967540796946585)
            ·
              refine ⟨5707645055975655597709939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7610193407967540796946585 5707645055975655597709939)
              ·
                refine ⟨8561467583963483396564909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5707645055975655597709939 8561467583963483396564909)
                ·
                  refine ⟨3210550343986306273711841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8561467583963483396564909 3210550343986306273711841)
                  ·
                    refine ⟨2407912757989729705283881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3210550343986306273711841 2407912757989729705283881)
                    ·
                      refine ⟨1805934568492297278962911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2407912757989729705283881 1805934568492297278962911)
                      ·
                        rfl

theorem cell23_3517045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 2, 1, 3, 2, 2].length) (baseStart_3517045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3517045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3517045 prefixEnd_3517045 := by exact prefixLift 3517045
  have htrace : WordTrace (prefixWord ++ tailWord_3517045) baseStart_3517045 baseEnd_3517045 := by
    simpa [prefixWord, tailWord_3517045, baseEnd_3517045] using wordTrace_append hprefix tailTrace_3517045
  have hstable : (prefixWord ++ tailWord_3517045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3517045).length < 2 ^ (prefixWord ++ tailWord_3517045).sum := by decide
  have hdescent : baseEnd_3517045 < baseStart_3517045 := by decide
  rcases family_descends (prefixWord ++ tailWord_3517045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3517061 : List Nat := [1, 3, 1, 1, 4, 4, 1, 1, 1, 3, 3]
def baseStart_3517061 : Nat := 118140960795 + 3517061 * 2 ^ 59
def prefixEnd_3517061 : Nat := 4983230072969 + 3 ^ 40 * 3517061 * 2
def baseEnd_3517061 : Nat := 1805942784182769216362837

theorem tailTrace_3517061 : CollatzResearch.WordTrace tailWord_3517061 prefixEnd_3517061 1805942784182769216362837 := by
  unfold tailWord_3517061
  simp only [CollatzResearch.WordTrace]
  refine ⟨128277753111296138042431037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85518502074197425361620691 128277753111296138042431037)
  ·
    refine ⟨48104157416736051765911639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128277753111296138042431037 48104157416736051765911639)
    ·
      refine ⟨72156236125104077648867459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48104157416736051765911639 72156236125104077648867459)
      ·
        refine ⟨108234354187656116473301189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72156236125104077648867459 108234354187656116473301189)
        ·
          refine ⟨20293941410185521838743973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108234354187656116473301189 20293941410185521838743973)
          ·
            refine ⟨3805114014409785344764495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20293941410185521838743973 3805114014409785344764495)
            ·
              refine ⟨5707671021614678017146743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3805114014409785344764495 5707671021614678017146743)
              ·
                refine ⟨8561506532422017025720115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5707671021614678017146743 8561506532422017025720115)
                ·
                  refine ⟨12842259798633025538580173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8561506532422017025720115 12842259798633025538580173)
                  ·
                    refine ⟨4815847424487384576967565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12842259798633025538580173 4815847424487384576967565)
                    ·
                      refine ⟨1805942784182769216362837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4815847424487384576967565 1805942784182769216362837)
                      ·
                        rfl

theorem cell23_3517061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 1, 1, 1, 3, 3].length) (baseStart_3517061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3517061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3517061 prefixEnd_3517061 := by exact prefixLift 3517061
  have htrace : WordTrace (prefixWord ++ tailWord_3517061) baseStart_3517061 baseEnd_3517061 := by
    simpa [prefixWord, tailWord_3517061, baseEnd_3517061] using wordTrace_append hprefix tailTrace_3517061
  have hstable : (prefixWord ++ tailWord_3517061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3517061).length < 2 ^ (prefixWord ++ tailWord_3517061).sum := by decide
  have hdescent : baseEnd_3517061 < baseStart_3517061 := by decide
  rcases family_descends (prefixWord ++ tailWord_3517061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3517074 : List Nat := [3, 2, 3, 1, 2, 1, 1, 1, 2, 2, 5]
def baseStart_3517074 : Nat := 118140960795 + 3517074 * 2 ^ 59
def prefixEnd_3517074 : Nat := 4983230072969 + 3 ^ 40 * 3517074 * 2
def baseEnd_3517074 : Nat := 1805949459431277665500277

theorem tailTrace_3517074 : CollatzResearch.WordTrace tailWord_3517074 prefixEnd_3517074 1805949459431277665500277 := by
  unfold tailWord_3517074
  simp only [CollatzResearch.WordTrace]
  refine ⟨32069556815062260315663569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85518818173499360841769517 32069556815062260315663569)
  ·
    refine ⟨24052167611296695236747677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32069556815062260315663569 24052167611296695236747677)
    ·
      refine ⟨9019562854236260713780379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24052167611296695236747677 9019562854236260713780379)
      ·
        refine ⟨13529344281354391070670569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9019562854236260713780379 13529344281354391070670569)
        ·
          refine ⟨10147008211015793303002927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13529344281354391070670569 10147008211015793303002927)
          ·
            refine ⟨15220512316523689954504391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10147008211015793303002927 15220512316523689954504391)
            ·
              refine ⟨22830768474785534931756587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15220512316523689954504391 22830768474785534931756587)
              ·
                refine ⟨34246152712178302397634881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22830768474785534931756587 34246152712178302397634881)
                ·
                  refine ⟨25684614534133726798226161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34246152712178302397634881 25684614534133726798226161)
                  ·
                    refine ⟨19263460900600295098669621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25684614534133726798226161 19263460900600295098669621)
                    ·
                      refine ⟨1805949459431277665500277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19263460900600295098669621 1805949459431277665500277)
                      ·
                        rfl

theorem cell23_3517074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_3517074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3517074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3517074 prefixEnd_3517074 := by exact prefixLift 3517074
  have htrace : WordTrace (prefixWord ++ tailWord_3517074) baseStart_3517074 baseEnd_3517074 := by
    simpa [prefixWord, tailWord_3517074, baseEnd_3517074] using wordTrace_append hprefix tailTrace_3517074
  have hstable : (prefixWord ++ tailWord_3517074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3517074).length < 2 ^ (prefixWord ++ tailWord_3517074).sum := by decide
  have hdescent : baseEnd_3517074 < baseStart_3517074 := by decide
  rcases family_descends (prefixWord ++ tailWord_3517074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3517191 : List Nat := [1, 1, 4, 4, 1, 2, 1, 1, 1, 3, 4]
def baseStart_3517191 : Nat := 118140960795 + 3517191 * 2 ^ 59
def prefixEnd_3517191 : Nat := 4983230072969 + 3 ^ 40 * 3517191 * 2
def baseEnd_3517191 : Nat := 1806009536667853707737239

theorem tailTrace_3517191 : CollatzResearch.WordTrace tailWord_3517191 prefixEnd_3517191 1806009536667853707737239 := by
  unfold tailWord_3517191
  simp only [CollatzResearch.WordTrace]
  refine ⟨128282494600825170244663427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85521663067216780163108951 128282494600825170244663427)
  ·
    refine ⟨192423741901237755366995141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128282494600825170244663427 192423741901237755366995141)
    ·
      refine ⟨36079451606482079131311589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 192423741901237755366995141 36079451606482079131311589)
      ·
        refine ⟨6764897176215389837120923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36079451606482079131311589 6764897176215389837120923)
        ·
          refine ⟨10147345764323084755681385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6764897176215389837120923 10147345764323084755681385)
          ·
            refine ⟨7610509323242313566761039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10147345764323084755681385 7610509323242313566761039)
            ·
              refine ⟨11415763984863470350141559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7610509323242313566761039 11415763984863470350141559)
              ·
                refine ⟨17123645977295205525212339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11415763984863470350141559 17123645977295205525212339)
                ·
                  refine ⟨25685468965942808287818509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17123645977295205525212339 25685468965942808287818509)
                  ·
                    refine ⟨9632050862228553107931941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25685468965942808287818509 9632050862228553107931941)
                    ·
                      refine ⟨1806009536667853707737239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9632050862228553107931941 1806009536667853707737239)
                      ·
                        rfl

theorem cell23_3517191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_3517191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3517191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3517191 prefixEnd_3517191 := by exact prefixLift 3517191
  have htrace : WordTrace (prefixWord ++ tailWord_3517191) baseStart_3517191 baseEnd_3517191 := by
    simpa [prefixWord, tailWord_3517191, baseEnd_3517191] using wordTrace_append hprefix tailTrace_3517191
  have hstable : (prefixWord ++ tailWord_3517191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3517191).length < 2 ^ (prefixWord ++ tailWord_3517191).sum := by decide
  have hdescent : baseEnd_3517191 < baseStart_3517191 := by decide
  rcases family_descends (prefixWord ++ tailWord_3517191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3517218 : List Nat := [3, 3, 1, 1, 2, 3, 2, 1, 3, 4]
def baseStart_3517218 : Nat := 118140960795 + 3517218 * 2 ^ 59
def prefixEnd_3517218 : Nat := 4983230072969 + 3 ^ 40 * 3517218 * 2
def baseEnd_3517218 : Nat := 602007800215175034033205

theorem tailTrace_3517218 : CollatzResearch.WordTrace tailWord_3517218 prefixEnd_3517218 602007800215175034033205 := by
  unfold tailWord_3517218
  simp only [CollatzResearch.WordTrace]
  refine ⟨32070869842931838463974077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85522319581151569237264205 32070869842931838463974077)
  ·
    refine ⟨12026576191099439423990279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32070869842931838463974077 12026576191099439423990279)
    ·
      refine ⟨18039864286649159135985419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12026576191099439423990279 18039864286649159135985419)
      ·
        refine ⟨27059796429973738703978129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18039864286649159135985419 27059796429973738703978129)
        ·
          refine ⟨20294847322480304027983597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27059796429973738703978129 20294847322480304027983597)
          ·
            refine ⟨7610567745930114010493849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20294847322480304027983597 7610567745930114010493849)
            ·
              refine ⟨5707925809447585507870387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7610567745930114010493849 5707925809447585507870387)
              ·
                refine ⟨8561888714171378261805581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5707925809447585507870387 8561888714171378261805581)
                ·
                  refine ⟨3210708267814266848177093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8561888714171378261805581 3210708267814266848177093)
                  ·
                    refine ⟨602007800215175034033205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3210708267814266848177093 602007800215175034033205)
                    ·
                      rfl

theorem cell23_3517218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 2, 1, 3, 4].length) (baseStart_3517218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3517218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3517218 prefixEnd_3517218 := by exact prefixLift 3517218
  have htrace : WordTrace (prefixWord ++ tailWord_3517218) baseStart_3517218 baseEnd_3517218 := by
    simpa [prefixWord, tailWord_3517218, baseEnd_3517218] using wordTrace_append hprefix tailTrace_3517218
  have hstable : (prefixWord ++ tailWord_3517218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3517218).length < 2 ^ (prefixWord ++ tailWord_3517218).sum := by decide
  have hdescent : baseEnd_3517218 < baseStart_3517218 := by decide
  rcases family_descends (prefixWord ++ tailWord_3517218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3517234 : List Nat := [3, 2, 1, 1, 3, 1, 1, 2, 1, 2, 6]
def baseStart_3517234 : Nat := 118140960795 + 3517234 * 2 ^ 59
def prefixEnd_3517234 : Nat := 4983230072969 + 3 ^ 40 * 3517234 * 2
def baseEnd_3517234 : Nat := 1806031616335997039499541

theorem tailTrace_3517234 : CollatzResearch.WordTrace tailWord_3517234 prefixEnd_3517234 1806031616335997039499541 := by
  unfold tailWord_3517234
  simp only [CollatzResearch.WordTrace]
  refine ⟨32071015734917347147119689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85522708626446259058985837 32071015734917347147119689)
  ·
    refine ⟨24053261801188010360339767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32071015734917347147119689 24053261801188010360339767)
    ·
      refine ⟨36079892701782015540509651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24053261801188010360339767 36079892701782015540509651)
      ·
        refine ⟨54119839052673023310764477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36079892701782015540509651 54119839052673023310764477)
        ·
          refine ⟨20294939644752383741536679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54119839052673023310764477 20294939644752383741536679)
          ·
            refine ⟨30442409467128575612305019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20294939644752383741536679 30442409467128575612305019)
            ·
              refine ⟨45663614200692863418457529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30442409467128575612305019 45663614200692863418457529)
              ·
                refine ⟨34247710650519647563843147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45663614200692863418457529 34247710650519647563843147)
                ·
                  refine ⟨51371565975779471345764721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34247710650519647563843147 51371565975779471345764721)
                  ·
                    refine ⟨38528674481834603509323541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51371565975779471345764721 38528674481834603509323541)
                    ·
                      refine ⟨1806031616335997039499541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38528674481834603509323541 1806031616335997039499541)
                      ·
                        rfl

theorem cell23_3517234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 2, 1, 2, 6].length) (baseStart_3517234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3517234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3517234 prefixEnd_3517234 := by exact prefixLift 3517234
  have htrace : WordTrace (prefixWord ++ tailWord_3517234) baseStart_3517234 baseEnd_3517234 := by
    simpa [prefixWord, tailWord_3517234, baseEnd_3517234] using wordTrace_append hprefix tailTrace_3517234
  have hstable : (prefixWord ++ tailWord_3517234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3517234).length < 2 ^ (prefixWord ++ tailWord_3517234).sum := by decide
  have hdescent : baseEnd_3517234 < baseStart_3517234 := by decide
  rcases family_descends (prefixWord ++ tailWord_3517234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3517251 : List Nat := [1, 1, 1, 3, 1, 4, 1, 3, 1, 5, 2]
def baseStart_3517251 : Nat := 118140960795 + 3517251 * 2 ^ 59
def prefixEnd_3517251 : Nat := 4983230072969 + 3 ^ 40 * 3517251 * 2
def baseEnd_3517251 : Nat := 1806040345507123472986963

theorem tailTrace_3517251 : CollatzResearch.WordTrace tailWord_3517251 prefixEnd_3517251 1806040345507123472986963 := by
  unfold tailWord_3517251
  simp only [CollatzResearch.WordTrace]
  refine ⟨128284682980607800491847607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85523121987071866994565071 128284682980607800491847607)
  ·
    refine ⟨192427024470911700737771411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128284682980607800491847607 192427024470911700737771411)
    ·
      refine ⟨288640536706367551106657117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192427024470911700737771411 288640536706367551106657117)
      ·
        refine ⟨108240201264887831664996419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 288640536706367551106657117 108240201264887831664996419)
        ·
          refine ⟨162360301897331747497494629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108240201264887831664996419 162360301897331747497494629)
          ·
            refine ⟨30442556605749702655780243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 162360301897331747497494629 30442556605749702655780243)
            ·
              refine ⟨45663834908624553983670365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30442556605749702655780243 45663834908624553983670365)
              ·
                refine ⟨17123938090734207743876387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45663834908624553983670365 17123938090734207743876387)
                ·
                  refine ⟨25685907136101311615814581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17123938090734207743876387 25685907136101311615814581)
                  ·
                    refine ⟨2408053794009497963982617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25685907136101311615814581 2408053794009497963982617)
                    ·
                      refine ⟨1806040345507123472986963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2408053794009497963982617 1806040345507123472986963)
                      ·
                        rfl

theorem cell23_3517251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 3, 1, 5, 2].length) (baseStart_3517251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3517251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3517251 prefixEnd_3517251 := by exact prefixLift 3517251
  have htrace : WordTrace (prefixWord ++ tailWord_3517251) baseStart_3517251 baseEnd_3517251 := by
    simpa [prefixWord, tailWord_3517251, baseEnd_3517251] using wordTrace_append hprefix tailTrace_3517251
  have hstable : (prefixWord ++ tailWord_3517251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3517251).length < 2 ^ (prefixWord ++ tailWord_3517251).sum := by decide
  have hdescent : baseEnd_3517251 < baseStart_3517251 := by decide
  rcases family_descends (prefixWord ++ tailWord_3517251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3517281 : List Nat := [1, 2, 3, 1, 1, 1, 2, 2, 2, 6, 2]
def baseStart_3517281 : Nat := 118140960795 + 3517281 * 2 ^ 59
def prefixEnd_3517281 : Nat := 4983230072969 + 3 ^ 40 * 3517281 * 2
def baseEnd_3517281 : Nat := 1806055749926758355611825

theorem tailTrace_3517281 : CollatzResearch.WordTrace tailWord_3517281 prefixEnd_3517281 1806055749926758355611825 := by
  unfold tailWord_3517281
  simp only [CollatzResearch.WordTrace]
  refine ⟨128285777170499115615439697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85523851446999410410293131 128285777170499115615439697)
  ·
    refine ⟨96214332877874336711579773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128285777170499115615439697 96214332877874336711579773)
    ·
      refine ⟨36080374829202876266842415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96214332877874336711579773 36080374829202876266842415)
      ·
        refine ⟨54120562243804314400263623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36080374829202876266842415 54120562243804314400263623)
        ·
          refine ⟨81180843365706471600395435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54120562243804314400263623 81180843365706471600395435)
          ·
            refine ⟨121771265048559707400593153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81180843365706471600395435 121771265048559707400593153)
            ·
              refine ⟨91328448786419780550444865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121771265048559707400593153 91328448786419780550444865)
              ·
                refine ⟨68496336589814835412833649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91328448786419780550444865 68496336589814835412833649)
                ·
                  refine ⟨51372252442361126559625237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68496336589814835412833649 51372252442361126559625237)
                  ·
                    refine ⟨2408074333235677807482433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 51372252442361126559625237 2408074333235677807482433)
                    ·
                      refine ⟨1806055749926758355611825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2408074333235677807482433 1806055749926758355611825)
                      ·
                        rfl

theorem cell23_3517281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 2, 6, 2].length) (baseStart_3517281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3517281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3517281 prefixEnd_3517281 := by exact prefixLift 3517281
  have htrace : WordTrace (prefixWord ++ tailWord_3517281) baseStart_3517281 baseEnd_3517281 := by
    simpa [prefixWord, tailWord_3517281, baseEnd_3517281] using wordTrace_append hprefix tailTrace_3517281
  have hstable : (prefixWord ++ tailWord_3517281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3517281).length < 2 ^ (prefixWord ++ tailWord_3517281).sum := by decide
  have hdescent : baseEnd_3517281 < baseStart_3517281 := by decide
  rcases family_descends (prefixWord ++ tailWord_3517281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3517282 : List Nat := [3, 3, 2, 1, 4, 1, 2, 1, 6]
def baseStart_3517282 : Nat := 118140960795 + 3517282 * 2 ^ 59
def prefixEnd_3517282 : Nat := 4983230072969 + 3 ^ 40 * 3517282 * 2
def baseEnd_3517282 : Nat := 200672918156379205744369

theorem tailTrace_3517282 : CollatzResearch.WordTrace tailWord_3517282 prefixEnd_3517282 200672918156379205744369 := by
  unfold tailWord_3517282
  simp only [CollatzResearch.WordTrace]
  refine ⟨32071453410873873196556525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85523875762330328524150733 32071453410873873196556525)
  ·
    refine ⟨12026795029077702448708697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32071453410873873196556525 12026795029077702448708697)
    ·
      refine ⟨9020096271808276836531523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12026795029077702448708697 9020096271808276836531523)
      ·
        refine ⟨13530144407712415254797285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9020096271808276836531523 13530144407712415254797285)
        ·
          refine ⟨2536902076446077860274491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13530144407712415254797285 2536902076446077860274491)
          ·
            refine ⟨3805353114669116790411737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2536902076446077860274491 3805353114669116790411737)
            ·
              refine ⟨2854014836001837592808803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3805353114669116790411737 2854014836001837592808803)
              ·
                refine ⟨4281022254002756389213205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2854014836001837592808803 4281022254002756389213205)
                ·
                  refine ⟨200672918156379205744369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4281022254002756389213205 200672918156379205744369)
                  ·
                    rfl

theorem cell23_3517282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 2, 1, 6].length) (baseStart_3517282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3517282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3517282 prefixEnd_3517282 := by exact prefixLift 3517282
  have htrace : WordTrace (prefixWord ++ tailWord_3517282) baseStart_3517282 baseEnd_3517282 := by
    simpa [prefixWord, tailWord_3517282, baseEnd_3517282] using wordTrace_append hprefix tailTrace_3517282
  have hstable : (prefixWord ++ tailWord_3517282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3517282).length < 2 ^ (prefixWord ++ tailWord_3517282).sum := by decide
  have hdescent : baseEnd_3517282 < baseStart_3517282 := by decide
  rcases family_descends (prefixWord ++ tailWord_3517282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3517298 : List Nat := [3, 2, 1, 2, 1, 1, 5, 2, 1, 1, 4]
def baseStart_3517298 : Nat := 118140960795 + 3517298 * 2 ^ 59
def prefixEnd_3517298 : Nat := 4983230072969 + 3 ^ 40 * 3517298 * 2
def baseEnd_3517298 : Nat := 1806064479097884789099247

theorem tailTrace_3517298 : CollatzResearch.WordTrace tailWord_3517298 prefixEnd_3517298 1806064479097884789099247 := by
  unfold tailWord_3517298
  simp only [CollatzResearch.WordTrace]
  refine ⟨32071599302859381879702137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85524264807625018345872365 32071599302859381879702137)
  ·
    refine ⟨24053699477144536409776603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32071599302859381879702137 24053699477144536409776603)
    ·
      refine ⟨36080549215716804614664905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24053699477144536409776603 36080549215716804614664905)
      ·
        refine ⟨27060411911787603460998679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36080549215716804614664905 27060411911787603460998679)
        ·
          refine ⟨40590617867681405191498019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27060411911787603460998679 40590617867681405191498019)
          ·
            refine ⟨60885926801522107787247029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40590617867681405191498019 60885926801522107787247029)
            ·
              refine ⟨5708055637642697605054409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60885926801522107787247029 5708055637642697605054409)
              ·
                refine ⟨4281041728232023203790807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5708055637642697605054409 4281041728232023203790807)
                ·
                  refine ⟨6421562592348034805686211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4281041728232023203790807 6421562592348034805686211)
                  ·
                    refine ⟨9632343888522052208529317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6421562592348034805686211 9632343888522052208529317)
                    ·
                      refine ⟨1806064479097884789099247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9632343888522052208529317 1806064479097884789099247)
                      ·
                        rfl

theorem cell23_3517298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 5, 2, 1, 1, 4].length) (baseStart_3517298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3517298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3517298 prefixEnd_3517298 := by exact prefixLift 3517298
  have htrace : WordTrace (prefixWord ++ tailWord_3517298) baseStart_3517298 baseEnd_3517298 := by
    simpa [prefixWord, tailWord_3517298, baseEnd_3517298] using wordTrace_append hprefix tailTrace_3517298
  have hstable : (prefixWord ++ tailWord_3517298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3517298).length < 2 ^ (prefixWord ++ tailWord_3517298).sum := by decide
  have hdescent : baseEnd_3517298 < baseStart_3517298 := by decide
  rcases family_descends (prefixWord ++ tailWord_3517298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3517302 : List Nat := [5, 1, 1, 3, 1, 2, 2, 1, 2, 3, 2]
def baseStart_3517302 : Nat := 118140960795 + 3517302 * 2 ^ 59
def prefixEnd_3517302 : Nat := 4983230072969 + 3 ^ 40 * 3517302 * 2
def baseEnd_3517302 : Nat := 1806066533020502773449229

theorem tailTrace_3517302 : CollatzResearch.WordTrace tailWord_3517302 prefixEnd_3517302 1806066533020502773449229 := by
  unfold tailWord_3517302
  simp only [CollatzResearch.WordTrace]
  refine ⟨8017908943963939762622135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 85524362068948690801302773 8017908943963939762622135)
  ·
    refine ⟨12026863415945909643933203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8017908943963939762622135 12026863415945909643933203)
    ·
      refine ⟨18040295123918864465899805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12026863415945909643933203 18040295123918864465899805)
      ·
        refine ⟨6765110671469574174712427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18040295123918864465899805 6765110671469574174712427)
        ·
          refine ⟨10147666007204361262068641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6765110671469574174712427 10147666007204361262068641)
          ·
            refine ⟨7610749505403270946551481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10147666007204361262068641 7610749505403270946551481)
            ·
              refine ⟨5708062129052453209913611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7610749505403270946551481 5708062129052453209913611)
              ·
                refine ⟨8562093193578679814870417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5708062129052453209913611 8562093193578679814870417)
                ·
                  refine ⟨6421569895184009861152813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8562093193578679814870417 6421569895184009861152813)
                  ·
                    refine ⟨2408088710694003697932305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6421569895184009861152813 2408088710694003697932305)
                    ·
                      refine ⟨1806066533020502773449229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2408088710694003697932305 1806066533020502773449229)
                      ·
                        rfl

theorem cell23_3517302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 2, 1, 2, 3, 2].length) (baseStart_3517302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3517302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3517302 prefixEnd_3517302 := by exact prefixLift 3517302
  have htrace : WordTrace (prefixWord ++ tailWord_3517302) baseStart_3517302 baseEnd_3517302 := by
    simpa [prefixWord, tailWord_3517302, baseEnd_3517302] using wordTrace_append hprefix tailTrace_3517302
  have hstable : (prefixWord ++ tailWord_3517302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3517302).length < 2 ^ (prefixWord ++ tailWord_3517302).sum := by decide
  have hdescent : baseEnd_3517302 < baseStart_3517302 := by decide
  rcases family_descends (prefixWord ++ tailWord_3517302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3517338 : List Nat := [3, 1, 1, 4, 3, 2, 1, 8]
def baseStart_3517338 : Nat := 118140960795 + 3517338 * 2 ^ 59
def prefixEnd_3517338 : Nat := 4983230072969 + 3 ^ 40 * 3517338 * 2
def baseEnd_3517338 : Nat := 66892037715706097503669

theorem tailTrace_3517338 : CollatzResearch.WordTrace tailWord_3517338 prefixEnd_3517338 66892037715706097503669 := by
  unfold tailWord_3517338
  simp only [CollatzResearch.WordTrace]
  refine ⟨32071964032823153587566167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85525237420861742900176445 32071964032823153587566167)
  ·
    refine ⟨48107946049234730381349251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32071964032823153587566167 48107946049234730381349251)
    ·
      refine ⟨72161919073852095572023877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48107946049234730381349251 72161919073852095572023877)
      ·
        refine ⟨13530359826347267919754477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72161919073852095572023877 13530359826347267919754477)
        ·
          refine ⟨5073884934880225469907929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13530359826347267919754477 5073884934880225469907929)
          ·
            refine ⟨3805413701160169102430947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5073884934880225469907929 3805413701160169102430947)
            ·
              refine ⟨5708120551740253653646421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3805413701160169102430947 5708120551740253653646421)
              ·
                refine ⟨66892037715706097503669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5708120551740253653646421 66892037715706097503669)
                ·
                  rfl

theorem cell23_3517338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 1, 8].length) (baseStart_3517338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3517338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3517338 prefixEnd_3517338 := by exact prefixLift 3517338
  have htrace : WordTrace (prefixWord ++ tailWord_3517338) baseStart_3517338 baseEnd_3517338 := by
    simpa [prefixWord, tailWord_3517338, baseEnd_3517338] using wordTrace_append hprefix tailTrace_3517338
  have hstable : (prefixWord ++ tailWord_3517338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3517338).length < 2 ^ (prefixWord ++ tailWord_3517338).sum := by decide
  have hdescent : baseEnd_3517338 < baseStart_3517338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3517338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3517348 : List Nat := [2, 3, 1, 2, 1, 2, 4, 1, 1, 3, 3]
def baseStart_3517348 : Nat := 118140960795 + 3517348 * 2 ^ 59
def prefixEnd_3517348 : Nat := 4983230072969 + 3 ^ 40 * 3517348 * 2
def baseEnd_3517348 : Nat := 1806090153130609593474017

theorem tailTrace_3517348 : CollatzResearch.WordTrace tailWord_3517348 prefixEnd_3517348 1806090153130609593474017 := by
  unfold tailWord_3517348
  simp only [CollatzResearch.WordTrace]
  refine ⟨64144110430628193029064349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85525480574170924038752465 64144110430628193029064349)
  ·
    refine ⟨24054041411485572385899131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64144110430628193029064349 24054041411485572385899131)
    ·
      refine ⟨36081062117228358578848697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24054041411485572385899131 36081062117228358578848697)
      ·
        refine ⟨27060796587921268934136523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36081062117228358578848697 27060796587921268934136523)
        ·
          refine ⟨40591194881881903401204785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27060796587921268934136523 40591194881881903401204785)
          ·
            refine ⟨30443396161411427550903589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40591194881881903401204785 30443396161411427550903589)
            ·
              refine ⟨5708136780264642665794423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30443396161411427550903589 5708136780264642665794423)
              ·
                refine ⟨8562205170396963998691635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5708136780264642665794423 8562205170396963998691635)
                ·
                  refine ⟨12843307755595445998037453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8562205170396963998691635 12843307755595445998037453)
                  ·
                    refine ⟨4816240408348292249264045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12843307755595445998037453 4816240408348292249264045)
                    ·
                      refine ⟨1806090153130609593474017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4816240408348292249264045 1806090153130609593474017)
                      ·
                        rfl

theorem cell23_3517348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 4, 1, 1, 3, 3].length) (baseStart_3517348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3517348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3517348 prefixEnd_3517348 := by exact prefixLift 3517348
  have htrace : WordTrace (prefixWord ++ tailWord_3517348) baseStart_3517348 baseEnd_3517348 := by
    simpa [prefixWord, tailWord_3517348, baseEnd_3517348] using wordTrace_append hprefix tailTrace_3517348
  have hstable : (prefixWord ++ tailWord_3517348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3517348).length < 2 ^ (prefixWord ++ tailWord_3517348).sum := by decide
  have hdescent : baseEnd_3517348 < baseStart_3517348 := by decide
  rcases family_descends (prefixWord ++ tailWord_3517348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3517411 : List Nat := [1, 1, 1, 6, 1, 1, 1, 4, 7]
def baseStart_3517411 : Nat := 118140960795 + 3517411 * 2 ^ 59
def prefixEnd_3517411 : Nat := 4983230072969 + 3 ^ 40 * 3517411 * 2
def baseEnd_3517411 : Nat := 200680278045760316331803

theorem tailTrace_3517411 : CollatzResearch.WordTrace tailWord_3517411 prefixEnd_3517411 200680278045760316331803 := by
  unfold tailWord_3517411
  simp only [CollatzResearch.WordTrace]
  refine ⟨128290518660028147817672087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85527012440018765211781391 128290518660028147817672087)
  ·
    refine ⟨192435777990042221726508131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128290518660028147817672087 192435777990042221726508131)
    ·
      refine ⟨288653666985063332589762197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192435777990042221726508131 288653666985063332589762197)
      ·
        refine ⟨13530640639924843715145103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 288653666985063332589762197 13530640639924843715145103)
        ·
          refine ⟨20295960959887265572717655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13530640639924843715145103 20295960959887265572717655)
          ·
            refine ⟨30443941439830898359076483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20295960959887265572717655 30443941439830898359076483)
            ·
              refine ⟨45665912159746347538614725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30443941439830898359076483 45665912159746347538614725)
              ·
                refine ⟨8562358529952440163490261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45665912159746347538614725 8562358529952440163490261)
                ·
                  refine ⟨200680278045760316331803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8562358529952440163490261 200680278045760316331803)
                  ·
                    rfl

theorem cell23_3517411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 4, 7].length) (baseStart_3517411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3517411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3517411 prefixEnd_3517411 := by exact prefixLift 3517411
  have htrace : WordTrace (prefixWord ++ tailWord_3517411) baseStart_3517411 baseEnd_3517411 := by
    simpa [prefixWord, tailWord_3517411, baseEnd_3517411] using wordTrace_append hprefix tailTrace_3517411
  have hstable : (prefixWord ++ tailWord_3517411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3517411).length < 2 ^ (prefixWord ++ tailWord_3517411).sum := by decide
  have hdescent : baseEnd_3517411 < baseStart_3517411 := by decide
  rcases family_descends (prefixWord ++ tailWord_3517411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3517445 : List Nat := [1, 3, 1, 1, 2, 3, 5, 2, 5]
def baseStart_3517445 : Nat := 118140960795 + 3517445 * 2 ^ 59
def prefixEnd_3517445 : Nat := 4983230072969 + 3 ^ 40 * 3517445 * 2
def baseEnd_3517445 : Nat := 200682217861566190440119

theorem tailTrace_3517445 : CollatzResearch.WordTrace tailWord_3517445 prefixEnd_3517445 200682217861566190440119 := by
  unfold tailWord_3517445
  simp only [CollatzResearch.WordTrace]
  refine ⟨128291758741904971624409789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85527839161269981082939859 128291758741904971624409789)
  ·
    refine ⟨48109409528214364359153671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128291758741904971624409789 48109409528214364359153671)
    ·
      refine ⟨72164114292321546538730507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48109409528214364359153671 72164114292321546538730507)
      ·
        refine ⟨108246171438482319808095761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72164114292321546538730507 108246171438482319808095761)
        ·
          refine ⟨81184628578861739856071821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108246171438482319808095761 81184628578861739856071821)
          ·
            refine ⟨30444235717073152446026933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81184628578861739856071821 30444235717073152446026933)
            ·
              refine ⟨2854147098475608041815025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30444235717073152446026933 2854147098475608041815025)
              ·
                refine ⟨2140610323856706031361269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2854147098475608041815025 2140610323856706031361269)
                ·
                  refine ⟨200682217861566190440119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2140610323856706031361269 200682217861566190440119)
                  ·
                    rfl

theorem cell23_3517445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 5, 2, 5].length) (baseStart_3517445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3517445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3517445 prefixEnd_3517445 := by exact prefixLift 3517445
  have htrace : WordTrace (prefixWord ++ tailWord_3517445) baseStart_3517445 baseEnd_3517445 := by
    simpa [prefixWord, tailWord_3517445, baseEnd_3517445] using wordTrace_append hprefix tailTrace_3517445
  have hstable : (prefixWord ++ tailWord_3517445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3517445).length < 2 ^ (prefixWord ++ tailWord_3517445).sum := by decide
  have hdescent : baseEnd_3517445 < baseStart_3517445 := by decide
  rcases family_descends (prefixWord ++ tailWord_3517445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3517451 : List Nat := [1, 1, 1, 1, 6, 2, 1, 1, 1, 1, 7]
def baseStart_3517451 : Nat := 118140960795 + 3517451 * 2 ^ 59
def prefixEnd_3517451 : Nat := 4983230072969 + 3 ^ 40 * 3517451 * 2
def baseEnd_3517451 : Nat := 1806143041638022690486043

theorem tailTrace_3517451 : CollatzResearch.WordTrace tailWord_3517451 prefixEnd_3517451 1806143041638022690486043 := by
  unfold tailWord_3517451
  simp only [CollatzResearch.WordTrace]
  refine ⟨128291977579883234649128207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85527985053255489766085471 128291977579883234649128207)
  ·
    refine ⟨192437966369824851973692311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128291977579883234649128207 192437966369824851973692311)
    ·
      refine ⟨288656949554737277960538467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192437966369824851973692311 288656949554737277960538467)
      ·
        refine ⟨432985424332105916940807701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288656949554737277960538467 432985424332105916940807701)
        ·
          refine ⟨20296191765567464856600361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 432985424332105916940807701 20296191765567464856600361)
          ·
            refine ⟨15222143824175598642450271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20296191765567464856600361 15222143824175598642450271)
            ·
              refine ⟨22833215736263397963675407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15222143824175598642450271 22833215736263397963675407)
              ·
                refine ⟨34249823604395096945513111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22833215736263397963675407 34249823604395096945513111)
                ·
                  refine ⟨51374735406592645418269667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34249823604395096945513111 51374735406592645418269667)
                  ·
                    refine ⟨77062103109888968127404501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51374735406592645418269667 77062103109888968127404501)
                    ·
                      refine ⟨1806143041638022690486043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 77062103109888968127404501 1806143041638022690486043)
                      ·
                        rfl

theorem cell23_3517451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 1, 1, 1, 7].length) (baseStart_3517451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3517451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3517451 prefixEnd_3517451 := by exact prefixLift 3517451
  have htrace : WordTrace (prefixWord ++ tailWord_3517451) baseStart_3517451 baseEnd_3517451 := by
    simpa [prefixWord, tailWord_3517451, baseEnd_3517451] using wordTrace_append hprefix tailTrace_3517451
  have hstable : (prefixWord ++ tailWord_3517451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3517451).length < 2 ^ (prefixWord ++ tailWord_3517451).sum := by decide
  have hdescent : baseEnd_3517451 < baseStart_3517451 := by decide
  rcases family_descends (prefixWord ++ tailWord_3517451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3517491 : List Nat := [1, 1, 1, 2, 4, 1, 1, 3, 2, 1, 6]
def baseStart_3517491 : Nat := 118140960795 + 3517491 * 2 ^ 59
def prefixEnd_3517491 : Nat := 4983230072969 + 3 ^ 40 * 3517491 * 2
def baseEnd_3517491 : Nat := 1806163580864202533985859

theorem tailTrace_3517491 : CollatzResearch.WordTrace tailWord_3517491 prefixEnd_3517491 1806163580864202533985859 := by
  unfold tailWord_3517491
  simp only [CollatzResearch.WordTrace]
  refine ⟨128293436499738321480584327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85528957666492214320389551 128293436499738321480584327)
  ·
    refine ⟨192440154749607482220876491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128293436499738321480584327 192440154749607482220876491)
    ·
      refine ⟨288660232124411223331314737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192440154749607482220876491 288660232124411223331314737)
      ·
        refine ⟨216495174093308417498486053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 288660232124411223331314737 216495174093308417498486053)
        ·
          refine ⟨40592845142495328280966135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 216495174093308417498486053 40592845142495328280966135)
          ·
            refine ⟨60889267713742992421449203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40592845142495328280966135 60889267713742992421449203)
            ·
              refine ⟨91333901570614488632173805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60889267713742992421449203 91333901570614488632173805)
              ·
                refine ⟨34250213088980433237065177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91333901570614488632173805 34250213088980433237065177)
                ·
                  refine ⟨25687659816735324927798883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34250213088980433237065177 25687659816735324927798883)
                  ·
                    refine ⟨38531489725102987391698325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25687659816735324927798883 38531489725102987391698325)
                    ·
                      refine ⟨1806163580864202533985859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38531489725102987391698325 1806163580864202533985859)
                      ·
                        rfl

theorem cell23_3517491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 3, 2, 1, 6].length) (baseStart_3517491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3517491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3517491 prefixEnd_3517491 := by exact prefixLift 3517491
  have htrace : WordTrace (prefixWord ++ tailWord_3517491) baseStart_3517491 baseEnd_3517491 := by
    simpa [prefixWord, tailWord_3517491, baseEnd_3517491] using wordTrace_append hprefix tailTrace_3517491
  have hstable : (prefixWord ++ tailWord_3517491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3517491).length < 2 ^ (prefixWord ++ tailWord_3517491).sum := by decide
  have hdescent : baseEnd_3517491 < baseStart_3517491 := by decide
  rcases family_descends (prefixWord ++ tailWord_3517491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3517518 : List Nat := [4, 1, 1, 1, 1, 3, 1, 5, 6]
def baseStart_3517518 : Nat := 118140960795 + 3517518 * 2 ^ 59
def prefixEnd_3517518 : Nat := 4983230072969 + 3 ^ 40 * 3517518 * 2
def baseEnd_3517518 : Nat := 200686382760208214260915

theorem tailTrace_3517518 : CollatzResearch.WordTrace tailWord_3517518 prefixEnd_3517518 200686382760208214260915 := by
  unfold tailWord_3517518
  simp only [CollatzResearch.WordTrace]
  refine ⟨16036802658830063136477151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85529614180427003394544805 16036802658830063136477151)
  ·
    refine ⟨24055203988245094704715727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16036802658830063136477151 24055203988245094704715727)
    ·
      refine ⟨36082805982367642057073591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24055203988245094704715727 36082805982367642057073591)
      ·
        refine ⟨54124208973551463085610387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36082805982367642057073591 54124208973551463085610387)
        ·
          refine ⟨81186313460327194628415581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54124208973551463085610387 81186313460327194628415581)
          ·
            refine ⟨30444867547622697985655843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81186313460327194628415581 30444867547622697985655843)
            ·
              refine ⟨45667301321434046978483765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30444867547622697985655843 45667301321434046978483765)
              ·
                refine ⟨4281309498884441904232853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45667301321434046978483765 4281309498884441904232853)
                ·
                  refine ⟨200686382760208214260915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4281309498884441904232853 200686382760208214260915)
                  ·
                    rfl

theorem cell23_3517518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 5, 6].length) (baseStart_3517518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3517518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3517518 prefixEnd_3517518 := by exact prefixLift 3517518
  have htrace : WordTrace (prefixWord ++ tailWord_3517518) baseStart_3517518 baseEnd_3517518 := by
    simpa [prefixWord, tailWord_3517518, baseEnd_3517518] using wordTrace_append hprefix tailTrace_3517518
  have hstable : (prefixWord ++ tailWord_3517518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3517518).length < 2 ^ (prefixWord ++ tailWord_3517518).sum := by decide
  have hdescent : baseEnd_3517518 < baseStart_3517518 := by decide
  rcases family_descends (prefixWord ++ tailWord_3517518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3517526 : List Nat := [5, 2, 2, 1, 3, 1, 1, 1, 2, 5]
def baseStart_3517526 : Nat := 118140960795 + 3517526 * 2 ^ 59
def prefixEnd_3517526 : Nat := 4983230072969 + 3 ^ 40 * 3517526 * 2
def baseEnd_3517526 : Nat := 602060517562369965682733

theorem tailTrace_3517526 : CollatzResearch.WordTrace tailWord_3517526 prefixEnd_3517526 602060517562369965682733 := by
  unfold tailWord_3517526
  simp only [CollatzResearch.WordTrace]
  refine ⟨8018419565913220153631777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 85529808703074348305405621 8018419565913220153631777)
  ·
    refine ⟨6013814674434915115223833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8018419565913220153631777 6013814674434915115223833)
    ·
      refine ⟨4510361005826186336417875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6013814674434915115223833 4510361005826186336417875)
      ·
        refine ⟨6765541508739279504626813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4510361005826186336417875 6765541508739279504626813)
        ·
          refine ⟨2537078065777229814235055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6765541508739279504626813 2537078065777229814235055)
          ·
            refine ⟨3805617098665844721352583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2537078065777229814235055 3805617098665844721352583)
            ·
              refine ⟨5708425647998767082028875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3805617098665844721352583 5708425647998767082028875)
              ·
                refine ⟨8562638471998150623043313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5708425647998767082028875 8562638471998150623043313)
                ·
                  refine ⟨6421978853998612967282485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8562638471998150623043313 6421978853998612967282485)
                  ·
                    refine ⟨602060517562369965682733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6421978853998612967282485 602060517562369965682733)
                    ·
                      rfl

theorem cell23_3517526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_3517526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3517526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3517526 prefixEnd_3517526 := by exact prefixLift 3517526
  have htrace : WordTrace (prefixWord ++ tailWord_3517526) baseStart_3517526 baseEnd_3517526 := by
    simpa [prefixWord, tailWord_3517526, baseEnd_3517526] using wordTrace_append hprefix tailTrace_3517526
  have hstable : (prefixWord ++ tailWord_3517526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3517526).length < 2 ^ (prefixWord ++ tailWord_3517526).sum := by decide
  have hdescent : baseEnd_3517526 < baseStart_3517526 := by decide
  rcases family_descends (prefixWord ++ tailWord_3517526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3517568 : List Nat := [2, 1, 1, 2, 1, 3, 2, 1, 5, 1, 4]
def baseStart_3517568 : Nat := 118140960795 + 3517568 * 2 ^ 59
def prefixEnd_3517568 : Nat := 4983230072969 + 3 ^ 40 * 3517568 * 2
def baseEnd_3517568 : Nat := 1806203118874598732723005

theorem tailTrace_3517568 : CollatzResearch.WordTrace tailWord_3517568 prefixEnd_3517568 1806203118874598732723005 := by
  unfold tailWord_3517568
  simp only [CollatzResearch.WordTrace]
  refine ⟨64148122460229681815568679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85530829946972909087424905 64148122460229681815568679)
  ·
    refine ⟨96222183690344522723353019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64148122460229681815568679 96222183690344522723353019)
    ·
      refine ⟨144333275535516784085029529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96222183690344522723353019 144333275535516784085029529)
      ·
        refine ⟨108249956651637588063772147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144333275535516784085029529 108249956651637588063772147)
        ·
          refine ⟨162374934977456382095658221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108249956651637588063772147 162374934977456382095658221)
          ·
            refine ⟨60890600616546143285871833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 162374934977456382095658221 60890600616546143285871833)
            ·
              refine ⟨45667950462409607464403875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60890600616546143285871833 45667950462409607464403875)
              ·
                refine ⟨68501925693614411196605813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45667950462409607464403875 68501925693614411196605813)
                ·
                  refine ⟨6422055533776351049681795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68501925693614411196605813 6422055533776351049681795)
                  ·
                    refine ⟨9633083300664526574522693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6422055533776351049681795 9633083300664526574522693)
                    ·
                      refine ⟨1806203118874598732723005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9633083300664526574522693 1806203118874598732723005)
                      ·
                        rfl

theorem cell23_3517568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 5, 1, 4].length) (baseStart_3517568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3517568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3517568 prefixEnd_3517568 := by exact prefixLift 3517568
  have htrace : WordTrace (prefixWord ++ tailWord_3517568) baseStart_3517568 baseEnd_3517568 := by
    simpa [prefixWord, tailWord_3517568, baseEnd_3517568] using wordTrace_append hprefix tailTrace_3517568
  have hstable : (prefixWord ++ tailWord_3517568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3517568).length < 2 ^ (prefixWord ++ tailWord_3517568).sum := by decide
  have hdescent : baseEnd_3517568 < baseStart_3517568 := by decide
  rcases family_descends (prefixWord ++ tailWord_3517568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3517582 : List Nat := [4, 1, 1, 3, 2, 2, 2, 2, 1, 5]
def baseStart_3517582 : Nat := 118140960795 + 3517582 * 2 ^ 59
def prefixEnd_3517582 : Nat := 4983230072969 + 3 ^ 40 * 3517582 * 2
def baseEnd_3517582 : Nat := 602070102534587225982647

theorem tailTrace_3517582 : CollatzResearch.WordTrace tailWord_3517582 prefixEnd_3517582 602070102534587225982647 := by
  unfold tailWord_3517582
  simp only [CollatzResearch.WordTrace]
  refine ⟨16037094442801080502768375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85531170361605762681431333 16037094442801080502768375)
  ·
    refine ⟨24055641664201620754152563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16037094442801080502768375 24055641664201620754152563)
    ·
      refine ⟨36083462496302431131228845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24055641664201620754152563 36083462496302431131228845)
      ·
        refine ⟨13531298436113411674210817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36083462496302431131228845 13531298436113411674210817)
        ·
          refine ⟨10148473827085058755658113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13531298436113411674210817 10148473827085058755658113)
          ·
            refine ⟨7611355370313794066743585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10148473827085058755658113 7611355370313794066743585)
            ·
              refine ⟨5708516527735345550057689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7611355370313794066743585 5708516527735345550057689)
              ·
                refine ⟨4281387395801509162543267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5708516527735345550057689 4281387395801509162543267)
                ·
                  refine ⟨6422081093702263743814901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4281387395801509162543267 6422081093702263743814901)
                  ·
                    refine ⟨602070102534587225982647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6422081093702263743814901 602070102534587225982647)
                    ·
                      rfl

theorem cell23_3517582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 2, 2, 1, 5].length) (baseStart_3517582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3517582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3517582 prefixEnd_3517582 := by exact prefixLift 3517582
  have htrace : WordTrace (prefixWord ++ tailWord_3517582) baseStart_3517582 baseEnd_3517582 := by
    simpa [prefixWord, tailWord_3517582, baseEnd_3517582] using wordTrace_append hprefix tailTrace_3517582
  have hstable : (prefixWord ++ tailWord_3517582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3517582).length < 2 ^ (prefixWord ++ tailWord_3517582).sum := by decide
  have hdescent : baseEnd_3517582 < baseStart_3517582 := by decide
  rcases family_descends (prefixWord ++ tailWord_3517582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3517596 : List Nat := [2, 2, 3, 2, 1, 4, 1, 3, 1, 1, 3]
def baseStart_3517596 : Nat := 118140960795 + 3517596 * 2 ^ 59
def prefixEnd_3517596 : Nat := 4983230072969 + 3 ^ 40 * 3517596 * 2
def baseEnd_3517596 : Nat := 1806217496332924623172877

theorem tailTrace_3517596 : CollatzResearch.WordTrace tailWord_3517596 prefixEnd_3517596 1806217496332924623172877 := by
  unfold tailWord_3517596
  simp only [CollatzResearch.WordTrace]
  refine ⟨64148633082178962206578321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85531510776238616275437761 64148633082178962206578321)
  ·
    refine ⟨48111474811634221654933741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64148633082178962206578321 48111474811634221654933741)
    ·
      refine ⟨18041803054362833120600153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48111474811634221654933741 18041803054362833120600153)
      ·
        refine ⟨13531352290772124840450115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18041803054362833120600153 13531352290772124840450115)
        ·
          refine ⟨20297028436158187260675173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13531352290772124840450115 20297028436158187260675173)
          ·
            refine ⟨3805692831779660111376595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20297028436158187260675173 3805692831779660111376595)
            ·
              refine ⟨5708539247669490167064893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3805692831779660111376595 5708539247669490167064893)
              ·
                refine ⟨2140702217876058812649335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5708539247669490167064893 2140702217876058812649335)
                ·
                  refine ⟨3211053326814088218974003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2140702217876058812649335 3211053326814088218974003)
                  ·
                    refine ⟨4816579990221132328461005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3211053326814088218974003 4816579990221132328461005)
                    ·
                      refine ⟨1806217496332924623172877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4816579990221132328461005 1806217496332924623172877)
                      ·
                        rfl

theorem cell23_3517596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 1, 3, 1, 1, 3].length) (baseStart_3517596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3517596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3517596 prefixEnd_3517596 := by exact prefixLift 3517596
  have htrace : WordTrace (prefixWord ++ tailWord_3517596) baseStart_3517596 baseEnd_3517596 := by
    simpa [prefixWord, tailWord_3517596, baseEnd_3517596] using wordTrace_append hprefix tailTrace_3517596
  have hstable : (prefixWord ++ tailWord_3517596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3517596).length < 2 ^ (prefixWord ++ tailWord_3517596).sum := by decide
  have hdescent : baseEnd_3517596 < baseStart_3517596 := by decide
  rcases family_descends (prefixWord ++ tailWord_3517596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3517605 : List Nat := [1, 3, 1, 2, 1, 5, 2, 1, 1, 1, 5]
def baseStart_3517605 : Nat := 118140960795 + 3517605 * 2 ^ 59
def prefixEnd_3517605 : Nat := 4983230072969 + 3 ^ 40 * 3517605 * 2
def baseEnd_3517605 : Nat := 1806222117658815087960335

theorem tailTrace_3517605 : CollatzResearch.WordTrace tailWord_3517605 prefixEnd_3517605 1806222117658815087960335 := by
  unfold tailWord_3517605
  simp only [CollatzResearch.WordTrace]
  refine ⟨128297594421325318950234269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85531729614216879300156179 128297594421325318950234269)
  ·
    refine ⟨48111597907996994606337851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128297594421325318950234269 48111597907996994606337851)
    ·
      refine ⟨72167396861995491909506777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48111597907996994606337851 72167396861995491909506777)
      ·
        refine ⟨54125547646496618932130083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72167396861995491909506777 54125547646496618932130083)
        ·
          refine ⟨81188321469744928398195125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54125547646496618932130083 81188321469744928398195125)
          ·
            refine ⟨7611405137788587037330793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 81188321469744928398195125 7611405137788587037330793)
            ·
              refine ⟨5708553853341440277998095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7611405137788587037330793 5708553853341440277998095)
              ·
                refine ⟨8562830780012160416997143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5708553853341440277998095 8562830780012160416997143)
                ·
                  refine ⟨12844246170018240625495715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8562830780012160416997143 12844246170018240625495715)
                  ·
                    refine ⟨19266369255027360938243573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12844246170018240625495715 19266369255027360938243573)
                    ·
                      refine ⟨1806222117658815087960335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19266369255027360938243573 1806222117658815087960335)
                      ·
                        rfl

theorem cell23_3517605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 2, 1, 1, 1, 5].length) (baseStart_3517605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3517605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3517605 prefixEnd_3517605 := by exact prefixLift 3517605
  have htrace : WordTrace (prefixWord ++ tailWord_3517605) baseStart_3517605 baseEnd_3517605 := by
    simpa [prefixWord, tailWord_3517605, baseEnd_3517605] using wordTrace_append hprefix tailTrace_3517605
  have hstable : (prefixWord ++ tailWord_3517605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3517605).length < 2 ^ (prefixWord ++ tailWord_3517605).sum := by decide
  have hdescent : baseEnd_3517605 < baseStart_3517605 := by decide
  rcases family_descends (prefixWord ++ tailWord_3517605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3517613 : List Nat := [1, 5, 2, 1, 3, 1, 3, 2, 1, 1, 3]
def baseStart_3517613 : Nat := 118140960795 + 3517613 * 2 ^ 59
def prefixEnd_3517613 : Nat := 4983230072969 + 3 ^ 40 * 3517613 * 2
def baseEnd_3517613 : Nat := 1806226225504051056660299

theorem tailTrace_3517613 : CollatzResearch.WordTrace tailWord_3517613 prefixEnd_3517613 1806226225504051056660299 := by
  unfold tailWord_3517613
  simp only [CollatzResearch.WordTrace]
  refine ⟨128297886205296336316525493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85531924136864224211016995 128297886205296336316525493)
  ·
    refine ⟨12027926831746531529674265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 128297886205296336316525493 12027926831746531529674265)
    ·
      refine ⟨9020945123809898647255699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12027926831746531529674265 9020945123809898647255699)
      ·
        refine ⟨13531417685714847970883549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9020945123809898647255699 13531417685714847970883549)
        ·
          refine ⟨5074281632143067989081331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13531417685714847970883549 5074281632143067989081331)
          ·
            refine ⟨7611422448214601983621997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5074281632143067989081331 7611422448214601983621997)
            ·
              refine ⟨2854283418080475743858249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7611422448214601983621997 2854283418080475743858249)
              ·
                refine ⟨2140712563560356807893687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2854283418080475743858249 2140712563560356807893687)
                ·
                  refine ⟨3211068845340535211840531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2140712563560356807893687 3211068845340535211840531)
                  ·
                    refine ⟨4816603268010802817760797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3211068845340535211840531 4816603268010802817760797)
                    ·
                      refine ⟨1806226225504051056660299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4816603268010802817760797 1806226225504051056660299)
                      ·
                        rfl

theorem cell23_3517613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 3, 2, 1, 1, 3].length) (baseStart_3517613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3517613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3517613 prefixEnd_3517613 := by exact prefixLift 3517613
  have htrace : WordTrace (prefixWord ++ tailWord_3517613) baseStart_3517613 baseEnd_3517613 := by
    simpa [prefixWord, tailWord_3517613, baseEnd_3517613] using wordTrace_append hprefix tailTrace_3517613
  have hstable : (prefixWord ++ tailWord_3517613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3517613).length < 2 ^ (prefixWord ++ tailWord_3517613).sum := by decide
  have hdescent : baseEnd_3517613 < baseStart_3517613 := by decide
  rcases family_descends (prefixWord ++ tailWord_3517613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3517619 : List Nat := [1, 1, 1, 2, 3, 2, 2, 6, 1, 2, 2]
def baseStart_3517619 : Nat := 118140960795 + 3517619 * 2 ^ 59
def prefixEnd_3517619 : Nat := 4983230072969 + 3 ^ 40 * 3517619 * 2
def baseEnd_3517619 : Nat := 1806229306387978033185271

theorem tailTrace_3517619 : CollatzResearch.WordTrace tailWord_3517619 prefixEnd_3517619 1806229306387978033185271 := by
  unfold tailWord_3517619
  simp only [CollatzResearch.WordTrace]
  refine ⟨128298105043274599341243911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85532070028849732894162607 128298105043274599341243911)
  ·
    refine ⟨192447157564911899011865867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128298105043274599341243911 192447157564911899011865867)
    ·
      refine ⟨288670736347367848517798801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192447157564911899011865867 288670736347367848517798801)
      ·
        refine ⟨216503052260525886388349101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 288670736347367848517798801 216503052260525886388349101)
        ·
          refine ⟨81188644597697207395630913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 216503052260525886388349101 81188644597697207395630913)
          ·
            refine ⟨60891483448272905546723185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81188644597697207395630913 60891483448272905546723185)
            ·
              refine ⟨45668612586204679160042389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60891483448272905546723185 45668612586204679160042389)
              ·
                refine ⟨2140716214978344335626987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 45668612586204679160042389 2140716214978344335626987)
                ·
                  refine ⟨3211074322467516503440481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2140716214978344335626987 3211074322467516503440481)
                  ·
                    refine ⟨2408305741850637377580361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3211074322467516503440481 2408305741850637377580361)
                    ·
                      refine ⟨1806229306387978033185271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2408305741850637377580361 1806229306387978033185271)
                      ·
                        rfl

theorem cell23_3517619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 6, 1, 2, 2].length) (baseStart_3517619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3517619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3517619 prefixEnd_3517619 := by exact prefixLift 3517619
  have htrace : WordTrace (prefixWord ++ tailWord_3517619) baseStart_3517619 baseEnd_3517619 := by
    simpa [prefixWord, tailWord_3517619, baseEnd_3517619] using wordTrace_append hprefix tailTrace_3517619
  have hstable : (prefixWord ++ tailWord_3517619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3517619).length < 2 ^ (prefixWord ++ tailWord_3517619).sum := by decide
  have hdescent : baseEnd_3517619 < baseStart_3517619 := by decide
  rcases family_descends (prefixWord ++ tailWord_3517619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3517635 : List Nat := [1, 1, 1, 3, 1, 1, 1, 4, 6, 1, 3]
def baseStart_3517635 : Nat := 118140960795 + 3517635 * 2 ^ 59
def prefixEnd_3517635 : Nat := 4983230072969 + 3 ^ 40 * 3517635 * 2
def baseEnd_3517635 : Nat := 1806237522078449970585197

theorem tailTrace_3517635 : CollatzResearch.WordTrace tailWord_3517635 prefixEnd_3517635 1806237522078449970585197 := by
  unfold tailWord_3517635
  simp only [CollatzResearch.WordTrace]
  refine ⟨128298688611216634073826359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85532459074144422715884239 128298688611216634073826359)
  ·
    refine ⟨192448032916824951110739539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128298688611216634073826359 192448032916824951110739539)
    ·
      refine ⟨288672049375237426666109309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192448032916824951110739539 288672049375237426666109309)
      ·
        refine ⟨108252018515714034999790991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 288672049375237426666109309 108252018515714034999790991)
        ·
          refine ⟨162378027773571052499686487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108252018515714034999790991 162378027773571052499686487)
          ·
            refine ⟨243567041660356578749529731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162378027773571052499686487 243567041660356578749529731)
            ·
              refine ⟨365350562490534868124294597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 243567041660356578749529731 365350562490534868124294597)
              ·
                refine ⟨68503230466975287773305237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 365350562490534868124294597 68503230466975287773305237)
                ·
                  refine ⟨3211088928139466614373683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 68503230466975287773305237 3211088928139466614373683)
                  ·
                    refine ⟨4816633392209199921560525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3211088928139466614373683 4816633392209199921560525)
                    ·
                      refine ⟨1806237522078449970585197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4816633392209199921560525 1806237522078449970585197)
                      ·
                        rfl

theorem cell23_3517635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 6, 1, 3].length) (baseStart_3517635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3517635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3517635 prefixEnd_3517635 := by exact prefixLift 3517635
  have htrace : WordTrace (prefixWord ++ tailWord_3517635) baseStart_3517635 baseEnd_3517635 := by
    simpa [prefixWord, tailWord_3517635, baseEnd_3517635] using wordTrace_append hprefix tailTrace_3517635
  have hstable : (prefixWord ++ tailWord_3517635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3517635).length < 2 ^ (prefixWord ++ tailWord_3517635).sum := by decide
  have hdescent : baseEnd_3517635 < baseStart_3517635 := by decide
  rcases family_descends (prefixWord ++ tailWord_3517635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3517636 : List Nat := [2, 3, 3, 1, 4, 1, 1, 2, 1, 1, 4]
def baseStart_3517636 : Nat := 118140960795 + 3517636 * 2 ^ 59
def prefixEnd_3517636 : Nat := 4983230072969 + 3 ^ 40 * 3517636 * 2
def baseEnd_3517636 : Nat := 1806238035559104466672693

theorem tailTrace_3517636 : CollatzResearch.WordTrace tailWord_3517636 prefixEnd_3517636 1806238035559104466672693 := by
  unfold tailWord_3517636
  simp only [CollatzResearch.WordTrace]
  refine ⟨64149362542106505622306381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85532483389475340829741841 64149362542106505622306381)
  ·
    refine ⟨24056010953289939608364893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64149362542106505622306381 24056010953289939608364893)
    ·
      refine ⟨9021004107483727353136835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24056010953289939608364893 9021004107483727353136835)
      ·
        refine ⟨13531506161225591029705253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9021004107483727353136835 13531506161225591029705253)
        ·
          refine ⟨2537157405229798318069735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13531506161225591029705253 2537157405229798318069735)
          ·
            refine ⟨3805736107844697477104603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2537157405229798318069735 3805736107844697477104603)
            ·
              refine ⟨5708604161767046215656905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3805736107844697477104603 5708604161767046215656905)
              ·
                refine ⟨4281453121325284661742679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5708604161767046215656905 4281453121325284661742679)
                ·
                  refine ⟨6422179681987926992614019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4281453121325284661742679 6422179681987926992614019)
                  ·
                    refine ⟨9633269522981890488921029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6422179681987926992614019 9633269522981890488921029)
                    ·
                      refine ⟨1806238035559104466672693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9633269522981890488921029 1806238035559104466672693)
                      ·
                        rfl

theorem cell23_3517636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 1, 2, 1, 1, 4].length) (baseStart_3517636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3517636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3517636 prefixEnd_3517636 := by exact prefixLift 3517636
  have htrace : WordTrace (prefixWord ++ tailWord_3517636) baseStart_3517636 baseEnd_3517636 := by
    simpa [prefixWord, tailWord_3517636, baseEnd_3517636] using wordTrace_append hprefix tailTrace_3517636
  have hstable : (prefixWord ++ tailWord_3517636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3517636).length < 2 ^ (prefixWord ++ tailWord_3517636).sum := by decide
  have hdescent : baseEnd_3517636 < baseStart_3517636 := by decide
  rcases family_descends (prefixWord ++ tailWord_3517636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
