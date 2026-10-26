import V185TrunkScan23Chunk0825

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4886287 : List Nat := [1, 1, 2, 1, 1, 1, 4, 1, 5, 4, 2]
def baseStart_4886287 : Nat := 118140960795 + 4886287 * 2 ^ 59
def prefixEnd_4886287 : Nat := 4983230072969 + 3 ^ 40 * 4886287 * 2
def baseEnd_4886287 : Nat := 2509013846815829113340881

theorem tailTrace_4886287 : CollatzResearch.WordTrace tailWord_4886287 prefixEnd_4886287 2509013846815829113340881 := by
  unfold tailWord_4886287
  simp only [CollatzResearch.WordTrace]
  refine ⟨178217528048824185225865115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118811685365882790150576743 178217528048824185225865115)
  ·
    refine ⟨267326292073236277838797673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178217528048824185225865115 267326292073236277838797673)
    ·
      refine ⟨200494719054927208379098255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 267326292073236277838797673 200494719054927208379098255)
      ·
        refine ⟨300742078582390812568647383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200494719054927208379098255 300742078582390812568647383)
        ·
          refine ⟨451113117873586218852971075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 300742078582390812568647383 451113117873586218852971075)
          ·
            refine ⟨676669676810379328279456613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 451113117873586218852971075 676669676810379328279456613)
            ·
              refine ⟨126875564401946124052398115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 676669676810379328279456613 126875564401946124052398115)
              ·
                refine ⟨190313346602919186078597173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126875564401946124052398115 190313346602919186078597173)
                ·
                  refine ⟨17841876244023673694868485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 190313346602919186078597173 17841876244023673694868485)
                  ·
                    refine ⟨3345351795754438817787841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17841876244023673694868485 3345351795754438817787841)
                    ·
                      refine ⟨2509013846815829113340881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3345351795754438817787841 2509013846815829113340881)
                      ·
                        rfl

theorem cell23_4886287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 5, 4, 2].length) (baseStart_4886287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4886287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4886287 prefixEnd_4886287 := by exact prefixLift 4886287
  have htrace : WordTrace (prefixWord ++ tailWord_4886287) baseStart_4886287 baseEnd_4886287 := by
    simpa [prefixWord, tailWord_4886287, baseEnd_4886287] using wordTrace_append hprefix tailTrace_4886287
  have hstable : (prefixWord ++ tailWord_4886287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4886287).length < 2 ^ (prefixWord ++ tailWord_4886287).sum := by decide
  have hdescent : baseEnd_4886287 < baseStart_4886287 := by decide
  rcases family_descends (prefixWord ++ tailWord_4886287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4886292 : List Nat := [2, 4, 4, 1, 1, 2, 2, 1, 2, 4]
def baseStart_4886292 : Nat := 118140960795 + 4886292 * 2 ^ 59
def prefixEnd_4886292 : Nat := 4983230072969 + 3 ^ 40 * 4886292 * 2
def baseEnd_4886292 : Nat := 836338804739700531259453

theorem tailTrace_4886292 : CollatzResearch.WordTrace tailWord_4886292 prefixEnd_4886292 836338804739700531259453 := by
  unfold tailWord_4886292
  simp only [CollatzResearch.WordTrace]
  refine ⟨89108855206903035539898565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118811806942537380719864753 89108855206903035539898565)
  ·
    refine ⟨16707910351294319163730981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89108855206903035539898565 16707910351294319163730981)
    ·
      refine ⟨3132733190867684843199559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16707910351294319163730981 3132733190867684843199559)
      ·
        refine ⟨4699099786301527264799339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3132733190867684843199559 4699099786301527264799339)
        ·
          refine ⟨7048649679452290897199009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4699099786301527264799339 7048649679452290897199009)
          ·
            refine ⟨5286487259589218172899257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7048649679452290897199009 5286487259589218172899257)
            ·
              refine ⟨3964865444691913629674443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5286487259589218172899257 3964865444691913629674443)
              ·
                refine ⟨5947298167037870444511665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3964865444691913629674443 5947298167037870444511665)
                ·
                  refine ⟨4460473625278402833383749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5947298167037870444511665 4460473625278402833383749)
                  ·
                    refine ⟨836338804739700531259453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4460473625278402833383749 836338804739700531259453)
                    ·
                      rfl

theorem cell23_4886292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_4886292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4886292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4886292 prefixEnd_4886292 := by exact prefixLift 4886292
  have htrace : WordTrace (prefixWord ++ tailWord_4886292) baseStart_4886292 baseEnd_4886292 := by
    simpa [prefixWord, tailWord_4886292, baseEnd_4886292] using wordTrace_append hprefix tailTrace_4886292
  have hstable : (prefixWord ++ tailWord_4886292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4886292).length < 2 ^ (prefixWord ++ tailWord_4886292).sum := by decide
  have hdescent : baseEnd_4886292 < baseStart_4886292 := by decide
  rcases family_descends (prefixWord ++ tailWord_4886292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4886298 : List Nat := [3, 1, 1, 3, 2, 4, 2, 1, 2, 1, 3]
def baseStart_4886298 : Nat := 118140960795 + 4886298 * 2 ^ 59
def prefixEnd_4886298 : Nat := 4983230072969 + 3 ^ 40 * 4886298 * 2
def baseEnd_4886298 : Nat := 2509019495103028570303331

theorem tailTrace_4886298 : CollatzResearch.WordTrace tailWord_4886298 prefixEnd_4886298 2509019495103028570303331 := by
  unfold tailWord_4886298
  simp only [CollatzResearch.WordTrace]
  refine ⟨44554482312946083526128887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118811952834522889403010365 44554482312946083526128887)
  ·
    refine ⟨66831723469419125289193331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44554482312946083526128887 66831723469419125289193331)
    ·
      refine ⟨100247585204128687933789997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66831723469419125289193331 100247585204128687933789997)
      ·
        refine ⟨37592844451548257975171249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100247585204128687933789997 37592844451548257975171249)
        ·
          refine ⟨28194633338661193481378437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37592844451548257975171249 28194633338661193481378437)
          ·
            refine ⟨5286493750998973777758457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28194633338661193481378437 5286493750998973777758457)
            ·
              refine ⟨3964870313249230333318843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5286493750998973777758457 3964870313249230333318843)
              ·
                refine ⟨5947305469873845499978265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3964870313249230333318843 5947305469873845499978265)
                ·
                  refine ⟨4460479102405384124983699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5947305469873845499978265 4460479102405384124983699)
                  ·
                    refine ⟨6690718653608076187475549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4460479102405384124983699 6690718653608076187475549)
                    ·
                      refine ⟨2509019495103028570303331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6690718653608076187475549 2509019495103028570303331)
                      ·
                        rfl

theorem cell23_4886298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 2, 1, 2, 1, 3].length) (baseStart_4886298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4886298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4886298 prefixEnd_4886298 := by exact prefixLift 4886298
  have htrace : WordTrace (prefixWord ++ tailWord_4886298) baseStart_4886298 baseEnd_4886298 := by
    simpa [prefixWord, tailWord_4886298, baseEnd_4886298] using wordTrace_append hprefix tailTrace_4886298
  have hstable : (prefixWord ++ tailWord_4886298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4886298).length < 2 ^ (prefixWord ++ tailWord_4886298).sum := by decide
  have hdescent : baseEnd_4886298 < baseStart_4886298 := by decide
  rcases family_descends (prefixWord ++ tailWord_4886298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4886302 : List Nat := [4, 3, 2, 2, 2, 1, 1, 2, 1, 2, 3]
def baseStart_4886302 : Nat := 118140960795 + 4886302 * 2 ^ 59
def prefixEnd_4886302 : Nat := 4983230072969 + 3 ^ 40 * 4886302 * 2
def baseEnd_4886302 : Nat := 2509021549025646554653313

theorem tailTrace_4886302 : CollatzResearch.WordTrace tailWord_4886302 prefixEnd_4886302 2509021549025646554653313 := by
  unfold tailWord_4886302
  simp only [CollatzResearch.WordTrace]
  refine ⟨22277259392971230348457645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118812050095846561858440773 22277259392971230348457645)
  ·
    refine ⟨8353972272364211380671617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22277259392971230348457645 8353972272364211380671617)
    ·
      refine ⟨6265479204273158535503713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8353972272364211380671617 6265479204273158535503713)
      ·
        refine ⟨4699109403204868901627785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6265479204273158535503713 4699109403204868901627785)
        ·
          refine ⟨3524332052403651676220839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4699109403204868901627785 3524332052403651676220839)
          ·
            refine ⟨5286498078605477514331259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3524332052403651676220839 5286498078605477514331259)
            ·
              refine ⟨7929747117908216271496889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5286498078605477514331259 7929747117908216271496889)
              ·
                refine ⟨5947310338431162203622667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7929747117908216271496889 5947310338431162203622667)
                ·
                  refine ⟨8920965507646743305434001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5947310338431162203622667 8920965507646743305434001)
                  ·
                    refine ⟨6690724130735057479075501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8920965507646743305434001 6690724130735057479075501)
                    ·
                      refine ⟨2509021549025646554653313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6690724130735057479075501 2509021549025646554653313)
                      ·
                        rfl

theorem cell23_4886302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_4886302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4886302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4886302 prefixEnd_4886302 := by exact prefixLift 4886302
  have htrace : WordTrace (prefixWord ++ tailWord_4886302) baseStart_4886302 baseEnd_4886302 := by
    simpa [prefixWord, tailWord_4886302, baseEnd_4886302] using wordTrace_append hprefix tailTrace_4886302
  have hstable : (prefixWord ++ tailWord_4886302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4886302).length < 2 ^ (prefixWord ++ tailWord_4886302).sum := by decide
  have hdescent : baseEnd_4886302 < baseStart_4886302 := by decide
  rcases family_descends (prefixWord ++ tailWord_4886302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4886304 : List Nat := [2, 1, 1, 5, 1, 1, 2, 3, 1, 4, 2]
def baseStart_4886304 : Nat := 118140960795 + 4886304 * 2 ^ 59
def prefixEnd_4886304 : Nat := 4983230072969 + 3 ^ 40 * 4886304 * 2
def baseEnd_4886304 : Nat := 2509022575986955546828303

theorem tailTrace_4886304 : CollatzResearch.WordTrace tailWord_4886304 prefixEnd_4886304 2509022575986955546828303 := by
  unfold tailWord_4886304
  simp only [CollatzResearch.WordTrace]
  refine ⟨89109074044881298564616983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118812098726508398086155977 89109074044881298564616983)
  ·
    refine ⟨133663611067321947846925475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89109074044881298564616983 133663611067321947846925475)
    ·
      refine ⟨200495416600982921770388213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133663611067321947846925475 200495416600982921770388213)
      ·
        refine ⟨18796445306342148915973895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 200495416600982921770388213 18796445306342148915973895)
        ·
          refine ⟨28194667959513223373960843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18796445306342148915973895 28194667959513223373960843)
          ·
            refine ⟨42292001939269835060941265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28194667959513223373960843 42292001939269835060941265)
            ·
              refine ⟨31719001454452376295705949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42292001939269835060941265 31719001454452376295705949)
              ·
                refine ⟨11894625545419641110889731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31719001454452376295705949 11894625545419641110889731)
                ·
                  refine ⟨17841938318129461666334597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11894625545419641110889731 17841938318129461666334597)
                  ·
                    refine ⟨3345363434649274062437737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17841938318129461666334597 3345363434649274062437737)
                    ·
                      refine ⟨2509022575986955546828303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3345363434649274062437737 2509022575986955546828303)
                      ·
                        rfl

theorem cell23_4886304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 3, 1, 4, 2].length) (baseStart_4886304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4886304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4886304 prefixEnd_4886304 := by exact prefixLift 4886304
  have htrace : WordTrace (prefixWord ++ tailWord_4886304) baseStart_4886304 baseEnd_4886304 := by
    simpa [prefixWord, tailWord_4886304, baseEnd_4886304] using wordTrace_append hprefix tailTrace_4886304
  have hstable : (prefixWord ++ tailWord_4886304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4886304).length < 2 ^ (prefixWord ++ tailWord_4886304).sum := by decide
  have hdescent : baseEnd_4886304 < baseStart_4886304 := by decide
  rcases family_descends (prefixWord ++ tailWord_4886304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4886308 : List Nat := [2, 3, 1, 3, 2, 3, 1, 2, 1, 3, 2]
def baseStart_4886308 : Nat := 118140960795 + 4886308 * 2 ^ 59
def prefixEnd_4886308 : Nat := 4983230072969 + 3 ^ 40 * 4886308 * 2
def baseEnd_4886308 : Nat := 2509024629909573531178285

theorem tailTrace_4886308 : CollatzResearch.WordTrace tailWord_4886308 prefixEnd_4886308 2509024629909573531178285 := by
  unfold tailWord_4886308
  simp only [CollatzResearch.WordTrace]
  refine ⟨89109146990874052906189789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118812195987832070541586385 89109146990874052906189789)
  ·
    refine ⟨33415930121577769839821171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89109146990874052906189789 33415930121577769839821171)
    ·
      refine ⟨50123895182366654759731757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33415930121577769839821171 50123895182366654759731757)
      ·
        refine ⟨18796460693387495534899409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50123895182366654759731757 18796460693387495534899409)
        ·
          refine ⟨14097345520040621651174557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18796460693387495534899409 14097345520040621651174557)
          ·
            refine ⟨5286504570015233119190459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14097345520040621651174557 5286504570015233119190459)
            ·
              refine ⟨7929756855022849678785689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5286504570015233119190459 7929756855022849678785689)
              ·
                refine ⟨5947317641267137259089267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7929756855022849678785689 5947317641267137259089267)
                ·
                  refine ⟨8920976461900705888633901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5947317641267137259089267 8920976461900705888633901)
                  ·
                    refine ⟨3345366173212764708237713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8920976461900705888633901 3345366173212764708237713)
                    ·
                      refine ⟨2509024629909573531178285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3345366173212764708237713 2509024629909573531178285)
                      ·
                        rfl

theorem cell23_4886308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 1, 2, 1, 3, 2].length) (baseStart_4886308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4886308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4886308 prefixEnd_4886308 := by exact prefixLift 4886308
  have htrace : WordTrace (prefixWord ++ tailWord_4886308) baseStart_4886308 baseEnd_4886308 := by
    simpa [prefixWord, tailWord_4886308, baseEnd_4886308] using wordTrace_append hprefix tailTrace_4886308
  have hstable : (prefixWord ++ tailWord_4886308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4886308).length < 2 ^ (prefixWord ++ tailWord_4886308).sum := by decide
  have hdescent : baseEnd_4886308 < baseStart_4886308 := by decide
  rcases family_descends (prefixWord ++ tailWord_4886308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4886324 : List Nat := [2, 5, 1, 1, 2, 1, 2, 1, 2, 1, 5]
def baseStart_4886324 : Nat := 118140960795 + 4886324 * 2 ^ 59
def prefixEnd_4886324 : Nat := 4983230072969 + 3 ^ 40 * 4886324 * 2
def baseEnd_4886324 : Nat := 2509032845600045468578211

theorem tailTrace_4886324 : CollatzResearch.WordTrace tailWord_4886324 prefixEnd_4886324 2509032845600045468578211 := by
  unfold tailWord_4886324
  simp only [CollatzResearch.WordTrace]
  refine ⟨89109438774845070272481013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118812585033126760363308017 89109438774845070272481013)
  ·
    refine ⟨8354009885141725338045095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 89109438774845070272481013 8354009885141725338045095)
    ·
      refine ⟨12531014827712588007067643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8354009885141725338045095 12531014827712588007067643)
      ·
        refine ⟨18796522241568882010601465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12531014827712588007067643 18796522241568882010601465)
        ·
          refine ⟨14097391681176661507951099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18796522241568882010601465 14097391681176661507951099)
          ·
            refine ⟨21146087521764992261926649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14097391681176661507951099 21146087521764992261926649)
            ·
              refine ⟨15859565641323744196444987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21146087521764992261926649 15859565641323744196444987)
              ·
                refine ⟨23789348461985616294667481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15859565641323744196444987 23789348461985616294667481)
                ·
                  refine ⟨17842011346489212221000611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23789348461985616294667481 17842011346489212221000611)
                  ·
                    refine ⟨26763017019733818331500917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17842011346489212221000611 26763017019733818331500917)
                    ·
                      refine ⟨2509032845600045468578211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26763017019733818331500917 2509032845600045468578211)
                      ·
                        rfl

theorem cell23_4886324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_4886324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4886324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4886324 prefixEnd_4886324 := by exact prefixLift 4886324
  have htrace : WordTrace (prefixWord ++ tailWord_4886324) baseStart_4886324 baseEnd_4886324 := by
    simpa [prefixWord, tailWord_4886324, baseEnd_4886324] using wordTrace_append hprefix tailTrace_4886324
  have hstable : (prefixWord ++ tailWord_4886324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4886324).length < 2 ^ (prefixWord ++ tailWord_4886324).sum := by decide
  have hdescent : baseEnd_4886324 < baseStart_4886324 := by decide
  rcases family_descends (prefixWord ++ tailWord_4886324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4886344 : List Nat := [2, 1, 3, 1, 1, 5, 1, 4, 5]
def baseStart_4886344 : Nat := 118140960795 + 4886344 * 2 ^ 59
def prefixEnd_4886344 : Nat := 4983230072969 + 3 ^ 40 * 4886344 * 2
def baseEnd_4886344 : Nat := 278782568357015043369791

theorem tailTrace_4886344 : CollatzResearch.WordTrace tailWord_4886344 prefixEnd_4886344 278782568357015043369791 := by
  unfold tailWord_4886344
  simp only [CollatzResearch.WordTrace]
  refine ⟨89109803504808841980345043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118813071339745122640460057 89109803504808841980345043)
  ·
    refine ⟨133664705257213262970517565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89109803504808841980345043 133664705257213262970517565)
    ·
      refine ⟨50124264471454973613944087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133664705257213262970517565 50124264471454973613944087)
      ·
        refine ⟨75186396707182460420916131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50124264471454973613944087 75186396707182460420916131)
        ·
          refine ⟨112779595060773690631374197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75186396707182460420916131 112779595060773690631374197)
          ·
            refine ⟨10573087036947533496691331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 112779595060773690631374197 10573087036947533496691331)
            ·
              refine ⟨15859630555421300245036997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10573087036947533496691331 15859630555421300245036997)
              ·
                refine ⟨2973680729141493795944437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15859630555421300245036997 2973680729141493795944437)
                ·
                  refine ⟨278782568357015043369791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2973680729141493795944437 278782568357015043369791)
                  ·
                    rfl

theorem cell23_4886344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 4, 5].length) (baseStart_4886344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4886344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4886344 prefixEnd_4886344 := by exact prefixLift 4886344
  have htrace : WordTrace (prefixWord ++ tailWord_4886344) baseStart_4886344 baseEnd_4886344 := by
    simpa [prefixWord, tailWord_4886344, baseEnd_4886344] using wordTrace_append hprefix tailTrace_4886344
  have hstable : (prefixWord ++ tailWord_4886344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4886344).length < 2 ^ (prefixWord ++ tailWord_4886344).sum := by decide
  have hdescent : baseEnd_4886344 < baseStart_4886344 := by decide
  rcases family_descends (prefixWord ++ tailWord_4886344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4886354 : List Nat := [3, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3]
def baseStart_4886354 : Nat := 118140960795 + 4886354 * 2 ^ 59
def prefixEnd_4886354 : Nat := 4983230072969 + 3 ^ 40 * 4886354 * 2
def baseEnd_4886354 : Nat := 2509048250019680351203073

theorem tailTrace_4886354 : CollatzResearch.WordTrace tailWord_4886354 prefixEnd_4886354 2509048250019680351203073 := by
  unfold tailWord_4886354
  simp only [CollatzResearch.WordTrace]
  refine ⟨44554992934895363917138529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118813314493054303779036077 44554992934895363917138529)
  ·
    refine ⟨33416244701171522937853897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44554992934895363917138529 33416244701171522937853897)
    ·
      refine ⟨25062183525878642203390423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33416244701171522937853897 25062183525878642203390423)
      ·
        refine ⟨37593275288817963305085635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25062183525878642203390423 37593275288817963305085635)
        ·
          refine ⟨56389912933226944957628453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37593275288817963305085635 56389912933226944957628453)
          ·
            refine ⟨10573108674980052179555335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56389912933226944957628453 10573108674980052179555335)
            ·
              refine ⟨15859663012470078269333003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10573108674980052179555335 15859663012470078269333003)
              ·
                refine ⟨23789494518705117403999505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15859663012470078269333003 23789494518705117403999505)
                ·
                  refine ⟨17842120889028838052999629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23789494518705117403999505 17842120889028838052999629)
                  ·
                    refine ⟨6690795333385814269874861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17842120889028838052999629 6690795333385814269874861)
                    ·
                      refine ⟨2509048250019680351203073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6690795333385814269874861 2509048250019680351203073)
                      ·
                        rfl

theorem cell23_4886354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3].length) (baseStart_4886354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4886354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4886354 prefixEnd_4886354 := by exact prefixLift 4886354
  have htrace : WordTrace (prefixWord ++ tailWord_4886354) baseStart_4886354 baseEnd_4886354 := by
    simpa [prefixWord, tailWord_4886354, baseEnd_4886354] using wordTrace_append hprefix tailTrace_4886354
  have hstable : (prefixWord ++ tailWord_4886354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4886354).length < 2 ^ (prefixWord ++ tailWord_4886354).sum := by decide
  have hdescent : baseEnd_4886354 < baseStart_4886354 := by decide
  rcases family_descends (prefixWord ++ tailWord_4886354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4886378 : List Nat := [3, 1, 3, 4, 1, 1, 2, 3, 5]
def baseStart_4886378 : Nat := 118140960795 + 4886378 * 2 ^ 59
def prefixEnd_4886378 : Nat := 4983230072969 + 3 ^ 40 * 4886378 * 2
def baseEnd_4886378 : Nat := 278784508172820917478107

theorem tailTrace_4886378 : CollatzResearch.WordTrace tailWord_4886378 prefixEnd_4886378 278784508172820917478107 := by
  unfold tailWord_4886378
  simp only [CollatzResearch.WordTrace]
  refine ⟨44555211772873626941856947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118813898060996338511618525 44555211772873626941856947)
  ·
    refine ⟨66832817659310440412785421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44555211772873626941856947 66832817659310440412785421)
    ·
      refine ⟨25062306622241415154794533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66832817659310440412785421 25062306622241415154794533)
      ·
        refine ⟨4699182491670265341523975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25062306622241415154794533 4699182491670265341523975)
        ·
          refine ⟨7048773737505398012285963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4699182491670265341523975 7048773737505398012285963)
          ·
            refine ⟨10573160606258097018428945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7048773737505398012285963 10573160606258097018428945)
            ·
              refine ⟨7929870454693572763821709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10573160606258097018428945 7929870454693572763821709)
              ·
                refine ⟨2973701420510089786433141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7929870454693572763821709 2973701420510089786433141)
                ·
                  refine ⟨278784508172820917478107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2973701420510089786433141 278784508172820917478107)
                  ·
                    rfl

theorem cell23_4886378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 2, 3, 5].length) (baseStart_4886378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4886378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4886378 prefixEnd_4886378 := by exact prefixLift 4886378
  have htrace : WordTrace (prefixWord ++ tailWord_4886378) baseStart_4886378 baseEnd_4886378 := by
    simpa [prefixWord, tailWord_4886378, baseEnd_4886378] using wordTrace_append hprefix tailTrace_4886378
  have hstable : (prefixWord ++ tailWord_4886378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4886378).length < 2 ^ (prefixWord ++ tailWord_4886378).sum := by decide
  have hdescent : baseEnd_4886378 < baseStart_4886378 := by decide
  rcases family_descends (prefixWord ++ tailWord_4886378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4886387 : List Nat := [1, 1, 1, 2, 2, 1, 3, 1, 7, 4]
def baseStart_4886387 : Nat := 118140960795 + 4886387 * 2 ^ 59
def prefixEnd_4886387 : Nat := 4983230072969 + 3 ^ 40 * 4886387 * 2
def baseEnd_4886387 : Nat := 836355064960426240696807

theorem tailTrace_4886387 : CollatzResearch.WordTrace tailWord_4886387 prefixEnd_4886387 836355064960426240696807 := by
  unfold tailWord_4886387
  simp only [CollatzResearch.WordTrace]
  refine ⟨178221175348461902304505415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118814116898974601536336943 178221175348461902304505415)
  ·
    refine ⟨267331763022692853456758123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178221175348461902304505415 267331763022692853456758123)
    ·
      refine ⟨400997644534039280185137185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 267331763022692853456758123 400997644534039280185137185)
      ·
        refine ⟨300748233400529460138852889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 400997644534039280185137185 300748233400529460138852889)
        ·
          refine ⟨225561175050397095104139667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 300748233400529460138852889 225561175050397095104139667)
          ·
            refine ⟨338341762575595642656209501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 225561175050397095104139667 338341762575595642656209501)
            ·
              refine ⟨126878160965848365996078563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 338341762575595642656209501 126878160965848365996078563)
              ·
                refine ⟨190317241448772548994117845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126878160965848365996078563 190317241448772548994117845)
                ·
                  refine ⟨4460560346455606617049637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 190317241448772548994117845 4460560346455606617049637)
                  ·
                    refine ⟨836355064960426240696807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4460560346455606617049637 836355064960426240696807)
                    ·
                      rfl

theorem cell23_4886387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 7, 4].length) (baseStart_4886387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4886387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4886387 prefixEnd_4886387 := by exact prefixLift 4886387
  have htrace : WordTrace (prefixWord ++ tailWord_4886387) baseStart_4886387 baseEnd_4886387 := by
    simpa [prefixWord, tailWord_4886387, baseEnd_4886387] using wordTrace_append hprefix tailTrace_4886387
  have hstable : (prefixWord ++ tailWord_4886387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4886387).length < 2 ^ (prefixWord ++ tailWord_4886387).sum := by decide
  have hdescent : baseEnd_4886387 < baseStart_4886387 := by decide
  rcases family_descends (prefixWord ++ tailWord_4886387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4886394 : List Nat := [3, 1, 1, 1, 1, 1, 5, 2, 2, 4, 2]
def baseStart_4886394 : Nat := 118140960795 + 4886394 * 2 ^ 59
def prefixEnd_4886394 : Nat := 4983230072969 + 3 ^ 40 * 4886394 * 2
def baseEnd_4886394 : Nat := 2509068789245860194702889

theorem tailTrace_4886394 : CollatzResearch.WordTrace tailWord_4886394 prefixEnd_4886394 2509068789245860194702889 := by
  unfold tailWord_4886394
  simp only [CollatzResearch.WordTrace]
  refine ⟨44555357664859135625002559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118814287106291028333340157 44555357664859135625002559)
  ·
    refine ⟨66833036497288703437503839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44555357664859135625002559 66833036497288703437503839)
    ·
      refine ⟨100249554745933055156255759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66833036497288703437503839 100249554745933055156255759)
      ·
        refine ⟨150374332118899582734383639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100249554745933055156255759 150374332118899582734383639)
        ·
          refine ⟨225561498178349374101575459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150374332118899582734383639 225561498178349374101575459)
          ·
            refine ⟨338342247267524061152363189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 225561498178349374101575459 338342247267524061152363189)
            ·
              refine ⟨31719585681330380733034049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 338342247267524061152363189 31719585681330380733034049)
              ·
                refine ⟨23789689260997785549775537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31719585681330380733034049 23789689260997785549775537)
                ·
                  refine ⟨17842266945748339162331653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23789689260997785549775537 17842266945748339162331653)
                  ·
                    refine ⟨3345425052327813592937185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17842266945748339162331653 3345425052327813592937185)
                    ·
                      refine ⟨2509068789245860194702889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3345425052327813592937185 2509068789245860194702889)
                      ·
                        rfl

theorem cell23_4886394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 2, 2, 4, 2].length) (baseStart_4886394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4886394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4886394 prefixEnd_4886394 := by exact prefixLift 4886394
  have htrace : WordTrace (prefixWord ++ tailWord_4886394) baseStart_4886394 baseEnd_4886394 := by
    simpa [prefixWord, tailWord_4886394, baseEnd_4886394] using wordTrace_append hprefix tailTrace_4886394
  have hstable : (prefixWord ++ tailWord_4886394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4886394).length < 2 ^ (prefixWord ++ tailWord_4886394).sum := by decide
  have hdescent : baseEnd_4886394 < baseStart_4886394 := by decide
  rcases family_descends (prefixWord ++ tailWord_4886394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4886404 : List Nat := [2, 3, 2, 1, 1, 1, 3, 3, 3, 4]
def baseStart_4886404 : Nat := 118140960795 + 4886404 * 2 ^ 59
def prefixEnd_4886404 : Nat := 4983230072969 + 3 ^ 40 * 4886404 * 2
def baseEnd_4886404 : Nat := 836357974684135051859281

theorem tailTrace_4886404 : CollatzResearch.WordTrace tailWord_4886404 prefixEnd_4886404 836357974684135051859281 := by
  unfold tailWord_4886404
  simp only [CollatzResearch.WordTrace]
  refine ⟨89110897694700157103937133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118814530259600209471916177 89110897694700157103937133)
  ·
    refine ⟨33416586635512558913976425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89110897694700157103937133 33416586635512558913976425)
    ·
      refine ⟨25062439976634419185482319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33416586635512558913976425 25062439976634419185482319)
      ·
        refine ⟨37593659964951628778223479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25062439976634419185482319 37593659964951628778223479)
        ·
          refine ⟨56390489947427443167335219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37593659964951628778223479 56390489947427443167335219)
          ·
            refine ⟨84585734921141164751002829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56390489947427443167335219 84585734921141164751002829)
            ·
              refine ⟨31719650595427936781626061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84585734921141164751002829 31719650595427936781626061)
              ·
                refine ⟨11894868973285476293109773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31719650595427936781626061 11894868973285476293109773)
                ·
                  refine ⟨4460575864982053609916165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11894868973285476293109773 4460575864982053609916165)
                  ·
                    refine ⟨836357974684135051859281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4460575864982053609916165 836357974684135051859281)
                    ·
                      rfl

theorem cell23_4886404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 3, 3, 4].length) (baseStart_4886404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4886404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4886404 prefixEnd_4886404 := by exact prefixLift 4886404
  have htrace : WordTrace (prefixWord ++ tailWord_4886404) baseStart_4886404 baseEnd_4886404 := by
    simpa [prefixWord, tailWord_4886404, baseEnd_4886404] using wordTrace_append hprefix tailTrace_4886404
  have hstable : (prefixWord ++ tailWord_4886404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4886404).length < 2 ^ (prefixWord ++ tailWord_4886404).sum := by decide
  have hdescent : baseEnd_4886404 < baseStart_4886404 := by decide
  rcases family_descends (prefixWord ++ tailWord_4886404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4886417 : List Nat := [1, 2, 2, 1, 1, 1, 4, 5, 6]
def baseStart_4886417 : Nat := 118140960795 + 4886417 * 2 ^ 59
def prefixEnd_4886417 : Nat := 4983230072969 + 3 ^ 40 * 4886417 * 2
def baseEnd_4886417 : Nat := 278786733255657067190587

theorem tailTrace_4886417 : CollatzResearch.WordTrace tailWord_4886417 prefixEnd_4886417 278786733255657067190587 := by
  unfold tailWord_4886417
  simp only [CollatzResearch.WordTrace]
  refine ⟨178222269538353217428097505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118814846358902144952065003 178222269538353217428097505)
  ·
    refine ⟨133666702153764913071073129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178222269538353217428097505 133666702153764913071073129)
    ·
      refine ⟨100250026615323684803304847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133666702153764913071073129 100250026615323684803304847)
      ·
        refine ⟨150375039922985527204957271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100250026615323684803304847 150375039922985527204957271)
        ·
          refine ⟨225562559884478290807435907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150375039922985527204957271 225562559884478290807435907)
          ·
            refine ⟨338343839826717436211153861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 225562559884478290807435907 338343839826717436211153861)
            ·
              refine ⟨63439469967509519289591349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 338343839826717436211153861 63439469967509519289591349)
              ·
                refine ⟨5947450309454017433399189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 63439469967509519289591349 5947450309454017433399189)
                ·
                  refine ⟨278786733255657067190587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5947450309454017433399189 278786733255657067190587)
                  ·
                    rfl

theorem cell23_4886417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 5, 6].length) (baseStart_4886417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4886417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4886417 prefixEnd_4886417 := by exact prefixLift 4886417
  have htrace : WordTrace (prefixWord ++ tailWord_4886417) baseStart_4886417 baseEnd_4886417 := by
    simpa [prefixWord, tailWord_4886417, baseEnd_4886417] using wordTrace_append hprefix tailTrace_4886417
  have hstable : (prefixWord ++ tailWord_4886417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4886417).length < 2 ^ (prefixWord ++ tailWord_4886417).sum := by decide
  have hdescent : baseEnd_4886417 < baseStart_4886417 := by decide
  rcases family_descends (prefixWord ++ tailWord_4886417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4886511 : List Nat := [1, 1, 2, 1, 4, 2, 4, 2, 2, 4]
def baseStart_4886511 : Nat := 118140960795 + 4886511 * 2 ^ 59
def prefixEnd_4886511 : Nat := 4983230072969 + 3 ^ 40 * 4886511 * 2
def baseEnd_4886511 : Nat := 836376288827478745646617

theorem tailTrace_4886511 : CollatzResearch.WordTrace tailWord_4886511 prefixEnd_4886511 836376288827478745646617 := by
  unfold tailWord_4886511
  simp only [CollatzResearch.WordTrace]
  refine ⟨178225698000012671482019387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118817132000008447654679591 178225698000012671482019387)
  ·
    refine ⟨267338547000019007223029081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178225698000012671482019387 267338547000019007223029081)
    ·
      refine ⟨200503910250014255417271811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 267338547000019007223029081 200503910250014255417271811)
      ·
        refine ⟨300755865375021383125907717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200503910250014255417271811 300755865375021383125907717)
        ·
          refine ⟨56391724757816509336107697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 300755865375021383125907717 56391724757816509336107697)
          ·
            refine ⟨42293793568362382002080773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56391724757816509336107697 42293793568362382002080773)
            ·
              refine ⟨7930086294067946625390145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42293793568362382002080773 7930086294067946625390145)
              ·
                refine ⟨5947564720550959969042609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7930086294067946625390145 5947564720550959969042609)
                ·
                  refine ⟨4460673540413219976781957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5947564720550959969042609 4460673540413219976781957)
                  ·
                    refine ⟨836376288827478745646617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4460673540413219976781957 836376288827478745646617)
                    ·
                      rfl

theorem cell23_4886511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 4, 2, 2, 4].length) (baseStart_4886511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4886511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4886511 prefixEnd_4886511 := by exact prefixLift 4886511
  have htrace : WordTrace (prefixWord ++ tailWord_4886511) baseStart_4886511 baseEnd_4886511 := by
    simpa [prefixWord, tailWord_4886511, baseEnd_4886511] using wordTrace_append hprefix tailTrace_4886511
  have hstable : (prefixWord ++ tailWord_4886511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4886511).length < 2 ^ (prefixWord ++ tailWord_4886511).sum := by decide
  have hdescent : baseEnd_4886511 < baseStart_4886511 := by decide
  rcases family_descends (prefixWord ++ tailWord_4886511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4886527 : List Nat := [1, 1, 2, 2, 1, 2, 1, 3, 2, 2, 6]
def baseStart_4886527 : Nat := 118140960795 + 4886527 * 2 ^ 59
def prefixEnd_4886527 : Nat := 4983230072969 + 3 ^ 40 * 4886527 * 2
def baseEnd_4886527 : Nat := 2509137082172908174339777

theorem tailTrace_4886527 : CollatzResearch.WordTrace tailWord_4886527 prefixEnd_4886527 2509137082172908174339777 := by
  unfold tailWord_4886527
  simp only [CollatzResearch.WordTrace]
  refine ⟨178226281567954706214601835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118817521045303137476401223 178226281567954706214601835)
  ·
    refine ⟨267339422351932059321902753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178226281567954706214601835 267339422351932059321902753)
    ·
      refine ⟨200504566763949044491427065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 267339422351932059321902753 200504566763949044491427065)
      ·
        refine ⟨150378425072961783368570299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 200504566763949044491427065 150378425072961783368570299)
        ·
          refine ⟨225567637609442675052855449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150378425072961783368570299 225567637609442675052855449)
          ·
            refine ⟨169175728207082006289641587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 225567637609442675052855449 169175728207082006289641587)
            ·
              refine ⟨253763592310623009434462381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 169175728207082006289641587 253763592310623009434462381)
              ·
                refine ⟨95161347116483628537923393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 253763592310623009434462381 95161347116483628537923393)
                ·
                  refine ⟨71371010337362721403442545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 95161347116483628537923393 71371010337362721403442545)
                  ·
                    refine ⟨53528257753022041052581909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 71371010337362721403442545 53528257753022041052581909)
                    ·
                      refine ⟨2509137082172908174339777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53528257753022041052581909 2509137082172908174339777)
                      ·
                        rfl

theorem cell23_4886527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 2, 2, 6].length) (baseStart_4886527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4886527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4886527 prefixEnd_4886527 := by exact prefixLift 4886527
  have htrace : WordTrace (prefixWord ++ tailWord_4886527) baseStart_4886527 baseEnd_4886527 := by
    simpa [prefixWord, tailWord_4886527, baseEnd_4886527] using wordTrace_append hprefix tailTrace_4886527
  have hstable : (prefixWord ++ tailWord_4886527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4886527).length < 2 ^ (prefixWord ++ tailWord_4886527).sum := by decide
  have hdescent : baseEnd_4886527 < baseStart_4886527 := by decide
  rcases family_descends (prefixWord ++ tailWord_4886527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4886585 : List Nat := [1, 2, 1, 5, 4, 1, 1, 1, 1, 3, 3]
def baseStart_4886585 : Nat := 118140960795 + 4886585 * 2 ^ 59
def prefixEnd_4886585 : Nat := 4983230072969 + 3 ^ 40 * 4886585 * 2
def baseEnd_4886585 : Nat := 2509166864050868947414511

theorem tailTrace_4886585 : CollatzResearch.WordTrace tailWord_4886585 prefixEnd_4886585 2509166864050868947414511 := by
  unfold tailWord_4886585
  simp only [CollatzResearch.WordTrace]
  refine ⟨178228397001744582120213209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118818931334496388080142139 178228397001744582120213209)
  ·
    refine ⟨133671297751308436590159907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178228397001744582120213209 133671297751308436590159907)
    ·
      refine ⟨200506946626962654885239861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133671297751308436590159907 200506946626962654885239861)
      ·
        refine ⟨18797526246277748895491237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 200506946626962654885239861 18797526246277748895491237)
        ·
          refine ⟨3524536171177077917904607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18797526246277748895491237 3524536171177077917904607)
          ·
            refine ⟨5286804256765616876856911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3524536171177077917904607 5286804256765616876856911)
            ·
              refine ⟨7930206385148425315285367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5286804256765616876856911 7930206385148425315285367)
              ·
                refine ⟨11895309577722637972928051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7930206385148425315285367 11895309577722637972928051)
                ·
                  refine ⟨17842964366583956959392077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11895309577722637972928051 17842964366583956959392077)
                  ·
                    refine ⟨6691111637468983859772029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17842964366583956959392077 6691111637468983859772029)
                    ·
                      refine ⟨2509166864050868947414511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6691111637468983859772029 2509166864050868947414511)
                      ·
                        rfl

theorem cell23_4886585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 1, 1, 1, 3, 3].length) (baseStart_4886585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4886585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4886585 prefixEnd_4886585 := by exact prefixLift 4886585
  have htrace : WordTrace (prefixWord ++ tailWord_4886585) baseStart_4886585 baseEnd_4886585 := by
    simpa [prefixWord, tailWord_4886585, baseEnd_4886585] using wordTrace_append hprefix tailTrace_4886585
  have hstable : (prefixWord ++ tailWord_4886585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4886585).length < 2 ^ (prefixWord ++ tailWord_4886585).sum := by decide
  have hdescent : baseEnd_4886585 < baseStart_4886585 := by decide
  rcases family_descends (prefixWord ++ tailWord_4886585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4886604 : List Nat := [2, 2, 1, 3, 1, 1, 2, 2, 1, 4, 4]
def baseStart_4886604 : Nat := 118140960795 + 4886604 * 2 ^ 59
def prefixEnd_4886604 : Nat := 4983230072969 + 3 ^ 40 * 4886604 * 2
def baseEnd_4886604 : Nat := 2509176620183304373076923

theorem tailTrace_4886604 : CollatzResearch.WordTrace tailWord_4886604 prefixEnd_4886604 2509176620183304373076923 := by
  unfold tailWord_4886604
  simp only [CollatzResearch.WordTrace]
  refine ⟨89114544994337874182577433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118819393325783832243436577 89114544994337874182577433)
  ·
    refine ⟨66835908745753405636933075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89114544994337874182577433 66835908745753405636933075)
    ·
      refine ⟨100253863118630108455399613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66835908745753405636933075 100253863118630108455399613)
      ·
        refine ⟨37595198669486290670774855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100253863118630108455399613 37595198669486290670774855)
        ·
          refine ⟨56392798004229436006162283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37595198669486290670774855 56392798004229436006162283)
          ·
            refine ⟨84589197006344154009243425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56392798004229436006162283 84589197006344154009243425)
            ·
              refine ⟨63441897754758115506932569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84589197006344154009243425 63441897754758115506932569)
              ·
                refine ⟨47581423316068586630199427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63441897754758115506932569 47581423316068586630199427)
                ·
                  refine ⟨71372134974102879945299141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47581423316068586630199427 71372134974102879945299141)
                  ·
                    refine ⟨13382275307644289989743589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 71372134974102879945299141 13382275307644289989743589)
                    ·
                      refine ⟨2509176620183304373076923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13382275307644289989743589 2509176620183304373076923)
                      ·
                        rfl

theorem cell23_4886604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 2, 1, 4, 4].length) (baseStart_4886604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4886604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4886604 prefixEnd_4886604 := by exact prefixLift 4886604
  have htrace : WordTrace (prefixWord ++ tailWord_4886604) baseStart_4886604 baseEnd_4886604 := by
    simpa [prefixWord, tailWord_4886604, baseEnd_4886604] using wordTrace_append hprefix tailTrace_4886604
  have hstable : (prefixWord ++ tailWord_4886604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4886604).length < 2 ^ (prefixWord ++ tailWord_4886604).sum := by decide
  have hdescent : baseEnd_4886604 < baseStart_4886604 := by decide
  rcases family_descends (prefixWord ++ tailWord_4886604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4886642 : List Nat := [3, 2, 1, 2, 2, 2, 4, 1, 2, 2, 2]
def baseStart_4886642 : Nat := 118140960795 + 4886642 * 2 ^ 59
def prefixEnd_4886642 : Nat := 4983230072969 + 3 ^ 40 * 4886642 * 2
def baseEnd_4886642 : Nat := 2509196132448175224401749

theorem tailTrace_4886642 : CollatzResearch.WordTrace tailWord_4886642 prefixEnd_4886642 2509196132448175224401749 := by
  unfold tailWord_4886642
  simp only [CollatzResearch.WordTrace]
  refine ⟨44557618990634520213759545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118820317308358720570025453 44557618990634520213759545)
  ·
    refine ⟨33418214242975890160319659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44557618990634520213759545 33418214242975890160319659)
    ·
      refine ⟨50127321364463835240479489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33418214242975890160319659 50127321364463835240479489)
      ·
        refine ⟨37595491023347876430359617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50127321364463835240479489 37595491023347876430359617)
        ·
          refine ⟨28196618267510907322769713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37595491023347876430359617 28196618267510907322769713)
          ·
            refine ⟨21147463700633180492077285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28196618267510907322769713 21147463700633180492077285)
            ·
              refine ⟨3965149443868721342264491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21147463700633180492077285 3965149443868721342264491)
              ·
                refine ⟨5947724165803082013396737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3965149443868721342264491 5947724165803082013396737)
                ·
                  refine ⟨4460793124352311510047553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5947724165803082013396737 4460793124352311510047553)
                  ·
                    refine ⟨3345594843264233632535665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4460793124352311510047553 3345594843264233632535665)
                    ·
                      refine ⟨2509196132448175224401749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3345594843264233632535665 2509196132448175224401749)
                      ·
                        rfl

theorem cell23_4886642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 4, 1, 2, 2, 2].length) (baseStart_4886642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4886642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4886642 prefixEnd_4886642 := by exact prefixLift 4886642
  have htrace : WordTrace (prefixWord ++ tailWord_4886642) baseStart_4886642 baseEnd_4886642 := by
    simpa [prefixWord, tailWord_4886642, baseEnd_4886642] using wordTrace_append hprefix tailTrace_4886642
  have hstable : (prefixWord ++ tailWord_4886642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4886642).length < 2 ^ (prefixWord ++ tailWord_4886642).sum := by decide
  have hdescent : baseEnd_4886642 < baseStart_4886642 := by decide
  rcases family_descends (prefixWord ++ tailWord_4886642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4886661 : List Nat := [1, 3, 1, 1, 5, 1, 1, 3, 2, 5]
def baseStart_4886661 : Nat := 118140960795 + 4886661 * 2 ^ 59
def prefixEnd_4886661 : Nat := 4983230072969 + 3 ^ 40 * 4886661 * 2
def baseEnd_4886661 : Nat := 836401962860203550021387

theorem tailTrace_4886661 : CollatzResearch.WordTrace tailWord_4886661 prefixEnd_4886661 836401962860203550021387 := by
  unfold tailWord_4886661
  simp only [CollatzResearch.WordTrace]
  refine ⟨178231168949469247099979837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118820779299646164733319891 178231168949469247099979837)
  ·
    refine ⟨66836688356050967662492439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 178231168949469247099979837 66836688356050967662492439)
    ·
      refine ⟨100255032534076451493738659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66836688356050967662492439 100255032534076451493738659)
      ·
        refine ⟨150382548801114677240607989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100255032534076451493738659 150382548801114677240607989)
        ·
          refine ⟨14098363950104500991306999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 150382548801114677240607989 14098363950104500991306999)
          ·
            refine ⟨21147545925156751486960499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14098363950104500991306999 21147545925156751486960499)
            ·
              refine ⟨31721318887735127230440749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21147545925156751486960499 31721318887735127230440749)
              ·
                refine ⟨11895494582900672711415281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31721318887735127230440749 11895494582900672711415281)
                ·
                  refine ⟨8921620937175504533561461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11895494582900672711415281 8921620937175504533561461)
                  ·
                    refine ⟨836401962860203550021387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8921620937175504533561461 836401962860203550021387)
                    ·
                      rfl

theorem cell23_4886661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 3, 2, 5].length) (baseStart_4886661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4886661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4886661 prefixEnd_4886661 := by exact prefixLift 4886661
  have htrace : WordTrace (prefixWord ++ tailWord_4886661) baseStart_4886661 baseEnd_4886661 := by
    simpa [prefixWord, tailWord_4886661, baseEnd_4886661] using wordTrace_append hprefix tailTrace_4886661
  have hstable : (prefixWord ++ tailWord_4886661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4886661).length < 2 ^ (prefixWord ++ tailWord_4886661).sum := by decide
  have hdescent : baseEnd_4886661 < baseStart_4886661 := by decide
  rcases family_descends (prefixWord ++ tailWord_4886661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4886681 : List Nat := [1, 2, 1, 2, 1, 2, 1, 2, 3, 6, 2]
def baseStart_4886681 : Nat := 118140960795 + 4886681 * 2 ^ 59
def prefixEnd_4886681 : Nat := 4983230072969 + 3 ^ 40 * 4886681 * 2
def baseEnd_4886681 : Nat := 2509216158193700571814069

theorem tailTrace_4886681 : CollatzResearch.WordTrace tailWord_4886681 prefixEnd_4886681 2509216158193700571814069 := by
  unfold tailWord_4886681
  simp only [CollatzResearch.WordTrace]
  refine ⟨178231898409396790515707897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118821265606264527010471931 178231898409396790515707897)
  ·
    refine ⟨133673923807047592886780923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178231898409396790515707897 133673923807047592886780923)
    ·
      refine ⟨200510885710571389330171385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133673923807047592886780923 200510885710571389330171385)
      ·
        refine ⟨150383164282928541997628539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 200510885710571389330171385 150383164282928541997628539)
        ·
          refine ⟨225574746424392812996442809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150383164282928541997628539 225574746424392812996442809)
          ·
            refine ⟨169181059818294609747332107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 225574746424392812996442809 169181059818294609747332107)
            ·
              refine ⟨253771589727441914620998161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 169181059818294609747332107 253771589727441914620998161)
              ·
                refine ⟨190328692295581435965748621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 253771589727441914620998161 190328692295581435965748621)
                ·
                  refine ⟨71373259610843038487155733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 190328692295581435965748621 71373259610843038487155733)
                  ·
                    refine ⟨3345621544258267429085425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 71373259610843038487155733 3345621544258267429085425)
                    ·
                      refine ⟨2509216158193700571814069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3345621544258267429085425 2509216158193700571814069)
                      ·
                        rfl

theorem cell23_4886681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 3, 6, 2].length) (baseStart_4886681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4886681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4886681 prefixEnd_4886681 := by exact prefixLift 4886681
  have htrace : WordTrace (prefixWord ++ tailWord_4886681) baseStart_4886681 baseEnd_4886681 := by
    simpa [prefixWord, tailWord_4886681, baseEnd_4886681] using wordTrace_append hprefix tailTrace_4886681
  have hstable : (prefixWord ++ tailWord_4886681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4886681).length < 2 ^ (prefixWord ++ tailWord_4886681).sum := by decide
  have hdescent : baseEnd_4886681 < baseStart_4886681 := by decide
  rcases family_descends (prefixWord ++ tailWord_4886681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4886682 : List Nat := [3, 1, 1, 5, 2, 2, 2, 2, 5]
def baseStart_4886682 : Nat := 118140960795 + 4886682 * 2 ^ 59
def prefixEnd_4886682 : Nat := 4983230072969 + 3 ^ 40 * 4886682 * 2
def baseEnd_4886682 : Nat := 278801852408261674211285

theorem tailTrace_4886682 : CollatzResearch.WordTrace tailWord_4886682 prefixEnd_4886682 278801852408261674211285 := by
  unfold tailWord_4886682
  simp only [CollatzResearch.WordTrace]
  refine ⟨44557983720598291921623575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118821289921595445124329533 44557983720598291921623575)
  ·
    refine ⟨66836975580897437882435363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44557983720598291921623575 66836975580897437882435363)
    ·
      refine ⟨100255463371346156823653045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66836975580897437882435363 100255463371346156823653045)
      ·
        refine ⟨9398949691063702202217473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 100255463371346156823653045 9398949691063702202217473)
        ·
          refine ⟨7049212268297776651663105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9398949691063702202217473 7049212268297776651663105)
          ·
            refine ⟨5286909201223332488747329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7049212268297776651663105 5286909201223332488747329)
            ·
              refine ⟨3965181900917499366560497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5286909201223332488747329 3965181900917499366560497)
              ·
                refine ⟨2973886425688124524920373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3965181900917499366560497 2973886425688124524920373)
                ·
                  refine ⟨278801852408261674211285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2973886425688124524920373 278801852408261674211285)
                  ·
                    rfl

theorem cell23_4886682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 2, 2, 5].length) (baseStart_4886682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4886682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4886682 prefixEnd_4886682 := by exact prefixLift 4886682
  have htrace : WordTrace (prefixWord ++ tailWord_4886682) baseStart_4886682 baseEnd_4886682 := by
    simpa [prefixWord, tailWord_4886682, baseEnd_4886682] using wordTrace_append hprefix tailTrace_4886682
  have hstable : (prefixWord ++ tailWord_4886682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4886682).length < 2 ^ (prefixWord ++ tailWord_4886682).sum := by decide
  have hdescent : baseEnd_4886682 < baseStart_4886682 := by decide
  rcases family_descends (prefixWord ++ tailWord_4886682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4886738 : List Nat := [3, 2, 2, 2, 1, 2, 3, 2, 6]
def baseStart_4886738 : Nat := 118140960795 + 4886738 * 2 ^ 59
def prefixEnd_4886738 : Nat := 4983230072969 + 3 ^ 40 * 4886738 * 2
def baseEnd_4886738 : Nat := 278805047399000760977923

theorem tailTrace_4886738 : CollatzResearch.WordTrace tailWord_4886738 prefixEnd_4886738 278805047399000760977923 := by
  unfold tailWord_4886738
  simp only [CollatzResearch.WordTrace]
  refine ⟨44558494342547572312633217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118822651580126859500355245 44558494342547572312633217)
  ·
    refine ⟨33418870756910679234474913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44558494342547572312633217 33418870756910679234474913)
    ·
      refine ⟨25064153067683009425856185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33418870756910679234474913 25064153067683009425856185)
      ·
        refine ⟨18798114800762257069392139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25064153067683009425856185 18798114800762257069392139)
        ·
          refine ⟨28197172201143385604088209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18798114800762257069392139 28197172201143385604088209)
          ·
            refine ⟨21147879150857539203066157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28197172201143385604088209 21147879150857539203066157)
            ·
              refine ⟨7930454681571577201149809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21147879150857539203066157 7930454681571577201149809)
              ·
                refine ⟨5947841011178682900862357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7930454681571577201149809 5947841011178682900862357)
                ·
                  refine ⟨278805047399000760977923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5947841011178682900862357 278805047399000760977923)
                  ·
                    rfl

theorem cell23_4886738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3, 2, 6].length) (baseStart_4886738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4886738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4886738 prefixEnd_4886738 := by exact prefixLift 4886738
  have htrace : WordTrace (prefixWord ++ tailWord_4886738) baseStart_4886738 baseEnd_4886738 := by
    simpa [prefixWord, tailWord_4886738, baseEnd_4886738] using wordTrace_append hprefix tailTrace_4886738
  have hstable : (prefixWord ++ tailWord_4886738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4886738).length < 2 ^ (prefixWord ++ tailWord_4886738).sum := by decide
  have hdescent : baseEnd_4886738 < baseStart_4886738 := by decide
  rcases family_descends (prefixWord ++ tailWord_4886738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4886742 : List Nat := [5, 2, 1, 2, 1, 2, 2, 1, 3, 4]
def baseStart_4886742 : Nat := 118140960795 + 4886742 * 2 ^ 59
def prefixEnd_4886742 : Nat := 4983230072969 + 3 ^ 40 * 4886742 * 2
def baseEnd_4886742 : Nat := 836415826837874944383763

theorem tailTrace_4886742 : CollatzResearch.WordTrace tailWord_4886742 prefixEnd_4886742 836415826837874944383763 := by
  unfold tailWord_4886742
  simp only [CollatzResearch.WordTrace]
  refine ⟨11139632703885987370854905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 118822748841450531955785653 11139632703885987370854905)
  ·
    refine ⟨8354724527914490528141179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11139632703885987370854905 8354724527914490528141179)
    ·
      refine ⟨12532086791871735792211769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8354724527914490528141179 12532086791871735792211769)
      ·
        refine ⟨9399065093903801844158827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12532086791871735792211769 9399065093903801844158827)
        ·
          refine ⟨14098597640855702766238241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9399065093903801844158827 14098597640855702766238241)
          ·
            refine ⟨10573948230641777074678681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14098597640855702766238241 10573948230641777074678681)
            ·
              refine ⟨7930461172981332806009011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10573948230641777074678681 7930461172981332806009011)
              ·
                refine ⟨11895691759471999209013517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7930461172981332806009011 11895691759471999209013517)
                ·
                  refine ⟨4460884409801999703380069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11895691759471999209013517 4460884409801999703380069)
                  ·
                    refine ⟨836415826837874944383763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4460884409801999703380069 836415826837874944383763)
                    ·
                      rfl

theorem cell23_4886742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 2, 1, 3, 4].length) (baseStart_4886742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4886742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4886742 prefixEnd_4886742 := by exact prefixLift 4886742
  have htrace : WordTrace (prefixWord ++ tailWord_4886742) baseStart_4886742 baseEnd_4886742 := by
    simpa [prefixWord, tailWord_4886742, baseEnd_4886742] using wordTrace_append hprefix tailTrace_4886742
  have hstable : (prefixWord ++ tailWord_4886742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4886742).length < 2 ^ (prefixWord ++ tailWord_4886742).sum := by decide
  have hdescent : baseEnd_4886742 < baseStart_4886742 := by decide
  rcases family_descends (prefixWord ++ tailWord_4886742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4886781 : List Nat := [1, 4, 1, 1, 1, 1, 1, 6, 1, 6]
def baseStart_4886781 : Nat := 118140960795 + 4886781 * 2 ^ 59
def prefixEnd_4886781 : Nat := 4983230072969 + 3 ^ 40 * 4886781 * 2
def baseEnd_4886781 : Nat := 836422502086383393521203

theorem tailTrace_4886781 : CollatzResearch.WordTrace tailWord_4886781 prefixEnd_4886781 836422502086383393521203 := by
  unfold tailWord_4886781
  simp only [CollatzResearch.WordTrace]
  refine ⟨178235545709034507594348197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118823697139356338396232131 178235545709034507594348197)
  ·
    refine ⟨33419164820443970173940287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 178235545709034507594348197 33419164820443970173940287)
    ·
      refine ⟨50128747230665955260910431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33419164820443970173940287 50128747230665955260910431)
      ·
        refine ⟨75193120845998932891365647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50128747230665955260910431 75193120845998932891365647)
        ·
          refine ⟨112789681268998399337048471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75193120845998932891365647 112789681268998399337048471)
          ·
            refine ⟨169184521903497599005572707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112789681268998399337048471 169184521903497599005572707)
            ·
              refine ⟨253776782855246398508359061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 169184521903497599005572707 253776782855246398508359061)
              ·
                refine ⟨11895786696339674930079331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 253776782855246398508359061 11895786696339674930079331)
                ·
                  refine ⟨17843680044509512395118997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11895786696339674930079331 17843680044509512395118997)
                  ·
                    refine ⟨836422502086383393521203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17843680044509512395118997 836422502086383393521203)
                    ·
                      rfl

theorem cell23_4886781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 6, 1, 6].length) (baseStart_4886781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4886781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4886781 prefixEnd_4886781 := by exact prefixLift 4886781
  have htrace : WordTrace (prefixWord ++ tailWord_4886781) baseStart_4886781 baseEnd_4886781 := by
    simpa [prefixWord, tailWord_4886781, baseEnd_4886781] using wordTrace_append hprefix tailTrace_4886781
  have hstable : (prefixWord ++ tailWord_4886781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4886781).length < 2 ^ (prefixWord ++ tailWord_4886781).sum := by decide
  have hdescent : baseEnd_4886781 < baseStart_4886781 := by decide
  rcases family_descends (prefixWord ++ tailWord_4886781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4886798 : List Nat := [4, 1, 1, 2, 1, 2, 1, 3, 4, 4]
def baseStart_4886798 : Nat := 118140960795 + 4886798 * 2 ^ 59
def prefixEnd_4886798 : Nat := 4983230072969 + 3 ^ 40 * 4886798 * 2
def baseEnd_4886798 : Nat := 836425411810092204683677

theorem tailTrace_4886798 : CollatzResearch.WordTrace tailWord_4886798 prefixEnd_4886798 836425411810092204683677 := by
  unfold tailWord_4886798
  simp only [CollatzResearch.WordTrace]
  refine ⟨22279520718746614937214631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118824110499981946331811365 22279520718746614937214631)
  ·
    refine ⟨33419281078119922405821947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22279520718746614937214631 33419281078119922405821947)
    ·
      refine ⟨50128921617179883608732921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33419281078119922405821947 50128921617179883608732921)
      ·
        refine ⟨37596691212884912706549691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50128921617179883608732921 37596691212884912706549691)
        ·
          refine ⟨56395036819327369059824537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37596691212884912706549691 56395036819327369059824537)
          ·
            refine ⟨42296277614495526794868403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56395036819327369059824537 42296277614495526794868403)
            ·
              refine ⟨63444416421743290192302605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42296277614495526794868403 63444416421743290192302605)
              ·
                refine ⟨23791656158153733822113477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63444416421743290192302605 23791656158153733822113477)
                ·
                  refine ⟨4460935529653825091646277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23791656158153733822113477 4460935529653825091646277)
                  ·
                    refine ⟨836425411810092204683677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4460935529653825091646277 836425411810092204683677)
                    ·
                      rfl

theorem cell23_4886798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 3, 4, 4].length) (baseStart_4886798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4886798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4886798 prefixEnd_4886798 := by exact prefixLift 4886798
  have htrace : WordTrace (prefixWord ++ tailWord_4886798) baseStart_4886798 baseEnd_4886798 := by
    simpa [prefixWord, tailWord_4886798, baseEnd_4886798] using wordTrace_append hprefix tailTrace_4886798
  have hstable : (prefixWord ++ tailWord_4886798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4886798).length < 2 ^ (prefixWord ++ tailWord_4886798).sum := by decide
  have hdescent : baseEnd_4886798 < baseStart_4886798 := by decide
  rcases family_descends (prefixWord ++ tailWord_4886798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4886801 : List Nat := [1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 6]
def baseStart_4886801 : Nat := 118140960795 + 4886801 * 2 ^ 59
def prefixEnd_4886801 : Nat := 4983230072969 + 3 ^ 40 * 4886801 * 2
def baseEnd_4886801 : Nat := 2509277775872240102313517

theorem tailTrace_4886801 : CollatzResearch.WordTrace tailWord_4886801 prefixEnd_4886801 2509277775872240102313517 := by
  unfold tailWord_4886801
  simp only [CollatzResearch.WordTrace]
  refine ⟨178236275168962051010076257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118824183445974700673384171 178236275168962051010076257)
  ·
    refine ⟨133677206376721538257557193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178236275168962051010076257 133677206376721538257557193)
    ·
      refine ⟨100257904782541153693167895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133677206376721538257557193 100257904782541153693167895)
      ·
        refine ⟨150386857173811730539751843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100257904782541153693167895 150386857173811730539751843)
        ·
          refine ⟨225580285760717595809627765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150386857173811730539751843 225580285760717595809627765)
          ·
            refine ⟨21148151790067274607152603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 225580285760717595809627765 21148151790067274607152603)
            ·
              refine ⟨31722227685100911910728905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21148151790067274607152603 31722227685100911910728905)
              ·
                refine ⟨23791670763825683933046679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31722227685100911910728905 23791670763825683933046679)
                ·
                  refine ⟨35687506145738525899570019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23791670763825683933046679 35687506145738525899570019)
                  ·
                    refine ⟨53531259218607788849355029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35687506145738525899570019 53531259218607788849355029)
                    ·
                      refine ⟨2509277775872240102313517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53531259218607788849355029 2509277775872240102313517)
                      ·
                        rfl

theorem cell23_4886801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 6].length) (baseStart_4886801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4886801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4886801 prefixEnd_4886801 := by exact prefixLift 4886801
  have htrace : WordTrace (prefixWord ++ tailWord_4886801) baseStart_4886801 baseEnd_4886801 := by
    simpa [prefixWord, tailWord_4886801, baseEnd_4886801] using wordTrace_append hprefix tailTrace_4886801
  have hstable : (prefixWord ++ tailWord_4886801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4886801).length < 2 ^ (prefixWord ++ tailWord_4886801).sum := by decide
  have hdescent : baseEnd_4886801 < baseStart_4886801 := by decide
  rcases family_descends (prefixWord ++ tailWord_4886801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4886808 : List Nat := [2, 1, 2, 3, 1, 2, 2, 2, 3, 2, 3]
def baseStart_4886808 : Nat := 118140960795 + 4886808 * 2 ^ 59
def prefixEnd_4886808 : Nat := 4983230072969 + 3 ^ 40 * 4886808 * 2
def baseEnd_4886808 : Nat := 2509281370236821574925985

theorem tailTrace_4886808 : CollatzResearch.WordTrace tailWord_4886808 prefixEnd_4886808 2509281370236821574925985 := by
  unfold tailWord_4886808
  simp only [CollatzResearch.WordTrace]
  refine ⟨89118265239968345602790539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118824353653291127470387385 89118265239968345602790539)
  ·
    refine ⟨133677397859952518404185809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89118265239968345602790539 133677397859952518404185809)
    ·
      refine ⟨100258048394964388803139357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133677397859952518404185809 100258048394964388803139357)
      ·
        refine ⟨37596768148111645801177259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100258048394964388803139357 37596768148111645801177259)
        ·
          refine ⟨56395152222167468701765889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37596768148111645801177259 56395152222167468701765889)
          ·
            refine ⟨42296364166625601526324417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56395152222167468701765889 42296364166625601526324417)
            ·
              refine ⟨31722273124969201144743313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42296364166625601526324417 31722273124969201144743313)
              ·
                refine ⟨23791704843726900858557485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31722273124969201144743313 23791704843726900858557485)
                ·
                  refine ⟨8921889316397587821959057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23791704843726900858557485 8921889316397587821959057)
                  ·
                    refine ⟨6691416987298190866469293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8921889316397587821959057 6691416987298190866469293)
                    ·
                      refine ⟨2509281370236821574925985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6691416987298190866469293 2509281370236821574925985)
                      ·
                        rfl

theorem cell23_4886808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 2, 3, 2, 3].length) (baseStart_4886808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4886808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4886808 prefixEnd_4886808 := by exact prefixLift 4886808
  have htrace : WordTrace (prefixWord ++ tailWord_4886808) baseStart_4886808 baseEnd_4886808 := by
    simpa [prefixWord, tailWord_4886808, baseEnd_4886808] using wordTrace_append hprefix tailTrace_4886808
  have hstable : (prefixWord ++ tailWord_4886808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4886808).length < 2 ^ (prefixWord ++ tailWord_4886808).sum := by decide
  have hdescent : baseEnd_4886808 < baseStart_4886808 := by decide
  rcases family_descends (prefixWord ++ tailWord_4886808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4886815 : List Nat := [1, 1, 2, 4, 3, 2, 1, 3, 2, 4]
def baseStart_4886815 : Nat := 118140960795 + 4886815 * 2 ^ 59
def prefixEnd_4886815 : Nat := 4983230072969 + 3 ^ 40 * 4886815 * 2
def baseEnd_4886815 : Nat := 836428321533801015846151

theorem tailTrace_4886815 : CollatzResearch.WordTrace tailWord_4886815 prefixEnd_4886815 836428321533801015846151 := by
  unfold tailWord_4886815
  simp only [CollatzResearch.WordTrace]
  refine ⟨178236785790911331401085899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118824523860607554267390599 178236785790911331401085899)
  ·
    refine ⟨267355178686366997101628849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178236785790911331401085899 267355178686366997101628849)
    ·
      refine ⟨200516384014775247826221637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 267355178686366997101628849 200516384014775247826221637)
      ·
        refine ⟨37596822002770358967416557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 200516384014775247826221637 37596822002770358967416557)
        ·
          refine ⟨14098808251038884612781209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37596822002770358967416557 14098808251038884612781209)
          ·
            refine ⟨10574106188279163459585907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14098808251038884612781209 10574106188279163459585907)
            ·
              refine ⟨15861159282418745189378861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10574106188279163459585907 15861159282418745189378861)
              ·
                refine ⟨5947934730907029446017073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15861159282418745189378861 5947934730907029446017073)
                ·
                  refine ⟨4460951048180272084512805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5947934730907029446017073 4460951048180272084512805)
                  ·
                    refine ⟨836428321533801015846151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4460951048180272084512805 836428321533801015846151)
                    ·
                      rfl

theorem cell23_4886815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 3, 2, 4].length) (baseStart_4886815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4886815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4886815 prefixEnd_4886815 := by exact prefixLift 4886815
  have htrace : WordTrace (prefixWord ++ tailWord_4886815) baseStart_4886815 baseEnd_4886815 := by
    simpa [prefixWord, tailWord_4886815, baseEnd_4886815] using wordTrace_append hprefix tailTrace_4886815
  have hstable : (prefixWord ++ tailWord_4886815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4886815).length < 2 ^ (prefixWord ++ tailWord_4886815).sum := by decide
  have hdescent : baseEnd_4886815 < baseStart_4886815 := by decide
  rcases family_descends (prefixWord ++ tailWord_4886815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4886818 : List Nat := [3, 3, 1, 1, 3, 1, 2, 1, 1, 1, 6]
def baseStart_4886818 : Nat := 118140960795 + 4886818 * 2 ^ 59
def prefixEnd_4886818 : Nat := 4983230072969 + 3 ^ 40 * 4886818 * 2
def baseEnd_4886818 : Nat := 2509286505043366535800939

theorem tailTrace_4886818 : CollatzResearch.WordTrace tailWord_4886818 prefixEnd_4886818 2509286505043366535800939 := by
  unfold tailWord_4886818
  simp only [CollatzResearch.WordTrace]
  refine ⟨44559223802475115728361277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118824596806600308608963405 44559223802475115728361277)
  ·
    refine ⟨16709708925928168398135479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44559223802475115728361277 16709708925928168398135479)
    ·
      refine ⟨25064563388892252597203219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16709708925928168398135479 25064563388892252597203219)
      ·
        refine ⟨37596845083338378895804829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25064563388892252597203219 37596845083338378895804829)
        ·
          refine ⟨14098816906251892085926811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37596845083338378895804829 14098816906251892085926811)
          ·
            refine ⟨21148225359377838128890217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14098816906251892085926811 21148225359377838128890217)
            ·
              refine ⟨15861169019533378596667663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21148225359377838128890217 15861169019533378596667663)
              ·
                refine ⟨23791753529300067895001495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15861169019533378596667663 23791753529300067895001495)
                ·
                  refine ⟨35687630293950101842502243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23791753529300067895001495 35687630293950101842502243)
                  ·
                    refine ⟨53531445440925152763753365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35687630293950101842502243 53531445440925152763753365)
                    ·
                      refine ⟨2509286505043366535800939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53531445440925152763753365 2509286505043366535800939)
                      ·
                        rfl

theorem cell23_4886818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 1, 1, 1, 6].length) (baseStart_4886818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4886818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4886818 prefixEnd_4886818 := by exact prefixLift 4886818
  have htrace : WordTrace (prefixWord ++ tailWord_4886818) baseStart_4886818 baseEnd_4886818 := by
    simpa [prefixWord, tailWord_4886818, baseEnd_4886818] using wordTrace_append hprefix tailTrace_4886818
  have hstable : (prefixWord ++ tailWord_4886818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4886818).length < 2 ^ (prefixWord ++ tailWord_4886818).sum := by decide
  have hdescent : baseEnd_4886818 < baseStart_4886818 := by decide
  rcases family_descends (prefixWord ++ tailWord_4886818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4886842 : List Nat := [3, 1, 1, 1, 4, 3, 3, 1, 1, 2, 3]
def baseStart_4886842 : Nat := 118140960795 + 4886842 * 2 ^ 59
def prefixEnd_4886842 : Nat := 4983230072969 + 3 ^ 40 * 4886842 * 2
def baseEnd_4886842 : Nat := 2509298828579074441900829

theorem tailTrace_4886842 : CollatzResearch.WordTrace tailWord_4886842 prefixEnd_4886842 2509298828579074441900829 := by
  unfold tailWord_4886842
  simp only [CollatzResearch.WordTrace]
  refine ⟨44559442640453378753079695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118825180374542343341545853 44559442640453378753079695)
  ·
    refine ⟨66839163960680068129619543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44559442640453378753079695 66839163960680068129619543)
    ·
      refine ⟨100258745941020102194429315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66839163960680068129619543 100258745941020102194429315)
      ·
        refine ⟨150388118911530153291643973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100258745941020102194429315 150388118911530153291643973)
        ·
          refine ⟨28197772295911903742183245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 150388118911530153291643973 28197772295911903742183245)
          ·
            refine ⟨10574164610966963903318717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28197772295911903742183245 10574164610966963903318717)
            ·
              refine ⟨3965311729112611463744519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10574164610966963903318717 3965311729112611463744519)
              ·
                refine ⟨5947967593668917195616779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3965311729112611463744519 5947967593668917195616779)
                ·
                  refine ⟨8921951390503375793425169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5947967593668917195616779 8921951390503375793425169)
                  ·
                    refine ⟨6691463542877531845068877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8921951390503375793425169 6691463542877531845068877)
                    ·
                      refine ⟨2509298828579074441900829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6691463542877531845068877 2509298828579074441900829)
                      ·
                        rfl

theorem cell23_4886842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 3, 1, 1, 2, 3].length) (baseStart_4886842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4886842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4886842 prefixEnd_4886842 := by exact prefixLift 4886842
  have htrace : WordTrace (prefixWord ++ tailWord_4886842) baseStart_4886842 baseEnd_4886842 := by
    simpa [prefixWord, tailWord_4886842, baseEnd_4886842] using wordTrace_append hprefix tailTrace_4886842
  have hstable : (prefixWord ++ tailWord_4886842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4886842).length < 2 ^ (prefixWord ++ tailWord_4886842).sum := by decide
  have hdescent : baseEnd_4886842 < baseStart_4886842 := by decide
  rcases family_descends (prefixWord ++ tailWord_4886842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4886851 : List Nat := [1, 1, 1, 3, 1, 3, 2, 2, 2, 2, 5]
def baseStart_4886851 : Nat := 118140960795 + 4886851 * 2 ^ 59
def prefixEnd_4886851 : Nat := 4983230072969 + 3 ^ 40 * 4886851 * 2
def baseEnd_4886851 : Nat := 2509303449904964906688287

theorem tailTrace_4886851 : CollatzResearch.WordTrace tailWord_4886851 prefixEnd_4886851 2509303449904964906688287 := by
  unfold tailWord_4886851
  simp only [CollatzResearch.WordTrace]
  refine ⟨178238098818780909549396407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118825399212520606366264271 178238098818780909549396407)
  ·
    refine ⟨267357148228171364324094611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178238098818780909549396407 267357148228171364324094611)
    ·
      refine ⟨401035722342257046486141917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 267357148228171364324094611 401035722342257046486141917)
      ·
        refine ⟨150388395878346392432303219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 401035722342257046486141917 150388395878346392432303219)
        ·
          refine ⟨225582593817519588648454829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150388395878346392432303219 225582593817519588648454829)
          ·
            refine ⟨84593472681569845743170561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 225582593817519588648454829 84593472681569845743170561)
            ·
              refine ⟨63445104511177384307377921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84593472681569845743170561 63445104511177384307377921)
              ·
                refine ⟨47583828383383038230533441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63445104511177384307377921 47583828383383038230533441)
                ·
                  refine ⟨35687871287537278672900081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47583828383383038230533441 35687871287537278672900081)
                  ·
                    refine ⟨26765903465652959004675061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35687871287537278672900081 26765903465652959004675061)
                    ·
                      refine ⟨2509303449904964906688287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26765903465652959004675061 2509303449904964906688287)
                      ·
                        rfl

theorem cell23_4886851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 2, 2, 5].length) (baseStart_4886851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4886851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4886851 prefixEnd_4886851 := by exact prefixLift 4886851
  have htrace : WordTrace (prefixWord ++ tailWord_4886851) baseStart_4886851 baseEnd_4886851 := by
    simpa [prefixWord, tailWord_4886851, baseEnd_4886851] using wordTrace_append hprefix tailTrace_4886851
  have hstable : (prefixWord ++ tailWord_4886851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4886851).length < 2 ^ (prefixWord ++ tailWord_4886851).sum := by decide
  have hdescent : baseEnd_4886851 < baseStart_4886851 := by decide
  rcases family_descends (prefixWord ++ tailWord_4886851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4886865 : List Nat := [1, 2, 2, 1, 4, 2, 1, 2, 3, 3, 2]
def baseStart_4886865 : Nat := 118140960795 + 4886865 * 2 ^ 59
def prefixEnd_4886865 : Nat := 4983230072969 + 3 ^ 40 * 4886865 * 2
def baseEnd_4886865 : Nat := 2509310638634127851913223

theorem tailTrace_4886865 : CollatzResearch.WordTrace tailWord_4886865 prefixEnd_4886865 2509310638634127851913223 := by
  unfold tailWord_4886865
  simp only [CollatzResearch.WordTrace]
  refine ⟨178238609440730189940406049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118825739627153459960270699 178238609440730189940406049)
  ·
    refine ⟨133678957080547642455304537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178238609440730189940406049 133678957080547642455304537)
    ·
      refine ⟨100259217810410731841478403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133678957080547642455304537 100259217810410731841478403)
      ·
        refine ⟨150388826715616097762217605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100259217810410731841478403 150388826715616097762217605)
        ·
          refine ⟨28197905009178018330415801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 150388826715616097762217605 28197905009178018330415801)
          ·
            refine ⟨21148428756883513747811851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28197905009178018330415801 21148428756883513747811851)
            ·
              refine ⟨31722643135325270621717777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21148428756883513747811851 31722643135325270621717777)
              ·
                refine ⟨23791982351493952966288333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31722643135325270621717777 23791982351493952966288333)
                ·
                  refine ⟨8921993381810232362358125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23791982351493952966288333 8921993381810232362358125)
                  ·
                    refine ⟨3345747518178837135884297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8921993381810232362358125 3345747518178837135884297)
                    ·
                      refine ⟨2509310638634127851913223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3345747518178837135884297 2509310638634127851913223)
                      ·
                        rfl

theorem cell23_4886865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 2, 3, 3, 2].length) (baseStart_4886865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4886865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4886865 prefixEnd_4886865 := by exact prefixLift 4886865
  have htrace : WordTrace (prefixWord ++ tailWord_4886865) baseStart_4886865 baseEnd_4886865 := by
    simpa [prefixWord, tailWord_4886865, baseEnd_4886865] using wordTrace_append hprefix tailTrace_4886865
  have hstable : (prefixWord ++ tailWord_4886865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4886865).length < 2 ^ (prefixWord ++ tailWord_4886865).sum := by decide
  have hdescent : baseEnd_4886865 < baseStart_4886865 := by decide
  rcases family_descends (prefixWord ++ tailWord_4886865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4886882 : List Nat := [3, 3, 2, 1, 1, 2, 2, 1, 3, 3, 2]
def baseStart_4886882 : Nat := 118140960795 + 4886882 * 2 ^ 59
def prefixEnd_4886882 : Nat := 4983230072969 + 3 ^ 40 * 4886882 * 2
def baseEnd_4886882 : Nat := 2509319367805254285400645

theorem tailTrace_4886882 : CollatzResearch.WordTrace tailWord_4886882 prefixEnd_4886882 2509319367805254285400645 := by
  unfold tailWord_4886882
  simp only [CollatzResearch.WordTrace]
  refine ⟨44559807370417150460943725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118826152987779067895849933 44559807370417150460943725)
  ·
    refine ⟨16709927763906431422853897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44559807370417150460943725 16709927763906431422853897)
    ·
      refine ⟨12532445822929823567140423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16709927763906431422853897 12532445822929823567140423)
      ·
        refine ⟨18798668734394735350710635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12532445822929823567140423 18798668734394735350710635)
        ·
          refine ⟨28198003101592103026065953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18798668734394735350710635 28198003101592103026065953)
          ·
            refine ⟨21148502326194077269549465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28198003101592103026065953 21148502326194077269549465)
            ·
              refine ⟨15861376744645557952162099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21148502326194077269549465 15861376744645557952162099)
              ·
                refine ⟨23792065116968336928243149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15861376744645557952162099 23792065116968336928243149)
                ·
                  refine ⟨8922024418863126348091181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23792065116968336928243149 8922024418863126348091181)
                  ·
                    refine ⟨3345759157073672380534193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8922024418863126348091181 3345759157073672380534193)
                    ·
                      refine ⟨2509319367805254285400645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3345759157073672380534193 2509319367805254285400645)
                      ·
                        rfl

theorem cell23_4886882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 1, 3, 3, 2].length) (baseStart_4886882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4886882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4886882 prefixEnd_4886882 := by exact prefixLift 4886882
  have htrace : WordTrace (prefixWord ++ tailWord_4886882) baseStart_4886882 baseEnd_4886882 := by
    simpa [prefixWord, tailWord_4886882, baseEnd_4886882] using wordTrace_append hprefix tailTrace_4886882
  have hstable : (prefixWord ++ tailWord_4886882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4886882).length < 2 ^ (prefixWord ++ tailWord_4886882).sum := by decide
  have hdescent : baseEnd_4886882 < baseStart_4886882 := by decide
  rcases family_descends (prefixWord ++ tailWord_4886882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4886911 : List Nat := [1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 7]
def baseStart_4886911 : Nat := 118140960795 + 4886911 * 2 ^ 59
def prefixEnd_4886911 : Nat := 4983230072969 + 3 ^ 40 * 4886911 * 2
def baseEnd_4886911 : Nat := 2509334258744234671938011

theorem tailTrace_4886911 : CollatzResearch.WordTrace tailWord_4886911 prefixEnd_4886911 2509334258744234671938011 := by
  unfold tailWord_4886911
  simp only [CollatzResearch.WordTrace]
  refine ⟨178240287198563539796580587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118826858132375693197720391 178240287198563539796580587)
  ·
    refine ⟨267360430797845309694870881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178240287198563539796580587 267360430797845309694870881)
    ·
      refine ⟨200520323098383982271153161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 267360430797845309694870881 200520323098383982271153161)
      ·
        refine ⟨150390242323787986703364871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 200520323098383982271153161 150390242323787986703364871)
        ·
          refine ⟨225585363485681980055047307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150390242323787986703364871 225585363485681980055047307)
          ·
            refine ⟨338378045228522970082570961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 225585363485681980055047307 338378045228522970082570961)
            ·
              refine ⟨253783533921392227561928221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 338378045228522970082570961 253783533921392227561928221)
              ·
                refine ⟨95168825220522085335723083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 253783533921392227561928221 95168825220522085335723083)
                ·
                  refine ⟨142753237830783128003584625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 95168825220522085335723083 142753237830783128003584625)
                  ·
                    refine ⟨107064928373087346002688469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 142753237830783128003584625 107064928373087346002688469)
                    ·
                      refine ⟨2509334258744234671938011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 107064928373087346002688469 2509334258744234671938011)
                      ·
                        rfl

theorem cell23_4886911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 7].length) (baseStart_4886911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4886911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4886911 prefixEnd_4886911 := by exact prefixLift 4886911
  have htrace : WordTrace (prefixWord ++ tailWord_4886911) baseStart_4886911 baseEnd_4886911 := by
    simpa [prefixWord, tailWord_4886911, baseEnd_4886911] using wordTrace_append hprefix tailTrace_4886911
  have hstable : (prefixWord ++ tailWord_4886911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4886911).length < 2 ^ (prefixWord ++ tailWord_4886911).sum := by decide
  have hdescent : baseEnd_4886911 < baseStart_4886911 := by decide
  rcases family_descends (prefixWord ++ tailWord_4886911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4886948 : List Nat := [2, 3, 1, 2, 1, 1, 4, 1, 1, 7]
def baseStart_4886948 : Nat := 118140960795 + 4886948 * 2 ^ 59
def prefixEnd_4886948 : Nat := 4983230072969 + 3 ^ 40 * 4886948 * 2
def baseEnd_4886948 : Nat := 836451085842817009058447

theorem tailTrace_4886948 : CollatzResearch.WordTrace tailWord_4886948 prefixEnd_4886948 836451085842817009058447 := by
  unfold tailWord_4886948
  simp only [CollatzResearch.WordTrace]
  refine ⟨89120818349714747557838749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118827757799619663410451665 89120818349714747557838749)
  ·
    refine ⟨33420306881143030334189531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89120818349714747557838749 33420306881143030334189531)
    ·
      refine ⟨50130460321714545501284297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33420306881143030334189531 50130460321714545501284297)
      ·
        refine ⟨37597845241285909125963223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50130460321714545501284297 37597845241285909125963223)
        ·
          refine ⟨56396767861928863688944835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37597845241285909125963223 56396767861928863688944835)
          ·
            refine ⟨84595151792893295533417253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56396767861928863688944835 84595151792893295533417253)
            ·
              refine ⟨15861590961167492912515735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 84595151792893295533417253 15861590961167492912515735)
              ·
                refine ⟨23792386441751239368773603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15861590961167492912515735 23792386441751239368773603)
                ·
                  refine ⟨35688579662626859053160405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23792386441751239368773603 35688579662626859053160405)
                  ·
                    refine ⟨836451085842817009058447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35688579662626859053160405 836451085842817009058447)
                    ·
                      rfl

theorem cell23_4886948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 1, 1, 7].length) (baseStart_4886948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4886948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4886948 prefixEnd_4886948 := by exact prefixLift 4886948
  have htrace : WordTrace (prefixWord ++ tailWord_4886948) baseStart_4886948 baseEnd_4886948 := by
    simpa [prefixWord, tailWord_4886948, baseEnd_4886948] using wordTrace_append hprefix tailTrace_4886948
  have hstable : (prefixWord ++ tailWord_4886948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4886948).length < 2 ^ (prefixWord ++ tailWord_4886948).sum := by decide
  have hdescent : baseEnd_4886948 < baseStart_4886948 := by decide
  rcases family_descends (prefixWord ++ tailWord_4886948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4886980 : List Nat := [2, 3, 3, 2, 3, 1, 2, 1, 2, 2, 2]
def baseStart_4886980 : Nat := 118140960795 + 4886980 * 2 ^ 59
def prefixEnd_4886980 : Nat := 4983230072969 + 3 ^ 40 * 4886980 * 2
def baseEnd_4886980 : Nat := 2509369688909394901975195

theorem tailTrace_4886980 : CollatzResearch.WordTrace tailWord_4886980 prefixEnd_4886980 2509369688909394901975195 := by
  unfold tailWord_4886980
  simp only [CollatzResearch.WordTrace]
  refine ⟨89121401917656782290421197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118828535890209043053894929 89121401917656782290421197)
  ·
    refine ⟨33420525719121293358907949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89121401917656782290421197 33420525719121293358907949)
    ·
      refine ⟨12532697144670485009590481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33420525719121293358907949 12532697144670485009590481)
      ·
        refine ⟨9399522858502863757192861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12532697144670485009590481 9399522858502863757192861)
        ·
          refine ⟨3524821071938573908947323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9399522858502863757192861 3524821071938573908947323)
          ·
            refine ⟨5287231607907860863420985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3524821071938573908947323 5287231607907860863420985)
            ·
              refine ⟨3965423705930895647565739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5287231607907860863420985 3965423705930895647565739)
              ·
                refine ⟨5948135558896343471348609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3965423705930895647565739 5948135558896343471348609)
                ·
                  refine ⟨4461101669172257603511457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5948135558896343471348609 4461101669172257603511457)
                  ·
                    refine ⟨3345826251879193202633593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4461101669172257603511457 3345826251879193202633593)
                    ·
                      refine ⟨2509369688909394901975195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3345826251879193202633593 2509369688909394901975195)
                      ·
                        rfl

theorem cell23_4886980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 2, 1, 2, 2, 2].length) (baseStart_4886980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4886980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4886980 prefixEnd_4886980 := by exact prefixLift 4886980
  have htrace : WordTrace (prefixWord ++ tailWord_4886980) baseStart_4886980 baseEnd_4886980 := by
    simpa [prefixWord, tailWord_4886980, baseEnd_4886980] using wordTrace_append hprefix tailTrace_4886980
  have hstable : (prefixWord ++ tailWord_4886980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4886980).length < 2 ^ (prefixWord ++ tailWord_4886980).sum := by decide
  have hdescent : baseEnd_4886980 < baseStart_4886980 := by decide
  rcases family_descends (prefixWord ++ tailWord_4886980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4886985 : List Nat := [1, 2, 1, 1, 2, 1, 4, 3, 2, 4, 2]
def baseStart_4886985 : Nat := 118140960795 + 4886985 * 2 ^ 59
def prefixEnd_4886985 : Nat := 4983230072969 + 3 ^ 40 * 4886985 * 2
def baseEnd_4886985 : Nat := 2509372256312667382412671

theorem tailTrace_4886985 : CollatzResearch.WordTrace tailWord_4886985 prefixEnd_4886985 2509372256312667382412671 := by
  unfold tailWord_4886985
  simp only [CollatzResearch.WordTrace]
  refine ⟨178242986200295450434774409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118828657466863633623182939 178242986200295450434774409)
  ·
    refine ⟨133682239650221587826080807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178242986200295450434774409 133682239650221587826080807)
    ·
      refine ⟨200523359475332381739121211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133682239650221587826080807 200523359475332381739121211)
      ·
        refine ⟨300785039212998572608681817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200523359475332381739121211 300785039212998572608681817)
        ·
          refine ⟨225588779409748929456511363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 300785039212998572608681817 225588779409748929456511363)
          ·
            refine ⟨338383169114623394184767045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 225588779409748929456511363 338383169114623394184767045)
            ·
              refine ⟨63446844208991886409643821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 338383169114623394184767045 63446844208991886409643821)
              ·
                refine ⟨23792566578371957403616433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63446844208991886409643821 23792566578371957403616433)
                ·
                  refine ⟨17844424933778968052712325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23792566578371957403616433 17844424933778968052712325)
                  ·
                    refine ⟨3345829675083556509883561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17844424933778968052712325 3345829675083556509883561)
                    ·
                      refine ⟨2509372256312667382412671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3345829675083556509883561 2509372256312667382412671)
                      ·
                        rfl

theorem cell23_4886985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 3, 2, 4, 2].length) (baseStart_4886985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4886985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4886985 prefixEnd_4886985 := by exact prefixLift 4886985
  have htrace : WordTrace (prefixWord ++ tailWord_4886985) baseStart_4886985 baseEnd_4886985 := by
    simpa [prefixWord, tailWord_4886985, baseEnd_4886985] using wordTrace_append hprefix tailTrace_4886985
  have hstable : (prefixWord ++ tailWord_4886985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4886985).length < 2 ^ (prefixWord ++ tailWord_4886985).sum := by decide
  have hdescent : baseEnd_4886985 < baseStart_4886985 := by decide
  rcases family_descends (prefixWord ++ tailWord_4886985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4887022 : List Nat := [4, 1, 2, 1, 2, 2, 2, 2, 2, 2, 3]
def baseStart_4887022 : Nat := 118140960795 + 4887022 * 2 ^ 59
def prefixEnd_4887022 : Nat := 4983230072969 + 3 ^ 40 * 4887022 * 2
def baseEnd_4887022 : Nat := 2509391255096883737650001

theorem tailTrace_4887022 : CollatzResearch.WordTrace tailWord_4887022 prefixEnd_4887022 2509391255096883737650001 := by
  unfold tailWord_4887022
  simp only [CollatzResearch.WordTrace]
  refine ⟨22280541962645175719233915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118829557134107603835914213 22280541962645175719233915)
  ·
    refine ⟨33420812943967763578850873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22280541962645175719233915 33420812943967763578850873)
    ·
      refine ⟨25065609707975822684138155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33420812943967763578850873 25065609707975822684138155)
      ·
        refine ⟨37598414561963734026207233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25065609707975822684138155 37598414561963734026207233)
        ·
          refine ⟨28198810921472800519655425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37598414561963734026207233 28198810921472800519655425)
          ·
            refine ⟨21149108191104600389741569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28198810921472800519655425 21149108191104600389741569)
            ·
              refine ⟨15861831143328450292306177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21149108191104600389741569 15861831143328450292306177)
              ·
                refine ⟨11896373357496337719229633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15861831143328450292306177 11896373357496337719229633)
                ·
                  refine ⟨8922280018122253289422225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11896373357496337719229633 8922280018122253289422225)
                  ·
                    refine ⟨6691710013591689967066669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8922280018122253289422225 6691710013591689967066669)
                    ·
                      refine ⟨2509391255096883737650001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6691710013591689967066669 2509391255096883737650001)
                      ·
                        rfl

theorem cell23_4887022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 2, 2, 2, 3].length) (baseStart_4887022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4887022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4887022 prefixEnd_4887022 := by exact prefixLift 4887022
  have htrace : WordTrace (prefixWord ++ tailWord_4887022) baseStart_4887022 baseEnd_4887022 := by
    simpa [prefixWord, tailWord_4887022, baseEnd_4887022] using wordTrace_append hprefix tailTrace_4887022
  have hstable : (prefixWord ++ tailWord_4887022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4887022).length < 2 ^ (prefixWord ++ tailWord_4887022).sum := by decide
  have hdescent : baseEnd_4887022 < baseStart_4887022 := by decide
  rcases family_descends (prefixWord ++ tailWord_4887022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4887025 : List Nat := [1, 2, 2, 2, 3, 1, 4, 2, 6]
def baseStart_4887025 : Nat := 118140960795 + 4887025 * 2 ^ 59
def prefixEnd_4887025 : Nat := 4983230072969 + 3 ^ 40 * 4887025 * 2
def baseEnd_4887025 : Nat := 278821421726538580656943

theorem tailTrace_4887025 : CollatzResearch.WordTrace tailWord_4887025 prefixEnd_4887025 278821421726538580656943 := by
  unfold tailWord_4887025
  simp only [CollatzResearch.WordTrace]
  refine ⟨178244445120150537266230529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118829630080100358177487019 178244445120150537266230529)
  ·
    refine ⟨133683333840112902949672897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178244445120150537266230529 133683333840112902949672897)
    ·
      refine ⟨100262500380084677212254673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133683333840112902949672897 100262500380084677212254673)
      ·
        refine ⟨75196875285063507909191005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100262500380084677212254673 75196875285063507909191005)
        ·
          refine ⟨28198828231898815465946627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75196875285063507909191005 28198828231898815465946627)
          ·
            refine ⟨42298242347848223198919941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28198828231898815465946627 42298242347848223198919941)
            ·
              refine ⟨7930920440221541849797489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42298242347848223198919941 7930920440221541849797489)
              ·
                refine ⟨5948190330166156387348117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7930920440221541849797489 5948190330166156387348117)
                ·
                  refine ⟨278821421726538580656943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5948190330166156387348117 278821421726538580656943)
                  ·
                    rfl

theorem cell23_4887025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 4, 2, 6].length) (baseStart_4887025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4887025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4887025 prefixEnd_4887025 := by exact prefixLift 4887025
  have htrace : WordTrace (prefixWord ++ tailWord_4887025) baseStart_4887025 baseEnd_4887025 := by
    simpa [prefixWord, tailWord_4887025, baseEnd_4887025] using wordTrace_append hprefix tailTrace_4887025
  have hstable : (prefixWord ++ tailWord_4887025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4887025).length < 2 ^ (prefixWord ++ tailWord_4887025).sum := by decide
  have hdescent : baseEnd_4887025 < baseStart_4887025 := by decide
  rcases family_descends (prefixWord ++ tailWord_4887025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4887046 : List Nat := [6, 2, 1, 1, 1, 1, 1, 1, 5, 4]
def baseStart_4887046 : Nat := 118140960795 + 4887046 * 2 ^ 59
def prefixEnd_4887046 : Nat := 4983230072969 + 3 ^ 40 * 4887046 * 2
def baseEnd_4887046 : Nat := 836467859544197214583297

theorem tailTrace_4887046 : CollatzResearch.WordTrace tailWord_4887046 prefixEnd_4887046 836467859544197214583297 := by
  unfold tailWord_4887046
  simp only [CollatzResearch.WordTrace]
  refine ⟨5570162845408576807898281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 118830140702049638568496661 5570162845408576807898281)
  ·
    refine ⟨4177622134056432605923711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5570162845408576807898281 4177622134056432605923711)
    ·
      refine ⟨6266433201084648908885567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4177622134056432605923711 6266433201084648908885567)
      ·
        refine ⟨9399649801626973363328351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6266433201084648908885567 9399649801626973363328351)
        ·
          refine ⟨14099474702440460044992527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9399649801626973363328351 14099474702440460044992527)
          ·
            refine ⟨21149212053660690067488791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14099474702440460044992527 21149212053660690067488791)
            ·
              refine ⟨31723818080491035101233187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21149212053660690067488791 31723818080491035101233187)
              ·
                refine ⟨47585727120736552651849781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31723818080491035101233187 47585727120736552651849781)
                ·
                  refine ⟨4461161917569051811110917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47585727120736552651849781 4461161917569051811110917)
                  ·
                    refine ⟨836467859544197214583297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4461161917569051811110917 836467859544197214583297)
                    ·
                      rfl

theorem cell23_4887046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_4887046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4887046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4887046 prefixEnd_4887046 := by exact prefixLift 4887046
  have htrace : WordTrace (prefixWord ++ tailWord_4887046) baseStart_4887046 baseEnd_4887046 := by
    simpa [prefixWord, tailWord_4887046, baseEnd_4887046] using wordTrace_append hprefix tailTrace_4887046
  have hstable : (prefixWord ++ tailWord_4887046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4887046).length < 2 ^ (prefixWord ++ tailWord_4887046).sum := by decide
  have hdescent : baseEnd_4887046 < baseStart_4887046 := by decide
  rcases family_descends (prefixWord ++ tailWord_4887046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4887048 : List Nat := [2, 1, 3, 2, 1, 1, 1, 1, 1, 3, 7]
def baseStart_4887048 : Nat := 118140960795 + 4887048 * 2 ^ 59
def prefixEnd_4887048 : Nat := 4983230072969 + 3 ^ 40 * 4887048 * 2
def baseEnd_4887048 : Nat := 2509404605593900635924881

theorem tailTrace_4887048 : CollatzResearch.WordTrace tailWord_4887048 prefixEnd_4887048 2509404605593900635924881 := by
  unfold tailWord_4887048
  simp only [CollatzResearch.WordTrace]
  refine ⟨89122641999533606097158899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118830189332711474796211865 89122641999533606097158899)
  ·
    refine ⟨133683962999300409145738349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89122641999533606097158899 133683962999300409145738349)
    ·
      refine ⟨50131486124737653429651881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133683962999300409145738349 50131486124737653429651881)
      ·
        refine ⟨37598614593553240072238911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50131486124737653429651881 37598614593553240072238911)
        ·
          refine ⟨56397921890329860108358367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37598614593553240072238911 56397921890329860108358367)
          ·
            refine ⟨84596882835494790162537551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56397921890329860108358367 84596882835494790162537551)
            ·
              refine ⟨126895324253242185243806327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84596882835494790162537551 126895324253242185243806327)
              ·
                refine ⟨190342986379863277865709491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126895324253242185243806327 190342986379863277865709491)
                ·
                  refine ⟨285514479569794916798564237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 190342986379863277865709491 285514479569794916798564237)
                  ·
                    refine ⟨107067929838673093799461589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 285514479569794916798564237 107067929838673093799461589)
                    ·
                      refine ⟨2509404605593900635924881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 107067929838673093799461589 2509404605593900635924881)
                      ·
                        rfl

theorem cell23_4887048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 1, 3, 7].length) (baseStart_4887048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4887048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4887048 prefixEnd_4887048 := by exact prefixLift 4887048
  have htrace : WordTrace (prefixWord ++ tailWord_4887048) baseStart_4887048 baseEnd_4887048 := by
    simpa [prefixWord, tailWord_4887048, baseEnd_4887048] using wordTrace_append hprefix tailTrace_4887048
  have hstable : (prefixWord ++ tailWord_4887048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4887048).length < 2 ^ (prefixWord ++ tailWord_4887048).sum := by decide
  have hdescent : baseEnd_4887048 < baseStart_4887048 := by decide
  rcases family_descends (prefixWord ++ tailWord_4887048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4887052 : List Nat := [2, 2, 1, 2, 4, 1, 1, 1, 5, 1, 3]
def baseStart_4887052 : Nat := 118140960795 + 4887052 * 2 ^ 59
def prefixEnd_4887052 : Nat := 4983230072969 + 3 ^ 40 * 4887052 * 2
def baseEnd_4887052 : Nat := 2509406659516518620274863

theorem tailTrace_4887052 : CollatzResearch.WordTrace tailWord_4887052 prefixEnd_4887052 2509406659516518620274863 := by
  unfold tailWord_4887052
  simp only [CollatzResearch.WordTrace]
  refine ⟨89122714945526360438731705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118830286594035147251642273 89122714945526360438731705)
  ·
    refine ⟨66842036209144770329048779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89122714945526360438731705 66842036209144770329048779)
    ·
      refine ⟨100263054313717155493573169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66842036209144770329048779 100263054313717155493573169)
      ·
        refine ⟨75197290735287866620179877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100263054313717155493573169 75197290735287866620179877)
        ·
          refine ⟨14099492012866474991283727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75197290735287866620179877 14099492012866474991283727)
          ·
            refine ⟨21149238019299712486925591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14099492012866474991283727 21149238019299712486925591)
            ·
              refine ⟨31723857028949568730388387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21149238019299712486925591 31723857028949568730388387)
              ·
                refine ⟨47585785543424353095582581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31723857028949568730388387 47585785543424353095582581)
                ·
                  refine ⟨4461167394696033102710867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47585785543424353095582581 4461167394696033102710867)
                  ·
                    refine ⟨6691751092044049654066301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4461167394696033102710867 6691751092044049654066301)
                    ·
                      refine ⟨2509406659516518620274863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6691751092044049654066301 2509406659516518620274863)
                      ·
                        rfl

theorem cell23_4887052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 1, 5, 1, 3].length) (baseStart_4887052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4887052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4887052 prefixEnd_4887052 := by exact prefixLift 4887052
  have htrace : WordTrace (prefixWord ++ tailWord_4887052) baseStart_4887052 baseEnd_4887052 := by
    simpa [prefixWord, tailWord_4887052, baseEnd_4887052] using wordTrace_append hprefix tailTrace_4887052
  have hstable : (prefixWord ++ tailWord_4887052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4887052).length < 2 ^ (prefixWord ++ tailWord_4887052).sum := by decide
  have hdescent : baseEnd_4887052 < baseStart_4887052 := by decide
  rcases family_descends (prefixWord ++ tailWord_4887052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4887076 : List Nat := [2, 3, 1, 5, 2, 1, 1, 2, 6]
def baseStart_4887076 : Nat := 118140960795 + 4887076 * 2 ^ 59
def prefixEnd_4887076 : Nat := 4983230072969 + 3 ^ 40 * 4887076 * 2
def baseEnd_4887076 : Nat := 278824331450247391819417

theorem tailTrace_4887076 : CollatzResearch.WordTrace tailWord_4887076 prefixEnd_4887076 278824331450247391819417 := by
  unfold tailWord_4887076
  simp only [CollatzResearch.WordTrace]
  refine ⟨89123152621482886488168541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118830870161977181984224721 89123152621482886488168541)
  ·
    refine ⟨33421182233056082433063203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89123152621482886488168541 33421182233056082433063203)
    ·
      refine ⟨50131773349584123649594805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33421182233056082433063203 50131773349584123649594805)
      ·
        refine ⟨4699853751523511592149513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 50131773349584123649594805 4699853751523511592149513)
        ·
          refine ⟨3524890313642633694112135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4699853751523511592149513 3524890313642633694112135)
          ·
            refine ⟨5287335470463950541168203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3524890313642633694112135 5287335470463950541168203)
            ·
              refine ⟨7931003205695925811752305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5287335470463950541168203 7931003205695925811752305)
              ·
                refine ⟨5948252404271944358814229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7931003205695925811752305 5948252404271944358814229)
                ·
                  refine ⟨278824331450247391819417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5948252404271944358814229 278824331450247391819417)
                  ·
                    rfl

theorem cell23_4887076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 1, 2, 6].length) (baseStart_4887076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4887076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4887076 prefixEnd_4887076 := by exact prefixLift 4887076
  have htrace : WordTrace (prefixWord ++ tailWord_4887076) baseStart_4887076 baseEnd_4887076 := by
    simpa [prefixWord, tailWord_4887076, baseEnd_4887076] using wordTrace_append hprefix tailTrace_4887076
  have hstable : (prefixWord ++ tailWord_4887076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4887076).length < 2 ^ (prefixWord ++ tailWord_4887076).sum := by decide
  have hdescent : baseEnd_4887076 < baseStart_4887076 := by decide
  rcases family_descends (prefixWord ++ tailWord_4887076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4887086 : List Nat := [4, 1, 3, 1, 3, 1, 2, 1, 3, 1, 3]
def baseStart_4887086 : Nat := 118140960795 + 4887086 * 2 ^ 59
def prefixEnd_4887086 : Nat := 4983230072969 + 3 ^ 40 * 4887086 * 2
def baseEnd_4887086 : Nat := 2509424117858771487249707

theorem tailTrace_4887086 : CollatzResearch.WordTrace tailWord_4887086 prefixEnd_4887086 2509424117858771487249707 := by
  unfold tailWord_4887086
  simp only [CollatzResearch.WordTrace]
  refine ⟨22280833746616193085525139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118831113315286363122800741 22280833746616193085525139)
  ·
    refine ⟨33421250619924289628287709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22280833746616193085525139 33421250619924289628287709)
    ·
      refine ⟨12532968982471608610607891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33421250619924289628287709 12532968982471608610607891)
      ·
        refine ⟨18799453473707412915911837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12532968982471608610607891 18799453473707412915911837)
        ·
          refine ⟨7049795052640279843466939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18799453473707412915911837 7049795052640279843466939)
          ·
            refine ⟨10574692578960419765200409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7049795052640279843466939 10574692578960419765200409)
            ·
              refine ⟨7931019434220314823900307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10574692578960419765200409 7931019434220314823900307)
              ·
                refine ⟨11896529151330472235850461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7931019434220314823900307 11896529151330472235850461)
                ·
                  refine ⟨4461198431748927088443923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11896529151330472235850461 4461198431748927088443923)
                  ·
                    refine ⟨6691797647623390632665885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4461198431748927088443923 6691797647623390632665885)
                    ·
                      refine ⟨2509424117858771487249707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6691797647623390632665885 2509424117858771487249707)
                      ·
                        rfl

theorem cell23_4887086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 2, 1, 3, 1, 3].length) (baseStart_4887086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4887086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4887086 prefixEnd_4887086 := by exact prefixLift 4887086
  have htrace : WordTrace (prefixWord ++ tailWord_4887086) baseStart_4887086 baseEnd_4887086 := by
    simpa [prefixWord, tailWord_4887086, baseEnd_4887086] using wordTrace_append hprefix tailTrace_4887086
  have hstable : (prefixWord ++ tailWord_4887086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4887086).length < 2 ^ (prefixWord ++ tailWord_4887086).sum := by decide
  have hdescent : baseEnd_4887086 < baseStart_4887086 := by decide
  rcases family_descends (prefixWord ++ tailWord_4887086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4887095 : List Nat := [1, 1, 3, 1, 2, 3, 3, 2, 1, 1, 5]
def baseStart_4887095 : Nat := 118140960795 + 4887095 * 2 ^ 59
def prefixEnd_4887095 : Nat := 4983230072969 + 3 ^ 40 * 4887095 * 2
def baseEnd_4887095 : Nat := 2509428739184661952037165

theorem tailTrace_4887095 : CollatzResearch.WordTrace tailWord_4887095 prefixEnd_4887095 2509428739184661952037165 := by
  unfold tailWord_4887095
  simp only [CollatzResearch.WordTrace]
  refine ⟨178246998229896939221278739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118831332153264626147519159 178246998229896939221278739)
  ·
    refine ⟨267370497344845408831918109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178246998229896939221278739 267370497344845408831918109)
    ·
      refine ⟨100263936504317028311969291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 267370497344845408831918109 100263936504317028311969291)
      ·
        refine ⟨150395904756475542467953937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100263936504317028311969291 150395904756475542467953937)
        ·
          refine ⟨112796928567356656850965453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150395904756475542467953937 112796928567356656850965453)
          ·
            refine ⟨42298848212758746319112045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 112796928567356656850965453 42298848212758746319112045)
            ·
              refine ⟨15862068079784529869667017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42298848212758746319112045 15862068079784529869667017)
              ·
                refine ⟨11896551059838397402250263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15862068079784529869667017 11896551059838397402250263)
                ·
                  refine ⟨17844826589757596103375395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11896551059838397402250263 17844826589757596103375395)
                  ·
                    refine ⟨26767239884636394155063093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17844826589757596103375395 26767239884636394155063093)
                    ·
                      refine ⟨2509428739184661952037165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26767239884636394155063093 2509428739184661952037165)
                      ·
                        rfl

theorem cell23_4887095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 2, 1, 1, 5].length) (baseStart_4887095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4887095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4887095 prefixEnd_4887095 := by exact prefixLift 4887095
  have htrace : WordTrace (prefixWord ++ tailWord_4887095) baseStart_4887095 baseEnd_4887095 := by
    simpa [prefixWord, tailWord_4887095, baseEnd_4887095] using wordTrace_append hprefix tailTrace_4887095
  have hstable : (prefixWord ++ tailWord_4887095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4887095).length < 2 ^ (prefixWord ++ tailWord_4887095).sum := by decide
  have hdescent : baseEnd_4887095 < baseStart_4887095 := by decide
  rcases family_descends (prefixWord ++ tailWord_4887095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4887109 : List Nat := [1, 3, 1, 1, 1, 5, 2, 2, 3, 2, 2]
def baseStart_4887109 : Nat := 118140960795 + 4887109 * 2 ^ 59
def prefixEnd_4887109 : Nat := 4983230072969 + 3 ^ 40 * 4887109 * 2
def baseEnd_4887109 : Nat := 2509435927913824897262101

theorem tailTrace_4887109 : CollatzResearch.WordTrace tailWord_4887109 prefixEnd_4887109 2509435927913824897262101 := by
  unfold tailWord_4887109
  simp only [CollatzResearch.WordTrace]
  refine ⟨178247508851846219612288381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118831672567897479741525587 178247508851846219612288381)
  ·
    refine ⟨66842815819442332354608143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 178247508851846219612288381 66842815819442332354608143)
    ·
      refine ⟨100264223729163498531912215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66842815819442332354608143 100264223729163498531912215)
      ·
        refine ⟨150396335593745247797868323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100264223729163498531912215 150396335593745247797868323)
        ·
          refine ⟨225594503390617871696802485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150396335593745247797868323 225594503390617871696802485)
          ·
            refine ⟨21149484692870425471575233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 225594503390617871696802485 21149484692870425471575233)
            ·
              refine ⟨15862113519652819103681425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21149484692870425471575233 15862113519652819103681425)
              ·
                refine ⟨11896585139739614327761069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15862113519652819103681425 11896585139739614327761069)
                ·
                  refine ⟨4461219427402355372910401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11896585139739614327761069 4461219427402355372910401)
                  ·
                    refine ⟨3345914570551766529682801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4461219427402355372910401 3345914570551766529682801)
                    ·
                      refine ⟨2509435927913824897262101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3345914570551766529682801 2509435927913824897262101)
                      ·
                        rfl

theorem cell23_4887109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 2, 3, 2, 2].length) (baseStart_4887109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4887109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4887109 prefixEnd_4887109 := by exact prefixLift 4887109
  have htrace : WordTrace (prefixWord ++ tailWord_4887109) baseStart_4887109 baseEnd_4887109 := by
    simpa [prefixWord, tailWord_4887109, baseEnd_4887109] using wordTrace_append hprefix tailTrace_4887109
  have hstable : (prefixWord ++ tailWord_4887109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4887109).length < 2 ^ (prefixWord ++ tailWord_4887109).sum := by decide
  have hdescent : baseEnd_4887109 < baseStart_4887109 := by decide
  rcases family_descends (prefixWord ++ tailWord_4887109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4887115 : List Nat := [1, 1, 1, 1, 3, 1, 8, 7]
def baseStart_4887115 : Nat := 118140960795 + 4887115 * 2 ^ 59
def prefixEnd_4887115 : Nat := 4983230072969 + 3 ^ 40 * 4887115 * 2
def baseEnd_4887115 : Nat := 92942185511027847177299

theorem tailTrace_4887115 : CollatzResearch.WordTrace tailWord_4887115 prefixEnd_4887115 92942185511027847177299 := by
  unfold tailWord_4887115
  simp only [CollatzResearch.WordTrace]
  refine ⟨178247727689824482637006799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118831818459882988424671199 178247727689824482637006799)
  ·
    refine ⟨267371591534736723955510199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178247727689824482637006799 267371591534736723955510199)
    ·
      refine ⟨401057387302105085933265299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 267371591534736723955510199 401057387302105085933265299)
      ·
        refine ⟨601586080953157628899897949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 401057387302105085933265299 601586080953157628899897949)
        ·
          refine ⟨225594780357434110837461731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 601586080953157628899897949 225594780357434110837461731)
          ·
            refine ⟨338392170536151166256192597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 225594780357434110837461731 338392170536151166256192597)
            ·
              refine ⟨3965533248470521479564757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 338392170536151166256192597 3965533248470521479564757)
              ·
                refine ⟨92942185511027847177299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3965533248470521479564757 92942185511027847177299)
                ·
                  rfl

theorem cell23_4887115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 8, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 8, 7].length) (baseStart_4887115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4887115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4887115 prefixEnd_4887115 := by exact prefixLift 4887115
  have htrace : WordTrace (prefixWord ++ tailWord_4887115) baseStart_4887115 baseEnd_4887115 := by
    simpa [prefixWord, tailWord_4887115, baseEnd_4887115] using wordTrace_append hprefix tailTrace_4887115
  have hstable : (prefixWord ++ tailWord_4887115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4887115).length < 2 ^ (prefixWord ++ tailWord_4887115).sum := by decide
  have hdescent : baseEnd_4887115 < baseStart_4887115 := by decide
  rcases family_descends (prefixWord ++ tailWord_4887115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4887132 : List Nat := [2, 2, 4, 1, 3, 2, 9]
def baseStart_4887132 : Nat := 118140960795 + 4887132 * 2 ^ 59
def prefixEnd_4887132 : Nat := 4983230072969 + 3 ^ 40 * 4887132 * 2
def baseEnd_4887132 : Nat := 30980836271220719842895

theorem tailTrace_4887132 : CollatzResearch.WordTrace tailWord_4887132 prefixEnd_4887132 30980836271220719842895 := by
  unfold tailWord_4887132
  simp only [CollatzResearch.WordTrace]
  refine ⟨89124173865381447270187825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118832231820508596360250433 89124173865381447270187825)
  ·
    refine ⟨66843130399036085452640869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89124173865381447270187825 66843130399036085452640869)
    ·
      refine ⟨12533086949819266022370163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66843130399036085452640869 12533086949819266022370163)
      ·
        refine ⟨18799630424728899033555245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12533086949819266022370163 18799630424728899033555245)
        ·
          refine ⟨7049861409273337137583217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18799630424728899033555245 7049861409273337137583217)
          ·
            refine ⟨5287396056955002853187413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7049861409273337137583217 5287396056955002853187413)
            ·
              refine ⟨30980836271220719842895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5287396056955002853187413 30980836271220719842895)
              ·
                rfl

theorem cell23_4887132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 9].length) (baseStart_4887132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4887132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4887132 prefixEnd_4887132 := by exact prefixLift 4887132
  have htrace : WordTrace (prefixWord ++ tailWord_4887132) baseStart_4887132 baseEnd_4887132 := by
    simpa [prefixWord, tailWord_4887132, baseEnd_4887132] using wordTrace_append hprefix tailTrace_4887132
  have hstable : (prefixWord ++ tailWord_4887132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4887132).length < 2 ^ (prefixWord ++ tailWord_4887132).sum := by decide
  have hdescent : baseEnd_4887132 < baseStart_4887132 := by decide
  rcases family_descends (prefixWord ++ tailWord_4887132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4887169 : List Nat := [1, 2, 4, 2, 1, 1, 3, 1, 3, 3, 2]
def baseStart_4887169 : Nat := 118140960795 + 4887169 * 2 ^ 59
def prefixEnd_4887169 : Nat := 4983230072969 + 3 ^ 40 * 4887169 * 2
def baseEnd_4887169 : Nat := 2509466736753094662511825

theorem tailTrace_4887169 : CollatzResearch.WordTrace tailWord_4887169 prefixEnd_4887169 2509466736753094662511825 := by
  unfold tailWord_4887169
  simp only [CollatzResearch.WordTrace]
  refine ⟨178249697231628849859472561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118833131487752566572981707 178249697231628849859472561)
  ·
    refine ⟨133687272923721637394604421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178249697231628849859472561 133687272923721637394604421)
    ·
      refine ⟨25066363673197807011488329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 133687272923721637394604421 25066363673197807011488329)
      ·
        refine ⟨18799772754898355258616247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25066363673197807011488329 18799772754898355258616247)
        ·
          refine ⟨28199659132347532887924371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18799772754898355258616247 28199659132347532887924371)
          ·
            refine ⟨42299488698521299331886557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28199659132347532887924371 42299488698521299331886557)
            ·
              refine ⟨15862308261945487249457459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42299488698521299331886557 15862308261945487249457459)
              ·
                refine ⟨23793462392918230874186189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15862308261945487249457459 23793462392918230874186189)
                ·
                  refine ⟨8922548397344336577819821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23793462392918230874186189 8922548397344336577819821)
                  ·
                    refine ⟨3345955649004126216682433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8922548397344336577819821 3345955649004126216682433)
                    ·
                      refine ⟨2509466736753094662511825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3345955649004126216682433 2509466736753094662511825)
                      ·
                        rfl

theorem cell23_4887169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 1, 3, 3, 2].length) (baseStart_4887169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4887169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4887169 prefixEnd_4887169 := by exact prefixLift 4887169
  have htrace : WordTrace (prefixWord ++ tailWord_4887169) baseStart_4887169 baseEnd_4887169 := by
    simpa [prefixWord, tailWord_4887169, baseEnd_4887169] using wordTrace_append hprefix tailTrace_4887169
  have hstable : (prefixWord ++ tailWord_4887169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4887169).length < 2 ^ (prefixWord ++ tailWord_4887169).sum := by decide
  have hdescent : baseEnd_4887169 < baseStart_4887169 := by decide
  rcases family_descends (prefixWord ++ tailWord_4887169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4887194 : List Nat := [3, 1, 1, 6, 2, 1, 2, 2, 1, 2, 2]
def baseStart_4887194 : Nat := 118140960795 + 4887194 * 2 ^ 59
def prefixEnd_4887194 : Nat := 4983230072969 + 3 ^ 40 * 4887194 * 2
def baseEnd_4887194 : Nat := 2509479573769457064699211

theorem tailTrace_4887194 : CollatzResearch.WordTrace tailWord_4887194 prefixEnd_4887194 2509479573769457064699211 := by
  unfold tailWord_4887194
  simp only [CollatzResearch.WordTrace]
  refine ⟨44562652264134569782283159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118833739371025519419421757 44562652264134569782283159)
  ·
    refine ⟨66843978396201854673424739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44562652264134569782283159 66843978396201854673424739)
    ·
      refine ⟨100265967594302782010137109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66843978396201854673424739 100265967594302782010137109)
      ·
        refine ⟨4699967230982942906725177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 100265967594302782010137109 4699967230982942906725177)
        ·
          refine ⟨3524975423237207180043883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4699967230982942906725177 3524975423237207180043883)
          ·
            refine ⟨5287463134855810770065825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3524975423237207180043883 5287463134855810770065825)
            ·
              refine ⟨3965597351141858077549369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5287463134855810770065825 3965597351141858077549369)
              ·
                refine ⟨2974198013356393558162027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3965597351141858077549369 2974198013356393558162027)
                ·
                  refine ⟨4461297020034590337243041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2974198013356393558162027 4461297020034590337243041)
                  ·
                    refine ⟨3345972765025942752932281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4461297020034590337243041 3345972765025942752932281)
                    ·
                      refine ⟨2509479573769457064699211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3345972765025942752932281 2509479573769457064699211)
                      ·
                        rfl

theorem cell23_4887194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_4887194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4887194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4887194 prefixEnd_4887194 := by exact prefixLift 4887194
  have htrace : WordTrace (prefixWord ++ tailWord_4887194) baseStart_4887194 baseEnd_4887194 := by
    simpa [prefixWord, tailWord_4887194, baseEnd_4887194] using wordTrace_append hprefix tailTrace_4887194
  have hstable : (prefixWord ++ tailWord_4887194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4887194).length < 2 ^ (prefixWord ++ tailWord_4887194).sum := by decide
  have hdescent : baseEnd_4887194 < baseStart_4887194 := by decide
  rcases family_descends (prefixWord ++ tailWord_4887194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4887205 : List Nat := [1, 3, 1, 2, 1, 2, 1, 5, 7]
def baseStart_4887205 : Nat := 118140960795 + 4887205 * 2 ^ 59
def prefixEnd_4887205 : Nat := 4983230072969 + 3 ^ 40 * 4887205 * 2
def baseEnd_4887205 : Nat := 278831691339628502406851

theorem tailTrace_4887205 : CollatzResearch.WordTrace tailWord_4887205 prefixEnd_4887205 278831691339628502406851 := by
  unfold tailWord_4887205
  simp only [CollatzResearch.WordTrace]
  refine ⟨178251010259498428007783069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118834006839665618671855379 178251010259498428007783069)
  ·
    refine ⟨66844128847311910502918651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 178251010259498428007783069 66844128847311910502918651)
    ·
      refine ⟨100266193270967865754377977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66844128847311910502918651 100266193270967865754377977)
      ·
        refine ⟨75199644953225899315783483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100266193270967865754377977 75199644953225899315783483)
        ·
          refine ⟨112799467429838848973675225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75199644953225899315783483 112799467429838848973675225)
          ·
            refine ⟨84599600572379136730256419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112799467429838848973675225 84599600572379136730256419)
            ·
              refine ⟨126899400858568705095384629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84599600572379136730256419 126899400858568705095384629)
              ·
                refine ⟨11896818830490816102692309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 126899400858568705095384629 11896818830490816102692309)
                ·
                  refine ⟨278831691339628502406851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11896818830490816102692309 278831691339628502406851)
                  ·
                    rfl

theorem cell23_4887205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 5, 7].length) (baseStart_4887205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4887205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4887205 prefixEnd_4887205 := by exact prefixLift 4887205
  have htrace : WordTrace (prefixWord ++ tailWord_4887205) baseStart_4887205 baseEnd_4887205 := by
    simpa [prefixWord, tailWord_4887205, baseEnd_4887205] using wordTrace_append hprefix tailTrace_4887205
  have hstable : (prefixWord ++ tailWord_4887205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4887205).length < 2 ^ (prefixWord ++ tailWord_4887205).sum := by decide
  have hdescent : baseEnd_4887205 < baseStart_4887205 := by decide
  rcases family_descends (prefixWord ++ tailWord_4887205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4887250 : List Nat := [3, 2, 2, 2, 3, 2, 1, 2, 2, 2, 2]
def baseStart_4887250 : Nat := 118140960795 + 4887250 * 2 ^ 59
def prefixEnd_4887250 : Nat := 4983230072969 + 3 ^ 40 * 4887250 * 2
def baseEnd_4887250 : Nat := 2509508328686108845598953

theorem tailTrace_4887250 : CollatzResearch.WordTrace tailWord_4887250 prefixEnd_4887250 2509508328686108845598953 := by
  unfold tailWord_4887250
  simp only [CollatzResearch.WordTrace]
  refine ⟨44563162886083850173292801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118835101029556933795447469 44563162886083850173292801)
  ·
    refine ⟨33422372164562887629969601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44563162886083850173292801 33422372164562887629969601)
    ·
      refine ⟨25066779123422165722477201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33422372164562887629969601 25066779123422165722477201)
      ·
        refine ⟨18800084342566624291857901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25066779123422165722477201 18800084342566624291857901)
        ·
          refine ⟨7050031628462484109446713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18800084342566624291857901 7050031628462484109446713)
          ·
            refine ⟨5287523721346863082085035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7050031628462484109446713 5287523721346863082085035)
            ·
              refine ⟨7931285582020294623127553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5287523721346863082085035 7931285582020294623127553)
              ·
                refine ⟨5948464186515220967345665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7931285582020294623127553 5948464186515220967345665)
                ·
                  refine ⟨4461348139886415725509249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5948464186515220967345665 4461348139886415725509249)
                  ·
                    refine ⟨3346011104914811794131937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4461348139886415725509249 3346011104914811794131937)
                    ·
                      refine ⟨2509508328686108845598953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3346011104914811794131937 2509508328686108845598953)
                      ·
                        rfl

theorem cell23_4887250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 1, 2, 2, 2, 2].length) (baseStart_4887250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4887250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4887250 prefixEnd_4887250 := by exact prefixLift 4887250
  have htrace : WordTrace (prefixWord ++ tailWord_4887250) baseStart_4887250 baseEnd_4887250 := by
    simpa [prefixWord, tailWord_4887250, baseEnd_4887250] using wordTrace_append hprefix tailTrace_4887250
  have hstable : (prefixWord ++ tailWord_4887250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4887250).length < 2 ^ (prefixWord ++ tailWord_4887250).sum := by decide
  have hdescent : baseEnd_4887250 < baseStart_4887250 := by decide
  rcases family_descends (prefixWord ++ tailWord_4887250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4887409 : List Nat := [1, 2, 2, 2, 1, 4, 2, 2, 1, 2, 4]
def baseStart_4887409 : Nat := 118140960795 + 4887409 * 2 ^ 59
def prefixEnd_4887409 : Nat := 4983230072969 + 3 ^ 40 * 4887409 * 2
def baseEnd_4887409 : Nat := 2509589972110173723510721

theorem tailTrace_4887409 : CollatzResearch.WordTrace tailWord_4887409 prefixEnd_4887409 2509589972110173723510721 := by
  unfold tailWord_4887409
  simp only [CollatzResearch.WordTrace]
  refine ⟨178258450750759370848209281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118838967167172913898806187 178258450750759370848209281)
  ·
    refine ⟨133693838063069528136156961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178258450750759370848209281 133693838063069528136156961)
    ·
      refine ⟨100270378547302146102117721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133693838063069528136156961 100270378547302146102117721)
      ·
        refine ⟨75202783910476609576588291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100270378547302146102117721 75202783910476609576588291)
        ·
          refine ⟨112804175865714914364882437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75202783910476609576588291 112804175865714914364882437)
          ·
            refine ⟨21150782974821546443415457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 112804175865714914364882437 21150782974821546443415457)
            ·
              refine ⟨15863087231116159832561593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21150782974821546443415457 15863087231116159832561593)
              ·
                refine ⟨11897315423337119874421195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15863087231116159832561593 11897315423337119874421195)
                ·
                  refine ⟨17845973135005679811631793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11897315423337119874421195 17845973135005679811631793)
                  ·
                    refine ⟨13384479851254259858723845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17845973135005679811631793 13384479851254259858723845)
                    ·
                      refine ⟨2509589972110173723510721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13384479851254259858723845 2509589972110173723510721)
                      ·
                        rfl

theorem cell23_4887409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 2, 1, 2, 4].length) (baseStart_4887409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4887409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4887409 prefixEnd_4887409 := by exact prefixLift 4887409
  have htrace : WordTrace (prefixWord ++ tailWord_4887409) baseStart_4887409 baseEnd_4887409 := by
    simpa [prefixWord, tailWord_4887409, baseEnd_4887409] using wordTrace_append hprefix tailTrace_4887409
  have hstable : (prefixWord ++ tailWord_4887409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4887409).length < 2 ^ (prefixWord ++ tailWord_4887409).sum := by decide
  have hdescent : baseEnd_4887409 < baseStart_4887409 := by decide
  rcases family_descends (prefixWord ++ tailWord_4887409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4887413 : List Nat := [1, 3, 4, 1, 1, 2, 4, 1, 1, 1, 4]
def baseStart_4887413 : Nat := 118140960795 + 4887413 * 2 ^ 59
def prefixEnd_4887413 : Nat := 4983230072969 + 3 ^ 40 * 4887413 * 2
def baseEnd_4887413 : Nat := 2509592026032791707860703

theorem tailTrace_4887413 : CollatzResearch.WordTrace tailWord_4887413 prefixEnd_4887413 2509592026032791707860703 := by
  unfold tailWord_4887413
  simp only [CollatzResearch.WordTrace]
  refine ⟨178258596642744879531354893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118839064428496586354236595 178258596642744879531354893)
  ·
    refine ⟨66846973741029329824258085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 178258596642744879531354893 66846973741029329824258085)
    ·
      refine ⟨12533807576442999342048391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66846973741029329824258085 12533807576442999342048391)
      ·
        refine ⟨18800711364664499013072587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12533807576442999342048391 18800711364664499013072587)
        ·
          refine ⟨28201067046996748519608881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18800711364664499013072587 28201067046996748519608881)
          ·
            refine ⟨21150800285247561389706661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28201067046996748519608881 21150800285247561389706661)
            ·
              refine ⟨3965775053483917760569999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21150800285247561389706661 3965775053483917760569999)
              ·
                refine ⟨5948662580225876640854999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3965775053483917760569999 5948662580225876640854999)
                ·
                  refine ⟨8922993870338814961282499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5948662580225876640854999 8922993870338814961282499)
                  ·
                    refine ⟨13384490805508222441923749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8922993870338814961282499 13384490805508222441923749)
                    ·
                      refine ⟨2509592026032791707860703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13384490805508222441923749 2509592026032791707860703)
                      ·
                        rfl

theorem cell23_4887413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 4, 1, 1, 1, 4].length) (baseStart_4887413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4887413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4887413 prefixEnd_4887413 := by exact prefixLift 4887413
  have htrace : WordTrace (prefixWord ++ tailWord_4887413) baseStart_4887413 baseEnd_4887413 := by
    simpa [prefixWord, tailWord_4887413, baseEnd_4887413] using wordTrace_append hprefix tailTrace_4887413
  have hstable : (prefixWord ++ tailWord_4887413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4887413).length < 2 ^ (prefixWord ++ tailWord_4887413).sum := by decide
  have hdescent : baseEnd_4887413 < baseStart_4887413 := by decide
  rcases family_descends (prefixWord ++ tailWord_4887413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4887456 : List Nat := [2, 1, 1, 4, 1, 1, 2, 3, 3, 3, 2]
def baseStart_4887456 : Nat := 118140960795 + 4887456 * 2 ^ 59
def prefixEnd_4887456 : Nat := 4983230072969 + 3 ^ 40 * 4887456 * 2
def baseEnd_4887456 : Nat := 2509614105700935039623005

theorem tailTrace_4887456 : CollatzResearch.WordTrace tailWord_4887456 prefixEnd_4887456 2509614105700935039623005 := by
  unfold tailWord_4887456
  simp only [CollatzResearch.WordTrace]
  refine ⟨89130082490794548937585111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118840109987726065250113481 89130082490794548937585111)
  ·
    refine ⟨133695123736191823406377667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89130082490794548937585111 133695123736191823406377667)
    ·
      refine ⟨200542685604287735109566501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133695123736191823406377667 200542685604287735109566501)
      ·
        refine ⟨37601753550803950333043719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 200542685604287735109566501 37601753550803950333043719)
        ·
          refine ⟨56402630326205925499565579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37601753550803950333043719 56402630326205925499565579)
          ·
            refine ⟨84603945489308888249348369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56402630326205925499565579 84603945489308888249348369)
            ·
              refine ⟨63452959116981666187011277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84603945489308888249348369 63452959116981666187011277)
              ·
                refine ⟨23794859668868124820129229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63452959116981666187011277 23794859668868124820129229)
                ·
                  refine ⟨8923072375825546807548461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23794859668868124820129229 8923072375825546807548461)
                  ·
                    refine ⟨3346152140934580052830673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8923072375825546807548461 3346152140934580052830673)
                    ·
                      refine ⟨2509614105700935039623005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3346152140934580052830673 2509614105700935039623005)
                      ·
                        rfl

theorem cell23_4887456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 3, 3, 3, 2].length) (baseStart_4887456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4887456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4887456 prefixEnd_4887456 := by exact prefixLift 4887456
  have htrace : WordTrace (prefixWord ++ tailWord_4887456) baseStart_4887456 baseEnd_4887456 := by
    simpa [prefixWord, tailWord_4887456, baseEnd_4887456] using wordTrace_append hprefix tailTrace_4887456
  have hstable : (prefixWord ++ tailWord_4887456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4887456).length < 2 ^ (prefixWord ++ tailWord_4887456).sum := by decide
  have hdescent : baseEnd_4887456 < baseStart_4887456 := by decide
  rcases family_descends (prefixWord ++ tailWord_4887456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4887501 : List Nat := [1, 6, 3, 1, 2, 1, 1, 2, 1, 2, 3]
def baseStart_4887501 : Nat := 118140960795 + 4887501 * 2 ^ 59
def prefixEnd_4887501 : Nat := 4983230072969 + 3 ^ 40 * 4887501 * 2
def baseEnd_4887501 : Nat := 2509637212330387363560299

theorem tailTrace_4887501 : CollatzResearch.WordTrace tailWord_4887501 prefixEnd_4887501 2509637212330387363560299 := by
  unfold tailWord_4887501
  simp only [CollatzResearch.WordTrace]
  refine ⟨178261806266426070560558357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118841204177617380373705571 178261806266426070560558357)
  ·
    refine ⟨8356022168738722057526173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 178261806266426070560558357 8356022168738722057526173)
    ·
      refine ⟨3133508313277020771572315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8356022168738722057526173 3133508313277020771572315)
      ·
        refine ⟨4700262469915531157358473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3133508313277020771572315 4700262469915531157358473)
        ·
          refine ⟨3525196852436648368018855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4700262469915531157358473 3525196852436648368018855)
          ·
            refine ⟨5287795278654972552028283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3525196852436648368018855 5287795278654972552028283)
            ·
              refine ⟨7931692917982458828042425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5287795278654972552028283 7931692917982458828042425)
              ·
                refine ⟨5948769688486844121031819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7931692917982458828042425 5948769688486844121031819)
                ·
                  refine ⟨8923154532730266181547729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5948769688486844121031819 8923154532730266181547729)
                  ·
                    refine ⟨6692365899547699636160797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8923154532730266181547729 6692365899547699636160797)
                    ·
                      refine ⟨2509637212330387363560299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6692365899547699636160797 2509637212330387363560299)
                      ·
                        rfl

theorem cell23_4887501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_4887501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4887501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4887501 prefixEnd_4887501 := by exact prefixLift 4887501
  have htrace : WordTrace (prefixWord ++ tailWord_4887501) baseStart_4887501 baseEnd_4887501 := by
    simpa [prefixWord, tailWord_4887501, baseEnd_4887501] using wordTrace_append hprefix tailTrace_4887501
  have hstable : (prefixWord ++ tailWord_4887501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4887501).length < 2 ^ (prefixWord ++ tailWord_4887501).sum := by decide
  have hdescent : baseEnd_4887501 < baseStart_4887501 := by decide
  rcases family_descends (prefixWord ++ tailWord_4887501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4887506 : List Nat := [3, 2, 2, 3, 1, 1, 1, 2, 2, 1, 5]
def baseStart_4887506 : Nat := 118140960795 + 4887506 * 2 ^ 59
def prefixEnd_4887506 : Nat := 4983230072969 + 3 ^ 40 * 4887506 * 2
def baseEnd_4887506 : Nat := 2509639779733659843997775

theorem tailTrace_4887506 : CollatzResearch.WordTrace tailWord_4887506 prefixEnd_4887506 2509639779733659843997775 := by
  unfold tailWord_4887506
  simp only [CollatzResearch.WordTrace]
  refine ⟨44565497157851989103622593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118841325754271970942993581 44565497157851989103622593)
  ·
    refine ⟨33424122868388991827716945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44565497157851989103622593 33424122868388991827716945)
    ·
      refine ⟨25068092151291743870787709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33424122868388991827716945 25068092151291743870787709)
      ·
        refine ⟨9400534556734403951545391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25068092151291743870787709 9400534556734403951545391)
        ·
          refine ⟨14100801835101605927318087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9400534556734403951545391 14100801835101605927318087)
          ·
            refine ⟨21151202752652408890977131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14100801835101605927318087 21151202752652408890977131)
            ·
              refine ⟨31726804128978613336465697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21151202752652408890977131 31726804128978613336465697)
              ·
                refine ⟨23795103096733960002349273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31726804128978613336465697 23795103096733960002349273)
                ·
                  refine ⟨17846327322550470001761955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23795103096733960002349273 17846327322550470001761955)
                  ·
                    refine ⟨26769490983825705002642933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17846327322550470001761955 26769490983825705002642933)
                    ·
                      refine ⟨2509639779733659843997775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26769490983825705002642933 2509639779733659843997775)
                      ·
                        rfl

theorem cell23_4887506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_4887506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4887506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4887506 prefixEnd_4887506 := by exact prefixLift 4887506
  have htrace : WordTrace (prefixWord ++ tailWord_4887506) baseStart_4887506 baseEnd_4887506 := by
    simpa [prefixWord, tailWord_4887506, baseEnd_4887506] using wordTrace_append hprefix tailTrace_4887506
  have hstable : (prefixWord ++ tailWord_4887506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4887506).length < 2 ^ (prefixWord ++ tailWord_4887506).sum := by decide
  have hdescent : baseEnd_4887506 < baseStart_4887506 := by decide
  rcases family_descends (prefixWord ++ tailWord_4887506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4887573 : List Nat := [1, 3, 2, 1, 4, 3, 1, 1, 2, 5]
def baseStart_4887573 : Nat := 118140960795 + 4887573 * 2 ^ 59
def prefixEnd_4887573 : Nat := 4983230072969 + 3 ^ 40 * 4887573 * 2
def baseEnd_4887573 : Nat := 836558060979170360619989

theorem tailTrace_4887573 : CollatzResearch.WordTrace tailWord_4887573 prefixEnd_4887573 836558060979170360619989 := by
  unfold tailWord_4887573
  simp only [CollatzResearch.WordTrace]
  refine ⟨178264432322165226857179373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118842954881443484571452915 178264432322165226857179373)
  ·
    refine ⟨66849162120811960071442265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 178264432322165226857179373 66849162120811960071442265)
    ·
      refine ⟨50136871590608970053581699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66849162120811960071442265 50136871590608970053581699)
      ·
        refine ⟨75205307385913455080372549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50136871590608970053581699 75205307385913455080372549)
        ·
          refine ⟨14100995134858772827569853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75205307385913455080372549 14100995134858772827569853)
          ·
            refine ⟨5287873175572039810338695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14100995134858772827569853 5287873175572039810338695)
            ·
              refine ⟨7931809763358059715508043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5287873175572039810338695 7931809763358059715508043)
              ·
                refine ⟨11897714645037089573262065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7931809763358059715508043 11897714645037089573262065)
                ·
                  refine ⟨8923285983777817179946549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11897714645037089573262065 8923285983777817179946549)
                  ·
                    refine ⟨836558060979170360619989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8923285983777817179946549 836558060979170360619989)
                    ·
                      rfl

theorem cell23_4887573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 1, 1, 2, 5].length) (baseStart_4887573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4887573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4887573 prefixEnd_4887573 := by exact prefixLift 4887573
  have htrace : WordTrace (prefixWord ++ tailWord_4887573) baseStart_4887573 baseEnd_4887573 := by
    simpa [prefixWord, tailWord_4887573, baseEnd_4887573] using wordTrace_append hprefix tailTrace_4887573
  have hstable : (prefixWord ++ tailWord_4887573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4887573).length < 2 ^ (prefixWord ++ tailWord_4887573).sum := by decide
  have hdescent : baseEnd_4887573 < baseStart_4887573 := by decide
  rcases family_descends (prefixWord ++ tailWord_4887573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4887576 : List Nat := [2, 1, 2, 3, 2, 3, 1, 1, 1, 3, 4]
def baseStart_4887576 : Nat := 118140960795 + 4887576 * 2 ^ 59
def prefixEnd_4887576 : Nat := 4983230072969 + 3 ^ 40 * 4887576 * 2
def baseEnd_4887576 : Nat := 2509675723379474570122453

theorem tailTrace_4887576 : CollatzResearch.WordTrace tailWord_4887576 prefixEnd_4887576 2509675723379474570122453 := by
  unfold tailWord_4887576
  simp only [CollatzResearch.WordTrace]
  refine ⟨89132270870577179184769291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118843027827436238913025721 89132270870577179184769291)
  ·
    refine ⟨133698406305865768777153937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89132270870577179184769291 133698406305865768777153937)
    ·
      refine ⟨100273804729399326582865453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133698406305865768777153937 100273804729399326582865453)
      ·
        refine ⟨37602676773524747468574545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100273804729399326582865453 37602676773524747468574545)
        ·
          refine ⟨28202007580143560601430909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37602676773524747468574545 28202007580143560601430909)
          ·
            refine ⟨10575752842553835225536591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28202007580143560601430909 10575752842553835225536591)
            ·
              refine ⟨15863629263830752838304887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10575752842553835225536591 15863629263830752838304887)
              ·
                refine ⟨23795443895746129257457331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15863629263830752838304887 23795443895746129257457331)
                ·
                  refine ⟨35693165843619193886185997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23795443895746129257457331 35693165843619193886185997)
                  ·
                    refine ⟨13384937191357197707319749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35693165843619193886185997 13384937191357197707319749)
                    ·
                      refine ⟨2509675723379474570122453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13384937191357197707319749 2509675723379474570122453)
                      ·
                        rfl

theorem cell23_4887576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 1, 1, 3, 4].length) (baseStart_4887576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4887576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4887576 prefixEnd_4887576 := by exact prefixLift 4887576
  have htrace : WordTrace (prefixWord ++ tailWord_4887576) baseStart_4887576 baseEnd_4887576 := by
    simpa [prefixWord, tailWord_4887576, baseEnd_4887576] using wordTrace_append hprefix tailTrace_4887576
  have hstable : (prefixWord ++ tailWord_4887576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4887576).length < 2 ^ (prefixWord ++ tailWord_4887576).sum := by decide
  have hdescent : baseEnd_4887576 < baseStart_4887576 := by decide
  rcases family_descends (prefixWord ++ tailWord_4887576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4887589 : List Nat := [1, 3, 1, 2, 2, 2, 1, 1, 1, 3, 6]
def baseStart_4887589 : Nat := 118140960795 + 4887589 * 2 ^ 59
def prefixEnd_4887589 : Nat := 4983230072969 + 3 ^ 40 * 4887589 * 2
def baseEnd_4887589 : Nat := 2509682398627983019259893

theorem tailTrace_4887589 : CollatzResearch.WordTrace tailWord_4887589 prefixEnd_4887589 2509682398627983019259893 := by
  unfold tailWord_4887589
  simp only [CollatzResearch.WordTrace]
  refine ⟨178265015890107261589761821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118843343926738174393174547 178265015890107261589761821)
  ·
    refine ⟨66849380958790223096160683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 178265015890107261589761821 66849380958790223096160683)
    ·
      refine ⟨100274071438185334644241025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66849380958790223096160683 100274071438185334644241025)
      ·
        refine ⟨75205553578639000983180769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100274071438185334644241025 75205553578639000983180769)
        ·
          refine ⟨56404165183979250737385577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75205553578639000983180769 56404165183979250737385577)
          ·
            refine ⟨42303123887984438053039183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56404165183979250737385577 42303123887984438053039183)
            ·
              refine ⟨63454685831976657079558775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42303123887984438053039183 63454685831976657079558775)
              ·
                refine ⟨95182028747964985619338163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63454685831976657079558775 95182028747964985619338163)
                ·
                  refine ⟨142773043121947478429007245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 95182028747964985619338163 142773043121947478429007245)
                  ·
                    refine ⟨53539891170730304410877717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 142773043121947478429007245 53539891170730304410877717)
                    ·
                      refine ⟨2509682398627983019259893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53539891170730304410877717 2509682398627983019259893)
                      ·
                        rfl

theorem cell23_4887589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 3, 6].length) (baseStart_4887589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4887589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4887589 prefixEnd_4887589 := by exact prefixLift 4887589
  have htrace : WordTrace (prefixWord ++ tailWord_4887589) baseStart_4887589 baseEnd_4887589 := by
    simpa [prefixWord, tailWord_4887589, baseEnd_4887589] using wordTrace_append hprefix tailTrace_4887589
  have hstable : (prefixWord ++ tailWord_4887589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4887589).length < 2 ^ (prefixWord ++ tailWord_4887589).sum := by decide
  have hdescent : baseEnd_4887589 < baseStart_4887589 := by decide
  rcases family_descends (prefixWord ++ tailWord_4887589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4887596 : List Nat := [2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 3]
def baseStart_4887596 : Nat := 118140960795 + 4887596 * 2 ^ 59
def prefixEnd_4887596 : Nat := 4983230072969 + 3 ^ 40 * 4887596 * 2
def baseEnd_4887596 : Nat := 2509685992992564491872361

theorem tailTrace_4887596 : CollatzResearch.WordTrace tailWord_4887596 prefixEnd_4887596 2509685992992564491872361 := by
  unfold tailWord_4887596
  simp only [CollatzResearch.WordTrace]
  refine ⟨89132635600540950892633321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118843514134054601190177761 89132635600540950892633321)
  ·
    refine ⟨66849476700405713169474991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89132635600540950892633321 66849476700405713169474991)
    ·
      refine ⟨100274215050608569754212487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66849476700405713169474991 100274215050608569754212487)
      ·
        refine ⟨150411322575912854631318731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100274215050608569754212487 150411322575912854631318731)
        ·
          refine ⟨225616983863869281946978097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150411322575912854631318731 225616983863869281946978097)
          ·
            refine ⟨169212737897901961460233573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 225616983863869281946978097 169212737897901961460233573)
            ·
              refine ⟨31727388355856617773793795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 169212737897901961460233573 31727388355856617773793795)
              ·
                refine ⟨47591082533784926660690693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31727388355856617773793795 47591082533784926660690693)
                ·
                  refine ⟨8923327975084673748879505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47591082533784926660690693 8923327975084673748879505)
                  ·
                    refine ⟨6692495981313505311659629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8923327975084673748879505 6692495981313505311659629)
                    ·
                      refine ⟨2509685992992564491872361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6692495981313505311659629 2509685992992564491872361)
                      ·
                        rfl

theorem cell23_4887596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 3].length) (baseStart_4887596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4887596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4887596 prefixEnd_4887596 := by exact prefixLift 4887596
  have htrace : WordTrace (prefixWord ++ tailWord_4887596) baseStart_4887596 baseEnd_4887596 := by
    simpa [prefixWord, tailWord_4887596, baseEnd_4887596] using wordTrace_append hprefix tailTrace_4887596
  have hstable : (prefixWord ++ tailWord_4887596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4887596).length < 2 ^ (prefixWord ++ tailWord_4887596).sum := by decide
  have hdescent : baseEnd_4887596 < baseStart_4887596 := by decide
  rcases family_descends (prefixWord ++ tailWord_4887596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4887619 : List Nat := [1, 1, 1, 3, 1, 2, 3, 2, 1, 2, 6]
def baseStart_4887619 : Nat := 118140960795 + 4887619 * 2 ^ 59
def prefixEnd_4887619 : Nat := 4983230072969 + 3 ^ 40 * 4887619 * 2
def baseEnd_4887619 : Nat := 2509697803047617901884755

theorem tailTrace_4887619 : CollatzResearch.WordTrace tailWord_4887619 prefixEnd_4887619 2509697803047617901884755 := by
  unfold tailWord_4887619
  simp only [CollatzResearch.WordTrace]
  refine ⟨178266110079998576713353911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118844073386665717808902607 178266110079998576713353911)
  ·
    refine ⟨267399165119997865070030867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178266110079998576713353911 267399165119997865070030867)
    ·
      refine ⟨401098747679996797605046301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 267399165119997865070030867 401098747679996797605046301)
      ·
        refine ⟨150412030379998799101892363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 401098747679996797605046301 150412030379998799101892363)
        ·
          refine ⟨225618045569998198652838545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150412030379998799101892363 225618045569998198652838545)
          ·
            refine ⟨169213534177498648989628909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 225618045569998198652838545 169213534177498648989628909)
            ·
              refine ⟨63455075316561993371110841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 169213534177498648989628909 63455075316561993371110841)
              ·
                refine ⟨47591306487421495028333131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63455075316561993371110841 47591306487421495028333131)
                ·
                  refine ⟨71386959731132242542499697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47591306487421495028333131 71386959731132242542499697)
                  ·
                    refine ⟨53540219798349181906874773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 71386959731132242542499697 53540219798349181906874773)
                    ·
                      refine ⟨2509697803047617901884755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53540219798349181906874773 2509697803047617901884755)
                      ·
                        rfl

theorem cell23_4887619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 2, 1, 2, 6].length) (baseStart_4887619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4887619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4887619 prefixEnd_4887619 := by exact prefixLift 4887619
  have htrace : WordTrace (prefixWord ++ tailWord_4887619) baseStart_4887619 baseEnd_4887619 := by
    simpa [prefixWord, tailWord_4887619, baseEnd_4887619] using wordTrace_append hprefix tailTrace_4887619
  have hstable : (prefixWord ++ tailWord_4887619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4887619).length < 2 ^ (prefixWord ++ tailWord_4887619).sum := by decide
  have hdescent : baseEnd_4887619 < baseStart_4887619 := by decide
  rcases family_descends (prefixWord ++ tailWord_4887619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4887670 : List Nat := [5, 1, 1, 2, 1, 1, 1, 2, 4, 3, 2]
def baseStart_4887670 : Nat := 118140960795 + 4887670 * 2 ^ 59
def prefixEnd_4887670 : Nat := 4983230072969 + 3 ^ 40 * 4887670 * 2
def baseEnd_4887670 : Nat := 2509723990560997202347021

theorem tailTrace_4887670 : CollatzResearch.WordTrace tailWord_4887670 prefixEnd_4887670 2509723990560997202347021 := by
  unfold tailWord_4887670
  simp only [CollatzResearch.WordTrace]
  refine ⟨11141748137675863276466279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 118845313468542541615640309 11141748137675863276466279)
  ·
    refine ⟨16712622206513794914699419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11141748137675863276466279 16712622206513794914699419)
    ·
      refine ⟨25068933309770692372049129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16712622206513794914699419 25068933309770692372049129)
      ·
        refine ⟨18801699982328019279036847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25068933309770692372049129 18801699982328019279036847)
        ·
          refine ⟨28202549973492028918555271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18801699982328019279036847 28202549973492028918555271)
          ·
            refine ⟨42303824960238043377832907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28202549973492028918555271 42303824960238043377832907)
            ·
              refine ⟨63455737440357065066749361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42303824960238043377832907 63455737440357065066749361)
              ·
                refine ⟨47591803080267798800062021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63455737440357065066749361 47591803080267798800062021)
                ·
                  refine ⟨8923463077550212275011629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47591803080267798800062021 8923463077550212275011629)
                  ·
                    refine ⟨3346298654081329603129361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8923463077550212275011629 3346298654081329603129361)
                    ·
                      refine ⟨2509723990560997202347021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3346298654081329603129361 2509723990560997202347021)
                      ·
                        rfl

theorem cell23_4887670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 2, 4, 3, 2].length) (baseStart_4887670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4887670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4887670 prefixEnd_4887670 := by exact prefixLift 4887670
  have htrace : WordTrace (prefixWord ++ tailWord_4887670) baseStart_4887670 baseEnd_4887670 := by
    simpa [prefixWord, tailWord_4887670, baseEnd_4887670] using wordTrace_append hprefix tailTrace_4887670
  have hstable : (prefixWord ++ tailWord_4887670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4887670).length < 2 ^ (prefixWord ++ tailWord_4887670).sum := by decide
  have hdescent : baseEnd_4887670 < baseStart_4887670 := by decide
  rcases family_descends (prefixWord ++ tailWord_4887670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4887676 : List Nat := [2, 2, 2, 1, 1, 3, 2, 3, 1, 6]
def baseStart_4887676 : Nat := 118140960795 + 4887676 * 2 ^ 59
def prefixEnd_4887676 : Nat := 4983230072969 + 3 ^ 40 * 4887676 * 2
def baseEnd_4887676 : Nat := 836575690481641392957331

theorem tailTrace_4887676 : CollatzResearch.WordTrace tailWord_4887676 prefixEnd_4887676 836575690481641392957331 := by
  unfold tailWord_4887676
  simp only [CollatzResearch.WordTrace]
  refine ⟨89134094520396037724089441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118845459360528050298785921 89134094520396037724089441)
  ·
    refine ⟨66850570890297028293067081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89134094520396037724089441 66850570890297028293067081)
    ·
      refine ⟨50137928167722771219800311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66850570890297028293067081 50137928167722771219800311)
      ·
        refine ⟨75206892251584156829700467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50137928167722771219800311 75206892251584156829700467)
        ·
          refine ⟨112810338377376235244550701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75206892251584156829700467 112810338377376235244550701)
          ·
            refine ⟨42303876891516088216706513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 112810338377376235244550701 42303876891516088216706513)
            ·
              refine ⟨31727907668637066162529885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42303876891516088216706513 31727907668637066162529885)
              ·
                refine ⟨11897965375738899810948707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31727907668637066162529885 11897965375738899810948707)
                ·
                  refine ⟨17846948063608349716423061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11897965375738899810948707 17846948063608349716423061)
                  ·
                    refine ⟨836575690481641392957331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17846948063608349716423061 836575690481641392957331)
                    ·
                      rfl

theorem cell23_4887676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 3, 1, 6].length) (baseStart_4887676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4887676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4887676 prefixEnd_4887676 := by exact prefixLift 4887676
  have htrace : WordTrace (prefixWord ++ tailWord_4887676) baseStart_4887676 baseEnd_4887676 := by
    simpa [prefixWord, tailWord_4887676, baseEnd_4887676] using wordTrace_append hprefix tailTrace_4887676
  have hstable : (prefixWord ++ tailWord_4887676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4887676).length < 2 ^ (prefixWord ++ tailWord_4887676).sum := by decide
  have hdescent : baseEnd_4887676 < baseStart_4887676 := by decide
  rcases family_descends (prefixWord ++ tailWord_4887676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4887703 : List Nat := [1, 1, 3, 3, 3, 1, 3, 1, 1, 1, 5]
def baseStart_4887703 : Nat := 118140960795 + 4887703 * 2 ^ 59
def prefixEnd_4887703 : Nat := 4983230072969 + 3 ^ 40 * 4887703 * 2
def baseEnd_4887703 : Nat := 2509740935422595573234369

theorem tailTrace_4887703 : CollatzResearch.WordTrace tailWord_4887703 prefixEnd_4887703 2509740935422595573234369 := by
  unfold tailWord_4887703
  simp only [CollatzResearch.WordTrace]
  refine ⟨178269173811694259059411763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118846115874462839372941175 178269173811694259059411763)
  ·
    refine ⟨267403760717541388589117645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178269173811694259059411763 267403760717541388589117645)
    ·
      refine ⟨100276410269078020720919117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 267403760717541388589117645 100276410269078020720919117)
      ·
        refine ⟨37603653850904257770344669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100276410269078020720919117 37603653850904257770344669)
        ·
          refine ⟨14101370194089096663879251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37603653850904257770344669 14101370194089096663879251)
          ·
            refine ⟨21152055291133644995818877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14101370194089096663879251 21152055291133644995818877)
            ·
              refine ⟨7932020734175116873432079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21152055291133644995818877 7932020734175116873432079)
              ·
                refine ⟨11898031101262675310148119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7932020734175116873432079 11898031101262675310148119)
                ·
                  refine ⟨17847046651894012965222179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11898031101262675310148119 17847046651894012965222179)
                  ·
                    refine ⟨26770569977841019447833269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17847046651894012965222179 26770569977841019447833269)
                    ·
                      refine ⟨2509740935422595573234369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26770569977841019447833269 2509740935422595573234369)
                      ·
                        rfl

theorem cell23_4887703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 3, 1, 1, 1, 5].length) (baseStart_4887703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4887703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4887703 prefixEnd_4887703 := by exact prefixLift 4887703
  have htrace : WordTrace (prefixWord ++ tailWord_4887703) baseStart_4887703 baseEnd_4887703 := by
    simpa [prefixWord, tailWord_4887703, baseEnd_4887703] using wordTrace_append hprefix tailTrace_4887703
  have hstable : (prefixWord ++ tailWord_4887703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4887703).length < 2 ^ (prefixWord ++ tailWord_4887703).sum := by decide
  have hdescent : baseEnd_4887703 < baseStart_4887703 := by decide
  rcases family_descends (prefixWord ++ tailWord_4887703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4887706 : List Nat := [3, 1, 1, 5, 1, 12]
def baseStart_4887706 : Nat := 118140960795 + 4887706 * 2 ^ 59
def prefixEnd_4887706 : Nat := 4983230072969 + 3 ^ 40 * 4887706 * 2
def baseEnd_4887706 : Nat := 10328158336891189553485

theorem tailTrace_4887706 : CollatzResearch.WordTrace tailWord_4887706 prefixEnd_4887706 10328158336891189553485 := by
  unfold tailWord_4887706
  simp only [CollatzResearch.WordTrace]
  refine ⟨44567320807670847642942743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118846188820455593714513981 44567320807670847642942743)
  ·
    refine ⟨66850981211506271464414115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44567320807670847642942743 66850981211506271464414115)
    ·
      refine ⟨100276471817259407196621173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66850981211506271464414115 100276471817259407196621173)
      ·
        refine ⟨9400919232868069424683235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 100276471817259407196621173 9400919232868069424683235)
        ·
          refine ⟨14101378849302104137024853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9400919232868069424683235 14101378849302104137024853)
          ·
            refine ⟨10328158336891189553485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 14101378849302104137024853 10328158336891189553485)
            ·
              rfl

theorem cell23_4887706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 12].length) (baseStart_4887706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4887706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4887706 prefixEnd_4887706 := by exact prefixLift 4887706
  have htrace : WordTrace (prefixWord ++ tailWord_4887706) baseStart_4887706 baseEnd_4887706 := by
    simpa [prefixWord, tailWord_4887706, baseEnd_4887706] using wordTrace_append hprefix tailTrace_4887706
  have hstable : (prefixWord ++ tailWord_4887706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4887706).length < 2 ^ (prefixWord ++ tailWord_4887706).sum := by decide
  have hdescent : baseEnd_4887706 < baseStart_4887706 := by decide
  rcases family_descends (prefixWord ++ tailWord_4887706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4887711 : List Nat := [1, 1, 2, 6, 2, 2, 2, 2, 1, 1, 3]
def baseStart_4887711 : Nat := 118140960795 + 4887711 * 2 ^ 59
def prefixEnd_4887711 : Nat := 4983230072969 + 3 ^ 40 * 4887711 * 2
def baseEnd_4887711 : Nat := 2509745043267831541934333

theorem tailTrace_4887711 : CollatzResearch.WordTrace tailWord_4887711 prefixEnd_4887711 2509745043267831541934333 := by
  unfold tailWord_4887711
  simp only [CollatzResearch.WordTrace]
  refine ⟨178269465595665276425702987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118846310397110184283801991 178269465595665276425702987)
  ·
    refine ⟨267404198393497914638554481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178269465595665276425702987 267404198393497914638554481)
    ·
      refine ⟨200553148795123435978915861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 267404198393497914638554481 200553148795123435978915861)
      ·
        refine ⟨9400928849771411061511681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 200553148795123435978915861 9400928849771411061511681)
        ·
          refine ⟨7050696637328558296133761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9400928849771411061511681 7050696637328558296133761)
          ·
            refine ⟨5288022477996418722100321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7050696637328558296133761 5288022477996418722100321)
            ·
              refine ⟨3966016858497314041575241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5288022477996418722100321 3966016858497314041575241)
              ·
                refine ⟨2974512643872985531181431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3966016858497314041575241 2974512643872985531181431)
                ·
                  refine ⟨4461768965809478296772147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2974512643872985531181431 4461768965809478296772147)
                  ·
                    refine ⟨6692653448714217445158221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4461768965809478296772147 6692653448714217445158221)
                    ·
                      refine ⟨2509745043267831541934333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6692653448714217445158221 2509745043267831541934333)
                      ·
                        rfl

theorem cell23_4887711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 2, 2, 1, 1, 3].length) (baseStart_4887711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4887711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4887711 prefixEnd_4887711 := by exact prefixLift 4887711
  have htrace : WordTrace (prefixWord ++ tailWord_4887711) baseStart_4887711 baseEnd_4887711 := by
    simpa [prefixWord, tailWord_4887711, baseEnd_4887711] using wordTrace_append hprefix tailTrace_4887711
  have hstable : (prefixWord ++ tailWord_4887711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4887711).length < 2 ^ (prefixWord ++ tailWord_4887711).sum := by decide
  have hdescent : baseEnd_4887711 < baseStart_4887711 := by decide
  rcases family_descends (prefixWord ++ tailWord_4887711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4887794 : List Nat := [3, 2, 1, 3, 3, 1, 2, 2, 1, 3, 2]
def baseStart_4887794 : Nat := 118140960795 + 4887794 * 2 ^ 59
def prefixEnd_4887794 : Nat := 4983230072969 + 3 ^ 40 * 4887794 * 2
def baseEnd_4887794 : Nat := 2509787662162154717196451

theorem tailTrace_4887794 : CollatzResearch.WordTrace tailWord_4887794 prefixEnd_4887794 2509787662162154717196451 := by
  unfold tailWord_4887794
  simp only [CollatzResearch.WordTrace]
  refine ⟨44568123213591145400243609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118848328569576387733982957 44568123213591145400243609)
  ·
    refine ⟨33426092410193359050182707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44568123213591145400243609 33426092410193359050182707)
    ·
      refine ⟨50139138615290038575274061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33426092410193359050182707 50139138615290038575274061)
      ·
        refine ⟨18802176980733764465727773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50139138615290038575274061 18802176980733764465727773)
        ·
          refine ⟨7050816367775161674647915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18802176980733764465727773 7050816367775161674647915)
          ·
            refine ⟨10576224551662742511971873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7050816367775161674647915 10576224551662742511971873)
            ·
              refine ⟨7932168413747056883978905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10576224551662742511971873 7932168413747056883978905)
              ·
                refine ⟨5949126310310292662984179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7932168413747056883978905 5949126310310292662984179)
                ·
                  refine ⟨8923689465465438994476269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5949126310310292662984179 8923689465465438994476269)
                  ·
                    refine ⟨3346383549549539622928601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8923689465465438994476269 3346383549549539622928601)
                    ·
                      refine ⟨2509787662162154717196451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3346383549549539622928601 2509787662162154717196451)
                      ·
                        rfl

theorem cell23_4887794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 2, 2, 1, 3, 2].length) (baseStart_4887794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4887794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4887794 prefixEnd_4887794 := by exact prefixLift 4887794
  have htrace : WordTrace (prefixWord ++ tailWord_4887794) baseStart_4887794 baseEnd_4887794 := by
    simpa [prefixWord, tailWord_4887794, baseEnd_4887794] using wordTrace_append hprefix tailTrace_4887794
  have hstable : (prefixWord ++ tailWord_4887794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4887794).length < 2 ^ (prefixWord ++ tailWord_4887794).sum := by decide
  have hdescent : baseEnd_4887794 < baseStart_4887794 := by decide
  rcases family_descends (prefixWord ++ tailWord_4887794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4887880 : List Nat := [2, 1, 3, 1, 1, 2, 1, 4, 2, 4, 2]
def baseStart_4887880 : Nat := 118140960795 + 4887880 * 2 ^ 59
def prefixEnd_4887880 : Nat := 4983230072969 + 3 ^ 40 * 4887880 * 2
def baseEnd_4887880 : Nat := 2509831821498441380721055

theorem tailTrace_4887880 : CollatzResearch.WordTrace tailWord_4887880 prefixEnd_4887880 2509831821498441380721055 := by
  unfold tailWord_4887880
  simp only [CollatzResearch.WordTrace]
  refine ⟨89137814766026509144302547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118850419688035345525736729 89137814766026509144302547)
  ·
    refine ⟨133706722149039763716453821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89137814766026509144302547 133706722149039763716453821)
    ·
      refine ⟨50140020805889911393670183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133706722149039763716453821 50140020805889911393670183)
      ·
        refine ⟨75210031208834867090505275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50140020805889911393670183 75210031208834867090505275)
        ·
          refine ⟨112815046813252300635757913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75210031208834867090505275 112815046813252300635757913)
          ·
            refine ⟨84611285109939225476818435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112815046813252300635757913 84611285109939225476818435)
            ·
              refine ⟨126916927664908838215227653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84611285109939225476818435 126916927664908838215227653)
              ·
                refine ⟨23796923937170407165355185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 126916927664908838215227653 23796923937170407165355185)
                ·
                  refine ⟨17847692952877805374016389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23796923937170407165355185 17847692952877805374016389)
                  ·
                    refine ⟨3346442428664588507628073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17847692952877805374016389 3346442428664588507628073)
                    ·
                      refine ⟨2509831821498441380721055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3346442428664588507628073 2509831821498441380721055)
                      ·
                        rfl

theorem cell23_4887880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 4, 2, 4, 2].length) (baseStart_4887880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4887880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4887880 prefixEnd_4887880 := by exact prefixLift 4887880
  have htrace : WordTrace (prefixWord ++ tailWord_4887880) baseStart_4887880 baseEnd_4887880 := by
    simpa [prefixWord, tailWord_4887880, baseEnd_4887880] using wordTrace_append hprefix tailTrace_4887880
  have hstable : (prefixWord ++ tailWord_4887880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4887880).length < 2 ^ (prefixWord ++ tailWord_4887880).sum := by decide
  have hdescent : baseEnd_4887880 < baseStart_4887880 := by decide
  rcases family_descends (prefixWord ++ tailWord_4887880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4887890 : List Nat := [3, 2, 2, 1, 1, 1, 1, 5, 3, 4]
def baseStart_4887890 : Nat := 118140960795 + 4887890 * 2 ^ 59
def prefixEnd_4887890 : Nat := 4983230072969 + 3 ^ 40 * 4887890 * 2
def baseEnd_4887890 : Nat := 836612318768328780532003

theorem tailTrace_4887890 : CollatzResearch.WordTrace tailWord_4887890 prefixEnd_4887890 836612318768328780532003 := by
  unfold tailWord_4887890
  simp only [CollatzResearch.WordTrace]
  refine ⟨44568998565504197499117281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118850662841344526664312749 44568998565504197499117281)
  ·
    refine ⟨33426748924128148124337961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44568998565504197499117281 33426748924128148124337961)
    ·
      refine ⟨25070061693096111093253471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33426748924128148124337961 25070061693096111093253471)
      ·
        refine ⟨37605092539644166639880207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25070061693096111093253471 37605092539644166639880207)
        ·
          refine ⟨56407638809466249959820311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37605092539644166639880207 56407638809466249959820311)
          ·
            refine ⟨84611458214199374939730467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56407638809466249959820311 84611458214199374939730467)
            ·
              refine ⟨126917187321299062409595701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84611458214199374939730467 126917187321299062409595701)
              ·
                refine ⟨11898486311371787100899597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 126917187321299062409595701 11898486311371787100899597)
                ·
                  refine ⟨4461932366764420162837349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11898486311371787100899597 4461932366764420162837349)
                  ·
                    refine ⟨836612318768328780532003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4461932366764420162837349 836612318768328780532003)
                    ·
                      rfl

theorem cell23_4887890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 5, 3, 4].length) (baseStart_4887890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4887890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4887890 prefixEnd_4887890 := by exact prefixLift 4887890
  have htrace : WordTrace (prefixWord ++ tailWord_4887890) baseStart_4887890 baseEnd_4887890 := by
    simpa [prefixWord, tailWord_4887890, baseEnd_4887890] using wordTrace_append hprefix tailTrace_4887890
  have hstable : (prefixWord ++ tailWord_4887890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4887890).length < 2 ^ (prefixWord ++ tailWord_4887890).sum := by decide
  have hdescent : baseEnd_4887890 < baseStart_4887890 := by decide
  rcases family_descends (prefixWord ++ tailWord_4887890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4887913 : List Nat := [1, 2, 1, 1, 1, 3, 2, 1, 1, 7, 3]
def baseStart_4887913 : Nat := 118140960795 + 4887913 * 2 ^ 59
def prefixEnd_4887913 : Nat := 4983230072969 + 3 ^ 40 * 4887913 * 2
def baseEnd_4887913 : Nat := 2509848766360039751608403

theorem tailTrace_4887913 : CollatzResearch.WordTrace tailWord_4887913 prefixEnd_4887913 2509848766360039751608403 := by
  unfold tailWord_4887913
  simp only [CollatzResearch.WordTrace]
  refine ⟨178276833140933464924556393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118851222093955643283037595 178276833140933464924556393)
  ·
    refine ⟨133707624855700098693417295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178276833140933464924556393 133707624855700098693417295)
    ·
      refine ⟨200561437283550148040125943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133707624855700098693417295 200561437283550148040125943)
      ·
        refine ⟨300842155925325222060188915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200561437283550148040125943 300842155925325222060188915)
        ·
          refine ⟨451263233887987833090283373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 300842155925325222060188915 451263233887987833090283373)
          ·
            refine ⟨169223712707995437408856265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 451263233887987833090283373 169223712707995437408856265)
            ·
              refine ⟨126917784530996578056642199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 169223712707995437408856265 126917784530996578056642199)
              ·
                refine ⟨190376676796494867084963299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126917784530996578056642199 190376676796494867084963299)
                ·
                  refine ⟨285565015194742300627444949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 190376676796494867084963299 285565015194742300627444949)
                  ·
                    refine ⟨6692930043626772670955741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 285565015194742300627444949 6692930043626772670955741)
                    ·
                      refine ⟨2509848766360039751608403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6692930043626772670955741 2509848766360039751608403)
                      ·
                        rfl

theorem cell23_4887913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 7, 3].length) (baseStart_4887913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4887913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4887913 prefixEnd_4887913 := by exact prefixLift 4887913
  have htrace : WordTrace (prefixWord ++ tailWord_4887913) baseStart_4887913 baseEnd_4887913 := by
    simpa [prefixWord, tailWord_4887913, baseEnd_4887913] using wordTrace_append hprefix tailTrace_4887913
  have hstable : (prefixWord ++ tailWord_4887913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4887913).length < 2 ^ (prefixWord ++ tailWord_4887913).sum := by decide
  have hdescent : baseEnd_4887913 < baseStart_4887913 := by decide
  rcases family_descends (prefixWord ++ tailWord_4887913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4887914 : List Nat := [3, 1, 3, 3, 2, 2, 1, 1, 2, 1, 4]
def baseStart_4887914 : Nat := 118140960795 + 4887914 * 2 ^ 59
def prefixEnd_4887914 : Nat := 4983230072969 + 3 ^ 40 * 4887914 * 2
def baseEnd_4887914 : Nat := 2509849279840694247695899

theorem tailTrace_4887914 : CollatzResearch.WordTrace tailWord_4887914 prefixEnd_4887914 2509849279840694247695899 := by
  unfold tailWord_4887914
  simp only [CollatzResearch.WordTrace]
  refine ⟨44569217403482460523835699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118851246409286561396895197 44569217403482460523835699)
  ·
    refine ⟨66853826105223690785753549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44569217403482460523835699 66853826105223690785753549)
    ·
      refine ⟨25070184789458884044657581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66853826105223690785753549 25070184789458884044657581)
      ·
        refine ⟨9401319296047081516746593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25070184789458884044657581 9401319296047081516746593)
        ·
          refine ⟨7050989472035311137559945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9401319296047081516746593 7050989472035311137559945)
          ·
            refine ⟨5288242104026483353169959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7050989472035311137559945 5288242104026483353169959)
            ·
              refine ⟨7932363156039725029754939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5288242104026483353169959 7932363156039725029754939)
              ·
                refine ⟨11898544734059587544632409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7932363156039725029754939 11898544734059587544632409)
                ·
                  refine ⟨8923908550544690658474307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11898544734059587544632409 8923908550544690658474307)
                  ·
                    refine ⟨13385862825817035987711461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8923908550544690658474307 13385862825817035987711461)
                    ·
                      refine ⟨2509849279840694247695899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13385862825817035987711461 2509849279840694247695899)
                      ·
                        rfl

theorem cell23_4887914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_4887914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4887914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4887914 prefixEnd_4887914 := by exact prefixLift 4887914
  have htrace : WordTrace (prefixWord ++ tailWord_4887914) baseStart_4887914 baseEnd_4887914 := by
    simpa [prefixWord, tailWord_4887914, baseEnd_4887914] using wordTrace_append hprefix tailTrace_4887914
  have hstable : (prefixWord ++ tailWord_4887914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4887914).length < 2 ^ (prefixWord ++ tailWord_4887914).sum := by decide
  have hdescent : baseEnd_4887914 < baseStart_4887914 := by decide
  rcases family_descends (prefixWord ++ tailWord_4887914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4887917 : List Nat := [1, 5, 1, 1, 1, 3, 3, 1, 2, 2, 3]
def baseStart_4887917 : Nat := 118140960795 + 4887917 * 2 ^ 59
def prefixEnd_4887917 : Nat := 4983230072969 + 3 ^ 40 * 4887917 * 2
def baseEnd_4887917 : Nat := 2509850820282657735958385

theorem tailTrace_4887917 : CollatzResearch.WordTrace tailWord_4887917 prefixEnd_4887917 2509850820282657735958385 := by
  unfold tailWord_4887917
  simp only [CollatzResearch.WordTrace]
  refine ⟨178276979032918973607702005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118851319355279315738468003 178276979032918973607702005)
  ·
    refine ⟨16713466784336153775722063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 178276979032918973607702005 16713466784336153775722063)
    ·
      refine ⟨25070200176504230663583095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16713466784336153775722063 25070200176504230663583095)
      ·
        refine ⟨37605300264756345995374643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25070200176504230663583095 37605300264756345995374643)
        ·
          refine ⟨56407950397134518993061965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37605300264756345995374643 56407950397134518993061965)
          ·
            refine ⟨21152981398925444622398237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56407950397134518993061965 21152981398925444622398237)
            ·
              refine ⟨7932368024597041733399339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21152981398925444622398237 7932368024597041733399339)
              ·
                refine ⟨11898552036895562600099009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7932368024597041733399339 11898552036895562600099009)
                ·
                  refine ⟨8923914027671671950074257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11898552036895562600099009 8923914027671671950074257)
                  ·
                    refine ⟨6692935520753753962555693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8923914027671671950074257 6692935520753753962555693)
                    ·
                      refine ⟨2509850820282657735958385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6692935520753753962555693 2509850820282657735958385)
                      ·
                        rfl

theorem cell23_4887917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3, 1, 2, 2, 3].length) (baseStart_4887917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4887917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4887917 prefixEnd_4887917 := by exact prefixLift 4887917
  have htrace : WordTrace (prefixWord ++ tailWord_4887917) baseStart_4887917 baseEnd_4887917 := by
    simpa [prefixWord, tailWord_4887917, baseEnd_4887917] using wordTrace_append hprefix tailTrace_4887917
  have hstable : (prefixWord ++ tailWord_4887917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4887917).length < 2 ^ (prefixWord ++ tailWord_4887917).sum := by decide
  have hdescent : baseEnd_4887917 < baseStart_4887917 := by decide
  rcases family_descends (prefixWord ++ tailWord_4887917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4887947 : List Nat := [1, 1, 1, 1, 4, 3, 4, 1, 3, 1, 3]
def baseStart_4887947 : Nat := 118140960795 + 4887947 * 2 ^ 59
def prefixEnd_4887947 : Nat := 4983230072969 + 3 ^ 40 * 4887947 * 2
def baseEnd_4887947 : Nat := 2509866224702292618583247

theorem tailTrace_4887947 : CollatzResearch.WordTrace tailWord_4887947 prefixEnd_4887947 2509866224702292618583247 := by
  unfold tailWord_4887947
  simp only [CollatzResearch.WordTrace]
  refine ⟨178278073222810288731294095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118852048815206859154196063 178278073222810288731294095)
  ·
    refine ⟨267417109834215433096941143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178278073222810288731294095 267417109834215433096941143)
    ·
      refine ⟨401125664751323149645411715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 267417109834215433096941143 401125664751323149645411715)
      ·
        refine ⟨601688497126984724468117573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 401125664751323149645411715 601688497126984724468117573)
        ·
          refine ⟨112816593211309635837772045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 601688497126984724468117573 112816593211309635837772045)
          ·
            refine ⟨42306222454241113439164517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 112816593211309635837772045 42306222454241113439164517)
            ·
              refine ⟨7932416710170208769843347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42306222454241113439164517 7932416710170208769843347)
              ·
                refine ⟨11898625065255313154765021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7932416710170208769843347 11898625065255313154765021)
                ·
                  refine ⟨4461984399470742433036883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11898625065255313154765021 4461984399470742433036883)
                  ·
                    refine ⟨6692976599206113649555325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4461984399470742433036883 6692976599206113649555325)
                    ·
                      refine ⟨2509866224702292618583247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6692976599206113649555325 2509866224702292618583247)
                      ·
                        rfl

theorem cell23_4887947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 4, 1, 3, 1, 3].length) (baseStart_4887947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4887947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4887947 prefixEnd_4887947 := by exact prefixLift 4887947
  have htrace : WordTrace (prefixWord ++ tailWord_4887947) baseStart_4887947 baseEnd_4887947 := by
    simpa [prefixWord, tailWord_4887947, baseEnd_4887947] using wordTrace_append hprefix tailTrace_4887947
  have hstable : (prefixWord ++ tailWord_4887947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4887947).length < 2 ^ (prefixWord ++ tailWord_4887947).sum := by decide
  have hdescent : baseEnd_4887947 < baseStart_4887947 := by decide
  rcases family_descends (prefixWord ++ tailWord_4887947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4887967 : List Nat := [1, 1, 2, 5, 1, 3, 2, 2, 1, 5]
def baseStart_4887967 : Nat := 118140960795 + 4887967 * 2 ^ 59
def prefixEnd_4887967 : Nat := 4983230072969 + 3 ^ 40 * 4887967 * 2
def baseEnd_4887967 : Nat := 836625498105127513444385

theorem tailTrace_4887967 : CollatzResearch.WordTrace tailWord_4887967 prefixEnd_4887967 836625498105127513444385 := by
  unfold tailWord_4887967
  simp only [CollatzResearch.WordTrace]
  refine ⟨178278802682737832147022155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118852535121825221431348103 178278802682737832147022155)
  ·
    refine ⟨267418204024106748220533233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178278802682737832147022155 267418204024106748220533233)
    ·
      refine ⟨200563653018080061165399925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 267418204024106748220533233 200563653018080061165399925)
      ·
        refine ⟨18802842470445005734256243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 200563653018080061165399925 18802842470445005734256243)
        ·
          refine ⟨28204263705667508601384365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18802842470445005734256243 28204263705667508601384365)
          ·
            refine ⟨10576598889625315725519137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28204263705667508601384365 10576598889625315725519137)
            ·
              refine ⟨7932449167218986794139353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10576598889625315725519137 7932449167218986794139353)
              ·
                refine ⟨5949336875414240095604515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7932449167218986794139353 5949336875414240095604515)
                ·
                  refine ⟨8924005313121360143406773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5949336875414240095604515 8924005313121360143406773)
                  ·
                    refine ⟨836625498105127513444385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8924005313121360143406773 836625498105127513444385)
                    ·
                      rfl

theorem cell23_4887967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 2, 2, 1, 5].length) (baseStart_4887967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4887967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4887967 prefixEnd_4887967 := by exact prefixLift 4887967
  have htrace : WordTrace (prefixWord ++ tailWord_4887967) baseStart_4887967 baseEnd_4887967 := by
    simpa [prefixWord, tailWord_4887967, baseEnd_4887967] using wordTrace_append hprefix tailTrace_4887967
  have hstable : (prefixWord ++ tailWord_4887967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4887967).length < 2 ^ (prefixWord ++ tailWord_4887967).sum := by decide
  have hdescent : baseEnd_4887967 < baseStart_4887967 := by decide
  rcases family_descends (prefixWord ++ tailWord_4887967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4887980 : List Nat := [2, 2, 1, 1, 1, 1, 5, 2, 4, 4]
def baseStart_4887980 : Nat := 118140960795 + 4887980 * 2 ^ 59
def prefixEnd_4887980 : Nat := 4983230072969 + 3 ^ 40 * 4887980 * 2
def baseEnd_4887980 : Nat := 836627723187963663156865

theorem tailTrace_4887980 : CollatzResearch.WordTrace tailWord_4887980 prefixEnd_4887980 836627723187963663156865 := by
  unfold tailWord_4887980
  simp only [CollatzResearch.WordTrace]
  refine ⟨89139638415845367683622697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118852851221127156911496929 89139638415845367683622697)
  ·
    refine ⟨66854728811884025762717023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89139638415845367683622697 66854728811884025762717023)
    ·
      refine ⟨100282093217826038644075535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66854728811884025762717023 100282093217826038644075535)
      ·
        refine ⟨150423139826739057966113303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100282093217826038644075535 150423139826739057966113303)
        ·
          refine ⟨225634709740108586949169955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150423139826739057966113303 225634709740108586949169955)
          ·
            refine ⟨338452064610162880423754933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 225634709740108586949169955 338452064610162880423754933)
            ·
              refine ⟨31729881057202770039727025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 338452064610162880423754933 31729881057202770039727025)
              ·
                refine ⟨23797410792902077529795269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31729881057202770039727025 23797410792902077529795269)
                ·
                  refine ⟨4462014523669139536836613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23797410792902077529795269 4462014523669139536836613)
                  ·
                    refine ⟨836627723187963663156865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4462014523669139536836613 836627723187963663156865)
                    ·
                      rfl

theorem cell23_4887980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 4].length) (baseStart_4887980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4887980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4887980 prefixEnd_4887980 := by exact prefixLift 4887980
  have htrace : WordTrace (prefixWord ++ tailWord_4887980) baseStart_4887980 baseEnd_4887980 := by
    simpa [prefixWord, tailWord_4887980, baseEnd_4887980] using wordTrace_append hprefix tailTrace_4887980
  have hstable : (prefixWord ++ tailWord_4887980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4887980).length < 2 ^ (prefixWord ++ tailWord_4887980).sum := by decide
  have hdescent : baseEnd_4887980 < baseStart_4887980 := by decide
  rcases family_descends (prefixWord ++ tailWord_4887980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4887987 : List Nat := [1, 1, 1, 2, 3, 1, 1, 4, 5, 2, 2]
def baseStart_4887987 : Nat := 118140960795 + 4887987 * 2 ^ 59
def prefixEnd_4887987 : Nat := 4983230072969 + 3 ^ 40 * 4887987 * 2
def baseEnd_4887987 : Nat := 2509886763928472462083063

theorem tailTrace_4887987 : CollatzResearch.WordTrace tailWord_4887987 prefixEnd_4887987 2509886763928472462083063 := by
  unfold tailWord_4887987
  simp only [CollatzResearch.WordTrace]
  refine ⟨178279532142665375562750215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118853021428443583708500143 178279532142665375562750215)
  ·
    refine ⟨267419298213998063344125323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178279532142665375562750215 267419298213998063344125323)
    ·
      refine ⟨401128947320997095016187985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 267419298213998063344125323 401128947320997095016187985)
      ·
        refine ⟨300846710490747821262140989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 401128947320997095016187985 300846710490747821262140989)
        ·
          refine ⟨112817516434030432973302871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 300846710490747821262140989 112817516434030432973302871)
          ·
            refine ⟨169226274651045649459954307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112817516434030432973302871 169226274651045649459954307)
            ·
              refine ⟨253839411976568474189931461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 169226274651045649459954307 253839411976568474189931461)
              ·
                refine ⟨47594889745606588910612149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 253839411976568474189931461 47594889745606588910612149)
                ·
                  refine ⟨4462020913650617710369889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47594889745606588910612149 4462020913650617710369889)
                  ·
                    refine ⟨3346515685237963282777417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4462020913650617710369889 3346515685237963282777417)
                    ·
                      refine ⟨2509886763928472462083063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3346515685237963282777417 2509886763928472462083063)
                      ·
                        rfl

theorem cell23_4887987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 4, 5, 2, 2].length) (baseStart_4887987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4887987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4887987 prefixEnd_4887987 := by exact prefixLift 4887987
  have htrace : WordTrace (prefixWord ++ tailWord_4887987) baseStart_4887987 baseEnd_4887987 := by
    simpa [prefixWord, tailWord_4887987, baseEnd_4887987] using wordTrace_append hprefix tailTrace_4887987
  have hstable : (prefixWord ++ tailWord_4887987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4887987).length < 2 ^ (prefixWord ++ tailWord_4887987).sum := by decide
  have hdescent : baseEnd_4887987 < baseStart_4887987 := by decide
  rcases family_descends (prefixWord ++ tailWord_4887987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4887997 : List Nat := [1, 4, 1, 2, 2, 1, 2, 4, 2, 4]
def baseStart_4887997 : Nat := 118140960795 + 4887997 * 2 ^ 59
def prefixEnd_4887997 : Nat := 4983230072969 + 3 ^ 40 * 4887997 * 2
def baseEnd_4887997 : Nat := 836630632911672474319339

theorem tailTrace_4887997 : CollatzResearch.WordTrace tailWord_4887997 prefixEnd_4887997 836630632911672474319339 := by
  unfold tailWord_4887997
  simp only [CollatzResearch.WordTrace]
  refine ⟨178279896872629147270614245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118853264581752764847076163 178279896872629147270614245)
  ·
    refine ⟨33427480663617965113240171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 178279896872629147270614245 33427480663617965113240171)
    ·
      refine ⟨50141220995426947669860257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33427480663617965113240171 50141220995426947669860257)
      ·
        refine ⟨37605915746570210752395193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50141220995426947669860257 37605915746570210752395193)
        ·
          refine ⟨28204436809927658064296395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37605915746570210752395193 28204436809927658064296395)
          ·
            refine ⟨42306655214891487096444593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28204436809927658064296395 42306655214891487096444593)
            ·
              refine ⟨31729991411168615322333445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42306655214891487096444593 31729991411168615322333445)
              ·
                refine ⟨5949373389594115372937521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31729991411168615322333445 5949373389594115372937521)
                ·
                  refine ⟨4462030042195586529703141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5949373389594115372937521 4462030042195586529703141)
                  ·
                    refine ⟨836630632911672474319339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4462030042195586529703141 836630632911672474319339)
                    ·
                      rfl

theorem cell23_4887997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 4, 2, 4].length) (baseStart_4887997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4887997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4887997 prefixEnd_4887997 := by exact prefixLift 4887997
  have htrace : WordTrace (prefixWord ++ tailWord_4887997) baseStart_4887997 baseEnd_4887997 := by
    simpa [prefixWord, tailWord_4887997, baseEnd_4887997] using wordTrace_append hprefix tailTrace_4887997
  have hstable : (prefixWord ++ tailWord_4887997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4887997).length < 2 ^ (prefixWord ++ tailWord_4887997).sum := by decide
  have hdescent : baseEnd_4887997 < baseStart_4887997 := by decide
  rcases family_descends (prefixWord ++ tailWord_4887997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4888010 : List Nat := [3, 1, 2, 1, 2, 4, 2, 8]
def baseStart_4888010 : Nat := 118140960795 + 4888010 * 2 ^ 59
def prefixEnd_4888010 : Nat := 4983230072969 + 3 ^ 40 * 4888010 * 2
def baseEnd_4888010 : Nat := 92959206443834291559091

theorem tailTrace_4888010 : CollatzResearch.WordTrace tailWord_4888010 prefixEnd_4888010 92959206443834291559091 := by
  unfold tailWord_4888010
  simp only [CollatzResearch.WordTrace]
  refine ⟨44570092755395512622709371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118853580681054700327224989 44570092755395512622709371)
  ·
    refine ⟨66855139133093268934064057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44570092755395512622709371 66855139133093268934064057)
    ·
      refine ⟨50141354349819951700548043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66855139133093268934064057 50141354349819951700548043)
      ·
        refine ⟨75212031524729927550822065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50141354349819951700548043 75212031524729927550822065)
        ·
          refine ⟨56409023643547445663116549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75212031524729927550822065 56409023643547445663116549)
          ·
            refine ⟨10576691933165146061834353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56409023643547445663116549 10576691933165146061834353)
            ·
              refine ⟨7932518949873859546375765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10576691933165146061834353 7932518949873859546375765)
              ·
                refine ⟨92959206443834291559091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7932518949873859546375765 92959206443834291559091)
                ·
                  rfl

theorem cell23_4888010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 2, 8].length) (baseStart_4888010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4888010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4888010 prefixEnd_4888010 := by exact prefixLift 4888010
  have htrace : WordTrace (prefixWord ++ tailWord_4888010) baseStart_4888010 baseEnd_4888010 := by
    simpa [prefixWord, tailWord_4888010, baseEnd_4888010] using wordTrace_append hprefix tailTrace_4888010
  have hstable : (prefixWord ++ tailWord_4888010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4888010).length < 2 ^ (prefixWord ++ tailWord_4888010).sum := by decide
  have hdescent : baseEnd_4888010 < baseStart_4888010 := by decide
  rcases family_descends (prefixWord ++ tailWord_4888010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4888014 : List Nat := [4, 1, 1, 1, 2, 1, 6, 1, 2, 4]
def baseStart_4888014 : Nat := 118140960795 + 4888014 * 2 ^ 59
def prefixEnd_4888014 : Nat := 4983230072969 + 3 ^ 40 * 4888014 * 2
def baseEnd_4888014 : Nat := 836633542635381285481813

theorem tailTrace_4888014 : CollatzResearch.WordTrace tailWord_4888014 prefixEnd_4888014 836633542635381285481813 := by
  unfold tailWord_4888014
  simp only [CollatzResearch.WordTrace]
  refine ⟨22285064614195944896747887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118853677942378372782655397 22285064614195944896747887)
  ·
    refine ⟨33427596921293917345121831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22285064614195944896747887 33427596921293917345121831)
    ·
      refine ⟨50141395381940876017682747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33427596921293917345121831 50141395381940876017682747)
      ·
        refine ⟨75212093072911314026524121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50141395381940876017682747 75212093072911314026524121)
        ·
          refine ⟨56409069804683485519893091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75212093072911314026524121 56409069804683485519893091)
          ·
            refine ⟨84613604707025228279839637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56409069804683485519893091 84613604707025228279839637)
            ·
              refine ⟨3966262720641807575617483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 84613604707025228279839637 3966262720641807575617483)
              ·
                refine ⟨5949394080962711363426225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3966262720641807575617483 5949394080962711363426225)
                ·
                  refine ⟨4462045560722033522569669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5949394080962711363426225 4462045560722033522569669)
                  ·
                    refine ⟨836633542635381285481813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4462045560722033522569669 836633542635381285481813)
                    ·
                      rfl

theorem cell23_4888014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 6, 1, 2, 4].length) (baseStart_4888014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4888014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4888014 prefixEnd_4888014 := by exact prefixLift 4888014
  have htrace : WordTrace (prefixWord ++ tailWord_4888014) baseStart_4888014 baseEnd_4888014 := by
    simpa [prefixWord, tailWord_4888014, baseEnd_4888014] using wordTrace_append hprefix tailTrace_4888014
  have hstable : (prefixWord ++ tailWord_4888014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4888014).length < 2 ^ (prefixWord ++ tailWord_4888014).sum := by decide
  have hdescent : baseEnd_4888014 < baseStart_4888014 := by decide
  rcases family_descends (prefixWord ++ tailWord_4888014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4888037 : List Nat := [1, 3, 1, 5, 1, 1, 1, 1, 3, 3, 3]
def baseStart_4888037 : Nat := 118140960795 + 4888037 * 2 ^ 59
def prefixEnd_4888037 : Nat := 4983230072969 + 3 ^ 40 * 4888037 * 2
def baseEnd_4888037 : Nat := 2509912437961197266457833

theorem tailTrace_4888037 : CollatzResearch.WordTrace tailWord_4888037 prefixEnd_4888037 2509912437961197266457833 := by
  unfold tailWord_4888037
  simp only [CollatzResearch.WordTrace]
  refine ⟨178281355792484234102070365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118854237194989489401380243 178281355792484234102070365)
  ·
    refine ⟨66855508422181587788276387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 178281355792484234102070365 66855508422181587788276387)
    ·
      refine ⟨100283262633272381682414581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66855508422181587788276387 100283262633272381682414581)
      ·
        refine ⟨9401555871869285782726367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 100283262633272381682414581 9401555871869285782726367)
        ·
          refine ⟨14102333807803928674089551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9401555871869285782726367 14102333807803928674089551)
          ·
            refine ⟨21153500711705893011134327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14102333807803928674089551 21153500711705893011134327)
            ·
              refine ⟨31730251067558839516701491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21153500711705893011134327 31730251067558839516701491)
              ·
                refine ⟨47595376601338259275052237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31730251067558839516701491 47595376601338259275052237)
                ·
                  refine ⟨17848266225501847228144589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47595376601338259275052237 17848266225501847228144589)
                  ·
                    refine ⟨6693099834563192710554221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17848266225501847228144589 6693099834563192710554221)
                    ·
                      refine ⟨2509912437961197266457833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6693099834563192710554221 2509912437961197266457833)
                      ·
                        rfl

theorem cell23_4888037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_4888037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4888037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4888037 prefixEnd_4888037 := by exact prefixLift 4888037
  have htrace : WordTrace (prefixWord ++ tailWord_4888037) baseStart_4888037 baseEnd_4888037 := by
    simpa [prefixWord, tailWord_4888037, baseEnd_4888037] using wordTrace_append hprefix tailTrace_4888037
  have hstable : (prefixWord ++ tailWord_4888037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4888037).length < 2 ^ (prefixWord ++ tailWord_4888037).sum := by decide
  have hdescent : baseEnd_4888037 < baseStart_4888037 := by decide
  rcases family_descends (prefixWord ++ tailWord_4888037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4888060 : List Nat := [2, 2, 2, 1, 2, 1, 3, 1, 2, 3, 4]
def baseStart_4888060 : Nat := 118140960795 + 4888060 * 2 ^ 59
def prefixEnd_4888060 : Nat := 4983230072969 + 3 ^ 40 * 4888060 * 2
def baseEnd_4888060 : Nat := 2509924248016250676470227

theorem tailTrace_4888060 : CollatzResearch.WordTrace tailWord_4888060 prefixEnd_4888060 2509924248016250676470227 := by
  unfold tailWord_4888060
  simp only [CollatzResearch.WordTrace]
  refine ⟨89141097335700454515078817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118854796447600606020105089 89141097335700454515078817)
  ·
    refine ⟨66855823001775340886309113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89141097335700454515078817 66855823001775340886309113)
    ·
      refine ⟨50141867251331505664731835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66855823001775340886309113 50141867251331505664731835)
      ·
        refine ⟨75212800876997258497097753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50141867251331505664731835 75212800876997258497097753)
        ·
          refine ⟨56409600657747943872823315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75212800876997258497097753 56409600657747943872823315)
          ·
            refine ⟨84614400986621915809234973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56409600657747943872823315 84614400986621915809234973)
            ·
              refine ⟨31730400369983218428463115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84614400986621915809234973 31730400369983218428463115)
              ·
                refine ⟨47595600554974827642694673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31730400369983218428463115 47595600554974827642694673)
                ·
                  refine ⟨35696700416231120732021005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47595600554974827642694673 35696700416231120732021005)
                  ·
                    refine ⟨13386262656086670274507877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35696700416231120732021005 13386262656086670274507877)
                    ·
                      refine ⟨2509924248016250676470227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13386262656086670274507877 2509924248016250676470227)
                      ·
                        rfl

theorem cell23_4888060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 1, 2, 3, 4].length) (baseStart_4888060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4888060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4888060 prefixEnd_4888060 := by exact prefixLift 4888060
  have htrace : WordTrace (prefixWord ++ tailWord_4888060) baseStart_4888060 baseEnd_4888060 := by
    simpa [prefixWord, tailWord_4888060, baseEnd_4888060] using wordTrace_append hprefix tailTrace_4888060
  have hstable : (prefixWord ++ tailWord_4888060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4888060).length < 2 ^ (prefixWord ++ tailWord_4888060).sum := by decide
  have hdescent : baseEnd_4888060 < baseStart_4888060 := by decide
  rcases family_descends (prefixWord ++ tailWord_4888060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4888090 : List Nat := [3, 1, 1, 3, 1, 1, 1, 1, 3, 4, 4]
def baseStart_4888090 : Nat := 118140960795 + 4888090 * 2 ^ 59
def prefixEnd_4888090 : Nat := 4983230072969 + 3 ^ 40 * 4888090 * 2
def baseEnd_4888090 : Nat := 2509939652435885559095089

theorem tailTrace_4888090 : CollatzResearch.WordTrace tailWord_4888090 prefixEnd_4888090 2509939652435885559095089 := by
  unfold tailWord_4888090
  simp only [CollatzResearch.WordTrace]
  refine ⟨44570822215323056038437431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118855525907528149435833149 44570822215323056038437431)
  ·
    refine ⟨66856233322984584057656147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44570822215323056038437431 66856233322984584057656147)
    ·
      refine ⟨100284349984476876086484221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66856233322984584057656147 100284349984476876086484221)
      ·
        refine ⟨37606631244178828532431583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100284349984476876086484221 37606631244178828532431583)
        ·
          refine ⟨56409946866268242798647375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37606631244178828532431583 56409946866268242798647375)
          ·
            refine ⟨84614920299402364197971063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56409946866268242798647375 84614920299402364197971063)
            ·
              refine ⟨126922380449103546296956595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84614920299402364197971063 126922380449103546296956595)
              ·
                refine ⟨190383570673655319445434893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126922380449103546296956595 190383570673655319445434893)
                ·
                  refine ⟨71393839002620744792038085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 190383570673655319445434893 71393839002620744792038085)
                  ·
                    refine ⟨13386344812991389648507141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 71393839002620744792038085 13386344812991389648507141)
                    ·
                      refine ⟨2509939652435885559095089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13386344812991389648507141 2509939652435885559095089)
                      ·
                        rfl

theorem cell23_4888090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 3, 4, 4].length) (baseStart_4888090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4888090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4888090 prefixEnd_4888090 := by exact prefixLift 4888090
  have htrace : WordTrace (prefixWord ++ tailWord_4888090) baseStart_4888090 baseEnd_4888090 := by
    simpa [prefixWord, tailWord_4888090, baseEnd_4888090] using wordTrace_append hprefix tailTrace_4888090
  have hstable : (prefixWord ++ tailWord_4888090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4888090).length < 2 ^ (prefixWord ++ tailWord_4888090).sum := by decide
  have hdescent : baseEnd_4888090 < baseStart_4888090 := by decide
  rcases family_descends (prefixWord ++ tailWord_4888090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4888117 : List Nat := [1, 3, 3, 1, 1, 4, 2, 1, 7]
def baseStart_4888117 : Nat := 118140960795 + 4888117 * 2 ^ 59
def prefixEnd_4888117 : Nat := 4983230072969 + 3 ^ 40 * 4888117 * 2
def baseEnd_4888117 : Nat := 278883724045950772606385

theorem tailTrace_4888117 : CollatzResearch.WordTrace tailWord_4888117 prefixEnd_4888117 278883724045950772606385 := by
  unfold tailWord_4888117
  simp only [CollatzResearch.WordTrace]
  refine ⟨178284273632194407764982605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118856182421462938509988403 178284273632194407764982605)
  ·
    refine ⟨66856602612072902911868477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 178284273632194407764982605 66856602612072902911868477)
    ·
      refine ⟨25071225979527338591950679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66856602612072902911868477 25071225979527338591950679)
      ·
        refine ⟨37606838969291007887926019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25071225979527338591950679 37606838969291007887926019)
        ·
          refine ⟨56410258453936511831889029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37606838969291007887926019 56410258453936511831889029)
          ·
            refine ⟨10576923460113095968479193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56410258453936511831889029 10576923460113095968479193)
            ·
              refine ⟨7932692595084821976359395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10576923460113095968479193 7932692595084821976359395)
              ·
                refine ⟨11899038892627232964539093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7932692595084821976359395 11899038892627232964539093)
                ·
                  refine ⟨278883724045950772606385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11899038892627232964539093 278883724045950772606385)
                  ·
                    rfl

theorem cell23_4888117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 2, 1, 7].length) (baseStart_4888117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4888117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4888117 prefixEnd_4888117 := by exact prefixLift 4888117
  have htrace : WordTrace (prefixWord ++ tailWord_4888117) baseStart_4888117 baseEnd_4888117 := by
    simpa [prefixWord, tailWord_4888117, baseEnd_4888117] using wordTrace_append hprefix tailTrace_4888117
  have hstable : (prefixWord ++ tailWord_4888117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4888117).length < 2 ^ (prefixWord ++ tailWord_4888117).sum := by decide
  have hdescent : baseEnd_4888117 < baseStart_4888117 := by decide
  rcases family_descends (prefixWord ++ tailWord_4888117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4888127 : List Nat := [1, 1, 2, 2, 3, 3, 2, 1, 2, 3, 3]
def baseStart_4888127 : Nat := 118140960795 + 4888127 * 2 ^ 59
def prefixEnd_4888127 : Nat := 4983230072969 + 3 ^ 40 * 4888127 * 2
def baseEnd_4888127 : Nat := 2509958651220101914332419

theorem tailTrace_4888127 : CollatzResearch.WordTrace tailWord_4888127 prefixEnd_4888127 2509958651220101914332419 := by
  unfold tailWord_4888127
  simp only [CollatzResearch.WordTrace]
  refine ⟨178284638362158179472846635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118856425574772119648564423 178284638362158179472846635)
  ·
    refine ⟨267426957543237269209269953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178284638362158179472846635 267426957543237269209269953)
    ·
      refine ⟨200570218157427951906952465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 267426957543237269209269953 200570218157427951906952465)
      ·
        refine ⟨150427663618070963930214349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 200570218157427951906952465 150427663618070963930214349)
        ·
          refine ⟨56410373856776611473830381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 150427663618070963930214349 56410373856776611473830381)
          ·
            refine ⟨21153890196291229302686393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56410373856776611473830381 21153890196291229302686393)
            ·
              refine ⟨15865417647218421977014795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21153890196291229302686393 15865417647218421977014795)
              ·
                refine ⟨23798126470827632965522193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15865417647218421977014795 23798126470827632965522193)
                ·
                  refine ⟨17848594853120724724141645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23798126470827632965522193 17848594853120724724141645)
                  ·
                    refine ⟨6693223069920271771553117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17848594853120724724141645 6693223069920271771553117)
                    ·
                      refine ⟨2509958651220101914332419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6693223069920271771553117 2509958651220101914332419)
                      ·
                        rfl

theorem cell23_4888127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 1, 2, 3, 3].length) (baseStart_4888127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4888127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4888127 prefixEnd_4888127 := by exact prefixLift 4888127
  have htrace : WordTrace (prefixWord ++ tailWord_4888127) baseStart_4888127 baseEnd_4888127 := by
    simpa [prefixWord, tailWord_4888127, baseEnd_4888127] using wordTrace_append hprefix tailTrace_4888127
  have hstable : (prefixWord ++ tailWord_4888127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4888127).length < 2 ^ (prefixWord ++ tailWord_4888127).sum := by decide
  have hdescent : baseEnd_4888127 < baseStart_4888127 := by decide
  rcases family_descends (prefixWord ++ tailWord_4888127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4888137 : List Nat := [1, 2, 1, 1, 2, 2, 1, 4, 2, 5, 2]
def baseStart_4888137 : Nat := 118140960795 + 4888137 * 2 ^ 59
def prefixEnd_4888137 : Nat := 4983230072969 + 3 ^ 40 * 4888137 * 2
def baseEnd_4888137 : Nat := 2509963786026646875207373

theorem tailTrace_4888137 : CollatzResearch.WordTrace tailWord_4888137 prefixEnd_4888137 2509963786026646875207373 := by
  unfold tailWord_4888137
  simp only [CollatzResearch.WordTrace]
  refine ⟨178285003092121951180710665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118856668728081300787140443 178285003092121951180710665)
  ·
    refine ⟨133713752319091463385532999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178285003092121951180710665 133713752319091463385532999)
    ·
      refine ⟨200570628478637195078299499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133713752319091463385532999 200570628478637195078299499)
      ·
        refine ⟨300855942717955792617449249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200570628478637195078299499 300855942717955792617449249)
        ·
          refine ⟨225641957038466844463086937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 300855942717955792617449249 225641957038466844463086937)
          ·
            refine ⟨169231467778850133347315203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 225641957038466844463086937 169231467778850133347315203)
            ·
              refine ⟨253847201668275200020972805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 169231467778850133347315203 253847201668275200020972805)
              ·
                refine ⟨47596350312801600003932401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 253847201668275200020972805 47596350312801600003932401)
                ·
                  refine ⟨35697262734601200002949301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47596350312801600003932401 35697262734601200002949301)
                  ·
                    refine ⟨3346618381368862500276497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35697262734601200002949301 3346618381368862500276497)
                    ·
                      refine ⟨2509963786026646875207373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3346618381368862500276497 2509963786026646875207373)
                      ·
                        rfl

theorem cell23_4888137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 4, 2, 5, 2].length) (baseStart_4888137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4888137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4888137 prefixEnd_4888137 := by exact prefixLift 4888137
  have htrace : WordTrace (prefixWord ++ tailWord_4888137) baseStart_4888137 baseEnd_4888137 := by
    simpa [prefixWord, tailWord_4888137, baseEnd_4888137] using wordTrace_append hprefix tailTrace_4888137
  have hstable : (prefixWord ++ tailWord_4888137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4888137).length < 2 ^ (prefixWord ++ tailWord_4888137).sum := by decide
  have hdescent : baseEnd_4888137 < baseStart_4888137 := by decide
  rcases family_descends (prefixWord ++ tailWord_4888137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4888167 : List Nat := [1, 1, 5, 1, 1, 1, 3, 1, 4, 1, 4]
def baseStart_4888167 : Nat := 118140960795 + 4888167 * 2 ^ 59
def prefixEnd_4888167 : Nat := 4983230072969 + 3 ^ 40 * 4888167 * 2
def baseEnd_4888167 : Nat := 2509979190446281757832235

theorem tailTrace_4888167 : CollatzResearch.WordTrace tailWord_4888167 prefixEnd_4888167 2509979190446281757832235 := by
  unfold tailWord_4888167
  simp only [CollatzResearch.WordTrace]
  refine ⟨178286097282013266304302755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118857398188008844202868503 178286097282013266304302755)
  ·
    refine ⟨267429145923019899456454133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178286097282013266304302755 267429145923019899456454133)
    ·
      refine ⟨25071482430283115574042575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 267429145923019899456454133 25071482430283115574042575)
      ·
        refine ⟨37607223645424673361063863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25071482430283115574042575 37607223645424673361063863)
        ·
          refine ⟨56410835468137010041595795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37607223645424673361063863 56410835468137010041595795)
          ·
            refine ⟨84616253202205515062393693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56410835468137010041595795 84616253202205515062393693)
            ·
              refine ⟨31731094950827068148397635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84616253202205515062393693 31731094950827068148397635)
              ·
                refine ⟨47596642426240602222596453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31731094950827068148397635 47596642426240602222596453)
                ·
                  refine ⟨8924370454920112916736835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47596642426240602222596453 8924370454920112916736835)
                  ·
                    refine ⟨13386555682380169375105253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8924370454920112916736835 13386555682380169375105253)
                    ·
                      refine ⟨2509979190446281757832235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13386555682380169375105253 2509979190446281757832235)
                      ·
                        rfl

theorem cell23_4888167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 1, 4, 1, 4].length) (baseStart_4888167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4888167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4888167 prefixEnd_4888167 := by exact prefixLift 4888167
  have htrace : WordTrace (prefixWord ++ tailWord_4888167) baseStart_4888167 baseEnd_4888167 := by
    simpa [prefixWord, tailWord_4888167, baseEnd_4888167] using wordTrace_append hprefix tailTrace_4888167
  have hstable : (prefixWord ++ tailWord_4888167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4888167).length < 2 ^ (prefixWord ++ tailWord_4888167).sum := by decide
  have hdescent : baseEnd_4888167 < baseStart_4888167 := by decide
  rcases family_descends (prefixWord ++ tailWord_4888167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4888174 : List Nat := [4, 1, 2, 2, 3, 1, 1, 1, 1, 2, 5]
def baseStart_4888174 : Nat := 118140960795 + 4888174 * 2 ^ 59
def prefixEnd_4888174 : Nat := 4983230072969 + 3 ^ 40 * 4888174 * 2
def baseEnd_4888174 : Nat := 2509982784810863230444703

theorem tailTrace_4888174 : CollatzResearch.WordTrace tailWord_4888174 prefixEnd_4888174 2509982784810863230444703 := by
  unfold tailWord_4888174
  simp only [CollatzResearch.WordTrace]
  refine ⟨22285794074123488312475947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118857568395325270999871717 22285794074123488312475947)
  ·
    refine ⟨33428691111185232468713921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22285794074123488312475947 33428691111185232468713921)
    ·
      refine ⟨25071518333388924351535441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33428691111185232468713921 25071518333388924351535441)
      ·
        refine ⟨18803638750041693263651581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25071518333388924351535441 18803638750041693263651581)
        ·
          refine ⟨7051364531265634973869343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18803638750041693263651581 7051364531265634973869343)
          ·
            refine ⟨10577046796898452460804015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7051364531265634973869343 10577046796898452460804015)
            ·
              refine ⟨15865570195347678691206023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10577046796898452460804015 15865570195347678691206023)
              ·
                refine ⟨23798355293021518036809035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15865570195347678691206023 23798355293021518036809035)
                ·
                  refine ⟨35697532939532277055213553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23798355293021518036809035 35697532939532277055213553)
                  ·
                    refine ⟨26773149704649207791410165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35697532939532277055213553 26773149704649207791410165)
                    ·
                      refine ⟨2509982784810863230444703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26773149704649207791410165 2509982784810863230444703)
                      ·
                        rfl

theorem cell23_4888174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 1, 1, 2, 5].length) (baseStart_4888174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4888174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4888174 prefixEnd_4888174 := by exact prefixLift 4888174
  have htrace : WordTrace (prefixWord ++ tailWord_4888174) baseStart_4888174 baseEnd_4888174 := by
    simpa [prefixWord, tailWord_4888174, baseEnd_4888174] using wordTrace_append hprefix tailTrace_4888174
  have hstable : (prefixWord ++ tailWord_4888174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4888174).length < 2 ^ (prefixWord ++ tailWord_4888174).sum := by decide
  have hdescent : baseEnd_4888174 < baseStart_4888174 := by decide
  rcases family_descends (prefixWord ++ tailWord_4888174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4888187 : List Nat := [1, 1, 1, 1, 1, 4, 3, 2, 4, 2, 3]
def baseStart_4888187 : Nat := 118140960795 + 4888187 * 2 ^ 59
def prefixEnd_4888187 : Nat := 4983230072969 + 3 ^ 40 * 4888187 * 2
def baseEnd_4888187 : Nat := 2509989460059371679582143

theorem tailTrace_4888187 : CollatzResearch.WordTrace tailWord_4888187 prefixEnd_4888187 2509989460059371679582143 := by
  unfold tailWord_4888187
  simp only [CollatzResearch.WordTrace]
  refine ⟨178286826741940809720030815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118857884494627206480020543 178286826741940809720030815)
  ·
    refine ⟨267430240112911214580046223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178286826741940809720030815 267430240112911214580046223)
    ·
      refine ⟨401145360169366821870069335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 267430240112911214580046223 401145360169366821870069335)
      ·
        refine ⟨601718040254050232805104003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 401145360169366821870069335 601718040254050232805104003)
        ·
          refine ⟨902577060381075349207656005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 601718040254050232805104003 902577060381075349207656005)
          ·
            refine ⟨169233198821451627976435501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 902577060381075349207656005 169233198821451627976435501)
            ·
              refine ⟨63462449558044360491163313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 169233198821451627976435501 63462449558044360491163313)
              ·
                refine ⟨47596837168533270368372485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63462449558044360491163313 47596837168533270368372485)
                ·
                  refine ⟨8924406969099988194069841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47596837168533270368372485 8924406969099988194069841)
                  ·
                    refine ⟨6693305226824991145552381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8924406969099988194069841 6693305226824991145552381)
                    ·
                      refine ⟨2509989460059371679582143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6693305226824991145552381 2509989460059371679582143)
                      ·
                        rfl

theorem cell23_4888187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 2, 4, 2, 3].length) (baseStart_4888187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4888187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4888187 prefixEnd_4888187 := by exact prefixLift 4888187
  have htrace : WordTrace (prefixWord ++ tailWord_4888187) baseStart_4888187 baseEnd_4888187 := by
    simpa [prefixWord, tailWord_4888187, baseEnd_4888187] using wordTrace_append hprefix tailTrace_4888187
  have hstable : (prefixWord ++ tailWord_4888187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4888187).length < 2 ^ (prefixWord ++ tailWord_4888187).sum := by decide
  have hdescent : baseEnd_4888187 < baseStart_4888187 := by decide
  rcases family_descends (prefixWord ++ tailWord_4888187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4888204 : List Nat := [2, 2, 1, 2, 1, 1, 6, 1, 2, 2, 3]
def baseStart_4888204 : Nat := 118140960795 + 4888204 * 2 ^ 59
def prefixEnd_4888204 : Nat := 4983230072969 + 3 ^ 40 * 4888204 * 2
def baseEnd_4888204 : Nat := 2509998189230498113069565

theorem tailTrace_4888204 : CollatzResearch.WordTrace tailWord_4888204 prefixEnd_4888204 2509998189230498113069565 := by
  unfold tailWord_4888204
  simp only [CollatzResearch.WordTrace]
  refine ⟨89143723391439610811699833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118858297855252814415599777 89143723391439610811699833)
  ·
    refine ⟨66857792543579708108774875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89143723391439610811699833 66857792543579708108774875)
    ·
      refine ⟨100286688815369562163162313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66857792543579708108774875 100286688815369562163162313)
      ·
        refine ⟨75215016611527171622371735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100286688815369562163162313 75215016611527171622371735)
        ·
          refine ⟨112822524917290757433557603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75215016611527171622371735 112822524917290757433557603)
          ·
            refine ⟨169233787375936136150336405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112822524917290757433557603 169233787375936136150336405)
            ·
              refine ⟨7932833783247006382047019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 169233787375936136150336405 7932833783247006382047019)
              ·
                refine ⟨11899250674870509573070529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7932833783247006382047019 11899250674870509573070529)
                ·
                  refine ⟨8924438006152882179802897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11899250674870509573070529 8924438006152882179802897)
                  ·
                    refine ⟨6693328504614661634852173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8924438006152882179802897 6693328504614661634852173)
                    ·
                      refine ⟨2509998189230498113069565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6693328504614661634852173 2509998189230498113069565)
                      ·
                        rfl

theorem cell23_4888204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 6, 1, 2, 2, 3].length) (baseStart_4888204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4888204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4888204 prefixEnd_4888204 := by exact prefixLift 4888204
  have htrace : WordTrace (prefixWord ++ tailWord_4888204) baseStart_4888204 baseEnd_4888204 := by
    simpa [prefixWord, tailWord_4888204, baseEnd_4888204] using wordTrace_append hprefix tailTrace_4888204
  have hstable : (prefixWord ++ tailWord_4888204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4888204).length < 2 ^ (prefixWord ++ tailWord_4888204).sum := by decide
  have hdescent : baseEnd_4888204 < baseStart_4888204 := by decide
  rcases family_descends (prefixWord ++ tailWord_4888204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4888224 : List Nat := [2, 1, 1, 4, 3, 2, 2, 2, 6]
def baseStart_4888224 : Nat := 118140960795 + 4888224 * 2 ^ 59
def prefixEnd_4888224 : Nat := 4983230072969 + 3 ^ 40 * 4888224 * 2
def baseEnd_4888224 : Nat := 278889828760398670535497

theorem tailTrace_4888224 : CollatzResearch.WordTrace tailWord_4888224 prefixEnd_4888224 278889828760398670535497 := by
  unfold tailWord_4888224
  simp only [CollatzResearch.WordTrace]
  refine ⟨89144088121403382519563863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118858784161871176692751817 89144088121403382519563863)
  ·
    refine ⟨133716132182105073779345795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89144088121403382519563863 133716132182105073779345795)
    ·
      refine ⟨200574198273157610669018693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133716132182105073779345795 200574198273157610669018693)
      ·
        refine ⟨37607662176217052000441005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 200574198273157610669018693 37607662176217052000441005)
        ·
          refine ⟨14102873316081394500165377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37607662176217052000441005 14102873316081394500165377)
          ·
            refine ⟨10577154987061045875124033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14102873316081394500165377 10577154987061045875124033)
            ·
              refine ⟨7932866240295784406343025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10577154987061045875124033 7932866240295784406343025)
              ·
                refine ⟨5949649680221838304757269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7932866240295784406343025 5949649680221838304757269)
                ·
                  refine ⟨278889828760398670535497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5949649680221838304757269 278889828760398670535497)
                  ·
                    rfl

theorem cell23_4888224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2, 2, 6].length) (baseStart_4888224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4888224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4888224 prefixEnd_4888224 := by exact prefixLift 4888224
  have htrace : WordTrace (prefixWord ++ tailWord_4888224) baseStart_4888224 baseEnd_4888224 := by
    simpa [prefixWord, tailWord_4888224, baseEnd_4888224] using wordTrace_append hprefix tailTrace_4888224
  have hstable : (prefixWord ++ tailWord_4888224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4888224).length < 2 ^ (prefixWord ++ tailWord_4888224).sum := by decide
  have hdescent : baseEnd_4888224 < baseStart_4888224 := by decide
  rcases family_descends (prefixWord ++ tailWord_4888224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4888228 : List Nat := [2, 3, 1, 2, 2, 2, 4, 2, 1, 4]
def baseStart_4888228 : Nat := 118140960795 + 4888228 * 2 ^ 59
def prefixEnd_4888228 : Nat := 4983230072969 + 3 ^ 40 * 4888228 * 2
def baseEnd_4888228 : Nat := 836670170922068673056485

theorem tailTrace_4888228 : CollatzResearch.WordTrace tailWord_4888228 prefixEnd_4888228 836670170922068673056485 := by
  unfold tailWord_4888228
  simp only [CollatzResearch.WordTrace]
  refine ⟨89144161067396136861136669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118858881423194849148182225 89144161067396136861136669)
  ·
    refine ⟨33429060400273551322926251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89144161067396136861136669 33429060400273551322926251)
    ·
      refine ⟨50143590600410326984389377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33429060400273551322926251 50143590600410326984389377)
      ·
        refine ⟨37607692950307745238292033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50143590600410326984389377 37607692950307745238292033)
        ·
          refine ⟨28205769712730808928719025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37607692950307745238292033 28205769712730808928719025)
          ·
            refine ⟨21154327284548106696539269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28205769712730808928719025 21154327284548106696539269)
            ·
              refine ⟨3966436365852770005601113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21154327284548106696539269 3966436365852770005601113)
              ·
                refine ⟨2974827274389577504200835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3966436365852770005601113 2974827274389577504200835)
                ·
                  refine ⟨4462240911584366256301253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2974827274389577504200835 4462240911584366256301253)
                  ·
                    refine ⟨836670170922068673056485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4462240911584366256301253 836670170922068673056485)
                    ·
                      rfl

theorem cell23_4888228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 4, 2, 1, 4].length) (baseStart_4888228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4888228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4888228 prefixEnd_4888228 := by exact prefixLift 4888228
  have htrace : WordTrace (prefixWord ++ tailWord_4888228) baseStart_4888228 baseEnd_4888228 := by
    simpa [prefixWord, tailWord_4888228, baseEnd_4888228] using wordTrace_append hprefix tailTrace_4888228
  have hstable : (prefixWord ++ tailWord_4888228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4888228).length < 2 ^ (prefixWord ++ tailWord_4888228).sum := by decide
  have hdescent : baseEnd_4888228 < baseStart_4888228 := by decide
  rcases family_descends (prefixWord ++ tailWord_4888228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4888254 : List Nat := [4, 2, 1, 1, 2, 2, 2, 1, 3, 5]
def baseStart_4888254 : Nat := 118140960795 + 4888254 * 2 ^ 59
def prefixEnd_4888254 : Nat := 4983230072969 + 3 ^ 40 * 4888254 * 2
def baseEnd_4888254 : Nat := 836674621087740972481445

theorem tailTrace_4888254 : CollatzResearch.WordTrace tailWord_4888254 prefixEnd_4888254 836674621087740972481445 := by
  unfold tailWord_4888254
  simp only [CollatzResearch.WordTrace]
  refine ⟨22286158804087260020339977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118859513621798720108479877 22286158804087260020339977)
  ·
    refine ⟨16714619103065445015254983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22286158804087260020339977 16714619103065445015254983)
    ·
      refine ⟨25071928654598167522882475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16714619103065445015254983 25071928654598167522882475)
      ·
        refine ⟨37607892981897251284323713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25071928654598167522882475 37607892981897251284323713)
        ·
          refine ⟨28205919736422938463242785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37607892981897251284323713 28205919736422938463242785)
          ·
            refine ⟨21154439802317203847432089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28205919736422938463242785 21154439802317203847432089)
            ·
              refine ⟨15865829851737902885574067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21154439802317203847432089 15865829851737902885574067)
              ·
                refine ⟨23798744777606854328361101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15865829851737902885574067 23798744777606854328361101)
                ·
                  refine ⟨8924529291602570373135413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23798744777606854328361101 8924529291602570373135413)
                  ·
                    refine ⟨836674621087740972481445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8924529291602570373135413 836674621087740972481445)
                    ·
                      rfl

theorem cell23_4888254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 1, 3, 5].length) (baseStart_4888254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4888254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4888254 prefixEnd_4888254 := by exact prefixLift 4888254
  have htrace : WordTrace (prefixWord ++ tailWord_4888254) baseStart_4888254 baseEnd_4888254 := by
    simpa [prefixWord, tailWord_4888254, baseEnd_4888254] using wordTrace_append hprefix tailTrace_4888254
  have hstable : (prefixWord ++ tailWord_4888254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4888254).length < 2 ^ (prefixWord ++ tailWord_4888254).sum := by decide
  have hdescent : baseEnd_4888254 < baseStart_4888254 := by decide
  rcases family_descends (prefixWord ++ tailWord_4888254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4888262 : List Nat := [6, 1, 2, 1, 1, 2, 2, 3, 1, 4]
def baseStart_4888262 : Nat := 118140960795 + 4888262 * 2 ^ 59
def prefixEnd_4888262 : Nat := 4983230072969 + 3 ^ 40 * 4888262 * 2
def baseEnd_4888262 : Nat := 836675990369486295381433

theorem tailTrace_4888262 : CollatzResearch.WordTrace tailWord_4888262 prefixEnd_4888262 836675990369486295381433 := by
  unfold tailWord_4888262
  simp only [CollatzResearch.WordTrace]
  refine ⟨5571548819270909297781595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 118859708144446065019340693 5571548819270909297781595)
  ·
    refine ⟨8357323228906363946672393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5571548819270909297781595 8357323228906363946672393)
    ·
      refine ⟨6267992421679772960004295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8357323228906363946672393 6267992421679772960004295)
      ·
        refine ⟨9401988632519659440006443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6267992421679772960004295 9401988632519659440006443)
        ·
          refine ⟨14102982948779489160009665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9401988632519659440006443 14102982948779489160009665)
          ·
            refine ⟨10577237211584616870007249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14102982948779489160009665 10577237211584616870007249)
            ·
              refine ⟨7932927908688462652505437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10577237211584616870007249 7932927908688462652505437)
              ·
                refine ⟨2974847965758173494689539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7932927908688462652505437 2974847965758173494689539)
                ·
                  refine ⟨4462271948637260242034309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2974847965758173494689539 4462271948637260242034309)
                  ·
                    refine ⟨836675990369486295381433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4462271948637260242034309 836675990369486295381433)
                    ·
                      rfl

theorem cell23_4888262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_4888262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4888262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4888262 prefixEnd_4888262 := by exact prefixLift 4888262
  have htrace : WordTrace (prefixWord ++ tailWord_4888262) baseStart_4888262 baseEnd_4888262 := by
    simpa [prefixWord, tailWord_4888262, baseEnd_4888262] using wordTrace_append hprefix tailTrace_4888262
  have hstable : (prefixWord ++ tailWord_4888262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4888262).length < 2 ^ (prefixWord ++ tailWord_4888262).sum := by decide
  have hdescent : baseEnd_4888262 < baseStart_4888262 := by decide
  rcases family_descends (prefixWord ++ tailWord_4888262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4888285 : List Nat := [1, 4, 3, 3, 1, 1, 2, 1, 3, 1, 3]
def baseStart_4888285 : Nat := 118140960795 + 4888285 * 2 ^ 59
def prefixEnd_4888285 : Nat := 4983230072969 + 3 ^ 40 * 4888285 * 2
def baseEnd_4888285 : Nat := 2510039781163512296156693

theorem tailTrace_4888285 : CollatzResearch.WordTrace tailWord_4888285 prefixEnd_4888285 2510039781163512296156693 := by
  unfold tailWord_4888285
  simp only [CollatzResearch.WordTrace]
  refine ⟨178290401095585772457098309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118860267397057181638065539 178290401095585772457098309)
  ·
    refine ⟨33429450205422332335705933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 178290401095585772457098309 33429450205422332335705933)
    ·
      refine ⟨12536043827033374625889725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33429450205422332335705933 12536043827033374625889725)
      ·
        refine ⟨4701016435137515484708647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12536043827033374625889725 4701016435137515484708647)
        ·
          refine ⟨7051524652706273227062971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4701016435137515484708647 7051524652706273227062971)
          ·
            refine ⟨10577286979059409840594457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7051524652706273227062971 10577286979059409840594457)
            ·
              refine ⟨7932965234294557380445843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10577286979059409840594457 7932965234294557380445843)
              ·
                refine ⟨11899447851441836070668765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7932965234294557380445843 11899447851441836070668765)
                ·
                  refine ⟨4462292944290688526500787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11899447851441836070668765 4462292944290688526500787)
                  ·
                    refine ⟨6693439416436032789751181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4462292944290688526500787 6693439416436032789751181)
                    ·
                      refine ⟨2510039781163512296156693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6693439416436032789751181 2510039781163512296156693)
                      ·
                        rfl

theorem cell23_4888285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_4888285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4888285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4888285 prefixEnd_4888285 := by exact prefixLift 4888285
  have htrace : WordTrace (prefixWord ++ tailWord_4888285) baseStart_4888285 baseEnd_4888285 := by
    simpa [prefixWord, tailWord_4888285, baseEnd_4888285] using wordTrace_append hprefix tailTrace_4888285
  have hstable : (prefixWord ++ tailWord_4888285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4888285).length < 2 ^ (prefixWord ++ tailWord_4888285).sum := by decide
  have hdescent : baseEnd_4888285 < baseStart_4888285 := by decide
  rcases family_descends (prefixWord ++ tailWord_4888285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4888287 : List Nat := [1, 1, 2, 3, 2, 2, 2, 2, 1, 1, 6]
def baseStart_4888287 : Nat := 118140960795 + 4888287 * 2 ^ 59
def prefixEnd_4888287 : Nat := 4983230072969 + 3 ^ 40 * 4888287 * 2
def baseEnd_4888287 : Nat := 2510040808124821288331683

theorem tailTrace_4888287 : CollatzResearch.WordTrace tailWord_4888287 prefixEnd_4888287 2510040808124821288331683 := by
  unfold tailWord_4888287
  simp only [CollatzResearch.WordTrace]
  refine ⟨178290474041578526798671115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118860316027719017865780743 178290474041578526798671115)
  ·
    refine ⟨267435711062367790198006673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178290474041578526798671115 267435711062367790198006673)
    ·
      refine ⟨200576783296775842648505005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 267435711062367790198006673 200576783296775842648505005)
      ·
        refine ⟨75216293736290940993189377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 200576783296775842648505005 75216293736290940993189377)
        ·
          refine ⟨56412220302218205744892033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75216293736290940993189377 56412220302218205744892033)
          ·
            refine ⟨42309165226663654308669025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56412220302218205744892033 42309165226663654308669025)
            ·
              refine ⟨31731873919997740731501769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42309165226663654308669025 31731873919997740731501769)
              ·
                refine ⟨23798905439998305548626327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31731873919997740731501769 23798905439998305548626327)
                ·
                  refine ⟨35698358159997458322939491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23798905439998305548626327 35698358159997458322939491)
                  ·
                    refine ⟨53547537239996187484409237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35698358159997458322939491 53547537239996187484409237)
                    ·
                      refine ⟨2510040808124821288331683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53547537239996187484409237 2510040808124821288331683)
                      ·
                        rfl

theorem cell23_4888287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 2, 1, 1, 6].length) (baseStart_4888287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4888287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4888287 prefixEnd_4888287 := by exact prefixLift 4888287
  have htrace : WordTrace (prefixWord ++ tailWord_4888287) baseStart_4888287 baseEnd_4888287 := by
    simpa [prefixWord, tailWord_4888287, baseEnd_4888287] using wordTrace_append hprefix tailTrace_4888287
  have hstable : (prefixWord ++ tailWord_4888287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4888287).length < 2 ^ (prefixWord ++ tailWord_4888287).sum := by decide
  have hdescent : baseEnd_4888287 < baseStart_4888287 := by decide
  rcases family_descends (prefixWord ++ tailWord_4888287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4888301 : List Nat := [1, 5, 1, 2, 1, 4, 1, 1, 1, 6]
def baseStart_4888301 : Nat := 118140960795 + 4888301 * 2 ^ 59
def prefixEnd_4888301 : Nat := 4983230072969 + 3 ^ 40 * 4888301 * 2
def baseEnd_4888301 : Nat := 836682665617994744518873

theorem tailTrace_4888301 : CollatzResearch.WordTrace tailWord_4888301 prefixEnd_4888301 836682665617994744518873 := by
  unfold tailWord_4888301
  simp only [CollatzResearch.WordTrace]
  refine ⟨178290984663527807189680757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118860656442351871459787171 178290984663527807189680757)
  ·
    refine ⟨16714779812205731924032571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 178290984663527807189680757 16714779812205731924032571)
    ·
      refine ⟨25072169718308597886048857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16714779812205731924032571 25072169718308597886048857)
      ·
        refine ⟨18804127288731448414536643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25072169718308597886048857 18804127288731448414536643)
        ·
          refine ⟨28206190933097172621804965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18804127288731448414536643 28206190933097172621804965)
          ·
            refine ⟨5288660799955719866588431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28206190933097172621804965 5288660799955719866588431)
            ·
              refine ⟨7932991199933579799882647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5288660799955719866588431 7932991199933579799882647)
              ·
                refine ⟨11899486799900369699823971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7932991199933579799882647 11899486799900369699823971)
                ·
                  refine ⟨17849230199850554549735957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11899486799900369699823971 17849230199850554549735957)
                  ·
                    refine ⟨836682665617994744518873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17849230199850554549735957 836682665617994744518873)
                    ·
                      rfl

theorem cell23_4888301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 1, 1, 1, 6].length) (baseStart_4888301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4888301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4888301 prefixEnd_4888301 := by exact prefixLift 4888301
  have htrace : WordTrace (prefixWord ++ tailWord_4888301) baseStart_4888301 baseEnd_4888301 := by
    simpa [prefixWord, tailWord_4888301, baseEnd_4888301] using wordTrace_append hprefix tailTrace_4888301
  have hstable : (prefixWord ++ tailWord_4888301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4888301).length < 2 ^ (prefixWord ++ tailWord_4888301).sum := by decide
  have hdescent : baseEnd_4888301 < baseStart_4888301 := by decide
  rcases family_descends (prefixWord ++ tailWord_4888301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4888337 : List Nat := [1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 5]
def baseStart_4888337 : Nat := 118140960795 + 4888337 * 2 ^ 59
def prefixEnd_4888337 : Nat := 4983230072969 + 3 ^ 40 * 4888337 * 2
def baseEnd_4888337 : Nat := 2510066482157546092706453

theorem tailTrace_4888337 : CollatzResearch.WordTrace tailWord_4888337 prefixEnd_4888337 2510066482157546092706453 := by
  unfold tailWord_4888337
  simp only [CollatzResearch.WordTrace]
  refine ⟨178292297691397385337991265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118861531794264923558660843 178292297691397385337991265)
  ·
    refine ⟨133719223268548039003493449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178292297691397385337991265 133719223268548039003493449)
    ·
      refine ⟨100289417451411029252620087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133719223268548039003493449 100289417451411029252620087)
      ·
        refine ⟨150434126177116543878930131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100289417451411029252620087 150434126177116543878930131)
        ·
          refine ⟨225651189265674815818395197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150434126177116543878930131 225651189265674815818395197)
          ·
            refine ⟨84619195974628055931898199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 225651189265674815818395197 84619195974628055931898199)
            ·
              refine ⟨126928793961942083897847299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84619195974628055931898199 126928793961942083897847299)
              ·
                refine ⟨190393190942913125846770949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126928793961942083897847299 190393190942913125846770949)
                ·
                  refine ⟨35698723301796211096269553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 190393190942913125846770949 35698723301796211096269553)
                  ·
                    refine ⟨26774042476347158322202165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35698723301796211096269553 26774042476347158322202165)
                    ·
                      refine ⟨2510066482157546092706453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26774042476347158322202165 2510066482157546092706453)
                      ·
                        rfl

theorem cell23_4888337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 5].length) (baseStart_4888337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4888337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4888337 prefixEnd_4888337 := by exact prefixLift 4888337
  have htrace : WordTrace (prefixWord ++ tailWord_4888337) baseStart_4888337 baseEnd_4888337 := by
    simpa [prefixWord, tailWord_4888337, baseEnd_4888337] using wordTrace_append hprefix tailTrace_4888337
  have hstable : (prefixWord ++ tailWord_4888337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4888337).length < 2 ^ (prefixWord ++ tailWord_4888337).sum := by decide
  have hdescent : baseEnd_4888337 < baseStart_4888337 := by decide
  rcases family_descends (prefixWord ++ tailWord_4888337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4888341 : List Nat := [1, 3, 2, 1, 2, 3, 2, 1, 4, 1, 3]
def baseStart_4888341 : Nat := 118140960795 + 4888341 * 2 ^ 59
def prefixEnd_4888341 : Nat := 4983230072969 + 3 ^ 40 * 4888341 * 2
def baseEnd_4888341 : Nat := 2510068536080164077056435

theorem tailTrace_4888341 : CollatzResearch.WordTrace tailWord_4888341 prefixEnd_4888341 2510068536080164077056435 := by
  unfold tailWord_4888341
  simp only [CollatzResearch.WordTrace]
  refine ⟨178292443583382894021136877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118861629055588596014091251 178292443583382894021136877)
  ·
    refine ⟨66859666343768585257926329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 178292443583382894021136877 66859666343768585257926329)
    ·
      refine ⟨50144749757826438943444747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66859666343768585257926329 50144749757826438943444747)
      ·
        refine ⟨75217124636739658415167121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50144749757826438943444747 75217124636739658415167121)
        ·
          refine ⟨56412843477554743811375341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75217124636739658415167121 56412843477554743811375341)
          ·
            refine ⟨21154816304083028929265753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56412843477554743811375341 21154816304083028929265753)
            ·
              refine ⟨15866112228062271696949315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21154816304083028929265753 15866112228062271696949315)
              ·
                refine ⟨23799168342093407545423973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15866112228062271696949315 23799168342093407545423973)
                ·
                  refine ⟨4462344064142513914766995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23799168342093407545423973 4462344064142513914766995)
                  ·
                    refine ⟨6693516096213770872150493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4462344064142513914766995 6693516096213770872150493)
                    ·
                      refine ⟨2510068536080164077056435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6693516096213770872150493 2510068536080164077056435)
                      ·
                        rfl

theorem cell23_4888341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 1, 4, 1, 3].length) (baseStart_4888341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4888341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4888341 prefixEnd_4888341 := by exact prefixLift 4888341
  have htrace : WordTrace (prefixWord ++ tailWord_4888341) baseStart_4888341 baseEnd_4888341 := by
    simpa [prefixWord, tailWord_4888341, baseEnd_4888341] using wordTrace_append hprefix tailTrace_4888341
  have hstable : (prefixWord ++ tailWord_4888341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4888341).length < 2 ^ (prefixWord ++ tailWord_4888341).sum := by decide
  have hdescent : baseEnd_4888341 < baseStart_4888341 := by decide
  rcases family_descends (prefixWord ++ tailWord_4888341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4888347 : List Nat := [1, 1, 1, 1, 1, 1, 4, 3, 1, 5, 4]
def baseStart_4888347 : Nat := 118140960795 + 4888347 * 2 ^ 59
def prefixEnd_4888347 : Nat := 4983230072969 + 3 ^ 40 * 4888347 * 2
def baseEnd_4888347 : Nat := 2510071616964091053581407

theorem tailTrace_4888347 : CollatzResearch.WordTrace tailWord_4888347 prefixEnd_4888347 2510071616964091053581407 := by
  unfold tailWord_4888347
  simp only [CollatzResearch.WordTrace]
  refine ⟨178292662421361157045855295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118861774947574104697236863 178292662421361157045855295)
  ·
    refine ⟨267438993632041735568782943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178292662421361157045855295 267438993632041735568782943)
    ·
      refine ⟨401158490448062603353174415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 267438993632041735568782943 401158490448062603353174415)
      ·
        refine ⟨601737735672093905029761623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 401158490448062603353174415 601737735672093905029761623)
        ·
          refine ⟨902606603508140857544642435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 601737735672093905029761623 902606603508140857544642435)
          ·
            refine ⟨1353909905262211286316963653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 902606603508140857544642435 1353909905262211286316963653)
            ·
              refine ⟨253858107236664616184430685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1353909905262211286316963653 253858107236664616184430685)
              ·
                refine ⟨95196790213749231069161507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 253858107236664616184430685 95196790213749231069161507)
                ·
                  refine ⟨142795185320623846603742261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 95196790213749231069161507 142795185320623846603742261)
                  ·
                    refine ⟨13387048623808485619100837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 142795185320623846603742261 13387048623808485619100837)
                    ·
                      refine ⟨2510071616964091053581407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13387048623808485619100837 2510071616964091053581407)
                      ·
                        rfl

theorem cell23_4888347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 5, 4].length) (baseStart_4888347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4888347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4888347 prefixEnd_4888347 := by exact prefixLift 4888347
  have htrace : WordTrace (prefixWord ++ tailWord_4888347) baseStart_4888347 baseEnd_4888347 := by
    simpa [prefixWord, tailWord_4888347, baseEnd_4888347] using wordTrace_append hprefix tailTrace_4888347
  have hstable : (prefixWord ++ tailWord_4888347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4888347).length < 2 ^ (prefixWord ++ tailWord_4888347).sum := by decide
  have hdescent : baseEnd_4888347 < baseStart_4888347 := by decide
  rcases family_descends (prefixWord ++ tailWord_4888347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4888351 : List Nat := [1, 1, 2, 4, 2, 1, 2, 2, 3, 3, 2]
def baseStart_4888351 : Nat := 118140960795 + 4888351 * 2 ^ 59
def prefixEnd_4888351 : Nat := 4983230072969 + 3 ^ 40 * 4888351 * 2
def baseEnd_4888351 : Nat := 2510073670886709037931389

theorem tailTrace_4888351 : CollatzResearch.WordTrace tailWord_4888351 prefixEnd_4888351 2510073670886709037931389 := by
  unfold tailWord_4888351
  simp only [CollatzResearch.WordTrace]
  refine ⟨178292808313346665729000907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118861872208897777152667271 178292808313346665729000907)
  ·
    refine ⟨267439212470019998593501361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178292808313346665729000907 267439212470019998593501361)
    ·
      refine ⟨200579409352514998945126021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 267439212470019998593501361 200579409352514998945126021)
      ·
        refine ⟨37608639253596562302211129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 200579409352514998945126021 37608639253596562302211129)
        ·
          refine ⟨28206479440197421726658347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37608639253596562302211129 28206479440197421726658347)
          ·
            refine ⟨42309719160296132589987521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28206479440197421726658347 42309719160296132589987521)
            ·
              refine ⟨31732289370222099442490641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42309719160296132589987521 31732289370222099442490641)
              ·
                refine ⟨23799217027666574581867981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31732289370222099442490641 23799217027666574581867981)
                ·
                  refine ⟨8924706385374965468200493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23799217027666574581867981 8924706385374965468200493)
                  ·
                    refine ⟨3346764894515612050575185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8924706385374965468200493 3346764894515612050575185)
                    ·
                      refine ⟨2510073670886709037931389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3346764894515612050575185 2510073670886709037931389)
                      ·
                        rfl

theorem cell23_4888351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 2, 3, 3, 2].length) (baseStart_4888351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4888351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4888351 prefixEnd_4888351 := by exact prefixLift 4888351
  have htrace : WordTrace (prefixWord ++ tailWord_4888351) baseStart_4888351 baseEnd_4888351 := by
    simpa [prefixWord, tailWord_4888351, baseEnd_4888351] using wordTrace_append hprefix tailTrace_4888351
  have hstable : (prefixWord ++ tailWord_4888351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4888351).length < 2 ^ (prefixWord ++ tailWord_4888351).sum := by decide
  have hdescent : baseEnd_4888351 < baseStart_4888351 := by decide
  rcases family_descends (prefixWord ++ tailWord_4888351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4888367 : List Nat := [1, 1, 2, 1, 2, 1, 2, 2, 3, 3, 5]
def baseStart_4888367 : Nat := 118140960795 + 4888367 * 2 ^ 59
def prefixEnd_4888367 : Nat := 4983230072969 + 3 ^ 40 * 4888367 * 2
def baseEnd_4888367 : Nat := 2510081886577180975331315

theorem tailTrace_4888367 : CollatzResearch.WordTrace tailWord_4888367 prefixEnd_4888367 2510081886577180975331315 := by
  unfold tailWord_4888367
  simp only [CollatzResearch.WordTrace]
  refine ⟨178293391881288700461583355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118862261254192466974388903 178293391881288700461583355)
  ·
    refine ⟨267440087821933050692375033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178293391881288700461583355 267440087821933050692375033)
    ·
      refine ⟨200580065866449788019281275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 267440087821933050692375033 200580065866449788019281275)
      ·
        refine ⟨300870098799674682028921913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200580065866449788019281275 300870098799674682028921913)
        ·
          refine ⟨225652574099756011521691435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 300870098799674682028921913 225652574099756011521691435)
          ·
            refine ⟨338478861149634017282537153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 225652574099756011521691435 338478861149634017282537153)
            ·
              refine ⟨253859145862225512961902865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 338478861149634017282537153 253859145862225512961902865)
              ·
                refine ⟨190394359396669134721427149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 253859145862225512961902865 190394359396669134721427149)
                ·
                  refine ⟨71397884773750925520535181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 190394359396669134721427149 71397884773750925520535181)
                  ·
                    refine ⟨26774206790156597070200693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 71397884773750925520535181 26774206790156597070200693)
                    ·
                      refine ⟨2510081886577180975331315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26774206790156597070200693 2510081886577180975331315)
                      ·
                        rfl

theorem cell23_4888367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 3, 3, 5].length) (baseStart_4888367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4888367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4888367 prefixEnd_4888367 := by exact prefixLift 4888367
  have htrace : WordTrace (prefixWord ++ tailWord_4888367) baseStart_4888367 baseEnd_4888367 := by
    simpa [prefixWord, tailWord_4888367, baseEnd_4888367] using wordTrace_append hprefix tailTrace_4888367
  have hstable : (prefixWord ++ tailWord_4888367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4888367).length < 2 ^ (prefixWord ++ tailWord_4888367).sum := by decide
  have hdescent : baseEnd_4888367 < baseStart_4888367 := by decide
  rcases family_descends (prefixWord ++ tailWord_4888367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4888394 : List Nat := [3, 1, 2, 1, 1, 1, 4, 2, 2, 2, 4]
def baseStart_4888394 : Nat := 118140960795 + 4888394 * 2 ^ 59
def prefixEnd_4888394 : Nat := 4983230072969 + 3 ^ 40 * 4888394 * 2
def baseEnd_4888394 : Nat := 2510095750554852369693691

theorem tailTrace_4888394 : CollatzResearch.WordTrace tailWord_4888394 prefixEnd_4888394 2510095750554852369693691 := by
  unfold tailWord_4888394
  simp only [CollatzResearch.WordTrace]
  refine ⟨44573594163047721018204059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118862917768127256048544157 44573594163047721018204059)
  ·
    refine ⟨66860391244571581527306089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44573594163047721018204059 66860391244571581527306089)
    ·
      refine ⟨50145293433428686145479567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66860391244571581527306089 50145293433428686145479567)
      ·
        refine ⟨75217940150143029218219351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50145293433428686145479567 75217940150143029218219351)
        ·
          refine ⟨112826910225214543827329027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75217940150143029218219351 112826910225214543827329027)
          ·
            refine ⟨169240365337821815740993541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112826910225214543827329027 169240365337821815740993541)
            ·
              refine ⟨31732568500841590451436289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 169240365337821815740993541 31732568500841590451436289)
              ·
                refine ⟨23799426375631192838577217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31732568500841590451436289 23799426375631192838577217)
                ·
                  refine ⟨17849569781723394628932913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23799426375631192838577217 17849569781723394628932913)
                  ·
                    refine ⟨13387177336292545971699685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17849569781723394628932913 13387177336292545971699685)
                    ·
                      refine ⟨2510095750554852369693691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13387177336292545971699685 2510095750554852369693691)
                      ·
                        rfl

theorem cell23_4888394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 2, 2, 2, 4].length) (baseStart_4888394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4888394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4888394 prefixEnd_4888394 := by exact prefixLift 4888394
  have htrace : WordTrace (prefixWord ++ tailWord_4888394) baseStart_4888394 baseEnd_4888394 := by
    simpa [prefixWord, tailWord_4888394, baseEnd_4888394] using wordTrace_append hprefix tailTrace_4888394
  have hstable : (prefixWord ++ tailWord_4888394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4888394).length < 2 ^ (prefixWord ++ tailWord_4888394).sum := by decide
  have hdescent : baseEnd_4888394 < baseStart_4888394 := by decide
  rcases family_descends (prefixWord ++ tailWord_4888394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4888449 : List Nat := [1, 2, 4, 4, 1, 2, 1, 2, 2, 2, 2]
def baseStart_4888449 : Nat := 118140960795 + 4888449 * 2 ^ 59
def prefixEnd_4888449 : Nat := 4983230072969 + 3 ^ 40 * 4888449 * 2
def baseEnd_4888449 : Nat := 2510123991990849654505939

theorem tailTrace_4888449 : CollatzResearch.WordTrace tailWord_4888449 prefixEnd_4888449 2510123991990849654505939 := by
  unfold tailWord_4888449
  simp only [CollatzResearch.WordTrace]
  refine ⟨178296382666991628466068401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118864255111327752310712267 178296382666991628466068401)
  ·
    refine ⟨133722287000243721349551301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178296382666991628466068401 133722287000243721349551301)
    ·
      refine ⟨25072928812545697753040869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 133722287000243721349551301 25072928812545697753040869)
      ·
        refine ⟨4701174152352318328695163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25072928812545697753040869 4701174152352318328695163)
        ·
          refine ⟨7051761228528477493042745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4701174152352318328695163 7051761228528477493042745)
          ·
            refine ⟨5288820921396358119782059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7051761228528477493042745 5288820921396358119782059)
            ·
              refine ⟨7933231382094537179673089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5288820921396358119782059 7933231382094537179673089)
              ·
                refine ⟨5949923536570902884754817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7933231382094537179673089 5949923536570902884754817)
                ·
                  refine ⟨4462442652428177163566113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5949923536570902884754817 4462442652428177163566113)
                  ·
                    refine ⟨3346831989321132872674585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4462442652428177163566113 3346831989321132872674585)
                    ·
                      refine ⟨2510123991990849654505939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3346831989321132872674585 2510123991990849654505939)
                      ·
                        rfl

theorem cell23_4888449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_4888449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4888449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4888449 prefixEnd_4888449 := by exact prefixLift 4888449
  have htrace : WordTrace (prefixWord ++ tailWord_4888449) baseStart_4888449 baseEnd_4888449 := by
    simpa [prefixWord, tailWord_4888449, baseEnd_4888449] using wordTrace_append hprefix tailTrace_4888449
  have hstable : (prefixWord ++ tailWord_4888449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4888449).length < 2 ^ (prefixWord ++ tailWord_4888449).sum := by decide
  have hdescent : baseEnd_4888449 < baseStart_4888449 := by decide
  rcases family_descends (prefixWord ++ tailWord_4888449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4888566 : List Nat := [5, 1, 1, 1, 5, 1, 2, 2, 1, 4]
def baseStart_4888566 : Nat := 118140960795 + 4888566 * 2 ^ 59
def prefixEnd_4888566 : Nat := 4983230072969 + 3 ^ 40 * 4888566 * 2
def baseEnd_4888566 : Nat := 836728023075808565580967

theorem tailTrace_4888566 : CollatzResearch.WordTrace tailWord_4888566 prefixEnd_4888566 836728023075808565580967 := by
  unfold tailWord_4888566
  simp only [CollatzResearch.WordTrace]
  refine ⟨11143790625472984840504847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 118867100005045171632051701 11143790625472984840504847)
  ·
    refine ⟨16715685938209477260757271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11143790625472984840504847 16715685938209477260757271)
    ·
      refine ⟨25073528907314215891135907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16715685938209477260757271 25073528907314215891135907)
      ·
        refine ⟨37610293360971323836703861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25073528907314215891135907 37610293360971323836703861)
        ·
          refine ⟨3525965002591061609690987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 37610293360971323836703861 3525965002591061609690987)
          ·
            refine ⟨5288947503886592414536481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3525965002591061609690987 5288947503886592414536481)
            ·
              refine ⟨3966710627914944310902361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5288947503886592414536481 3966710627914944310902361)
              ·
                refine ⟨2975032970936208233176771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3966710627914944310902361 2975032970936208233176771)
                ·
                  refine ⟨4462549456404312349765157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2975032970936208233176771 4462549456404312349765157)
                  ·
                    refine ⟨836728023075808565580967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4462549456404312349765157 836728023075808565580967)
                    ·
                      rfl

theorem cell23_4888566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 2, 2, 1, 4].length) (baseStart_4888566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4888566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4888566 prefixEnd_4888566 := by exact prefixLift 4888566
  have htrace : WordTrace (prefixWord ++ tailWord_4888566) baseStart_4888566 baseEnd_4888566 := by
    simpa [prefixWord, tailWord_4888566, baseEnd_4888566] using wordTrace_append hprefix tailTrace_4888566
  have hstable : (prefixWord ++ tailWord_4888566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4888566).length < 2 ^ (prefixWord ++ tailWord_4888566).sum := by decide
  have hdescent : baseEnd_4888566 < baseStart_4888566 := by decide
  rcases family_descends (prefixWord ++ tailWord_4888566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4888571 : List Nat := [1, 1, 1, 1, 1, 3, 4, 3, 4, 4]
def baseStart_4888571 : Nat := 118140960795 + 4888571 * 2 ^ 59
def prefixEnd_4888571 : Nat := 4983230072969 + 3 ^ 40 * 4888571 * 2
def baseEnd_4888571 : Nat := 836728878876899392393459

theorem tailTrace_4888571 : CollatzResearch.WordTrace tailWord_4888571 prefixEnd_4888571 836728878876899392393459 := by
  unfold tailWord_4888571
  simp only [CollatzResearch.WordTrace]
  refine ⟨178300832372549643302009567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118867221581699762201339711 178300832372549643302009567)
  ·
    refine ⟨267451248558824464953014351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178300832372549643302009567 267451248558824464953014351)
    ·
      refine ⟨401176872838236697429521527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 267451248558824464953014351 401176872838236697429521527)
      ·
        refine ⟨601765309257355046144282291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 401176872838236697429521527 601765309257355046144282291)
        ·
          refine ⟨902647963886032569216423437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 601765309257355046144282291 902647963886032569216423437)
          ·
            refine ⟨338492986457262213456158789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 902647963886032569216423437 338492986457262213456158789)
            ·
              refine ⟨63467434960736665023029773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 338492986457262213456158789 63467434960736665023029773)
              ·
                refine ⟨23800288110276249383636165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63467434960736665023029773 23800288110276249383636165)
                ·
                  refine ⟨4462554020676796759431781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23800288110276249383636165 4462554020676796759431781)
                  ·
                    refine ⟨836728878876899392393459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4462554020676796759431781 836728878876899392393459)
                    ·
                      rfl

theorem cell23_4888571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 3, 4, 4].length) (baseStart_4888571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4888571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4888571 prefixEnd_4888571 := by exact prefixLift 4888571
  have htrace : WordTrace (prefixWord ++ tailWord_4888571) baseStart_4888571 baseEnd_4888571 := by
    simpa [prefixWord, tailWord_4888571, baseEnd_4888571] using wordTrace_append hprefix tailTrace_4888571
  have hstable : (prefixWord ++ tailWord_4888571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4888571).length < 2 ^ (prefixWord ++ tailWord_4888571).sum := by decide
  have hdescent : baseEnd_4888571 < baseStart_4888571 := by decide
  rcases family_descends (prefixWord ++ tailWord_4888571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4888588 : List Nat := [2, 2, 1, 2, 3, 1, 1, 5, 2, 4]
def baseStart_4888588 : Nat := 118140960795 + 4888588 * 2 ^ 59
def prefixEnd_4888588 : Nat := 4983230072969 + 3 ^ 40 * 4888588 * 2
def baseEnd_4888588 : Nat := 836731788600608203555933

theorem tailTrace_4888588 : CollatzResearch.WordTrace tailWord_4888588 prefixEnd_4888588 836731788600608203555933 := by
  unfold tailWord_4888588
  simp only [CollatzResearch.WordTrace]
  refine ⟨89150726206744027602689209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118867634942325370136918945 89150726206744027602689209)
  ·
    refine ⟨66863044655058020702016907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89150726206744027602689209 66863044655058020702016907)
    ·
      refine ⟨100294566982587031053025361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66863044655058020702016907 100294566982587031053025361)
      ·
        refine ⟨75220925236940273289769021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100294566982587031053025361 75220925236940273289769021)
        ·
          refine ⟨28207846963852602483663383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75220925236940273289769021 28207846963852602483663383)
          ·
            refine ⟨42311770445778903725495075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28207846963852602483663383 42311770445778903725495075)
            ·
              refine ⟨63467655668668355588242613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42311770445778903725495075 63467655668668355588242613)
              ·
                refine ⟨5950092718937658336397745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 63467655668668355588242613 5950092718937658336397745)
                ·
                  refine ⟨4462569539203243752298309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5950092718937658336397745 4462569539203243752298309)
                  ·
                    refine ⟨836731788600608203555933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4462569539203243752298309 836731788600608203555933)
                    ·
                      rfl

theorem cell23_4888588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 5, 2, 4].length) (baseStart_4888588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4888588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4888588 prefixEnd_4888588 := by exact prefixLift 4888588
  have htrace : WordTrace (prefixWord ++ tailWord_4888588) baseStart_4888588 baseEnd_4888588 := by
    simpa [prefixWord, tailWord_4888588, baseEnd_4888588] using wordTrace_append hprefix tailTrace_4888588
  have hstable : (prefixWord ++ tailWord_4888588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4888588).length < 2 ^ (prefixWord ++ tailWord_4888588).sum := by decide
  have hdescent : baseEnd_4888588 < baseStart_4888588 := by decide
  rcases family_descends (prefixWord ++ tailWord_4888588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4888599 : List Nat := [1, 1, 3, 5, 3, 1, 1, 1, 2, 3, 2]
def baseStart_4888599 : Nat := 118140960795 + 4888599 * 2 ^ 59
def prefixEnd_4888599 : Nat := 4983230072969 + 3 ^ 40 * 4888599 * 2
def baseEnd_4888599 : Nat := 2510201014089024067630249

theorem tailTrace_4888599 : CollatzResearch.WordTrace tailWord_4888599 prefixEnd_4888599 2510201014089024067630249 := by
  unfold tailWord_4888599
  simp only [CollatzResearch.WordTrace]
  refine ⟨178301853616448204084028851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118867902410965469389352567 178301853616448204084028851)
  ·
    refine ⟨267452780424672306126043277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178301853616448204084028851 267452780424672306126043277)
    ·
      refine ⟨100294792659252114797266229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 267452780424672306126043277 100294792659252114797266229)
      ·
        refine ⟨9402636811804885762243709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 100294792659252114797266229 9402636811804885762243709)
        ·
          refine ⟨3525988804426832160841391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9402636811804885762243709 3525988804426832160841391)
          ·
            refine ⟨5288983206640248241262087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3525988804426832160841391 5288983206640248241262087)
            ·
              refine ⟨7933474809960372361893131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5288983206640248241262087 7933474809960372361893131)
              ·
                refine ⟨11900212214940558542839697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7933474809960372361893131 11900212214940558542839697)
                ·
                  refine ⟨8925159161205418907129773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11900212214940558542839697 8925159161205418907129773)
                  ·
                    refine ⟨3346934685452032090173665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8925159161205418907129773 3346934685452032090173665)
                    ·
                      refine ⟨2510201014089024067630249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3346934685452032090173665 2510201014089024067630249)
                      ·
                        rfl

theorem cell23_4888599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 1, 1, 2, 3, 2].length) (baseStart_4888599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4888599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4888599 prefixEnd_4888599 := by exact prefixLift 4888599
  have htrace : WordTrace (prefixWord ++ tailWord_4888599) baseStart_4888599 baseEnd_4888599 := by
    simpa [prefixWord, tailWord_4888599, baseEnd_4888599] using wordTrace_append hprefix tailTrace_4888599
  have hstable : (prefixWord ++ tailWord_4888599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4888599).length < 2 ^ (prefixWord ++ tailWord_4888599).sum := by decide
  have hdescent : baseEnd_4888599 < baseStart_4888599 := by decide
  rcases family_descends (prefixWord ++ tailWord_4888599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4888622 : List Nat := [4, 1, 3, 1, 1, 4, 1, 2, 2, 4]
def baseStart_4888622 : Nat := 118140960795 + 4888622 * 2 ^ 59
def prefixEnd_4888622 : Nat := 4983230072969 + 3 ^ 40 * 4888622 * 2
def baseEnd_4888622 : Nat := 836737608048025825880881

theorem tailTrace_4888622 : CollatzResearch.WordTrace tailWord_4888622 prefixEnd_4888622 836737608048025825880881 := by
  unfold tailWord_4888622
  simp only [CollatzResearch.WordTrace]
  refine ⟨22287836561920609876514515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118868461663576586008077413 22287836561920609876514515)
  ·
    refine ⟨33431754842880914814771773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22287836561920609876514515 33431754842880914814771773)
    ·
      refine ⟨12536908066080343055539415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33431754842880914814771773 12536908066080343055539415)
      ·
        refine ⟨18805362099120514583309123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12536908066080343055539415 18805362099120514583309123)
        ·
          refine ⟨28208043148680771874963685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18805362099120514583309123 28208043148680771874963685)
          ·
            refine ⟨5289008090377644726555691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28208043148680771874963685 5289008090377644726555691)
            ·
              refine ⟨7933512135566467089833537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5289008090377644726555691 7933512135566467089833537)
              ·
                refine ⟨5950134101674850317375153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7933512135566467089833537 5950134101674850317375153)
                ·
                  refine ⟨4462600576256137738031365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5950134101674850317375153 4462600576256137738031365)
                  ·
                    refine ⟨836737608048025825880881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4462600576256137738031365 836737608048025825880881)
                    ·
                      rfl

theorem cell23_4888622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 1, 2, 2, 4].length) (baseStart_4888622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4888622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4888622 prefixEnd_4888622 := by exact prefixLift 4888622
  have htrace : WordTrace (prefixWord ++ tailWord_4888622) baseStart_4888622 baseEnd_4888622 := by
    simpa [prefixWord, tailWord_4888622, baseEnd_4888622] using wordTrace_append hprefix tailTrace_4888622
  have hstable : (prefixWord ++ tailWord_4888622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4888622).length < 2 ^ (prefixWord ++ tailWord_4888622).sum := by decide
  have hdescent : baseEnd_4888622 < baseStart_4888622 := by decide
  rcases family_descends (prefixWord ++ tailWord_4888622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4888731 : List Nat := [1, 1, 1, 1, 1, 1, 2, 5, 3, 2, 5]
def baseStart_4888731 : Nat := 118140960795 + 4888731 * 2 ^ 59
def prefixEnd_4888731 : Nat := 4983230072969 + 3 ^ 40 * 4888731 * 2
def baseEnd_4888731 : Nat := 2510268793535417551179641

theorem tailTrace_4888731 : CollatzResearch.WordTrace tailWord_4888731 prefixEnd_4888731 2510268793535417551179641 := by
  unfold tailWord_4888731
  simp only [CollatzResearch.WordTrace]
  refine ⟨178306668051969990627834047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118871112034646660418556031 178306668051969990627834047)
  ·
    refine ⟨267460002077954985941751071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178306668051969990627834047 267460002077954985941751071)
    ·
      refine ⟨401190003116932478912626607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 267460002077954985941751071 401190003116932478912626607)
      ·
        refine ⟨601785004675398718368939911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 401190003116932478912626607 601785004675398718368939911)
        ·
          refine ⟨902677507013098077553409867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 601785004675398718368939911 902677507013098077553409867)
          ·
            refine ⟨1354016260519647116330114801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 902677507013098077553409867 1354016260519647116330114801)
            ·
              refine ⟨1015512195389735337247586101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1354016260519647116330114801 1015512195389735337247586101)
              ·
                refine ⟨95204268317787687866961197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1015512195389735337247586101 95204268317787687866961197)
                ·
                  refine ⟨35701600619170382950110449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 95204268317787687866961197 35701600619170382950110449)
                  ·
                    refine ⟨26776200464377787212582837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35701600619170382950110449 26776200464377787212582837)
                    ·
                      refine ⟨2510268793535417551179641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26776200464377787212582837 2510268793535417551179641)
                      ·
                        rfl

theorem cell23_4888731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 3, 2, 5].length) (baseStart_4888731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4888731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4888731 prefixEnd_4888731 := by exact prefixLift 4888731
  have htrace : WordTrace (prefixWord ++ tailWord_4888731) baseStart_4888731 baseEnd_4888731 := by
    simpa [prefixWord, tailWord_4888731, baseEnd_4888731] using wordTrace_append hprefix tailTrace_4888731
  have hstable : (prefixWord ++ tailWord_4888731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4888731).length < 2 ^ (prefixWord ++ tailWord_4888731).sum := by decide
  have hdescent : baseEnd_4888731 < baseStart_4888731 := by decide
  rcases family_descends (prefixWord ++ tailWord_4888731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4888751 : List Nat := [1, 1, 2, 1, 2, 3, 1, 2, 2, 8]
def baseStart_4888751 : Nat := 118140960795 + 4888751 * 2 ^ 59
def prefixEnd_4888751 : Nat := 4983230072969 + 3 ^ 40 * 4888751 * 2
def baseEnd_4888751 : Nat := 836759687716169157643183

theorem tailTrace_4888751 : CollatzResearch.WordTrace tailWord_4888751 prefixEnd_4888751 836759687716169157643183 := by
  unfold tailWord_4888751
  simp only [CollatzResearch.WordTrace]
  refine ⟨178307397511897534043562107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118871598341265022695708071 178307397511897534043562107)
  ·
    refine ⟨267461096267846301065343161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178307397511897534043562107 267461096267846301065343161)
    ·
      refine ⟨200595822200884725799007371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 267461096267846301065343161 200595822200884725799007371)
      ·
        refine ⟨300893733301327088698511057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200595822200884725799007371 300893733301327088698511057)
        ·
          refine ⟨225670299975995316523883293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 300893733301327088698511057 225670299975995316523883293)
          ·
            refine ⟨84626362490998243696456235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 225670299975995316523883293 84626362490998243696456235)
            ·
              refine ⟨126939543736497365544684353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84626362490998243696456235 126939543736497365544684353)
              ·
                refine ⟨95204657802373024158513265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 126939543736497365544684353 95204657802373024158513265)
                ·
                  refine ⟨71403493351779768118884949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 95204657802373024158513265 71403493351779768118884949)
                  ·
                    refine ⟨836759687716169157643183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 71403493351779768118884949 836759687716169157643183)
                    ·
                      rfl

theorem cell23_4888751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 2, 8].length) (baseStart_4888751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4888751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4888751 prefixEnd_4888751 := by exact prefixLift 4888751
  have htrace : WordTrace (prefixWord ++ tailWord_4888751) baseStart_4888751 baseEnd_4888751 := by
    simpa [prefixWord, tailWord_4888751, baseEnd_4888751] using wordTrace_append hprefix tailTrace_4888751
  have hstable : (prefixWord ++ tailWord_4888751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4888751).length < 2 ^ (prefixWord ++ tailWord_4888751).sum := by decide
  have hdescent : baseEnd_4888751 < baseStart_4888751 := by decide
  rcases family_descends (prefixWord ++ tailWord_4888751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4888772 : List Nat := [2, 3, 3, 1, 2, 3, 1, 1, 2, 5]
def baseStart_4888772 : Nat := 118140960795 + 4888772 * 2 ^ 59
def prefixEnd_4888772 : Nat := 4983230072969 + 3 ^ 40 * 4888772 * 2
def baseEnd_4888772 : Nat := 836763282080750630255651

theorem tailTrace_4888772 : CollatzResearch.WordTrace tailWord_4888772 prefixEnd_4888772 836763282080750630255651 := by
  unfold tailWord_4888772
  simp only [CollatzResearch.WordTrace]
  refine ⟨89154081722410727315038285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118872108963214303086717713 89154081722410727315038285)
  ·
    refine ⟨33432780645904022743139357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89154081722410727315038285 33432780645904022743139357)
    ·
      refine ⟨12537292742214008528677259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33432780645904022743139357 12537292742214008528677259)
      ·
        refine ⟨18805939113321012793015889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12537292742214008528677259 18805939113321012793015889)
        ·
          refine ⟨14104454334990759594761917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18805939113321012793015889 14104454334990759594761917)
          ·
            refine ⟨5289170375621534848035719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14104454334990759594761917 5289170375621534848035719)
            ·
              refine ⟨7933755563432302272053579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5289170375621534848035719 7933755563432302272053579)
              ·
                refine ⟨11900633345148453408080369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7933755563432302272053579 11900633345148453408080369)
                ·
                  refine ⟨8925475008861340056060277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11900633345148453408080369 8925475008861340056060277)
                  ·
                    refine ⟨836763282080750630255651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8925475008861340056060277 836763282080750630255651)
                    ·
                      rfl

theorem cell23_4888772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 1, 1, 2, 5].length) (baseStart_4888772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4888772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4888772 prefixEnd_4888772 := by exact prefixLift 4888772
  have htrace : WordTrace (prefixWord ++ tailWord_4888772) baseStart_4888772 baseEnd_4888772 := by
    simpa [prefixWord, tailWord_4888772, baseEnd_4888772] using wordTrace_append hprefix tailTrace_4888772
  have hstable : (prefixWord ++ tailWord_4888772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4888772).length < 2 ^ (prefixWord ++ tailWord_4888772).sum := by decide
  have hdescent : baseEnd_4888772 < baseStart_4888772 := by decide
  rcases family_descends (prefixWord ++ tailWord_4888772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4888825 : List Nat := [1, 2, 1, 3, 1, 1, 2, 3, 5, 1, 3]
def baseStart_4888825 : Nat := 118140960795 + 4888825 * 2 ^ 59
def prefixEnd_4888825 : Nat := 4983230072969 + 3 ^ 40 * 4888825 * 2
def baseEnd_4888825 : Nat := 2510317060716940183404209

theorem tailTrace_4888825 : CollatzResearch.WordTrace tailWord_4888825 prefixEnd_4888825 2510317060716940183404209 := by
  unfold tailWord_4888825
  simp only [CollatzResearch.WordTrace]
  refine ⟨178310096513629444681755929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118873397675752963121170619 178310096513629444681755929)
  ·
    refine ⟨133732572385222083511316947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178310096513629444681755929 133732572385222083511316947)
    ·
      refine ⟨200598858577833125266975421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133732572385222083511316947 200598858577833125266975421)
      ·
        refine ⟨75224571966687421975115783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 200598858577833125266975421 75224571966687421975115783)
        ·
          refine ⟨112836857950031132962673675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75224571966687421975115783 112836857950031132962673675)
          ·
            refine ⟨169255286925046699444010513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112836857950031132962673675 169255286925046699444010513)
            ·
              refine ⟨126941465193785024583007885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 169255286925046699444010513 126941465193785024583007885)
              ·
                refine ⟨47603049447669384218627957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 126941465193785024583007885 47603049447669384218627957)
                ·
                  refine ⟨4462785885719004770496371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47603049447669384218627957 4462785885719004770496371)
                  ·
                    refine ⟨6694178828578507155744557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4462785885719004770496371 6694178828578507155744557)
                    ·
                      refine ⟨2510317060716940183404209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6694178828578507155744557 2510317060716940183404209)
                      ·
                        rfl

theorem cell23_4888825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 3, 5, 1, 3].length) (baseStart_4888825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4888825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4888825 prefixEnd_4888825 := by exact prefixLift 4888825
  have htrace : WordTrace (prefixWord ++ tailWord_4888825) baseStart_4888825 baseEnd_4888825 := by
    simpa [prefixWord, tailWord_4888825, baseEnd_4888825] using wordTrace_append hprefix tailTrace_4888825
  have hstable : (prefixWord ++ tailWord_4888825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4888825).length < 2 ^ (prefixWord ++ tailWord_4888825).sum := by decide
  have hdescent : baseEnd_4888825 < baseStart_4888825 := by decide
  rcases family_descends (prefixWord ++ tailWord_4888825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4888835 : List Nat := [1, 1, 1, 3, 2, 3, 1, 3, 1, 5, 2]
def baseStart_4888835 : Nat := 118140960795 + 4888835 * 2 ^ 59
def prefixEnd_4888835 : Nat := 4983230072969 + 3 ^ 40 * 4888835 * 2
def baseEnd_4888835 : Nat := 2510322195523485144279163

theorem tailTrace_4888835 : CollatzResearch.WordTrace tailWord_4888835 prefixEnd_4888835 2510322195523485144279163 := by
  unfold tailWord_4888835
  simp only [CollatzResearch.WordTrace]
  refine ⟨178310461243593216389619959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118873640829062144259746639 178310461243593216389619959)
  ·
    refine ⟨267465691865389824584429939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178310461243593216389619959 267465691865389824584429939)
    ·
      refine ⟨401198537798084736876644909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 267465691865389824584429939 401198537798084736876644909)
      ·
        refine ⟨150449451674281776328741841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 401198537798084736876644909 150449451674281776328741841)
        ·
          refine ⟨112837088755711332246556381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150449451674281776328741841 112837088755711332246556381)
          ·
            refine ⟨42313908283391749592458643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 112837088755711332246556381 42313908283391749592458643)
            ·
              refine ⟨63470862425087624388687965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42313908283391749592458643 63470862425087624388687965)
              ·
                refine ⟨23801573409407859145757987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63470862425087624388687965 23801573409407859145757987)
                ·
                  refine ⟨35702360114111788718636981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23801573409407859145757987 35702360114111788718636981)
                  ·
                    refine ⟨3347096260697980192372217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35702360114111788718636981 3347096260697980192372217)
                    ·
                      refine ⟨2510322195523485144279163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3347096260697980192372217 2510322195523485144279163)
                      ·
                        rfl

theorem cell23_4888835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 3, 1, 5, 2].length) (baseStart_4888835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4888835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4888835 prefixEnd_4888835 := by exact prefixLift 4888835
  have htrace : WordTrace (prefixWord ++ tailWord_4888835) baseStart_4888835 baseEnd_4888835 := by
    simpa [prefixWord, tailWord_4888835, baseEnd_4888835] using wordTrace_append hprefix tailTrace_4888835
  have hstable : (prefixWord ++ tailWord_4888835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4888835).length < 2 ^ (prefixWord ++ tailWord_4888835).sum := by decide
  have hdescent : baseEnd_4888835 < baseStart_4888835 := by decide
  rcases family_descends (prefixWord ++ tailWord_4888835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4888836 : List Nat := [2, 3, 2, 2, 3, 2, 1, 3, 1, 4]
def baseStart_4888836 : Nat := 118140960795 + 4888836 * 2 ^ 59
def prefixEnd_4888836 : Nat := 4983230072969 + 3 ^ 40 * 4888836 * 2
def baseEnd_4888836 : Nat := 836774236334713213455553

theorem tailTrace_4888836 : CollatzResearch.WordTrace tailWord_4888836 prefixEnd_4888836 836774236334713213455553 := by
  unfold tailWord_4888836
  simp only [CollatzResearch.WordTrace]
  refine ⟨89155248858294796780203181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118873665144393062373604241 89155248858294796780203181)
  ·
    refine ⟨33433218321860548792576193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89155248858294796780203181 33433218321860548792576193)
    ·
      refine ⟨25074913741395411594432145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33433218321860548792576193 25074913741395411594432145)
      ·
        refine ⟨18806185306046558695824109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25074913741395411594432145 18806185306046558695824109)
        ·
          refine ⟨7052319489767459510934041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18806185306046558695824109 7052319489767459510934041)
          ·
            refine ⟨5289239617325594633200531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7052319489767459510934041 5289239617325594633200531)
            ·
              refine ⟨7933859425988391949800797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5289239617325594633200531 7933859425988391949800797)
              ·
                refine ⟨2975197284745646981175299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7933859425988391949800797 2975197284745646981175299)
                ·
                  refine ⟨4462795927118470471762949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2975197284745646981175299 4462795927118470471762949)
                  ·
                    refine ⟨836774236334713213455553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4462795927118470471762949 836774236334713213455553)
                    ·
                      rfl

theorem cell23_4888836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 1, 3, 1, 4].length) (baseStart_4888836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4888836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4888836 prefixEnd_4888836 := by exact prefixLift 4888836
  have htrace : WordTrace (prefixWord ++ tailWord_4888836) baseStart_4888836 baseEnd_4888836 := by
    simpa [prefixWord, tailWord_4888836, baseEnd_4888836] using wordTrace_append hprefix tailTrace_4888836
  have hstable : (prefixWord ++ tailWord_4888836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4888836).length < 2 ^ (prefixWord ++ tailWord_4888836).sum := by decide
  have hdescent : baseEnd_4888836 < baseStart_4888836 := by decide
  rcases family_descends (prefixWord ++ tailWord_4888836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4888882 : List Nat := [3, 2, 1, 1, 5, 1, 1, 1, 3, 1, 4]
def baseStart_4888882 : Nat := 118140960795 + 4888882 * 2 ^ 59
def prefixEnd_4888882 : Nat := 4983230072969 + 3 ^ 40 * 4888882 * 2
def baseEnd_4888882 : Nat := 2510346329114246460391447

theorem tailTrace_4888882 : CollatzResearch.WordTrace tailWord_4888882 prefixEnd_4888882 2510346329114246460391447 := by
  unfold tailWord_4888882
  simp only [CollatzResearch.WordTrace]
  refine ⟨44578043868605735854145225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118874783649615295611053933 44578043868605735854145225)
  ·
    refine ⟨33433532901454301890608919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44578043868605735854145225 33433532901454301890608919)
    ·
      refine ⟨50150299352181452835913379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33433532901454301890608919 50150299352181452835913379)
      ·
        refine ⟨75225449028272179253870069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50150299352181452835913379 75225449028272179253870069)
        ·
          refine ⟨7052385846400516805050319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 75225449028272179253870069 7052385846400516805050319)
          ·
            refine ⟨10578578769600775207575479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7052385846400516805050319 10578578769600775207575479)
            ·
              refine ⟨15867868154401162811363219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10578578769600775207575479 15867868154401162811363219)
              ·
                refine ⟨23801802231601744217044829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15867868154401162811363219 23801802231601744217044829)
                ·
                  refine ⟨8925675836850654081391811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23801802231601744217044829 8925675836850654081391811)
                  ·
                    refine ⟨13388513755275981122087717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8925675836850654081391811 13388513755275981122087717)
                    ·
                      refine ⟨2510346329114246460391447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13388513755275981122087717 2510346329114246460391447)
                      ·
                        rfl

theorem cell23_4888882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 1, 3, 1, 4].length) (baseStart_4888882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4888882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4888882 prefixEnd_4888882 := by exact prefixLift 4888882
  have htrace : WordTrace (prefixWord ++ tailWord_4888882) baseStart_4888882 baseEnd_4888882 := by
    simpa [prefixWord, tailWord_4888882, baseEnd_4888882] using wordTrace_append hprefix tailTrace_4888882
  have hstable : (prefixWord ++ tailWord_4888882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4888882).length < 2 ^ (prefixWord ++ tailWord_4888882).sum := by decide
  have hdescent : baseEnd_4888882 < baseStart_4888882 := by decide
  rcases family_descends (prefixWord ++ tailWord_4888882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4888888 : List Nat := [2, 1, 2, 1, 3, 1, 4, 9]
def baseStart_4888888 : Nat := 118140960795 + 4888888 * 2 ^ 59
def prefixEnd_4888888 : Nat := 4983230072969 + 3 ^ 40 * 4888888 * 2
def baseEnd_4888888 : Nat := 92975904074006423589497

theorem tailTrace_4888888 : CollatzResearch.WordTrace tailWord_4888888 prefixEnd_4888888 92975904074006423589497 := by
  unfold tailWord_4888888
  simp only [CollatzResearch.WordTrace]
  refine ⟨89156197156200603220649659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118874929541600804294199545 89156197156200603220649659)
  ·
    refine ⟨133734295734300904830974489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89156197156200603220649659 133734295734300904830974489)
    ·
      refine ⟨100300721800725678623230867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133734295734300904830974489 100300721800725678623230867)
      ·
        refine ⟨150451082701088517934846301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100300721800725678623230867 150451082701088517934846301)
        ·
          refine ⟨56419156012908194225567363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 150451082701088517934846301 56419156012908194225567363)
          ·
            refine ⟨84628734019362291338351045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56419156012908194225567363 84628734019362291338351045)
            ·
              refine ⟨15867887628630429625940821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 84628734019362291338351045 15867887628630429625940821)
              ·
                refine ⟨92975904074006423589497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15867887628630429625940821 92975904074006423589497)
                ·
                  rfl

theorem cell23_4888888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 9].length) (baseStart_4888888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4888888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4888888 prefixEnd_4888888 := by exact prefixLift 4888888
  have htrace : WordTrace (prefixWord ++ tailWord_4888888) baseStart_4888888 baseEnd_4888888 := by
    simpa [prefixWord, tailWord_4888888, baseEnd_4888888] using wordTrace_append hprefix tailTrace_4888888
  have hstable : (prefixWord ++ tailWord_4888888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4888888).length < 2 ^ (prefixWord ++ tailWord_4888888).sum := by decide
  have hdescent : baseEnd_4888888 < baseStart_4888888 := by decide
  rcases family_descends (prefixWord ++ tailWord_4888888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4888895 : List Nat := [1, 1, 2, 2, 4, 1, 3, 2, 1, 2, 4]
def baseStart_4888895 : Nat := 118140960795 + 4888895 * 2 ^ 59
def prefixEnd_4888895 : Nat := 4983230072969 + 3 ^ 40 * 4888895 * 2
def baseEnd_4888895 : Nat := 2510353004362754909528887

theorem tailTrace_4888895 : CollatzResearch.WordTrace tailWord_4888895 prefixEnd_4888895 2510353004362754909528887 := by
  unfold tailWord_4888895
  simp only [CollatzResearch.WordTrace]
  refine ⟨178312649623375846636804139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118875099748917231091202759 178312649623375846636804139)
  ·
    refine ⟨267468974435063769955206209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178312649623375846636804139 267468974435063769955206209)
    ·
      refine ⟨200601730826297827466404657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 267468974435063769955206209 200601730826297827466404657)
      ·
        refine ⟨150451298119723370599803493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 200601730826297827466404657 150451298119723370599803493)
        ·
          refine ⟨28209618397448131987463155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 150451298119723370599803493 28209618397448131987463155)
          ·
            refine ⟨42314427596172197981194733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28209618397448131987463155 42314427596172197981194733)
            ·
              refine ⟨15867910348564574242948025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42314427596172197981194733 15867910348564574242948025)
              ·
                refine ⟨11900932761423430682211019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15867910348564574242948025 11900932761423430682211019)
                ·
                  refine ⟨17851399142135146023316529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11900932761423430682211019 17851399142135146023316529)
                  ·
                    refine ⟨13388549356601359517487397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17851399142135146023316529 13388549356601359517487397)
                    ·
                      refine ⟨2510353004362754909528887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13388549356601359517487397 2510353004362754909528887)
                      ·
                        rfl

theorem cell23_4888895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 2, 1, 2, 4].length) (baseStart_4888895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4888895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4888895 prefixEnd_4888895 := by exact prefixLift 4888895
  have htrace : WordTrace (prefixWord ++ tailWord_4888895) baseStart_4888895 baseEnd_4888895 := by
    simpa [prefixWord, tailWord_4888895, baseEnd_4888895] using wordTrace_append hprefix tailTrace_4888895
  have hstable : (prefixWord ++ tailWord_4888895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4888895).length < 2 ^ (prefixWord ++ tailWord_4888895).sum := by decide
  have hdescent : baseEnd_4888895 < baseStart_4888895 := by decide
  rcases family_descends (prefixWord ++ tailWord_4888895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4888932 : List Nat := [2, 3, 1, 1, 3, 1, 4, 1, 1, 3, 3]
def baseStart_4888932 : Nat := 118140960795 + 4888932 * 2 ^ 59
def prefixEnd_4888932 : Nat := 4983230072969 + 3 ^ 40 * 4888932 * 2
def baseEnd_4888932 : Nat := 2510372003146971264766217

theorem tailTrace_4888932 : CollatzResearch.WordTrace tailWord_4888932 prefixEnd_4888932 2510372003146971264766217 := by
  unfold tailWord_4888932
  simp only [CollatzResearch.WordTrace]
  refine ⟨89156999562120900977950525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118875999416161201303934033 89156999562120900977950525)
  ·
    refine ⟨33433874835795337866731447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89156999562120900977950525 33433874835795337866731447)
    ·
      refine ⟨50150812253693006800097171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33433874835795337866731447 50150812253693006800097171)
      ·
        refine ⟨75226218380539510200145757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50150812253693006800097171 75226218380539510200145757)
        ·
          refine ⟨28209831892702316325054659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75226218380539510200145757 28209831892702316325054659)
          ·
            refine ⟨42314747839053474487581989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28209831892702316325054659 42314747839053474487581989)
            ·
              refine ⟨7934015219822526466421623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42314747839053474487581989 7934015219822526466421623)
              ·
                refine ⟨11901022829733789699632435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7934015219822526466421623 11901022829733789699632435)
                ·
                  refine ⟨17851534244600684549448653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11901022829733789699632435 17851534244600684549448653)
                  ·
                    refine ⟨6694325341725256706043245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17851534244600684549448653 6694325341725256706043245)
                    ·
                      refine ⟨2510372003146971264766217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6694325341725256706043245 2510372003146971264766217)
                      ·
                        rfl

theorem cell23_4888932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 4, 1, 1, 3, 3].length) (baseStart_4888932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4888932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4888932 prefixEnd_4888932 := by exact prefixLift 4888932
  have htrace : WordTrace (prefixWord ++ tailWord_4888932) baseStart_4888932 baseEnd_4888932 := by
    simpa [prefixWord, tailWord_4888932, baseEnd_4888932] using wordTrace_append hprefix tailTrace_4888932
  have hstable : (prefixWord ++ tailWord_4888932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4888932).length < 2 ^ (prefixWord ++ tailWord_4888932).sum := by decide
  have hdescent : baseEnd_4888932 < baseStart_4888932 := by decide
  rcases family_descends (prefixWord ++ tailWord_4888932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4888950 : List Nat := [5, 1, 1, 4, 2, 1, 2, 1, 1, 1, 4]
def baseStart_4888950 : Nat := 118140960795 + 4888950 * 2 ^ 59
def prefixEnd_4888950 : Nat := 4983230072969 + 3 ^ 40 * 4888950 * 2
def baseEnd_4888950 : Nat := 2510381245798752194341135

theorem tailTrace_4888950 : CollatzResearch.WordTrace tailWord_4888950 prefixEnd_4888950 2510381245798752194341135 := by
  unfold tailWord_4888950
  simp only [CollatzResearch.WordTrace]
  refine ⟨11144665977386036939378519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 118876437092117727353370869 11144665977386036939378519)
  ·
    refine ⟨16716998966079055409067779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11144665977386036939378519 16716998966079055409067779)
    ·
      refine ⟨25075498449118583113601669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16716998966079055409067779 25075498449118583113601669)
      ·
        refine ⟨4701655959209734333800313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25075498449118583113601669 4701655959209734333800313)
        ·
          refine ⟨3526241969407300750350235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4701655959209734333800313 3526241969407300750350235)
          ·
            refine ⟨5289362954110951125525353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3526241969407300750350235 5289362954110951125525353)
            ·
              refine ⟨3967022215583213344144015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5289362954110951125525353 3967022215583213344144015)
              ·
                refine ⟨5950533323374820016216023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3967022215583213344144015 5950533323374820016216023)
                ·
                  refine ⟨8925799985062230024324035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5950533323374820016216023 8925799985062230024324035)
                  ·
                    refine ⟨13388699977593345036486053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8925799985062230024324035 13388699977593345036486053)
                    ·
                      refine ⟨2510381245798752194341135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13388699977593345036486053 2510381245798752194341135)
                      ·
                        rfl

theorem cell23_4888950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_4888950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4888950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4888950 prefixEnd_4888950 := by exact prefixLift 4888950
  have htrace : WordTrace (prefixWord ++ tailWord_4888950) baseStart_4888950 baseEnd_4888950 := by
    simpa [prefixWord, tailWord_4888950, baseEnd_4888950] using wordTrace_append hprefix tailTrace_4888950
  have hstable : (prefixWord ++ tailWord_4888950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4888950).length < 2 ^ (prefixWord ++ tailWord_4888950).sum := by decide
  have hdescent : baseEnd_4888950 < baseStart_4888950 := by decide
  rcases family_descends (prefixWord ++ tailWord_4888950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4888985 : List Nat := [1, 2, 1, 2, 1, 4, 1, 3, 2, 2, 4]
def baseStart_4888985 : Nat := 118140960795 + 4888985 * 2 ^ 59
def prefixEnd_4888985 : Nat := 4983230072969 + 3 ^ 40 * 4888985 * 2
def baseEnd_4888985 : Nat := 2510399217621659557403473

theorem tailTrace_4888985 : CollatzResearch.WordTrace tailWord_4888985 prefixEnd_4888985 2510399217621659557403473 := by
  unfold tailWord_4888985
  simp only [CollatzResearch.WordTrace]
  refine ⟨178315932193049792007580409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118877288128699861338386939 178315932193049792007580409)
  ·
    refine ⟨133736949144787344005685307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178315932193049792007580409 133736949144787344005685307)
    ·
      refine ⟨200605423717181016008527961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133736949144787344005685307 200605423717181016008527961)
      ·
        refine ⟨150454067787885762006395971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 200605423717181016008527961 150454067787885762006395971)
        ·
          refine ⟨225681101681828643009593957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150454067787885762006395971 225681101681828643009593957)
          ·
            refine ⟨42315206565342870564298867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 225681101681828643009593957 42315206565342870564298867)
            ·
              refine ⟨63472809848014305846448301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42315206565342870564298867 63472809848014305846448301)
              ·
                refine ⟨23802303693005364692418113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63472809848014305846448301 23802303693005364692418113)
                ·
                  refine ⟨17851727769754023519313585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23802303693005364692418113 17851727769754023519313585)
                  ·
                    refine ⟨13388795827315517639485189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17851727769754023519313585 13388795827315517639485189)
                    ·
                      refine ⟨2510399217621659557403473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13388795827315517639485189 2510399217621659557403473)
                      ·
                        rfl

theorem cell23_4888985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 3, 2, 2, 4].length) (baseStart_4888985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4888985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4888985 prefixEnd_4888985 := by exact prefixLift 4888985
  have htrace : WordTrace (prefixWord ++ tailWord_4888985) baseStart_4888985 baseEnd_4888985 := by
    simpa [prefixWord, tailWord_4888985, baseEnd_4888985] using wordTrace_append hprefix tailTrace_4888985
  have hstable : (prefixWord ++ tailWord_4888985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4888985).length < 2 ^ (prefixWord ++ tailWord_4888985).sum := by decide
  have hdescent : baseEnd_4888985 < baseStart_4888985 := by decide
  rcases family_descends (prefixWord ++ tailWord_4888985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4888993 : List Nat := [1, 2, 3, 5, 1, 1, 2, 2, 1, 3, 2]
def baseStart_4888993 : Nat := 118140960795 + 4888993 * 2 ^ 59
def prefixEnd_4888993 : Nat := 4983230072969 + 3 ^ 40 * 4888993 * 2
def baseEnd_4888993 : Nat := 2510403325466895526103437

theorem tailTrace_4888993 : CollatzResearch.WordTrace tailWord_4888993 prefixEnd_4888993 2510403325466895526103437 := by
  unfold tailWord_4888993
  simp only [CollatzResearch.WordTrace]
  refine ⟨178316223977020809373871633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118877482651347206249247755 178316223977020809373871633)
  ·
    refine ⟨133737167982765607030403725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178316223977020809373871633 133737167982765607030403725)
    ·
      refine ⟨50151437993537102636401397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133737167982765607030403725 50151437993537102636401397)
      ·
        refine ⟨4701697311894103372162631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 50151437993537102636401397 4701697311894103372162631)
        ·
          refine ⟨7052545967841155058243947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4701697311894103372162631 7052545967841155058243947)
          ·
            refine ⟨10578818951761732587365921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7052545967841155058243947 10578818951761732587365921)
            ·
              refine ⟨7934114213821299440524441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10578818951761732587365921 7934114213821299440524441)
              ·
                refine ⟨5950585660365974580393331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7934114213821299440524441 5950585660365974580393331)
                ·
                  refine ⟨8925878490548961870589997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5950585660365974580393331 8925878490548961870589997)
                  ·
                    refine ⟨3347204433955860701471249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8925878490548961870589997 3347204433955860701471249)
                    ·
                      refine ⟨2510403325466895526103437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3347204433955860701471249 2510403325466895526103437)
                      ·
                        rfl

theorem cell23_4888993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_4888993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4888993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4888993 prefixEnd_4888993 := by exact prefixLift 4888993
  have htrace : WordTrace (prefixWord ++ tailWord_4888993) baseStart_4888993 baseEnd_4888993 := by
    simpa [prefixWord, tailWord_4888993, baseEnd_4888993] using wordTrace_append hprefix tailTrace_4888993
  have hstable : (prefixWord ++ tailWord_4888993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4888993).length < 2 ^ (prefixWord ++ tailWord_4888993).sum := by decide
  have hdescent : baseEnd_4888993 < baseStart_4888993 := by decide
  rcases family_descends (prefixWord ++ tailWord_4888993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4888995 : List Nat := [1, 1, 1, 4, 1, 4, 2, 2, 7]
def baseStart_4888995 : Nat := 118140960795 + 4888995 * 2 ^ 59
def prefixEnd_4888995 : Nat := 4983230072969 + 3 ^ 40 * 4888995 * 2
def baseEnd_4888995 : Nat := 278933816936467168697603

theorem tailTrace_4888995 : CollatzResearch.WordTrace tailWord_4888995 prefixEnd_4888995 278933816936467168697603 := by
  unfold tailWord_4888995
  simp only [CollatzResearch.WordTrace]
  refine ⟨178316296923013563715444439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118877531282009042476962959 178316296923013563715444439)
  ·
    refine ⟨267474445384520345573166659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178316296923013563715444439 267474445384520345573166659)
    ·
      refine ⟨401211668076780518359749989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 267474445384520345573166659 401211668076780518359749989)
      ·
        refine ⟨75227187764396347192453123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 401211668076780518359749989 75227187764396347192453123)
        ·
          refine ⟨112840781646594520788679685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75227187764396347192453123 112840781646594520788679685)
          ·
            refine ⟨21157646558736472647877441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 112840781646594520788679685 21157646558736472647877441)
            ·
              refine ⟨15868234919052354485908081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21157646558736472647877441 15868234919052354485908081)
              ·
                refine ⟨11901176189289265864431061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15868234919052354485908081 11901176189289265864431061)
                ·
                  refine ⟨278933816936467168697603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11901176189289265864431061 278933816936467168697603)
                  ·
                    rfl

theorem cell23_4888995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 2, 7].length) (baseStart_4888995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4888995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4888995 prefixEnd_4888995 := by exact prefixLift 4888995
  have htrace : WordTrace (prefixWord ++ tailWord_4888995) baseStart_4888995 baseEnd_4888995 := by
    simpa [prefixWord, tailWord_4888995, baseEnd_4888995] using wordTrace_append hprefix tailTrace_4888995
  have hstable : (prefixWord ++ tailWord_4888995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4888995).length < 2 ^ (prefixWord ++ tailWord_4888995).sum := by decide
  have hdescent : baseEnd_4888995 < baseStart_4888995 := by decide
  rcases family_descends (prefixWord ++ tailWord_4888995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4889022 : List Nat := [4, 2, 1, 1, 1, 1, 2, 1, 4, 3, 3]
def baseStart_4889022 : Nat := 118140960795 + 4889022 * 2 ^ 59
def prefixEnd_4889022 : Nat := 4983230072969 + 3 ^ 40 * 4889022 * 2
def baseEnd_4889022 : Nat := 2510418216405875912640803

theorem tailTrace_4889022 : CollatzResearch.WordTrace tailWord_4889022 prefixEnd_4889022 2510418216405875912640803 := by
  unfold tailWord_4889022
  simp only [CollatzResearch.WordTrace]
  refine ⟨22289660211739468415834665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118878187795943831551118213 22289660211739468415834665)
  ·
    refine ⟨16717245158804601311875999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22289660211739468415834665 16717245158804601311875999)
    ·
      refine ⟨25075867738206901967813999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16717245158804601311875999 25075867738206901967813999)
      ·
        refine ⟨37613801607310352951720999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25075867738206901967813999 37613801607310352951720999)
        ·
          refine ⟨56420702410965529427581499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37613801607310352951720999 56420702410965529427581499)
          ·
            refine ⟨84631053616448294141372249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56420702410965529427581499 84631053616448294141372249)
            ·
              refine ⟨63473290212336220606029187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84631053616448294141372249 63473290212336220606029187)
              ·
                refine ⟨95209935318504330909043781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63473290212336220606029187 95209935318504330909043781)
                ·
                  refine ⟨17851862872219562045445709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 95209935318504330909043781 17851862872219562045445709)
                  ·
                    refine ⟨6694448577082335767042141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17851862872219562045445709 6694448577082335767042141)
                    ·
                      refine ⟨2510418216405875912640803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6694448577082335767042141 2510418216405875912640803)
                      ·
                        rfl

theorem cell23_4889022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 4, 3, 3].length) (baseStart_4889022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4889022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4889022 prefixEnd_4889022 := by exact prefixLift 4889022
  have htrace : WordTrace (prefixWord ++ tailWord_4889022) baseStart_4889022 baseEnd_4889022 := by
    simpa [prefixWord, tailWord_4889022, baseEnd_4889022] using wordTrace_append hprefix tailTrace_4889022
  have hstable : (prefixWord ++ tailWord_4889022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4889022).length < 2 ^ (prefixWord ++ tailWord_4889022).sum := by decide
  have hdescent : baseEnd_4889022 < baseStart_4889022 := by decide
  rcases family_descends (prefixWord ++ tailWord_4889022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4889059 : List Nat := [1, 1, 1, 6, 3, 1, 2, 1, 2, 5]
def baseStart_4889059 : Nat := 118140960795 + 4889059 * 2 ^ 59
def prefixEnd_4889059 : Nat := 4983230072969 + 3 ^ 40 * 4889059 * 2
def baseEnd_4889059 : Nat := 836812405063364089292711

theorem tailTrace_4889059 : CollatzResearch.WordTrace tailWord_4889059 prefixEnd_4889059 836812405063364089292711 := by
  unfold tailWord_4889059
  simp only [CollatzResearch.WordTrace]
  refine ⟨178318631194781702645774231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118879087463187801763849487 178318631194781702645774231)
  ·
    refine ⟨267477946792172553968661347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178318631194781702645774231 267477946792172553968661347)
    ·
      refine ⟨401216920188258830952992021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 267477946792172553968661347 401216920188258830952992021)
      ·
        refine ⟨18807043133824632700921501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 401216920188258830952992021 18807043133824632700921501)
        ·
          refine ⟨7052641175184237262845563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18807043133824632700921501 7052641175184237262845563)
          ·
            refine ⟨10578961762776355894268345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7052641175184237262845563 10578961762776355894268345)
            ·
              refine ⟨7934221322082266920701259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10578961762776355894268345 7934221322082266920701259)
              ·
                refine ⟨11901331983123400381051889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7934221322082266920701259 11901331983123400381051889)
                ·
                  refine ⟨8925998987342550285788917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11901331983123400381051889 8925998987342550285788917)
                  ·
                    refine ⟨836812405063364089292711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8925998987342550285788917 836812405063364089292711)
                    ·
                      rfl

theorem cell23_4889059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 2, 1, 2, 5].length) (baseStart_4889059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4889059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4889059 prefixEnd_4889059 := by exact prefixLift 4889059
  have htrace : WordTrace (prefixWord ++ tailWord_4889059) baseStart_4889059 baseEnd_4889059 := by
    simpa [prefixWord, tailWord_4889059, baseEnd_4889059] using wordTrace_append hprefix tailTrace_4889059
  have hstable : (prefixWord ++ tailWord_4889059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4889059).length < 2 ^ (prefixWord ++ tailWord_4889059).sum := by decide
  have hdescent : baseEnd_4889059 < baseStart_4889059 := by decide
  rcases family_descends (prefixWord ++ tailWord_4889059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4889075 : List Nat := [1, 1, 1, 2, 2, 2, 4, 1, 2, 1, 6]
def baseStart_4889075 : Nat := 118140960795 + 4889075 * 2 ^ 59
def prefixEnd_4889075 : Nat := 4983230072969 + 3 ^ 40 * 4889075 * 2
def baseEnd_4889075 : Nat := 2510445430880564205278059

theorem tailTrace_4889075 : CollatzResearch.WordTrace tailWord_4889075 prefixEnd_4889075 2510445430880564205278059 := by
  unfold tailWord_4889075
  simp only [CollatzResearch.WordTrace]
  refine ⟨178319214762723737378356679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118879476508482491585571119 178319214762723737378356679)
  ·
    refine ⟨267478822144085606067535019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178319214762723737378356679 267478822144085606067535019)
    ·
      refine ⟨401218233216128409101302529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 267478822144085606067535019 401218233216128409101302529)
      ·
        refine ⟨300913674912096306825976897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 401218233216128409101302529 300913674912096306825976897)
        ·
          refine ⟨225685256184072230119482673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 300913674912096306825976897 225685256184072230119482673)
          ·
            refine ⟨169263942138054172589612005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 225685256184072230119482673 169263942138054172589612005)
            ·
              refine ⟨31736989150885157360552251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 169263942138054172589612005 31736989150885157360552251)
              ·
                refine ⟨47605483726327736040828377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31736989150885157360552251 47605483726327736040828377)
                ·
                  refine ⟨35704112794745802030621283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47605483726327736040828377 35704112794745802030621283)
                  ·
                    refine ⟨53556169192118703045931925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35704112794745802030621283 53556169192118703045931925)
                    ·
                      refine ⟨2510445430880564205278059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53556169192118703045931925 2510445430880564205278059)
                      ·
                        rfl

theorem cell23_4889075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 1, 2, 1, 6].length) (baseStart_4889075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4889075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4889075 prefixEnd_4889075 := by exact prefixLift 4889075
  have htrace : WordTrace (prefixWord ++ tailWord_4889075) baseStart_4889075 baseEnd_4889075 := by
    simpa [prefixWord, tailWord_4889075, baseEnd_4889075] using wordTrace_append hprefix tailTrace_4889075
  have hstable : (prefixWord ++ tailWord_4889075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4889075).length < 2 ^ (prefixWord ++ tailWord_4889075).sum := by decide
  have hdescent : baseEnd_4889075 < baseStart_4889075 := by decide
  rcases family_descends (prefixWord ++ tailWord_4889075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4889082 : List Nat := [3, 1, 1, 1, 1, 2, 2, 3, 4, 2, 3]
def baseStart_4889082 : Nat := 118140960795 + 4889082 * 2 ^ 59
def prefixEnd_4889082 : Nat := 4983230072969 + 3 ^ 40 * 4889082 * 2
def baseEnd_4889082 : Nat := 2510449025245145677890527

theorem tailTrace_4889082 : CollatzResearch.WordTrace tailWord_4889082 prefixEnd_4889082 2510449025245145677890527 := by
  unfold tailWord_4889082
  simp only [CollatzResearch.WordTrace]
  refine ⟨44579867518424594393465375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118879646715798918382574333 44579867518424594393465375)
  ·
    refine ⟨66869801277636891590198063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44579867518424594393465375 66869801277636891590198063)
    ·
      refine ⟨100304701916455337385297095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66869801277636891590198063 100304701916455337385297095)
      ·
        refine ⟨150457052874683006077945643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100304701916455337385297095 150457052874683006077945643)
        ·
          refine ⟨225685579312024509116918465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150457052874683006077945643 225685579312024509116918465)
          ·
            refine ⟨169264184484018381837688849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 225685579312024509116918465 169264184484018381837688849)
            ·
              refine ⟨126948138363013786378266637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 169264184484018381837688849 126948138363013786378266637)
              ·
                refine ⟨47605551886130169891849989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 126948138363013786378266637 47605551886130169891849989)
                ·
                  refine ⟨8926040978649406854721873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47605551886130169891849989 8926040978649406854721873)
                  ·
                    refine ⟨6694530733987055141041405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8926040978649406854721873 6694530733987055141041405)
                    ·
                      refine ⟨2510449025245145677890527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6694530733987055141041405 2510449025245145677890527)
                      ·
                        rfl

theorem cell23_4889082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 3, 4, 2, 3].length) (baseStart_4889082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4889082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4889082 prefixEnd_4889082 := by exact prefixLift 4889082
  have htrace : WordTrace (prefixWord ++ tailWord_4889082) baseStart_4889082 baseEnd_4889082 := by
    simpa [prefixWord, tailWord_4889082, baseEnd_4889082] using wordTrace_append hprefix tailTrace_4889082
  have hstable : (prefixWord ++ tailWord_4889082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4889082).length < 2 ^ (prefixWord ++ tailWord_4889082).sum := by decide
  have hdescent : baseEnd_4889082 < baseStart_4889082 := by decide
  rcases family_descends (prefixWord ++ tailWord_4889082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4889105 : List Nat := [1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 6]
def baseStart_4889105 : Nat := 118140960795 + 4889105 * 2 ^ 59
def prefixEnd_4889105 : Nat := 4983230072969 + 3 ^ 40 * 4889105 * 2
def baseEnd_4889105 : Nat := 2510460835300199087902921

theorem tailTrace_4889105 : CollatzResearch.WordTrace tailWord_4889105 prefixEnd_4889105 2510460835300199087902921 := by
  unfold tailWord_4889105
  simp only [CollatzResearch.WordTrace]
  refine ⟨178320308952615052501948769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118880205968410035001299179 178320308952615052501948769)
  ·
    refine ⟨133740231714461289376461577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178320308952615052501948769 133740231714461289376461577)
    ·
      refine ⟨100305173785845967032346183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133740231714461289376461577 100305173785845967032346183)
      ·
        refine ⟨150457760678768950548519275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100305173785845967032346183 150457760678768950548519275)
        ·
          refine ⟨225686641018153425822778913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150457760678768950548519275 225686641018153425822778913)
          ·
            refine ⟨169264980763615069367084185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 225686641018153425822778913 169264980763615069367084185)
            ·
              refine ⟨126948735572711302025313139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 169264980763615069367084185 126948735572711302025313139)
              ·
                refine ⟨190423103359066953037969709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126948735572711302025313139 190423103359066953037969709)
                ·
                  refine ⟨71408663759650107389238641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 190423103359066953037969709 71408663759650107389238641)
                  ·
                    refine ⟨53556497819737580541928981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 71408663759650107389238641 53556497819737580541928981)
                    ·
                      refine ⟨2510460835300199087902921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53556497819737580541928981 2510460835300199087902921)
                      ·
                        rfl

theorem cell23_4889105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 6].length) (baseStart_4889105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4889105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4889105 prefixEnd_4889105 := by exact prefixLift 4889105
  have htrace : WordTrace (prefixWord ++ tailWord_4889105) baseStart_4889105 baseEnd_4889105 := by
    simpa [prefixWord, tailWord_4889105, baseEnd_4889105] using wordTrace_append hprefix tailTrace_4889105
  have hstable : (prefixWord ++ tailWord_4889105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4889105).length < 2 ^ (prefixWord ++ tailWord_4889105).sum := by decide
  have hdescent : baseEnd_4889105 < baseStart_4889105 := by decide
  rcases family_descends (prefixWord ++ tailWord_4889105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4889116 : List Nat := [2, 2, 3, 1, 2, 4, 1, 1, 2, 2, 3]
def baseStart_4889116 : Nat := 118140960795 + 4889116 * 2 ^ 59
def prefixEnd_4889116 : Nat := 4983230072969 + 3 ^ 40 * 4889116 * 2
def baseEnd_4889116 : Nat := 2510466483587398544865371

theorem tailTrace_4889116 : CollatzResearch.WordTrace tailWord_4889116 prefixEnd_4889116 2510466483587398544865371 := by
  unfold tailWord_4889116
  simp only [CollatzResearch.WordTrace]
  refine ⟨89160355077787600690299601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118880473437050134253732801 89160355077787600690299601)
  ·
    refine ⟨66870266308340700517724701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89160355077787600690299601 66870266308340700517724701)
    ·
      refine ⟨25076349865627762694146763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66870266308340700517724701 25076349865627762694146763)
      ·
        refine ⟨37614524798441644041220145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25076349865627762694146763 37614524798441644041220145)
        ·
          refine ⟨28210893598831233030915109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37614524798441644041220145 28210893598831233030915109)
          ·
            refine ⟨5289542549780856193296583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28210893598831233030915109 5289542549780856193296583)
            ·
              refine ⟨7934313824671284289944875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5289542549780856193296583 7934313824671284289944875)
              ·
                refine ⟨11901470737006926434917313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7934313824671284289944875 11901470737006926434917313)
                ·
                  refine ⟨8926103052755194826187985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11901470737006926434917313 8926103052755194826187985)
                  ·
                    refine ⟨6694577289566396119640989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8926103052755194826187985 6694577289566396119640989)
                    ·
                      refine ⟨2510466483587398544865371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6694577289566396119640989 2510466483587398544865371)
                      ·
                        rfl

theorem cell23_4889116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 1, 1, 2, 2, 3].length) (baseStart_4889116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4889116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4889116 prefixEnd_4889116 := by exact prefixLift 4889116
  have htrace : WordTrace (prefixWord ++ tailWord_4889116) baseStart_4889116 baseEnd_4889116 := by
    simpa [prefixWord, tailWord_4889116, baseEnd_4889116] using wordTrace_append hprefix tailTrace_4889116
  have hstable : (prefixWord ++ tailWord_4889116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4889116).length < 2 ^ (prefixWord ++ tailWord_4889116).sum := by decide
  have hdescent : baseEnd_4889116 < baseStart_4889116 := by decide
  rcases family_descends (prefixWord ++ tailWord_4889116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4889139 : List Nat := [1, 1, 1, 2, 4, 2, 2, 1, 4, 3, 2]
def baseStart_4889139 : Nat := 118140960795 + 4889139 * 2 ^ 59
def prefixEnd_4889139 : Nat := 4983230072969 + 3 ^ 40 * 4889139 * 2
def baseEnd_4889139 : Nat := 2510478293642451954877765

theorem tailTrace_4889139 : CollatzResearch.WordTrace tailWord_4889139 prefixEnd_4889139 2510478293642451954877765 := by
  unfold tailWord_4889139
  simp only [CollatzResearch.WordTrace]
  refine ⟨178321549034491876308686471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118881032689661250872457647 178321549034491876308686471)
  ·
    refine ⟨267482323551737814463029707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178321549034491876308686471 267482323551737814463029707)
    ·
      refine ⟨401223485327606721694544561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 267482323551737814463029707 401223485327606721694544561)
      ·
        refine ⟨300917613995705041270908421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 401223485327606721694544561 300917613995705041270908421)
        ·
          refine ⟨56422052624194695238295329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 300917613995705041270908421 56422052624194695238295329)
          ·
            refine ⟨42316539468146021428721497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56422052624194695238295329 42316539468146021428721497)
            ·
              refine ⟨31737404601109516071541123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42316539468146021428721497 31737404601109516071541123)
              ·
                refine ⟨47606106901664274107311685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31737404601109516071541123 47606106901664274107311685)
                ·
                  refine ⟨8926145044062051395120941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47606106901664274107311685 8926145044062051395120941)
                  ·
                    refine ⟨3347304391523269273170353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8926145044062051395120941 3347304391523269273170353)
                    ·
                      refine ⟨2510478293642451954877765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3347304391523269273170353 2510478293642451954877765)
                      ·
                        rfl

theorem cell23_4889139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 1, 4, 3, 2].length) (baseStart_4889139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4889139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4889139 prefixEnd_4889139 := by exact prefixLift 4889139
  have htrace : WordTrace (prefixWord ++ tailWord_4889139) baseStart_4889139 baseEnd_4889139 := by
    simpa [prefixWord, tailWord_4889139, baseEnd_4889139] using wordTrace_append hprefix tailTrace_4889139
  have hstable : (prefixWord ++ tailWord_4889139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4889139).length < 2 ^ (prefixWord ++ tailWord_4889139).sum := by decide
  have hdescent : baseEnd_4889139 < baseStart_4889139 := by decide
  rcases family_descends (prefixWord ++ tailWord_4889139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4889146 : List Nat := [3, 1, 1, 1, 3, 4, 2, 1, 3, 1, 3]
def baseStart_4889146 : Nat := 118140960795 + 4889146 * 2 ^ 59
def prefixEnd_4889146 : Nat := 4983230072969 + 3 ^ 40 * 4889146 * 2
def baseEnd_4889146 : Nat := 2510481888007033427490233

theorem tailTrace_4889146 : CollatzResearch.WordTrace tailWord_4889146 prefixEnd_4889146 2510481888007033427490233 := by
  unfold tailWord_4889146
  simp only [CollatzResearch.WordTrace]
  refine ⟨44580451086366629126047823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118881202896977677669460861 44580451086366629126047823)
  ·
    refine ⟨66870676629549943689071735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44580451086366629126047823 66870676629549943689071735)
    ·
      refine ⟨100306014944324915533607603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66870676629549943689071735 100306014944324915533607603)
      ·
        refine ⟨150459022416487373300411405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100306014944324915533607603 150459022416487373300411405)
        ·
          refine ⟨56422133406182764987654277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 150459022416487373300411405 56422133406182764987654277)
          ·
            refine ⟨10579150013659268435185177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56422133406182764987654277 10579150013659268435185177)
            ·
              refine ⟨7934362510244451326388883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10579150013659268435185177 7934362510244451326388883)
              ·
                refine ⟨11901543765366676989583325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7934362510244451326388883 11901543765366676989583325)
                ·
                  refine ⟨4463078912012503871093747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11901543765366676989583325 4463078912012503871093747)
                  ·
                    refine ⟨6694618368018755806640621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4463078912012503871093747 6694618368018755806640621)
                    ·
                      refine ⟨2510481888007033427490233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6694618368018755806640621 2510481888007033427490233)
                      ·
                        rfl

theorem cell23_4889146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 2, 1, 3, 1, 3].length) (baseStart_4889146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4889146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4889146 prefixEnd_4889146 := by exact prefixLift 4889146
  have htrace : WordTrace (prefixWord ++ tailWord_4889146) baseStart_4889146 baseEnd_4889146 := by
    simpa [prefixWord, tailWord_4889146, baseEnd_4889146] using wordTrace_append hprefix tailTrace_4889146
  have hstable : (prefixWord ++ tailWord_4889146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4889146).length < 2 ^ (prefixWord ++ tailWord_4889146).sum := by decide
  have hdescent : baseEnd_4889146 < baseStart_4889146 := by decide
  rcases family_descends (prefixWord ++ tailWord_4889146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4889152 : List Nat := [2, 1, 1, 2, 2, 2, 2, 1, 5, 1, 4]
def baseStart_4889152 : Nat := 118140960795 + 4889152 * 2 ^ 59
def prefixEnd_4889152 : Nat := 4983230072969 + 3 ^ 40 * 4889152 * 2
def baseEnd_4889152 : Nat := 2510484968890960404015205

theorem tailTrace_4889152 : CollatzResearch.WordTrace tailWord_4889152 prefixEnd_4889152 2510484968890960404015205 := by
  unfold tailWord_4889152
  simp only [CollatzResearch.WordTrace]
  refine ⟨89161011591722389764454855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118881348788963186352606473 89161011591722389764454855)
  ·
    refine ⟨133741517387583584646682283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89161011591722389764454855 133741517387583584646682283)
    ·
      refine ⟨200612276081375376970023425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133741517387583584646682283 200612276081375376970023425)
      ·
        refine ⟨150459207061031532727517569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 200612276081375376970023425 150459207061031532727517569)
        ·
          refine ⟨112844405295773649545638177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150459207061031532727517569 112844405295773649545638177)
          ·
            refine ⟨84633303971830237159228633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112844405295773649545638177 84633303971830237159228633)
            ·
              refine ⟨63474977978872677869421475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84633303971830237159228633 63474977978872677869421475)
              ·
                refine ⟨95212466968309016804132213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63474977978872677869421475 95212466968309016804132213)
                ·
                  refine ⟨8926168778278970325387395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 95212466968309016804132213 8926168778278970325387395)
                  ·
                    refine ⟨13389253167418455488081093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8926168778278970325387395 13389253167418455488081093)
                    ·
                      refine ⟨2510484968890960404015205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13389253167418455488081093 2510484968890960404015205)
                      ·
                        rfl

theorem cell23_4889152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 5, 1, 4].length) (baseStart_4889152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4889152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4889152 prefixEnd_4889152 := by exact prefixLift 4889152
  have htrace : WordTrace (prefixWord ++ tailWord_4889152) baseStart_4889152 baseEnd_4889152 := by
    simpa [prefixWord, tailWord_4889152, baseEnd_4889152] using wordTrace_append hprefix tailTrace_4889152
  have hstable : (prefixWord ++ tailWord_4889152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4889152).length < 2 ^ (prefixWord ++ tailWord_4889152).sum := by decide
  have hdescent : baseEnd_4889152 < baseStart_4889152 := by decide
  rcases family_descends (prefixWord ++ tailWord_4889152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4889169 : List Nat := [1, 2, 2, 1, 3, 3, 1, 4, 1, 1, 4]
def baseStart_4889169 : Nat := 118140960795 + 4889169 * 2 ^ 59
def prefixEnd_4889169 : Nat := 4983230072969 + 3 ^ 40 * 4889169 * 2
def baseEnd_4889169 : Nat := 2510493698062086837502627

theorem tailTrace_4889169 : CollatzResearch.WordTrace tailWord_4889169 prefixEnd_4889169 2510493698062086837502627 := by
  unfold tailWord_4889169
  simp only [CollatzResearch.WordTrace]
  refine ⟨178322643224383191432278561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118881762149588794288185707 178322643224383191432278561)
  ·
    refine ⟨133741982418287393574208921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178322643224383191432278561 133741982418287393574208921)
    ·
      refine ⟨100306486813715545180656691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133741982418287393574208921 100306486813715545180656691)
      ·
        refine ⟨150459730220573317770985037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100306486813715545180656691 150459730220573317770985037)
        ·
          refine ⟨56422398832714994164119389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 150459730220573317770985037 56422398832714994164119389)
          ·
            refine ⟨21158399562268122811544771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56422398832714994164119389 21158399562268122811544771)
            ·
              refine ⟨31737599343402184217317157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21158399562268122811544771 31737599343402184217317157)
              ·
                refine ⟨5950799876887909540746967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31737599343402184217317157 5950799876887909540746967)
                ·
                  refine ⟨8926199815331864311120451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5950799876887909540746967 8926199815331864311120451)
                  ·
                    refine ⟨13389299722997796466680677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8926199815331864311120451 13389299722997796466680677)
                    ·
                      refine ⟨2510493698062086837502627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13389299722997796466680677 2510493698062086837502627)
                      ·
                        rfl

theorem cell23_4889169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 4, 1, 1, 4].length) (baseStart_4889169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4889169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4889169 prefixEnd_4889169 := by exact prefixLift 4889169
  have htrace : WordTrace (prefixWord ++ tailWord_4889169) baseStart_4889169 baseEnd_4889169 := by
    simpa [prefixWord, tailWord_4889169, baseEnd_4889169] using wordTrace_append hprefix tailTrace_4889169
  have hstable : (prefixWord ++ tailWord_4889169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4889169).length < 2 ^ (prefixWord ++ tailWord_4889169).sum := by decide
  have hdescent : baseEnd_4889169 < baseStart_4889169 := by decide
  rcases family_descends (prefixWord ++ tailWord_4889169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4889236 : List Nat := [2, 4, 2, 2, 1, 1, 1, 1, 3, 3, 3]
def baseStart_4889236 : Nat := 118140960795 + 4889236 * 2 ^ 59
def prefixEnd_4889236 : Nat := 4983230072969 + 3 ^ 40 * 4889236 * 2
def baseEnd_4889236 : Nat := 2510528101265938075364819

theorem tailTrace_4889236 : CollatzResearch.WordTrace tailWord_4889236 prefixEnd_4889236 2510528101265938075364819 := by
  unfold tailWord_4889236
  simp only [CollatzResearch.WordTrace]
  refine ⟨89162543457570230937483781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118883391276760307916645041 89162543457570230937483781)
  ·
    refine ⟨16717976898294418300778209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89162543457570230937483781 16717976898294418300778209)
    ·
      refine ⟨12538482673720813725583657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16717976898294418300778209 12538482673720813725583657)
      ·
        refine ⟨9403862005290610294187743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12538482673720813725583657 9403862005290610294187743)
        ·
          refine ⟨14105793007935915441281615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9403862005290610294187743 14105793007935915441281615)
          ·
            refine ⟨21158689511903873161922423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14105793007935915441281615 21158689511903873161922423)
            ·
              refine ⟨31738034267855809742883635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21158689511903873161922423 31738034267855809742883635)
              ·
                refine ⟨47607051401783714614325453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31738034267855809742883635 47607051401783714614325453)
                ·
                  refine ⟨17852644275668892980372045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47607051401783714614325453 17852644275668892980372045)
                  ·
                    refine ⟨6694741603375834867639517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17852644275668892980372045 6694741603375834867639517)
                    ·
                      refine ⟨2510528101265938075364819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6694741603375834867639517 2510528101265938075364819)
                      ·
                        rfl

theorem cell23_4889236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_4889236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4889236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4889236 prefixEnd_4889236 := by exact prefixLift 4889236
  have htrace : WordTrace (prefixWord ++ tailWord_4889236) baseStart_4889236 baseEnd_4889236 := by
    simpa [prefixWord, tailWord_4889236, baseEnd_4889236] using wordTrace_append hprefix tailTrace_4889236
  have hstable : (prefixWord ++ tailWord_4889236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4889236).length < 2 ^ (prefixWord ++ tailWord_4889236).sum := by decide
  have hdescent : baseEnd_4889236 < baseStart_4889236 := by decide
  rcases family_descends (prefixWord ++ tailWord_4889236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4889269 : List Nat := [1, 3, 3, 3, 1, 1, 1, 1, 1, 8]
def baseStart_4889269 : Nat := 118140960795 + 4889269 * 2 ^ 59
def prefixEnd_4889269 : Nat := 4983230072969 + 3 ^ 40 * 4889269 * 2
def baseEnd_4889269 : Nat := 836848348709178815417389

theorem tailTrace_4889269 : CollatzResearch.WordTrace tailWord_4889269 prefixEnd_4889269 836848348709178815417389 := by
  unfold tailWord_4889269
  simp only [CollatzResearch.WordTrace]
  refine ⟨178326290524020908510918861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118884193682680605673945907 178326290524020908510918861)
  ·
    refine ⟨66872358946507840691594573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 178326290524020908510918861 66872358946507840691594573)
    ·
      refine ⟨25077134604940440259347965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66872358946507840691594573 25077134604940440259347965)
      ·
        refine ⟨9403925476852665097255487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25077134604940440259347965 9403925476852665097255487)
        ·
          refine ⟨14105888215278997645883231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9403925476852665097255487 14105888215278997645883231)
          ·
            refine ⟨21158832322918496468824847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14105888215278997645883231 21158832322918496468824847)
            ·
              refine ⟨31738248484377744703237271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21158832322918496468824847 31738248484377744703237271)
              ·
                refine ⟨47607372726566617054855907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31738248484377744703237271 47607372726566617054855907)
                ·
                  refine ⟨71411059089849925582283861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47607372726566617054855907 71411059089849925582283861)
                  ·
                    refine ⟨836848348709178815417389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 71411059089849925582283861 836848348709178815417389)
                    ·
                      rfl

theorem cell23_4889269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 1, 1, 8].length) (baseStart_4889269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4889269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4889269 prefixEnd_4889269 := by exact prefixLift 4889269
  have htrace : WordTrace (prefixWord ++ tailWord_4889269) baseStart_4889269 baseEnd_4889269 := by
    simpa [prefixWord, tailWord_4889269, baseEnd_4889269] using wordTrace_append hprefix tailTrace_4889269
  have hstable : (prefixWord ++ tailWord_4889269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4889269).length < 2 ^ (prefixWord ++ tailWord_4889269).sum := by decide
  have hdescent : baseEnd_4889269 < baseStart_4889269 := by decide
  rcases family_descends (prefixWord ++ tailWord_4889269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4889270 : List Nat := [5, 1, 3, 1, 2, 1, 2, 1, 1, 3, 3]
def baseStart_4889270 : Nat := 118140960795 + 4889270 * 2 ^ 59
def prefixEnd_4889270 : Nat := 4983230072969 + 3 ^ 40 * 4889270 * 2
def baseEnd_4889270 : Nat := 2510545559608190942339663

theorem tailTrace_4889270 : CollatzResearch.WordTrace tailWord_4889270 prefixEnd_4889270 2510545559608190942339663 := by
  unfold tailWord_4889270
  simp only [CollatzResearch.WordTrace]
  refine ⟨11145395437313580355106579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 118884217998011523787803509 11145395437313580355106579)
  ·
    refine ⟨16718093155970370532659869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11145395437313580355106579 16718093155970370532659869)
    ·
      refine ⟨6269284933488888949747451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16718093155970370532659869 6269284933488888949747451)
      ·
        refine ⟨9403927400233333424621177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6269284933488888949747451 9403927400233333424621177)
        ·
          refine ⟨7052945550175000068465883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9403927400233333424621177 7052945550175000068465883)
          ·
            refine ⟨10579418325262500102698825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7052945550175000068465883 10579418325262500102698825)
            ·
              refine ⟨7934563743946875077024119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10579418325262500102698825 7934563743946875077024119)
              ·
                refine ⟨11901845615920312615536179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7934563743946875077024119 11901845615920312615536179)
                ·
                  refine ⟨17852768423880468923304269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11901845615920312615536179 17852768423880468923304269)
                  ·
                    refine ⟨6694788158955175846239101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17852768423880468923304269 6694788158955175846239101)
                    ·
                      refine ⟨2510545559608190942339663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6694788158955175846239101 2510545559608190942339663)
                      ·
                        rfl

theorem cell23_4889270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_4889270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4889270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4889270 prefixEnd_4889270 := by exact prefixLift 4889270
  have htrace : WordTrace (prefixWord ++ tailWord_4889270) baseStart_4889270 baseEnd_4889270 := by
    simpa [prefixWord, tailWord_4889270, baseEnd_4889270] using wordTrace_append hprefix tailTrace_4889270
  have hstable : (prefixWord ++ tailWord_4889270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4889270).length < 2 ^ (prefixWord ++ tailWord_4889270).sum := by decide
  have hdescent : baseEnd_4889270 < baseStart_4889270 := by decide
  rcases family_descends (prefixWord ++ tailWord_4889270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4889316 : List Nat := [2, 3, 1, 1, 1, 4, 2, 4, 5]
def baseStart_4889316 : Nat := 118140960795 + 4889316 * 2 ^ 59
def prefixEnd_4889316 : Nat := 4983230072969 + 3 ^ 40 * 4889316 * 2
def baseEnd_4889316 : Nat := 278952131079810862484939

theorem tailTrace_4889316 : CollatzResearch.WordTrace tailWord_4889316 prefixEnd_4889316 278952131079810862484939 := by
  unfold tailWord_4889316
  simp only [CollatzResearch.WordTrace]
  refine ⟨89164002377425317768939901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118885336503233757025253201 89164002377425317768939901)
  ·
    refine ⟨33436500891534494163352463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89164002377425317768939901 33436500891534494163352463)
    ·
      refine ⟨50154751337301741245028695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33436500891534494163352463 50154751337301741245028695)
      ·
        refine ⟨75232127005952611867543043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50154751337301741245028695 75232127005952611867543043)
        ·
          refine ⟨112848190508928917801314565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75232127005952611867543043 112848190508928917801314565)
          ·
            refine ⟨21159035720424172087746481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 112848190508928917801314565 21159035720424172087746481)
            ·
              refine ⟨15869276790318129065809861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21159035720424172087746481 15869276790318129065809861)
              ·
                refine ⟨2975489398184649199839349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15869276790318129065809861 2975489398184649199839349)
                ·
                  refine ⟨278952131079810862484939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2975489398184649199839349 278952131079810862484939)
                  ·
                    rfl

theorem cell23_4889316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 4, 5].length) (baseStart_4889316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4889316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4889316 prefixEnd_4889316 := by exact prefixLift 4889316
  have htrace : WordTrace (prefixWord ++ tailWord_4889316) baseStart_4889316 baseEnd_4889316 := by
    simpa [prefixWord, tailWord_4889316, baseEnd_4889316] using wordTrace_append hprefix tailTrace_4889316
  have hstable : (prefixWord ++ tailWord_4889316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4889316).length < 2 ^ (prefixWord ++ tailWord_4889316).sum := by decide
  have hdescent : baseEnd_4889316 < baseStart_4889316 := by decide
  rcases family_descends (prefixWord ++ tailWord_4889316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4889326 : List Nat := [4, 1, 2, 1, 1, 3, 2, 1, 2, 3, 3]
def baseStart_4889326 : Nat := 118140960795 + 4889326 * 2 ^ 59
def prefixEnd_4889326 : Nat := 4983230072969 + 3 ^ 40 * 4889326 * 2
def baseEnd_4889326 : Nat := 2510574314524842723239405

theorem tailTrace_4889326 : CollatzResearch.WordTrace tailWord_4889326 prefixEnd_4889326 2510574314524842723239405 := by
  unfold tailWord_4889326
  simp only [CollatzResearch.WordTrace]
  refine ⟨22291046185601800905717979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118885579656542938163829221 22291046185601800905717979)
  ·
    refine ⟨33436569278402701358576969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22291046185601800905717979 33436569278402701358576969)
    ·
      refine ⟨25077426958802026018932727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33436569278402701358576969 25077426958802026018932727)
      ·
        refine ⟨37616140438203039028399091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25077426958802026018932727 37616140438203039028399091)
        ·
          refine ⟨56424210657304558542598637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37616140438203039028399091 56424210657304558542598637)
          ·
            refine ⟨21159078996489209453474489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56424210657304558542598637 21159078996489209453474489)
            ·
              refine ⟨15869309247366907090105867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21159078996489209453474489 15869309247366907090105867)
              ·
                refine ⟨23803963871050360635158801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15869309247366907090105867 23803963871050360635158801)
                ·
                  refine ⟨17852972903287770476369101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23803963871050360635158801 17852972903287770476369101)
                  ·
                    refine ⟨6694864838732913928638413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17852972903287770476369101 6694864838732913928638413)
                    ·
                      refine ⟨2510574314524842723239405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6694864838732913928638413 2510574314524842723239405)
                      ·
                        rfl

theorem cell23_4889326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 1, 2, 3, 3].length) (baseStart_4889326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4889326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4889326 prefixEnd_4889326 := by exact prefixLift 4889326
  have htrace : WordTrace (prefixWord ++ tailWord_4889326) baseStart_4889326 baseEnd_4889326 := by
    simpa [prefixWord, tailWord_4889326, baseEnd_4889326] using wordTrace_append hprefix tailTrace_4889326
  have hstable : (prefixWord ++ tailWord_4889326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4889326).length < 2 ^ (prefixWord ++ tailWord_4889326).sum := by decide
  have hdescent : baseEnd_4889326 < baseStart_4889326 := by decide
  rcases family_descends (prefixWord ++ tailWord_4889326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4889346 : List Nat := [3, 4, 1, 1, 1, 2, 2, 1, 1, 7]
def baseStart_4889346 : Nat := 118140960795 + 4889346 * 2 ^ 59
def prefixEnd_4889346 : Nat := 4983230072969 + 3 ^ 40 * 4889346 * 2
def baseEnd_4889346 : Nat := 836861528045977548329771

theorem tailTrace_4889346 : CollatzResearch.WordTrace tailWord_4889346 prefixEnd_4889346 836861528045977548329771 := by
  unfold tailWord_4889346
  simp only [CollatzResearch.WordTrace]
  refine ⟨44582274736185487665367973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118886065963161300440981261 44582274736185487665367973)
  ·
    refine ⟨8359176513034778937256495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44582274736185487665367973 8359176513034778937256495)
    ·
      refine ⟨12538764769552168405884743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8359176513034778937256495 12538764769552168405884743)
      ·
        refine ⟨18808147154328252608827115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12538764769552168405884743 18808147154328252608827115)
        ·
          refine ⟨28212220731492378913240673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18808147154328252608827115 28212220731492378913240673)
          ·
            refine ⟨21159165548619284184930505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28212220731492378913240673 21159165548619284184930505)
            ·
              refine ⟨15869374161464463138697879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21159165548619284184930505 15869374161464463138697879)
              ·
                refine ⟨23804061242196694708046819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15869374161464463138697879 23804061242196694708046819)
                ·
                  refine ⟨35706091863295042062070229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23804061242196694708046819 35706091863295042062070229)
                  ·
                    refine ⟨836861528045977548329771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35706091863295042062070229 836861528045977548329771)
                    ·
                      rfl

theorem cell23_4889346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_4889346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4889346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4889346 prefixEnd_4889346 := by exact prefixLift 4889346
  have htrace : WordTrace (prefixWord ++ tailWord_4889346) baseStart_4889346 baseEnd_4889346 := by
    simpa [prefixWord, tailWord_4889346, baseEnd_4889346] using wordTrace_append hprefix tailTrace_4889346
  have hstable : (prefixWord ++ tailWord_4889346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4889346).length < 2 ^ (prefixWord ++ tailWord_4889346).sum := by decide
  have hdescent : baseEnd_4889346 < baseStart_4889346 := by decide
  rcases family_descends (prefixWord ++ tailWord_4889346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4889349 : List Nat := [1, 3, 1, 1, 2, 1, 1, 2, 6, 1, 4]
def baseStart_4889349 : Nat := 118140960795 + 4889349 * 2 ^ 59
def prefixEnd_4889349 : Nat := 4983230072969 + 3 ^ 40 * 4889349 * 2
def baseEnd_4889349 : Nat := 2510586124579896133251799

theorem tailTrace_4889349 : CollatzResearch.WordTrace tailWord_4889349 prefixEnd_4889349 2510586124579896133251799 := by
  unfold tailWord_4889349
  simp only [CollatzResearch.WordTrace]
  refine ⟨178329208363731082173831101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118886138909154054782554067 178329208363731082173831101)
  ·
    refine ⟨66873453136399155815186663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 178329208363731082173831101 66873453136399155815186663)
    ·
      refine ⟨100310179704598733722779995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66873453136399155815186663 100310179704598733722779995)
      ·
        refine ⟨150465269556898100584169993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100310179704598733722779995 150465269556898100584169993)
        ·
          refine ⟨112848952167673575438127495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150465269556898100584169993 112848952167673575438127495)
          ·
            refine ⟨169273428251510363157191243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112848952167673575438127495 169273428251510363157191243)
            ·
              refine ⟨253910142377265544735786865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 169273428251510363157191243 253910142377265544735786865)
              ·
                refine ⟨190432606782949158551840149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 253910142377265544735786865 190432606782949158551840149)
                ·
                  refine ⟨8926528442950741807117507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 190432606782949158551840149 8926528442950741807117507)
                  ·
                    refine ⟨13389792664426112710676261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8926528442950741807117507 13389792664426112710676261)
                    ·
                      refine ⟨2510586124579896133251799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13389792664426112710676261 2510586124579896133251799)
                      ·
                        rfl

theorem cell23_4889349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 6, 1, 4].length) (baseStart_4889349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4889349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4889349 prefixEnd_4889349 := by exact prefixLift 4889349
  have htrace : WordTrace (prefixWord ++ tailWord_4889349) baseStart_4889349 baseEnd_4889349 := by
    simpa [prefixWord, tailWord_4889349, baseEnd_4889349] using wordTrace_append hprefix tailTrace_4889349
  have hstable : (prefixWord ++ tailWord_4889349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4889349).length < 2 ^ (prefixWord ++ tailWord_4889349).sum := by decide
  have hdescent : baseEnd_4889349 < baseStart_4889349 := by decide
  rcases family_descends (prefixWord ++ tailWord_4889349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4889369 : List Nat := [1, 2, 1, 2, 1, 1, 1, 4, 3, 4, 3]
def baseStart_4889369 : Nat := 118140960795 + 4889369 * 2 ^ 59
def prefixEnd_4889369 : Nat := 4983230072969 + 3 ^ 40 * 4889369 * 2
def baseEnd_4889369 : Nat := 2510596394192986055001707

theorem tailTrace_4889369 : CollatzResearch.WordTrace tailWord_4889369 prefixEnd_4889369 2510596394192986055001707 := by
  unfold tailWord_4889369
  simp only [CollatzResearch.WordTrace]
  refine ⟨178329937823658625589559161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118886625215772417059706107 178329937823658625589559161)
  ·
    refine ⟨133747453367743969192169371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178329937823658625589559161 133747453367743969192169371)
    ·
      refine ⟨200621180051615953788254057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133747453367743969192169371 200621180051615953788254057)
      ·
        refine ⟨150465885038711965341190543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 200621180051615953788254057 150465885038711965341190543)
        ·
          refine ⟨225698827558067948011785815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150465885038711965341190543 225698827558067948011785815)
          ·
            refine ⟨338548241337101922017678723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 225698827558067948011785815 338548241337101922017678723)
            ·
              refine ⟨507822362005652883026518085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 338548241337101922017678723 507822362005652883026518085)
              ·
                refine ⟨95216692876059915567472141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 507822362005652883026518085 95216692876059915567472141)
                ·
                  refine ⟨35706259828522468337802053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 95216692876059915567472141 35706259828522468337802053)
                  ·
                    refine ⟨6694923717847962813337885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35706259828522468337802053 6694923717847962813337885)
                    ·
                      refine ⟨2510596394192986055001707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6694923717847962813337885 2510596394192986055001707)
                      ·
                        rfl

theorem cell23_4889369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 3, 4, 3].length) (baseStart_4889369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4889369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4889369 prefixEnd_4889369 := by exact prefixLift 4889369
  have htrace : WordTrace (prefixWord ++ tailWord_4889369) baseStart_4889369 baseEnd_4889369 := by
    simpa [prefixWord, tailWord_4889369, baseEnd_4889369] using wordTrace_append hprefix tailTrace_4889369
  have hstable : (prefixWord ++ tailWord_4889369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4889369).length < 2 ^ (prefixWord ++ tailWord_4889369).sum := by decide
  have hdescent : baseEnd_4889369 < baseStart_4889369 := by decide
  rcases family_descends (prefixWord ++ tailWord_4889369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4889373 : List Nat := [1, 4, 2, 4, 1, 1, 1, 1, 1, 2, 5]
def baseStart_4889373 : Nat := 118140960795 + 4889373 * 2 ^ 59
def prefixEnd_4889373 : Nat := 4983230072969 + 3 ^ 40 * 4889373 * 2
def baseEnd_4889373 : Nat := 2510598448115604039351689

theorem tailTrace_4889373 : CollatzResearch.WordTrace tailWord_4889373 prefixEnd_4889373 2510598448115604039351689 := by
  unfold tailWord_4889373
  simp only [CollatzResearch.WordTrace]
  refine ⟨178330083715644134272704773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118886722477096089515136515 178330083715644134272704773)
  ·
    refine ⟨33436890696683275176132145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 178330083715644134272704773 33436890696683275176132145)
    ·
      refine ⟨25077668022512456382099109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33436890696683275176132145 25077668022512456382099109)
      ·
        refine ⟨4702062754221085571643583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25077668022512456382099109 4702062754221085571643583)
        ·
          refine ⟨7053094131331628357465375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4702062754221085571643583 7053094131331628357465375)
          ·
            refine ⟨10579641196997442536198063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7053094131331628357465375 10579641196997442536198063)
            ·
              refine ⟨15869461795496163804297095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10579641196997442536198063 15869461795496163804297095)
              ·
                refine ⟨23804192693244245706445643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15869461795496163804297095 23804192693244245706445643)
                ·
                  refine ⟨35706289039866368559668465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23804192693244245706445643 35706289039866368559668465)
                  ·
                    refine ⟨26779716779899776419751349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35706289039866368559668465 26779716779899776419751349)
                    ·
                      refine ⟨2510598448115604039351689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26779716779899776419751349 2510598448115604039351689)
                      ·
                        rfl

theorem cell23_4889373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_4889373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4889373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4889373 prefixEnd_4889373 := by exact prefixLift 4889373
  have htrace : WordTrace (prefixWord ++ tailWord_4889373) baseStart_4889373 baseEnd_4889373 := by
    simpa [prefixWord, tailWord_4889373, baseEnd_4889373] using wordTrace_append hprefix tailTrace_4889373
  have hstable : (prefixWord ++ tailWord_4889373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4889373).length < 2 ^ (prefixWord ++ tailWord_4889373).sum := by decide
  have hdescent : baseEnd_4889373 < baseStart_4889373 := by decide
  rcases family_descends (prefixWord ++ tailWord_4889373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4889456 : List Nat := [2, 1, 1, 1, 4, 1, 4, 1, 3, 1, 4]
def baseStart_4889456 : Nat := 118140960795 + 4889456 * 2 ^ 59
def prefixEnd_4889456 : Nat := 4983230072969 + 3 ^ 40 * 4889456 * 2
def baseEnd_4889456 : Nat := 2510641067009927214613807

theorem tailTrace_4889456 : CollatzResearch.WordTrace tailWord_4889456 prefixEnd_4889456 2510641067009927214613807 := by
  unfold tailWord_4889456
  simp only [CollatzResearch.WordTrace]
  refine ⟨89166555487171719723988111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118888740649562292965317481 89166555487171719723988111)
  ·
    refine ⟨133749833230757579585982167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89166555487171719723988111 133749833230757579585982167)
    ·
      refine ⟨200624749846136369378973251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133749833230757579585982167 200624749846136369378973251)
      ·
        refine ⟨300937124769204554068459877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200624749846136369378973251 300937124769204554068459877)
        ·
          refine ⟨56425710894225853887836227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 300937124769204554068459877 56425710894225853887836227)
          ·
            refine ⟨84638566341338780831754341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56425710894225853887836227 84638566341338780831754341)
            ·
              refine ⟨15869731189001021405953939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 84638566341338780831754341 15869731189001021405953939)
              ·
                refine ⟨23804596783501532108930909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15869731189001021405953939 23804596783501532108930909)
                ·
                  refine ⟨8926723793813074540849091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23804596783501532108930909 8926723793813074540849091)
                  ·
                    refine ⟨13390085690719611811273637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8926723793813074540849091 13390085690719611811273637)
                    ·
                      refine ⟨2510641067009927214613807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13390085690719611811273637 2510641067009927214613807)
                      ·
                        rfl

theorem cell23_4889456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 1, 3, 1, 4].length) (baseStart_4889456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4889456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4889456 prefixEnd_4889456 := by exact prefixLift 4889456
  have htrace : WordTrace (prefixWord ++ tailWord_4889456) baseStart_4889456 baseEnd_4889456 := by
    simpa [prefixWord, tailWord_4889456, baseEnd_4889456] using wordTrace_append hprefix tailTrace_4889456
  have hstable : (prefixWord ++ tailWord_4889456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4889456).length < 2 ^ (prefixWord ++ tailWord_4889456).sum := by decide
  have hdescent : baseEnd_4889456 < baseStart_4889456 := by decide
  rcases family_descends (prefixWord ++ tailWord_4889456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4889466 : List Nat := [3, 1, 1, 1, 1, 1, 3, 4, 4, 4]
def baseStart_4889466 : Nat := 118140960795 + 4889466 * 2 ^ 59
def prefixEnd_4889466 : Nat := 4983230072969 + 3 ^ 40 * 4889466 * 2
def baseEnd_4889466 : Nat := 836882067272157391829587

theorem tailTrace_4889466 : CollatzResearch.WordTrace tailWord_4889466 prefixEnd_4889466 836882067272157391829587 := by
  unfold tailWord_4889466
  simp only [CollatzResearch.WordTrace]
  refine ⟨44583368926076802788960063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118888983802871474103893501 44583368926076802788960063)
  ·
    refine ⟨66875053389115204183440095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44583368926076802788960063 66875053389115204183440095)
    ·
      refine ⟨100312580083672806275160143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66875053389115204183440095 100312580083672806275160143)
      ·
        refine ⟨150468870125509209412740215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100312580083672806275160143 150468870125509209412740215)
        ·
          refine ⟨225703305188263814119110323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150468870125509209412740215 225703305188263814119110323)
          ·
            refine ⟨338554957782395721178665485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 225703305188263814119110323 338554957782395721178665485)
            ·
              refine ⟨126958109168398395441999557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 338554957782395721178665485 126958109168398395441999557)
              ·
                refine ⟨23804645469074699145374917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 126958109168398395441999557 23804645469074699145374917)
                ·
                  refine ⟨4463371025451506089757797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23804645469074699145374917 4463371025451506089757797)
                  ·
                    refine ⟨836882067272157391829587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4463371025451506089757797 836882067272157391829587)
                    ·
                      rfl

theorem cell23_4889466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 4, 4, 4].length) (baseStart_4889466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4889466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4889466 prefixEnd_4889466 := by exact prefixLift 4889466
  have htrace : WordTrace (prefixWord ++ tailWord_4889466) baseStart_4889466 baseEnd_4889466 := by
    simpa [prefixWord, tailWord_4889466, baseEnd_4889466] using wordTrace_append hprefix tailTrace_4889466
  have hstable : (prefixWord ++ tailWord_4889466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4889466).length < 2 ^ (prefixWord ++ tailWord_4889466).sum := by decide
  have hdescent : baseEnd_4889466 < baseStart_4889466 := by decide
  rcases family_descends (prefixWord ++ tailWord_4889466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4889474 : List Nat := [3, 4, 2, 2, 2, 1, 1, 2, 6]
def baseStart_4889474 : Nat := 118140960795 + 4889474 * 2 ^ 59
def prefixEnd_4889474 : Nat := 4983230072969 + 3 ^ 40 * 4889474 * 2
def baseEnd_4889474 : Nat := 278961145517967571576525

theorem tailTrace_4889474 : CollatzResearch.WordTrace tailWord_4889474 prefixEnd_4889474 278961145517967571576525 := by
  unfold tailWord_4889474
  simp only [CollatzResearch.WordTrace]
  refine ⟨44583441872069557130532869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118889178325518819014754317 44583441872069557130532869)
  ·
    refine ⟨8359395351013041961974913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44583441872069557130532869 8359395351013041961974913)
    ·
      refine ⟨6269546513259781471481185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8359395351013041961974913 6269546513259781471481185)
      ·
        refine ⟨4702159884944836103610889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6269546513259781471481185 4702159884944836103610889)
        ·
          refine ⟨3526619913708627077708167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4702159884944836103610889 3526619913708627077708167)
          ·
            refine ⟨5289929870562940616562251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3526619913708627077708167 5289929870562940616562251)
            ·
              refine ⟨7934894805844410924843377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5289929870562940616562251 7934894805844410924843377)
              ·
                refine ⟨5951171104383308193632533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7934894805844410924843377 5951171104383308193632533)
                ·
                  refine ⟨278961145517967571576525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5951171104383308193632533 278961145517967571576525)
                  ·
                    rfl

theorem cell23_4889474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 1, 2, 6].length) (baseStart_4889474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4889474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4889474 prefixEnd_4889474 := by exact prefixLift 4889474
  have htrace : WordTrace (prefixWord ++ tailWord_4889474) baseStart_4889474 baseEnd_4889474 := by
    simpa [prefixWord, tailWord_4889474, baseEnd_4889474] using wordTrace_append hprefix tailTrace_4889474
  have hstable : (prefixWord ++ tailWord_4889474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4889474).length < 2 ^ (prefixWord ++ tailWord_4889474).sum := by decide
  have hdescent : baseEnd_4889474 < baseStart_4889474 := by decide
  rcases family_descends (prefixWord ++ tailWord_4889474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4889476 : List Nat := [2, 3, 2, 1, 1, 1, 1, 5, 1, 1, 5]
def baseStart_4889476 : Nat := 118140960795 + 4889476 * 2 ^ 59
def prefixEnd_4889476 : Nat := 4983230072969 + 3 ^ 40 * 4889476 * 2
def baseEnd_4889476 : Nat := 2510651336623017136363715

theorem tailTrace_4889476 : CollatzResearch.WordTrace tailWord_4889476 prefixEnd_4889476 2510651336623017136363715 := by
  unfold tailWord_4889476
  simp only [CollatzResearch.WordTrace]
  refine ⟨89166920217135491431852141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118889226956180655242469521 89166920217135491431852141)
  ·
    refine ⟨33437595081425809286944553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89166920217135491431852141 33437595081425809286944553)
    ·
      refine ⟨25078196311069356965208415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33437595081425809286944553 25078196311069356965208415)
      ·
        refine ⟨37617294466604035447812623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25078196311069356965208415 37617294466604035447812623)
        ·
          refine ⟨56425941699906053171718935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37617294466604035447812623 56425941699906053171718935)
          ·
            refine ⟨84638912549859079757578403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56425941699906053171718935 84638912549859079757578403)
            ·
              refine ⟨126958368824788619636367605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84638912549859079757578403 126958368824788619636367605)
              ·
                refine ⟨11902347077323933090909463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 126958368824788619636367605 11902347077323933090909463)
                ·
                  refine ⟨17853520615985899636364195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11902347077323933090909463 17853520615985899636364195)
                  ·
                    refine ⟨26780280923978849454546293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17853520615985899636364195 26780280923978849454546293)
                    ·
                      refine ⟨2510651336623017136363715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26780280923978849454546293 2510651336623017136363715)
                      ·
                        rfl

theorem cell23_4889476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 5, 1, 1, 5].length) (baseStart_4889476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4889476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4889476 prefixEnd_4889476 := by exact prefixLift 4889476
  have htrace : WordTrace (prefixWord ++ tailWord_4889476) baseStart_4889476 baseEnd_4889476 := by
    simpa [prefixWord, tailWord_4889476, baseEnd_4889476] using wordTrace_append hprefix tailTrace_4889476
  have hstable : (prefixWord ++ tailWord_4889476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4889476).length < 2 ^ (prefixWord ++ tailWord_4889476).sum := by decide
  have hdescent : baseEnd_4889476 < baseStart_4889476 := by decide
  rcases family_descends (prefixWord ++ tailWord_4889476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4889483 : List Nat := [1, 1, 1, 1, 4, 2, 5, 2, 2, 4]
def baseStart_4889483 : Nat := 118140960795 + 4889483 * 2 ^ 59
def prefixEnd_4889483 : Nat := 4983230072969 + 3 ^ 40 * 4889483 * 2
def baseEnd_4889483 : Nat := 836884976995866202992061

theorem tailTrace_4889483 : CollatzResearch.WordTrace tailWord_4889483 prefixEnd_4889483 836884976995866202992061 := by
  unfold tailWord_4889483
  simp only [CollatzResearch.WordTrace]
  refine ⟨178334095745245623059209103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118889397163497082039472735 178334095745245623059209103)
  ·
    refine ⟨267501143617868434588813655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178334095745245623059209103 267501143617868434588813655)
    ·
      refine ⟨401251715426802651883220483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 267501143617868434588813655 401251715426802651883220483)
      ·
        refine ⟨601877573140203977824830725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 401251715426802651883220483 601877573140203977824830725)
        ·
          refine ⟨112852044963788245842155761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 601877573140203977824830725 112852044963788245842155761)
          ·
            refine ⟨84639033722841184381616821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112852044963788245842155761 84639033722841184381616821)
            ·
              refine ⟨7934909411516361035776577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 84639033722841184381616821 7934909411516361035776577)
              ·
                refine ⟨5951182058637270776832433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7934909411516361035776577 5951182058637270776832433)
                ·
                  refine ⟨4463386543977953082624325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5951182058637270776832433 4463386543977953082624325)
                  ·
                    refine ⟨836884976995866202992061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4463386543977953082624325 836884976995866202992061)
                    ·
                      rfl

theorem cell23_4889483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 5, 2, 2, 4].length) (baseStart_4889483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4889483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4889483 prefixEnd_4889483 := by exact prefixLift 4889483
  have htrace : WordTrace (prefixWord ++ tailWord_4889483) baseStart_4889483 baseEnd_4889483 := by
    simpa [prefixWord, tailWord_4889483, baseEnd_4889483] using wordTrace_append hprefix tailTrace_4889483
  have hstable : (prefixWord ++ tailWord_4889483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4889483).length < 2 ^ (prefixWord ++ tailWord_4889483).sum := by decide
  have hdescent : baseEnd_4889483 < baseStart_4889483 := by decide
  rcases family_descends (prefixWord ++ tailWord_4889483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4889489 : List Nat := [1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 7]
def baseStart_4889489 : Nat := 118140960795 + 4889489 * 2 ^ 59
def prefixEnd_4889489 : Nat := 4983230072969 + 3 ^ 40 * 4889489 * 2
def baseEnd_4889489 : Nat := 2510658011871525585501155

theorem tailTrace_4889489 : CollatzResearch.WordTrace tailWord_4889489 prefixEnd_4889489 2510658011871525585501155 := by
  unfold tailWord_4889489
  simp only [CollatzResearch.WordTrace]
  refine ⟨178334314583223886083927521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118889543055482590722618347 178334314583223886083927521)
  ·
    refine ⟨133750735937417914562945641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178334314583223886083927521 133750735937417914562945641)
    ·
      refine ⟨100313051953063435922209231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133750735937417914562945641 100313051953063435922209231)
      ·
        refine ⟨150469577929595153883313847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100313051953063435922209231 150469577929595153883313847)
        ·
          refine ⟨225704366894392730824970771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150469577929595153883313847 225704366894392730824970771)
          ·
            refine ⟨338556550341589096237456157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 225704366894392730824970771 338556550341589096237456157)
            ·
              refine ⟨126958706378095911089046059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 338556550341589096237456157 126958706378095911089046059)
              ·
                refine ⟨190438059567143866633569089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126958706378095911089046059 190438059567143866633569089)
                ·
                  refine ⟨142828544675357899975176817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 190438059567143866633569089 142828544675357899975176817)
                  ·
                    refine ⟨107121408506518424981382613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 142828544675357899975176817 107121408506518424981382613)
                    ·
                      refine ⟨2510658011871525585501155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 107121408506518424981382613 2510658011871525585501155)
                      ·
                        rfl

theorem cell23_4889489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 7].length) (baseStart_4889489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4889489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4889489 prefixEnd_4889489 := by exact prefixLift 4889489
  have htrace : WordTrace (prefixWord ++ tailWord_4889489) baseStart_4889489 baseEnd_4889489 := by
    simpa [prefixWord, tailWord_4889489, baseEnd_4889489] using wordTrace_append hprefix tailTrace_4889489
  have hstable : (prefixWord ++ tailWord_4889489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4889489).length < 2 ^ (prefixWord ++ tailWord_4889489).sum := by decide
  have hdescent : baseEnd_4889489 < baseStart_4889489 := by decide
  rcases family_descends (prefixWord ++ tailWord_4889489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4889500 : List Nat := [2, 2, 3, 3, 2, 2, 1, 1, 1, 6]
def baseStart_4889500 : Nat := 118140960795 + 4889500 * 2 ^ 59
def prefixEnd_4889500 : Nat := 4983230072969 + 3 ^ 40 * 4889500 * 2
def baseEnd_4889500 : Nat := 836887886719575014154535

theorem tailTrace_4889500 : CollatzResearch.WordTrace tailWord_4889500 prefixEnd_4889500 836887886719575014154535 := by
  unfold tailWord_4889500
  simp only [CollatzResearch.WordTrace]
  refine ⟨89167357893092017481288977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118889810524122689975051969 89167357893092017481288977)
  ·
    refine ⟨66875518419819013110966733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89167357893092017481288977 66875518419819013110966733)
    ·
      refine ⟨25078319407432129916612525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66875518419819013110966733 25078319407432129916612525)
      ·
        refine ⟨9404369777787048718729697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25078319407432129916612525 9404369777787048718729697)
        ·
          refine ⟨7053277333340286539047273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9404369777787048718729697 7053277333340286539047273)
          ·
            refine ⟨5289958000005214904285455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7053277333340286539047273 5289958000005214904285455)
            ·
              refine ⟨7934937000007822356428183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5289958000005214904285455 7934937000007822356428183)
              ·
                refine ⟨11902405500011733534642275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7934937000007822356428183 11902405500011733534642275)
                ·
                  refine ⟨17853608250017600301963413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11902405500011733534642275 17853608250017600301963413)
                  ·
                    refine ⟨836887886719575014154535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17853608250017600301963413 836887886719575014154535)
                    ·
                      rfl

theorem cell23_4889500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 1, 1, 1, 6].length) (baseStart_4889500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4889500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4889500 prefixEnd_4889500 := by exact prefixLift 4889500
  have htrace : WordTrace (prefixWord ++ tailWord_4889500) baseStart_4889500 baseEnd_4889500 := by
    simpa [prefixWord, tailWord_4889500, baseEnd_4889500] using wordTrace_append hprefix tailTrace_4889500
  have hstable : (prefixWord ++ tailWord_4889500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4889500).length < 2 ^ (prefixWord ++ tailWord_4889500).sum := by decide
  have hdescent : baseEnd_4889500 < baseStart_4889500 := by decide
  rcases family_descends (prefixWord ++ tailWord_4889500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4889503 : List Nat := [1, 1, 2, 5, 2, 1, 3, 1, 1, 2, 4]
def baseStart_4889503 : Nat := 118140960795 + 4889503 * 2 ^ 59
def prefixEnd_4889503 : Nat := 4983230072969 + 3 ^ 40 * 4889503 * 2
def baseEnd_4889503 : Nat := 2510665200600688530726091

theorem tailTrace_4889503 : CollatzResearch.WordTrace tailWord_4889503 prefixEnd_4889503 2510665200600688530726091 := by
  unfold tailWord_4889503
  simp only [CollatzResearch.WordTrace]
  refine ⟨178334825205173166474937163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118889883470115444316624775 178334825205173166474937163)
  ·
    refine ⟨267502237807759749712405745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178334825205173166474937163 267502237807759749712405745)
    ·
      refine ⟨200626678355819812284304309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 267502237807759749712405745 200626678355819812284304309)
      ·
        refine ⟨18808751095858107401653529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 200626678355819812284304309 18808751095858107401653529)
        ·
          refine ⟨14106563321893580551240147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18808751095858107401653529 14106563321893580551240147)
          ·
            refine ⟨21159844982840370826860221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14106563321893580551240147 21159844982840370826860221)
            ·
              refine ⟨7934941868565139060072583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21159844982840370826860221 7934941868565139060072583)
              ·
                refine ⟨11902412802847708590108875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7934941868565139060072583 11902412802847708590108875)
                ·
                  refine ⟨17853619204271562885163313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11902412802847708590108875 17853619204271562885163313)
                  ·
                    refine ⟨13390214403203672163872485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17853619204271562885163313 13390214403203672163872485)
                    ·
                      refine ⟨2510665200600688530726091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13390214403203672163872485 2510665200600688530726091)
                      ·
                        rfl

theorem cell23_4889503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 3, 1, 1, 2, 4].length) (baseStart_4889503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4889503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4889503 prefixEnd_4889503 := by exact prefixLift 4889503
  have htrace : WordTrace (prefixWord ++ tailWord_4889503) baseStart_4889503 baseEnd_4889503 := by
    simpa [prefixWord, tailWord_4889503, baseEnd_4889503] using wordTrace_append hprefix tailTrace_4889503
  have hstable : (prefixWord ++ tailWord_4889503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4889503).length < 2 ^ (prefixWord ++ tailWord_4889503).sum := by decide
  have hdescent : baseEnd_4889503 < baseStart_4889503 := by decide
  rcases family_descends (prefixWord ++ tailWord_4889503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4889546 : List Nat := [3, 1, 2, 1, 2, 1, 1, 3, 2, 3, 4]
def baseStart_4889546 : Nat := 118140960795 + 4889546 * 2 ^ 59
def prefixEnd_4889546 : Nat := 4983230072969 + 3 ^ 40 * 4889546 * 2
def baseEnd_4889546 : Nat := 2510687280268831862488393

theorem tailTrace_4889546 : CollatzResearch.WordTrace tailWord_4889546 prefixEnd_4889546 2510687280268831862488393 := by
  unfold tailWord_4889546
  simp only [CollatzResearch.WordTrace]
  refine ⟨44584098386004346204688123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118890929029344923212501661 44584098386004346204688123)
  ·
    refine ⟨66876147579006519307032185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44584098386004346204688123 66876147579006519307032185)
    ·
      refine ⟨50157110684254889480274139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66876147579006519307032185 50157110684254889480274139)
      ·
        refine ⟨75235666026382334220411209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50157110684254889480274139 75235666026382334220411209)
        ·
          refine ⟨56426749519786750665308407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75235666026382334220411209 56426749519786750665308407)
          ·
            refine ⟨84640124279680125997962611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56426749519786750665308407 84640124279680125997962611)
            ·
              refine ⟨126960186419520188996943917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84640124279680125997962611 126960186419520188996943917)
              ·
                refine ⟨47610069907320070873853969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 126960186419520188996943917 47610069907320070873853969)
                ·
                  refine ⟨35707552430490053155390477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47610069907320070873853969 35707552430490053155390477)
                  ·
                    refine ⟨13390332161433769933271429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35707552430490053155390477 13390332161433769933271429)
                    ·
                      refine ⟨2510687280268831862488393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13390332161433769933271429 2510687280268831862488393)
                      ·
                        rfl

theorem cell23_4889546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 3, 2, 3, 4].length) (baseStart_4889546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4889546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4889546 prefixEnd_4889546 := by exact prefixLift 4889546
  have htrace : WordTrace (prefixWord ++ tailWord_4889546) baseStart_4889546 baseEnd_4889546 := by
    simpa [prefixWord, tailWord_4889546, baseEnd_4889546] using wordTrace_append hprefix tailTrace_4889546
  have hstable : (prefixWord ++ tailWord_4889546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4889546).length < 2 ^ (prefixWord ++ tailWord_4889546).sum := by decide
  have hdescent : baseEnd_4889546 < baseStart_4889546 := by decide
  rcases family_descends (prefixWord ++ tailWord_4889546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4889557 : List Nat := [1, 3, 2, 3, 3, 1, 1, 3, 2, 1, 3]
def baseStart_4889557 : Nat := 118140960795 + 4889557 * 2 ^ 59
def prefixEnd_4889557 : Nat := 4983230072969 + 3 ^ 40 * 4889557 * 2
def baseEnd_4889557 : Nat := 2510692928556031319450843

theorem tailTrace_4889557 : CollatzResearch.WordTrace tailWord_4889557 prefixEnd_4889557 2510692928556031319450843 := by
  unfold tailWord_4889557
  simp only [CollatzResearch.WordTrace]
  refine ⟨178336794746977533697402925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118891196497985022464935283 178336794746977533697402925)
  ·
    refine ⟨66876298030116575136526097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 178336794746977533697402925 66876298030116575136526097)
    ·
      refine ⟨50157223522587431352394573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66876298030116575136526097 50157223522587431352394573)
      ·
        refine ⟨18808958820970286757147965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50157223522587431352394573 18808958820970286757147965)
        ·
          refine ⟨7053359557863857533930487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18808958820970286757147965 7053359557863857533930487)
          ·
            refine ⟨10580039336795786300895731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7053359557863857533930487 10580039336795786300895731)
            ·
              refine ⟨15870059005193679451343597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10580039336795786300895731 15870059005193679451343597)
              ·
                refine ⟨5951272126947629794253849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15870059005193679451343597 5951272126947629794253849)
                ·
                  refine ⟨4463454095210722345690387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5951272126947629794253849 4463454095210722345690387)
                  ·
                    refine ⟨6695181142816083518535581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4463454095210722345690387 6695181142816083518535581)
                    ·
                      refine ⟨2510692928556031319450843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6695181142816083518535581 2510692928556031319450843)
                      ·
                        rfl

theorem cell23_4889557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 3, 2, 1, 3].length) (baseStart_4889557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4889557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4889557 prefixEnd_4889557 := by exact prefixLift 4889557
  have htrace : WordTrace (prefixWord ++ tailWord_4889557) baseStart_4889557 baseEnd_4889557 := by
    simpa [prefixWord, tailWord_4889557, baseEnd_4889557] using wordTrace_append hprefix tailTrace_4889557
  have hstable : (prefixWord ++ tailWord_4889557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4889557).length < 2 ^ (prefixWord ++ tailWord_4889557).sum := by decide
  have hdescent : baseEnd_4889557 < baseStart_4889557 := by decide
  rcases family_descends (prefixWord ++ tailWord_4889557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4889633 : List Nat := [1, 2, 3, 2, 3, 2, 1, 1, 1, 7]
def baseStart_4889633 : Nat := 118140960795 + 4889633 * 2 ^ 59
def prefixEnd_4889633 : Nat := 4983230072969 + 3 ^ 40 * 4889633 * 2
def baseEnd_4889633 : Nat := 836910651028591007366831

theorem tailTrace_4889633 : CollatzResearch.WordTrace tailWord_4889633 prefixEnd_4889633 836910651028591007366831 := by
  unfold tailWord_4889633
  simp only [CollatzResearch.WordTrace]
  refine ⟨178339566694702198677169553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118893044463134799118113035 178339566694702198677169553)
  ·
    refine ⟨133754675021026649007877165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178339566694702198677169553 133754675021026649007877165)
    ·
      refine ⟨50158003132884993377953937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133754675021026649007877165 50158003132884993377953937)
      ·
        refine ⟨37618502349663745033465453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50158003132884993377953937 37618502349663745033465453)
        ·
          refine ⟨14106938381123904387549545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37618502349663745033465453 14106938381123904387549545)
          ·
            refine ⟨10580203785842928290662159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14106938381123904387549545 10580203785842928290662159)
            ·
              refine ⟨15870305678764392435993239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10580203785842928290662159 15870305678764392435993239)
              ·
                refine ⟨23805458518146588653989859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15870305678764392435993239 23805458518146588653989859)
                ·
                  refine ⟨35708187777219882980984789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23805458518146588653989859 35708187777219882980984789)
                  ·
                    refine ⟨836910651028591007366831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35708187777219882980984789 836910651028591007366831)
                    ·
                      rfl

theorem cell23_4889633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 1, 1, 7].length) (baseStart_4889633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4889633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4889633 prefixEnd_4889633 := by exact prefixLift 4889633
  have htrace : WordTrace (prefixWord ++ tailWord_4889633) baseStart_4889633 baseEnd_4889633 := by
    simpa [prefixWord, tailWord_4889633, baseEnd_4889633] using wordTrace_append hprefix tailTrace_4889633
  have hstable : (prefixWord ++ tailWord_4889633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4889633).length < 2 ^ (prefixWord ++ tailWord_4889633).sum := by decide
  have hdescent : baseEnd_4889633 < baseStart_4889633 := by decide
  rcases family_descends (prefixWord ++ tailWord_4889633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4889653 : List Nat := [1, 3, 3, 1, 1, 1, 1, 3, 4, 1, 4]
def baseStart_4889653 : Nat := 118140960795 + 4889653 * 2 ^ 59
def prefixEnd_4889653 : Nat := 4983230072969 + 3 ^ 40 * 4889653 * 2
def baseEnd_4889653 : Nat := 2510742222698862943850401

theorem tailTrace_4889653 : CollatzResearch.WordTrace tailWord_4889653 prefixEnd_4889653 2510742222698862943850401 := by
  unfold tailWord_4889653
  simp only [CollatzResearch.WordTrace]
  refine ⟨178340296154629742092897613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118893530769753161395265075 178340296154629742092897613)
  ·
    refine ⟨66877611057986153284836605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 178340296154629742092897613 66877611057986153284836605)
    ·
      refine ⟨25079104146744807481813727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66877611057986153284836605 25079104146744807481813727)
      ·
        refine ⟨37618656220117211222720591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25079104146744807481813727 37618656220117211222720591)
        ·
          refine ⟨56427984330175816834080887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37618656220117211222720591 56427984330175816834080887)
          ·
            refine ⟨84641976495263725251121331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56427984330175816834080887 84641976495263725251121331)
            ·
              refine ⟨126962964742895587876681997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84641976495263725251121331 126962964742895587876681997)
              ·
                refine ⟨47611111778585845453755749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 126962964742895587876681997 47611111778585845453755749)
                ·
                  refine ⟨8927083458484846022579203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47611111778585845453755749 8927083458484846022579203)
                  ·
                    refine ⟨13390625187727269033868805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8927083458484846022579203 13390625187727269033868805)
                    ·
                      refine ⟨2510742222698862943850401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13390625187727269033868805 2510742222698862943850401)
                      ·
                        rfl

theorem cell23_4889653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 3, 4, 1, 4].length) (baseStart_4889653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4889653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4889653 prefixEnd_4889653 := by exact prefixLift 4889653
  have htrace : WordTrace (prefixWord ++ tailWord_4889653) baseStart_4889653 baseEnd_4889653 := by
    simpa [prefixWord, tailWord_4889653, baseEnd_4889653] using wordTrace_append hprefix tailTrace_4889653
  have hstable : (prefixWord ++ tailWord_4889653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4889653).length < 2 ^ (prefixWord ++ tailWord_4889653).sum := by decide
  have hdescent : baseEnd_4889653 < baseStart_4889653 := by decide
  rcases family_descends (prefixWord ++ tailWord_4889653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4889673 : List Nat := [1, 2, 1, 1, 2, 2, 2, 1, 6, 2, 3]
def baseStart_4889673 : Nat := 118140960795 + 4889673 * 2 ^ 59
def prefixEnd_4889673 : Nat := 4983230072969 + 3 ^ 40 * 4889673 * 2
def baseEnd_4889673 : Nat := 2510752492311952865600309

theorem tailTrace_4889673 : CollatzResearch.WordTrace tailWord_4889673 prefixEnd_4889673 2510752492311952865600309 := by
  unfold tailWord_4889673
  simp only [CollatzResearch.WordTrace]
  refine ⟨178341025614557285508625673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118894017076371523672417115 178341025614557285508625673)
  ·
    refine ⟨133755769210917964131469255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178341025614557285508625673 133755769210917964131469255)
    ·
      refine ⟨200633653816376946197203883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133755769210917964131469255 200633653816376946197203883)
      ·
        refine ⟨300950480724565419295805825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200633653816376946197203883 300950480724565419295805825)
        ·
          refine ⟨225712860543424064471854369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 300950480724565419295805825 225712860543424064471854369)
          ·
            refine ⟨169284645407568048353890777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 225712860543424064471854369 169284645407568048353890777)
            ·
              refine ⟨126963484055676036265418083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 169284645407568048353890777 126963484055676036265418083)
              ·
                refine ⟨190445226083514054398127125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126963484055676036265418083 190445226083514054398127125)
                ·
                  refine ⟨8927119972664721299912209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 190445226083514054398127125 8927119972664721299912209)
                  ·
                    refine ⟨6695339979498540974934157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8927119972664721299912209 6695339979498540974934157)
                    ·
                      refine ⟨2510752492311952865600309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6695339979498540974934157 2510752492311952865600309)
                      ·
                        rfl

theorem cell23_4889673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 6, 2, 3].length) (baseStart_4889673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4889673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4889673 prefixEnd_4889673 := by exact prefixLift 4889673
  have htrace : WordTrace (prefixWord ++ tailWord_4889673) baseStart_4889673 baseEnd_4889673 := by
    simpa [prefixWord, tailWord_4889673, baseEnd_4889673] using wordTrace_append hprefix tailTrace_4889673
  have hstable : (prefixWord ++ tailWord_4889673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4889673).length < 2 ^ (prefixWord ++ tailWord_4889673).sum := by decide
  have hdescent : baseEnd_4889673 < baseStart_4889673 := by decide
  rcases family_descends (prefixWord ++ tailWord_4889673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4889697 : List Nat := [1, 2, 3, 1, 1, 2, 5, 3, 1, 4]
def baseStart_4889697 : Nat := 118140960795 + 4889697 * 2 ^ 59
def prefixEnd_4889697 : Nat := 4983230072969 + 3 ^ 40 * 4889697 * 2
def baseEnd_4889697 : Nat := 836921605282553590566733

theorem tailTrace_4889697 : CollatzResearch.WordTrace tailWord_4889697 prefixEnd_4889697 836921605282553590566733 := by
  unfold tailWord_4889697
  simp only [CollatzResearch.WordTrace]
  refine ⟨178341900966470337607499345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118894600644313558404999563 178341900966470337607499345)
  ·
    refine ⟨133756425724852753205624509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178341900966470337607499345 133756425724852753205624509)
    ·
      refine ⟨50158659646819782452109191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133756425724852753205624509 50158659646819782452109191)
      ·
        refine ⟨75237989470229673678163787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50158659646819782452109191 75237989470229673678163787)
        ·
          refine ⟨112856984205344510517245681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75237989470229673678163787 112856984205344510517245681)
          ·
            refine ⟨84642738154008382887934261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112856984205344510517245681 84642738154008382887934261)
            ·
              refine ⟨7935256701938285895743837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 84642738154008382887934261 7935256701938285895743837)
              ·
                refine ⟨2975721263226857210903939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7935256701938285895743837 2975721263226857210903939)
                ·
                  refine ⟨4463581894840285816355909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2975721263226857210903939 4463581894840285816355909)
                  ·
                    refine ⟨836921605282553590566733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4463581894840285816355909 836921605282553590566733)
                    ·
                      rfl

theorem cell23_4889697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 5, 3, 1, 4].length) (baseStart_4889697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4889697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4889697 prefixEnd_4889697 := by exact prefixLift 4889697
  have htrace : WordTrace (prefixWord ++ tailWord_4889697) baseStart_4889697 baseEnd_4889697 := by
    simpa [prefixWord, tailWord_4889697, baseEnd_4889697] using wordTrace_append hprefix tailTrace_4889697
  have hstable : (prefixWord ++ tailWord_4889697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4889697).length < 2 ^ (prefixWord ++ tailWord_4889697).sum := by decide
  have hdescent : baseEnd_4889697 < baseStart_4889697 := by decide
  rcases family_descends (prefixWord ++ tailWord_4889697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4889714 : List Nat := [3, 2, 1, 2, 2, 1, 5, 2, 1, 4]
def baseStart_4889714 : Nat := 118140960795 + 4889714 * 2 ^ 59
def prefixEnd_4889714 : Nat := 4983230072969 + 3 ^ 40 * 4889714 * 2
def baseEnd_4889714 : Nat := 836924515006262401729207

theorem tailTrace_4889714 : CollatzResearch.WordTrace tailWord_4889714 prefixEnd_4889714 836924515006262401729207 := by
  unfold tailWord_4889714
  simp only [CollatzResearch.WordTrace]
  refine ⟨44585630251852187377717049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118895014004939166340578797 44585630251852187377717049)
  ·
    refine ⟨33439222688889140533287787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44585630251852187377717049 33439222688889140533287787)
    ·
      refine ⟨50158834033333710799931681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33439222688889140533287787 50158834033333710799931681)
      ·
        refine ⟨37619125525000283099948761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50158834033333710799931681 37619125525000283099948761)
        ·
          refine ⟨28214344143750212324961571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37619125525000283099948761 28214344143750212324961571)
          ·
            refine ⟨42321516215625318487442357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28214344143750212324961571 42321516215625318487442357)
            ·
              refine ⟨3967642145214873608197721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42321516215625318487442357 3967642145214873608197721)
              ·
                refine ⟨2975731608911155206148291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3967642145214873608197721 2975731608911155206148291)
                ·
                  refine ⟨4463597413366732809222437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2975731608911155206148291 4463597413366732809222437)
                  ·
                    refine ⟨836924515006262401729207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4463597413366732809222437 836924515006262401729207)
                    ·
                      rfl

theorem cell23_4889714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 5, 2, 1, 4].length) (baseStart_4889714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4889714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4889714 prefixEnd_4889714 := by exact prefixLift 4889714
  have htrace : WordTrace (prefixWord ++ tailWord_4889714) baseStart_4889714 baseEnd_4889714 := by
    simpa [prefixWord, tailWord_4889714, baseEnd_4889714] using wordTrace_append hprefix tailTrace_4889714
  have hstable : (prefixWord ++ tailWord_4889714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4889714).length < 2 ^ (prefixWord ++ tailWord_4889714).sum := by decide
  have hdescent : baseEnd_4889714 < baseStart_4889714 := by decide
  rcases family_descends (prefixWord ++ tailWord_4889714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4889757 : List Nat := [1, 4, 2, 1, 1, 2, 5, 1, 1, 5]
def baseStart_4889757 : Nat := 118140960795 + 4889757 * 2 ^ 59
def prefixEnd_4889757 : Nat := 4983230072969 + 3 ^ 40 * 4889757 * 2
def baseEnd_4889757 : Nat := 836931874895643512316641

theorem tailTrace_4889757 : CollatzResearch.WordTrace tailWord_4889757 prefixEnd_4889757 836931874895643512316641 := by
  unfold tailWord_4889757
  simp only [CollatzResearch.WordTrace]
  refine ⟨178344089346252967854683525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118896059564168645236455683 178344089346252967854683525)
  ·
    refine ⟨33439516752422431472753161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 178344089346252967854683525 33439516752422431472753161)
    ·
      refine ⟨25079637564316823604564871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33439516752422431472753161 25079637564316823604564871)
      ·
        refine ⟨37619456346475235406847307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25079637564316823604564871 37619456346475235406847307)
        ·
          refine ⟨56429184519712853110270961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37619456346475235406847307 56429184519712853110270961)
          ·
            refine ⟨42321888389784639832703221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56429184519712853110270961 42321888389784639832703221)
            ·
              refine ⟨3967677036542309984315927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42321888389784639832703221 3967677036542309984315927)
              ·
                refine ⟨5951515554813464976473891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3967677036542309984315927 5951515554813464976473891)
                ·
                  refine ⟨8927273332220197464710837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5951515554813464976473891 8927273332220197464710837)
                  ·
                    refine ⟨836931874895643512316641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8927273332220197464710837 836931874895643512316641)
                    ·
                      rfl

theorem cell23_4889757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 5, 1, 1, 5].length) (baseStart_4889757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4889757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4889757 prefixEnd_4889757 := by exact prefixLift 4889757
  have htrace : WordTrace (prefixWord ++ tailWord_4889757) baseStart_4889757 baseEnd_4889757 := by
    simpa [prefixWord, tailWord_4889757, baseEnd_4889757] using wordTrace_append hprefix tailTrace_4889757
  have hstable : (prefixWord ++ tailWord_4889757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4889757).length < 2 ^ (prefixWord ++ tailWord_4889757).sum := by decide
  have hdescent : baseEnd_4889757 < baseStart_4889757 := by decide
  rcases family_descends (prefixWord ++ tailWord_4889757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4889798 : List Nat := [6, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2]
def baseStart_4889798 : Nat := 118140960795 + 4889798 * 2 ^ 59
def prefixEnd_4889798 : Nat := 4983230072969 + 3 ^ 40 * 4889798 * 2
def baseEnd_4889798 : Nat := 2510816677393764876537235

theorem tailTrace_4889798 : CollatzResearch.WordTrace tailWord_4889798 prefixEnd_4889798 2510816677393764876537235 := by
  unfold tailWord_4889798
  simp only [CollatzResearch.WordTrace]
  refine ⟨5573299523097013495528939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 118897056492736287904617365 5573299523097013495528939)
  ·
    refine ⟨8359949284645520243293409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5573299523097013495528939 8359949284645520243293409)
    ·
      refine ⟨6269961963484140182470057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8359949284645520243293409 6269961963484140182470057)
      ·
        refine ⟨4702471472613105136852543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6269961963484140182470057 4702471472613105136852543)
        ·
          refine ⟨7053707208919657705278815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4702471472613105136852543 7053707208919657705278815)
          ·
            refine ⟨10580560813379486557918223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7053707208919657705278815 10580560813379486557918223)
            ·
              refine ⟨15870841220069229836877335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10580560813379486557918223 15870841220069229836877335)
              ·
                refine ⟨23806261830103844755316003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15870841220069229836877335 23806261830103844755316003)
                ·
                  refine ⟨35709392745155767132974005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23806261830103844755316003 35709392745155767132974005)
                  ·
                    refine ⟨3347755569858353168716313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35709392745155767132974005 3347755569858353168716313)
                    ·
                      refine ⟨2510816677393764876537235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3347755569858353168716313 2510816677393764876537235)
                      ·
                        rfl

theorem cell23_4889798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_4889798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4889798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4889798 prefixEnd_4889798 := by exact prefixLift 4889798
  have htrace : WordTrace (prefixWord ++ tailWord_4889798) baseStart_4889798 baseEnd_4889798 := by
    simpa [prefixWord, tailWord_4889798, baseEnd_4889798] using wordTrace_append hprefix tailTrace_4889798
  have hstable : (prefixWord ++ tailWord_4889798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4889798).length < 2 ^ (prefixWord ++ tailWord_4889798).sum := by decide
  have hdescent : baseEnd_4889798 < baseStart_4889798 := by decide
  rcases family_descends (prefixWord ++ tailWord_4889798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4889805 : List Nat := [1, 6, 2, 2, 1, 1, 2, 3, 1, 1, 3]
def baseStart_4889805 : Nat := 118140960795 + 4889805 * 2 ^ 59
def prefixEnd_4889805 : Nat := 4983230072969 + 3 ^ 40 * 4889805 * 2
def baseEnd_4889805 : Nat := 2510820271758346349149703

theorem tailTrace_4889805 : CollatzResearch.WordTrace tailWord_4889805 prefixEnd_4889805 2510820271758346349149703 := by
  unfold tailWord_4889805
  simp only [CollatzResearch.WordTrace]
  refine ⟨178345840050079072052430869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118897226700052714701620579 178345840050079072052430869)
  ·
    refine ⟨8359961252347456502457697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 178345840050079072052430869 8359961252347456502457697)
    ·
      refine ⟨6269970939260592376843273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8359961252347456502457697 6269970939260592376843273)
      ·
        refine ⟨4702478204445444282632455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6269970939260592376843273 4702478204445444282632455)
        ·
          refine ⟨7053717306668166423948683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4702478204445444282632455 7053717306668166423948683)
          ·
            refine ⟨10580575960002249635923025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7053717306668166423948683 10580575960002249635923025)
            ·
              refine ⟨7935431970001687226942269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10580575960002249635923025 7935431970001687226942269)
              ·
                refine ⟨2975786988750632710103351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7935431970001687226942269 2975786988750632710103351)
                ·
                  refine ⟨4463680483125949065155027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2975786988750632710103351 4463680483125949065155027)
                  ·
                    refine ⟨6695520724688923597732541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4463680483125949065155027 6695520724688923597732541)
                    ·
                      refine ⟨2510820271758346349149703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6695520724688923597732541 2510820271758346349149703)
                      ·
                        rfl

theorem cell23_4889805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_4889805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4889805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4889805 prefixEnd_4889805 := by exact prefixLift 4889805
  have htrace : WordTrace (prefixWord ++ tailWord_4889805) baseStart_4889805 baseEnd_4889805 := by
    simpa [prefixWord, tailWord_4889805, baseEnd_4889805] using wordTrace_append hprefix tailTrace_4889805
  have hstable : (prefixWord ++ tailWord_4889805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4889805).length < 2 ^ (prefixWord ++ tailWord_4889805).sum := by decide
  have hdescent : baseEnd_4889805 < baseStart_4889805 := by decide
  rcases family_descends (prefixWord ++ tailWord_4889805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4889821 : List Nat := [1, 4, 3, 2, 2, 2, 1, 2, 2, 4]
def baseStart_4889821 : Nat := 118140960795 + 4889821 * 2 ^ 59
def prefixEnd_4889821 : Nat := 4983230072969 + 3 ^ 40 * 4889821 * 2
def baseEnd_4889821 : Nat := 836942829149606095516543

theorem tailTrace_4889821 : CollatzResearch.WordTrace tailWord_4889821 prefixEnd_4889821 836942829149606095516543 := by
  unfold tailWord_4889821
  simp only [CollatzResearch.WordTrace]
  refine ⟨178346423618021106785013317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118897615745347404523342211 178346423618021106785013317)
  ·
    refine ⟨33439954428378957522189997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 178346423618021106785013317 33439954428378957522189997)
    ·
      refine ⟨12539982910642109070821249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33439954428378957522189997 12539982910642109070821249)
      ·
        refine ⟨9404987182981581803115937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12539982910642109070821249 9404987182981581803115937)
        ·
          refine ⟨7053740387236186352336953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9404987182981581803115937 7053740387236186352336953)
          ·
            refine ⟨5290305290427139764252715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7053740387236186352336953 5290305290427139764252715)
            ·
              refine ⟨7935457935640709646379073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5290305290427139764252715 7935457935640709646379073)
              ·
                refine ⟨5951593451730532234784305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7935457935640709646379073 5951593451730532234784305)
                ·
                  refine ⟨4463695088797899176088229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5951593451730532234784305 4463695088797899176088229)
                  ·
                    refine ⟨836942829149606095516543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4463695088797899176088229 836942829149606095516543)
                    ·
                      rfl

theorem cell23_4889821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 1, 2, 2, 4].length) (baseStart_4889821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4889821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4889821 prefixEnd_4889821 := by exact prefixLift 4889821
  have htrace : WordTrace (prefixWord ++ tailWord_4889821) baseStart_4889821 baseEnd_4889821 := by
    simpa [prefixWord, tailWord_4889821, baseEnd_4889821] using wordTrace_append hprefix tailTrace_4889821
  have hstable : (prefixWord ++ tailWord_4889821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4889821).length < 2 ^ (prefixWord ++ tailWord_4889821).sum := by decide
  have hdescent : baseEnd_4889821 < baseStart_4889821 := by decide
  rcases family_descends (prefixWord ++ tailWord_4889821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4889870 : List Nat := [4, 1, 1, 2, 1, 3, 1, 1, 1, 3, 5]
def baseStart_4889870 : Nat := 118140960795 + 4889870 * 2 ^ 59
def prefixEnd_4889870 : Nat := 4983230072969 + 3 ^ 40 * 4889870 * 2
def baseEnd_4889870 : Nat := 2510853648000888594836903

theorem tailTrace_4889870 : CollatzResearch.WordTrace tailWord_4889870 prefixEnd_4889870 2510853648000888594836903 := by
  unfold tailWord_4889870
  simp only [CollatzResearch.WordTrace]
  refine ⟨22293526349355448519193383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118898807196562392102364709 22293526349355448519193383)
  ·
    refine ⟨33440289524033172778790075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22293526349355448519193383 33440289524033172778790075)
    ·
      refine ⟨50160434286049759168185113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33440289524033172778790075 50160434286049759168185113)
      ·
        refine ⟨37620325714537319376138835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50160434286049759168185113 37620325714537319376138835)
        ·
          refine ⟨56430488571805979064208253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37620325714537319376138835 56430488571805979064208253)
          ·
            refine ⟨21161433214427242149078095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56430488571805979064208253 21161433214427242149078095)
            ·
              refine ⟨31742149821640863223617143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21161433214427242149078095 31742149821640863223617143)
              ·
                refine ⟨47613224732461294835425715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31742149821640863223617143 47613224732461294835425715)
                ·
                  refine ⟨71419837098691942253138573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47613224732461294835425715 71419837098691942253138573)
                  ·
                    refine ⟨26782438912009478344926965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 71419837098691942253138573 26782438912009478344926965)
                    ·
                      refine ⟨2510853648000888594836903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26782438912009478344926965 2510853648000888594836903)
                      ·
                        rfl

theorem cell23_4889870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 1, 1, 3, 5].length) (baseStart_4889870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4889870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4889870 prefixEnd_4889870 := by exact prefixLift 4889870
  have htrace : WordTrace (prefixWord ++ tailWord_4889870) baseStart_4889870 baseEnd_4889870 := by
    simpa [prefixWord, tailWord_4889870, baseEnd_4889870] using wordTrace_append hprefix tailTrace_4889870
  have hstable : (prefixWord ++ tailWord_4889870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4889870).length < 2 ^ (prefixWord ++ tailWord_4889870).sum := by decide
  have hdescent : baseEnd_4889870 < baseStart_4889870 := by decide
  rcases family_descends (prefixWord ++ tailWord_4889870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4889883 : List Nat := [1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 9]
def baseStart_4889883 : Nat := 118140960795 + 4889883 * 2 ^ 59
def prefixEnd_4889883 : Nat := 4983230072969 + 3 ^ 40 * 4889883 * 2
def baseEnd_4889883 : Nat := 2510860323249397043974343

theorem tailTrace_4889883 : CollatzResearch.WordTrace tailWord_4889883 prefixEnd_4889883 2510860323249397043974343 := by
  unfold tailWord_4889883
  simp only [CollatzResearch.WordTrace]
  refine ⟨178348684943796491373770303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118899123295864327582513535 178348684943796491373770303)
  ·
    refine ⟨267523027415694737060655455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178348684943796491373770303 267523027415694737060655455)
    ·
      refine ⟨401284541123542105590983183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 267523027415694737060655455 401284541123542105590983183)
      ·
        refine ⟨601926811685313158386474775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 401284541123542105590983183 601926811685313158386474775)
        ·
          refine ⟨902890217527969737579712163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 601926811685313158386474775 902890217527969737579712163)
          ·
            refine ⟨1354335326291954606369568245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 902890217527969737579712163 1354335326291954606369568245)
            ·
              refine ⟨126968936839870744347147023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1354335326291954606369568245 126968936839870744347147023)
              ·
                refine ⟨190453405259806116520720535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126968936839870744347147023 190453405259806116520720535)
                ·
                  refine ⟨285680107889709174781080803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 190453405259806116520720535 285680107889709174781080803)
                  ·
                    refine ⟨428520161834563762171621205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 285680107889709174781080803 428520161834563762171621205)
                    ·
                      refine ⟨2510860323249397043974343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 428520161834563762171621205 2510860323249397043974343)
                      ·
                        rfl

theorem cell23_4889883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 9].length) (baseStart_4889883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4889883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4889883 prefixEnd_4889883 := by exact prefixLift 4889883
  have htrace : WordTrace (prefixWord ++ tailWord_4889883) baseStart_4889883 baseEnd_4889883 := by
    simpa [prefixWord, tailWord_4889883, baseEnd_4889883] using wordTrace_append hprefix tailTrace_4889883
  have hstable : (prefixWord ++ tailWord_4889883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4889883).length < 2 ^ (prefixWord ++ tailWord_4889883).sum := by decide
  have hdescent : baseEnd_4889883 < baseStart_4889883 := by decide
  rcases family_descends (prefixWord ++ tailWord_4889883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4889884 : List Nat := [2, 2, 3, 1, 1, 1, 4, 1, 4, 2, 2]
def baseStart_4889884 : Nat := 118140960795 + 4889884 * 2 ^ 59
def prefixEnd_4889884 : Nat := 4983230072969 + 3 ^ 40 * 4889884 * 2
def baseEnd_4889884 : Nat := 2510860836730051540061839

theorem tailTrace_4889884 : CollatzResearch.WordTrace tailWord_4889884 prefixEnd_4889884 2510860836730051540061839 := by
  unfold tailWord_4889884
  simp only [CollatzResearch.WordTrace]
  refine ⟨89174360708396434272278353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118899147611195245696371137 89174360708396434272278353)
  ·
    refine ⟨66880770531297325704208765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89174360708396434272278353 66880770531297325704208765)
    ·
      refine ⟨25080288949236497139078287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66880770531297325704208765 25080288949236497139078287)
      ·
        refine ⟨37620433423854745708617431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25080288949236497139078287 37620433423854745708617431)
        ·
          refine ⟨56430650135782118562926147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37620433423854745708617431 56430650135782118562926147)
          ·
            refine ⟨84645975203673177844389221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56430650135782118562926147 84645975203673177844389221)
            ·
              refine ⟨15871120350688720845822979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 84645975203673177844389221 15871120350688720845822979)
              ·
                refine ⟨23806680526033081268734469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15871120350688720845822979 23806680526033081268734469)
                ·
                  refine ⟨4463752598631202737887713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23806680526033081268734469 4463752598631202737887713)
                  ·
                    refine ⟨3347814448973402053415785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4463752598631202737887713 3347814448973402053415785)
                    ·
                      refine ⟨2510860836730051540061839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3347814448973402053415785 2510860836730051540061839)
                      ·
                        rfl

theorem cell23_4889884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 1, 4, 2, 2].length) (baseStart_4889884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4889884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4889884 prefixEnd_4889884 := by exact prefixLift 4889884
  have htrace : WordTrace (prefixWord ++ tailWord_4889884) baseStart_4889884 baseEnd_4889884 := by
    simpa [prefixWord, tailWord_4889884, baseEnd_4889884] using wordTrace_append hprefix tailTrace_4889884
  have hstable : (prefixWord ++ tailWord_4889884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4889884).length < 2 ^ (prefixWord ++ tailWord_4889884).sum := by decide
  have hdescent : baseEnd_4889884 < baseStart_4889884 := by decide
  rcases family_descends (prefixWord ++ tailWord_4889884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4889900 : List Nat := [2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 3]
def baseStart_4889900 : Nat := 118140960795 + 4889900 * 2 ^ 59
def prefixEnd_4889900 : Nat := 4983230072969 + 3 ^ 40 * 4889900 * 2
def baseEnd_4889900 : Nat := 2510869052420523477461765

theorem tailTrace_4889900 : CollatzResearch.WordTrace tailWord_4889900 prefixEnd_4889900 2510869052420523477461765 := by
  unfold tailWord_4889900
  simp only [CollatzResearch.WordTrace]
  refine ⟨89174652492367451638569577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118899536656489935518092769 89174652492367451638569577)
  ·
    refine ⟨66880989369275588728927183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89174652492367451638569577 66880989369275588728927183)
    ·
      refine ⟨100321484053913383093390775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66880989369275588728927183 100321484053913383093390775)
      ·
        refine ⟨150482226080870074640086163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100321484053913383093390775 150482226080870074640086163)
        ·
          refine ⟨225723339121305111960129245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150482226080870074640086163 225723339121305111960129245)
          ·
            refine ⟨84646252170489416985048467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 225723339121305111960129245 84646252170489416985048467)
            ·
              refine ⟨126969378255734125477572701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84646252170489416985048467 126969378255734125477572701)
              ·
                refine ⟨47613516845900297054089763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 126969378255734125477572701 47613516845900297054089763)
                ·
                  refine ⟨71420275268850445581134645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47613516845900297054089763 71420275268850445581134645)
                  ·
                    refine ⟨6695650806454729273231373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 71420275268850445581134645 6695650806454729273231373)
                    ·
                      refine ⟨2510869052420523477461765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6695650806454729273231373 2510869052420523477461765)
                      ·
                        rfl

theorem cell23_4889900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 3].length) (baseStart_4889900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4889900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4889900 prefixEnd_4889900 := by exact prefixLift 4889900
  have htrace : WordTrace (prefixWord ++ tailWord_4889900) baseStart_4889900 baseEnd_4889900 := by
    simpa [prefixWord, tailWord_4889900, baseEnd_4889900] using wordTrace_append hprefix tailTrace_4889900
  have hstable : (prefixWord ++ tailWord_4889900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4889900).length < 2 ^ (prefixWord ++ tailWord_4889900).sum := by decide
  have hdescent : baseEnd_4889900 < baseStart_4889900 := by decide
  rcases family_descends (prefixWord ++ tailWord_4889900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4889941 : List Nat := [1, 3, 2, 2, 3, 3, 2, 2, 5]
def baseStart_4889941 : Nat := 118140960795 + 4889941 * 2 ^ 59
def prefixEnd_4889941 : Nat := 4983230072969 + 3 ^ 40 * 4889941 * 2
def baseEnd_4889941 : Nat := 278987789458595313005453

theorem tailTrace_4889941 : CollatzResearch.WordTrace tailWord_4889941 prefixEnd_4889941 278987789458595313005453 := by
  unfold tailWord_4889941
  simp only [CollatzResearch.WordTrace]
  refine ⟨178350800377586367279381677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118900533585057578186254451 178350800377586367279381677)
  ·
    refine ⟨66881550141594887729768129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 178350800377586367279381677 66881550141594887729768129)
    ·
      refine ⟨50161162606196165797326097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66881550141594887729768129 50161162606196165797326097)
      ·
        refine ⟨37620871954647124347994573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50161162606196165797326097 37620871954647124347994573)
        ·
          refine ⟨14107826982992671630497965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37620871954647124347994573 14107826982992671630497965)
          ·
            refine ⟨5290435118622251861436737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14107826982992671630497965 5290435118622251861436737)
            ·
              refine ⟨3967826338966688896077553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5290435118622251861436737 3967826338966688896077553)
              ·
                refine ⟨2975869754225016672058165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3967826338966688896077553 2975869754225016672058165)
                ·
                  refine ⟨278987789458595313005453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2975869754225016672058165 278987789458595313005453)
                  ·
                    rfl

theorem cell23_4889941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 2, 2, 5].length) (baseStart_4889941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4889941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4889941 prefixEnd_4889941 := by exact prefixLift 4889941
  have htrace : WordTrace (prefixWord ++ tailWord_4889941) baseStart_4889941 baseEnd_4889941 := by
    simpa [prefixWord, tailWord_4889941, baseEnd_4889941] using wordTrace_append hprefix tailTrace_4889941
  have hstable : (prefixWord ++ tailWord_4889941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4889941).length < 2 ^ (prefixWord ++ tailWord_4889941).sum := by decide
  have hdescent : baseEnd_4889941 < baseStart_4889941 := by decide
  rcases family_descends (prefixWord ++ tailWord_4889941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4889967 : List Nat := [1, 1, 2, 1, 3, 1, 5, 2, 3, 4]
def baseStart_4889967 : Nat := 118140960795 + 4889967 * 2 ^ 59
def prefixEnd_4889967 : Nat := 4983230072969 + 3 ^ 40 * 4889967 * 2
def baseEnd_4889967 : Nat := 836967818541458238441319

theorem tailTrace_4889967 : CollatzResearch.WordTrace tailWord_4889967 prefixEnd_4889967 836967818541458238441319 := by
  unfold tailWord_4889967
  simp only [CollatzResearch.WordTrace]
  refine ⟨178351748675492173719828155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118901165783661449146552103 178351748675492173719828155)
  ·
    refine ⟨267527623013238260579742233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178351748675492173719828155 267527623013238260579742233)
    ·
      refine ⟨200645717259928695434806675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 267527623013238260579742233 200645717259928695434806675)
      ·
        refine ⟨300968575889893043152210013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200645717259928695434806675 300968575889893043152210013)
        ·
          refine ⟨112863215958709891182078755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 300968575889893043152210013 112863215958709891182078755)
          ·
            refine ⟨169294823938064836773118133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112863215958709891182078755 169294823938064836773118133)
            ·
              refine ⟨15871389744193578447479825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 169294823938064836773118133 15871389744193578447479825)
              ·
                refine ⟨11903542308145183835609869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15871389744193578447479825 11903542308145183835609869)
                ·
                  refine ⟨4463828365554443938353701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11903542308145183835609869 4463828365554443938353701)
                  ·
                    refine ⟨836967818541458238441319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4463828365554443938353701 836967818541458238441319)
                    ·
                      rfl

theorem cell23_4889967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 2, 3, 4].length) (baseStart_4889967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4889967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4889967 prefixEnd_4889967 := by exact prefixLift 4889967
  have htrace : WordTrace (prefixWord ++ tailWord_4889967) baseStart_4889967 baseEnd_4889967 := by
    simpa [prefixWord, tailWord_4889967, baseEnd_4889967] using wordTrace_append hprefix tailTrace_4889967
  have hstable : (prefixWord ++ tailWord_4889967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4889967).length < 2 ^ (prefixWord ++ tailWord_4889967).sum := by decide
  have hdescent : baseEnd_4889967 < baseStart_4889967 := by decide
  rcases family_descends (prefixWord ++ tailWord_4889967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4889980 : List Nat := [2, 2, 2, 1, 1, 1, 4, 2, 8]
def baseStart_4889980 : Nat := 118140960795 + 4889980 * 2 ^ 59
def prefixEnd_4889980 : Nat := 4983230072969 + 3 ^ 40 * 4889980 * 2
def baseEnd_4889980 : Nat := 278990014541431462717933

theorem tailTrace_4889980 : CollatzResearch.WordTrace tailWord_4889980 prefixEnd_4889980 278990014541431462717933 := by
  unfold tailWord_4889980
  simp only [CollatzResearch.WordTrace]
  refine ⟨89176111412222538470025697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118901481882963384626700929 89176111412222538470025697)
  ·
    refine ⟨66882083559166903852519273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89176111412222538470025697 66882083559166903852519273)
    ·
      refine ⟨50161562669375177889389455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66882083559166903852519273 50161562669375177889389455)
      ·
        refine ⟨75242344004062766834084183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50161562669375177889389455 75242344004062766834084183)
        ·
          refine ⟨112863516006094150251126275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75242344004062766834084183 112863516006094150251126275)
          ·
            refine ⟨169295274009141225376689413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112863516006094150251126275 169295274009141225376689413)
            ·
              refine ⟨31742863876713979758129265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 169295274009141225376689413 31742863876713979758129265)
              ·
                refine ⟨23807147907535484818596949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31742863876713979758129265 23807147907535484818596949)
                ·
                  refine ⟨278990014541431462717933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23807147907535484818596949 278990014541431462717933)
                  ·
                    rfl

theorem cell23_4889980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 2, 8].length) (baseStart_4889980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4889980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4889980 prefixEnd_4889980 := by exact prefixLift 4889980
  have htrace : WordTrace (prefixWord ++ tailWord_4889980) baseStart_4889980 baseEnd_4889980 := by
    simpa [prefixWord, tailWord_4889980, baseEnd_4889980] using wordTrace_append hprefix tailTrace_4889980
  have hstable : (prefixWord ++ tailWord_4889980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4889980).length < 2 ^ (prefixWord ++ tailWord_4889980).sum := by decide
  have hdescent : baseEnd_4889980 < baseStart_4889980 := by decide
  rcases family_descends (prefixWord ++ tailWord_4889980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4890081 : List Nat := [1, 2, 3, 1, 2, 5, 1, 2, 1, 1, 4]
def baseStart_4890081 : Nat := 118140960795 + 4890081 * 2 ^ 59
def prefixEnd_4890081 : Nat := 4983230072969 + 3 ^ 40 * 4890081 * 2
def baseEnd_4890081 : Nat := 2510961992418987269298433

theorem tailTrace_4890081 : CollatzResearch.WordTrace tailWord_4890081 prefixEnd_4890081 2510961992418987269298433 := by
  unfold tailWord_4890081
  simp only [CollatzResearch.WordTrace]
  refine ⟨178355906597079171189478097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118903937731386114126318731 178355906597079171189478097)
  ·
    refine ⟨133766929947809378392108573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178355906597079171189478097 133766929947809378392108573)
    ·
      refine ⟨50162598730428516897040715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133766929947809378392108573 50162598730428516897040715)
      ·
        refine ⟨75243898095642775345561073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50162598730428516897040715 75243898095642775345561073)
        ·
          refine ⟨56432923571732081509170805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75243898095642775345561073 56432923571732081509170805)
          ·
            refine ⟨5290586584849882641484763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 56432923571732081509170805 5290586584849882641484763)
            ·
              refine ⟨7935879877274823962227145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5290586584849882641484763 7935879877274823962227145)
              ·
                refine ⟨5951909907956117971670359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7935879877274823962227145 5951909907956117971670359)
                ·
                  refine ⟨8927864861934176957505539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5951909907956117971670359 8927864861934176957505539)
                  ·
                    refine ⟨13391797292901265436258309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8927864861934176957505539 13391797292901265436258309)
                    ·
                      refine ⟨2510961992418987269298433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13391797292901265436258309 2510961992418987269298433)
                      ·
                        rfl

theorem cell23_4890081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 1, 2, 1, 1, 4].length) (baseStart_4890081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4890081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4890081 prefixEnd_4890081 := by exact prefixLift 4890081
  have htrace : WordTrace (prefixWord ++ tailWord_4890081) baseStart_4890081 baseEnd_4890081 := by
    simpa [prefixWord, tailWord_4890081, baseEnd_4890081] using wordTrace_append hprefix tailTrace_4890081
  have hstable : (prefixWord ++ tailWord_4890081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4890081).length < 2 ^ (prefixWord ++ tailWord_4890081).sum := by decide
  have hdescent : baseEnd_4890081 < baseStart_4890081 := by decide
  rcases family_descends (prefixWord ++ tailWord_4890081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4890087 : List Nat := [1, 1, 5, 2, 1, 2, 2, 9]
def baseStart_4890087 : Nat := 118140960795 + 4890087 * 2 ^ 59
def prefixEnd_4890087 : Nat := 4983230072969 + 3 ^ 40 * 4890087 * 2
def baseEnd_4890087 : Nat := 92998706418626453549015

theorem tailTrace_4890087 : CollatzResearch.WordTrace tailWord_4890087 prefixEnd_4890087 92998706418626453549015 := by
  unfold tailWord_4890087
  simp only [CollatzResearch.WordTrace]
  refine ⟨178356125435057434214196515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118904083623371622809464343 178356125435057434214196515)
  ·
    refine ⟨267534188152586151321294773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178356125435057434214196515 267534188152586151321294773)
    ·
      refine ⟨25081330139304951686371385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 267534188152586151321294773 25081330139304951686371385)
      ·
        refine ⟨18810997604478713764778539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25081330139304951686371385 18810997604478713764778539)
        ·
          refine ⟨28216496406718070647167809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18810997604478713764778539 28216496406718070647167809)
          ·
            refine ⟨21162372305038552985375857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28216496406718070647167809 21162372305038552985375857)
            ·
              refine ⟨15871779228778914739031893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21162372305038552985375857 15871779228778914739031893)
              ·
                refine ⟨92998706418626453549015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15871779228778914739031893 92998706418626453549015)
                ·
                  rfl

theorem cell23_4890087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 9].length) (baseStart_4890087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4890087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4890087 prefixEnd_4890087 := by exact prefixLift 4890087
  have htrace : WordTrace (prefixWord ++ tailWord_4890087) baseStart_4890087 baseEnd_4890087 := by
    simpa [prefixWord, tailWord_4890087, baseEnd_4890087] using wordTrace_append hprefix tailTrace_4890087
  have hstable : (prefixWord ++ tailWord_4890087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4890087).length < 2 ^ (prefixWord ++ tailWord_4890087).sum := by decide
  have hdescent : baseEnd_4890087 < baseStart_4890087 := by decide
  rcases family_descends (prefixWord ++ tailWord_4890087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4890094 : List Nat := [4, 1, 2, 1, 2, 1, 3, 2, 1, 2, 4]
def baseStart_4890094 : Nat := 118140960795 + 4890094 * 2 ^ 59
def prefixEnd_4890094 : Nat := 4983230072969 + 3 ^ 40 * 4890094 * 2
def baseEnd_4890094 : Nat := 2510968667667495718435873

theorem tailTrace_4890094 : CollatzResearch.WordTrace tailWord_4890094 prefixEnd_4890094 2510968667667495718435873 := by
  unfold tailWord_4890094
  simp only [CollatzResearch.WordTrace]
  refine ⟨22294547593254009301212667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118904253830688049606467557 22294547593254009301212667)
  ·
    refine ⟨33441821389881013951819001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22294547593254009301212667 33441821389881013951819001)
    ·
      refine ⟨25081366042410760463864251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33441821389881013951819001 25081366042410760463864251)
      ·
        refine ⟨37622049063616140695796377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25081366042410760463864251 37622049063616140695796377)
        ·
          refine ⟨28216536797712105521847283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37622049063616140695796377 28216536797712105521847283)
          ·
            refine ⟨42324805196568158282770925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28216536797712105521847283 42324805196568158282770925)
            ·
              refine ⟨15871801948713059356039097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42324805196568158282770925 15871801948713059356039097)
              ·
                refine ⟨11903851461534794517029323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15871801948713059356039097 11903851461534794517029323)
                ·
                  refine ⟨17855777192302191775543985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11903851461534794517029323 17855777192302191775543985)
                  ·
                    refine ⟨13391832894226643831657989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17855777192302191775543985 13391832894226643831657989)
                    ·
                      refine ⟨2510968667667495718435873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13391832894226643831657989 2510968667667495718435873)
                      ·
                        rfl

theorem cell23_4890094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 2, 1, 2, 4].length) (baseStart_4890094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4890094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4890094 prefixEnd_4890094 := by exact prefixLift 4890094
  have htrace : WordTrace (prefixWord ++ tailWord_4890094) baseStart_4890094 baseEnd_4890094 := by
    simpa [prefixWord, tailWord_4890094, baseEnd_4890094] using wordTrace_append hprefix tailTrace_4890094
  have hstable : (prefixWord ++ tailWord_4890094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4890094).length < 2 ^ (prefixWord ++ tailWord_4890094).sum := by decide
  have hdescent : baseEnd_4890094 < baseStart_4890094 := by decide
  rcases family_descends (prefixWord ++ tailWord_4890094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4890098 : List Nat := [3, 2, 1, 4, 1, 2, 3, 1, 1, 1, 4]
def baseStart_4890098 : Nat := 118140960795 + 4890098 * 2 ^ 59
def prefixEnd_4890098 : Nat := 4983230072969 + 3 ^ 40 * 4890098 * 2
def baseEnd_4890098 : Nat := 2510970721590113702785855

theorem tailTrace_4890098 : CollatzResearch.WordTrace tailWord_4890098 prefixEnd_4890098 2510970721590113702785855 := by
  unfold tailWord_4890098
  simp only [CollatzResearch.WordTrace]
  refine ⟨44589131659504395773211737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118904351092011722061897965 44589131659504395773211737)
  ·
    refine ⟨33441848744628296829908803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44589131659504395773211737 33441848744628296829908803)
    ·
      refine ⟨50162773116942445244863205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33441848744628296829908803 50162773116942445244863205)
      ·
        refine ⟨9405519959426708483411851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50162773116942445244863205 9405519959426708483411851)
        ·
          refine ⟨14108279939140062725117777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9405519959426708483411851 14108279939140062725117777)
          ·
            refine ⟨10581209954355047043838333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14108279939140062725117777 10581209954355047043838333)
            ·
              refine ⟨3967953732883142641439375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10581209954355047043838333 3967953732883142641439375)
              ·
                refine ⟨5951930599324713962159063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3967953732883142641439375 5951930599324713962159063)
                ·
                  refine ⟨8927895898987070943238595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5951930599324713962159063 8927895898987070943238595)
                  ·
                    refine ⟨13391843848480606414857893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8927895898987070943238595 13391843848480606414857893)
                    ·
                      refine ⟨2510970721590113702785855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13391843848480606414857893 2510970721590113702785855)
                      ·
                        rfl

theorem cell23_4890098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 3, 1, 1, 1, 4].length) (baseStart_4890098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4890098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4890098 prefixEnd_4890098 := by exact prefixLift 4890098
  have htrace : WordTrace (prefixWord ++ tailWord_4890098) baseStart_4890098 baseEnd_4890098 := by
    simpa [prefixWord, tailWord_4890098, baseEnd_4890098] using wordTrace_append hprefix tailTrace_4890098
  have hstable : (prefixWord ++ tailWord_4890098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4890098).length < 2 ^ (prefixWord ++ tailWord_4890098).sum := by decide
  have hdescent : baseEnd_4890098 < baseStart_4890098 := by decide
  rcases family_descends (prefixWord ++ tailWord_4890098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4890101 : List Nat := [1, 3, 5, 1, 1, 1, 3, 1, 1, 1, 5]
def baseStart_4890101 : Nat := 118140960795 + 4890101 * 2 ^ 59
def prefixEnd_4890101 : Nat := 4983230072969 + 3 ^ 40 * 4890101 * 2
def baseEnd_4890101 : Nat := 2510972262032077191048341

theorem tailTrace_4890101 : CollatzResearch.WordTrace tailWord_4890101 prefixEnd_4890101 2510972262032077191048341 := by
  unfold tailWord_4890101
  simp only [CollatzResearch.WordTrace]
  refine ⟨178356636057006714605206157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118904424038004476403470771 178356636057006714605206157)
  ·
    refine ⟨66883738521377517976952309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 178356636057006714605206157 66883738521377517976952309)
    ·
      refine ⟨6270350486379142310339279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 66883738521377517976952309 6270350486379142310339279)
      ·
        refine ⟨9405525729568713465508919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6270350486379142310339279 9405525729568713465508919)
        ·
          refine ⟨14108288594353070198263379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9405525729568713465508919 14108288594353070198263379)
          ·
            refine ⟨21162432891529605297395069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14108288594353070198263379 21162432891529605297395069)
            ·
              refine ⟨7935912334323601986523151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21162432891529605297395069 7935912334323601986523151)
              ·
                refine ⟨11903868501485402979784727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7935912334323601986523151 11903868501485402979784727)
                ·
                  refine ⟨17855802752228104469677091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11903868501485402979784727 17855802752228104469677091)
                  ·
                    refine ⟨26783704128342156704515637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17855802752228104469677091 26783704128342156704515637)
                    ·
                      refine ⟨2510972262032077191048341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26783704128342156704515637 2510972262032077191048341)
                      ·
                        rfl

theorem cell23_4890101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_4890101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4890101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4890101 prefixEnd_4890101 := by exact prefixLift 4890101
  have htrace : WordTrace (prefixWord ++ tailWord_4890101) baseStart_4890101 baseEnd_4890101 := by
    simpa [prefixWord, tailWord_4890101, baseEnd_4890101] using wordTrace_append hprefix tailTrace_4890101
  have hstable : (prefixWord ++ tailWord_4890101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4890101).length < 2 ^ (prefixWord ++ tailWord_4890101).sum := by decide
  have hdescent : baseEnd_4890101 < baseStart_4890101 := by decide
  rcases family_descends (prefixWord ++ tailWord_4890101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4890131 : List Nat := [1, 1, 1, 2, 1, 6, 2, 3, 2, 1, 3]
def baseStart_4890131 : Nat := 118140960795 + 4890131 * 2 ^ 59
def prefixEnd_4890131 : Nat := 4983230072969 + 3 ^ 40 * 4890131 * 2
def baseEnd_4890131 : Nat := 2510987666451712073673203

theorem tailTrace_4890131 : CollatzResearch.WordTrace tailWord_4890131 prefixEnd_4890131 2510987666451712073673203 := by
  unfold tailWord_4890131
  simp only [CollatzResearch.WordTrace]
  refine ⟨178357730246898029728798247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118905153497932019819198831 178357730246898029728798247)
  ·
    refine ⟨267536595370347044593197371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178357730246898029728798247 267536595370347044593197371)
    ·
      refine ⟨401304893055520566889796057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 267536595370347044593197371 401304893055520566889796057)
      ·
        refine ⟨300978669791640425167347043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 401304893055520566889796057 300978669791640425167347043)
        ·
          refine ⟨451468004687460637751020565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 300978669791640425167347043 451468004687460637751020565)
          ·
            refine ⟨21162562719724717394579089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 451468004687460637751020565 21162562719724717394579089)
            ·
              refine ⟨15871922039793538045934317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21162562719724717394579089 15871922039793538045934317)
              ·
                refine ⟨5951970764922576767225369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15871922039793538045934317 5951970764922576767225369)
                ·
                  refine ⟨4463978073691932575419027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5951970764922576767225369 4463978073691932575419027)
                  ·
                    refine ⟨6695967110537898863128541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4463978073691932575419027 6695967110537898863128541)
                    ·
                      refine ⟨2510987666451712073673203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6695967110537898863128541 2510987666451712073673203)
                      ·
                        rfl

theorem cell23_4890131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 3, 2, 1, 3].length) (baseStart_4890131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4890131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4890131 prefixEnd_4890131 := by exact prefixLift 4890131
  have htrace : WordTrace (prefixWord ++ tailWord_4890131) baseStart_4890131 baseEnd_4890131 := by
    simpa [prefixWord, tailWord_4890131, baseEnd_4890131] using wordTrace_append hprefix tailTrace_4890131
  have hstable : (prefixWord ++ tailWord_4890131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4890131).length < 2 ^ (prefixWord ++ tailWord_4890131).sum := by decide
  have hdescent : baseEnd_4890131 < baseStart_4890131 := by decide
  rcases family_descends (prefixWord ++ tailWord_4890131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4890141 : List Nat := [1, 4, 2, 2, 1, 1, 1, 3, 3, 3, 2]
def baseStart_4890141 : Nat := 118140960795 + 4890141 * 2 ^ 59
def prefixEnd_4890141 : Nat := 4983230072969 + 3 ^ 40 * 4890141 * 2
def baseEnd_4890141 : Nat := 2510992801258257034548157

theorem tailTrace_4890141 : CollatzResearch.WordTrace tailWord_4890141 prefixEnd_4890141 2510992801258257034548157 := by
  unfold tailWord_4890141
  simp only [CollatzResearch.WordTrace]
  refine ⟨178358094976861801436662277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118905396651241200957774851 178358094976861801436662277)
  ·
    refine ⟨33442142808161587769374177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 178358094976861801436662277 33442142808161587769374177)
    ·
      refine ⟨25081607106121190827030633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33442142808161587769374177 25081607106121190827030633)
      ·
        refine ⟨18811205329590893120272975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25081607106121190827030633 18811205329590893120272975)
        ·
          refine ⟨28216807994386339680409463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18811205329590893120272975 28216807994386339680409463)
          ·
            refine ⟨42325211991579509520614195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28216807994386339680409463 42325211991579509520614195)
            ·
              refine ⟨63487817987369264280921293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42325211991579509520614195 63487817987369264280921293)
              ·
                refine ⟨23807931745263474105345485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63487817987369264280921293 23807931745263474105345485)
                ·
                  refine ⟨8927974404473802789504557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23807931745263474105345485 8927974404473802789504557)
                  ·
                    refine ⟨3347990401677676046064209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8927974404473802789504557 3347990401677676046064209)
                    ·
                      refine ⟨2510992801258257034548157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3347990401677676046064209 2510992801258257034548157)
                      ·
                        rfl

theorem cell23_4890141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 3, 3, 3, 2].length) (baseStart_4890141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4890141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4890141 prefixEnd_4890141 := by exact prefixLift 4890141
  have htrace : WordTrace (prefixWord ++ tailWord_4890141) baseStart_4890141 baseEnd_4890141 := by
    simpa [prefixWord, tailWord_4890141, baseEnd_4890141] using wordTrace_append hprefix tailTrace_4890141
  have hstable : (prefixWord ++ tailWord_4890141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4890141).length < 2 ^ (prefixWord ++ tailWord_4890141).sum := by decide
  have hdescent : baseEnd_4890141 < baseStart_4890141 := by decide
  rcases family_descends (prefixWord ++ tailWord_4890141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4890152 : List Nat := [2, 1, 5, 2, 3, 1, 2, 1, 1, 2, 3]
def baseStart_4890152 : Nat := 118140960795 + 4890152 * 2 ^ 59
def prefixEnd_4890152 : Nat := 4983230072969 + 3 ^ 40 * 4890152 * 2
def baseEnd_4890152 : Nat := 2510998449545456491510607

theorem tailTrace_4890152 : CollatzResearch.WordTrace tailWord_4890152 prefixEnd_4890152 2510998449545456491510607 := by
  unfold tailWord_4890152
  simp only [CollatzResearch.WordTrace]
  refine ⟨89179248089910975157656355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118905664119881300210208473 89179248089910975157656355)
  ·
    refine ⟨133768872134866462736484533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89179248089910975157656355 133768872134866462736484533)
    ·
      refine ⟨12540831762643730881545425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 133768872134866462736484533 12540831762643730881545425)
      ·
        refine ⟨9405623821982798161159069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12540831762643730881545425 9405623821982798161159069)
        ·
          refine ⟨3527108933243549310434651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9405623821982798161159069 3527108933243549310434651)
          ·
            refine ⟨5290663399865323965651977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3527108933243549310434651 5290663399865323965651977)
            ·
              refine ⟨3967997549898992974238983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5290663399865323965651977 3967997549898992974238983)
              ·
                refine ⟨5951996324848489461358475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3967997549898992974238983 5951996324848489461358475)
                ·
                  refine ⟨8927994487272734192037713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5951996324848489461358475 8927994487272734192037713)
                  ·
                    refine ⟨6695995865454550644028285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8927994487272734192037713 6695995865454550644028285)
                    ·
                      refine ⟨2510998449545456491510607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6695995865454550644028285 2510998449545456491510607)
                      ·
                        rfl

theorem cell23_4890152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 2, 1, 1, 2, 3].length) (baseStart_4890152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4890152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4890152 prefixEnd_4890152 := by exact prefixLift 4890152
  have htrace : WordTrace (prefixWord ++ tailWord_4890152) baseStart_4890152 baseEnd_4890152 := by
    simpa [prefixWord, tailWord_4890152, baseEnd_4890152] using wordTrace_append hprefix tailTrace_4890152
  have hstable : (prefixWord ++ tailWord_4890152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4890152).length < 2 ^ (prefixWord ++ tailWord_4890152).sum := by decide
  have hdescent : baseEnd_4890152 < baseStart_4890152 := by decide
  rcases family_descends (prefixWord ++ tailWord_4890152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4890182 : List Nat := [6, 1, 1, 1, 4, 1, 1, 1, 1, 3, 3]
def baseStart_4890182 : Nat := 118140960795 + 4890182 * 2 ^ 59
def prefixEnd_4890182 : Nat := 4983230072969 + 3 ^ 40 * 4890182 * 2
def baseEnd_4890182 : Nat := 2511013853965091374135469

theorem tailTrace_4890182 : CollatzResearch.WordTrace tailWord_4890182 prefixEnd_4890182 2511013853965091374135469 := by
  unfold tailWord_4890182
  simp only [CollatzResearch.WordTrace]
  refine ⟨5573737199053539544965775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 118906393579808843625936533 5573737199053539544965775)
  ·
    refine ⟨8360605798580309317448663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5573737199053539544965775 8360605798580309317448663)
    ·
      refine ⟨12540908697870463976172995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8360605798580309317448663 12540908697870463976172995)
      ·
        refine ⟨18811363046805695964259493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12540908697870463976172995 18811363046805695964259493)
        ·
          refine ⟨3527130571276067993298655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18811363046805695964259493 3527130571276067993298655)
          ·
            refine ⟨5290695856914101989947983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3527130571276067993298655 5290695856914101989947983)
            ·
              refine ⟨7936043785371152984921975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5290695856914101989947983 7936043785371152984921975)
              ·
                refine ⟨11904065678056729477382963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7936043785371152984921975 11904065678056729477382963)
                ·
                  refine ⟨17856098517085094216074445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11904065678056729477382963 17856098517085094216074445)
                  ·
                    refine ⟨6696036943906910331027917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17856098517085094216074445 6696036943906910331027917)
                    ·
                      refine ⟨2511013853965091374135469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6696036943906910331027917 2511013853965091374135469)
                      ·
                        rfl

theorem cell23_4890182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 1, 1, 1, 3, 3].length) (baseStart_4890182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4890182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4890182 prefixEnd_4890182 := by exact prefixLift 4890182
  have htrace : WordTrace (prefixWord ++ tailWord_4890182) baseStart_4890182 baseEnd_4890182 := by
    simpa [prefixWord, tailWord_4890182, baseEnd_4890182] using wordTrace_append hprefix tailTrace_4890182
  have hstable : (prefixWord ++ tailWord_4890182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4890182).length < 2 ^ (prefixWord ++ tailWord_4890182).sum := by decide
  have hdescent : baseEnd_4890182 < baseStart_4890182 := by decide
  rcases family_descends (prefixWord ++ tailWord_4890182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4890188 : List Nat := [2, 2, 1, 3, 1, 5, 1, 1, 1, 4, 2]
def baseStart_4890188 : Nat := 118140960795 + 4890188 * 2 ^ 59
def prefixEnd_4890188 : Nat := 4983230072969 + 3 ^ 40 * 4890188 * 2
def baseEnd_4890188 : Nat := 2511016934849018350660441

theorem tailTrace_4890188 : CollatzResearch.WordTrace tailWord_4890188 prefixEnd_4890188 2511016934849018350660441 := by
  unfold tailWord_4890188
  simp only [CollatzResearch.WordTrace]
  refine ⟨89179904603845764231811609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118906539471794352309082145 89179904603845764231811609)
  ·
    refine ⟨66884928452884323173858707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89179904603845764231811609 66884928452884323173858707)
    ·
      refine ⟨100327392679326484760788061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66884928452884323173858707 100327392679326484760788061)
      ·
        refine ⟨37622772254747431785295523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100327392679326484760788061 37622772254747431785295523)
        ·
          refine ⟨56434158382121147677943285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37622772254747431785295523 56434158382121147677943285)
          ·
            refine ⟨5290702348323857594807183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 56434158382121147677943285 5290702348323857594807183)
            ·
              refine ⟨7936053522485786392210775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5290702348323857594807183 7936053522485786392210775)
              ·
                refine ⟨11904080283728679588316163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7936053522485786392210775 11904080283728679588316163)
                ·
                  refine ⟨17856120425593019382474245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11904080283728679588316163 17856120425593019382474245)
                  ·
                    refine ⟨3348022579798691134213921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17856120425593019382474245 3348022579798691134213921)
                    ·
                      refine ⟨2511016934849018350660441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3348022579798691134213921 2511016934849018350660441)
                      ·
                        rfl

theorem cell23_4890188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 1, 1, 1, 4, 2].length) (baseStart_4890188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4890188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4890188 prefixEnd_4890188 := by exact prefixLift 4890188
  have htrace : WordTrace (prefixWord ++ tailWord_4890188) baseStart_4890188 baseEnd_4890188 := by
    simpa [prefixWord, tailWord_4890188, baseEnd_4890188] using wordTrace_append hprefix tailTrace_4890188
  have hstable : (prefixWord ++ tailWord_4890188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4890188).length < 2 ^ (prefixWord ++ tailWord_4890188).sum := by decide
  have hdescent : baseEnd_4890188 < baseStart_4890188 := by decide
  rcases family_descends (prefixWord ++ tailWord_4890188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4890194 : List Nat := [3, 2, 2, 1, 2, 2, 2, 2, 7]
def baseStart_4890194 : Nat := 118140960795 + 4890194 * 2 ^ 59
def prefixEnd_4890194 : Nat := 4983230072969 + 3 ^ 40 * 4890194 * 2
def baseEnd_4890194 : Nat := 279002223970327258576157

theorem tailTrace_4890194 : CollatzResearch.WordTrace tailWord_4890194 prefixEnd_4890194 279002223970327258576157 := by
  unfold tailWord_4890194
  simp only [CollatzResearch.WordTrace]
  refine ⟨44590007011417447872085409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118906685363779860992227757 44590007011417447872085409)
  ·
    refine ⟨33442505258563085904064057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44590007011417447872085409 33442505258563085904064057)
    ·
      refine ⟨25081878943922314428048043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33442505258563085904064057 25081878943922314428048043)
      ·
        refine ⟨37622818415883471642072065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25081878943922314428048043 37622818415883471642072065)
        ·
          refine ⟨28217113811912603731554049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37622818415883471642072065 28217113811912603731554049)
          ·
            refine ⟨21162835358934452798665537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28217113811912603731554049 21162835358934452798665537)
            ·
              refine ⟨15872126519200839598999153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21162835358934452798665537 15872126519200839598999153)
              ·
                refine ⟨11904094889400629699249365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15872126519200839598999153 11904094889400629699249365)
                ·
                  refine ⟨279002223970327258576157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11904094889400629699249365 279002223970327258576157)
                  ·
                    rfl

theorem cell23_4890194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 2, 7].length) (baseStart_4890194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4890194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4890194 prefixEnd_4890194 := by exact prefixLift 4890194
  have htrace : WordTrace (prefixWord ++ tailWord_4890194) baseStart_4890194 baseEnd_4890194 := by
    simpa [prefixWord, tailWord_4890194, baseEnd_4890194] using wordTrace_append hprefix tailTrace_4890194
  have hstable : (prefixWord ++ tailWord_4890194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4890194).length < 2 ^ (prefixWord ++ tailWord_4890194).sum := by decide
  have hdescent : baseEnd_4890194 < baseStart_4890194 := by decide
  rcases family_descends (prefixWord ++ tailWord_4890194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4890211 : List Nat := [1, 1, 1, 5, 1, 3, 3, 3, 5]
def baseStart_4890211 : Nat := 118140960795 + 4890211 * 2 ^ 59
def prefixEnd_4890211 : Nat := 4983230072969 + 3 ^ 40 * 4890211 * 2
def baseEnd_4890211 : Nat := 279003193878230195630315

theorem tailTrace_4890211 : CollatzResearch.WordTrace tailWord_4890211 prefixEnd_4890211 279003193878230195630315 := by
  unfold tailWord_4890211
  simp only [CollatzResearch.WordTrace]
  refine ⟨178360648086608203391710487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118907098724405468927806991 178360648086608203391710487)
  ·
    refine ⟨267540972129912305087565731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178360648086608203391710487 267540972129912305087565731)
    ·
      refine ⟨401311458194868457631348597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 267540972129912305087565731 401311458194868457631348597)
      ·
        refine ⟨37622949205768917902938931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 401311458194868457631348597 37622949205768917902938931)
        ·
          refine ⟨56434423808653376854408397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37622949205768917902938931 56434423808653376854408397)
          ·
            refine ⟨21162908928245016320403149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56434423808653376854408397 21162908928245016320403149)
            ·
              refine ⟨7936090848091881120151181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21162908928245016320403149 7936090848091881120151181)
              ·
                refine ⟨2976034068034455420056693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7936090848091881120151181 2976034068034455420056693)
                ·
                  refine ⟨279003193878230195630315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2976034068034455420056693 279003193878230195630315)
                  ·
                    rfl

theorem cell23_4890211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 3, 3, 5].length) (baseStart_4890211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4890211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4890211 prefixEnd_4890211 := by exact prefixLift 4890211
  have htrace : WordTrace (prefixWord ++ tailWord_4890211) baseStart_4890211 baseEnd_4890211 := by
    simpa [prefixWord, tailWord_4890211, baseEnd_4890211] using wordTrace_append hprefix tailTrace_4890211
  have hstable : (prefixWord ++ tailWord_4890211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4890211).length < 2 ^ (prefixWord ++ tailWord_4890211).sum := by decide
  have hdescent : baseEnd_4890211 < baseStart_4890211 := by decide
  rcases family_descends (prefixWord ++ tailWord_4890211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4890224 : List Nat := [2, 1, 1, 1, 6, 1, 1, 1, 4, 5]
def baseStart_4890224 : Nat := 118140960795 + 4890224 * 2 ^ 59
def prefixEnd_4890224 : Nat := 4983230072969 + 3 ^ 40 * 4890224 * 2
def baseEnd_4890224 : Nat := 837011806717526736603425

theorem tailTrace_4890224 : CollatzResearch.WordTrace tailWord_4890224 prefixEnd_4890224 837011806717526736603425 := by
  unfold tailWord_4890224
  simp only [CollatzResearch.WordTrace]
  refine ⟨89180561117780553305966863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118907414823707404407955817 89180561117780553305966863)
  ·
    refine ⟨133770841676670829958950295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89180561117780553305966863 133770841676670829958950295)
    ·
      refine ⟨200656262515006244938425443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133770841676670829958950295 200656262515006244938425443)
      ·
        refine ⟨300984393772509367407638165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200656262515006244938425443 300984393772509367407638165)
        ·
          refine ⟨14108643458086376597233039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 300984393772509367407638165 14108643458086376597233039)
          ·
            refine ⟨21162965187129564895849559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14108643458086376597233039 21162965187129564895849559)
            ·
              refine ⟨31744447780694347343774339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21162965187129564895849559 31744447780694347343774339)
              ·
                refine ⟨47616671671041521015661509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31744447780694347343774339 47616671671041521015661509)
                ·
                  refine ⟨8928125938320285190436533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47616671671041521015661509 8928125938320285190436533)
                  ·
                    refine ⟨837011806717526736603425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8928125938320285190436533 837011806717526736603425)
                    ·
                      rfl

theorem cell23_4890224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 1, 4, 5].length) (baseStart_4890224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4890224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4890224 prefixEnd_4890224 := by exact prefixLift 4890224
  have htrace : WordTrace (prefixWord ++ tailWord_4890224) baseStart_4890224 baseEnd_4890224 := by
    simpa [prefixWord, tailWord_4890224, baseEnd_4890224] using wordTrace_append hprefix tailTrace_4890224
  have hstable : (prefixWord ++ tailWord_4890224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4890224).length < 2 ^ (prefixWord ++ tailWord_4890224).sum := by decide
  have hdescent : baseEnd_4890224 < baseStart_4890224 := by decide
  rcases family_descends (prefixWord ++ tailWord_4890224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4890258 : List Nat := [3, 2, 3, 1, 3, 1, 2, 1, 2, 5]
def baseStart_4890258 : Nat := 118140960795 + 4890258 * 2 ^ 59
def prefixEnd_4890258 : Nat := 4983230072969 + 3 ^ 40 * 4890258 * 2
def baseEnd_4890258 : Nat := 837017626164944358928373

theorem tailTrace_4890258 : CollatzResearch.WordTrace tailWord_4890258 prefixEnd_4890258 837017626164944358928373 := by
  unfold tailWord_4890258
  simp only [CollatzResearch.WordTrace]
  refine ⟨44590590579359482604667857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118908241544958620279114285 44590590579359482604667857)
  ·
    refine ⟨33442942934519611953500893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44590590579359482604667857 33442942934519611953500893)
    ·
      refine ⟨12541103600444854482562835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33442942934519611953500893 12541103600444854482562835)
      ·
        refine ⟨18811655400667281723844253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12541103600444854482562835 18811655400667281723844253)
        ·
          refine ⟨7054370775250230646441595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18811655400667281723844253 7054370775250230646441595)
          ·
            refine ⟨10581556162875345969662393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7054370775250230646441595 10581556162875345969662393)
            ·
              refine ⟨7936167122156509477246795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10581556162875345969662393 7936167122156509477246795)
              ·
                refine ⟨11904250683234764215870193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7936167122156509477246795 11904250683234764215870193)
                ·
                  refine ⟨8928188012426073161902645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11904250683234764215870193 8928188012426073161902645)
                  ·
                    refine ⟨837017626164944358928373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8928188012426073161902645 837017626164944358928373)
                    ·
                      rfl

theorem cell23_4890258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 2, 1, 2, 5].length) (baseStart_4890258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4890258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4890258 prefixEnd_4890258 := by exact prefixLift 4890258
  have htrace : WordTrace (prefixWord ++ tailWord_4890258) baseStart_4890258 baseEnd_4890258 := by
    simpa [prefixWord, tailWord_4890258, baseEnd_4890258] using wordTrace_append hprefix tailTrace_4890258
  have hstable : (prefixWord ++ tailWord_4890258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4890258).length < 2 ^ (prefixWord ++ tailWord_4890258).sum := by decide
  have hdescent : baseEnd_4890258 < baseStart_4890258 := by decide
  rcases family_descends (prefixWord ++ tailWord_4890258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4890371 : List Nat := [1, 1, 1, 3, 2, 2, 2, 3, 3, 2, 3]
def baseStart_4890371 : Nat := 118140960795 + 4890371 * 2 ^ 59
def prefixEnd_4890371 : Nat := 4983230072969 + 3 ^ 40 * 4890371 * 2
def baseEnd_4890371 : Nat := 2511110901808791134672099

theorem tailTrace_4890371 : CollatzResearch.WordTrace tailWord_4890371 prefixEnd_4890371 2511110901808791134672099 := by
  unfold tailWord_4890371
  simp only [CollatzResearch.WordTrace]
  refine ⟨178366483766028550717534967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118910989177352367145023311 178366483766028550717534967)
  ·
    refine ⟨267549725649042826076302451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178366483766028550717534967 267549725649042826076302451)
    ·
      refine ⟨401324588473564239114453677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 267549725649042826076302451 401324588473564239114453677)
      ·
        refine ⟨150496720677586589667920129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 401324588473564239114453677 150496720677586589667920129)
        ·
          refine ⟨112872540508189942250940097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150496720677586589667920129 112872540508189942250940097)
          ·
            refine ⟨84654405381142456688205073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112872540508189942250940097 84654405381142456688205073)
            ·
              refine ⟨63490804035856842516153805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84654405381142456688205073 63490804035856842516153805)
              ·
                refine ⟨23809051513446315943557677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63490804035856842516153805 23809051513446315943557677)
                ·
                  refine ⟨8928394317542368478834129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23809051513446315943557677 8928394317542368478834129)
                  ·
                    refine ⟨6696295738156776359125597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8928394317542368478834129 6696295738156776359125597)
                    ·
                      refine ⟨2511110901808791134672099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6696295738156776359125597 2511110901808791134672099)
                      ·
                        rfl

theorem cell23_4890371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 3, 3, 2, 3].length) (baseStart_4890371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4890371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4890371 prefixEnd_4890371 := by exact prefixLift 4890371
  have htrace : WordTrace (prefixWord ++ tailWord_4890371) baseStart_4890371 baseEnd_4890371 := by
    simpa [prefixWord, tailWord_4890371, baseEnd_4890371] using wordTrace_append hprefix tailTrace_4890371
  have hstable : (prefixWord ++ tailWord_4890371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4890371).length < 2 ^ (prefixWord ++ tailWord_4890371).sum := by decide
  have hdescent : baseEnd_4890371 < baseStart_4890371 := by decide
  rcases family_descends (prefixWord ++ tailWord_4890371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4890391 : List Nat := [1, 1, 3, 4, 2, 3, 9]
def baseStart_4890391 : Nat := 118140960795 + 4890391 * 2 ^ 59
def prefixEnd_4890391 : Nat := 4983230072969 + 3 ^ 40 * 4890391 * 2
def baseEnd_4890391 : Nat := 31001495943480013042247

theorem tailTrace_4890391 : CollatzResearch.WordTrace tailWord_4890391 prefixEnd_4890391 31001495943480013042247 := by
  unfold tailWord_4890391
  simp only [CollatzResearch.WordTrace]
  refine ⟨178367213225956094133263027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118911475483970729422175351 178367213225956094133263027)
  ·
    refine ⟨267550819838934141199894541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178367213225956094133263027 267550819838934141199894541)
    ·
      refine ⟨100331557439600302949960453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 267550819838934141199894541 100331557439600302949960453)
      ·
        refine ⟨18812167019925056803117585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 100331557439600302949960453 18812167019925056803117585)
        ·
          refine ⟨14109125264943792602338189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18812167019925056803117585 14109125264943792602338189)
          ·
            refine ⟨5290921974353922225876821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14109125264943792602338189 5290921974353922225876821)
            ·
              refine ⟨31001495943480013042247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5290921974353922225876821 31001495943480013042247)
              ·
                rfl

theorem cell23_4890391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 9].length) (baseStart_4890391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4890391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4890391 prefixEnd_4890391 := by exact prefixLift 4890391
  have htrace : WordTrace (prefixWord ++ tailWord_4890391) baseStart_4890391 baseEnd_4890391 := by
    simpa [prefixWord, tailWord_4890391, baseEnd_4890391] using wordTrace_append hprefix tailTrace_4890391
  have hstable : (prefixWord ++ tailWord_4890391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4890391).length < 2 ^ (prefixWord ++ tailWord_4890391).sum := by decide
  have hdescent : baseEnd_4890391 < baseStart_4890391 := by decide
  rcases family_descends (prefixWord ++ tailWord_4890391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4890422 : List Nat := [5, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3]
def baseStart_4890422 : Nat := 118140960795 + 4890422 * 2 ^ 59
def prefixEnd_4890422 : Nat := 4983230072969 + 3 ^ 40 * 4890422 * 2
def baseEnd_4890422 : Nat := 2511137089322170435134365

theorem tailTrace_4890422 : CollatzResearch.WordTrace tailWord_4890422 prefixEnd_4890422 2511137089322170435134365 := by
  unfold tailWord_4890422
  simp only [CollatzResearch.WordTrace]
  refine ⟨11148021493052736651727595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 118912229259229190951761013 11148021493052736651727595)
  ·
    refine ⟨16722032239579104977591393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11148021493052736651727595 16722032239579104977591393)
    ·
      refine ⟨12541524179684328733193545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16722032239579104977591393 12541524179684328733193545)
      ·
        refine ⟨9406143134763246549895159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12541524179684328733193545 9406143134763246549895159)
        ·
          refine ⟨14109214702144869824842739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9406143134763246549895159 14109214702144869824842739)
          ·
            refine ⟨21163822053217304737264109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14109214702144869824842739 21163822053217304737264109)
            ·
              refine ⟨7936433269956489276474041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21163822053217304737264109 7936433269956489276474041)
              ·
                refine ⟨5952324952467366957355531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7936433269956489276474041 5952324952467366957355531)
                ·
                  refine ⟨8928487428701050436033297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5952324952467366957355531 8928487428701050436033297)
                  ·
                    refine ⟨6696365571525787827024973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8928487428701050436033297 6696365571525787827024973)
                    ·
                      refine ⟨2511137089322170435134365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6696365571525787827024973 2511137089322170435134365)
                      ·
                        rfl

theorem cell23_4890422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_4890422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4890422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4890422 prefixEnd_4890422 := by exact prefixLift 4890422
  have htrace : WordTrace (prefixWord ++ tailWord_4890422) baseStart_4890422 baseEnd_4890422 := by
    simpa [prefixWord, tailWord_4890422, baseEnd_4890422] using wordTrace_append hprefix tailTrace_4890422
  have hstable : (prefixWord ++ tailWord_4890422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4890422).length < 2 ^ (prefixWord ++ tailWord_4890422).sum := by decide
  have hdescent : baseEnd_4890422 < baseStart_4890422 := by decide
  rcases family_descends (prefixWord ++ tailWord_4890422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4890452 : List Nat := [2, 4, 1, 1, 3, 2, 2, 2, 2, 1, 3]
def baseStart_4890452 : Nat := 118140960795 + 4890452 * 2 ^ 59
def prefixEnd_4890452 : Nat := 4983230072969 + 3 ^ 40 * 4890452 * 2
def baseEnd_4890452 : Nat := 2511152493741805317759227

theorem tailTrace_4890452 : CollatzResearch.WordTrace tailWord_4890452 prefixEnd_4890452 2511152493741805317759227 := by
  unfold tailWord_4890452
  simp only [CollatzResearch.WordTrace]
  refine ⟨89184719039367550775616805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118912958719156734367489073 89184719039367550775616805)
  ·
    refine ⟨16722134819881415770428151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89184719039367550775616805 16722134819881415770428151)
    ·
      refine ⟨25083202229822123655642227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16722134819881415770428151 25083202229822123655642227)
      ·
        refine ⟨37624803344733185483463341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25083202229822123655642227 37624803344733185483463341)
        ·
          refine ⟨14109301254274944556298753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37624803344733185483463341 14109301254274944556298753)
          ·
            refine ⟨10581975940706208417224065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14109301254274944556298753 10581975940706208417224065)
            ·
              refine ⟨7936481955529656312918049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10581975940706208417224065 7936481955529656312918049)
              ·
                refine ⟨5952361466647242234688537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7936481955529656312918049 5952361466647242234688537)
                ·
                  refine ⟨4464271099985431676016403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5952361466647242234688537 4464271099985431676016403)
                  ·
                    refine ⟨6696406649978147514024605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4464271099985431676016403 6696406649978147514024605)
                    ·
                      refine ⟨2511152493741805317759227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6696406649978147514024605 2511152493741805317759227)
                      ·
                        rfl

theorem cell23_4890452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 2, 2, 2, 1, 3].length) (baseStart_4890452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4890452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4890452 prefixEnd_4890452 := by exact prefixLift 4890452
  have htrace : WordTrace (prefixWord ++ tailWord_4890452) baseStart_4890452 baseEnd_4890452 := by
    simpa [prefixWord, tailWord_4890452, baseEnd_4890452] using wordTrace_append hprefix tailTrace_4890452
  have hstable : (prefixWord ++ tailWord_4890452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4890452).length < 2 ^ (prefixWord ++ tailWord_4890452).sum := by decide
  have hdescent : baseEnd_4890452 < baseStart_4890452 := by decide
  rcases family_descends (prefixWord ++ tailWord_4890452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4890458 : List Nat := [3, 1, 1, 2, 1, 3, 1, 2, 3, 4, 2]
def baseStart_4890458 : Nat := 118140960795 + 4890458 * 2 ^ 59
def prefixEnd_4890458 : Nat := 4983230072969 + 3 ^ 40 * 4890458 * 2
def baseEnd_4890458 : Nat := 2511155574625732294284199

theorem tailTrace_4890458 : CollatzResearch.WordTrace tailWord_4890458 prefixEnd_4890458 2511155574625732294284199 := by
  unfold tailWord_4890458
  simp only [CollatzResearch.WordTrace]
  refine ⟨44592414229178341143988007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118913104611142243050634685 44592414229178341143988007)
  ·
    refine ⟨66888621343767511715982011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44592414229178341143988007 66888621343767511715982011)
    ·
      refine ⟨100332932015651267573973017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66888621343767511715982011 100332932015651267573973017)
      ·
        refine ⟨75249699011738450680479763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100332932015651267573973017 75249699011738450680479763)
        ·
          refine ⟨112874548517607676020719645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75249699011738450680479763 112874548517607676020719645)
          ·
            refine ⟨42327955694102878507769867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 112874548517607676020719645 42327955694102878507769867)
            ·
              refine ⟨63491933541154317761654801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42327955694102878507769867 63491933541154317761654801)
              ·
                refine ⟨47618950155865738321241101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63491933541154317761654801 47618950155865738321241101)
                ·
                  refine ⟨17857106308449651870465413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47618950155865738321241101 17857106308449651870465413)
                  ·
                    refine ⟨3348207432834309725712265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17857106308449651870465413 3348207432834309725712265)
                    ·
                      refine ⟨2511155574625732294284199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3348207432834309725712265 2511155574625732294284199)
                      ·
                        rfl

theorem cell23_4890458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 2, 3, 4, 2].length) (baseStart_4890458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4890458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4890458 prefixEnd_4890458 := by exact prefixLift 4890458
  have htrace : WordTrace (prefixWord ++ tailWord_4890458) baseStart_4890458 baseEnd_4890458 := by
    simpa [prefixWord, tailWord_4890458, baseEnd_4890458] using wordTrace_append hprefix tailTrace_4890458
  have hstable : (prefixWord ++ tailWord_4890458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4890458).length < 2 ^ (prefixWord ++ tailWord_4890458).sum := by decide
  have hdescent : baseEnd_4890458 < baseStart_4890458 := by decide
  rcases family_descends (prefixWord ++ tailWord_4890458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4890468 : List Nat := [2, 3, 1, 1, 5, 1, 1, 1, 2, 6]
def baseStart_4890468 : Nat := 118140960795 + 4890468 * 2 ^ 59
def prefixEnd_4890468 : Nat := 4983230072969 + 3 ^ 40 * 4890468 * 2
def baseEnd_4890468 : Nat := 837053569810759085053051

theorem tailTrace_4890468 : CollatzResearch.WordTrace tailWord_4890468 prefixEnd_4890468 837053569810759085053051 := by
  unfold tailWord_4890468
  simp only [CollatzResearch.WordTrace]
  refine ⟨89185010823338568141908029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118913347764451424189210705 89185010823338568141908029)
  ·
    refine ⟨33444379058751963053215511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89185010823338568141908029 33444379058751963053215511)
    ·
      refine ⟨50166568588127944579823267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33444379058751963053215511 50166568588127944579823267)
      ·
        refine ⟨75249852882191916869734901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50166568588127944579823267 75249852882191916869734901)
        ·
          refine ⟨7054673707705492206537647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 75249852882191916869734901 7054673707705492206537647)
          ·
            refine ⟨10582010561558238309806471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7054673707705492206537647 10582010561558238309806471)
            ·
              refine ⟨15873015842337357464709707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10582010561558238309806471 15873015842337357464709707)
              ·
                refine ⟨23809523763506036197064561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15873015842337357464709707 23809523763506036197064561)
                ·
                  refine ⟨17857142822629527147798421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23809523763506036197064561 17857142822629527147798421)
                  ·
                    refine ⟨837053569810759085053051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17857142822629527147798421 837053569810759085053051)
                    ·
                      rfl

theorem cell23_4890468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 1, 2, 6].length) (baseStart_4890468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4890468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4890468 prefixEnd_4890468 := by exact prefixLift 4890468
  have htrace : WordTrace (prefixWord ++ tailWord_4890468) baseStart_4890468 baseEnd_4890468 := by
    simpa [prefixWord, tailWord_4890468, baseEnd_4890468] using wordTrace_append hprefix tailTrace_4890468
  have hstable : (prefixWord ++ tailWord_4890468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4890468).length < 2 ^ (prefixWord ++ tailWord_4890468).sum := by decide
  have hdescent : baseEnd_4890468 < baseStart_4890468 := by decide
  rcases family_descends (prefixWord ++ tailWord_4890468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4890481 : List Nat := [1, 2, 2, 2, 1, 3, 3, 2, 7]
def baseStart_4890481 : Nat := 118140960795 + 4890481 * 2 ^ 59
def prefixEnd_4890481 : Nat := 4983230072969 + 3 ^ 40 * 4890481 * 2
def baseEnd_4890481 : Nat := 279018598297865078255177

theorem tailTrace_4890481 : CollatzResearch.WordTrace tailWord_4890481 prefixEnd_4890481 279018598297865078255177 := by
  unfold tailWord_4890481
  simp only [CollatzResearch.WordTrace]
  refine ⟨178370495795630039504039297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118913663863753359669359531 178370495795630039504039297)
  ·
    refine ⟨133777871846722529628029473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178370495795630039504039297 133777871846722529628029473)
    ·
      refine ⟨100333403885041897221022105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133777871846722529628029473 100333403885041897221022105)
      ·
        refine ⟨75250052913781422915766579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100333403885041897221022105 75250052913781422915766579)
        ·
          refine ⟨112875079370672134373649869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75250052913781422915766579 112875079370672134373649869)
          ·
            refine ⟨42328154764002050390118701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 112875079370672134373649869 42328154764002050390118701)
            ·
              refine ⟨15873058036500768896294513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42328154764002050390118701 15873058036500768896294513)
              ·
                refine ⟨11904793527375576672220885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15873058036500768896294513 11904793527375576672220885)
                ·
                  refine ⟨279018598297865078255177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11904793527375576672220885 279018598297865078255177)
                  ·
                    rfl

theorem cell23_4890481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 2, 7].length) (baseStart_4890481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4890481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4890481 prefixEnd_4890481 := by exact prefixLift 4890481
  have htrace : WordTrace (prefixWord ++ tailWord_4890481) baseStart_4890481 baseEnd_4890481 := by
    simpa [prefixWord, tailWord_4890481, baseEnd_4890481] using wordTrace_append hprefix tailTrace_4890481
  have hstable : (prefixWord ++ tailWord_4890481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4890481).length < 2 ^ (prefixWord ++ tailWord_4890481).sum := by decide
  have hdescent : baseEnd_4890481 < baseStart_4890481 := by decide
  rcases family_descends (prefixWord ++ tailWord_4890481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4890491 : List Nat := [1, 1, 1, 1, 1, 5, 1, 1, 3, 5, 3]
def baseStart_4890491 : Nat := 118140960795 + 4890491 * 2 ^ 59
def prefixEnd_4890491 : Nat := 4983230072969 + 3 ^ 40 * 4890491 * 2
def baseEnd_4890491 : Nat := 2511172519487330665171547

theorem tailTrace_4890491 : CollatzResearch.WordTrace tailWord_4890491 prefixEnd_4890491 2511172519487330665171547 := by
  unfold tailWord_4890491
  simp only [CollatzResearch.WordTrace]
  refine ⟨178370860525593811211903327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118913907017062540807935551 178370860525593811211903327)
  ·
    refine ⟨267556290788390716817854991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178370860525593811211903327 267556290788390716817854991)
    ·
      refine ⟨401334436182586075226782487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 267556290788390716817854991 401334436182586075226782487)
      ·
        refine ⟨602001654273879112840173731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 401334436182586075226782487 602001654273879112840173731)
        ·
          refine ⟨903002481410818669260260597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 602001654273879112840173731 903002481410818669260260597)
          ·
            refine ⟨84656482632264250243149431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 903002481410818669260260597 84656482632264250243149431)
            ·
              refine ⟨126984723948396375364724147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84656482632264250243149431 126984723948396375364724147)
              ·
                refine ⟨190477085922594563047086221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126984723948396375364724147 190477085922594563047086221)
                ·
                  refine ⟨71428907220972961142657333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 190477085922594563047086221 71428907220972961142657333)
                  ·
                    refine ⟨6696460051966215107124125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 71428907220972961142657333 6696460051966215107124125)
                    ·
                      refine ⟨2511172519487330665171547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6696460051966215107124125 2511172519487330665171547)
                      ·
                        rfl

theorem cell23_4890491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 3, 5, 3].length) (baseStart_4890491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4890491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4890491 prefixEnd_4890491 := by exact prefixLift 4890491
  have htrace : WordTrace (prefixWord ++ tailWord_4890491) baseStart_4890491 baseEnd_4890491 := by
    simpa [prefixWord, tailWord_4890491, baseEnd_4890491] using wordTrace_append hprefix tailTrace_4890491
  have hstable : (prefixWord ++ tailWord_4890491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4890491).length < 2 ^ (prefixWord ++ tailWord_4890491).sum := by decide
  have hdescent : baseEnd_4890491 < baseStart_4890491 := by decide
  rcases family_descends (prefixWord ++ tailWord_4890491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4890521 : List Nat := [1, 2, 1, 2, 1, 3, 2, 3, 1, 2, 5]
def baseStart_4890521 : Nat := 118140960795 + 4890521 * 2 ^ 59
def prefixEnd_4890521 : Nat := 4983230072969 + 3 ^ 40 * 4890521 * 2
def baseEnd_4890521 : Nat := 2511187923906965547796409

theorem tailTrace_4890521 : CollatzResearch.WordTrace tailWord_4890521 prefixEnd_4890521 2511187923906965547796409 := by
  unfold tailWord_4890521
  simp only [CollatzResearch.WordTrace]
  refine ⟨178371954715485126335495417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118914636476990084223663611 178371954715485126335495417)
  ·
    refine ⟨133778966036613844751621563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178371954715485126335495417 133778966036613844751621563)
    ·
      refine ⟨200668449054920767127432345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133778966036613844751621563 200668449054920767127432345)
      ·
        refine ⟨150501336791190575345574259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 200668449054920767127432345 150501336791190575345574259)
        ·
          refine ⟨225752005186785863018361389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150501336791190575345574259 225752005186785863018361389)
          ·
            refine ⟨84657001945044698631885521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 225752005186785863018361389 84657001945044698631885521)
            ·
              refine ⟨63492751458783523973914141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84657001945044698631885521 63492751458783523973914141)
              ·
                refine ⟨23809781797043821490217803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63492751458783523973914141 23809781797043821490217803)
                ·
                  refine ⟨35714672695565732235326705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23809781797043821490217803 35714672695565732235326705)
                  ·
                    refine ⟨26786004521674299176495029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35714672695565732235326705 26786004521674299176495029)
                    ·
                      refine ⟨2511187923906965547796409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26786004521674299176495029 2511187923906965547796409)
                      ·
                        rfl

theorem cell23_4890521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 3, 1, 2, 5].length) (baseStart_4890521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4890521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4890521 prefixEnd_4890521 := by exact prefixLift 4890521
  have htrace : WordTrace (prefixWord ++ tailWord_4890521) baseStart_4890521 baseEnd_4890521 := by
    simpa [prefixWord, tailWord_4890521, baseEnd_4890521] using wordTrace_append hprefix tailTrace_4890521
  have hstable : (prefixWord ++ tailWord_4890521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4890521).length < 2 ^ (prefixWord ++ tailWord_4890521).sum := by decide
  have hdescent : baseEnd_4890521 < baseStart_4890521 := by decide
  rcases family_descends (prefixWord ++ tailWord_4890521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4890526 : List Nat := [4, 3, 1, 3, 1, 2, 1, 1, 1, 4, 2]
def baseStart_4890526 : Nat := 118140960795 + 4890526 * 2 ^ 59
def prefixEnd_4890526 : Nat := 4983230072969 + 3 ^ 40 * 4890526 * 2
def baseEnd_4890526 : Nat := 2511190491310238028233887

theorem tailTrace_4890526 : CollatzResearch.WordTrace tailWord_4890526 prefixEnd_4890526 2511190491310238028233887 := by
  unfold tailWord_4890526
  simp only [CollatzResearch.WordTrace]
  refine ⟨22296517135058376523678429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118914758053644674792951621 22296517135058376523678429)
  ·
    refine ⟨8361193925646891196379411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22296517135058376523678429 8361193925646891196379411)
    ·
      refine ⟨12541790888470336794569117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8361193925646891196379411 12541790888470336794569117)
      ·
        refine ⟨4703171583176376297963419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12541790888470336794569117 4703171583176376297963419)
        ·
          refine ⟨7054757374764564446945129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4703171583176376297963419 7054757374764564446945129)
          ·
            refine ⟨5291068031073423335208847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7054757374764564446945129 5291068031073423335208847)
            ·
              refine ⟨7936602046610135002813271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5291068031073423335208847 7936602046610135002813271)
              ·
                refine ⟨11904903069915202504219907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7936602046610135002813271 11904903069915202504219907)
                ·
                  refine ⟨17857354604872803756329861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11904903069915202504219907 17857354604872803756329861)
                  ·
                    refine ⟨3348253988413650704311849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17857354604872803756329861 3348253988413650704311849)
                    ·
                      refine ⟨2511190491310238028233887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3348253988413650704311849 2511190491310238028233887)
                      ·
                        rfl

theorem cell23_4890526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_4890526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4890526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4890526 prefixEnd_4890526 := by exact prefixLift 4890526
  have htrace : WordTrace (prefixWord ++ tailWord_4890526) baseStart_4890526 baseEnd_4890526 := by
    simpa [prefixWord, tailWord_4890526, baseEnd_4890526] using wordTrace_append hprefix tailTrace_4890526
  have hstable : (prefixWord ++ tailWord_4890526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4890526).length < 2 ^ (prefixWord ++ tailWord_4890526).sum := by decide
  have hdescent : baseEnd_4890526 < baseStart_4890526 := by decide
  rcases family_descends (prefixWord ++ tailWord_4890526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4890551 : List Nat := [1, 1, 3, 1, 3, 1, 1, 2, 2, 3, 5]
def baseStart_4890551 : Nat := 118140960795 + 4890551 * 2 ^ 59
def prefixEnd_4890551 : Nat := 4983230072969 + 3 ^ 40 * 4890551 * 2
def baseEnd_4890551 : Nat := 2511203328326600430421271

theorem tailTrace_4890551 : CollatzResearch.WordTrace tailWord_4890551 prefixEnd_4890551 2511203328326600430421271 := by
  unfold tailWord_4890551
  simp only [CollatzResearch.WordTrace]
  refine ⟨178373048905376441459087507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118915365936917627639391671 178373048905376441459087507)
  ·
    refine ⟨267559573358064662188631261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178373048905376441459087507 267559573358064662188631261)
    ·
      refine ⟨100334840009274248320736723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 267559573358064662188631261 100334840009274248320736723)
      ·
        refine ⟨150502260013911372481105085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100334840009274248320736723 150502260013911372481105085)
        ·
          refine ⟨56438347505216764680414407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 150502260013911372481105085 56438347505216764680414407)
          ·
            refine ⟨84657521257825147020621611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56438347505216764680414407 84657521257825147020621611)
            ·
              refine ⟨126986281886737720530932417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84657521257825147020621611 126986281886737720530932417)
              ·
                refine ⟨95239711415053290398199313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 126986281886737720530932417 95239711415053290398199313)
                ·
                  refine ⟨71429783561289967798649485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 95239711415053290398199313 71429783561289967798649485)
                  ·
                    refine ⟨26786168835483737924493557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 71429783561289967798649485 26786168835483737924493557)
                    ·
                      refine ⟨2511203328326600430421271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26786168835483737924493557 2511203328326600430421271)
                      ·
                        rfl

theorem cell23_4890551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 2, 3, 5].length) (baseStart_4890551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4890551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4890551 prefixEnd_4890551 := by exact prefixLift 4890551
  have htrace : WordTrace (prefixWord ++ tailWord_4890551) baseStart_4890551 baseEnd_4890551 := by
    simpa [prefixWord, tailWord_4890551, baseEnd_4890551] using wordTrace_append hprefix tailTrace_4890551
  have hstable : (prefixWord ++ tailWord_4890551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4890551).length < 2 ^ (prefixWord ++ tailWord_4890551).sum := by decide
  have hdescent : baseEnd_4890551 < baseStart_4890551 := by decide
  rcases family_descends (prefixWord ++ tailWord_4890551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4890571 : List Nat := [1, 1, 1, 1, 3, 4, 1, 3, 8]
def baseStart_4890571 : Nat := 118140960795 + 4890571 * 2 ^ 59
def prefixEnd_4890571 : Nat := 4983230072969 + 3 ^ 40 * 4890571 * 2
def baseEnd_4890571 : Nat := 279023733104410039130131

theorem tailTrace_4890571 : CollatzResearch.WordTrace tailWord_4890571 prefixEnd_4890571 279023733104410039130131 := by
  unfold tailWord_4890571
  simp only [CollatzResearch.WordTrace]
  refine ⟨178373778365303984874815567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118915852243535989916543711 178373778365303984874815567)
  ·
    refine ⟨267560667547955977312223351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178373778365303984874815567 267560667547955977312223351)
    ·
      refine ⟨401341001321933965968335027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 267560667547955977312223351 401341001321933965968335027)
      ·
        refine ⟨602011501982900948952502541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 401341001321933965968335027 602011501982900948952502541)
        ·
          refine ⟨225754313243587855857188453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 602011501982900948952502541 225754313243587855857188453)
          ·
            refine ⟨42328933733172722973222835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 225754313243587855857188453 42328933733172722973222835)
            ·
              refine ⟨63493400599759084459834253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42328933733172722973222835 63493400599759084459834253)
              ·
                refine ⟨23810025224909656672437845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63493400599759084459834253 23810025224909656672437845)
                ·
                  refine ⟨279023733104410039130131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23810025224909656672437845 279023733104410039130131)
                  ·
                    rfl

theorem cell23_4890571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 3, 8].length) (baseStart_4890571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4890571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4890571 prefixEnd_4890571 := by exact prefixLift 4890571
  have htrace : WordTrace (prefixWord ++ tailWord_4890571) baseStart_4890571 baseEnd_4890571 := by
    simpa [prefixWord, tailWord_4890571, baseEnd_4890571] using wordTrace_append hprefix tailTrace_4890571
  have hstable : (prefixWord ++ tailWord_4890571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4890571).length < 2 ^ (prefixWord ++ tailWord_4890571).sum := by decide
  have hdescent : baseEnd_4890571 < baseStart_4890571 := by decide
  rcases family_descends (prefixWord ++ tailWord_4890571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4890611 : List Nat := [1, 1, 1, 2, 2, 2, 1, 2, 1, 3, 7]
def baseStart_4890611 : Nat := 118140960795 + 4890611 * 2 ^ 59
def prefixEnd_4890611 : Nat := 4983230072969 + 3 ^ 40 * 4890611 * 2
def baseEnd_4890611 : Nat := 2511234137165870195670995

theorem tailTrace_4890611 : CollatzResearch.WordTrace tailWord_4890611 prefixEnd_4890611 2511234137165870195670995 := by
  unfold tailWord_4890611
  simp only [CollatzResearch.WordTrace]
  refine ⟨178375237285159071706271687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118916824856772714470847791 178375237285159071706271687)
  ·
    refine ⟨267562855927738607559407531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178375237285159071706271687 267562855927738607559407531)
    ·
      refine ⟨401344283891607911339111297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 267562855927738607559407531 401344283891607911339111297)
      ·
        refine ⟨301008212918705933504333473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 401344283891607911339111297 301008212918705933504333473)
        ·
          refine ⟨225756159689029450128250105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 301008212918705933504333473 225756159689029450128250105)
          ·
            refine ⟨169317119766772087596187579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 225756159689029450128250105 169317119766772087596187579)
            ·
              refine ⟨253975679650158131394281369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 169317119766772087596187579 253975679650158131394281369)
              ·
                refine ⟨190481759737618598545711027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 253975679650158131394281369 190481759737618598545711027)
                ·
                  refine ⟨285722639606427897818566541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 190481759737618598545711027 285722639606427897818566541)
                  ·
                    refine ⟨107145989852410461681962453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 285722639606427897818566541 107145989852410461681962453)
                    ·
                      refine ⟨2511234137165870195670995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 107145989852410461681962453 2511234137165870195670995)
                      ·
                        rfl

theorem cell23_4890611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 3, 7].length) (baseStart_4890611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4890611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4890611 prefixEnd_4890611 := by exact prefixLift 4890611
  have htrace : WordTrace (prefixWord ++ tailWord_4890611) baseStart_4890611 baseEnd_4890611 := by
    simpa [prefixWord, tailWord_4890611, baseEnd_4890611] using wordTrace_append hprefix tailTrace_4890611
  have hstable : (prefixWord ++ tailWord_4890611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4890611).length < 2 ^ (prefixWord ++ tailWord_4890611).sum := by decide
  have hdescent : baseEnd_4890611 < baseStart_4890611 := by decide
  rcases family_descends (prefixWord ++ tailWord_4890611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4890622 : List Nat := [4, 2, 2, 2, 1, 2, 2, 2, 6]
def baseStart_4890622 : Nat := 118140960795 + 4890622 * 2 ^ 59
def prefixEnd_4890622 : Nat := 4983230072969 + 3 ^ 40 * 4890622 * 2
def baseEnd_4890622 : Nat := 279026642828118850292605

theorem tailTrace_4890622 : CollatzResearch.WordTrace tailWord_4890622 prefixEnd_4890622 279026642828118850292605 := by
  unfold tailWord_4890622
  simp only [CollatzResearch.WordTrace]
  refine ⟨22296954811014902573115265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118917092325412813723281413 22296954811014902573115265)
  ·
    refine ⟨16722716108261176929836449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22296954811014902573115265 16722716108261176929836449)
    ·
      refine ⟨12542037081195882697377337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16722716108261176929836449 12542037081195882697377337)
      ·
        refine ⟨9406527810896912023033003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12542037081195882697377337 9406527810896912023033003)
        ·
          refine ⟨14109791716345368034549505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9406527810896912023033003 14109791716345368034549505)
          ·
            refine ⟨10582343787259026025912129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14109791716345368034549505 10582343787259026025912129)
            ·
              refine ⟨7936757840444269519434097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10582343787259026025912129 7936757840444269519434097)
              ·
                refine ⟨5952568380333202139575573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7936757840444269519434097 5952568380333202139575573)
                ·
                  refine ⟨279026642828118850292605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5952568380333202139575573 279026642828118850292605)
                  ·
                    rfl

theorem cell23_4890622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 2, 2, 6].length) (baseStart_4890622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4890622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4890622 prefixEnd_4890622 := by exact prefixLift 4890622
  have htrace : WordTrace (prefixWord ++ tailWord_4890622) baseStart_4890622 baseEnd_4890622 := by
    simpa [prefixWord, tailWord_4890622, baseEnd_4890622] using wordTrace_append hprefix tailTrace_4890622
  have hstable : (prefixWord ++ tailWord_4890622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4890622).length < 2 ^ (prefixWord ++ tailWord_4890622).sum := by decide
  have hdescent : baseEnd_4890622 < baseStart_4890622 := by decide
  rcases family_descends (prefixWord ++ tailWord_4890622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4890655 : List Nat := [1, 1, 2, 4, 1, 2, 2, 4, 1, 1, 4]
def baseStart_4890655 : Nat := 118140960795 + 4890655 * 2 ^ 59
def prefixEnd_4890655 : Nat := 4983230072969 + 3 ^ 40 * 4890655 * 2
def baseEnd_4890655 : Nat := 2511256730314668023520793

theorem tailTrace_4890655 : CollatzResearch.WordTrace tailWord_4890655 prefixEnd_4890655 2511256730314668023520793 := by
  unfold tailWord_4890655
  simp only [CollatzResearch.WordTrace]
  refine ⟨178376842096999667220873419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118917894731333111480582279 178376842096999667220873419)
  ·
    refine ⟨267565263145499500831310129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178376842096999667220873419 267565263145499500831310129)
    ·
      refine ⟨200673947359124625623482597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 267565263145499500831310129 200673947359124625623482597)
      ·
        refine ⟨37626365129835867304402987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 200673947359124625623482597 37626365129835867304402987)
        ·
          refine ⟨56439547694753800956604481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37626365129835867304402987 56439547694753800956604481)
          ·
            refine ⟨42329660771065350717453361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56439547694753800956604481 42329660771065350717453361)
            ·
              refine ⟨31747245578299013038090021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42329660771065350717453361 31747245578299013038090021)
              ·
                refine ⟨5952608545931064944641879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31747245578299013038090021 5952608545931064944641879)
                ·
                  refine ⟨8928912818896597416962819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5952608545931064944641879 8928912818896597416962819)
                  ·
                    refine ⟨13393369228344896125444229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8928912818896597416962819 13393369228344896125444229)
                    ·
                      refine ⟨2511256730314668023520793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13393369228344896125444229 2511256730314668023520793)
                      ·
                        rfl

theorem cell23_4890655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 4, 1, 1, 4].length) (baseStart_4890655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4890655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4890655 prefixEnd_4890655 := by exact prefixLift 4890655
  have htrace : WordTrace (prefixWord ++ tailWord_4890655) baseStart_4890655 baseEnd_4890655 := by
    simpa [prefixWord, tailWord_4890655, baseEnd_4890655] using wordTrace_append hprefix tailTrace_4890655
  have hstable : (prefixWord ++ tailWord_4890655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4890655).length < 2 ^ (prefixWord ++ tailWord_4890655).sum := by decide
  have hdescent : baseEnd_4890655 < baseStart_4890655 := by decide
  rcases family_descends (prefixWord ++ tailWord_4890655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4890666 : List Nat := [3, 1, 4, 1, 2, 2, 2, 3, 1, 1, 3]
def baseStart_4890666 : Nat := 118140960795 + 4890666 * 2 ^ 59
def prefixEnd_4890666 : Nat := 4983230072969 + 3 ^ 40 * 4890666 * 2
def baseEnd_4890666 : Nat := 2511262378601867480483243

theorem tailTrace_4890666 : CollatzResearch.WordTrace tailWord_4890666 prefixEnd_4890666 2511262378601867480483243 := by
  unfold tailWord_4890666
  simp only [CollatzResearch.WordTrace]
  refine ⟨44594310824989954024880963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118918162199973210733015901 44594310824989954024880963)
  ·
    refine ⟨66891466237484931037321445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44594310824989954024880963 66891466237484931037321445)
    ·
      refine ⟨12542149919528424569497771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66891466237484931037321445 12542149919528424569497771)
      ·
        refine ⟨18813224879292636854246657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12542149919528424569497771 18813224879292636854246657)
        ·
          refine ⟨14109918659469477640684993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18813224879292636854246657 14109918659469477640684993)
          ·
            refine ⟨10582438994602108230513745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14109918659469477640684993 10582438994602108230513745)
            ·
              refine ⟨7936829245951581172885309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10582438994602108230513745 7936829245951581172885309)
              ·
                refine ⟨2976310967231842939831991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7936829245951581172885309 2976310967231842939831991)
                ·
                  refine ⟨4464466450847764409747987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2976310967231842939831991 4464466450847764409747987)
                  ·
                    refine ⟨6696699676271646614621981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4464466450847764409747987 6696699676271646614621981)
                    ·
                      refine ⟨2511262378601867480483243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6696699676271646614621981 2511262378601867480483243)
                      ·
                        rfl

theorem cell23_4890666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 2, 3, 1, 1, 3].length) (baseStart_4890666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4890666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4890666 prefixEnd_4890666 := by exact prefixLift 4890666
  have htrace : WordTrace (prefixWord ++ tailWord_4890666) baseStart_4890666 baseEnd_4890666 := by
    simpa [prefixWord, tailWord_4890666, baseEnd_4890666] using wordTrace_append hprefix tailTrace_4890666
  have hstable : (prefixWord ++ tailWord_4890666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4890666).length < 2 ^ (prefixWord ++ tailWord_4890666).sum := by decide
  have hdescent : baseEnd_4890666 < baseStart_4890666 := by decide
  rcases family_descends (prefixWord ++ tailWord_4890666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4890668 : List Nat := [2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 4]
def baseStart_4890668 : Nat := 118140960795 + 4890668 * 2 ^ 59
def prefixEnd_4890668 : Nat := 4983230072969 + 3 ^ 40 * 4890668 * 2
def baseEnd_4890668 : Nat := 2511263405563176472658233

theorem tailTrace_4890668 : CollatzResearch.WordTrace tailWord_4890668 prefixEnd_4890668 2511263405563176472658233 := by
  unfold tailWord_4890668
  simp only [CollatzResearch.WordTrace]
  refine ⟨89188658122976285220548329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118918210830635046960731105 89188658122976285220548329)
  ·
    refine ⟨66891493592232213915411247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89188658122976285220548329 66891493592232213915411247)
    ·
      refine ⟨100337240388348320873116871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66891493592232213915411247 100337240388348320873116871)
      ·
        refine ⟨150505860582522481309675307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100337240388348320873116871 150505860582522481309675307)
        ·
          refine ⟨225758790873783721964512961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150505860582522481309675307 225758790873783721964512961)
          ·
            refine ⟨169319093155337791473384721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 225758790873783721964512961 169319093155337791473384721)
            ·
              refine ⟨126989319866503343605038541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 169319093155337791473384721 126989319866503343605038541)
              ·
                refine ⟨47620994949938753851889453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 126989319866503343605038541 47620994949938753851889453)
                ·
                  refine ⟨17857873106227032694458545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47620994949938753851889453 17857873106227032694458545)
                  ·
                    refine ⟨13393404829670274520843909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17857873106227032694458545 13393404829670274520843909)
                    ·
                      refine ⟨2511263405563176472658233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13393404829670274520843909 2511263405563176472658233)
                      ·
                        rfl

theorem cell23_4890668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 4].length) (baseStart_4890668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4890668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4890668 prefixEnd_4890668 := by exact prefixLift 4890668
  have htrace : WordTrace (prefixWord ++ tailWord_4890668) baseStart_4890668 baseEnd_4890668 := by
    simpa [prefixWord, tailWord_4890668, baseEnd_4890668] using wordTrace_append hprefix tailTrace_4890668
  have hstable : (prefixWord ++ tailWord_4890668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4890668).length < 2 ^ (prefixWord ++ tailWord_4890668).sum := by decide
  have hdescent : baseEnd_4890668 < baseStart_4890668 := by decide
  rcases family_descends (prefixWord ++ tailWord_4890668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4890672 : List Nat := [2, 1, 1, 1, 2, 5, 4, 1, 1, 1, 4]
def baseStart_4890672 : Nat := 118140960795 + 4890672 * 2 ^ 59
def prefixEnd_4890672 : Nat := 4983230072969 + 3 ^ 40 * 4890672 * 2
def baseEnd_4890672 : Nat := 2511265459485794457008215

theorem tailTrace_4890672 : CollatzResearch.WordTrace tailWord_4890672 prefixEnd_4890672 2511265459485794457008215 := by
  unfold tailWord_4890672
  simp only [CollatzResearch.WordTrace]
  refine ⟨89188731068969039562121135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118918308091958719416161513 89188731068969039562121135)
  ·
    refine ⟨133783096603453559343181703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89188731068969039562121135 133783096603453559343181703)
    ·
      refine ⟨200674644905180339014772555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133783096603453559343181703 200674644905180339014772555)
      ·
        refine ⟨301011967357770508522158833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200674644905180339014772555 301011967357770508522158833)
        ·
          refine ⟨225758975518327881391619125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 301011967357770508522158833 225758975518327881391619125)
          ·
            refine ⟨21164903954843238880464293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 225758975518327881391619125 21164903954843238880464293)
            ·
              refine ⟨3968419491533107290087055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21164903954843238880464293 3968419491533107290087055)
              ·
                refine ⟨5952629237299660935130583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3968419491533107290087055 5952629237299660935130583)
                ·
                  refine ⟨8928943855949491402695875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5952629237299660935130583 8928943855949491402695875)
                  ·
                    refine ⟨13393415783924237104043813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8928943855949491402695875 13393415783924237104043813)
                    ·
                      refine ⟨2511265459485794457008215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13393415783924237104043813 2511265459485794457008215)
                      ·
                        rfl

theorem cell23_4890672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 4, 1, 1, 1, 4].length) (baseStart_4890672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4890672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4890672 prefixEnd_4890672 := by exact prefixLift 4890672
  have htrace : WordTrace (prefixWord ++ tailWord_4890672) baseStart_4890672 baseEnd_4890672 := by
    simpa [prefixWord, tailWord_4890672, baseEnd_4890672] using wordTrace_append hprefix tailTrace_4890672
  have hstable : (prefixWord ++ tailWord_4890672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4890672).length < 2 ^ (prefixWord ++ tailWord_4890672).sum := by decide
  have hdescent : baseEnd_4890672 < baseStart_4890672 := by decide
  rcases family_descends (prefixWord ++ tailWord_4890672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4890689 : List Nat := [1, 2, 5, 1, 2, 1, 1, 3, 3, 2, 2]
def baseStart_4890689 : Nat := 118140960795 + 4890689 * 2 ^ 59
def prefixEnd_4890689 : Nat := 4983230072969 + 3 ^ 40 * 4890689 * 2
def baseEnd_4890689 : Nat := 2511274188656920890495637

theorem tailTrace_4890689 : CollatzResearch.WordTrace tailWord_4890689 prefixEnd_4890689 2511274188656920890495637 := by
  unfold tailWord_4890689
  simp only [CollatzResearch.WordTrace]
  refine ⟨178378082178876491027611121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118918721452584327351740747 178378082178876491027611121)
  ·
    refine ⟨133783561634157368270708341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178378082178876491027611121 133783561634157368270708341)
    ·
      refine ⟨12542208903202253275378907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 133783561634157368270708341 12542208903202253275378907)
      ·
        refine ⟨18813313354803379913068361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12542208903202253275378907 18813313354803379913068361)
        ·
          refine ⟨14109985016102534934801271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18813313354803379913068361 14109985016102534934801271)
          ·
            refine ⟨21164977524153802402201907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14109985016102534934801271 21164977524153802402201907)
            ·
              refine ⟨31747466286230703603302861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21164977524153802402201907 31747466286230703603302861)
              ·
                refine ⟨11905299857336513851238573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31747466286230703603302861 11905299857336513851238573)
                ·
                  refine ⟨4464487446501192694214465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11905299857336513851238573 4464487446501192694214465)
                  ·
                    refine ⟨3348365584875894520660849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4464487446501192694214465 3348365584875894520660849)
                    ·
                      refine ⟨2511274188656920890495637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3348365584875894520660849 2511274188656920890495637)
                      ·
                        rfl

theorem cell23_4890689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 3, 3, 2, 2].length) (baseStart_4890689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4890689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4890689 prefixEnd_4890689 := by exact prefixLift 4890689
  have htrace : WordTrace (prefixWord ++ tailWord_4890689) baseStart_4890689 baseEnd_4890689 := by
    simpa [prefixWord, tailWord_4890689, baseEnd_4890689] using wordTrace_append hprefix tailTrace_4890689
  have hstable : (prefixWord ++ tailWord_4890689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4890689).length < 2 ^ (prefixWord ++ tailWord_4890689).sum := by decide
  have hdescent : baseEnd_4890689 < baseStart_4890689 := by decide
  rcases family_descends (prefixWord ++ tailWord_4890689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4890702 : List Nat := [4, 1, 1, 1, 1, 6, 1, 1, 1, 2, 4]
def baseStart_4890702 : Nat := 118140960795 + 4890702 * 2 ^ 59
def prefixEnd_4890702 : Nat := 4983230072969 + 3 ^ 40 * 4890702 * 2
def baseEnd_4890702 : Nat := 2511280863905429339633077

theorem tailTrace_4890702 : CollatzResearch.WordTrace tailWord_4890702 prefixEnd_4890702 2511280863905429339633077 := by
  unfold tailWord_4890702
  simp only [CollatzResearch.WordTrace]
  refine ⟨22297319540978674280979295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118919037551886262831889573 22297319540978674280979295)
  ·
    refine ⟨33445979311468011421468943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22297319540978674280979295 33445979311468011421468943)
    ·
      refine ⟨50168968967202017132203415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33445979311468011421468943 50168968967202017132203415)
      ·
        refine ⟨75253453450803025698305123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50168968967202017132203415 75253453450803025698305123)
        ·
          refine ⟨112880180176204538547457685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75253453450803025698305123 112880180176204538547457685)
          ·
            refine ⟨5291258445759587744412079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 112880180176204538547457685 5291258445759587744412079)
            ·
              refine ⟨7936887668639381616618119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5291258445759587744412079 7936887668639381616618119)
              ·
                refine ⟨11905331502959072424927179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7936887668639381616618119 11905331502959072424927179)
                ·
                  refine ⟨17857997254438608637390769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11905331502959072424927179 17857997254438608637390769)
                  ·
                    refine ⟨13393497940828956478043077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17857997254438608637390769 13393497940828956478043077)
                    ·
                      refine ⟨2511280863905429339633077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13393497940828956478043077 2511280863905429339633077)
                      ·
                        rfl

theorem cell23_4890702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 1, 1, 1, 2, 4].length) (baseStart_4890702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4890702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4890702 prefixEnd_4890702 := by exact prefixLift 4890702
  have htrace : WordTrace (prefixWord ++ tailWord_4890702) baseStart_4890702 baseEnd_4890702 := by
    simpa [prefixWord, tailWord_4890702, baseEnd_4890702] using wordTrace_append hprefix tailTrace_4890702
  have hstable : (prefixWord ++ tailWord_4890702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4890702).length < 2 ^ (prefixWord ++ tailWord_4890702).sum := by decide
  have hdescent : baseEnd_4890702 < baseStart_4890702 := by decide
  rcases family_descends (prefixWord ++ tailWord_4890702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4890768 : List Nat := [2, 1, 1, 1, 1, 1, 6, 1, 9]
def baseStart_4890768 : Nat := 118140960795 + 4890768 * 2 ^ 59
def prefixEnd_4890768 : Nat := 4983230072969 + 3 ^ 40 * 4890768 * 2
def baseEnd_4890768 : Nat := 279034972625402897934197

theorem tailTrace_4890768 : CollatzResearch.WordTrace tailWord_4890768 prefixEnd_4890768 279034972625402897934197 := by
  unfold tailWord_4890768
  simp only [CollatzResearch.WordTrace]
  refine ⟨89190481772795143759868479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118920642363726858346491305 89190481772795143759868479)
  ·
    refine ⟨133785722659192715639802719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89190481772795143759868479 133785722659192715639802719)
    ·
      refine ⟨200678583988789073459704079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133785722659192715639802719 200678583988789073459704079)
      ·
        refine ⟨301017875983183610189556119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200678583988789073459704079 301017875983183610189556119)
        ·
          refine ⟨451526813974775415284334179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 301017875983183610189556119 451526813974775415284334179)
          ·
            refine ⟨677290220962163122926501269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 451526813974775415284334179 677290220962163122926501269)
            ·
              refine ⟨31747979107601396387179747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 677290220962163122926501269 31747979107601396387179747)
              ·
                refine ⟨47621968661402094580769621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31747979107601396387179747 47621968661402094580769621)
                ·
                  refine ⟨279034972625402897934197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 47621968661402094580769621 279034972625402897934197)
                  ·
                    rfl

theorem cell23_4890768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 1, 9].length) (baseStart_4890768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4890768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4890768 prefixEnd_4890768 := by exact prefixLift 4890768
  have htrace : WordTrace (prefixWord ++ tailWord_4890768) baseStart_4890768 baseEnd_4890768 := by
    simpa [prefixWord, tailWord_4890768, baseEnd_4890768] using wordTrace_append hprefix tailTrace_4890768
  have hstable : (prefixWord ++ tailWord_4890768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4890768).length < 2 ^ (prefixWord ++ tailWord_4890768).sum := by decide
  have hdescent : baseEnd_4890768 < baseStart_4890768 := by decide
  rcases family_descends (prefixWord ++ tailWord_4890768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4890802 : List Nat := [3, 2, 1, 1, 1, 3, 3, 4, 5]
def baseStart_4890802 : Nat := 118140960795 + 4890802 * 2 ^ 59
def prefixEnd_4890802 : Nat := 4983230072969 + 3 ^ 40 * 4890802 * 2
def baseEnd_4890802 : Nat := 279036912441208772042513

theorem tailTrace_4890802 : CollatzResearch.WordTrace tailWord_4890802 prefixEnd_4890802 279036912441208772042513 := by
  unfold tailWord_4890802
  simp only [CollatzResearch.WordTrace]
  refine ⟨44595550906866777831618665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118921469084978074217649773 44595550906866777831618665)
  ·
    refine ⟨33446663180150083373713999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44595550906866777831618665 33446663180150083373713999)
    ·
      refine ⟨50169994770225125060570999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33446663180150083373713999 50169994770225125060570999)
      ·
        refine ⟨75254992155337687590856499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50169994770225125060570999 75254992155337687590856499)
        ·
          refine ⟨112882488233006531386284749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75254992155337687590856499 112882488233006531386284749)
          ·
            refine ⟨42330933087377449269856781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 112882488233006531386284749 42330933087377449269856781)
            ·
              refine ⟨15874099907766543476196293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42330933087377449269856781 15874099907766543476196293)
              ·
                refine ⟨2976393732706226901786805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15874099907766543476196293 2976393732706226901786805)
                ·
                  refine ⟨279036912441208772042513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2976393732706226901786805 279036912441208772042513)
                  ·
                    rfl

theorem cell23_4890802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 4, 5].length) (baseStart_4890802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4890802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4890802 prefixEnd_4890802 := by exact prefixLift 4890802
  have htrace : WordTrace (prefixWord ++ tailWord_4890802) baseStart_4890802 baseEnd_4890802 := by
    simpa [prefixWord, tailWord_4890802, baseEnd_4890802] using wordTrace_append hprefix tailTrace_4890802
  have hstable : (prefixWord ++ tailWord_4890802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4890802).length < 2 ^ (prefixWord ++ tailWord_4890802).sum := by decide
  have hdescent : baseEnd_4890802 < baseStart_4890802 := by decide
  rcases family_descends (prefixWord ++ tailWord_4890802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4890926 : List Nat := [4, 1, 3, 3, 1, 1, 1, 3, 6]
def baseStart_4890926 : Nat := 118140960795 + 4890926 * 2 ^ 59
def prefixEnd_4890926 : Nat := 4983230072969 + 3 ^ 40 * 4890926 * 2
def baseEnd_4890926 : Nat := 279043987063559607025783

theorem tailTrace_4890926 : CollatzResearch.WordTrace tailWord_4890926 prefixEnd_4890926 279043987063559607025783 := by
  unfold tailWord_4890926
  simp only [CollatzResearch.WordTrace]
  refine ⟨22298340784877235062998579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118924484186011920335992421 22298340784877235062998579)
  ·
    refine ⟨33447511177315852594497869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22298340784877235062998579 33447511177315852594497869)
    ·
      refine ⟨12542816691493444722936701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33447511177315852594497869 12542816691493444722936701)
      ·
        refine ⟨4703556259310041771101263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12542816691493444722936701 4703556259310041771101263)
        ·
          refine ⟨7055334388965062656651895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4703556259310041771101263 7055334388965062656651895)
          ·
            refine ⟨10583001583447593984977843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7055334388965062656651895 10583001583447593984977843)
            ·
              refine ⟨15874502375171390977466765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10583001583447593984977843 15874502375171390977466765)
              ·
                refine ⟨5952938390689271616550037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15874502375171390977466765 5952938390689271616550037)
                ·
                  refine ⟨279043987063559607025783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5952938390689271616550037 279043987063559607025783)
                  ·
                    rfl

theorem cell23_4890926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 3, 6].length) (baseStart_4890926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4890926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4890926 prefixEnd_4890926 := by exact prefixLift 4890926
  have htrace : WordTrace (prefixWord ++ tailWord_4890926) baseStart_4890926 baseEnd_4890926 := by
    simpa [prefixWord, tailWord_4890926, baseEnd_4890926] using wordTrace_append hprefix tailTrace_4890926
  have hstable : (prefixWord ++ tailWord_4890926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4890926).length < 2 ^ (prefixWord ++ tailWord_4890926).sum := by decide
  have hdescent : baseEnd_4890926 < baseStart_4890926 := by decide
  rcases family_descends (prefixWord ++ tailWord_4890926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4890935 : List Nat := [1, 1, 3, 1, 2, 1, 1, 2, 5, 6]
def baseStart_4890935 : Nat := 118140960795 + 4890935 * 2 ^ 59
def prefixEnd_4890935 : Nat := 4983230072969 + 3 ^ 40 * 4890935 * 2
def baseEnd_4890935 : Nat := 837133501632642309339835

theorem tailTrace_4890935 : CollatzResearch.WordTrace tailWord_4890935 prefixEnd_4890935 837133501632642309339835 := by
  unfold tailWord_4890935
  simp only [CollatzResearch.WordTrace]
  refine ⟨178387054535985275041066259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118924703023990183360710839 178387054535985275041066259)
  ·
    refine ⟨267580581803977912561599389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178387054535985275041066259 267580581803977912561599389)
    ·
      refine ⟨100342718176491717210599771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 267580581803977912561599389 100342718176491717210599771)
      ·
        refine ⟨150514077264737575815899657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100342718176491717210599771 150514077264737575815899657)
        ·
          refine ⟨112885557948553181861924743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150514077264737575815899657 112885557948553181861924743)
          ·
            refine ⟨169328336922829772792887115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112885557948553181861924743 169328336922829772792887115)
            ·
              refine ⟨253992505384244659189330673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 169328336922829772792887115 253992505384244659189330673)
              ·
                refine ⟨190494379038183494391998005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 253992505384244659189330673 190494379038183494391998005)
                ·
                  refine ⟨17858848034829702599249813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 190494379038183494391998005 17858848034829702599249813)
                  ·
                    refine ⟨837133501632642309339835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17858848034829702599249813 837133501632642309339835)
                    ·
                      rfl

theorem cell23_4890935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 5, 6].length) (baseStart_4890935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4890935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4890935 prefixEnd_4890935 := by exact prefixLift 4890935
  have htrace : WordTrace (prefixWord ++ tailWord_4890935) baseStart_4890935 baseEnd_4890935 := by
    simpa [prefixWord, tailWord_4890935, baseEnd_4890935] using wordTrace_append hprefix tailTrace_4890935
  have hstable : (prefixWord ++ tailWord_4890935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4890935).length < 2 ^ (prefixWord ++ tailWord_4890935).sum := by decide
  have hdescent : baseEnd_4890935 < baseStart_4890935 := by decide
  rcases family_descends (prefixWord ++ tailWord_4890935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4890952 : List Nat := [2, 1, 3, 1, 1, 2, 2, 1, 6, 4]
def baseStart_4890952 : Nat := 118140960795 + 4890952 * 2 ^ 59
def prefixEnd_4890952 : Nat := 4983230072969 + 3 ^ 40 * 4890952 * 2
def baseEnd_4890952 : Nat := 837136411356351120502309

theorem tailTrace_4890952 : CollatzResearch.WordTrace tailWord_4890952 prefixEnd_4890952 837136411356351120502309 := by
  unfold tailWord_4890952
  simp only [CollatzResearch.WordTrace]
  refine ⟨89193837288461843472217555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118925116384615791296290073 89193837288461843472217555)
  ·
    refine ⟨133790755932692765208326333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89193837288461843472217555 133790755932692765208326333)
    ·
      refine ⟨50171533474759786953122375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133790755932692765208326333 50171533474759786953122375)
      ·
        refine ⟨75257300212139680429683563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50171533474759786953122375 75257300212139680429683563)
        ·
          refine ⟨112885950318209520644525345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75257300212139680429683563 112885950318209520644525345)
          ·
            refine ⟨84664462738657140483394009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112885950318209520644525345 84664462738657140483394009)
            ·
              refine ⟨63498347053992855362545507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84664462738657140483394009 63498347053992855362545507)
              ·
                refine ⟨95247520580989283043818261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63498347053992855362545507 95247520580989283043818261)
                ·
                  refine ⟨4464727527233872642678981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 95247520580989283043818261 4464727527233872642678981)
                  ·
                    refine ⟨837136411356351120502309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4464727527233872642678981 837136411356351120502309)
                    ·
                      rfl

theorem cell23_4890952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 6, 4].length) (baseStart_4890952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4890952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4890952 prefixEnd_4890952 := by exact prefixLift 4890952
  have htrace : WordTrace (prefixWord ++ tailWord_4890952) baseStart_4890952 baseEnd_4890952 := by
    simpa [prefixWord, tailWord_4890952, baseEnd_4890952] using wordTrace_append hprefix tailTrace_4890952
  have hstable : (prefixWord ++ tailWord_4890952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4890952).length < 2 ^ (prefixWord ++ tailWord_4890952).sum := by decide
  have hdescent : baseEnd_4890952 < baseStart_4890952 := by decide
  rcases family_descends (prefixWord ++ tailWord_4890952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4890955 : List Nat := [1, 1, 1, 1, 3, 1, 1, 4, 3, 1, 6]
def baseStart_4890955 : Nat := 118140960795 + 4890955 * 2 ^ 59
def prefixEnd_4890955 : Nat := 4983230072969 + 3 ^ 40 * 4890955 * 2
def baseEnd_4890955 : Nat := 2511410774511016849769413

theorem tailTrace_4890955 : CollatzResearch.WordTrace tailWord_4890955 prefixEnd_4890955 2511410774511016849769413 := by
  unfold tailWord_4890955
  simp only [CollatzResearch.WordTrace]
  refine ⟨178387783995912818456794319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118925189330608545637862879 178387783995912818456794319)
  ·
    refine ⟨267581675993869227685191479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178387783995912818456794319 267581675993869227685191479)
    ·
      refine ⟨401372513990803841527787219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 267581675993869227685191479 401372513990803841527787219)
      ·
        refine ⟨602058770986205762291680829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 401372513990803841527787219 602058770986205762291680829)
        ·
          refine ⟨225772039119827160859380311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 602058770986205762291680829 225772039119827160859380311)
          ·
            refine ⟨338658058679740741289070467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 225772039119827160859380311 338658058679740741289070467)
            ·
              refine ⟨507987088019611111933605701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 338658058679740741289070467 507987088019611111933605701)
              ·
                refine ⟨95247579003677083487551069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 507987088019611111933605701 95247579003677083487551069)
                ·
                  refine ⟨35717842126378906307831651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 95247579003677083487551069 35717842126378906307831651)
                  ·
                    refine ⟨53576763189568359461747477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35717842126378906307831651 53576763189568359461747477)
                    ·
                      refine ⟨2511410774511016849769413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53576763189568359461747477 2511410774511016849769413)
                      ·
                        rfl

theorem cell23_4890955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 3, 1, 6].length) (baseStart_4890955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4890955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4890955 prefixEnd_4890955 := by exact prefixLift 4890955
  have htrace : WordTrace (prefixWord ++ tailWord_4890955) baseStart_4890955 baseEnd_4890955 := by
    simpa [prefixWord, tailWord_4890955, baseEnd_4890955] using wordTrace_append hprefix tailTrace_4890955
  have hstable : (prefixWord ++ tailWord_4890955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4890955).length < 2 ^ (prefixWord ++ tailWord_4890955).sum := by decide
  have hdescent : baseEnd_4890955 < baseStart_4890955 := by decide
  rcases family_descends (prefixWord ++ tailWord_4890955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4890959 : List Nat := [1, 1, 2, 1, 1, 2, 1, 3, 7, 2, 2]
def baseStart_4890959 : Nat := 118140960795 + 4890959 * 2 ^ 59
def prefixEnd_4890959 : Nat := 4983230072969 + 3 ^ 40 * 4890959 * 2
def baseEnd_4890959 : Nat := 2511412828433634834119395

theorem tailTrace_4890959 : CollatzResearch.WordTrace tailWord_4890959 prefixEnd_4890959 2511412828433634834119395 := by
  unfold tailWord_4890959
  simp only [CollatzResearch.WordTrace]
  refine ⟨178387929887898327139939931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118925286591932218093293287 178387929887898327139939931)
  ·
    refine ⟨267581894831847490709909897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178387929887898327139939931 267581894831847490709909897)
    ·
      refine ⟨200686421123885618032432423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 267581894831847490709909897 200686421123885618032432423)
      ·
        refine ⟨301029631685828427048648635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200686421123885618032432423 301029631685828427048648635)
        ·
          refine ⟨451544447528742640572972953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 301029631685828427048648635 451544447528742640572972953)
          ·
            refine ⟨338658335646556980429729715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 451544447528742640572972953 338658335646556980429729715)
            ·
              refine ⟨507987503469835470644594573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 338658335646556980429729715 507987503469835470644594573)
              ·
                refine ⟨190495313801188301491722965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 507987503469835470644594573 190495313801188301491722965)
                ·
                  refine ⟨4464733917215350816212257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 190495313801188301491722965 4464733917215350816212257)
                  ·
                    refine ⟨3348550437911513112159193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4464733917215350816212257 3348550437911513112159193)
                    ·
                      refine ⟨2511412828433634834119395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3348550437911513112159193 2511412828433634834119395)
                      ·
                        rfl

theorem cell23_4890959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 7, 2, 2].length) (baseStart_4890959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4890959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4890959 prefixEnd_4890959 := by exact prefixLift 4890959
  have htrace : WordTrace (prefixWord ++ tailWord_4890959) baseStart_4890959 baseEnd_4890959 := by
    simpa [prefixWord, tailWord_4890959, baseEnd_4890959] using wordTrace_append hprefix tailTrace_4890959
  have hstable : (prefixWord ++ tailWord_4890959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4890959).length < 2 ^ (prefixWord ++ tailWord_4890959).sum := by decide
  have hdescent : baseEnd_4890959 < baseStart_4890959 := by decide
  rcases family_descends (prefixWord ++ tailWord_4890959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4890965 : List Nat := [1, 3, 2, 2, 15]
def baseStart_4890965 : Nat := 118140960795 + 4890965 * 2 ^ 59
def prefixEnd_4890965 : Nat := 4983230072969 + 3 ^ 40 * 4890965 * 2
def baseEnd_4890965 : Nat := 3445014964770317984423

theorem tailTrace_4890965 : CollatzResearch.WordTrace tailWord_4890965 prefixEnd_4890965 3445014964770317984423 := by
  unfold tailWord_4890965
  simp only [CollatzResearch.WordTrace]
  refine ⟨178388148725876590164658349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118925432483917726776438899 178388148725876590164658349)
  ·
    refine ⟨66895555772203721311746881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 178388148725876590164658349 66895555772203721311746881)
    ·
      refine ⟨50171666829152790983810161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66895555772203721311746881 50171666829152790983810161)
      ·
        refine ⟨37628750121864593237857621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50171666829152790983810161 37628750121864593237857621)
        ·
          refine ⟨3445014964770317984423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 15 37628750121864593237857621 3445014964770317984423)
          ·
            rfl

theorem cell23_4890965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 15].length) (baseStart_4890965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4890965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4890965 prefixEnd_4890965 := by exact prefixLift 4890965
  have htrace : WordTrace (prefixWord ++ tailWord_4890965) baseStart_4890965 baseEnd_4890965 := by
    simpa [prefixWord, tailWord_4890965, baseEnd_4890965] using wordTrace_append hprefix tailTrace_4890965
  have hstable : (prefixWord ++ tailWord_4890965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4890965).length < 2 ^ (prefixWord ++ tailWord_4890965).sum := by decide
  have hdescent : baseEnd_4890965 < baseStart_4890965 := by decide
  rcases family_descends (prefixWord ++ tailWord_4890965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4890986 : List Nat := [3, 1, 3, 3, 1, 1, 2, 3, 2, 4]
def baseStart_4890986 : Nat := 118140960795 + 4890986 * 2 ^ 59
def prefixEnd_4890986 : Nat := 4983230072969 + 3 ^ 40 * 4890986 * 2
def baseEnd_4890986 : Nat := 837142230803768742827257

theorem tailTrace_4890986 : CollatzResearch.WordTrace tailWord_4890986 prefixEnd_4890986 837142230803768742827257 := by
  unfold tailWord_4890986
  simp only [CollatzResearch.WordTrace]
  refine ⟨44597228664700127687793203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118925943105867007167448541 44597228664700127687793203)
  ·
    refine ⟨66895842997050191531689805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44597228664700127687793203 66895842997050191531689805)
    ·
      refine ⟨25085941123893821824383677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66895842997050191531689805 25085941123893821824383677)
      ·
        refine ⟨9407227921460183184143879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25085941123893821824383677 9407227921460183184143879)
        ·
          refine ⟨14110841882190274776215819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9407227921460183184143879 14110841882190274776215819)
          ·
            refine ⟨21166262823285412164323729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14110841882190274776215819 21166262823285412164323729)
            ·
              refine ⟨15874697117464059123242797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21166262823285412164323729 15874697117464059123242797)
              ·
                refine ⟨5953011419049022171216049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15874697117464059123242797 5953011419049022171216049)
                ·
                  refine ⟨4464758564286766628412037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5953011419049022171216049 4464758564286766628412037)
                  ·
                    refine ⟨837142230803768742827257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4464758564286766628412037 837142230803768742827257)
                    ·
                      rfl

theorem cell23_4890986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 3, 2, 4].length) (baseStart_4890986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4890986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4890986 prefixEnd_4890986 := by exact prefixLift 4890986
  have htrace : WordTrace (prefixWord ++ tailWord_4890986) baseStart_4890986 baseEnd_4890986 := by
    simpa [prefixWord, tailWord_4890986, baseEnd_4890986] using wordTrace_append hprefix tailTrace_4890986
  have hstable : (prefixWord ++ tailWord_4890986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4890986).length < 2 ^ (prefixWord ++ tailWord_4890986).sum := by decide
  have hdescent : baseEnd_4890986 < baseStart_4890986 := by decide
  rcases family_descends (prefixWord ++ tailWord_4890986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4890989 : List Nat := [1, 5, 1, 1, 1, 2, 4, 1, 1, 2, 4]
def baseStart_4890989 : Nat := 118140960795 + 4890989 * 2 ^ 59
def prefixEnd_4890989 : Nat := 4983230072969 + 3 ^ 40 * 4890989 * 2
def baseEnd_4890989 : Nat := 2511428232853269716744257

theorem tailTrace_4890989 : CollatzResearch.WordTrace tailWord_4890989 prefixEnd_4890989 2511428232853269716744257 := by
  unfold tailWord_4890989
  simp only [CollatzResearch.WordTrace]
  refine ⟨178389024077789642263532021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118926016051859761509021347 178389024077789642263532021)
  ·
    refine ⟨16723971007292778962206127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 178389024077789642263532021 16723971007292778962206127)
    ·
      refine ⟨25085956510939168443309191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16723971007292778962206127 25085956510939168443309191)
      ·
        refine ⟨37628934766408752664963787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25085956510939168443309191 37628934766408752664963787)
        ·
          refine ⟨56443402149613128997445681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37628934766408752664963787 56443402149613128997445681)
          ·
            refine ⟨42332551612209846748084261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56443402149613128997445681 42332551612209846748084261)
            ·
              refine ⟨7937353427289346265265799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42332551612209846748084261 7937353427289346265265799)
              ·
                refine ⟨11906030140934019397898699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7937353427289346265265799 11906030140934019397898699)
                ·
                  refine ⟨17859045211401029096848049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11906030140934019397898699 17859045211401029096848049)
                  ·
                    refine ⟨13394283908550771822636037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17859045211401029096848049 13394283908550771822636037)
                    ·
                      refine ⟨2511428232853269716744257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13394283908550771822636037 2511428232853269716744257)
                      ·
                        rfl

theorem cell23_4890989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4, 1, 1, 2, 4].length) (baseStart_4890989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4890989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4890989 prefixEnd_4890989 := by exact prefixLift 4890989
  have htrace : WordTrace (prefixWord ++ tailWord_4890989) baseStart_4890989 baseEnd_4890989 := by
    simpa [prefixWord, tailWord_4890989, baseEnd_4890989] using wordTrace_append hprefix tailTrace_4890989
  have hstable : (prefixWord ++ tailWord_4890989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4890989).length < 2 ^ (prefixWord ++ tailWord_4890989).sum := by decide
  have hdescent : baseEnd_4890989 < baseStart_4890989 := by decide
  rcases family_descends (prefixWord ++ tailWord_4890989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4891030 : List Nat := [5, 3, 1, 2, 1, 1, 1, 2, 1, 1, 5]
def baseStart_4891030 : Nat := 118140960795 + 4891030 * 2 ^ 59
def prefixEnd_4891030 : Nat := 4983230072969 + 3 ^ 40 * 4891030 * 2
def baseEnd_4891030 : Nat := 2511449285560104056331569

theorem tailTrace_4891030 : CollatzResearch.WordTrace tailWord_4891030 prefixEnd_4891030 2511449285560104056331569 := by
  unfold tailWord_4891030
  simp only [CollatzResearch.WordTrace]
  refine ⟨11149407466915069141610909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 118927012980427404177183029 11149407466915069141610909)
  ·
    refine ⟨4181027800093150928104091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11149407466915069141610909 4181027800093150928104091)
    ·
      refine ⟨6271541700139726392156137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4181027800093150928104091 6271541700139726392156137)
      ·
        refine ⟨4703656275104794794117103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6271541700139726392156137 4703656275104794794117103)
        ·
          refine ⟨7055484412657192191175655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4703656275104794794117103 7055484412657192191175655)
          ·
            refine ⟨10583226618985788286763483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7055484412657192191175655 10583226618985788286763483)
            ·
              refine ⟨15874839928478682430145225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10583226618985788286763483 15874839928478682430145225)
              ·
                refine ⟨11906129946359011822608919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15874839928478682430145225 11906129946359011822608919)
                ·
                  refine ⟨17859194919538517733913379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11906129946359011822608919 17859194919538517733913379)
                  ·
                    refine ⟨26788792379307776600870069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17859194919538517733913379 26788792379307776600870069)
                    ·
                      refine ⟨2511449285560104056331569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26788792379307776600870069 2511449285560104056331569)
                      ·
                        rfl

theorem cell23_4891030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_4891030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4891030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4891030 prefixEnd_4891030 := by exact prefixLift 4891030
  have htrace : WordTrace (prefixWord ++ tailWord_4891030) baseStart_4891030 baseEnd_4891030 := by
    simpa [prefixWord, tailWord_4891030, baseEnd_4891030] using wordTrace_append hprefix tailTrace_4891030
  have hstable : (prefixWord ++ tailWord_4891030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4891030).length < 2 ^ (prefixWord ++ tailWord_4891030).sum := by decide
  have hdescent : baseEnd_4891030 < baseStart_4891030 := by decide
  rcases family_descends (prefixWord ++ tailWord_4891030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4891043 : List Nat := [1, 1, 1, 4, 1, 5, 3, 1, 2, 1, 3]
def baseStart_4891043 : Nat := 118140960795 + 4891043 * 2 ^ 59
def prefixEnd_4891043 : Nat := 4983230072969 + 3 ^ 40 * 4891043 * 2
def baseEnd_4891043 : Nat := 2511455960808612505469009

theorem tailTrace_4891043 : CollatzResearch.WordTrace tailWord_4891043 prefixEnd_4891043 2511455960808612505469009 := by
  unfold tailWord_4891043
  simp only [CollatzResearch.WordTrace]
  refine ⟨178390993619594009485997783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118927329079729339657331855 178390993619594009485997783)
  ·
    refine ⟨267586490429391014228996675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178390993619594009485997783 267586490429391014228996675)
    ·
      refine ⟨401379735644086521343495013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 267586490429391014228996675 401379735644086521343495013)
      ·
        refine ⟨75258700433266222751905315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 401379735644086521343495013 75258700433266222751905315)
        ·
          refine ⟨112888050649899334127857973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75258700433266222751905315 112888050649899334127857973)
          ·
            refine ⟨10583254748428062574486685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 112888050649899334127857973 10583254748428062574486685)
            ·
              refine ⟨3968720530660523465432507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10583254748428062574486685 3968720530660523465432507)
              ·
                refine ⟨5953080795990785198148761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3968720530660523465432507 5953080795990785198148761)
                ·
                  refine ⟨4464810596993088898611571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5953080795990785198148761 4464810596993088898611571)
                  ·
                    refine ⟨6697215895489633347917357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4464810596993088898611571 6697215895489633347917357)
                    ·
                      refine ⟨2511455960808612505469009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6697215895489633347917357 2511455960808612505469009)
                      ·
                        rfl

theorem cell23_4891043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 3, 1, 2, 1, 3].length) (baseStart_4891043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4891043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4891043 prefixEnd_4891043 := by exact prefixLift 4891043
  have htrace : WordTrace (prefixWord ++ tailWord_4891043) baseStart_4891043 baseEnd_4891043 := by
    simpa [prefixWord, tailWord_4891043, baseEnd_4891043] using wordTrace_append hprefix tailTrace_4891043
  have hstable : (prefixWord ++ tailWord_4891043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4891043).length < 2 ^ (prefixWord ++ tailWord_4891043).sum := by decide
  have hdescent : baseEnd_4891043 < baseStart_4891043 := by decide
  rcases family_descends (prefixWord ++ tailWord_4891043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4891050 : List Nat := [3, 1, 6, 1, 1, 2, 2, 7]
def baseStart_4891050 : Nat := 118140960795 + 4891050 * 2 ^ 59
def prefixEnd_4891050 : Nat := 4983230072969 + 3 ^ 40 * 4891050 * 2
def baseEnd_4891050 : Nat := 93017020561970147336351

theorem tailTrace_4891050 : CollatzResearch.WordTrace tailWord_4891050 prefixEnd_4891050 93017020561970147336351 := by
  unfold tailWord_4891050
  simp only [CollatzResearch.WordTrace]
  refine ⟨44597812232642162420375651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118927499287045766454335069 44597812232642162420375651)
  ·
    refine ⟨66896718348963243630563477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44597812232642162420375651 66896718348963243630563477)
    ·
      refine ⟨3135783672607652045182663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 66896718348963243630563477 3135783672607652045182663)
      ·
        refine ⟨4703675508911478067773995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3135783672607652045182663 4703675508911478067773995)
        ·
          refine ⟨7055513263367217101660993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4703675508911478067773995 7055513263367217101660993)
          ·
            refine ⟨5291634947525412826245745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7055513263367217101660993 5291634947525412826245745)
            ·
              refine ⟨3968726210644059619684309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5291634947525412826245745 3968726210644059619684309)
              ·
                refine ⟨93017020561970147336351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3968726210644059619684309 93017020561970147336351)
                ·
                  rfl

theorem cell23_4891050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 2, 7].length) (baseStart_4891050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4891050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4891050 prefixEnd_4891050 := by exact prefixLift 4891050
  have htrace : WordTrace (prefixWord ++ tailWord_4891050) baseStart_4891050 baseEnd_4891050 := by
    simpa [prefixWord, tailWord_4891050, baseEnd_4891050] using wordTrace_append hprefix tailTrace_4891050
  have hstable : (prefixWord ++ tailWord_4891050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4891050).length < 2 ^ (prefixWord ++ tailWord_4891050).sum := by decide
  have hdescent : baseEnd_4891050 < baseStart_4891050 := by decide
  rcases family_descends (prefixWord ++ tailWord_4891050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4891052 : List Nat := [2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 5]
def baseStart_4891052 : Nat := 118140960795 + 4891052 * 2 ^ 59
def prefixEnd_4891052 : Nat := 4983230072969 + 3 ^ 40 * 4891052 * 2
def baseEnd_4891052 : Nat := 2511460582134502970256467

theorem tailTrace_4891052 : CollatzResearch.WordTrace tailWord_4891052 prefixEnd_4891052 2511460582134502970256467 := by
  unfold tailWord_4891052
  simp only [CollatzResearch.WordTrace]
  refine ⟨89195660938280702011537705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118927547917707602682050273 89195660938280702011537705)
  ·
    refine ⟨66896745703710526508653279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89195660938280702011537705 66896745703710526508653279)
    ·
      refine ⟨100345118555565789762979919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66896745703710526508653279 100345118555565789762979919)
      ·
        refine ⟨150517677833348684644469879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100345118555565789762979919 150517677833348684644469879)
        ·
          refine ⟨225776516750023026966704819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150517677833348684644469879 225776516750023026966704819)
          ·
            refine ⟨338664775125034540450057229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 225776516750023026966704819 338664775125034540450057229)
            ·
              refine ⟨126999290671887952668771461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 338664775125034540450057229 126999290671887952668771461)
              ·
                refine ⟨23812367000978991125394649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 126999290671887952668771461 23812367000978991125394649)
                ·
                  refine ⟨17859275250734243344045987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23812367000978991125394649 17859275250734243344045987)
                  ·
                    refine ⟨26788912876101365016068981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17859275250734243344045987 26788912876101365016068981)
                    ·
                      refine ⟨2511460582134502970256467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26788912876101365016068981 2511460582134502970256467)
                      ·
                        rfl

theorem cell23_4891052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 5].length) (baseStart_4891052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4891052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4891052 prefixEnd_4891052 := by exact prefixLift 4891052
  have htrace : WordTrace (prefixWord ++ tailWord_4891052) baseStart_4891052 baseEnd_4891052 := by
    simpa [prefixWord, tailWord_4891052, baseEnd_4891052] using wordTrace_append hprefix tailTrace_4891052
  have hstable : (prefixWord ++ tailWord_4891052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4891052).length < 2 ^ (prefixWord ++ tailWord_4891052).sum := by decide
  have hdescent : baseEnd_4891052 < baseStart_4891052 := by decide
  rcases family_descends (prefixWord ++ tailWord_4891052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4891069 : List Nat := [1, 4, 1, 2, 2, 3, 1, 1, 2, 1, 5]
def baseStart_4891069 : Nat := 118140960795 + 4891069 * 2 ^ 59
def prefixEnd_4891069 : Nat := 4983230072969 + 3 ^ 40 * 4891069 * 2
def baseEnd_4891069 : Nat := 2511469311305629403743889

theorem tailTrace_4891069 : CollatzResearch.WordTrace tailWord_4891069 prefixEnd_4891069 2511469311305629403743889 := by
  unfold tailWord_4891069
  simp only [CollatzResearch.WordTrace]
  refine ⟨178391941917499815926444261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118927961278333210617629507 178391941917499815926444261)
  ·
    refine ⟨33448489109531215486208299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 178391941917499815926444261 33448489109531215486208299)
    ·
      refine ⟨50172733664296823229312449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33448489109531215486208299 50172733664296823229312449)
      ·
        refine ⟨37629550248222617421984337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50172733664296823229312449 37629550248222617421984337)
        ·
          refine ⟨28222162686166963066488253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37629550248222617421984337 28222162686166963066488253)
          ·
            refine ⟨10583311007312611149933095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28222162686166963066488253 10583311007312611149933095)
            ·
              refine ⟨15874966510968916724899643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10583311007312611149933095 15874966510968916724899643)
              ·
                refine ⟨23812449766453375087349465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15874966510968916724899643 23812449766453375087349465)
                ·
                  refine ⟨17859337324840031315512099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23812449766453375087349465 17859337324840031315512099)
                  ·
                    refine ⟨26789005987260046973268149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17859337324840031315512099 26789005987260046973268149)
                    ·
                      refine ⟨2511469311305629403743889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26789005987260046973268149 2511469311305629403743889)
                      ·
                        rfl

theorem cell23_4891069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 1, 2, 1, 5].length) (baseStart_4891069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4891069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4891069 prefixEnd_4891069 := by exact prefixLift 4891069
  have htrace : WordTrace (prefixWord ++ tailWord_4891069) baseStart_4891069 baseEnd_4891069 := by
    simpa [prefixWord, tailWord_4891069, baseEnd_4891069] using wordTrace_append hprefix tailTrace_4891069
  have hstable : (prefixWord ++ tailWord_4891069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4891069).length < 2 ^ (prefixWord ++ tailWord_4891069).sum := by decide
  have hdescent : baseEnd_4891069 < baseStart_4891069 := by decide
  rcases family_descends (prefixWord ++ tailWord_4891069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4891082 : List Nat := [3, 1, 2, 1, 2, 2, 1, 1, 1, 2, 7]
def baseStart_4891082 : Nat := 118140960795 + 4891082 * 2 ^ 59
def prefixEnd_4891082 : Nat := 4983230072969 + 3 ^ 40 * 4891082 * 2
def baseEnd_4891082 : Nat := 2511475986554137852881329

theorem tailTrace_4891082 : CollatzResearch.WordTrace tailWord_4891082 prefixEnd_4891082 2511475986554137852881329 := by
  unfold tailWord_4891082
  simp only [CollatzResearch.WordTrace]
  refine ⟨44598104016613179786666875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118928277377635146097778333 44598104016613179786666875)
  ·
    refine ⟨66897156024919769680000313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44598104016613179786666875 66897156024919769680000313)
    ·
      refine ⟨50172867018689827260000235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66897156024919769680000313 50172867018689827260000235)
      ·
        refine ⟨75259300528034740890000353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50172867018689827260000235 75259300528034740890000353)
        ·
          refine ⟨56444475396026055667500265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75259300528034740890000353 56444475396026055667500265)
          ·
            refine ⟨42333356547019541750625199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56444475396026055667500265 42333356547019541750625199)
            ·
              refine ⟨63500034820529312625937799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42333356547019541750625199 63500034820529312625937799)
              ·
                refine ⟨95250052230793968938906699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63500034820529312625937799 95250052230793968938906699)
                ·
                  refine ⟨142875078346190953408360049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 95250052230793968938906699 142875078346190953408360049)
                  ·
                    refine ⟨107156308759643215056270037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 142875078346190953408360049 107156308759643215056270037)
                    ·
                      refine ⟨2511475986554137852881329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 107156308759643215056270037 2511475986554137852881329)
                      ·
                        rfl

theorem cell23_4891082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 1, 2, 7].length) (baseStart_4891082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4891082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4891082 prefixEnd_4891082 := by exact prefixLift 4891082
  have htrace : WordTrace (prefixWord ++ tailWord_4891082) baseStart_4891082 baseEnd_4891082 := by
    simpa [prefixWord, tailWord_4891082, baseEnd_4891082] using wordTrace_append hprefix tailTrace_4891082
  have hstable : (prefixWord ++ tailWord_4891082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4891082).length < 2 ^ (prefixWord ++ tailWord_4891082).sum := by decide
  have hdescent : baseEnd_4891082 < baseStart_4891082 := by decide
  rcases family_descends (prefixWord ++ tailWord_4891082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4891089 : List Nat := [1, 2, 2, 1, 2, 1, 1, 8, 5]
def baseStart_4891089 : Nat := 118140960795 + 4891089 * 2 ^ 59
def prefixEnd_4891089 : Nat := 4983230072969 + 3 ^ 40 * 4891089 * 2
def baseEnd_4891089 : Nat := 279053286768746591721533

theorem tailTrace_4891089 : CollatzResearch.WordTrace tailWord_4891089 prefixEnd_4891089 279053286768746591721533 := by
  unfold tailWord_4891089
  simp only [CollatzResearch.WordTrace]
  refine ⟨178392671377427359342172321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118928447584951572894781547 178392671377427359342172321)
  ·
    refine ⟨133794503533070519506629241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178392671377427359342172321 133794503533070519506629241)
    ·
      refine ⟨100345877649802889629971931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133794503533070519506629241 100345877649802889629971931)
      ·
        refine ⟨150518816474704334444957897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100345877649802889629971931 150518816474704334444957897)
        ·
          refine ⟨112889112356028250833718423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150518816474704334444957897 112889112356028250833718423)
          ·
            refine ⟨169333668534042376250577635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112889112356028250833718423 169333668534042376250577635)
            ·
              refine ⟨254000502801063564375866453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 169333668534042376250577635 254000502801063564375866453)
              ·
                refine ⟨2976568392199963645029685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 254000502801063564375866453 2976568392199963645029685)
                ·
                  refine ⟨279053286768746591721533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2976568392199963645029685 279053286768746591721533)
                  ·
                    rfl

theorem cell23_4891089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 8, 5].length) (baseStart_4891089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4891089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4891089 prefixEnd_4891089 := by exact prefixLift 4891089
  have htrace : WordTrace (prefixWord ++ tailWord_4891089) baseStart_4891089 baseEnd_4891089 := by
    simpa [prefixWord, tailWord_4891089, baseEnd_4891089] using wordTrace_append hprefix tailTrace_4891089
  have hstable : (prefixWord ++ tailWord_4891089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4891089).length < 2 ^ (prefixWord ++ tailWord_4891089).sum := by decide
  have hdescent : baseEnd_4891089 < baseStart_4891089 := by decide
  rcases family_descends (prefixWord ++ tailWord_4891089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4891139 : List Nat := [1, 1, 1, 3, 2, 1, 3, 4, 2, 1, 4]
def baseStart_4891139 : Nat := 118140960795 + 4891139 * 2 ^ 59
def prefixEnd_4891139 : Nat := 4983230072969 + 3 ^ 40 * 4891139 * 2
def baseEnd_4891139 : Nat := 2511505254951444129868567

theorem tailTrace_4891139 : CollatzResearch.WordTrace tailWord_4891139 prefixEnd_4891139 2511505254951444129868567 := by
  unfold tailWord_4891139
  simp only [CollatzResearch.WordTrace]
  refine ⟨178394495027246217881492471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118929663351497478587661647 178394495027246217881492471)
  ·
    refine ⟨267591742540869326822238707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178394495027246217881492471 267591742540869326822238707)
    ·
      refine ⟨401387613811303990233358061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 267591742540869326822238707 401387613811303990233358061)
      ·
        refine ⟨150520355179238996337509273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 401387613811303990233358061 150520355179238996337509273)
        ·
          refine ⟨112890266384429247253131955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150520355179238996337509273 112890266384429247253131955)
          ·
            refine ⟨169335399576643870879697933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112890266384429247253131955 169335399576643870879697933)
            ·
              refine ⟨63500774841241451579886725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 169335399576643870879697933 63500774841241451579886725)
              ·
                refine ⟨11906395282732772171228761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63500774841241451579886725 11906395282732772171228761)
                ·
                  refine ⟨8929796462049579128421571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11906395282732772171228761 8929796462049579128421571)
                  ·
                    refine ⟨13394694693074368692632357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8929796462049579128421571 13394694693074368692632357)
                    ·
                      refine ⟨2511505254951444129868567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13394694693074368692632357 2511505254951444129868567)
                      ·
                        rfl

theorem cell23_4891139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 4, 2, 1, 4].length) (baseStart_4891139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4891139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4891139 prefixEnd_4891139 := by exact prefixLift 4891139
  have htrace : WordTrace (prefixWord ++ tailWord_4891139) baseStart_4891139 baseEnd_4891139 := by
    simpa [prefixWord, tailWord_4891139, baseEnd_4891139] using wordTrace_append hprefix tailTrace_4891139
  have hstable : (prefixWord ++ tailWord_4891139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4891139).length < 2 ^ (prefixWord ++ tailWord_4891139).sum := by decide
  have hdescent : baseEnd_4891139 < baseStart_4891139 := by decide
  rcases family_descends (prefixWord ++ tailWord_4891139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4891140 : List Nat := [2, 3, 2, 3, 1, 3, 2, 2, 5]
def baseStart_4891140 : Nat := 118140960795 + 4891140 * 2 ^ 59
def prefixEnd_4891140 : Nat := 4983230072969 + 3 ^ 40 * 4891140 * 2
def baseEnd_4891140 : Nat := 279056196492455402884007

theorem tailTrace_4891140 : CollatzResearch.WordTrace tailWord_4891140 prefixEnd_4891140 279056196492455402884007 := by
  unfold tailWord_4891140
  simp only [CollatzResearch.WordTrace]
  refine ⟨89197265750121297526139437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118929687666828396701519249 89197265750121297526139437)
  ·
    refine ⟨33448974656295486572302289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89197265750121297526139437 33448974656295486572302289)
    ·
      refine ⟨25086730992221614929226717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33448974656295486572302289 25086730992221614929226717)
      ·
        refine ⟨9407524122083105598460019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25086730992221614929226717 9407524122083105598460019)
        ·
          refine ⟨14111286183124658397690029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9407524122083105598460019 14111286183124658397690029)
          ·
            refine ⟨5291732318671746899133761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14111286183124658397690029 5291732318671746899133761)
            ·
              refine ⟨3968799239003810174350321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5291732318671746899133761 3968799239003810174350321)
              ·
                refine ⟨2976599429252857630762741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3968799239003810174350321 2976599429252857630762741)
                ·
                  refine ⟨279056196492455402884007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2976599429252857630762741 279056196492455402884007)
                  ·
                    rfl

theorem cell23_4891140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 2, 2, 5].length) (baseStart_4891140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4891140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4891140 prefixEnd_4891140 := by exact prefixLift 4891140
  have htrace : WordTrace (prefixWord ++ tailWord_4891140) baseStart_4891140 baseEnd_4891140 := by
    simpa [prefixWord, tailWord_4891140, baseEnd_4891140] using wordTrace_append hprefix tailTrace_4891140
  have hstable : (prefixWord ++ tailWord_4891140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4891140).length < 2 ^ (prefixWord ++ tailWord_4891140).sum := by decide
  have hdescent : baseEnd_4891140 < baseStart_4891140 := by decide
  rcases family_descends (prefixWord ++ tailWord_4891140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4891196 : List Nat := [2, 2, 2, 2, 3, 1, 3, 2, 6]
def baseStart_4891196 : Nat := 118140960795 + 4891196 * 2 ^ 59
def prefixEnd_4891196 : Nat := 4983230072969 + 3 ^ 40 * 4891196 * 2
def baseEnd_4891196 : Nat := 279059391483194489650645

theorem tailTrace_4891196 : CollatzResearch.WordTrace tailWord_4891196 prefixEnd_4891196 279059391483194489650645 := by
  unfold tailWord_4891196
  simp only [CollatzResearch.WordTrace]
  refine ⟨89198286994019858308158721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118931049325359811077544961 89198286994019858308158721)
  ·
    refine ⟨66898715245514893731119041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89198286994019858308158721 66898715245514893731119041)
    ·
      refine ⟨50174036434136170298339281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66898715245514893731119041 50174036434136170298339281)
      ·
        refine ⟨37630527325602127723754461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50174036434136170298339281 37630527325602127723754461)
        ·
          refine ⟨14111447747100797896407923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37630527325602127723754461 14111447747100797896407923)
          ·
            refine ⟨21167171620651196844611885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14111447747100797896407923 21167171620651196844611885)
            ·
              refine ⟨7937689357744198816729457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21167171620651196844611885 7937689357744198816729457)
              ·
                refine ⟨5953267018308149112547093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7937689357744198816729457 5953267018308149112547093)
                ·
                  refine ⟨279059391483194489650645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5953267018308149112547093 279059391483194489650645)
                  ·
                    rfl

theorem cell23_4891196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 3, 2, 6].length) (baseStart_4891196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4891196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4891196 prefixEnd_4891196 := by exact prefixLift 4891196
  have htrace : WordTrace (prefixWord ++ tailWord_4891196) baseStart_4891196 baseEnd_4891196 := by
    simpa [prefixWord, tailWord_4891196, baseEnd_4891196] using wordTrace_append hprefix tailTrace_4891196
  have hstable : (prefixWord ++ tailWord_4891196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4891196).length < 2 ^ (prefixWord ++ tailWord_4891196).sum := by decide
  have hdescent : baseEnd_4891196 < baseStart_4891196 := by decide
  rcases family_descends (prefixWord ++ tailWord_4891196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4891216 : List Nat := [2, 1, 1, 1, 1, 3, 2, 1, 6, 3, 2]
def baseStart_4891216 : Nat := 118140960795 + 4891216 * 2 ^ 59
def prefixEnd_4891216 : Nat := 4983230072969 + 3 ^ 40 * 4891216 * 2
def baseEnd_4891216 : Nat := 2511544792961840328605713

theorem tailTrace_4891216 : CollatzResearch.WordTrace tailWord_4891216 prefixEnd_4891216 2511544792961840328605713 := by
  unfold tailWord_4891216
  simp only [CollatzResearch.WordTrace]
  refine ⟨89198651723983630016022751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118931535631978173354697001 89198651723983630016022751)
  ·
    refine ⟨133797977585975445024034127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89198651723983630016022751 133797977585975445024034127)
    ·
      refine ⟨200696966378963167536051191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133797977585975445024034127 200696966378963167536051191)
      ·
        refine ⟨301045449568444751304076787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200696966378963167536051191 301045449568444751304076787)
        ·
          refine ⟨451568174352667126956115181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 301045449568444751304076787 451568174352667126956115181)
          ·
            refine ⟨169338065382250172608543193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 451568174352667126956115181 169338065382250172608543193)
            ·
              refine ⟨127003549036687629456407395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 169338065382250172608543193 127003549036687629456407395)
              ·
                refine ⟨190505323555031444184611093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 127003549036687629456407395 190505323555031444184611093)
                ·
                  refine ⟨8929937041642098946153645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 190505323555031444184611093 8929937041642098946153645)
                  ·
                    refine ⟨3348726390615787104807617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8929937041642098946153645 3348726390615787104807617)
                    ·
                      refine ⟨2511544792961840328605713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3348726390615787104807617 2511544792961840328605713)
                      ·
                        rfl

theorem cell23_4891216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 6, 3, 2].length) (baseStart_4891216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4891216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4891216 prefixEnd_4891216 := by exact prefixLift 4891216
  have htrace : WordTrace (prefixWord ++ tailWord_4891216) baseStart_4891216 baseEnd_4891216 := by
    simpa [prefixWord, tailWord_4891216, baseEnd_4891216] using wordTrace_append hprefix tailTrace_4891216
  have hstable : (prefixWord ++ tailWord_4891216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4891216).length < 2 ^ (prefixWord ++ tailWord_4891216).sum := by decide
  have hdescent : baseEnd_4891216 < baseStart_4891216 := by decide
  rcases family_descends (prefixWord ++ tailWord_4891216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4891234 : List Nat := [3, 3, 2, 3, 1, 2, 1, 3, 1, 4]
def baseStart_4891234 : Nat := 118140960795 + 4891234 * 2 ^ 59
def prefixEnd_4891234 : Nat := 4983230072969 + 3 ^ 40 * 4891234 * 2
def baseEnd_4891234 : Nat := 837184678537873752726877

theorem tailTrace_4891234 : CollatzResearch.WordTrace tailWord_4891234 prefixEnd_4891234 837184678537873752726877 := by
  unfold tailWord_4891234
  simp only [CollatzResearch.WordTrace]
  refine ⟨44599489990475512276550189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118931973307934699404133837 44599489990475512276550189)
  ·
    refine ⟨16724808746428317103706321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44599489990475512276550189 16724808746428317103706321)
    ·
      refine ⟨12543606559821237827779741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16724808746428317103706321 12543606559821237827779741)
      ·
        refine ⟨4703852459932964185417403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12543606559821237827779741 4703852459932964185417403)
        ·
          refine ⟨7055778689899446278126105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4703852459932964185417403 7055778689899446278126105)
          ·
            refine ⟨5291834017424584708594579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7055778689899446278126105 5291834017424584708594579)
            ·
              refine ⟨7937751026136877062891869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5291834017424584708594579 7937751026136877062891869)
              ·
                refine ⟨2976656634801328898584451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7937751026136877062891869 2976656634801328898584451)
                ·
                  refine ⟨4464984952201993347876677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2976656634801328898584451 4464984952201993347876677)
                  ·
                    refine ⟨837184678537873752726877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4464984952201993347876677 837184678537873752726877)
                    ·
                      rfl

theorem cell23_4891234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 1, 3, 1, 4].length) (baseStart_4891234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4891234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4891234 prefixEnd_4891234 := by exact prefixLift 4891234
  have htrace : WordTrace (prefixWord ++ tailWord_4891234) baseStart_4891234 baseEnd_4891234 := by
    simpa [prefixWord, tailWord_4891234, baseEnd_4891234] using wordTrace_append hprefix tailTrace_4891234
  have hstable : (prefixWord ++ tailWord_4891234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4891234).length < 2 ^ (prefixWord ++ tailWord_4891234).sum := by decide
  have hdescent : baseEnd_4891234 < baseStart_4891234 := by decide
  rcases family_descends (prefixWord ++ tailWord_4891234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4891239 : List Nat := [1, 1, 5, 1, 1, 1, 1, 3, 3, 6]
def baseStart_4891239 : Nat := 118140960795 + 4891239 * 2 ^ 59
def prefixEnd_4891239 : Nat := 4983230072969 + 3 ^ 40 * 4891239 * 2
def baseEnd_4891239 : Nat := 837185534338964579539369

theorem tailTrace_4891239 : CollatzResearch.WordTrace tailWord_4891239 prefixEnd_4891239 837185534338964579539369 := by
  unfold tailWord_4891239
  simp only [CollatzResearch.WordTrace]
  refine ⟨178398142326883934960132771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118932094884589289973421847 178398142326883934960132771)
  ·
    refine ⟨267597213490325902440199157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178398142326883934960132771 267597213490325902440199157)
    ·
      refine ⟨25087238764718053353768671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 267597213490325902440199157 25087238764718053353768671)
      ·
        refine ⟨37630858147077080030653007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25087238764718053353768671 37630858147077080030653007)
        ·
          refine ⟨56446287220615620045979511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37630858147077080030653007 56446287220615620045979511)
          ·
            refine ⟨84669430830923430068969267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56446287220615620045979511 84669430830923430068969267)
            ·
              refine ⟨127004146246385145103453901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84669430830923430068969267 127004146246385145103453901)
              ·
                refine ⟨47626554842394429413795213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 127004146246385145103453901 47626554842394429413795213)
                ·
                  refine ⟨17859958065897911030173205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47626554842394429413795213 17859958065897911030173205)
                  ·
                    refine ⟨837185534338964579539369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17859958065897911030173205 837185534338964579539369)
                    ·
                      rfl

theorem cell23_4891239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 3, 3, 6].length) (baseStart_4891239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4891239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4891239 prefixEnd_4891239 := by exact prefixLift 4891239
  have htrace : WordTrace (prefixWord ++ tailWord_4891239) baseStart_4891239 baseEnd_4891239 := by
    simpa [prefixWord, tailWord_4891239, baseEnd_4891239] using wordTrace_append hprefix tailTrace_4891239
  have hstable : (prefixWord ++ tailWord_4891239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4891239).length < 2 ^ (prefixWord ++ tailWord_4891239).sum := by decide
  have hdescent : baseEnd_4891239 < baseStart_4891239 := by decide
  rcases family_descends (prefixWord ++ tailWord_4891239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4891250 : List Nat := [3, 2, 1, 2, 4, 1, 1, 2, 2, 3, 2]
def baseStart_4891250 : Nat := 118140960795 + 4891250 * 2 ^ 59
def prefixEnd_4891250 : Nat := 4983230072969 + 3 ^ 40 * 4891250 * 2
def baseEnd_4891250 : Nat := 2511562251304093195580557

theorem tailTrace_4891250 : CollatzResearch.WordTrace tailWord_4891250 prefixEnd_4891250 2511562251304093195580557 := by
  unfold tailWord_4891250
  simp only [CollatzResearch.WordTrace]
  refine ⟨44599635882461020959695801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118932362353229389225855469 44599635882461020959695801)
  ·
    refine ⟨33449726911845765719771851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44599635882461020959695801 33449726911845765719771851)
    ·
      refine ⟨50174590367768648579657777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33449726911845765719771851 50174590367768648579657777)
      ·
        refine ⟨37630942775826486434743333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50174590367768648579657777 37630942775826486434743333)
        ·
          refine ⟨7055801770467466206514375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37630942775826486434743333 7055801770467466206514375)
          ·
            refine ⟨10583702655701199309771563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7055801770467466206514375 10583702655701199309771563)
            ·
              refine ⟨15875553983551798964657345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10583702655701199309771563 15875553983551798964657345)
              ·
                refine ⟨11906665487663849223493009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15875553983551798964657345 11906665487663849223493009)
                ·
                  refine ⟨8929999115747886917619757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11906665487663849223493009 8929999115747886917619757)
                  ·
                    refine ⟨3348749668405457594107409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8929999115747886917619757 3348749668405457594107409)
                    ·
                      refine ⟨2511562251304093195580557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3348749668405457594107409 2511562251304093195580557)
                      ·
                        rfl

theorem cell23_4891250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 2, 2, 3, 2].length) (baseStart_4891250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4891250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4891250 prefixEnd_4891250 := by exact prefixLift 4891250
  have htrace : WordTrace (prefixWord ++ tailWord_4891250) baseStart_4891250 baseEnd_4891250 := by
    simpa [prefixWord, tailWord_4891250, baseEnd_4891250] using wordTrace_append hprefix tailTrace_4891250
  have hstable : (prefixWord ++ tailWord_4891250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4891250).length < 2 ^ (prefixWord ++ tailWord_4891250).sum := by decide
  have hdescent : baseEnd_4891250 < baseStart_4891250 := by decide
  rcases family_descends (prefixWord ++ tailWord_4891250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4891257 : List Nat := [1, 2, 1, 3, 3, 3, 3, 2, 1, 1, 3]
def baseStart_4891257 : Nat := 118140960795 + 4891257 * 2 ^ 59
def prefixEnd_4891257 : Nat := 4983230072969 + 3 ^ 40 * 4891257 * 2
def baseEnd_4891257 : Nat := 2511565845668674668193025

theorem tailTrace_4891257 : CollatzResearch.WordTrace tailWord_4891257 prefixEnd_4891257 2511565845668674668193025 := by
  unfold tailWord_4891257
  simp only [CollatzResearch.WordTrace]
  refine ⟨178398798840818724034288025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118932532560545816022858683 178398798840818724034288025)
  ·
    refine ⟨133799099130614043025716019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178398798840818724034288025 133799099130614043025716019)
    ·
      refine ⟨200698648695921064538574029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133799099130614043025716019 200698648695921064538574029)
      ·
        refine ⟨75261993260970399201965261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 200698648695921064538574029 75261993260970399201965261)
        ·
          refine ⟨28223247472863899700736973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75261993260970399201965261 28223247472863899700736973)
          ·
            refine ⟨10583717802323962387776365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28223247472863899700736973 10583717802323962387776365)
            ·
              refine ⟨3968894175871485895416137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10583717802323962387776365 3968894175871485895416137)
              ·
                refine ⟨2976670631903614421562103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3968894175871485895416137 2976670631903614421562103)
                ·
                  refine ⟨4465005947855421632343155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2976670631903614421562103 4465005947855421632343155)
                  ·
                    refine ⟨6697508921783132448514733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4465005947855421632343155 6697508921783132448514733)
                    ·
                      refine ⟨2511565845668674668193025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6697508921783132448514733 2511565845668674668193025)
                      ·
                        rfl

theorem cell23_4891257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 3, 2, 1, 1, 3].length) (baseStart_4891257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4891257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4891257 prefixEnd_4891257 := by exact prefixLift 4891257
  have htrace : WordTrace (prefixWord ++ tailWord_4891257) baseStart_4891257 baseEnd_4891257 := by
    simpa [prefixWord, tailWord_4891257, baseEnd_4891257] using wordTrace_append hprefix tailTrace_4891257
  have hstable : (prefixWord ++ tailWord_4891257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4891257).length < 2 ^ (prefixWord ++ tailWord_4891257).sum := by decide
  have hdescent : baseEnd_4891257 < baseStart_4891257 := by decide
  rcases family_descends (prefixWord ++ tailWord_4891257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4891259 : List Nat := [1, 1, 1, 1, 1, 4, 2, 1, 5, 2, 4]
def baseStart_4891259 : Nat := 118140960795 + 4891259 * 2 ^ 59
def prefixEnd_4891259 : Nat := 4983230072969 + 3 ^ 40 * 4891259 * 2
def baseEnd_4891259 : Nat := 2511566872629983660368015

theorem tailTrace_4891259 : CollatzResearch.WordTrace tailWord_4891259 prefixEnd_4891259 2511566872629983660368015 := by
  unfold tailWord_4891259
  simp only [CollatzResearch.WordTrace]
  refine ⟨178398871786811478375860831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118932581191207652250573887 178398871786811478375860831)
  ·
    refine ⟨267598307680217217563791247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178398871786811478375860831 267598307680217217563791247)
    ·
      refine ⟨401397461520325826345686871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 267598307680217217563791247 401397461520325826345686871)
      ·
        refine ⟨602096192280488739518530307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 401397461520325826345686871 602096192280488739518530307)
        ·
          refine ⟨903144288420733109277795461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 602096192280488739518530307 903144288420733109277795461)
          ·
            refine ⟨169339554078887457989586649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 903144288420733109277795461 169339554078887457989586649)
            ·
              refine ⟨127004665559165593492189987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 169339554078887457989586649 127004665559165593492189987)
              ·
                refine ⟨190506998338748390238284981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 127004665559165593492189987 190506998338748390238284981)
                ·
                  refine ⟨17860031094257661584839217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 190506998338748390238284981 17860031094257661584839217)
                  ·
                    refine ⟨13395023320693246188629413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17860031094257661584839217 13395023320693246188629413)
                    ·
                      refine ⟨2511566872629983660368015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13395023320693246188629413 2511566872629983660368015)
                      ·
                        rfl

theorem cell23_4891259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 5, 2, 4].length) (baseStart_4891259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4891259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4891259 prefixEnd_4891259 := by exact prefixLift 4891259
  have htrace : WordTrace (prefixWord ++ tailWord_4891259) baseStart_4891259 baseEnd_4891259 := by
    simpa [prefixWord, tailWord_4891259, baseEnd_4891259] using wordTrace_append hprefix tailTrace_4891259
  have hstable : (prefixWord ++ tailWord_4891259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4891259).length < 2 ^ (prefixWord ++ tailWord_4891259).sum := by decide
  have hdescent : baseEnd_4891259 < baseStart_4891259 := by decide
  rcases family_descends (prefixWord ++ tailWord_4891259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4891263 : List Nat := [1, 1, 2, 2, 1, 1, 1, 7, 3, 2, 2]
def baseStart_4891263 : Nat := 118140960795 + 4891263 * 2 ^ 59
def prefixEnd_4891263 : Nat := 4983230072969 + 3 ^ 40 * 4891263 * 2
def baseEnd_4891263 : Nat := 2511568926552601644717997

theorem tailTrace_4891263 : CollatzResearch.WordTrace tailWord_4891263 prefixEnd_4891263 2511568926552601644717997 := by
  unfold tailWord_4891263
  simp only [CollatzResearch.WordTrace]
  refine ⟨178399017678796987059006443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118932678452531324706004295 178399017678796987059006443)
  ·
    refine ⟨267598526518195480588509665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178399017678796987059006443 267598526518195480588509665)
    ·
      refine ⟨200698894888646610441382249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 267598526518195480588509665 200698894888646610441382249)
      ·
        refine ⟨150524171166484957831036687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 200698894888646610441382249 150524171166484957831036687)
        ·
          refine ⟨225786256749727436746555031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150524171166484957831036687 225786256749727436746555031)
          ·
            refine ⟨338679385124591155119832547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 225786256749727436746555031 338679385124591155119832547)
            ·
              refine ⟨508019077686886732679748821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 338679385124591155119832547 508019077686886732679748821)
              ·
                refine ⟨11906697133286407797181613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 508019077686886732679748821 11906697133286407797181613)
                ·
                  refine ⟨4465011424982402923943105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11906697133286407797181613 4465011424982402923943105)
                  ·
                    refine ⟨3348758568736802192957329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4465011424982402923943105 3348758568736802192957329)
                    ·
                      refine ⟨2511568926552601644717997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3348758568736802192957329 2511568926552601644717997)
                      ·
                        rfl

theorem cell23_4891263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 7, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 7, 3, 2, 2].length) (baseStart_4891263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4891263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4891263 prefixEnd_4891263 := by exact prefixLift 4891263
  have htrace : WordTrace (prefixWord ++ tailWord_4891263) baseStart_4891263 baseEnd_4891263 := by
    simpa [prefixWord, tailWord_4891263, baseEnd_4891263] using wordTrace_append hprefix tailTrace_4891263
  have hstable : (prefixWord ++ tailWord_4891263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4891263).length < 2 ^ (prefixWord ++ tailWord_4891263).sum := by decide
  have hdescent : baseEnd_4891263 < baseStart_4891263 := by decide
  rcases family_descends (prefixWord ++ tailWord_4891263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4891269 : List Nat := [1, 3, 1, 1, 4, 2, 1, 10]
def baseStart_4891269 : Nat := 118140960795 + 4891269 * 2 ^ 59
def prefixEnd_4891269 : Nat := 4983230072969 + 3 ^ 40 * 4891269 * 2
def baseEnd_4891269 : Nat := 93021185460612171157147

theorem tailTrace_4891269 : CollatzResearch.WordTrace tailWord_4891269 prefixEnd_4891269 93021185460612171157147 := by
  unfold tailWord_4891269
  simp only [CollatzResearch.WordTrace]
  refine ⟨178399236516775250083724861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118932824344516833389149907 178399236516775250083724861)
  ·
    refine ⟨66899713693790718781396823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 178399236516775250083724861 66899713693790718781396823)
    ·
      refine ⟨100349570540686078172095235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66899713693790718781396823 100349570540686078172095235)
      ·
        refine ⟨150524355811029117258142853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100349570540686078172095235 150524355811029117258142853)
        ·
          refine ⟨28223316714567959485901785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 150524355811029117258142853 28223316714567959485901785)
          ·
            refine ⟨21167487535925969614426339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28223316714567959485901785 21167487535925969614426339)
            ·
              refine ⟨31751231303888954421639509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21167487535925969614426339 31751231303888954421639509)
              ·
                refine ⟨93021185460612171157147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 31751231303888954421639509 93021185460612171157147)
                ·
                  rfl

theorem cell23_4891269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 10].length) (baseStart_4891269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4891269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4891269 prefixEnd_4891269 := by exact prefixLift 4891269
  have htrace : WordTrace (prefixWord ++ tailWord_4891269) baseStart_4891269 baseEnd_4891269 := by
    simpa [prefixWord, tailWord_4891269, baseEnd_4891269] using wordTrace_append hprefix tailTrace_4891269
  have hstable : (prefixWord ++ tailWord_4891269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4891269).length < 2 ^ (prefixWord ++ tailWord_4891269).sum := by decide
  have hdescent : baseEnd_4891269 < baseStart_4891269 := by decide
  rcases family_descends (prefixWord ++ tailWord_4891269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4891300 : List Nat := [2, 3, 1, 2, 2, 1, 5, 1, 1, 2, 3]
def baseStart_4891300 : Nat := 118140960795 + 4891300 * 2 ^ 59
def prefixEnd_4891300 : Nat := 4983230072969 + 3 ^ 40 * 4891300 * 2
def baseEnd_4891300 : Nat := 2511587925336817999955327

theorem tailTrace_4891300 : CollatzResearch.WordTrace tailWord_4891300 prefixEnd_4891300 2511587925336817999955327 := by
  unfold tailWord_4891300
  simp only [CollatzResearch.WordTrace]
  refine ⟨89200183589831471189051677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118933578119775294918735569 89200183589831471189051677)
  ·
    refine ⟨33450068846186801695894379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89200183589831471189051677 33450068846186801695894379)
    ·
      refine ⟨50175103269280202543841569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33450068846186801695894379 50175103269280202543841569)
      ·
        refine ⟨37631327451960151907881177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50175103269280202543841569 37631327451960151907881177)
        ·
          refine ⟨28223495588970113930910883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37631327451960151907881177 28223495588970113930910883)
          ·
            refine ⟨42335243383455170896366325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28223495588970113930910883 42335243383455170896366325)
            ·
              refine ⟨3968929067198922271534343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42335243383455170896366325 3968929067198922271534343)
              ·
                refine ⟨5953393600798383407301515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3968929067198922271534343 5953393600798383407301515)
                ·
                  refine ⟨8930090401197575110952273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5953393600798383407301515 8930090401197575110952273)
                  ·
                    refine ⟨6697567800898181333214205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8930090401197575110952273 6697567800898181333214205)
                    ·
                      refine ⟨2511587925336817999955327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6697567800898181333214205 2511587925336817999955327)
                      ·
                        rfl

theorem cell23_4891300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 5, 1, 1, 2, 3].length) (baseStart_4891300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4891300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4891300 prefixEnd_4891300 := by exact prefixLift 4891300
  have htrace : WordTrace (prefixWord ++ tailWord_4891300) baseStart_4891300 baseEnd_4891300 := by
    simpa [prefixWord, tailWord_4891300, baseEnd_4891300] using wordTrace_append hprefix tailTrace_4891300
  have hstable : (prefixWord ++ tailWord_4891300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4891300).length < 2 ^ (prefixWord ++ tailWord_4891300).sum := by decide
  have hdescent : baseEnd_4891300 < baseStart_4891300 := by decide
  rcases family_descends (prefixWord ++ tailWord_4891300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4891303 : List Nat := [1, 1, 6, 3, 2, 10]
def baseStart_4891303 : Nat := 118140960795 + 4891303 * 2 ^ 59
def prefixEnd_4891303 : Nat := 4983230072969 + 3 ^ 40 * 4891303 * 2
def baseEnd_4891303 : Nat := 10335759118431199539991

theorem tailTrace_4891303 : CollatzResearch.WordTrace tailWord_4891303 prefixEnd_4891303 10335759118431199539991 := by
  unfold tailWord_4891303
  simp only [CollatzResearch.WordTrace]
  refine ⟨178400476598652073890462563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118933651065768049260308375 178400476598652073890462563)
  ·
    refine ⟨267600714897978110835693845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178400476598652073890462563 267600714897978110835693845)
    ·
      refine ⟨12543783510842723945423149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 267600714897978110835693845 12543783510842723945423149)
      ·
        refine ⟨4703918816566021479533681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12543783510842723945423149 4703918816566021479533681)
        ·
          refine ⟨3527939112424516109650261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4703918816566021479533681 3527939112424516109650261)
          ·
            refine ⟨10335759118431199539991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3527939112424516109650261 10335759118431199539991)
            ·
              rfl

theorem cell23_4891303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 10].length) (baseStart_4891303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4891303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4891303 prefixEnd_4891303 := by exact prefixLift 4891303
  have htrace : WordTrace (prefixWord ++ tailWord_4891303) baseStart_4891303 baseEnd_4891303 := by
    simpa [prefixWord, tailWord_4891303, baseEnd_4891303] using wordTrace_append hprefix tailTrace_4891303
  have hstable : (prefixWord ++ tailWord_4891303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4891303).length < 2 ^ (prefixWord ++ tailWord_4891303).sum := by decide
  have hdescent : baseEnd_4891303 < baseStart_4891303 := by decide
  rcases family_descends (prefixWord ++ tailWord_4891303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4891340 : List Nat := [2, 2, 1, 5, 1, 1, 2, 1, 3, 3, 2]
def baseStart_4891340 : Nat := 118140960795 + 4891340 * 2 ^ 59
def prefixEnd_4891340 : Nat := 4983230072969 + 3 ^ 40 * 4891340 * 2
def baseEnd_4891340 : Nat := 2511608464562997843455143

theorem tailTrace_4891340 : CollatzResearch.WordTrace tailWord_4891340 prefixEnd_4891340 2511608464562997843455143 := by
  unfold tailWord_4891340
  simp only [CollatzResearch.WordTrace]
  refine ⟨89200913049759014604779737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118934550733012019473039649 89200913049759014604779737)
  ·
    refine ⟨66900684787319260953584803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89200913049759014604779737 66900684787319260953584803)
    ·
      refine ⟨100351027180978891430377205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66900684787319260953584803 100351027180978891430377205)
      ·
        refine ⟨9407908798216771071597863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 100351027180978891430377205 9407908798216771071597863)
        ·
          refine ⟨14111863197325156607396795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9407908798216771071597863 14111863197325156607396795)
          ·
            refine ⟨21167794795987734911095193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14111863197325156607396795 21167794795987734911095193)
            ·
              refine ⟨15875846096990801183321395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21167794795987734911095193 15875846096990801183321395)
              ·
                refine ⟨23813769145486201774982093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15875846096990801183321395 23813769145486201774982093)
                ·
                  refine ⟨8930163429557325665618285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23813769145486201774982093 8930163429557325665618285)
                  ·
                    refine ⟨3348811286083997124606857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8930163429557325665618285 3348811286083997124606857)
                    ·
                      refine ⟨2511608464562997843455143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3348811286083997124606857 2511608464562997843455143)
                      ·
                        rfl

theorem cell23_4891340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 1, 3, 3, 2].length) (baseStart_4891340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4891340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4891340 prefixEnd_4891340 := by exact prefixLift 4891340
  have htrace : WordTrace (prefixWord ++ tailWord_4891340) baseStart_4891340 baseEnd_4891340 := by
    simpa [prefixWord, tailWord_4891340, baseEnd_4891340] using wordTrace_append hprefix tailTrace_4891340
  have hstable : (prefixWord ++ tailWord_4891340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4891340).length < 2 ^ (prefixWord ++ tailWord_4891340).sum := by decide
  have hdescent : baseEnd_4891340 < baseStart_4891340 := by decide
  rcases family_descends (prefixWord ++ tailWord_4891340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4891353 : List Nat := [1, 2, 1, 2, 3, 2, 1, 4, 1, 4, 2]
def baseStart_4891353 : Nat := 118140960795 + 4891353 * 2 ^ 59
def prefixEnd_4891353 : Nat := 4983230072969 + 3 ^ 40 * 4891353 * 2
def baseEnd_4891353 : Nat := 2511615139811506292592583

theorem tailTrace_4891353 : CollatzResearch.WordTrace tailWord_4891353 prefixEnd_4891353 2511615139811506292592583 := by
  unfold tailWord_4891353
  simp only [CollatzResearch.WordTrace]
  refine ⟨178402300248470932429782713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118934866832313954953188475 178402300248470932429782713)
  ·
    refine ⟨133801725186353199322337035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178402300248470932429782713 133801725186353199322337035)
    ·
      refine ⟨200702587779529798983505553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133801725186353199322337035 200702587779529798983505553)
      ·
        refine ⟨150526940834647349237629165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 200702587779529798983505553 150526940834647349237629165)
        ·
          refine ⟨56447602812992755964110937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 150526940834647349237629165 56447602812992755964110937)
          ·
            refine ⟨42335702109744566973083203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56447602812992755964110937 42335702109744566973083203)
            ·
              refine ⟨63503553164616850459624805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42335702109744566973083203 63503553164616850459624805)
              ·
                refine ⟨11906916218365659461179651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63503553164616850459624805 11906916218365659461179651)
                ·
                  refine ⟨17860374327548489191769477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11906916218365659461179651 17860374327548489191769477)
                  ·
                    refine ⟨3348820186415341723456777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17860374327548489191769477 3348820186415341723456777)
                    ·
                      refine ⟨2511615139811506292592583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3348820186415341723456777 2511615139811506292592583)
                      ·
                        rfl

theorem cell23_4891353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 4, 1, 4, 2].length) (baseStart_4891353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4891353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4891353 prefixEnd_4891353 := by exact prefixLift 4891353
  have htrace : WordTrace (prefixWord ++ tailWord_4891353) baseStart_4891353 baseEnd_4891353 := by
    simpa [prefixWord, tailWord_4891353, baseEnd_4891353] using wordTrace_append hprefix tailTrace_4891353
  have hstable : (prefixWord ++ tailWord_4891353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4891353).length < 2 ^ (prefixWord ++ tailWord_4891353).sum := by decide
  have hdescent : baseEnd_4891353 < baseStart_4891353 := by decide
  rcases family_descends (prefixWord ++ tailWord_4891353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4891376 : List Nat := [2, 1, 1, 1, 3, 1, 6, 1, 7]
def baseStart_4891376 : Nat := 118140960795 + 4891376 * 2 ^ 59
def prefixEnd_4891376 : Nat := 4983230072969 + 3 ^ 40 * 4891376 * 2
def baseEnd_4891376 : Nat := 279069661096284411400553

theorem tailTrace_4891376 : CollatzResearch.WordTrace tailWord_4891376 prefixEnd_4891376 279069661096284411400553 := by
  unfold tailWord_4891376
  simp only [CollatzResearch.WordTrace]
  refine ⟨89201569563693803678934991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118935426084925071571913321 89201569563693803678934991)
  ·
    refine ⟨133802354345540705518402487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89201569563693803678934991 133802354345540705518402487)
    ·
      refine ⟨200703531518311058277603731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133802354345540705518402487 200703531518311058277603731)
      ·
        refine ⟨301055297277466587416405597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200703531518311058277603731 301055297277466587416405597)
        ·
          refine ⟨112895736479049970281152099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 301055297277466587416405597 112895736479049970281152099)
          ·
            refine ⟨169343604718574955421728149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112895736479049970281152099 169343604718574955421728149)
            ·
              refine ⟨7937981471183201035393507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 169343604718574955421728149 7937981471183201035393507)
              ·
                refine ⟨11906972206774801553090261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7937981471183201035393507 11906972206774801553090261)
                ·
                  refine ⟨279069661096284411400553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11906972206774801553090261 279069661096284411400553)
                  ·
                    rfl

theorem cell23_4891376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 6, 1, 7].length) (baseStart_4891376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4891376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4891376 prefixEnd_4891376 := by exact prefixLift 4891376
  have htrace : WordTrace (prefixWord ++ tailWord_4891376) baseStart_4891376 baseEnd_4891376 := by
    simpa [prefixWord, tailWord_4891376, baseEnd_4891376] using wordTrace_append hprefix tailTrace_4891376
  have hstable : (prefixWord ++ tailWord_4891376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4891376).length < 2 ^ (prefixWord ++ tailWord_4891376).sum := by decide
  have hdescent : baseEnd_4891376 < baseStart_4891376 := by decide
  rcases family_descends (prefixWord ++ tailWord_4891376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4891381 : List Nat := [1, 3, 6, 1, 2, 1, 1, 1, 1, 3, 3]
def baseStart_4891381 : Nat := 118140960795 + 4891381 * 2 ^ 59
def prefixEnd_4891381 : Nat := 4983230072969 + 3 ^ 40 * 4891381 * 2
def baseEnd_4891381 : Nat := 2511629517269832183042455

theorem tailTrace_4891381 : CollatzResearch.WordTrace tailWord_4891381 prefixEnd_4891381 2511629517269832183042455 := by
  unfold tailWord_4891381
  simp only [CollatzResearch.WordTrace]
  refine ⟨178403321492369493211801997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118935547661579662141201331 178403321492369493211801997)
  ·
    refine ⟨66901245559638559954425749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 178403321492369493211801997 66901245559638559954425749)
    ·
      refine ⟨3135995885608057497863707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 66901245559638559954425749 3135995885608057497863707)
      ·
        refine ⟨4703993828412086246795561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3135995885608057497863707 4703993828412086246795561)
        ·
          refine ⟨3527995371309064685096671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4703993828412086246795561 3527995371309064685096671)
          ·
            refine ⟨5291993056963597027645007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3527995371309064685096671 5291993056963597027645007)
            ·
              refine ⟨7937989585445395541467511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5291993056963597027645007 7937989585445395541467511)
              ·
                refine ⟨11906984378168093312201267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7937989585445395541467511 11906984378168093312201267)
                ·
                  refine ⟨17860476567252139968301901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11906984378168093312201267 17860476567252139968301901)
                  ·
                    refine ⟨6697678712719552488113213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17860476567252139968301901 6697678712719552488113213)
                    ·
                      refine ⟨2511629517269832183042455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6697678712719552488113213 2511629517269832183042455)
                      ·
                        rfl

theorem cell23_4891381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_4891381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4891381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4891381 prefixEnd_4891381 := by exact prefixLift 4891381
  have htrace : WordTrace (prefixWord ++ tailWord_4891381) baseStart_4891381 baseEnd_4891381 := by
    simpa [prefixWord, tailWord_4891381, baseEnd_4891381] using wordTrace_append hprefix tailTrace_4891381
  have hstable : (prefixWord ++ tailWord_4891381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4891381).length < 2 ^ (prefixWord ++ tailWord_4891381).sum := by decide
  have hdescent : baseEnd_4891381 < baseStart_4891381 := by decide
  rcases family_descends (prefixWord ++ tailWord_4891381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4891416 : List Nat := [2, 1, 2, 3, 1, 1, 1, 4, 1, 2, 5]
def baseStart_4891416 : Nat := 118140960795 + 4891416 * 2 ^ 59
def prefixEnd_4891416 : Nat := 4983230072969 + 3 ^ 40 * 4891416 * 2
def baseEnd_4891416 : Nat := 2511647489092739546104793

theorem tailTrace_4891416 : CollatzResearch.WordTrace tailWord_4891416 prefixEnd_4891416 2511647489092739546104793 := by
  unfold tailWord_4891416
  simp only [CollatzResearch.WordTrace]
  refine ⟨89202299023621347094663051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118936398698161796126217401 89202299023621347094663051)
  ·
    refine ⟨133803448535432020641994577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89202299023621347094663051 133803448535432020641994577)
    ·
      refine ⟨100352586401574015481495933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133803448535432020641994577 100352586401574015481495933)
      ·
        refine ⟨37632219900590255805560975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100352586401574015481495933 37632219900590255805560975)
        ·
          refine ⟨56448329850885383708341463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37632219900590255805560975 56448329850885383708341463)
          ·
            refine ⟨84672494776328075562512195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56448329850885383708341463 84672494776328075562512195)
            ·
              refine ⟨127008742164492113343768293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84672494776328075562512195 127008742164492113343768293)
              ·
                refine ⟨23814139155842271251956555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 127008742164492113343768293 23814139155842271251956555)
                ·
                  refine ⟨35721208733763406877934833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23814139155842271251956555 35721208733763406877934833)
                  ·
                    refine ⟨26790906550322555158451125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35721208733763406877934833 26790906550322555158451125)
                    ·
                      refine ⟨2511647489092739546104793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26790906550322555158451125 2511647489092739546104793)
                      ·
                        rfl

theorem cell23_4891416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 4, 1, 2, 5].length) (baseStart_4891416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4891416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4891416 prefixEnd_4891416 := by exact prefixLift 4891416
  have htrace : WordTrace (prefixWord ++ tailWord_4891416) baseStart_4891416 baseEnd_4891416 := by
    simpa [prefixWord, tailWord_4891416, baseEnd_4891416] using wordTrace_append hprefix tailTrace_4891416
  have hstable : (prefixWord ++ tailWord_4891416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4891416).length < 2 ^ (prefixWord ++ tailWord_4891416).sum := by decide
  have hdescent : baseEnd_4891416 < baseStart_4891416 := by decide
  rcases family_descends (prefixWord ++ tailWord_4891416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4891423 : List Nat := [1, 1, 2, 4, 2, 3, 1, 2, 2, 5]
def baseStart_4891423 : Nat := 118140960795 + 4891423 * 2 ^ 59
def prefixEnd_4891423 : Nat := 4983230072969 + 3 ^ 40 * 4891423 * 2
def baseEnd_4891423 : Nat := 837217027819107006239087

theorem tailTrace_4891423 : CollatzResearch.WordTrace tailWord_4891423 prefixEnd_4891423 837217027819107006239087 := by
  unfold tailWord_4891423
  simp only [CollatzResearch.WordTrace]
  refine ⟨178404853358217334384830923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118936568905478222923220615 178404853358217334384830923)
  ·
    refine ⟨267607280037326001577246385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178404853358217334384830923 267607280037326001577246385)
    ·
      refine ⟨200705460027994501182934789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 267607280037326001577246385 200705460027994501182934789)
      ·
        refine ⟨37632273755248968971800273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 200705460027994501182934789 37632273755248968971800273)
        ·
          refine ⟨28224205316436726728850205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37632273755248968971800273 28224205316436726728850205)
          ·
            refine ⟨10584076993663772523318827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28224205316436726728850205 10584076993663772523318827)
            ·
              refine ⟨15876115490495658784978241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10584076993663772523318827 15876115490495658784978241)
              ·
                refine ⟨11907086617871744088733681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15876115490495658784978241 11907086617871744088733681)
                ·
                  refine ⟨8930314963403808066550261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11907086617871744088733681 8930314963403808066550261)
                  ·
                    refine ⟨837217027819107006239087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8930314963403808066550261 837217027819107006239087)
                    ·
                      rfl

theorem cell23_4891423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 2, 2, 5].length) (baseStart_4891423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4891423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4891423 prefixEnd_4891423 := by exact prefixLift 4891423
  have htrace : WordTrace (prefixWord ++ tailWord_4891423) baseStart_4891423 baseEnd_4891423 := by
    simpa [prefixWord, tailWord_4891423, baseEnd_4891423] using wordTrace_append hprefix tailTrace_4891423
  have hstable : (prefixWord ++ tailWord_4891423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4891423).length < 2 ^ (prefixWord ++ tailWord_4891423).sum := by decide
  have hdescent : baseEnd_4891423 < baseStart_4891423 := by decide
  rcases family_descends (prefixWord ++ tailWord_4891423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4891456 : List Nat := [2, 1, 1, 2, 2, 1, 1, 3, 2, 4, 4]
def baseStart_4891456 : Nat := 118140960795 + 4891456 * 2 ^ 59
def prefixEnd_4891456 : Nat := 4983230072969 + 3 ^ 40 * 4891456 * 2
def baseEnd_4891456 : Nat := 2511668028318919389604609

theorem tailTrace_4891456 : CollatzResearch.WordTrace tailWord_4891456 prefixEnd_4891456 2511668028318919389604609 := by
  unfold tailWord_4891456
  simp only [CollatzResearch.WordTrace]
  refine ⟨89203028483548890510391111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118937371311398520680521481 89203028483548890510391111)
  ·
    refine ⟨133804542725323335765586667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89203028483548890510391111 133804542725323335765586667)
    ·
      refine ⟨200706814087985003648380001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133804542725323335765586667 200706814087985003648380001)
      ·
        refine ⟨150530110565988752736285001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 200706814087985003648380001 150530110565988752736285001)
        ·
          refine ⟨112897582924491564552213751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150530110565988752736285001 112897582924491564552213751)
          ·
            refine ⟨169346374386737346828320627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112897582924491564552213751 169346374386737346828320627)
            ·
              refine ⟨254019561580106020242480941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 169346374386737346828320627 254019561580106020242480941)
              ·
                refine ⟨95257335592539757590930353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 254019561580106020242480941 95257335592539757590930353)
                ·
                  refine ⟨71443001694404818193197765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 95257335592539757590930353 71443001694404818193197765)
                  ·
                    refine ⟨13395562817700903411224581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 71443001694404818193197765 13395562817700903411224581)
                    ·
                      refine ⟨2511668028318919389604609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13395562817700903411224581 2511668028318919389604609)
                      ·
                        rfl

theorem cell23_4891456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 2, 4, 4].length) (baseStart_4891456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4891456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4891456 prefixEnd_4891456 := by exact prefixLift 4891456
  have htrace : WordTrace (prefixWord ++ tailWord_4891456) baseStart_4891456 baseEnd_4891456 := by
    simpa [prefixWord, tailWord_4891456, baseEnd_4891456] using wordTrace_append hprefix tailTrace_4891456
  have hstable : (prefixWord ++ tailWord_4891456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4891456).length < 2 ^ (prefixWord ++ tailWord_4891456).sum := by decide
  have hdescent : baseEnd_4891456 < baseStart_4891456 := by decide
  rcases family_descends (prefixWord ++ tailWord_4891456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4891457 : List Nat := [1, 2, 5, 3, 1, 1, 2, 1, 2, 5]
def baseStart_4891457 : Nat := 118140960795 + 4891457 * 2 ^ 59
def prefixEnd_4891457 : Nat := 4983230072969 + 3 ^ 40 * 4891457 * 2
def baseEnd_4891457 : Nat := 837222847266524628564035

theorem tailTrace_4891457 : CollatzResearch.WordTrace tailWord_4891457 prefixEnd_4891457 837222847266524628564035 := by
  unfold tailWord_4891457
  simp only [CollatzResearch.WordTrace]
  refine ⟨178406093440094158191568625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118937395626729438794379083 178406093440094158191568625)
  ·
    refine ⟨133804570080070618643676469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178406093440094158191568625 133804570080070618643676469)
    ·
      refine ⟨12544178445006620497844669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 133804570080070618643676469 12544178445006620497844669)
      ·
        refine ⟨4704066916877482686691751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12544178445006620497844669 4704066916877482686691751)
        ·
          refine ⟨7056100375316224030037627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4704066916877482686691751 7056100375316224030037627)
          ·
            refine ⟨10584150562974336045056441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7056100375316224030037627 10584150562974336045056441)
            ·
              refine ⟨7938112922230752033792331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10584150562974336045056441 7938112922230752033792331)
              ·
                refine ⟨11907169383346128050688497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7938112922230752033792331 11907169383346128050688497)
                ·
                  refine ⟨8930377037509596038016373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11907169383346128050688497 8930377037509596038016373)
                  ·
                    refine ⟨837222847266524628564035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8930377037509596038016373 837222847266524628564035)
                    ·
                      rfl

theorem cell23_4891457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 2, 1, 2, 5].length) (baseStart_4891457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4891457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4891457 prefixEnd_4891457 := by exact prefixLift 4891457
  have htrace : WordTrace (prefixWord ++ tailWord_4891457) baseStart_4891457 baseEnd_4891457 := by
    simpa [prefixWord, tailWord_4891457, baseEnd_4891457] using wordTrace_append hprefix tailTrace_4891457
  have hstable : (prefixWord ++ tailWord_4891457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4891457).length < 2 ^ (prefixWord ++ tailWord_4891457).sum := by decide
  have hdescent : baseEnd_4891457 < baseStart_4891457 := by decide
  rcases family_descends (prefixWord ++ tailWord_4891457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4891466 : List Nat := [3, 1, 2, 1, 1, 1, 2, 4, 8]
def baseStart_4891466 : Nat := 118140960795 + 4891466 * 2 ^ 59
def prefixEnd_4891466 : Nat := 4983230072969 + 3 ^ 40 * 4891466 * 2
def baseEnd_4891466 : Nat := 279074795902829372275507

theorem tailTrace_4891466 : CollatzResearch.WordTrace tailWord_4891466 prefixEnd_4891466 279074795902829372275507 := by
  unfold tailWord_4891466
  simp only [CollatzResearch.WordTrace]
  refine ⟨44601605424265388182161563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118937614464707701819097501 44601605424265388182161563)
  ·
    refine ⟨66902408136398082273242345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44601605424265388182161563 66902408136398082273242345)
    ·
      refine ⟨50176806102298561704931759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66902408136398082273242345 50176806102298561704931759)
      ·
        refine ⟨75265209153447842557397639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50176806102298561704931759 75265209153447842557397639)
        ·
          refine ⟨112897813730171763836096459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75265209153447842557397639 112897813730171763836096459)
          ·
            refine ⟨169346720595257645754144689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112897813730171763836096459 169346720595257645754144689)
            ·
              refine ⟨127010040446443234315608517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 169346720595257645754144689 127010040446443234315608517)
              ·
                refine ⟨23814382583708106434176597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 127010040446443234315608517 23814382583708106434176597)
                ·
                  refine ⟨279074795902829372275507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23814382583708106434176597 279074795902829372275507)
                  ·
                    rfl

theorem cell23_4891466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 4, 8].length) (baseStart_4891466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4891466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4891466 prefixEnd_4891466 := by exact prefixLift 4891466
  have htrace : WordTrace (prefixWord ++ tailWord_4891466) baseStart_4891466 baseEnd_4891466 := by
    simpa [prefixWord, tailWord_4891466, baseEnd_4891466] using wordTrace_append hprefix tailTrace_4891466
  have hstable : (prefixWord ++ tailWord_4891466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4891466).length < 2 ^ (prefixWord ++ tailWord_4891466).sum := by decide
  have hdescent : baseEnd_4891466 < baseStart_4891466 := by decide
  rcases family_descends (prefixWord ++ tailWord_4891466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4891513 : List Nat := [1, 2, 1, 3, 2, 3, 2, 1, 3, 5]
def baseStart_4891513 : Nat := 118140960795 + 4891513 * 2 ^ 59
def prefixEnd_4891513 : Nat := 4983230072969 + 3 ^ 40 * 4891513 * 2
def baseEnd_4891513 : Nat := 837232432238741888863949

theorem tailTrace_4891513 : CollatzResearch.WordTrace tailWord_4891513 prefixEnd_4891513 837232432238741888863949 := by
  unfold tailWord_4891513
  simp only [CollatzResearch.WordTrace]
  refine ⟨178408135927891279755607193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118938757285260853170404795 178408135927891279755607193)
  ·
    refine ⟨133806101945918459816705395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178408135927891279755607193 133806101945918459816705395)
    ·
      refine ⟨200709152918877689725058093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133806101945918459816705395 200709152918877689725058093)
      ·
        refine ⟨75265932344579133646896785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 200709152918877689725058093 75265932344579133646896785)
        ·
          refine ⟨56449449258434350235172589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75265932344579133646896785 56449449258434350235172589)
          ·
            refine ⟨21168543471912881338189721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56449449258434350235172589 21168543471912881338189721)
            ·
              refine ⟨15876407603934661003642291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21168543471912881338189721 15876407603934661003642291)
              ·
                refine ⟨23814611405901991505463437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15876407603934661003642291 23814611405901991505463437)
                ·
                  refine ⟨8930479277213246814548789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23814611405901991505463437 8930479277213246814548789)
                  ·
                    refine ⟨837232432238741888863949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8930479277213246814548789 837232432238741888863949)
                    ·
                      rfl

theorem cell23_4891513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 1, 3, 5].length) (baseStart_4891513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4891513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4891513 prefixEnd_4891513 := by exact prefixLift 4891513
  have htrace : WordTrace (prefixWord ++ tailWord_4891513) baseStart_4891513 baseEnd_4891513 := by
    simpa [prefixWord, tailWord_4891513, baseEnd_4891513] using wordTrace_append hprefix tailTrace_4891513
  have hstable : (prefixWord ++ tailWord_4891513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4891513).length < 2 ^ (prefixWord ++ tailWord_4891513).sum := by decide
  have hdescent : baseEnd_4891513 < baseStart_4891513 := by decide
  rcases family_descends (prefixWord ++ tailWord_4891513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4891520 : List Nat := [2, 1, 1, 2, 1, 2, 2, 5, 2, 3, 2]
def baseStart_4891520 : Nat := 118140960795 + 4891520 * 2 ^ 59
def prefixEnd_4891520 : Nat := 4983230072969 + 3 ^ 40 * 4891520 * 2
def baseEnd_4891520 : Nat := 2511700891080807139204315

theorem tailTrace_4891520 : CollatzResearch.WordTrace tailWord_4891520 prefixEnd_4891520 2511700891080807139204315 := by
  unfold tailWord_4891520
  simp only [CollatzResearch.WordTrace]
  refine ⟨89204195619432959975556007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118938927492577279967408009 89204195619432959975556007)
  ·
    refine ⟨133806293429149439963334011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89204195619432959975556007 133806293429149439963334011)
    ·
      refine ⟨200709440143724159945001017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133806293429149439963334011 200709440143724159945001017)
      ·
        refine ⟨150532080107793119958750763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 200709440143724159945001017 150532080107793119958750763)
        ·
          refine ⟨225798120161689679938126145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150532080107793119958750763 225798120161689679938126145)
          ·
            refine ⟨169348590121267259953594609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 225798120161689679938126145 169348590121267259953594609)
            ·
              refine ⟨127011442590950444965195957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 169348590121267259953594609 127011442590950444965195957)
              ·
                refine ⟨11907322742901604215487121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 127011442590950444965195957 11907322742901604215487121)
                ·
                  refine ⟨8930492057176203161615341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11907322742901604215487121 8930492057176203161615341)
                  ·
                    refine ⟨3348934521441076185605753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8930492057176203161615341 3348934521441076185605753)
                    ·
                      refine ⟨2511700891080807139204315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3348934521441076185605753 2511700891080807139204315)
                      ·
                        rfl

theorem cell23_4891520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 5, 2, 3, 2].length) (baseStart_4891520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4891520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4891520 prefixEnd_4891520 := by exact prefixLift 4891520
  have htrace : WordTrace (prefixWord ++ tailWord_4891520) baseStart_4891520 baseEnd_4891520 := by
    simpa [prefixWord, tailWord_4891520, baseEnd_4891520] using wordTrace_append hprefix tailTrace_4891520
  have hstable : (prefixWord ++ tailWord_4891520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4891520).length < 2 ^ (prefixWord ++ tailWord_4891520).sum := by decide
  have hdescent : baseEnd_4891520 < baseStart_4891520 := by decide
  rcases family_descends (prefixWord ++ tailWord_4891520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4891573 : List Nat := [1, 3, 3, 2, 1, 1, 3, 9]
def baseStart_4891573 : Nat := 118140960795 + 4891573 * 2 ^ 59
def prefixEnd_4891573 : Nat := 4983230072969 + 3 ^ 40 * 4891573 * 2
def baseEnd_4891573 : Nat := 93026966872425756734873

theorem tailTrace_4891573 : CollatzResearch.WordTrace tailWord_4891573 prefixEnd_4891573 93026966872425756734873 := by
  unfold tailWord_4891573
  simp only [CollatzResearch.WordTrace]
  refine ⟨178410324307673910002791373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118940216205115940001860915 178410324307673910002791373)
  ·
    refine ⟨66903871615377716251046765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 178410324307673910002791373 66903871615377716251046765)
    ·
      refine ⟨25088951855766643594142537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66903871615377716251046765 25088951855766643594142537)
      ·
        refine ⟨18816713891824982695606903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25088951855766643594142537 18816713891824982695606903)
        ·
          refine ⟨28225070837737474043410355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18816713891824982695606903 28225070837737474043410355)
          ·
            refine ⟨42337606256606211065115533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28225070837737474043410355 42337606256606211065115533)
            ·
              refine ⟨15876602346227329149418325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42337606256606211065115533 15876602346227329149418325)
              ·
                refine ⟨93026966872425756734873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15876602346227329149418325 93026966872425756734873)
                ·
                  rfl

theorem cell23_4891573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 9].length) (baseStart_4891573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4891573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4891573 prefixEnd_4891573 := by exact prefixLift 4891573
  have htrace : WordTrace (prefixWord ++ tailWord_4891573) baseStart_4891573 baseEnd_4891573 := by
    simpa [prefixWord, tailWord_4891573, baseEnd_4891573] using wordTrace_append hprefix tailTrace_4891573
  have hstable : (prefixWord ++ tailWord_4891573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4891573).length < 2 ^ (prefixWord ++ tailWord_4891573).sum := by decide
  have hdescent : baseEnd_4891573 < baseStart_4891573 := by decide
  rcases family_descends (prefixWord ++ tailWord_4891573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4891601 : List Nat := [1, 2, 2, 1, 2, 1, 7, 2, 1, 2, 2]
def baseStart_4891601 : Nat := 118140960795 + 4891601 * 2 ^ 59
def prefixEnd_4891601 : Nat := 4983230072969 + 3 ^ 40 * 4891601 * 2
def baseEnd_4891601 : Nat := 2511742483013821322291443

theorem tailTrace_4891601 : CollatzResearch.WordTrace tailWord_4891601 prefixEnd_4891601 2511742483013821322291443 := by
  unfold tailWord_4891601
  simp only [CollatzResearch.WordTrace]
  refine ⟨178411345551572470784810657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118940897034381647189873771 178411345551572470784810657)
  ·
    refine ⟨133808509163679353088607993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178411345551572470784810657 133808509163679353088607993)
    ·
      refine ⟨100356381872759514816455995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133808509163679353088607993 100356381872759514816455995)
      ·
        refine ⟨150534572809139272224683993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100356381872759514816455995 150534572809139272224683993)
        ·
          refine ⟨112900929606854454168512995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150534572809139272224683993 112900929606854454168512995)
          ·
            refine ⟨169351394410281681252769493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112900929606854454168512995 169351394410281681252769493)
            ·
              refine ⟨3969173306490976904361785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 169351394410281681252769493 3969173306490976904361785)
              ·
                refine ⟨2976879979868232678271339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3969173306490976904361785 2976879979868232678271339)
                ·
                  refine ⟨4465319969802349017407009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2976879979868232678271339 4465319969802349017407009)
                  ·
                    refine ⟨3348989977351761763055257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4465319969802349017407009 3348989977351761763055257)
                    ·
                      refine ⟨2511742483013821322291443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3348989977351761763055257 2511742483013821322291443)
                      ·
                        rfl

theorem cell23_4891601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 7, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 7, 2, 1, 2, 2].length) (baseStart_4891601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4891601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4891601 prefixEnd_4891601 := by exact prefixLift 4891601
  have htrace : WordTrace (prefixWord ++ tailWord_4891601) baseStart_4891601 baseEnd_4891601 := by
    simpa [prefixWord, tailWord_4891601, baseEnd_4891601] using wordTrace_append hprefix tailTrace_4891601
  have hstable : (prefixWord ++ tailWord_4891601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4891601).length < 2 ^ (prefixWord ++ tailWord_4891601).sum := by decide
  have hdescent : baseEnd_4891601 < baseStart_4891601 := by decide
  rcases family_descends (prefixWord ++ tailWord_4891601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4891621 : List Nat := [1, 3, 1, 6, 1, 2, 1, 2, 1, 2, 3]
def baseStart_4891621 : Nat := 118140960795 + 4891621 * 2 ^ 59
def prefixEnd_4891621 : Nat := 4983230072969 + 3 ^ 40 * 4891621 * 2
def baseEnd_4891621 : Nat := 2511752752626911244041351

theorem tailTrace_4891621 : CollatzResearch.WordTrace tailWord_4891621 prefixEnd_4891621 2511752752626911244041351 := by
  unfold tailWord_4891621
  simp only [CollatzResearch.WordTrace]
  refine ⟨178412075011500014200538717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118941383341000009467025811 178412075011500014200538717)
  ·
    refine ⟨66904528129312505325202019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 178412075011500014200538717 66904528129312505325202019)
    ·
      refine ⟨100356792193968757987803029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66904528129312505325202019 100356792193968757987803029)
      ·
        refine ⟨4704224634092285530678267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 100356792193968757987803029 4704224634092285530678267)
        ·
          refine ⟨7056336951138428296017401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4704224634092285530678267 7056336951138428296017401)
          ·
            refine ⟨5292252713353821222013051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7056336951138428296017401 5292252713353821222013051)
            ·
              refine ⟨7938379070030731833019577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5292252713353821222013051 7938379070030731833019577)
              ·
                refine ⟨5953784302523048874764683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7938379070030731833019577 5953784302523048874764683)
                ·
                  refine ⟨8930676453784573312147025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5953784302523048874764683 8930676453784573312147025)
                  ·
                    refine ⟨6698007340338429984110269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8930676453784573312147025 6698007340338429984110269)
                    ·
                      refine ⟨2511752752626911244041351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6698007340338429984110269 2511752752626911244041351)
                      ·
                        rfl

theorem cell23_4891621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_4891621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4891621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4891621 prefixEnd_4891621 := by exact prefixLift 4891621
  have htrace : WordTrace (prefixWord ++ tailWord_4891621) baseStart_4891621 baseEnd_4891621 := by
    simpa [prefixWord, tailWord_4891621, baseEnd_4891621] using wordTrace_append hprefix tailTrace_4891621
  have hstable : (prefixWord ++ tailWord_4891621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4891621).length < 2 ^ (prefixWord ++ tailWord_4891621).sum := by decide
  have hdescent : baseEnd_4891621 < baseStart_4891621 := by decide
  rcases family_descends (prefixWord ++ tailWord_4891621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4891634 : List Nat := [3, 2, 1, 5, 1, 1, 1, 2, 1, 3, 3]
def baseStart_4891634 : Nat := 118140960795 + 4891634 * 2 ^ 59
def prefixEnd_4891634 : Nat := 4983230072969 + 3 ^ 40 * 4891634 * 2
def baseEnd_4891634 : Nat := 2511759427875419693178791

theorem tailTrace_4891634 : CollatzResearch.WordTrace tailWord_4891634 prefixEnd_4891634 2511759427875419693178791 := by
  unfold tailWord_4891634
  simp only [CollatzResearch.WordTrace]
  refine ⟨44603137290113229355190489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118941699440301944947174637 44603137290113229355190489)
  ·
    refine ⟨33452352967584922016392867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44603137290113229355190489 33452352967584922016392867)
    ·
      refine ⟨50178529451377383024589301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33452352967584922016392867 50178529451377383024589301)
      ·
        refine ⟨4704237136066629658555247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 50178529451377383024589301 4704237136066629658555247)
        ·
          refine ⟨7056355704099944487832871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4704237136066629658555247 7056355704099944487832871)
          ·
            refine ⟨10584533556149916731749307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7056355704099944487832871 10584533556149916731749307)
            ·
              refine ⟨15876800334224875097623961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10584533556149916731749307 15876800334224875097623961)
              ·
                refine ⟨11907600250668656323217971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15876800334224875097623961 11907600250668656323217971)
                ·
                  refine ⟨17861400376002984484826957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11907600250668656323217971 17861400376002984484826957)
                  ·
                    refine ⟨6698025141001119181810109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17861400376002984484826957 6698025141001119181810109)
                    ·
                      refine ⟨2511759427875419693178791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6698025141001119181810109 2511759427875419693178791)
                      ·
                        rfl

theorem cell23_4891634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_4891634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4891634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4891634 prefixEnd_4891634 := by exact prefixLift 4891634
  have htrace : WordTrace (prefixWord ++ tailWord_4891634) baseStart_4891634 baseEnd_4891634 := by
    simpa [prefixWord, tailWord_4891634, baseEnd_4891634] using wordTrace_append hprefix tailTrace_4891634
  have hstable : (prefixWord ++ tailWord_4891634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4891634).length < 2 ^ (prefixWord ++ tailWord_4891634).sum := by decide
  have hdescent : baseEnd_4891634 < baseStart_4891634 := by decide
  rcases family_descends (prefixWord ++ tailWord_4891634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4891657 : List Nat := [1, 2, 1, 1, 3, 1, 1, 5, 4, 2, 2]
def baseStart_4891657 : Nat := 118140960795 + 4891657 * 2 ^ 59
def prefixEnd_4891657 : Nat := 4983230072969 + 3 ^ 40 * 4891657 * 2
def baseEnd_4891657 : Nat := 2511771237930473103191185

theorem tailTrace_4891657 : CollatzResearch.WordTrace tailWord_4891657 prefixEnd_4891657 2511771237930473103191185 := by
  unfold tailWord_4891657
  simp only [CollatzResearch.WordTrace]
  refine ⟨178413388039369592348849225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118942258692913061565899483 178413388039369592348849225)
  ·
    refine ⟨133810041029527194261636919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178413388039369592348849225 133810041029527194261636919)
    ·
      refine ⟨200715061544290791392455379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133810041029527194261636919 200715061544290791392455379)
      ·
        refine ⟨301072592316436187088683069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200715061544290791392455379 301072592316436187088683069)
        ·
          refine ⟨112902222118663570158256151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 301072592316436187088683069 112902222118663570158256151)
          ·
            refine ⟨169353333177995355237384227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112902222118663570158256151 169353333177995355237384227)
            ·
              refine ⟨254029999766993032856076341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 169353333177995355237384227 254029999766993032856076341)
              ·
                refine ⟨23815312478155596830257157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 254029999766993032856076341 23815312478155596830257157)
                ·
                  refine ⟨4465371089654174405673217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23815312478155596830257157 4465371089654174405673217)
                  ·
                    refine ⟨3349028317240630804254913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4465371089654174405673217 3349028317240630804254913)
                    ·
                      refine ⟨2511771237930473103191185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3349028317240630804254913 2511771237930473103191185)
                      ·
                        rfl

theorem cell23_4891657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 5, 4, 2, 2].length) (baseStart_4891657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4891657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4891657 prefixEnd_4891657 := by exact prefixLift 4891657
  have htrace : WordTrace (prefixWord ++ tailWord_4891657) baseStart_4891657 baseEnd_4891657 := by
    simpa [prefixWord, tailWord_4891657, baseEnd_4891657] using wordTrace_append hprefix tailTrace_4891657
  have hstable : (prefixWord ++ tailWord_4891657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4891657).length < 2 ^ (prefixWord ++ tailWord_4891657).sum := by decide
  have hdescent : baseEnd_4891657 < baseStart_4891657 := by decide
  rcases family_descends (prefixWord ++ tailWord_4891657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4891660 : List Nat := [2, 2, 1, 2, 3, 2, 1, 1, 2, 4, 3]
def baseStart_4891660 : Nat := 118140960795 + 4891660 * 2 ^ 59
def prefixEnd_4891660 : Nat := 4983230072969 + 3 ^ 40 * 4891660 * 2
def baseEnd_4891660 : Nat := 2511772778372436591453671

theorem tailTrace_4891660 : CollatzResearch.WordTrace tailWord_4891660 prefixEnd_4891660 2511772778372436591453671 := by
  unfold tailWord_4891660
  simp only [CollatzResearch.WordTrace]
  refine ⟨89206748729179361930604217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118942331638905815907472289 89206748729179361930604217)
  ·
    refine ⟨66905061546884521447953163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89206748729179361930604217 66905061546884521447953163)
    ·
      refine ⟨100357592320326782171929745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66905061546884521447953163 100357592320326782171929745)
      ·
        refine ⟨75268194240245086628947309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100357592320326782171929745 75268194240245086628947309)
        ·
          refine ⟨28225572840091907485855241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75268194240245086628947309 28225572840091907485855241)
          ·
            refine ⟨21169179630068930614391431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28225572840091907485855241 21169179630068930614391431)
            ·
              refine ⟨31753769445103395921587147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21169179630068930614391431 31753769445103395921587147)
              ·
                refine ⟨47630654167655093882380721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31753769445103395921587147 47630654167655093882380721)
                ·
                  refine ⟨35722990625741320411785541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47630654167655093882380721 35722990625741320411785541)
                  ·
                    refine ⟨6698060742326497577209789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35722990625741320411785541 6698060742326497577209789)
                    ·
                      refine ⟨2511772778372436591453671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6698060742326497577209789 2511772778372436591453671)
                      ·
                        rfl

theorem cell23_4891660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 1, 2, 4, 3].length) (baseStart_4891660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4891660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4891660 prefixEnd_4891660 := by exact prefixLift 4891660
  have htrace : WordTrace (prefixWord ++ tailWord_4891660) baseStart_4891660 baseEnd_4891660 := by
    simpa [prefixWord, tailWord_4891660, baseEnd_4891660] using wordTrace_append hprefix tailTrace_4891660
  have hstable : (prefixWord ++ tailWord_4891660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4891660).length < 2 ^ (prefixWord ++ tailWord_4891660).sum := by decide
  have hdescent : baseEnd_4891660 < baseStart_4891660 := by decide
  rcases family_descends (prefixWord ++ tailWord_4891660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4891674 : List Nat := [3, 1, 1, 3, 1, 2, 1, 5, 2, 2, 2]
def baseStart_4891674 : Nat := 118140960795 + 4891674 * 2 ^ 59
def prefixEnd_4891674 : Nat := 4983230072969 + 3 ^ 40 * 4891674 * 2
def baseEnd_4891674 : Nat := 2511779967101599536678607

theorem tailTrace_4891674 : CollatzResearch.WordTrace tailWord_4891674 prefixEnd_4891674 2511779967101599536678607 := by
  unfold tailWord_4891674
  simp only [CollatzResearch.WordTrace]
  refine ⟨44603502020077001063054519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118942672053538669501478717 44603502020077001063054519)
  ·
    refine ⟨66905253030115501594581779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44603502020077001063054519 66905253030115501594581779)
    ·
      refine ⟨100357879545173252391872669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66905253030115501594581779 100357879545173252391872669)
      ·
        refine ⟨37634204829439969646952251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100357879545173252391872669 37634204829439969646952251)
        ·
          refine ⟨56451307244159954470428377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37634204829439969646952251 56451307244159954470428377)
          ·
            refine ⟨42338480433119965852821283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56451307244159954470428377 42338480433119965852821283)
            ·
              refine ⟨63507720649679948779231925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42338480433119965852821283 63507720649679948779231925)
              ·
                refine ⟨5953848810907495198052993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 63507720649679948779231925 5953848810907495198052993)
                ·
                  refine ⟨4465386608180621398539745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5953848810907495198052993 4465386608180621398539745)
                  ·
                    refine ⟨3349039956135466048904809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4465386608180621398539745 3349039956135466048904809)
                    ·
                      refine ⟨2511779967101599536678607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3349039956135466048904809 2511779967101599536678607)
                      ·
                        rfl

theorem cell23_4891674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 5, 2, 2, 2].length) (baseStart_4891674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4891674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4891674 prefixEnd_4891674 := by exact prefixLift 4891674
  have htrace : WordTrace (prefixWord ++ tailWord_4891674) baseStart_4891674 baseEnd_4891674 := by
    simpa [prefixWord, tailWord_4891674, baseEnd_4891674] using wordTrace_append hprefix tailTrace_4891674
  have hstable : (prefixWord ++ tailWord_4891674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4891674).length < 2 ^ (prefixWord ++ tailWord_4891674).sum := by decide
  have hdescent : baseEnd_4891674 < baseStart_4891674 := by decide
  rcases family_descends (prefixWord ++ tailWord_4891674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4891697 : List Nat := [1, 2, 2, 3, 1, 2, 4, 3, 5]
def baseStart_4891697 : Nat := 118140960795 + 4891697 * 2 ^ 59
def prefixEnd_4891697 : Nat := 4983230072969 + 3 ^ 40 * 4891697 * 2
def baseEnd_4891697 : Nat := 279087975239628105187889

theorem tailTrace_4891697 : CollatzResearch.WordTrace tailWord_4891697 prefixEnd_4891697 279087975239628105187889 := by
  unfold tailWord_4891697
  simp only [CollatzResearch.WordTrace]
  refine ⟨178414846959224679180305345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118943231306149786120203563 178414846959224679180305345)
  ·
    refine ⟨133811135219418509385229009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178414846959224679180305345 133811135219418509385229009)
    ·
      refine ⟨100358351414563882038921757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133811135219418509385229009 100358351414563882038921757)
      ·
        refine ⟨37634381780461455764595659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100358351414563882038921757 37634381780461455764595659)
        ·
          refine ⟨56451572670692183646893489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37634381780461455764595659 56451572670692183646893489)
          ·
            refine ⟨42338679503019137735170117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56451572670692183646893489 42338679503019137735170117)
            ·
              refine ⟨7938502406816088325344397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42338679503019137735170117 7938502406816088325344397)
              ·
                refine ⟨2976938402556033122004149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7938502406816088325344397 2976938402556033122004149)
                ·
                  refine ⟨279087975239628105187889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2976938402556033122004149 279087975239628105187889)
                  ·
                    rfl

theorem cell23_4891697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4, 3, 5].length) (baseStart_4891697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4891697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4891697 prefixEnd_4891697 := by exact prefixLift 4891697
  have htrace : WordTrace (prefixWord ++ tailWord_4891697) baseStart_4891697 baseEnd_4891697 := by
    simpa [prefixWord, tailWord_4891697, baseEnd_4891697] using wordTrace_append hprefix tailTrace_4891697
  have hstable : (prefixWord ++ tailWord_4891697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4891697).length < 2 ^ (prefixWord ++ tailWord_4891697).sum := by decide
  have hdescent : baseEnd_4891697 < baseStart_4891697 := by decide
  rcases family_descends (prefixWord ++ tailWord_4891697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4891723 : List Nat := [1, 1, 1, 1, 3, 1, 2, 1, 4, 8]
def baseStart_4891723 : Nat := 118140960795 + 4891723 * 2 ^ 59
def prefixEnd_4891723 : Nat := 4983230072969 + 3 ^ 40 * 4891723 * 2
def baseEnd_4891723 : Nat := 837268375884556614988627

theorem tailTrace_4891723 : CollatzResearch.WordTrace tailWord_4891723 prefixEnd_4891723 837268375884556614988627 := by
  unfold tailWord_4891723
  simp only [CollatzResearch.WordTrace]
  refine ⟨178415795257130485620751823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118943863504753657080501215 178415795257130485620751823)
  ·
    refine ⟨267623692885695728431127735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178415795257130485620751823 267623692885695728431127735)
    ·
      refine ⟨401435539328543592646691603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 267623692885695728431127735 401435539328543592646691603)
      ·
        refine ⟨602153308992815388970037405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 401435539328543592646691603 602153308992815388970037405)
        ·
          refine ⟨225807490872305770863764027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 602153308992815388970037405 225807490872305770863764027)
          ·
            refine ⟨338711236308458656295646041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 225807490872305770863764027 338711236308458656295646041)
            ·
              refine ⟨254033427231343992221734531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 338711236308458656295646041 254033427231343992221734531)
              ·
                refine ⟨381050140847015988332601797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 254033427231343992221734531 381050140847015988332601797)
                ·
                  refine ⟨71446901408815497812362837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 381050140847015988332601797 71446901408815497812362837)
                  ·
                    refine ⟨837268375884556614988627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 71446901408815497812362837 837268375884556614988627)
                    ·
                      rfl

theorem cell23_4891723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 4, 8].length) (baseStart_4891723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4891723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4891723 prefixEnd_4891723 := by exact prefixLift 4891723
  have htrace : WordTrace (prefixWord ++ tailWord_4891723) baseStart_4891723 baseEnd_4891723 := by
    simpa [prefixWord, tailWord_4891723, baseEnd_4891723] using wordTrace_append hprefix tailTrace_4891723
  have hstable : (prefixWord ++ tailWord_4891723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4891723).length < 2 ^ (prefixWord ++ tailWord_4891723).sum := by decide
  have hdescent : baseEnd_4891723 < baseStart_4891723 := by decide
  rcases family_descends (prefixWord ++ tailWord_4891723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4891740 : List Nat := [2, 2, 4, 1, 1, 1, 1, 1, 2, 8]
def baseStart_4891740 : Nat := 118140960795 + 4891740 * 2 ^ 59
def prefixEnd_4891740 : Nat := 4983230072969 + 3 ^ 40 * 4891740 * 2
def baseEnd_4891740 : Nat := 837271285608265426151101

theorem tailTrace_4891740 : CollatzResearch.WordTrace tailWord_4891740 prefixEnd_4891740 837271285608265426151101 := by
  unfold tailWord_4891740
  simp only [CollatzResearch.WordTrace]
  refine ⟨89208207649034448762060337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118944276865379265016080449 89208207649034448762060337)
  ·
    refine ⟨66906155736775836571545253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89208207649034448762060337 66906155736775836571545253)
    ·
      refine ⟨12544904200645469357164735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66906155736775836571545253 12544904200645469357164735)
      ·
        refine ⟨18817356300968204035747103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12544904200645469357164735 18817356300968204035747103)
        ·
          refine ⟨28226034451452306053620655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18817356300968204035747103 28226034451452306053620655)
          ·
            refine ⟨42339051677178459080430983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28226034451452306053620655 42339051677178459080430983)
            ·
              refine ⟨63508577515767688620646475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42339051677178459080430983 63508577515767688620646475)
              ·
                refine ⟨95262866273651532930969713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63508577515767688620646475 95262866273651532930969713)
                ·
                  refine ⟨71447149705238649698227285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 95262866273651532930969713 71447149705238649698227285)
                  ·
                    refine ⟨837271285608265426151101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 71447149705238649698227285 837271285608265426151101)
                    ·
                      rfl

theorem cell23_4891740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 2, 8].length) (baseStart_4891740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4891740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4891740 prefixEnd_4891740 := by exact prefixLift 4891740
  have htrace : WordTrace (prefixWord ++ tailWord_4891740) baseStart_4891740 baseEnd_4891740 := by
    simpa [prefixWord, tailWord_4891740, baseEnd_4891740] using wordTrace_append hprefix tailTrace_4891740
  have hstable : (prefixWord ++ tailWord_4891740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4891740).length < 2 ^ (prefixWord ++ tailWord_4891740).sum := by decide
  have hdescent : baseEnd_4891740 < baseStart_4891740 := by decide
  rcases family_descends (prefixWord ++ tailWord_4891740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4891767 : List Nat := [1, 1, 3, 1, 1, 4, 3, 2, 2, 2, 3]
def baseStart_4891767 : Nat := 118140960795 + 4891767 * 2 ^ 59
def prefixEnd_4891767 : Nat := 4983230072969 + 3 ^ 40 * 4891767 * 2
def baseEnd_4891767 : Nat := 2511827720802467672815679

theorem tailTrace_4891767 : CollatzResearch.WordTrace tailWord_4891767 prefixEnd_4891767 2511827720802467672815679 := by
  unfold tailWord_4891767
  simp only [CollatzResearch.WordTrace]
  refine ⟨178417400068971081135353555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118944933379314054090235703 178417400068971081135353555)
  ·
    refine ⟨267626100103456621703030333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178417400068971081135353555 267626100103456621703030333)
    ·
      refine ⟨100359787538796233138636375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 267626100103456621703030333 100359787538796233138636375)
      ·
        refine ⟨150539681308194349707954563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100359787538796233138636375 150539681308194349707954563)
        ·
          refine ⟨225809521962291524561931845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150539681308194349707954563 225809521962291524561931845)
          ·
            refine ⟨42339285367929660855362221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 225809521962291524561931845 42339285367929660855362221)
            ·
              refine ⟨15877232012973622820760833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42339285367929660855362221 15877232012973622820760833)
              ·
                refine ⟨11907924009730217115570625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15877232012973622820760833 11907924009730217115570625)
                ·
                  refine ⟨8930943007297662836677969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11907924009730217115570625 8930943007297662836677969)
                  ·
                    refine ⟨6698207255473247127508477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8930943007297662836677969 6698207255473247127508477)
                    ·
                      refine ⟨2511827720802467672815679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6698207255473247127508477 2511827720802467672815679)
                      ·
                        rfl

theorem cell23_4891767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 2, 2, 2, 3].length) (baseStart_4891767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4891767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4891767 prefixEnd_4891767 := by exact prefixLift 4891767
  have htrace : WordTrace (prefixWord ++ tailWord_4891767) baseStart_4891767 baseEnd_4891767 := by
    simpa [prefixWord, tailWord_4891767, baseEnd_4891767] using wordTrace_append hprefix tailTrace_4891767
  have hstable : (prefixWord ++ tailWord_4891767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4891767).length < 2 ^ (prefixWord ++ tailWord_4891767).sum := by decide
  have hdescent : baseEnd_4891767 < baseStart_4891767 := by decide
  rcases family_descends (prefixWord ++ tailWord_4891767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4891831 : List Nat := [1, 1, 3, 1, 4, 1, 3, 4, 1, 1, 3]
def baseStart_4891831 : Nat := 118140960795 + 4891831 * 2 ^ 59
def prefixEnd_4891831 : Nat := 4983230072969 + 3 ^ 40 * 4891831 * 2
def baseEnd_4891831 : Nat := 2511860583564355422415385

theorem tailTrace_4891831 : CollatzResearch.WordTrace tailWord_4891831 prefixEnd_4891831 2511860583564355422415385 := by
  unfold tailWord_4891831
  simp only [CollatzResearch.WordTrace]
  refine ⟨178419734340739220065683347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118946489560492813377122231 178419734340739220065683347)
  ·
    refine ⟨267629601511108830098525021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178419734340739220065683347 267629601511108830098525021)
    ·
      refine ⟨100361100566665811286946883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 267629601511108830098525021 100361100566665811286946883)
      ·
        refine ⟨150541650849998716930420325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100361100566665811286946883 150541650849998716930420325)
        ·
          refine ⟨28226559534374759424453811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 150541650849998716930420325 28226559534374759424453811)
          ·
            refine ⟨42339839301562139136680717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28226559534374759424453811 42339839301562139136680717)
            ·
              refine ⟨15877439738085802176255269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42339839301562139136680717 15877439738085802176255269)
              ·
                refine ⟨2977019950891087908047863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15877439738085802176255269 2977019950891087908047863)
                ·
                  refine ⟨4465529926336631862071795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2977019950891087908047863 4465529926336631862071795)
                  ·
                    refine ⟨6698294889504947793107693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4465529926336631862071795 6698294889504947793107693)
                    ·
                      refine ⟨2511860583564355422415385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6698294889504947793107693 2511860583564355422415385)
                      ·
                        rfl

theorem cell23_4891831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 4, 1, 1, 3].length) (baseStart_4891831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4891831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4891831 prefixEnd_4891831 := by exact prefixLift 4891831
  have htrace : WordTrace (prefixWord ++ tailWord_4891831) baseStart_4891831 baseEnd_4891831 := by
    simpa [prefixWord, tailWord_4891831, baseEnd_4891831] using wordTrace_append hprefix tailTrace_4891831
  have hstable : (prefixWord ++ tailWord_4891831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4891831).length < 2 ^ (prefixWord ++ tailWord_4891831).sum := by decide
  have hdescent : baseEnd_4891831 < baseStart_4891831 := by decide
  rcases family_descends (prefixWord ++ tailWord_4891831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
