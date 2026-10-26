import V185TrunkScan20Chunk051

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_316465 : List Nat := [1, 2, 2, 3, 1, 2, 2, 7]
def baseStart_316465 : Nat := 118140960795 + 316465 * 2 ^ 59
def prefixEnd_316465 : Nat := 4983230072969 + 3 ^ 40 * 316465 * 2
def baseEnd_316465 : Nat := 48147749725988018646551

theorem tailTrace_316465 : CollatzResearch.WordTrace tailWord_316465 prefixEnd_316465 48147749725988018646551 := by
  unfold tailWord_316465
  simp only [CollatzResearch.WordTrace]
  refine ⟨11542426798508827764134849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7694951199005885176089899 11542426798508827764134849)
  ·
    refine ⟨8656820098881620823101137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11542426798508827764134849 8656820098881620823101137)
    ·
      refine ⟨6492615074161215617325853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8656820098881620823101137 6492615074161215617325853)
      ·
        refine ⟨2434730652810455856497195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6492615074161215617325853 2434730652810455856497195)
        ·
          refine ⟨3652095979215683784745793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2434730652810455856497195 3652095979215683784745793)
          ·
            refine ⟨2739071984411762838559345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3652095979215683784745793 2739071984411762838559345)
            ·
              refine ⟨2054303988308822128919509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2739071984411762838559345 2054303988308822128919509)
              ·
                refine ⟨48147749725988018646551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2054303988308822128919509 48147749725988018646551)
                ·
                  rfl

theorem cell20_316465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 7].length) (baseStart_316465 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_316465 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_316465 prefixEnd_316465 := by exact prefixLift 316465
  have htrace : WordTrace (prefixWord ++ tailWord_316465) baseStart_316465 baseEnd_316465 := by
    simpa [prefixWord, tailWord_316465, baseEnd_316465] using wordTrace_append hprefix tailTrace_316465
  have hstable : (prefixWord ++ tailWord_316465).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316465).length < 2 ^ (prefixWord ++ tailWord_316465).sum := by decide
  have hdescent : baseEnd_316465 < baseStart_316465 := by decide
  rcases family_descends (prefixWord ++ tailWord_316465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316478 : List Nat := [4, 2, 1, 3, 1, 3, 2, 4]
def baseStart_316478 : Nat := 118140960795 + 316478 * 2 ^ 59
def prefixEnd_316478 : Nat := 4983230072969 + 3 ^ 40 * 316478 * 2
def baseEnd_316478 : Nat := 48149727577397929502089

theorem tailTrace_316478 : CollatzResearch.WordTrace tailWord_316478 prefixEnd_316478 48149727577397929502089 := by
  unfold tailWord_316478
  simp only [CollatzResearch.WordTrace]
  refine ⟨1442862618432716373044761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7695267298307820656238725 1442862618432716373044761)
  ·
    refine ⟨1082146963824537279783571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1442862618432716373044761 1082146963824537279783571)
    ·
      refine ⟨1623220445736805919675357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1082146963824537279783571 1623220445736805919675357)
      ·
        refine ⟨608707667151302219878259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1623220445736805919675357 608707667151302219878259)
        ·
          refine ⟨913061500726953329817389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 608707667151302219878259 913061500726953329817389)
          ·
            refine ⟨342398062772607498681521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 913061500726953329817389 342398062772607498681521)
            ·
              refine ⟨256798547079455624011141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 342398062772607498681521 256798547079455624011141)
              ·
                refine ⟨48149727577397929502089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 256798547079455624011141 48149727577397929502089)
                ·
                  rfl

theorem cell20_316478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 2, 4].length) (baseStart_316478 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_316478 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_316478 prefixEnd_316478 := by exact prefixLift 316478
  have htrace : WordTrace (prefixWord ++ tailWord_316478) baseStart_316478 baseEnd_316478 := by
    simpa [prefixWord, tailWord_316478, baseEnd_316478] using wordTrace_append hprefix tailTrace_316478
  have hstable : (prefixWord ++ tailWord_316478).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316478).length < 2 ^ (prefixWord ++ tailWord_316478).sum := by decide
  have hdescent : baseEnd_316478 < baseStart_316478 := by decide
  rcases family_descends (prefixWord ++ tailWord_316478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316509 : List Nat := [1, 4, 4, 1, 2, 2, 1, 1, 4]
def baseStart_316509 : Nat := 118140960795 + 316509 * 2 ^ 59
def prefixEnd_316509 : Nat := 4983230072969 + 3 ^ 40 * 316509 * 2
def baseEnd_316509 : Nat := 144463331976895458472807

theorem tailTrace_316509 : CollatzResearch.WordTrace tailWord_316509 prefixEnd_316509 144463331976895458472807 := by
  unfold tailWord_316509
  simp only [CollatzResearch.WordTrace]
  refine ⟨11544031610349423278736581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7696021073566282185824387 11544031610349423278736581)
  ·
    refine ⟨2164505926940516864763109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11544031610349423278736581 2164505926940516864763109)
    ·
      refine ⟨405844861301346912143083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2164505926940516864763109 405844861301346912143083)
      ·
        refine ⟨608767291952020368214625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 405844861301346912143083 608767291952020368214625)
        ·
          refine ⟨456575468964015276160969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 608767291952020368214625 456575468964015276160969)
          ·
            refine ⟨342431601723011457120727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 456575468964015276160969 342431601723011457120727)
            ·
              refine ⟨513647402584517185681091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 342431601723011457120727 513647402584517185681091)
              ·
                refine ⟨770471103876775778521637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 513647402584517185681091 770471103876775778521637)
                ·
                  refine ⟨144463331976895458472807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 770471103876775778521637 144463331976895458472807)
                  ·
                    rfl

theorem cell20_316509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 1, 1, 4].length) (baseStart_316509 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_316509 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_316509 prefixEnd_316509 := by exact prefixLift 316509
  have htrace : WordTrace (prefixWord ++ tailWord_316509) baseStart_316509 baseEnd_316509 := by
    simpa [prefixWord, tailWord_316509, baseEnd_316509] using wordTrace_append hprefix tailTrace_316509
  have hstable : (prefixWord ++ tailWord_316509).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316509).length < 2 ^ (prefixWord ++ tailWord_316509).sum := by decide
  have hdescent : baseEnd_316509 < baseStart_316509 := by decide
  rcases family_descends (prefixWord ++ tailWord_316509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316513 : List Nat := [1, 2, 3, 1, 1, 2, 2, 6, 2]
def baseStart_316513 : Nat := 118140960795 + 316513 * 2 ^ 59
def prefixEnd_316513 : Nat := 4983230072969 + 3 ^ 40 * 316513 * 2
def baseEnd_316513 : Nat := 144465157685889222339457

theorem tailTrace_316513 : CollatzResearch.WordTrace tailWord_316513 prefixEnd_316513 144465157685889222339457 := by
  unfold tailWord_316513
  simp only [CollatzResearch.WordTrace]
  refine ⟨11544177502334931961882193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7696118334889954641254795 11544177502334931961882193)
  ·
    refine ⟨8658133126751198971411645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11544177502334931961882193 8658133126751198971411645)
    ·
      refine ⟨3246799922531699614279367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8658133126751198971411645 3246799922531699614279367)
      ·
        refine ⟨4870199883797549421419051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3246799922531699614279367 4870199883797549421419051)
        ·
          refine ⟨7305299825696324132128577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4870199883797549421419051 7305299825696324132128577)
          ·
            refine ⟨5478974869272243099096433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7305299825696324132128577 5478974869272243099096433)
            ·
              refine ⟨4109231151954182324322325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5478974869272243099096433 4109231151954182324322325)
              ·
                refine ⟨192620210247852296452609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4109231151954182324322325 192620210247852296452609)
                ·
                  refine ⟨144465157685889222339457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 192620210247852296452609 144465157685889222339457)
                  ·
                    rfl

theorem cell20_316513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 6, 2].length) (baseStart_316513 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_316513 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_316513 prefixEnd_316513 := by exact prefixLift 316513
  have htrace : WordTrace (prefixWord ++ tailWord_316513) baseStart_316513 baseEnd_316513 := by
    simpa [prefixWord, tailWord_316513, baseEnd_316513] using wordTrace_append hprefix tailTrace_316513
  have hstable : (prefixWord ++ tailWord_316513).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316513).length < 2 ^ (prefixWord ++ tailWord_316513).sum := by decide
  have hdescent : baseEnd_316513 < baseStart_316513 := by decide
  rcases family_descends (prefixWord ++ tailWord_316513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316527 : List Nat := [1, 1, 2, 1, 3, 3, 3, 3, 3]
def baseStart_316527 : Nat := 118140960795 + 316527 * 2 ^ 59
def prefixEnd_316527 : Nat := 4983230072969 + 3 ^ 40 * 316527 * 2
def baseEnd_316527 : Nat := 144471547667367395872733

theorem tailTrace_316527 : CollatzResearch.WordTrace tailWord_316527 prefixEnd_316527 144471547667367395872733 := by
  unfold tailWord_316527
  simp only [CollatzResearch.WordTrace]
  refine ⟨11544688124284212352891835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7696458749522808235261223 11544688124284212352891835)
  ·
    refine ⟨17317032186426318529337753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11544688124284212352891835 17317032186426318529337753)
    ·
      refine ⟨12987774139819738897003315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17317032186426318529337753 12987774139819738897003315)
      ·
        refine ⟨19481661209729608345504973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12987774139819738897003315 19481661209729608345504973)
        ·
          refine ⟨7305622953648603129564365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19481661209729608345504973 7305622953648603129564365)
          ·
            refine ⟨2739608607618226173586637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7305622953648603129564365 2739608607618226173586637)
            ·
              refine ⟨1027353227856834815094989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2739608607618226173586637 1027353227856834815094989)
              ·
                refine ⟨385257460446313055660621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1027353227856834815094989 385257460446313055660621)
                ·
                  refine ⟨144471547667367395872733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 385257460446313055660621 144471547667367395872733)
                  ·
                    rfl

theorem cell20_316527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 3, 3].length) (baseStart_316527 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_316527 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_316527 prefixEnd_316527 := by exact prefixLift 316527
  have htrace : WordTrace (prefixWord ++ tailWord_316527) baseStart_316527 baseEnd_316527 := by
    simpa [prefixWord, tailWord_316527, baseEnd_316527] using wordTrace_append hprefix tailTrace_316527
  have hstable : (prefixWord ++ tailWord_316527).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316527).length < 2 ^ (prefixWord ++ tailWord_316527).sum := by decide
  have hdescent : baseEnd_316527 < baseStart_316527 := by decide
  rcases family_descends (prefixWord ++ tailWord_316527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316541 : List Nat := [1, 4, 1, 1, 3, 1, 1, 8]
def baseStart_316541 : Nat := 118140960795 + 316541 * 2 ^ 59
def prefixEnd_316541 : Nat := 4983230072969 + 3 ^ 40 * 316541 * 2
def baseEnd_316541 : Nat := 48159312549615189802003

theorem tailTrace_316541 : CollatzResearch.WordTrace tailWord_316541 prefixEnd_316541 48159312549615189802003 := by
  unfold tailWord_316541
  simp only [CollatzResearch.WordTrace]
  refine ⟨11545198746233492743901477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7696799164155661829267651 11545198746233492743901477)
  ·
    refine ⟨2164724764918779889481527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11545198746233492743901477 2164724764918779889481527)
    ·
      refine ⟨3247087147378169834222291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2164724764918779889481527 3247087147378169834222291)
      ·
        refine ⟨4870630721067254751333437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3247087147378169834222291 4870630721067254751333437)
        ·
          refine ⟨1826486520400220531750039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4870630721067254751333437 1826486520400220531750039)
          ·
            refine ⟨2739729780600330797625059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1826486520400220531750039 2739729780600330797625059)
            ·
              refine ⟨4109594670900496196437589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2739729780600330797625059 4109594670900496196437589)
              ·
                refine ⟨48159312549615189802003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4109594670900496196437589 48159312549615189802003)
                ·
                  rfl

theorem cell20_316541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 8].length) (baseStart_316541 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_316541 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_316541 prefixEnd_316541 := by exact prefixLift 316541
  have htrace : WordTrace (prefixWord ++ tailWord_316541) baseStart_316541 baseEnd_316541 := by
    simpa [prefixWord, tailWord_316541, baseEnd_316541] using wordTrace_append hprefix tailTrace_316541
  have hstable : (prefixWord ++ tailWord_316541).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316541).length < 2 ^ (prefixWord ++ tailWord_316541).sum := by decide
  have hdescent : baseEnd_316541 < baseStart_316541 := by decide
  rcases family_descends (prefixWord ++ tailWord_316541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316551 : List Nat := [1, 1, 4, 2, 1, 1, 1, 7, 2]
def baseStart_316551 : Nat := 118140960795 + 316551 * 2 ^ 59
def prefixEnd_316551 : Nat := 4983230072969 + 3 ^ 40 * 316551 * 2
def baseEnd_316551 : Nat := 144482501921329979072635

theorem tailTrace_316551 : CollatzResearch.WordTrace tailWord_316551 prefixEnd_316551 144482501921329979072635 := by
  unfold tailWord_316551
  simp only [CollatzResearch.WordTrace]
  refine ⟨11545563476197264451765507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7697042317464842967843671 11545563476197264451765507)
  ·
    refine ⟨17318345214295896677648261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11545563476197264451765507 17318345214295896677648261)
    ·
      refine ⟨3247189727680480627059049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17318345214295896677648261 3247189727680480627059049)
      ·
        refine ⟨2435392295760360470294287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3247189727680480627059049 2435392295760360470294287)
        ·
          refine ⟨3653088443640540705441431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2435392295760360470294287 3653088443640540705441431)
          ·
            refine ⟨5479632665460811058162147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3653088443640540705441431 5479632665460811058162147)
            ·
              refine ⟨8219448998191216587243221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5479632665460811058162147 8219448998191216587243221)
              ·
                refine ⟨192643335895106638763513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 8219448998191216587243221 192643335895106638763513)
                ·
                  refine ⟨144482501921329979072635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 192643335895106638763513 144482501921329979072635)
                  ·
                    rfl

theorem cell20_316551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 7, 2].length) (baseStart_316551 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_316551 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_316551 prefixEnd_316551 := by exact prefixLift 316551
  have htrace : WordTrace (prefixWord ++ tailWord_316551) baseStart_316551 baseEnd_316551 := by
    simpa [prefixWord, tailWord_316551, baseEnd_316551] using wordTrace_append hprefix tailTrace_316551
  have hstable : (prefixWord ++ tailWord_316551).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316551).length < 2 ^ (prefixWord ++ tailWord_316551).sum := by decide
  have hdescent : baseEnd_316551 < baseStart_316551 := by decide
  rcases family_descends (prefixWord ++ tailWord_316551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316568 : List Nat := [2, 1, 2, 4, 2, 2, 1, 4, 2]
def baseStart_316568 : Nat := 118140960795 + 316568 * 2 ^ 59
def prefixEnd_316568 : Nat := 4983230072969 + 3 ^ 40 * 316568 * 2
def baseEnd_316568 : Nat := 144490261184553475505899

theorem tailTrace_316568 : CollatzResearch.WordTrace tailWord_316568 prefixEnd_316568 144490261184553475505899 := by
  unfold tailWord_316568
  simp only [CollatzResearch.WordTrace]
  refine ⟨5773091758567838177567179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7697455678090450903422905 5773091758567838177567179)
  ·
    refine ⟨8659637637851757266350769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5773091758567838177567179 8659637637851757266350769)
    ·
      refine ⟨6494728228388817949763077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8659637637851757266350769 6494728228388817949763077)
      ·
        refine ⟨1217761542822903365580577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6494728228388817949763077 1217761542822903365580577)
        ·
          refine ⟨913321157117177524185433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1217761542822903365580577 913321157117177524185433)
          ·
            refine ⟨684990867837883143139075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 913321157117177524185433 684990867837883143139075)
            ·
              refine ⟨1027486301756824714708613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 684990867837883143139075 1027486301756824714708613)
              ·
                refine ⟨192653681579404634007865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1027486301756824714708613 192653681579404634007865)
                ·
                  refine ⟨144490261184553475505899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 192653681579404634007865 144490261184553475505899)
                  ·
                    rfl

theorem cell20_316568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 4, 2].length) (baseStart_316568 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_316568 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_316568 prefixEnd_316568 := by exact prefixLift 316568
  have htrace : WordTrace (prefixWord ++ tailWord_316568) baseStart_316568 baseEnd_316568 := by
    simpa [prefixWord, tailWord_316568, baseEnd_316568] using wordTrace_append hprefix tailTrace_316568
  have hstable : (prefixWord ++ tailWord_316568).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316568).length < 2 ^ (prefixWord ++ tailWord_316568).sum := by decide
  have hdescent : baseEnd_316568 < baseStart_316568 := by decide
  rcases family_descends (prefixWord ++ tailWord_316568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316575 : List Nat := [1, 1, 2, 6, 2, 2, 1, 5]
def baseStart_316575 : Nat := 118140960795 + 316575 * 2 ^ 59
def prefixEnd_316575 : Nat := 4983230072969 + 3 ^ 40 * 316575 * 2
def baseEnd_316575 : Nat := 48164485391764187424179

theorem tailTrace_316575 : CollatzResearch.WordTrace tailWord_316575 prefixEnd_316575 48164485391764187424179 := by
  unfold tailWord_316575
  simp only [CollatzResearch.WordTrace]
  refine ⟨11546438828110316550639179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7697625885406877700426119 11546438828110316550639179)
  ·
    refine ⟨17319658242165474825958769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11546438828110316550639179 17319658242165474825958769)
    ·
      refine ⟨12989743681624106119469077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17319658242165474825958769 12989743681624106119469077)
      ·
        refine ⟨608894235076129974350113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 12989743681624106119469077 608894235076129974350113)
        ·
          refine ⟨456670676307097480762585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 608894235076129974350113 456670676307097480762585)
          ·
            refine ⟨342503007230323110571939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 456670676307097480762585 342503007230323110571939)
            ·
              refine ⟨513754510845484665857909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 342503007230323110571939 513754510845484665857909)
              ·
                refine ⟨48164485391764187424179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 513754510845484665857909 48164485391764187424179)
                ·
                  rfl

theorem cell20_316575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 1, 5].length) (baseStart_316575 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_316575 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_316575 prefixEnd_316575 := by exact prefixLift 316575
  have htrace : WordTrace (prefixWord ++ tailWord_316575) baseStart_316575 baseEnd_316575 := by
    simpa [prefixWord, tailWord_316575, baseEnd_316575] using wordTrace_append hprefix tailTrace_316575
  have hstable : (prefixWord ++ tailWord_316575).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316575).length < 2 ^ (prefixWord ++ tailWord_316575).sum := by decide
  have hdescent : baseEnd_316575 < baseStart_316575 := by decide
  rcases family_descends (prefixWord ++ tailWord_316575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316606 : List Nat := [4, 2, 1, 1, 3, 1, 1, 5, 2]
def baseStart_316606 : Nat := 118140960795 + 316606 * 2 ^ 59
def prefixEnd_316606 : Nat := 4983230072969 + 3 ^ 40 * 316606 * 2
def baseEnd_316606 : Nat := 144507605419994232239077

theorem tailTrace_316606 : CollatzResearch.WordTrace tailWord_316606 prefixEnd_316606 144507605419994232239077 := by
  unfold tailWord_316606
  simp only [CollatzResearch.WordTrace]
  refine ⟨1443446186374751105627209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7698379660665339230011781 1443446186374751105627209)
  ·
    refine ⟨1082584639781063329220407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1443446186374751105627209 1082584639781063329220407)
    ·
      refine ⟨1623876959671594993830611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1082584639781063329220407 1623876959671594993830611)
      ·
        refine ⟨2435815439507392490745917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1623876959671594993830611 2435815439507392490745917)
        ·
          refine ⟨913430789815272184029719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2435815439507392490745917 913430789815272184029719)
          ·
            refine ⟨1370146184722908276044579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 913430789815272184029719 1370146184722908276044579)
            ·
              refine ⟨2055219277084362414066869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1370146184722908276044579 2055219277084362414066869)
              ·
                refine ⟨192676807226658976318769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2055219277084362414066869 192676807226658976318769)
                ·
                  refine ⟨144507605419994232239077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 192676807226658976318769 144507605419994232239077)
                  ·
                    rfl

theorem cell20_316606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 5, 2].length) (baseStart_316606 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_316606 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_316606 prefixEnd_316606 := by exact prefixLift 316606
  have htrace : WordTrace (prefixWord ++ tailWord_316606) baseStart_316606 baseEnd_316606 := by
    simpa [prefixWord, tailWord_316606, baseEnd_316606] using wordTrace_append hprefix tailTrace_316606
  have hstable : (prefixWord ++ tailWord_316606).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316606).length < 2 ^ (prefixWord ++ tailWord_316606).sum := by decide
  have hdescent : baseEnd_316606 < baseStart_316606 := by decide
  rcases family_descends (prefixWord ++ tailWord_316606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316648 : List Nat := [2, 1, 4, 1, 2, 1, 1, 4, 4]
def baseStart_316648 : Nat := 118140960795 + 316648 * 2 ^ 59
def prefixEnd_316648 : Nat := 4983230072969 + 3 ^ 40 * 316648 * 2
def baseEnd_316648 : Nat := 144526775364428752838905

theorem tailTrace_316648 : CollatzResearch.WordTrace tailWord_316648 prefixEnd_316648 144526775364428752838905 := by
  unfold tailWord_316648
  simp only [CollatzResearch.WordTrace]
  refine ⟨5774550678422925009023299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7699400904563900012031065 5774550678422925009023299)
  ·
    refine ⟨8661826017634387513534949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5774550678422925009023299 8661826017634387513534949)
    ·
      refine ⟨1624092378306447658787803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8661826017634387513534949 1624092378306447658787803)
      ·
        refine ⟨2436138567459671488181705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1624092378306447658787803 2436138567459671488181705)
        ·
          refine ⟨1827103925594753616136279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2436138567459671488181705 1827103925594753616136279)
          ·
            refine ⟨2740655888392130424204419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1827103925594753616136279 2740655888392130424204419)
            ·
              refine ⟨4110983832588195636306629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2740655888392130424204419 4110983832588195636306629)
              ·
                refine ⟨770809468610286681807493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4110983832588195636306629 770809468610286681807493)
                ·
                  refine ⟨144526775364428752838905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 770809468610286681807493 144526775364428752838905)
                  ·
                    rfl

theorem cell20_316648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 4, 4].length) (baseStart_316648 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_316648 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_316648 prefixEnd_316648 := by exact prefixLift 316648
  have htrace : WordTrace (prefixWord ++ tailWord_316648) baseStart_316648 baseEnd_316648 := by
    simpa [prefixWord, tailWord_316648, baseEnd_316648] using wordTrace_append hprefix tailTrace_316648
  have hstable : (prefixWord ++ tailWord_316648).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316648).length < 2 ^ (prefixWord ++ tailWord_316648).sum := by decide
  have hdescent : baseEnd_316648 < baseStart_316648 := by decide
  rcases family_descends (prefixWord ++ tailWord_316648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316696 : List Nat := [2, 1, 2, 3, 1, 3, 4, 1, 3]
def baseStart_316696 : Nat := 118140960795 + 316696 * 2 ^ 59
def prefixEnd_316696 : Nat := 4983230072969 + 3 ^ 40 * 316696 * 2
def baseEnd_316696 : Nat := 144548683872353919238709

theorem tailTrace_316696 : CollatzResearch.WordTrace tailWord_316696 prefixEnd_316696 144548683872353919238709 := by
  unfold tailWord_316696
  simp only [CollatzResearch.WordTrace]
  refine ⟨5775426030335977107896971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7700568040447969477195961 5775426030335977107896971)
  ·
    refine ⟨8663139045503965661845457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5775426030335977107896971 8663139045503965661845457)
    ·
      refine ⟨6497354284127974246384093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8663139045503965661845457 6497354284127974246384093)
      ·
        refine ⟨2436507856547990342394035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6497354284127974246384093 2436507856547990342394035)
        ·
          refine ⟨3654761784821985513591053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2436507856547990342394035 3654761784821985513591053)
          ·
            refine ⟨1370535669308244567596645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3654761784821985513591053 1370535669308244567596645)
            ·
              refine ⟨256975437995295856424371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1370535669308244567596645 256975437995295856424371)
              ·
                refine ⟨385463156992943784636557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 256975437995295856424371 385463156992943784636557)
                ·
                  refine ⟨144548683872353919238709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 385463156992943784636557 144548683872353919238709)
                  ·
                    rfl

theorem cell20_316696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 4, 1, 3].length) (baseStart_316696 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_316696 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_316696 prefixEnd_316696 := by exact prefixLift 316696
  have htrace : WordTrace (prefixWord ++ tailWord_316696) baseStart_316696 baseEnd_316696 := by
    simpa [prefixWord, tailWord_316696, baseEnd_316696] using wordTrace_append hprefix tailTrace_316696
  have hstable : (prefixWord ++ tailWord_316696).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316696).length < 2 ^ (prefixWord ++ tailWord_316696).sum := by decide
  have hdescent : baseEnd_316696 < baseStart_316696 := by decide
  rcases family_descends (prefixWord ++ tailWord_316696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316733 : List Nat := [1, 4, 1, 5, 2, 1, 2, 2, 2]
def baseStart_316733 : Nat := 118140960795 + 316733 * 2 ^ 59
def prefixEnd_316733 : Nat := 4983230072969 + 3 ^ 40 * 316733 * 2
def baseEnd_316733 : Nat := 144565571680546235005225

theorem tailTrace_316733 : CollatzResearch.WordTrace tailWord_316733 prefixEnd_316733 144565571680546235005225 := by
  unfold tailWord_316733
  simp only [CollatzResearch.WordTrace]
  refine ⟨11552201561537909534890853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7701467707691939689927235 11552201561537909534890853)
  ·
    refine ⟨2166037792788358037792035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11552201561537909534890853 2166037792788358037792035)
    ·
      refine ⟨3249056689182537056688053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2166037792788358037792035 3249056689182537056688053)
      ·
        refine ⟨304599064610862849064505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3249056689182537056688053 304599064610862849064505)
        ·
          refine ⟨228449298458147136798379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 304599064610862849064505 228449298458147136798379)
          ·
            refine ⟨342673947687220705197569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 228449298458147136798379 342673947687220705197569)
            ·
              refine ⟨257005460765415528898177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 342673947687220705197569 257005460765415528898177)
              ·
                refine ⟨192754095574061646673633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 257005460765415528898177 192754095574061646673633)
                ·
                  refine ⟨144565571680546235005225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 192754095574061646673633 144565571680546235005225)
                  ·
                    rfl

theorem cell20_316733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 2, 2, 2].length) (baseStart_316733 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_316733 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_316733 prefixEnd_316733 := by exact prefixLift 316733
  have htrace : WordTrace (prefixWord ++ tailWord_316733) baseStart_316733 baseEnd_316733 := by
    simpa [prefixWord, tailWord_316733, baseEnd_316733] using wordTrace_append hprefix tailTrace_316733
  have hstable : (prefixWord ++ tailWord_316733).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316733).length < 2 ^ (prefixWord ++ tailWord_316733).sum := by decide
  have hdescent : baseEnd_316733 < baseStart_316733 := by decide
  rcases family_descends (prefixWord ++ tailWord_316733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316734 : List Nat := [4, 2, 1, 2, 1, 1, 4, 2, 3]
def baseStart_316734 : Nat := 118140960795 + 316734 * 2 ^ 59
def prefixEnd_316734 : Nat := 4983230072969 + 3 ^ 40 * 316734 * 2
def baseEnd_316734 : Nat := 144566028107794675971887

theorem tailTrace_316734 : CollatzResearch.WordTrace tailWord_316734 prefixEnd_316734 144566028107794675971887 := by
  unfold tailWord_316734
  simp only [CollatzResearch.WordTrace]
  refine ⟨1444029754316785838209657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7701492023022857803784837 1444029754316785838209657)
  ·
    refine ⟨1083022315737589378657243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1444029754316785838209657 1083022315737589378657243)
    ·
      refine ⟨1624533473606384067985865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1083022315737589378657243 1624533473606384067985865)
      ·
        refine ⟨1218400105204788050989399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1624533473606384067985865 1218400105204788050989399)
        ·
          refine ⟨1827600157807182076484099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1218400105204788050989399 1827600157807182076484099)
          ·
            refine ⟨2741400236710773114726149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1827600157807182076484099 2741400236710773114726149)
            ·
              refine ⟨514012544383269959011153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2741400236710773114726149 514012544383269959011153)
              ·
                refine ⟨385509408287452469258365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 514012544383269959011153 385509408287452469258365)
                ·
                  refine ⟨144566028107794675971887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 385509408287452469258365 144566028107794675971887)
                  ·
                    rfl

theorem cell20_316734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 4, 2, 3].length) (baseStart_316734 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_316734 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_316734 prefixEnd_316734 := by exact prefixLift 316734
  have htrace : WordTrace (prefixWord ++ tailWord_316734) baseStart_316734 baseEnd_316734 := by
    simpa [prefixWord, tailWord_316734, baseEnd_316734] using wordTrace_append hprefix tailTrace_316734
  have hstable : (prefixWord ++ tailWord_316734).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316734).length < 2 ^ (prefixWord ++ tailWord_316734).sum := by decide
  have hdescent : baseEnd_316734 < baseStart_316734 := by decide
  rcases family_descends (prefixWord ++ tailWord_316734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316737 : List Nat := [1, 2, 5, 2, 1, 1, 4, 2, 2]
def baseStart_316737 : Nat := 118140960795 + 316737 * 2 ^ 59
def prefixEnd_316737 : Nat := 4983230072969 + 3 ^ 40 * 316737 * 2
def baseEnd_316737 : Nat := 144567397389539998871875

theorem tailTrace_316737 : CollatzResearch.WordTrace tailWord_316737 prefixEnd_316737 144567397389539998871875 := by
  unfold tailWord_316737
  simp only [CollatzResearch.WordTrace]
  refine ⟨11552347453523418218036465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7701564969015612145357643 11552347453523418218036465)
  ·
    refine ⟨8664260590142563663527349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11552347453523418218036465 8664260590142563663527349)
    ·
      refine ⟨812274430325865343455689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8664260590142563663527349 812274430325865343455689)
      ·
        refine ⟨609205822744399007591767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 812274430325865343455689 609205822744399007591767)
        ·
          refine ⟨913808734116598511387651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 609205822744399007591767 913808734116598511387651)
          ·
            refine ⟨1370713101174897767081477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 913808734116598511387651 1370713101174897767081477)
            ·
              refine ⟨257008706470293331327777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1370713101174897767081477 257008706470293331327777)
              ·
                refine ⟨192756529852719998495833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 257008706470293331327777 192756529852719998495833)
                ·
                  refine ⟨144567397389539998871875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 192756529852719998495833 144567397389539998871875)
                  ·
                    rfl

theorem cell20_316737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 4, 2, 2].length) (baseStart_316737 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_316737 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_316737 prefixEnd_316737 := by exact prefixLift 316737
  have htrace : WordTrace (prefixWord ++ tailWord_316737) baseStart_316737 baseEnd_316737 := by
    simpa [prefixWord, tailWord_316737, baseEnd_316737] using wordTrace_append hprefix tailTrace_316737
  have hstable : (prefixWord ++ tailWord_316737).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316737).length < 2 ^ (prefixWord ++ tailWord_316737).sum := by decide
  have hdescent : baseEnd_316737 < baseStart_316737 := by decide
  rcases family_descends (prefixWord ++ tailWord_316737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316748 : List Nat := [2, 2, 1, 3, 2, 4, 1, 5]
def baseStart_316748 : Nat := 118140960795 + 316748 * 2 ^ 59
def prefixEnd_316748 : Nat := 4983230072969 + 3 ^ 40 * 316748 * 2
def baseEnd_316748 : Nat := 48190806029757616501721

theorem tailTrace_316748 : CollatzResearch.WordTrace tailWord_316748 prefixEnd_316748 48190806029757616501721 := by
  unfold tailWord_316748
  simp only [CollatzResearch.WordTrace]
  refine ⟨5776374328241783548343449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7701832437655711397791265 5776374328241783548343449)
  ·
    refine ⟨4332280746181337661257587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5776374328241783548343449 4332280746181337661257587)
    ·
      refine ⟨6498421119272006491886381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4332280746181337661257587 6498421119272006491886381)
      ·
        refine ⟨2436907919727002434457393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6498421119272006491886381 2436907919727002434457393)
        ·
          refine ⟨1827680939795251825843045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2436907919727002434457393 1827680939795251825843045)
          ·
            refine ⟨342690176211609717345571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1827680939795251825843045 342690176211609717345571)
            ·
              refine ⟨514035264317414576018357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 342690176211609717345571 514035264317414576018357)
              ·
                refine ⟨48190806029757616501721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 514035264317414576018357 48190806029757616501721)
                ·
                  rfl

theorem cell20_316748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 1, 5].length) (baseStart_316748 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_316748 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_316748 prefixEnd_316748 := by exact prefixLift 316748
  have htrace : WordTrace (prefixWord ++ tailWord_316748) baseStart_316748 baseEnd_316748 := by
    simpa [prefixWord, tailWord_316748, baseEnd_316748] using wordTrace_append hprefix tailTrace_316748
  have hstable : (prefixWord ++ tailWord_316748).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316748).length < 2 ^ (prefixWord ++ tailWord_316748).sum := by decide
  have hdescent : baseEnd_316748 < baseStart_316748 := by decide
  rcases family_descends (prefixWord ++ tailWord_316748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316783 : List Nat := [1, 1, 2, 1, 3, 1, 3, 2, 6]
def baseStart_316783 : Nat := 118140960795 + 316783 * 2 ^ 59
def prefixEnd_316783 : Nat := 4983230072969 + 3 ^ 40 * 316783 * 2
def baseEnd_316783 : Nat := 144588393042968283338353

theorem tailTrace_316783 : CollatzResearch.WordTrace tailWord_316783 prefixEnd_316783 144588393042968283338353 := by
  unfold tailWord_316783
  simp only [CollatzResearch.WordTrace]
  refine ⟨11554025211356768074211003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7702683474237845382807335 11554025211356768074211003)
  ·
    refine ⟨17331037817035152111316505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11554025211356768074211003 17331037817035152111316505)
    ·
      refine ⟨12998278362776364083487379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17331037817035152111316505 12998278362776364083487379)
      ·
        refine ⟨19497417544164546125231069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12998278362776364083487379 19497417544164546125231069)
        ·
          refine ⟨7311531579061704796961651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19497417544164546125231069 7311531579061704796961651)
          ·
            refine ⟨10967297368592557195442477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7311531579061704796961651 10967297368592557195442477)
            ·
              refine ⟨4112736513222208948290929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10967297368592557195442477 4112736513222208948290929)
              ·
                refine ⟨3084552384916656711218197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4112736513222208948290929 3084552384916656711218197)
                ·
                  refine ⟨144588393042968283338353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3084552384916656711218197 144588393042968283338353)
                  ·
                    rfl

theorem cell20_316783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 2, 6].length) (baseStart_316783 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_316783 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_316783 prefixEnd_316783 := by exact prefixLift 316783
  have htrace : WordTrace (prefixWord ++ tailWord_316783) baseStart_316783 baseEnd_316783 := by
    simpa [prefixWord, tailWord_316783, baseEnd_316783] using wordTrace_append hprefix tailTrace_316783
  have hstable : (prefixWord ++ tailWord_316783).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316783).length < 2 ^ (prefixWord ++ tailWord_316783).sum := by decide
  have hdescent : baseEnd_316783 < baseStart_316783 := by decide
  rcases family_descends (prefixWord ++ tailWord_316783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316789 : List Nat := [1, 3, 4, 1, 3, 2, 1, 2, 3]
def baseStart_316789 : Nat := 118140960795 + 316789 * 2 ^ 59
def prefixEnd_316789 : Nat := 4983230072969 + 3 ^ 40 * 316789 * 2
def baseEnd_316789 : Nat := 144591131606458929138329

theorem tailTrace_316789 : CollatzResearch.WordTrace tailWord_316789 prefixEnd_316789 144591131606458929138329 := by
  unfold tailWord_316789
  simp only [CollatzResearch.WordTrace]
  refine ⟨11554244049335031098929421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7702829366223354065952947 11554244049335031098929421)
  ·
    refine ⟨4332841518500636662098533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11554244049335031098929421 4332841518500636662098533)
    ·
      refine ⟨812407784718869374143475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4332841518500636662098533 812407784718869374143475)
      ·
        refine ⟨1218611677078304061215213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 812407784718869374143475 1218611677078304061215213)
        ·
          refine ⟨456979378904364022955705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1218611677078304061215213 456979378904364022955705)
          ·
            refine ⟨342734534178273017216779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 456979378904364022955705 342734534178273017216779)
            ·
              refine ⟨514101801267409525825169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 342734534178273017216779 514101801267409525825169)
              ·
                refine ⟨385576350950557144368877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 514101801267409525825169 385576350950557144368877)
                ·
                  refine ⟨144591131606458929138329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 385576350950557144368877 144591131606458929138329)
                  ·
                    rfl

theorem cell20_316789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 1, 2, 3].length) (baseStart_316789 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_316789 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_316789 prefixEnd_316789 := by exact prefixLift 316789
  have htrace : WordTrace (prefixWord ++ tailWord_316789) baseStart_316789 baseEnd_316789 := by
    simpa [prefixWord, tailWord_316789, baseEnd_316789] using wordTrace_append hprefix tailTrace_316789
  have hstable : (prefixWord ++ tailWord_316789).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316789).length < 2 ^ (prefixWord ++ tailWord_316789).sum := by decide
  have hdescent : baseEnd_316789 < baseStart_316789 := by decide
  rcases family_descends (prefixWord ++ tailWord_316789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316793 : List Nat := [1, 2, 1, 3, 2, 1, 5, 2, 3]
def baseStart_316793 : Nat := 118140960795 + 316793 * 2 ^ 59
def prefixEnd_316793 : Nat := 4983230072969 + 3 ^ 40 * 316793 * 2
def baseEnd_316793 : Nat := 144592957315452693004979

theorem tailTrace_316793 : CollatzResearch.WordTrace tailWord_316793 prefixEnd_316793 144592957315452693004979 := by
  unfold tailWord_316793
  simp only [CollatzResearch.WordTrace]
  refine ⟨11554389941320539782075033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7702926627547026521383355 11554389941320539782075033)
  ·
    refine ⟨8665792455990404836556275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11554389941320539782075033 8665792455990404836556275)
    ·
      refine ⟨12998688683985607254834413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8665792455990404836556275 12998688683985607254834413)
      ·
        refine ⟨4874508256494602720562905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12998688683985607254834413 4874508256494602720562905)
        ·
          refine ⟨3655881192370952040422179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4874508256494602720562905 3655881192370952040422179)
          ·
            refine ⟨5483821788556428060633269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3655881192370952040422179 5483821788556428060633269)
            ·
              refine ⟨514108292677165130684369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5483821788556428060633269 514108292677165130684369)
              ·
                refine ⟨385581219507873848013277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 514108292677165130684369 385581219507873848013277)
                ·
                  refine ⟨144592957315452693004979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 385581219507873848013277 144592957315452693004979)
                  ·
                    rfl

theorem cell20_316793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 5, 2, 3].length) (baseStart_316793 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_316793 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_316793 prefixEnd_316793 := by exact prefixLift 316793
  have htrace : WordTrace (prefixWord ++ tailWord_316793) baseStart_316793 baseEnd_316793 := by
    simpa [prefixWord, tailWord_316793, baseEnd_316793] using wordTrace_append hprefix tailTrace_316793
  have hstable : (prefixWord ++ tailWord_316793).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316793).length < 2 ^ (prefixWord ++ tailWord_316793).sum := by decide
  have hdescent : baseEnd_316793 < baseStart_316793 := by decide
  rcases family_descends (prefixWord ++ tailWord_316793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316824 : List Nat := [2, 1, 2, 5, 2, 1, 1, 6]
def baseStart_316824 : Nat := 118140960795 + 316824 * 2 ^ 59
def prefixEnd_316824 : Nat := 4983230072969 + 3 ^ 40 * 316824 * 2
def baseEnd_316824 : Nat := 48202368853384787657173

theorem tailTrace_316824 : CollatzResearch.WordTrace tailWord_316824 prefixEnd_316824 48202368853384787657173 := by
  unfold tailWord_316824
  simp only [CollatzResearch.WordTrace]
  refine ⟨5777760302104116038226763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7703680402805488050969017 5777760302104116038226763)
  ·
    refine ⟨8666640453156174057340145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5777760302104116038226763 8666640453156174057340145)
    ·
      refine ⟨6499980339867130543005109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8666640453156174057340145 6499980339867130543005109)
      ·
        refine ⟨609373156862543488406729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6499980339867130543005109 609373156862543488406729)
        ·
          refine ⟨457029867646907616305047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 609373156862543488406729 457029867646907616305047)
          ·
            refine ⟨685544801470361424457571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 457029867646907616305047 685544801470361424457571)
            ·
              refine ⟨1028317202205542136686357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 685544801470361424457571 1028317202205542136686357)
              ·
                refine ⟨48202368853384787657173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1028317202205542136686357 48202368853384787657173)
                ·
                  rfl

theorem cell20_316824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 6].length) (baseStart_316824 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_316824 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_316824 prefixEnd_316824 := by exact prefixLift 316824
  have htrace : WordTrace (prefixWord ++ tailWord_316824) baseStart_316824 baseEnd_316824 := by
    simpa [prefixWord, tailWord_316824, baseEnd_316824] using wordTrace_append hprefix tailTrace_316824
  have hstable : (prefixWord ++ tailWord_316824).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316824).length < 2 ^ (prefixWord ++ tailWord_316824).sum := by decide
  have hdescent : baseEnd_316824 < baseStart_316824 := by decide
  rcases family_descends (prefixWord ++ tailWord_316824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316830 : List Nat := [4, 3, 1, 2, 2, 2, 1, 3, 2]
def baseStart_316830 : Nat := 118140960795 + 316830 * 2 ^ 59
def prefixEnd_316830 : Nat := 4983230072969 + 3 ^ 40 * 316830 * 2
def baseEnd_316830 : Nat := 144609845123645008771495

theorem tailTrace_316830 : CollatzResearch.WordTrace tailWord_316830 prefixEnd_316830 144609845123645008771495 := by
  unfold tailWord_316830
  simp only [CollatzResearch.WordTrace]
  refine ⟨1444467430273311887646493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7703826294790996734114629 1444467430273311887646493)
  ·
    refine ⟨541675286352491957867435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1444467430273311887646493 541675286352491957867435)
    ·
      refine ⟨812512929528737936801153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 541675286352491957867435 812512929528737936801153)
      ·
        refine ⟨609384697146553452600865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 812512929528737936801153 609384697146553452600865)
        ·
          refine ⟨457038522859915089450649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 609384697146553452600865 457038522859915089450649)
          ·
            refine ⟨342778892144936317087987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 457038522859915089450649 342778892144936317087987)
            ·
              refine ⟨514168338217404475631981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 342778892144936317087987 514168338217404475631981)
              ·
                refine ⟨192813126831526678361993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 514168338217404475631981 192813126831526678361993)
                ·
                  refine ⟨144609845123645008771495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 192813126831526678361993 144609845123645008771495)
                  ·
                    rfl

theorem cell20_316830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 1, 3, 2].length) (baseStart_316830 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_316830 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_316830 prefixEnd_316830 := by exact prefixLift 316830
  have htrace : WordTrace (prefixWord ++ tailWord_316830) baseStart_316830 baseEnd_316830 := by
    simpa [prefixWord, tailWord_316830, baseEnd_316830] using wordTrace_append hprefix tailTrace_316830
  have hstable : (prefixWord ++ tailWord_316830).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316830).length < 2 ^ (prefixWord ++ tailWord_316830).sum := by decide
  have hdescent : baseEnd_316830 < baseStart_316830 := by decide
  rcases family_descends (prefixWord ++ tailWord_316830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316834 : List Nat := [3, 3, 1, 2, 1, 2, 3, 3, 2]
def baseStart_316834 : Nat := 118140960795 + 316834 * 2 ^ 59
def prefixEnd_316834 : Nat := 4983230072969 + 3 ^ 40 * 316834 * 2
def baseEnd_316834 : Nat := 144611670832638772638145

theorem tailTrace_316834 : CollatzResearch.WordTrace tailWord_316834 prefixEnd_316834 144611670832638772638145 := by
  unfold tailWord_316834
  simp only [CollatzResearch.WordTrace]
  refine ⟨2888971333543000946079389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7703923556114669189545037 2888971333543000946079389)
  ·
    refine ⟨1083364250078625354779771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2888971333543000946079389 1083364250078625354779771)
    ·
      refine ⟨1625046375117938032169657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1083364250078625354779771 1625046375117938032169657)
      ·
        refine ⟨1218784781338453524127243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1625046375117938032169657 1218784781338453524127243)
        ·
          refine ⟨1828177172007680286190865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1218784781338453524127243 1828177172007680286190865)
          ·
            refine ⟨1371132879005760214643149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1828177172007680286190865 1371132879005760214643149)
            ·
              refine ⟨514174829627160080491181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1371132879005760214643149 514174829627160080491181)
              ·
                refine ⟨192815561110185030184193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 514174829627160080491181 192815561110185030184193)
                ·
                  refine ⟨144611670832638772638145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 192815561110185030184193 144611670832638772638145)
                  ·
                    rfl

theorem cell20_316834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 3, 3, 2].length) (baseStart_316834 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_316834 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_316834 prefixEnd_316834 := by exact prefixLift 316834
  have htrace : WordTrace (prefixWord ++ tailWord_316834) baseStart_316834 baseEnd_316834 := by
    simpa [prefixWord, tailWord_316834, baseEnd_316834] using wordTrace_append hprefix tailTrace_316834
  have hstable : (prefixWord ++ tailWord_316834).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316834).length < 2 ^ (prefixWord ++ tailWord_316834).sum := by decide
  have hdescent : baseEnd_316834 < baseStart_316834 := by decide
  rcases family_descends (prefixWord ++ tailWord_316834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316906 : List Nat := [3, 1, 3, 1, 5, 1, 2, 2, 2]
def baseStart_316906 : Nat := 118140960795 + 316906 * 2 ^ 59
def prefixEnd_316906 : Nat := 4983230072969 + 3 ^ 40 * 316906 * 2
def baseEnd_316906 : Nat := 144644533594526522237851

theorem tailTrace_316906 : CollatzResearch.WordTrace tailWord_316906 prefixEnd_316906 144644533594526522237851 := by
  unfold tailWord_316906
  simp only [CollatzResearch.WordTrace]
  refine ⟨2889627847477790020234643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7705674259940773387292381 2889627847477790020234643)
  ·
    refine ⟨4334441771216685030351965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2889627847477790020234643 4334441771216685030351965)
    ·
      refine ⟨1625415664206256886381987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4334441771216685030351965 1625415664206256886381987)
      ·
        refine ⟨2438123496309385329572981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1625415664206256886381987 2438123496309385329572981)
        ·
          refine ⟨228574077779004874647467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2438123496309385329572981 228574077779004874647467)
          ·
            refine ⟨342861116668507311971201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 228574077779004874647467 342861116668507311971201)
            ·
              refine ⟨257145837501380483978401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 342861116668507311971201 257145837501380483978401)
              ·
                refine ⟨192859378126035362983801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 257145837501380483978401 192859378126035362983801)
                ·
                  refine ⟨144644533594526522237851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 192859378126035362983801 144644533594526522237851)
                  ·
                    rfl

theorem cell20_316906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 2, 2, 2].length) (baseStart_316906 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_316906 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_316906 prefixEnd_316906 := by exact prefixLift 316906
  have htrace : WordTrace (prefixWord ++ tailWord_316906) baseStart_316906 baseEnd_316906 := by
    simpa [prefixWord, tailWord_316906, baseEnd_316906] using wordTrace_append hprefix tailTrace_316906
  have hstable : (prefixWord ++ tailWord_316906).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316906).length < 2 ^ (prefixWord ++ tailWord_316906).sum := by decide
  have hdescent : baseEnd_316906 < baseStart_316906 := by decide
  rcases family_descends (prefixWord ++ tailWord_316906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316917 : List Nat := [1, 3, 5, 1, 1, 3, 1, 5]
def baseStart_316917 : Nat := 118140960795 + 316917 * 2 ^ 59
def prefixEnd_316917 : Nat := 4983230072969 + 3 ^ 40 * 316917 * 2
def baseEnd_316917 : Nat := 48216518098086457623713

theorem tailTrace_316917 : CollatzResearch.WordTrace tailWord_316917 prefixEnd_316917 48216518098086457623713 := by
  unfold tailWord_316917
  simp only [CollatzResearch.WordTrace]
  refine ⟨11558912592871308959589005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7705941728580872639726003 11558912592871308959589005)
  ·
    refine ⟨4334592222326740859845877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11558912592871308959589005 4334592222326740859845877)
    ·
      refine ⟨406368020843131955610551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4334592222326740859845877 406368020843131955610551)
      ·
        refine ⟨609552031264697933415827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 406368020843131955610551 609552031264697933415827)
        ·
          refine ⟨914328046897046900123741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 609552031264697933415827 914328046897046900123741)
          ·
            refine ⟨342873017586392587546403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 914328046897046900123741 342873017586392587546403)
            ·
              refine ⟨514309526379588881319605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 342873017586392587546403 514309526379588881319605)
              ·
                refine ⟨48216518098086457623713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 514309526379588881319605 48216518098086457623713)
                ·
                  rfl

theorem cell20_316917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 1, 5].length) (baseStart_316917 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_316917 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_316917 prefixEnd_316917 := by exact prefixLift 316917
  have htrace : WordTrace (prefixWord ++ tailWord_316917) baseStart_316917 baseEnd_316917 := by
    simpa [prefixWord, tailWord_316917, baseEnd_316917] using wordTrace_append hprefix tailTrace_316917
  have hstable : (prefixWord ++ tailWord_316917).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316917).length < 2 ^ (prefixWord ++ tailWord_316917).sum := by decide
  have hdescent : baseEnd_316917 < baseStart_316917 := by decide
  rcases family_descends (prefixWord ++ tailWord_316917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316938 : List Nat := [3, 1, 2, 2, 2, 3, 3, 4]
def baseStart_316938 : Nat := 118140960795 + 316938 * 2 ^ 59
def prefixEnd_316938 : Nat := 4983230072969 + 3 ^ 40 * 316938 * 2
def baseEnd_316938 : Nat := 48219713088825544390351

theorem tailTrace_316938 : CollatzResearch.WordTrace tailWord_316938 prefixEnd_316938 48219713088825544390351 := by
  unfold tailWord_316938
  simp only [CollatzResearch.WordTrace]
  refine ⟨2889919631448807386525867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7706452350530153030735645 2889919631448807386525867)
  ·
    refine ⟨4334879447173211079788801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2889919631448807386525867 4334879447173211079788801)
    ·
      refine ⟨3251159585379908309841601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4334879447173211079788801 3251159585379908309841601)
      ·
        refine ⟨2438369689034931232381201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3251159585379908309841601 2438369689034931232381201)
        ·
          refine ⟨1828777266776198424285901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2438369689034931232381201 1828777266776198424285901)
          ·
            refine ⟨685791475041074409107213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1828777266776198424285901 685791475041074409107213)
            ·
              refine ⟨257171803140402903415205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 685791475041074409107213 257171803140402903415205)
              ·
                refine ⟨48219713088825544390351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 257171803140402903415205 48219713088825544390351)
                ·
                  rfl

theorem cell20_316938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 3, 4].length) (baseStart_316938 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_316938 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_316938 prefixEnd_316938 := by exact prefixLift 316938
  have htrace : WordTrace (prefixWord ++ tailWord_316938) baseStart_316938 baseEnd_316938 := by
    simpa [prefixWord, tailWord_316938, baseEnd_316938] using wordTrace_append hprefix tailTrace_316938
  have hstable : (prefixWord ++ tailWord_316938).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316938).length < 2 ^ (prefixWord ++ tailWord_316938).sum := by decide
  have hdescent : baseEnd_316938 < baseStart_316938 := by decide
  rcases family_descends (prefixWord ++ tailWord_316938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316958 : List Nat := [4, 3, 3, 1, 1, 1, 1, 1, 5]
def baseStart_316958 : Nat := 118140960795 + 316958 * 2 ^ 59
def prefixEnd_316958 : Nat := 4983230072969 + 3 ^ 40 * 316958 * 2
def baseEnd_316958 : Nat := 144668267811445452504305

theorem tailTrace_316958 : CollatzResearch.WordTrace tailWord_316958 prefixEnd_316958 144668267811445452504305 := by
  unfold tailWord_316958
  simp only [CollatzResearch.WordTrace]
  refine ⟨1445050998215346620228941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7706938657148515307887685 1445050998215346620228941)
  ·
    refine ⟨541894124330754982585853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1445050998215346620228941 541894124330754982585853)
    ·
      refine ⟨203210296624033118469695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 541894124330754982585853 203210296624033118469695)
      ·
        refine ⟨304815444936049677704543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203210296624033118469695 304815444936049677704543)
        ·
          refine ⟨457223167404074516556815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 304815444936049677704543 457223167404074516556815)
          ·
            refine ⟨685834751106111774835223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 457223167404074516556815 685834751106111774835223)
            ·
              refine ⟨1028752126659167662252835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 685834751106111774835223 1028752126659167662252835)
              ·
                refine ⟨1543128189988751493379253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1028752126659167662252835 1543128189988751493379253)
                ·
                  refine ⟨144668267811445452504305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1543128189988751493379253 144668267811445452504305)
                  ·
                    rfl

theorem cell20_316958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 1, 5].length) (baseStart_316958 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_316958 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_316958 prefixEnd_316958 := by exact prefixLift 316958
  have htrace : WordTrace (prefixWord ++ tailWord_316958) baseStart_316958 baseEnd_316958 := by
    simpa [prefixWord, tailWord_316958, baseEnd_316958] using wordTrace_append hprefix tailTrace_316958
  have hstable : (prefixWord ++ tailWord_316958).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316958).length < 2 ^ (prefixWord ++ tailWord_316958).sum := by decide
  have hdescent : baseEnd_316958 < baseStart_316958 := by decide
  rcases family_descends (prefixWord ++ tailWord_316958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317004 : List Nat := [2, 2, 1, 3, 1, 3, 1, 2, 5]
def baseStart_317004 : Nat := 118140960795 + 317004 * 2 ^ 59
def prefixEnd_317004 : Nat := 4983230072969 + 3 ^ 40 * 317004 * 2
def baseEnd_317004 : Nat := 144689263464873736970783

theorem tailTrace_317004 : CollatzResearch.WordTrace tailWord_317004 prefixEnd_317004 144689263464873736970783 := by
  unfold tailWord_317004
  simp only [CollatzResearch.WordTrace]
  refine ⟨5781042871778061409003033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7708057162370748545337377 5781042871778061409003033)
  ·
    refine ⟨4335782153833546056752275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5781042871778061409003033 4335782153833546056752275)
    ·
      refine ⟨6503673230750319085128413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4335782153833546056752275 6503673230750319085128413)
      ·
        refine ⟨2438877461531369656923155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6503673230750319085128413 2438877461531369656923155)
        ·
          refine ⟨3658316192297054485384733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2438877461531369656923155 3658316192297054485384733)
          ·
            refine ⟨1371868572111395432019275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3658316192297054485384733 1371868572111395432019275)
            ·
              refine ⟨2057802858167093148028913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1371868572111395432019275 2057802858167093148028913)
              ·
                refine ⟨1543352143625319861021685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2057802858167093148028913 1543352143625319861021685)
                ·
                  refine ⟨144689263464873736970783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1543352143625319861021685 144689263464873736970783)
                  ·
                    rfl

theorem cell20_317004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 2, 5].length) (baseStart_317004 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_317004 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_317004 prefixEnd_317004 := by exact prefixLift 317004
  have htrace : WordTrace (prefixWord ++ tailWord_317004) baseStart_317004 baseEnd_317004 := by
    simpa [prefixWord, tailWord_317004, baseEnd_317004] using wordTrace_append hprefix tailTrace_317004
  have hstable : (prefixWord ++ tailWord_317004).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317004).length < 2 ^ (prefixWord ++ tailWord_317004).sum := by decide
  have hdescent : baseEnd_317004 < baseStart_317004 := by decide
  rcases family_descends (prefixWord ++ tailWord_317004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317028 : List Nat := [2, 3, 1, 1, 2, 3, 3, 1, 4]
def baseStart_317028 : Nat := 118140960795 + 317028 * 2 ^ 59
def prefixEnd_317028 : Nat := 4983230072969 + 3 ^ 40 * 317028 * 2
def baseEnd_317028 : Nat := 144700217718836320170685

theorem tailTrace_317028 : CollatzResearch.WordTrace tailWord_317028 prefixEnd_317028 144700217718836320170685 := by
  unfold tailWord_317028
  simp only [CollatzResearch.WordTrace]
  refine ⟨5781480547734587458439869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7708640730312783277919825 5781480547734587458439869)
  ·
    refine ⟨2168055205400470296914951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5781480547734587458439869 2168055205400470296914951)
    ·
      refine ⟨3252082808100705445372427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2168055205400470296914951 3252082808100705445372427)
      ·
        refine ⟨4878124212151058168058641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3252082808100705445372427 4878124212151058168058641)
        ·
          refine ⟨3658593159113293626043981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4878124212151058168058641 3658593159113293626043981)
          ·
            refine ⟨1371972434667485109766493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3658593159113293626043981 1371972434667485109766493)
            ·
              refine ⟨514489663000306916162435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1371972434667485109766493 514489663000306916162435)
              ·
                refine ⟨771734494500460374243653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 514489663000306916162435 771734494500460374243653)
                ·
                  refine ⟨144700217718836320170685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 771734494500460374243653 144700217718836320170685)
                  ·
                    rfl

theorem cell20_317028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 3, 1, 4].length) (baseStart_317028 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_317028 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_317028 prefixEnd_317028 := by exact prefixLift 317028
  have htrace : WordTrace (prefixWord ++ tailWord_317028) baseStart_317028 baseEnd_317028 := by
    simpa [prefixWord, tailWord_317028, baseEnd_317028] using wordTrace_append hprefix tailTrace_317028
  have hstable : (prefixWord ++ tailWord_317028).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317028).length < 2 ^ (prefixWord ++ tailWord_317028).sum := by decide
  have hdescent : baseEnd_317028 < baseStart_317028 := by decide
  rcases family_descends (prefixWord ++ tailWord_317028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317038 : List Nat := [4, 1, 2, 2, 3, 1, 1, 3, 3]
def baseStart_317038 : Nat := 118140960795 + 317038 * 2 ^ 59
def prefixEnd_317038 : Nat := 4983230072969 + 3 ^ 40 * 317038 * 2
def baseEnd_317038 : Nat := 144704781991320729837311

theorem tailTrace_317038 : CollatzResearch.WordTrace tailWord_317038 prefixEnd_317038 144704781991320729837311 := by
  unfold tailWord_317038
  simp only [CollatzResearch.WordTrace]
  refine ⟨1445415728179118328092971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7708883883621964416495845 1445415728179118328092971)
  ·
    refine ⟨2168123592268677492139457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1445415728179118328092971 2168123592268677492139457)
    ·
      refine ⟨1626092694201508119104593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2168123592268677492139457 1626092694201508119104593)
      ·
        refine ⟨1219569520651131089328445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1626092694201508119104593 1219569520651131089328445)
        ·
          refine ⟨457338570244174158498167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1219569520651131089328445 457338570244174158498167)
          ·
            refine ⟨686007855366261237747251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 457338570244174158498167 686007855366261237747251)
            ·
              refine ⟨1029011783049391856620877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 686007855366261237747251 1029011783049391856620877)
              ·
                refine ⟨385879418643521946232829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1029011783049391856620877 385879418643521946232829)
                ·
                  refine ⟨144704781991320729837311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 385879418643521946232829 144704781991320729837311)
                  ·
                    rfl

theorem cell20_317038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 3, 3].length) (baseStart_317038 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_317038 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_317038 prefixEnd_317038 := by exact prefixLift 317038
  have htrace : WordTrace (prefixWord ++ tailWord_317038) baseStart_317038 baseEnd_317038 := by
    simpa [prefixWord, tailWord_317038, baseEnd_317038] using wordTrace_append hprefix tailTrace_317038
  have hstable : (prefixWord ++ tailWord_317038).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317038).length < 2 ^ (prefixWord ++ tailWord_317038).sum := by decide
  have hdescent : baseEnd_317038 < baseStart_317038 := by decide
  rcases family_descends (prefixWord ++ tailWord_317038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317049 : List Nat := [1, 2, 1, 3, 3, 1, 2, 1, 6]
def baseStart_317049 : Nat := 118140960795 + 317049 * 2 ^ 59
def prefixEnd_317049 : Nat := 4983230072969 + 3 ^ 40 * 317049 * 2
def baseEnd_317049 : Nat := 144709802691053580470599

theorem tailTrace_317049 : CollatzResearch.WordTrace tailWord_317049 prefixEnd_317049 144709802691053580470599 := by
  unfold tailWord_317049
  simp only [CollatzResearch.WordTrace]
  refine ⟨11563727028393095503394201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7709151352262063668929467 11563727028393095503394201)
  ·
    refine ⟨8672795271294821627545651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11563727028393095503394201 8672795271294821627545651)
    ·
      refine ⟨13009192906942232441318477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8672795271294821627545651 13009192906942232441318477)
      ·
        refine ⟨4878447340103337165494429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13009192906942232441318477 4878447340103337165494429)
        ·
          refine ⟨1829417752538751437060411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4878447340103337165494429 1829417752538751437060411)
          ·
            refine ⟨2744126628808127155590617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1829417752538751437060411 2744126628808127155590617)
            ·
              refine ⟨2058094971606095366692963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2744126628808127155590617 2058094971606095366692963)
              ·
                refine ⟨3087142457409143050039445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2058094971606095366692963 3087142457409143050039445)
                ·
                  refine ⟨144709802691053580470599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3087142457409143050039445 144709802691053580470599)
                  ·
                    rfl

theorem cell20_317049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 1, 6].length) (baseStart_317049 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_317049 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_317049 prefixEnd_317049 := by exact prefixLift 317049
  have htrace : WordTrace (prefixWord ++ tailWord_317049) baseStart_317049 baseEnd_317049 := by
    simpa [prefixWord, tailWord_317049, baseEnd_317049] using wordTrace_append hprefix tailTrace_317049
  have hstable : (prefixWord ++ tailWord_317049).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317049).length < 2 ^ (prefixWord ++ tailWord_317049).sum := by decide
  have hdescent : baseEnd_317049 < baseStart_317049 := by decide
  rcases family_descends (prefixWord ++ tailWord_317049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317056 : List Nat := [2, 1, 1, 2, 1, 4, 1, 8]
def baseStart_317056 : Nat := 118140960795 + 317056 * 2 ^ 59
def prefixEnd_317056 : Nat := 4983230072969 + 3 ^ 40 * 317056 * 2
def baseEnd_317056 : Nat := 48237665893930889079079

theorem tailTrace_317056 : CollatzResearch.WordTrace tailWord_317056 prefixEnd_317056 48237665893930889079079 := by
  unfold tailWord_317056
  simp only [CollatzResearch.WordTrace]
  refine ⟨5781991169683867849449511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7709321559578490465932681 5781991169683867849449511)
  ·
    refine ⟨8672986754525801774174267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5781991169683867849449511 8672986754525801774174267)
    ·
      refine ⟨13009480131788702661261401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8672986754525801774174267 13009480131788702661261401)
      ·
        refine ⟨9757110098841526995946051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13009480131788702661261401 9757110098841526995946051)
        ·
          refine ⟨14635665148262290493919077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9757110098841526995946051 14635665148262290493919077)
          ·
            refine ⟨2744187215299179467609827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14635665148262290493919077 2744187215299179467609827)
            ·
              refine ⟨4116280822948769201414741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2744187215299179467609827 4116280822948769201414741)
              ·
                refine ⟨48237665893930889079079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4116280822948769201414741 48237665893930889079079)
                ·
                  rfl

theorem cell20_317056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 8].length) (baseStart_317056 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_317056 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_317056 prefixEnd_317056 := by exact prefixLift 317056
  have htrace : WordTrace (prefixWord ++ tailWord_317056) baseStart_317056 baseEnd_317056 := by
    simpa [prefixWord, tailWord_317056, baseEnd_317056] using wordTrace_append hprefix tailTrace_317056
  have hstable : (prefixWord ++ tailWord_317056).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317056).length < 2 ^ (prefixWord ++ tailWord_317056).sum := by decide
  have hdescent : baseEnd_317056 < baseStart_317056 := by decide
  rcases family_descends (prefixWord ++ tailWord_317056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317163 : List Nat := [1, 1, 1, 1, 2, 4, 4, 2, 4]
def baseStart_317163 : Nat := 118140960795 + 317163 * 2 ^ 59
def prefixEnd_317163 : Nat := 4983230072969 + 3 ^ 40 * 317163 * 2
def baseEnd_317163 : Nat := 144761835397375850670133

theorem tailTrace_317163 : CollatzResearch.WordTrace tailWord_317163 prefixEnd_317163 144761835397375850670133 := by
  unfold tailWord_317163
  simp only [CollatzResearch.WordTrace]
  refine ⟨11567884949980092973044143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7711923299986728648696095 11567884949980092973044143)
  ·
    refine ⟨17351827424970139459566215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11567884949980092973044143 17351827424970139459566215)
    ·
      refine ⟨26027741137455209189349323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17351827424970139459566215 26027741137455209189349323)
      ·
        refine ⟨39041611706182813784023985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26027741137455209189349323 39041611706182813784023985)
        ·
          refine ⟨29281208779637110338017989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39041611706182813784023985 29281208779637110338017989)
          ·
            refine ⟨5490226646181958188378373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29281208779637110338017989 5490226646181958188378373)
            ·
              refine ⟨1029417496159117160320945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5490226646181958188378373 1029417496159117160320945)
              ·
                refine ⟨772063122119337870240709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1029417496159117160320945 772063122119337870240709)
                ·
                  refine ⟨144761835397375850670133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 772063122119337870240709 144761835397375850670133)
                  ·
                    rfl

theorem cell20_317163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 2, 4].length) (baseStart_317163 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_317163 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_317163 prefixEnd_317163 := by exact prefixLift 317163
  have htrace : WordTrace (prefixWord ++ tailWord_317163) baseStart_317163 baseEnd_317163 := by
    simpa [prefixWord, tailWord_317163, baseEnd_317163] using wordTrace_append hprefix tailTrace_317163
  have hstable : (prefixWord ++ tailWord_317163).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317163).length < 2 ^ (prefixWord ++ tailWord_317163).sum := by decide
  have hdescent : baseEnd_317163 < baseStart_317163 := by decide
  rcases family_descends (prefixWord ++ tailWord_317163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317172 : List Nat := [2, 6, 1, 1, 1, 3, 1, 3, 2]
def baseStart_317172 : Nat := 118140960795 + 317172 * 2 ^ 59
def prefixEnd_317172 : Nat := 4983230072969 + 3 ^ 40 * 317172 * 2
def baseEnd_317172 : Nat := 144765943242611819370097

theorem tailTrace_317172 : CollatzResearch.WordTrace tailWord_317172 prefixEnd_317172 144765943242611819370097 := by
  unfold tailWord_317172
  simp only [CollatzResearch.WordTrace]
  refine ⟨5784106603473743755060885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7712142137964991673414513 5784106603473743755060885)
  ·
    refine ⟨271129997037831738518479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 5784106603473743755060885 271129997037831738518479)
    ·
      refine ⟨406694995556747607777719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 271129997037831738518479 406694995556747607777719)
      ·
        refine ⟨610042493335121411666579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 406694995556747607777719 610042493335121411666579)
        ·
          refine ⟨915063740002682117499869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 610042493335121411666579 915063740002682117499869)
          ·
            refine ⟨343148902501005794062451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 915063740002682117499869 343148902501005794062451)
            ·
              refine ⟨514723353751508691093677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 343148902501005794062451 514723353751508691093677)
              ·
                refine ⟨193021257656815759160129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 514723353751508691093677 193021257656815759160129)
                ·
                  refine ⟨144765943242611819370097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 193021257656815759160129 144765943242611819370097)
                  ·
                    rfl

theorem cell20_317172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_317172 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_317172 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_317172 prefixEnd_317172 := by exact prefixLift 317172
  have htrace : WordTrace (prefixWord ++ tailWord_317172) baseStart_317172 baseEnd_317172 := by
    simpa [prefixWord, tailWord_317172, baseEnd_317172] using wordTrace_append hprefix tailTrace_317172
  have hstable : (prefixWord ++ tailWord_317172).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317172).length < 2 ^ (prefixWord ++ tailWord_317172).sum := by decide
  have hdescent : baseEnd_317172 < baseStart_317172 := by decide
  rcases family_descends (prefixWord ++ tailWord_317172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317194 : List Nat := [3, 1, 2, 2, 1, 3, 2, 1, 5]
def baseStart_317194 : Nat := 118140960795 + 317194 * 2 ^ 59
def prefixEnd_317194 : Nat := 4983230072969 + 3 ^ 40 * 317194 * 2
def baseEnd_317194 : Nat := 144775984642077520636673

theorem tailTrace_317194 : CollatzResearch.WordTrace tailWord_317194 prefixEnd_317194 144775984642077520636673 := by
  unfold tailWord_317194
  simp only [CollatzResearch.WordTrace]
  refine ⟨2892253903216946316855659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7712677075245190178281757 2892253903216946316855659)
  ·
    refine ⟨4338380854825419475283489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2892253903216946316855659 4338380854825419475283489)
    ·
      refine ⟨3253785641119064606462617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4338380854825419475283489 3253785641119064606462617)
      ·
        refine ⟨2440339230839298454846963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3253785641119064606462617 2440339230839298454846963)
        ·
          refine ⟨3660508846258947682270445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2440339230839298454846963 3660508846258947682270445)
          ·
            refine ⟨1372690817347105380851417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3660508846258947682270445 1372690817347105380851417)
            ·
              refine ⟨1029518113010329035638563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1372690817347105380851417 1029518113010329035638563)
              ·
                refine ⟨1544277169515493553457845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1029518113010329035638563 1544277169515493553457845)
                ·
                  refine ⟨144775984642077520636673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1544277169515493553457845 144775984642077520636673)
                  ·
                    rfl

theorem cell20_317194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 1, 5].length) (baseStart_317194 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_317194 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_317194 prefixEnd_317194 := by exact prefixLift 317194
  have htrace : WordTrace (prefixWord ++ tailWord_317194) baseStart_317194 baseEnd_317194 := by
    simpa [prefixWord, tailWord_317194, baseEnd_317194] using wordTrace_append hprefix tailTrace_317194
  have hstable : (prefixWord ++ tailWord_317194).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317194).length < 2 ^ (prefixWord ++ tailWord_317194).sum := by decide
  have hdescent : baseEnd_317194 < baseStart_317194 := by decide
  rcases family_descends (prefixWord ++ tailWord_317194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317208 : List Nat := [2, 1, 2, 3, 1, 1, 3, 7]
def baseStart_317208 : Nat := 118140960795 + 317208 * 2 ^ 59
def prefixEnd_317208 : Nat := 4983230072969 + 3 ^ 40 * 317208 * 2
def baseEnd_317208 : Nat := 48260791541185231389983

theorem tailTrace_317208 : CollatzResearch.WordTrace tailWord_317208 prefixEnd_317208 48260791541185231389983 := by
  unfold tailWord_317208
  simp only [CollatzResearch.WordTrace]
  refine ⟨5784763117408532829216139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7713017489878043772288185 5784763117408532829216139)
  ·
    refine ⟨8677144676112799243824209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5784763117408532829216139 8677144676112799243824209)
    ·
      refine ⟨6507858507084599432868157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8677144676112799243824209 6507858507084599432868157)
      ·
        refine ⟨2440446940156724787325559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6507858507084599432868157 2440446940156724787325559)
        ·
          refine ⟨3660670410235087180988339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2440446940156724787325559 3660670410235087180988339)
          ·
            refine ⟨5491005615352630771482509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3660670410235087180988339 5491005615352630771482509)
            ·
              refine ⟨2059127105757236539305941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5491005615352630771482509 2059127105757236539305941)
              ·
                refine ⟨48260791541185231389983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2059127105757236539305941 48260791541185231389983)
                ·
                  rfl

theorem cell20_317208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 7].length) (baseStart_317208 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_317208 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_317208 prefixEnd_317208 := by exact prefixLift 317208
  have htrace : WordTrace (prefixWord ++ tailWord_317208) baseStart_317208 baseEnd_317208 := by
    simpa [prefixWord, tailWord_317208, baseEnd_317208] using wordTrace_append hprefix tailTrace_317208
  have hstable : (prefixWord ++ tailWord_317208).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317208).length < 2 ^ (prefixWord ++ tailWord_317208).sum := by decide
  have hdescent : baseEnd_317208 < baseStart_317208 := by decide
  rcases family_descends (prefixWord ++ tailWord_317208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317291 : List Nat := [1, 1, 1, 1, 2, 2, 3, 4, 5]
def baseStart_317291 : Nat := 118140960795 + 317291 * 2 ^ 59
def prefixEnd_317291 : Nat := 4983230072969 + 3 ^ 40 * 317291 * 2
def baseEnd_317291 : Nat := 144820258085176294402943

theorem tailTrace_317291 : CollatzResearch.WordTrace tailWord_317291 prefixEnd_317291 144820258085176294402943 := by
  unfold tailWord_317291
  simp only [CollatzResearch.WordTrace]
  refine ⟨11572553493516370833703727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7715035662344247222469151 11572553493516370833703727)
  ·
    refine ⟨17358830240274556250555591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11572553493516370833703727 17358830240274556250555591)
    ·
      refine ⟨26038245360411834375833387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17358830240274556250555591 26038245360411834375833387)
      ·
        refine ⟨39057368040617751563750081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26038245360411834375833387 39057368040617751563750081)
        ·
          refine ⟨29293026030463313672812561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39057368040617751563750081 29293026030463313672812561)
          ·
            refine ⟨21969769522847485254609421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29293026030463313672812561 21969769522847485254609421)
            ·
              refine ⟨8238663571067806970478533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21969769522847485254609421 8238663571067806970478533)
              ·
                refine ⟨1544749419575213806964725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8238663571067806970478533 1544749419575213806964725)
                ·
                  refine ⟨144820258085176294402943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1544749419575213806964725 144820258085176294402943)
                  ·
                    rfl

theorem cell20_317291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 4, 5].length) (baseStart_317291 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_317291 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_317291 prefixEnd_317291 := by exact prefixLift 317291
  have htrace : WordTrace (prefixWord ++ tailWord_317291) baseStart_317291 baseEnd_317291 := by
    simpa [prefixWord, tailWord_317291, baseEnd_317291] using wordTrace_append hprefix tailTrace_317291
  have hstable : (prefixWord ++ tailWord_317291).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317291).length < 2 ^ (prefixWord ++ tailWord_317291).sum := by decide
  have hdescent : baseEnd_317291 < baseStart_317291 := by decide
  rcases family_descends (prefixWord ++ tailWord_317291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317315 : List Nat := [1, 1, 1, 3, 4, 2, 1, 3, 4]
def baseStart_317315 : Nat := 118140960795 + 317315 * 2 ^ 59
def prefixEnd_317315 : Nat := 4983230072969 + 3 ^ 40 * 317315 * 2
def baseEnd_317315 : Nat := 144831212339138877602845

theorem tailTrace_317315 : CollatzResearch.WordTrace tailWord_317315 prefixEnd_317315 144831212339138877602845 := by
  unfold tailWord_317315
  simp only [CollatzResearch.WordTrace]
  refine ⟨11573428845429422932577399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7715619230286281955051599 11573428845429422932577399)
  ·
    refine ⟨17360143268144134398866099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11573428845429422932577399 17360143268144134398866099)
    ·
      refine ⟨26040214902216201598299149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17360143268144134398866099 26040214902216201598299149)
      ·
        refine ⟨9765080588331075599362181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26040214902216201598299149 9765080588331075599362181)
        ·
          refine ⟨1830952610312076674880409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9765080588331075599362181 1830952610312076674880409)
          ·
            refine ⟨1373214457734057506160307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1830952610312076674880409 1373214457734057506160307)
            ·
              refine ⟨2059821686601086259240461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1373214457734057506160307 2059821686601086259240461)
              ·
                refine ⟨772433132475407347215173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2059821686601086259240461 772433132475407347215173)
                ·
                  refine ⟨144831212339138877602845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 772433132475407347215173 144831212339138877602845)
                  ·
                    rfl

theorem cell20_317315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 3, 4].length) (baseStart_317315 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_317315 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_317315 prefixEnd_317315 := by exact prefixLift 317315
  have htrace : WordTrace (prefixWord ++ tailWord_317315) baseStart_317315 baseEnd_317315 := by
    simpa [prefixWord, tailWord_317315, baseEnd_317315] using wordTrace_append hprefix tailTrace_317315
  have hstable : (prefixWord ++ tailWord_317315).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317315).length < 2 ^ (prefixWord ++ tailWord_317315).sum := by decide
  have hdescent : baseEnd_317315 < baseStart_317315 := by decide
  rcases family_descends (prefixWord ++ tailWord_317315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317332 : List Nat := [2, 4, 2, 1, 1, 2, 2, 2, 4]
def baseStart_317332 : Nat := 118140960795 + 317332 * 2 ^ 59
def prefixEnd_317332 : Nat := 4983230072969 + 3 ^ 40 * 317332 * 2
def baseEnd_317332 : Nat := 144838971602362374036109

theorem tailTrace_317332 : CollatzResearch.WordTrace tailWord_317332 prefixEnd_317332 144838971602362374036109 := by
  unfold tailWord_317332
  simp only [CollatzResearch.WordTrace]
  refine ⟨5787024443183917417973125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7716032590911889890630833 5787024443183917417973125)
  ·
    refine ⟨1085067083096984515869961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5787024443183917417973125 1085067083096984515869961)
    ·
      refine ⟨813800312322738386902471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1085067083096984515869961 813800312322738386902471)
      ·
        refine ⟨1220700468484107580353707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 813800312322738386902471 1220700468484107580353707)
        ·
          refine ⟨1831050702726161370530561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1220700468484107580353707 1831050702726161370530561)
          ·
            refine ⟨1373288027044621027897921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1831050702726161370530561 1373288027044621027897921)
            ·
              refine ⟨1029966020283465770923441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1373288027044621027897921 1029966020283465770923441)
              ·
                refine ⟨772474515212599328192581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1029966020283465770923441 772474515212599328192581)
                ·
                  refine ⟨144838971602362374036109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 772474515212599328192581 144838971602362374036109)
                  ·
                    rfl

theorem cell20_317332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_317332 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_317332 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_317332 prefixEnd_317332 := by exact prefixLift 317332
  have htrace : WordTrace (prefixWord ++ tailWord_317332) baseStart_317332 baseEnd_317332 := by
    simpa [prefixWord, tailWord_317332, baseEnd_317332] using wordTrace_append hprefix tailTrace_317332
  have hstable : (prefixWord ++ tailWord_317332).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317332).length < 2 ^ (prefixWord ++ tailWord_317332).sum := by decide
  have hdescent : baseEnd_317332 < baseStart_317332 := by decide
  rcases family_descends (prefixWord ++ tailWord_317332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317345 : List Nat := [1, 2, 3, 4, 3, 1, 1, 3, 2]
def baseStart_317345 : Nat := 118140960795 + 317345 * 2 ^ 59
def prefixEnd_317345 : Nat := 4983230072969 + 3 ^ 40 * 317345 * 2
def baseEnd_317345 : Nat := 144844905156592106602723

theorem tailTrace_317345 : CollatzResearch.WordTrace tailWord_317345 prefixEnd_317345 144844905156592106602723 := by
  unfold tailWord_317345
  simp only [CollatzResearch.WordTrace]
  refine ⟨11574523035320738056169489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7716348690213825370779659 11574523035320738056169489)
  ·
    refine ⟨8680892276490553542127117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11574523035320738056169489 8680892276490553542127117)
    ·
      refine ⟨3255334603683957578297669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8680892276490553542127117 3255334603683957578297669)
      ·
        refine ⟨610375238190742045930813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3255334603683957578297669 610375238190742045930813)
        ·
          refine ⟨228890714321528267224055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 610375238190742045930813 228890714321528267224055)
          ·
            refine ⟨343336071482292400836083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 228890714321528267224055 343336071482292400836083)
            ·
              refine ⟨515004107223438601254125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 343336071482292400836083 515004107223438601254125)
              ·
                refine ⟨193126540208789475470297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 515004107223438601254125 193126540208789475470297)
                ·
                  refine ⟨144844905156592106602723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 193126540208789475470297 144844905156592106602723)
                  ·
                    rfl

theorem cell20_317345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 1, 3, 2].length) (baseStart_317345 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_317345 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_317345 prefixEnd_317345 := by exact prefixLift 317345
  have htrace : WordTrace (prefixWord ++ tailWord_317345) baseStart_317345 baseEnd_317345 := by
    simpa [prefixWord, tailWord_317345, baseEnd_317345] using wordTrace_append hprefix tailTrace_317345
  have hstable : (prefixWord ++ tailWord_317345).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317345).length < 2 ^ (prefixWord ++ tailWord_317345).sum := by decide
  have hdescent : baseEnd_317345 < baseStart_317345 := by decide
  rcases family_descends (prefixWord ++ tailWord_317345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317415 : List Nat := [1, 1, 5, 2, 4, 7]
def baseStart_317415 : Nat := 118140960795 + 317415 * 2 ^ 59
def prefixEnd_317415 : Nat := 4983230072969 + 3 ^ 40 * 317415 * 2
def baseEnd_317415 : Nat := 5365809446814184232189

theorem tailTrace_317415 : CollatzResearch.WordTrace tailWord_317415 prefixEnd_317415 5365809446814184232189 := by
  unfold tailWord_317415
  simp only [CollatzResearch.WordTrace]
  refine ⟨11577076145067140011217699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7718050763378093340811799 11577076145067140011217699)
  ·
    refine ⟨17365614217600710016826549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11577076145067140011217699 17365614217600710016826549)
    ·
      refine ⟨1628026332900066564077489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17365614217600710016826549 1628026332900066564077489)
      ·
        refine ⟨1221019749675049923058117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1628026332900066564077489 1221019749675049923058117)
        ·
          refine ⟨228941203064071860573397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1221019749675049923058117 228941203064071860573397)
          ·
            refine ⟨5365809446814184232189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 228941203064071860573397 5365809446814184232189)
            ·
              rfl

theorem cell20_317415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 7].length) (baseStart_317415 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_317415 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_317415 prefixEnd_317415 := by exact prefixLift 317415
  have htrace : WordTrace (prefixWord ++ tailWord_317415) baseStart_317415 baseEnd_317415 := by
    simpa [prefixWord, tailWord_317415, baseEnd_317415] using wordTrace_append hprefix tailTrace_317415
  have hstable : (prefixWord ++ tailWord_317415).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317415).length < 2 ^ (prefixWord ++ tailWord_317415).sum := by decide
  have hdescent : baseEnd_317415 < baseStart_317415 := by decide
  rcases family_descends (prefixWord ++ tailWord_317415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317425 : List Nat := [1, 2, 2, 2, 5, 1, 1, 4, 2]
def baseStart_317425 : Nat := 118140960795 + 317425 * 2 ^ 59
def prefixEnd_317425 : Nat := 4983230072969 + 3 ^ 40 * 317425 * 2
def baseEnd_317425 : Nat := 144881419336467383935729

theorem tailTrace_317425 : CollatzResearch.WordTrace tailWord_317425 prefixEnd_317425 144881419336467383935729 := by
  unfold tailWord_317425
  simp only [CollatzResearch.WordTrace]
  refine ⟨11577440875030911719081729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7718293916687274479387819 11577440875030911719081729)
  ·
    refine ⟨8683080656273183789311297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11577440875030911719081729 8683080656273183789311297)
    ·
      refine ⟨6512310492204887841983473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8683080656273183789311297 6512310492204887841983473)
      ·
        refine ⟨4884232869153665881487605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6512310492204887841983473 4884232869153665881487605)
        ·
          refine ⟨457896831483156176389463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4884232869153665881487605 457896831483156176389463)
          ·
            refine ⟨686845247224734264584195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 457896831483156176389463 686845247224734264584195)
            ·
              refine ⟨1030267870837101396876293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 686845247224734264584195 1030267870837101396876293)
              ·
                refine ⟨193175225781956511914305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1030267870837101396876293 193175225781956511914305)
                ·
                  refine ⟨144881419336467383935729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 193175225781956511914305 144881419336467383935729)
                  ·
                    rfl

theorem cell20_317425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 4, 2].length) (baseStart_317425 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_317425 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_317425 prefixEnd_317425 := by exact prefixLift 317425
  have htrace : WordTrace (prefixWord ++ tailWord_317425) baseStart_317425 baseEnd_317425 := by
    simpa [prefixWord, tailWord_317425, baseEnd_317425] using wordTrace_append hprefix tailTrace_317425
  have hstable : (prefixWord ++ tailWord_317425).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317425).length < 2 ^ (prefixWord ++ tailWord_317425).sum := by decide
  have hdescent : baseEnd_317425 < baseStart_317425 := by decide
  rcases family_descends (prefixWord ++ tailWord_317425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317474 : List Nat := [3, 3, 1, 1, 1, 2, 9]
def baseStart_317474 : Nat := 118140960795 + 317474 * 2 ^ 59
def prefixEnd_317474 : Nat := 4983230072969 + 3 ^ 40 * 317474 * 2
def baseEnd_317474 : Nat := 16100420474626776811355

theorem tailTrace_317474 : CollatzResearch.WordTrace tailWord_317474 prefixEnd_317474 16100420474626776811355 := by
  unfold tailWord_317474
  simp only [CollatzResearch.WordTrace]
  refine ⟨2894807012963348271903869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7719485367902262058410317 2894807012963348271903869)
  ·
    refine ⟨1085552629861255601963951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2894807012963348271903869 1085552629861255601963951)
    ·
      refine ⟨1628328944791883402945927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1085552629861255601963951 1628328944791883402945927)
      ·
        refine ⟨2442493417187825104418891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1628328944791883402945927 2442493417187825104418891)
        ·
          refine ⟨3663740125781737656628337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2442493417187825104418891 3663740125781737656628337)
          ·
            refine ⟨2747805094336303242471253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3663740125781737656628337 2747805094336303242471253)
            ·
              refine ⟨16100420474626776811355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2747805094336303242471253 16100420474626776811355)
              ·
                rfl

theorem cell20_317474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 9].length) (baseStart_317474 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_317474 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_317474 prefixEnd_317474 := by exact prefixLift 317474
  have htrace : WordTrace (prefixWord ++ tailWord_317474) baseStart_317474 baseEnd_317474 := by
    simpa [prefixWord, tailWord_317474, baseEnd_317474] using wordTrace_append hprefix tailTrace_317474
  have hstable : (prefixWord ++ tailWord_317474).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317474).length < 2 ^ (prefixWord ++ tailWord_317474).sum := by decide
  have hdescent : baseEnd_317474 < baseStart_317474 := by decide
  rcases family_descends (prefixWord ++ tailWord_317474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317477 : List Nat := [1, 3, 1, 2, 2, 5, 1, 2, 3]
def baseStart_317477 : Nat := 118140960795 + 317477 * 2 ^ 59
def prefixEnd_317477 : Nat := 4983230072969 + 3 ^ 40 * 317477 * 2
def baseEnd_317477 : Nat := 144905153553386314202183

theorem tailTrace_317477 : CollatzResearch.WordTrace tailWord_317477 prefixEnd_317477 144905153553386314202183 := by
  unfold tailWord_317477
  simp only [CollatzResearch.WordTrace]
  refine ⟨11579337470842524599974685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7719558313895016399983123 11579337470842524599974685)
  ·
    refine ⟨4342251551565946724990507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11579337470842524599974685 4342251551565946724990507)
    ·
      refine ⟨6513377327348920087485761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4342251551565946724990507 6513377327348920087485761)
      ·
        refine ⟨4885032995511690065614321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6513377327348920087485761 4885032995511690065614321)
        ·
          refine ⟨3663774746633767549210741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4885032995511690065614321 3663774746633767549210741)
          ·
            refine ⟨343478882496915707738507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3663774746633767549210741 343478882496915707738507)
            ·
              refine ⟨515218323745373561607761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 343478882496915707738507 515218323745373561607761)
              ·
                refine ⟨386413742809030171205821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 515218323745373561607761 386413742809030171205821)
                ·
                  refine ⟨144905153553386314202183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 386413742809030171205821 144905153553386314202183)
                  ·
                    rfl

theorem cell20_317477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 1, 2, 3].length) (baseStart_317477 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_317477 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_317477 prefixEnd_317477 := by exact prefixLift 317477
  have htrace : WordTrace (prefixWord ++ tailWord_317477) baseStart_317477 baseEnd_317477 := by
    simpa [prefixWord, tailWord_317477, baseEnd_317477] using wordTrace_append hprefix tailTrace_317477
  have hstable : (prefixWord ++ tailWord_317477).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317477).length < 2 ^ (prefixWord ++ tailWord_317477).sum := by decide
  have hdescent : baseEnd_317477 < baseStart_317477 := by decide
  rcases family_descends (prefixWord ++ tailWord_317477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317494 : List Nat := [5, 1, 2, 1, 1, 1, 5, 1, 3]
def baseStart_317494 : Nat := 118140960795 + 317494 * 2 ^ 59
def prefixEnd_317494 : Nat := 4983230072969 + 3 ^ 40 * 317494 * 2
def baseEnd_317494 : Nat := 144912912816609810635447

theorem tailTrace_317494 : CollatzResearch.WordTrace tailWord_317494 prefixEnd_317494 144912912816609810635447 := by
  unfold tailWord_317494
  simp only [CollatzResearch.WordTrace]
  refine ⟨723747344486308531458971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7719971674520624335562357 723747344486308531458971)
  ·
    refine ⟨1085621016729462797188457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 723747344486308531458971 1085621016729462797188457)
    ·
      refine ⟨814215762547097097891343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1085621016729462797188457 814215762547097097891343)
      ·
        refine ⟨1221323643820645646837015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 814215762547097097891343 1221323643820645646837015)
        ·
          refine ⟨1831985465730968470255523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1221323643820645646837015 1831985465730968470255523)
          ·
            refine ⟨2747978198596452705383285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1831985465730968470255523 2747978198596452705383285)
            ·
              refine ⟨257622956118417441129683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2747978198596452705383285 257622956118417441129683)
              ·
                refine ⟨386434434177626161694525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 257622956118417441129683 386434434177626161694525)
                ·
                  refine ⟨144912912816609810635447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 386434434177626161694525 144912912816609810635447)
                  ·
                    rfl

theorem cell20_317494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 5, 1, 3].length) (baseStart_317494 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_317494 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_317494 prefixEnd_317494 := by exact prefixLift 317494
  have htrace : WordTrace (prefixWord ++ tailWord_317494) baseStart_317494 baseEnd_317494 := by
    simpa [prefixWord, tailWord_317494, baseEnd_317494] using wordTrace_append hprefix tailTrace_317494
  have hstable : (prefixWord ++ tailWord_317494).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317494).length < 2 ^ (prefixWord ++ tailWord_317494).sum := by decide
  have hdescent : baseEnd_317494 < baseStart_317494 := by decide
  rcases family_descends (prefixWord ++ tailWord_317494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317591 : List Nat := [1, 1, 3, 3, 4, 1, 2, 2, 3]
def baseStart_317591 : Nat := 118140960795 + 317591 * 2 ^ 59
def prefixEnd_317591 : Nat := 4983230072969 + 3 ^ 40 * 317591 * 2
def baseEnd_317591 : Nat := 144957186259708584401717

theorem tailTrace_317591 : CollatzResearch.WordTrace tailWord_317591 prefixEnd_317591 144957186259708584401717 := by
  unfold tailWord_317591
  simp only [CollatzResearch.WordTrace]
  refine ⟨11583495392429522069624627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7722330261619681379749751 11583495392429522069624627)
  ·
    refine ⟨17375243088644283104436941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11583495392429522069624627 17375243088644283104436941)
    ·
      refine ⟨6515716158241606164163853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17375243088644283104436941 6515716158241606164163853)
      ·
        refine ⟨2443393559340602311561445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6515716158241606164163853 2443393559340602311561445)
        ·
          refine ⟨458136292376362933417771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2443393559340602311561445 458136292376362933417771)
          ·
            refine ⟨687204438564544400126657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 458136292376362933417771 687204438564544400126657)
            ·
              refine ⟨515403328923408300094993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 687204438564544400126657 515403328923408300094993)
              ·
                refine ⟨386552496692556225071245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 515403328923408300094993 386552496692556225071245)
                ·
                  refine ⟨144957186259708584401717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 386552496692556225071245 144957186259708584401717)
                  ·
                    rfl

theorem cell20_317591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 2, 2, 3].length) (baseStart_317591 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_317591 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_317591 prefixEnd_317591 := by exact prefixLift 317591
  have htrace : WordTrace (prefixWord ++ tailWord_317591) baseStart_317591 baseEnd_317591 := by
    simpa [prefixWord, tailWord_317591, baseEnd_317591] using wordTrace_append hprefix tailTrace_317591
  have hstable : (prefixWord ++ tailWord_317591).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317591).length < 2 ^ (prefixWord ++ tailWord_317591).sum := by decide
  have hdescent : baseEnd_317591 < baseStart_317591 := by decide
  rcases family_descends (prefixWord ++ tailWord_317591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317640 : List Nat := [2, 1, 3, 1, 2, 1, 1, 1, 8]
def baseStart_317640 : Nat := 118140960795 + 317640 * 2 ^ 59
def prefixEnd_317640 : Nat := 4983230072969 + 3 ^ 40 * 317640 * 2
def baseEnd_317640 : Nat := 144979551194882191768183

theorem tailTrace_317640 : CollatzResearch.WordTrace tailWord_317640 prefixEnd_317640 144979551194882191768183 := by
  unfold tailWord_317640
  simp only [CollatzResearch.WordTrace]
  refine ⟨5792641284626001719079187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7723521712834668958772249 5792641284626001719079187)
  ·
    refine ⟨8688961926939002578618781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5792641284626001719079187 8688961926939002578618781)
    ·
      refine ⟨3258360722602125966982043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8688961926939002578618781 3258360722602125966982043)
      ·
        refine ⟨4887541083903188950473065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3258360722602125966982043 4887541083903188950473065)
        ·
          refine ⟨3665655812927391712854799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4887541083903188950473065 3665655812927391712854799)
          ·
            refine ⟨5498483719391087569282199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3665655812927391712854799 5498483719391087569282199)
            ·
              refine ⟨8247725579086631353923299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5498483719391087569282199 8247725579086631353923299)
              ·
                refine ⟨12371588368629947030884949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8247725579086631353923299 12371588368629947030884949)
                ·
                  refine ⟨144979551194882191768183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12371588368629947030884949 144979551194882191768183)
                  ·
                    rfl

theorem cell20_317640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 8].length) (baseStart_317640 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_317640 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_317640 prefixEnd_317640 := by exact prefixLift 317640
  have htrace : WordTrace (prefixWord ++ tailWord_317640) baseStart_317640 baseEnd_317640 := by
    simpa [prefixWord, tailWord_317640, baseEnd_317640] using wordTrace_append hprefix tailTrace_317640
  have hstable : (prefixWord ++ tailWord_317640).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317640).length < 2 ^ (prefixWord ++ tailWord_317640).sum := by decide
  have hdescent : baseEnd_317640 < baseStart_317640 := by decide
  rcases family_descends (prefixWord ++ tailWord_317640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317647 : List Nat := [1, 1, 2, 1, 1, 3, 11]
def baseStart_317647 : Nat := 118140960795 + 317647 * 2 ^ 59
def prefixEnd_317647 : Nat := 4983230072969 + 3 ^ 40 * 317647 * 2
def baseEnd_317647 : Nat := 16109194020624586503869

theorem tailTrace_317647 : CollatzResearch.WordTrace tailWord_317647 prefixEnd_317647 16109194020624586503869 := by
  unfold tailWord_317647
  simp only [CollatzResearch.WordTrace]
  refine ⟨11585537880226643633663195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7723691920151095755775463 11585537880226643633663195)
  ·
    refine ⟨17378306820339965450494793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11585537880226643633663195 17378306820339965450494793)
    ·
      refine ⟨13033730115254974087871095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17378306820339965450494793 13033730115254974087871095)
      ·
        refine ⟨19550595172882461131806643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13033730115254974087871095 19550595172882461131806643)
        ·
          refine ⟨29325892759323691697709965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19550595172882461131806643 29325892759323691697709965)
          ·
            refine ⟨10997209784746384386641237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29325892759323691697709965 10997209784746384386641237)
            ·
              refine ⟨16109194020624586503869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 10997209784746384386641237 16109194020624586503869)
              ·
                rfl

theorem cell20_317647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 11].length) (baseStart_317647 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_317647 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_317647 prefixEnd_317647 := by exact prefixLift 317647
  have htrace : WordTrace (prefixWord ++ tailWord_317647) baseStart_317647 baseEnd_317647 := by
    simpa [prefixWord, tailWord_317647, baseEnd_317647] using wordTrace_append hprefix tailTrace_317647
  have hstable : (prefixWord ++ tailWord_317647).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317647).length < 2 ^ (prefixWord ++ tailWord_317647).sum := by decide
  have hdescent : baseEnd_317647 < baseStart_317647 := by decide
  rcases family_descends (prefixWord ++ tailWord_317647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317650 : List Nat := [3, 2, 2, 2, 1, 3, 1, 1, 5]
def baseStart_317650 : Nat := 118140960795 + 317650 * 2 ^ 59
def prefixEnd_317650 : Nat := 4983230072969 + 3 ^ 40 * 317650 * 2
def baseEnd_317650 : Nat := 144984115467366601434809

theorem tailTrace_317650 : CollatzResearch.WordTrace tailWord_317650 prefixEnd_317650 144984115467366601434809 := by
  unfold tailWord_317650
  simp only [CollatzResearch.WordTrace]
  refine ⟨2896411824803943786505601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7723764866143850097348269 2896411824803943786505601)
  ·
    refine ⟨2172308868602957839879201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2896411824803943786505601 2172308868602957839879201)
    ·
      refine ⟨1629231651452218379909401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2172308868602957839879201 1629231651452218379909401)
      ·
        refine ⟨1221923738589163784932051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1629231651452218379909401 1221923738589163784932051)
        ·
          refine ⟨1832885607883745677398077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1221923738589163784932051 1832885607883745677398077)
          ·
            refine ⟨687332102956404629024279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1832885607883745677398077 687332102956404629024279)
            ·
              refine ⟨1030998154434606943536419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 687332102956404629024279 1030998154434606943536419)
              ·
                refine ⟨1546497231651910415304629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1030998154434606943536419 1546497231651910415304629)
                ·
                  refine ⟨144984115467366601434809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1546497231651910415304629 144984115467366601434809)
                  ·
                    rfl

theorem cell20_317650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 1, 5].length) (baseStart_317650 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_317650 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_317650 prefixEnd_317650 := by exact prefixLift 317650
  have htrace : WordTrace (prefixWord ++ tailWord_317650) baseStart_317650 baseEnd_317650 := by
    simpa [prefixWord, tailWord_317650, baseEnd_317650] using wordTrace_append hprefix tailTrace_317650
  have hstable : (prefixWord ++ tailWord_317650).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317650).length < 2 ^ (prefixWord ++ tailWord_317650).sum := by decide
  have hdescent : baseEnd_317650 < baseStart_317650 := by decide
  rcases family_descends (prefixWord ++ tailWord_317650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317677 : List Nat := [1, 5, 1, 2, 4, 1, 2, 4]
def baseStart_317677 : Nat := 118140960795 + 317677 * 2 ^ 59
def prefixEnd_317677 : Nat := 4983230072969 + 3 ^ 40 * 317677 * 2
def baseEnd_317677 : Nat := 48332146334358169178233

theorem tailTrace_317677 : CollatzResearch.WordTrace tailWord_317677 prefixEnd_317677 48332146334358169178233 := by
  unfold tailWord_317677
  simp only [CollatzResearch.WordTrace]
  refine ⟨11586632070117958757255285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7724421380078639171503523 11586632070117958757255285)
  ·
    refine ⟨1086246756573558633492683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11586632070117958757255285 1086246756573558633492683)
    ·
      refine ⟨1629370134860337950239025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1086246756573558633492683 1629370134860337950239025)
      ·
        refine ⟨1222027601145253462679269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1629370134860337950239025 1222027601145253462679269)
        ·
          refine ⟨229130175214735024252363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1222027601145253462679269 229130175214735024252363)
          ·
            refine ⟨343695262822102536378545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 229130175214735024252363 343695262822102536378545)
            ·
              refine ⟨257771447116576902283909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 343695262822102536378545 257771447116576902283909)
              ·
                refine ⟨48332146334358169178233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 257771447116576902283909 48332146334358169178233)
                ·
                  rfl

theorem cell20_317677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 2, 4].length) (baseStart_317677 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_317677 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_317677 prefixEnd_317677 := by exact prefixLift 317677
  have htrace : WordTrace (prefixWord ++ tailWord_317677) baseStart_317677 baseEnd_317677 := by
    simpa [prefixWord, tailWord_317677, baseEnd_317677] using wordTrace_append hprefix tailTrace_317677
  have hstable : (prefixWord ++ tailWord_317677).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317677).length < 2 ^ (prefixWord ++ tailWord_317677).sum := by decide
  have hdescent : baseEnd_317677 < baseStart_317677 := by decide
  rcases family_descends (prefixWord ++ tailWord_317677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317722 : List Nat := [3, 1, 1, 3, 4, 2, 2, 1, 3]
def baseStart_317722 : Nat := 118140960795 + 317722 * 2 ^ 59
def prefixEnd_317722 : Nat := 4983230072969 + 3 ^ 40 * 317722 * 2
def baseEnd_317722 : Nat := 145016978229254351034515

theorem tailTrace_317722 : CollatzResearch.WordTrace tailWord_317722 prefixEnd_317722 145016978229254351034515 := by
  unfold tailWord_317722
  simp only [CollatzResearch.WordTrace]
  refine ⟨2897068338738732860660855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7725515569969954295095613 2897068338738732860660855)
  ·
    refine ⟨4345602508108099290991283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2897068338738732860660855 4345602508108099290991283)
    ·
      refine ⟨6518403762162148936486925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4345602508108099290991283 6518403762162148936486925)
      ·
        refine ⟨2444401410810805851182597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6518403762162148936486925 2444401410810805851182597)
        ·
          refine ⟨458325264527026097096737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2444401410810805851182597 458325264527026097096737)
          ·
            refine ⟨343743948395269572822553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 458325264527026097096737 343743948395269572822553)
            ·
              refine ⟨257807961296452179616915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 343743948395269572822553 257807961296452179616915)
              ·
                refine ⟨386711941944678269425373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 257807961296452179616915 386711941944678269425373)
                ·
                  refine ⟨145016978229254351034515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 386711941944678269425373 145016978229254351034515)
                  ·
                    rfl

theorem cell20_317722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 2, 1, 3].length) (baseStart_317722 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_317722 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_317722 prefixEnd_317722 := by exact prefixLift 317722
  have htrace : WordTrace (prefixWord ++ tailWord_317722) baseStart_317722 baseEnd_317722 := by
    simpa [prefixWord, tailWord_317722, baseEnd_317722] using wordTrace_append hprefix tailTrace_317722
  have hstable : (prefixWord ++ tailWord_317722).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317722).length < 2 ^ (prefixWord ++ tailWord_317722).sum := by decide
  have hdescent : baseEnd_317722 < baseStart_317722 := by decide
  rcases family_descends (prefixWord ++ tailWord_317722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317723 : List Nat := [1, 1, 1, 1, 1, 1, 7, 7]
def baseStart_317723 : Nat := 118140960795 + 317723 * 2 ^ 59
def prefixEnd_317723 : Nat := 4983230072969 + 3 ^ 40 * 317723 * 2
def baseEnd_317723 : Nat := 48339144885500930667059

theorem tailTrace_317723 : CollatzResearch.WordTrace tailWord_317723 prefixEnd_317723 48339144885500930667059 := by
  unfold tailWord_317723
  simp only [CollatzResearch.WordTrace]
  refine ⟨11588309827951308613429823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7725539885300872408953215 11588309827951308613429823)
  ·
    refine ⟨17382464741926962920144735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11588309827951308613429823 17382464741926962920144735)
    ·
      refine ⟨26073697112890444380217103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17382464741926962920144735 26073697112890444380217103)
      ·
        refine ⟨39110545669335666570325655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26073697112890444380217103 39110545669335666570325655)
        ·
          refine ⟨58665818504003499855488483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39110545669335666570325655 58665818504003499855488483)
          ·
            refine ⟨87998727756005249783232725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58665818504003499855488483 87998727756005249783232725)
            ·
              refine ⟨2062470181781373041794517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 87998727756005249783232725 2062470181781373041794517)
              ·
                refine ⟨48339144885500930667059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2062470181781373041794517 48339144885500930667059)
                ·
                  rfl

theorem cell20_317723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 7].length) (baseStart_317723 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_317723 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_317723 prefixEnd_317723 := by exact prefixLift 317723
  have htrace : WordTrace (prefixWord ++ tailWord_317723) baseStart_317723 baseEnd_317723 := by
    simpa [prefixWord, tailWord_317723, baseEnd_317723] using wordTrace_append hprefix tailTrace_317723
  have hstable : (prefixWord ++ tailWord_317723).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317723).length < 2 ^ (prefixWord ++ tailWord_317723).sum := by decide
  have hdescent : baseEnd_317723 < baseStart_317723 := by decide
  rcases family_descends (prefixWord ++ tailWord_317723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317778 : List Nat := [3, 2, 2, 1, 1, 1, 5, 5]
def baseStart_317778 : Nat := 118140960795 + 317778 * 2 ^ 59
def prefixEnd_317778 : Nat := 4983230072969 + 3 ^ 40 * 317778 * 2
def baseEnd_317778 : Nat := 48347512718389015055873

theorem tailTrace_317778 : CollatzResearch.WordTrace tailWord_317778 prefixEnd_317778 48347512718389015055873 := by
  unfold tailWord_317778
  simp only [CollatzResearch.WordTrace]
  refine ⟨2897578960688013251670497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7726877228501368671121325 2897578960688013251670497)
  ·
    refine ⟨2173184220516009938752873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2897578960688013251670497 2173184220516009938752873)
    ·
      refine ⟨1629888165387007454064655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2173184220516009938752873 1629888165387007454064655)
      ·
        refine ⟨2444832248080511181096983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1629888165387007454064655 2444832248080511181096983)
        ·
          refine ⟨3667248372120766771645475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2444832248080511181096983 3667248372120766771645475)
          ·
            refine ⟨5500872558181150157468213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3667248372120766771645475 5500872558181150157468213)
            ·
              refine ⟨515706802329482827262645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5500872558181150157468213 515706802329482827262645)
              ·
                refine ⟨48347512718389015055873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 515706802329482827262645 48347512718389015055873)
                ·
                  rfl

theorem cell20_317778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 5, 5].length) (baseStart_317778 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_317778 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_317778 prefixEnd_317778 := by exact prefixLift 317778
  have htrace : WordTrace (prefixWord ++ tailWord_317778) baseStart_317778 baseEnd_317778 := by
    simpa [prefixWord, tailWord_317778, baseEnd_317778] using wordTrace_append hprefix tailTrace_317778
  have hstable : (prefixWord ++ tailWord_317778).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317778).length < 2 ^ (prefixWord ++ tailWord_317778).sum := by decide
  have hdescent : baseEnd_317778 < baseStart_317778 := by decide
  rcases family_descends (prefixWord ++ tailWord_317778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317881 : List Nat := [1, 2, 1, 4, 3, 2, 3, 2, 2]
def baseStart_317881 : Nat := 118140960795 + 317881 * 2 ^ 59
def prefixEnd_317881 : Nat := 4983230072969 + 3 ^ 40 * 317881 * 2
def baseEnd_317881 : Nat := 145089550161756464733865

theorem tailTrace_317881 : CollatzResearch.WordTrace tailWord_317881 prefixEnd_317881 145089550161756464733865 := by
  unfold tailWord_317881
  simp only [CollatzResearch.WordTrace]
  refine ⟨11594072561378901597681497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7729381707585934398454331 11594072561378901597681497)
  ·
    refine ⟨8695554421034176198261123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11594072561378901597681497 8695554421034176198261123)
    ·
      refine ⟨13043331631551264297391685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8695554421034176198261123 13043331631551264297391685)
      ·
        refine ⟨2445624680915862055760941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13043331631551264297391685 2445624680915862055760941)
        ·
          refine ⟨917109255343448270910353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2445624680915862055760941 917109255343448270910353)
          ·
            refine ⟨687831941507586203182765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 917109255343448270910353 687831941507586203182765)
            ·
              refine ⟨257936978065344826193537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 687831941507586203182765 257936978065344826193537)
              ·
                refine ⟨193452733549008619645153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 257936978065344826193537 193452733549008619645153)
                ·
                  refine ⟨145089550161756464733865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 193452733549008619645153 145089550161756464733865)
                  ·
                    rfl

theorem cell20_317881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 3, 2, 2].length) (baseStart_317881 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_317881 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_317881 prefixEnd_317881 := by exact prefixLift 317881
  have htrace : WordTrace (prefixWord ++ tailWord_317881) baseStart_317881 baseEnd_317881 := by
    simpa [prefixWord, tailWord_317881, baseEnd_317881] using wordTrace_append hprefix tailTrace_317881
  have hstable : (prefixWord ++ tailWord_317881).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317881).length < 2 ^ (prefixWord ++ tailWord_317881).sum := by decide
  have hdescent : baseEnd_317881 < baseStart_317881 := by decide
  rcases family_descends (prefixWord ++ tailWord_317881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317885 : List Nat := [1, 4, 1, 2, 2, 2, 3, 1, 4]
def baseStart_317885 : Nat := 118140960795 + 317885 * 2 ^ 59
def prefixEnd_317885 : Nat := 4983230072969 + 3 ^ 40 * 317885 * 2
def baseEnd_317885 : Nat := 145091375870750228600515

theorem tailTrace_317885 : CollatzResearch.WordTrace tailWord_317885 prefixEnd_317885 145091375870750228600515 := by
  unfold tailWord_317885
  simp only [CollatzResearch.WordTrace]
  refine ⟨11594218453364410280827109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7729478968909606853884739 11594218453364410280827109)
  ·
    refine ⟨2173915960005826927655083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11594218453364410280827109 2173915960005826927655083)
    ·
      refine ⟨3260873940008740391482625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2173915960005826927655083 3260873940008740391482625)
      ·
        refine ⟨2445655455006555293611969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3260873940008740391482625 2445655455006555293611969)
        ·
          refine ⟨1834241591254916470208977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2445655455006555293611969 1834241591254916470208977)
          ·
            refine ⟨1375681193441187352656733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1834241591254916470208977 1375681193441187352656733)
            ·
              refine ⟨515880447540445257246275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1375681193441187352656733 515880447540445257246275)
              ·
                refine ⟨773820671310667885869413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 515880447540445257246275 773820671310667885869413)
                ·
                  refine ⟨145091375870750228600515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 773820671310667885869413 145091375870750228600515)
                  ·
                    rfl

theorem cell20_317885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 3, 1, 4].length) (baseStart_317885 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_317885 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_317885 prefixEnd_317885 := by exact prefixLift 317885
  have htrace : WordTrace (prefixWord ++ tailWord_317885) baseStart_317885 baseEnd_317885 := by
    simpa [prefixWord, tailWord_317885, baseEnd_317885] using wordTrace_append hprefix tailTrace_317885
  have hstable : (prefixWord ++ tailWord_317885).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317885).length < 2 ^ (prefixWord ++ tailWord_317885).sum := by decide
  have hdescent : baseEnd_317885 < baseStart_317885 := by decide
  rcases family_descends (prefixWord ++ tailWord_317885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317895 : List Nat := [1, 1, 4, 1, 1, 6, 2, 1, 3]
def baseStart_317895 : Nat := 118140960795 + 317895 * 2 ^ 59
def prefixEnd_317895 : Nat := 4983230072969 + 3 ^ 40 * 317895 * 2
def baseEnd_317895 : Nat := 145095940143234638267141

theorem tailTrace_317895 : CollatzResearch.WordTrace tailWord_317895 prefixEnd_317895 145095940143234638267141 := by
  unfold tailWord_317895
  simp only [CollatzResearch.WordTrace]
  refine ⟨11594583183328181988691139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7729722122218787992460759 11594583183328181988691139)
  ·
    refine ⟨17391874774992272983036709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11594583183328181988691139 17391874774992272983036709)
    ·
      refine ⟨3260976520311051184319383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17391874774992272983036709 3260976520311051184319383)
      ·
        refine ⟨4891464780466576776479075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3260976520311051184319383 4891464780466576776479075)
        ·
          refine ⟨7337197170699865164718613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4891464780466576776479075 7337197170699865164718613)
          ·
            refine ⟨343931117376556179596185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 7337197170699865164718613 343931117376556179596185)
            ·
              refine ⟨257948338032417134697139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 343931117376556179596185 257948338032417134697139)
              ·
                refine ⟨386922507048625702045709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 257948338032417134697139 386922507048625702045709)
                ·
                  refine ⟨145095940143234638267141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 386922507048625702045709 145095940143234638267141)
                  ·
                    rfl

theorem cell20_317895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 2, 1, 3].length) (baseStart_317895 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_317895 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_317895 prefixEnd_317895 := by exact prefixLift 317895
  have htrace : WordTrace (prefixWord ++ tailWord_317895) baseStart_317895 baseEnd_317895 := by
    simpa [prefixWord, tailWord_317895, baseEnd_317895] using wordTrace_append hprefix tailTrace_317895
  have hstable : (prefixWord ++ tailWord_317895).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317895).length < 2 ^ (prefixWord ++ tailWord_317895).sum := by decide
  have hdescent : baseEnd_317895 < baseStart_317895 := by decide
  rcases family_descends (prefixWord ++ tailWord_317895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317913 : List Nat := [1, 2, 1, 2, 4, 1, 1, 8]
def baseStart_317913 : Nat := 118140960795 + 317913 * 2 ^ 59
def prefixEnd_317913 : Nat := 4983230072969 + 3 ^ 40 * 317913 * 2
def baseEnd_317913 : Nat := 48368051944568858555689

theorem tailTrace_317913 : CollatzResearch.WordTrace tailWord_317913 prefixEnd_317913 48368051944568858555689 := by
  unfold tailWord_317913
  simp only [CollatzResearch.WordTrace]
  refine ⟨11595239697262971062846393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7730159798175314041897595 11595239697262971062846393)
  ·
    refine ⟨8696429772947228297134795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11595239697262971062846393 8696429772947228297134795)
    ·
      refine ⟨13044644659420842445702193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8696429772947228297134795 13044644659420842445702193)
      ·
        refine ⟨9783483494565631834276645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13044644659420842445702193 9783483494565631834276645)
        ·
          refine ⟨1834403155231055968926871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9783483494565631834276645 1834403155231055968926871)
          ·
            refine ⟨2751604732846583953390307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1834403155231055968926871 2751604732846583953390307)
            ·
              refine ⟨4127407099269875930085461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2751604732846583953390307 4127407099269875930085461)
              ·
                refine ⟨48368051944568858555689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4127407099269875930085461 48368051944568858555689)
                ·
                  rfl

theorem cell20_317913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 8].length) (baseStart_317913 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_317913 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_317913 prefixEnd_317913 := by exact prefixLift 317913
  have htrace : WordTrace (prefixWord ++ tailWord_317913) baseStart_317913 baseEnd_317913 := by
    simpa [prefixWord, tailWord_317913, baseEnd_317913] using wordTrace_append hprefix tailTrace_317913
  have hstable : (prefixWord ++ tailWord_317913).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317913).length < 2 ^ (prefixWord ++ tailWord_317913).sum := by decide
  have hdescent : baseEnd_317913 < baseStart_317913 := by decide
  rcases family_descends (prefixWord ++ tailWord_317913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317933 : List Nat := [1, 5, 1, 3, 1, 2, 2, 2, 3]
def baseStart_317933 : Nat := 118140960795 + 317933 * 2 ^ 59
def prefixEnd_317933 : Nat := 4983230072969 + 3 ^ 40 * 317933 * 2
def baseEnd_317933 : Nat := 145113284378675395000319

theorem tailTrace_317933 : CollatzResearch.WordTrace tailWord_317933 prefixEnd_317933 145113284378675395000319 := by
  unfold tailWord_317933
  simp only [CollatzResearch.WordTrace]
  refine ⟨11595969157190514478574453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7730646104793676319049635 11595969157190514478574453)
  ·
    refine ⟨1087122108486610732366355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11595969157190514478574453 1087122108486610732366355)
    ·
      refine ⟨1630683162729916098549533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1087122108486610732366355 1630683162729916098549533)
      ·
        refine ⟨611506186023718536956075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1630683162729916098549533 611506186023718536956075)
        ·
          refine ⟨917259279035577805434113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 611506186023718536956075 917259279035577805434113)
          ·
            refine ⟨687944459276683354075585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 917259279035577805434113 687944459276683354075585)
            ·
              refine ⟨515958344457512515556689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 687944459276683354075585 515958344457512515556689)
              ·
                refine ⟨386968758343134386667517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 515958344457512515556689 386968758343134386667517)
                ·
                  refine ⟨145113284378675395000319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 386968758343134386667517 145113284378675395000319)
                  ·
                    rfl

theorem cell20_317933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 2, 2, 3].length) (baseStart_317933 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_317933 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_317933 prefixEnd_317933 := by exact prefixLift 317933
  have htrace : WordTrace (prefixWord ++ tailWord_317933) baseStart_317933 baseEnd_317933 := by
    simpa [prefixWord, tailWord_317933, baseEnd_317933] using wordTrace_append hprefix tailTrace_317933
  have hstable : (prefixWord ++ tailWord_317933).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317933).length < 2 ^ (prefixWord ++ tailWord_317933).sum := by decide
  have hdescent : baseEnd_317933 < baseStart_317933 := by decide
  rcases family_descends (prefixWord ++ tailWord_317933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317944 : List Nat := [2, 1, 2, 1, 1, 4, 2, 3, 4]
def baseStart_317944 : Nat := 118140960795 + 317944 * 2 ^ 59
def prefixEnd_317944 : Nat := 4983230072969 + 3 ^ 40 * 317944 * 2
def baseEnd_317944 : Nat := 145118305078408245633607

theorem tailTrace_317944 : CollatzResearch.WordTrace tailWord_317944 prefixEnd_317944 145118305078408245633607 := by
  unfold tailWord_317944
  simp only [CollatzResearch.WordTrace]
  refine ⟨5798185180075331678612443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7730913573433775571483257 5798185180075331678612443)
  ·
    refine ⟨8697277770112997517918665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5798185180075331678612443 8697277770112997517918665)
    ·
      refine ⟨6522958327584748138438999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8697277770112997517918665 6522958327584748138438999)
      ·
        refine ⟨9784437491377122207658499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6522958327584748138438999 9784437491377122207658499)
        ·
          refine ⟨14676656237065683311487749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9784437491377122207658499 14676656237065683311487749)
          ·
            refine ⟨2751873044449815620903953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14676656237065683311487749 2751873044449815620903953)
            ·
              refine ⟨2063904783337361715677965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2751873044449815620903953 2063904783337361715677965)
              ·
                refine ⟨773964293751510643379237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2063904783337361715677965 773964293751510643379237)
                ·
                  refine ⟨145118305078408245633607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 773964293751510643379237 145118305078408245633607)
                  ·
                    rfl

theorem cell20_317944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 3, 4].length) (baseStart_317944 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_317944 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_317944 prefixEnd_317944 := by exact prefixLift 317944
  have htrace : WordTrace (prefixWord ++ tailWord_317944) baseStart_317944 baseEnd_317944 := by
    simpa [prefixWord, tailWord_317944, baseEnd_317944] using wordTrace_append hprefix tailTrace_317944
  have hstable : (prefixWord ++ tailWord_317944).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317944).length < 2 ^ (prefixWord ++ tailWord_317944).sum := by decide
  have hdescent : baseEnd_317944 < baseStart_317944 := by decide
  rcases family_descends (prefixWord ++ tailWord_317944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317988 : List Nat := [2, 3, 1, 5, 1, 2, 1, 2, 3]
def baseStart_317988 : Nat := 118140960795 + 317988 * 2 ^ 59
def prefixEnd_317988 : Nat := 4983230072969 + 3 ^ 40 * 317988 * 2
def baseEnd_317988 : Nat := 145138387877339648166761

theorem tailTrace_317988 : CollatzResearch.WordTrace tailWord_317988 prefixEnd_317988 145138387877339648166761 := by
  unfold tailWord_317988
  simp only [CollatzResearch.WordTrace]
  refine ⟨5798987585995629435913309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7731983447994172581217745 5798987585995629435913309)
  ·
    refine ⟨2174620344748361038467491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5798987585995629435913309 2174620344748361038467491)
    ·
      refine ⟨3261930517122541557701237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2174620344748361038467491 3261930517122541557701237)
      ·
        refine ⟨305805985980238271034491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3261930517122541557701237 305805985980238271034491)
        ·
          refine ⟨458708978970357406551737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 305805985980238271034491 458708978970357406551737)
          ·
            refine ⟨344031734227768054913803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 458708978970357406551737 344031734227768054913803)
            ·
              refine ⟨516047601341652082370705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 344031734227768054913803 516047601341652082370705)
              ·
                refine ⟨387035701006239061778029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 516047601341652082370705 387035701006239061778029)
                ·
                  refine ⟨145138387877339648166761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 387035701006239061778029 145138387877339648166761)
                  ·
                    rfl

theorem cell20_317988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 1, 2, 3].length) (baseStart_317988 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_317988 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_317988 prefixEnd_317988 := by exact prefixLift 317988
  have htrace : WordTrace (prefixWord ++ tailWord_317988) baseStart_317988 baseEnd_317988 := by
    simpa [prefixWord, tailWord_317988, baseEnd_317988] using wordTrace_append hprefix tailTrace_317988
  have hstable : (prefixWord ++ tailWord_317988).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317988).length < 2 ^ (prefixWord ++ tailWord_317988).sum := by decide
  have hdescent : baseEnd_317988 < baseStart_317988 := by decide
  rcases family_descends (prefixWord ++ tailWord_317988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317992 : List Nat := [2, 1, 5, 2, 1, 2, 1, 1, 5]
def baseStart_317992 : Nat := 118140960795 + 317992 * 2 ^ 59
def prefixEnd_317992 : Nat := 4983230072969 + 3 ^ 40 * 317992 * 2
def baseEnd_317992 : Nat := 145140213586333412033411

theorem tailTrace_317992 : CollatzResearch.WordTrace tailWord_317992 prefixEnd_317992 145140213586333412033411 := by
  unfold tailWord_317992
  simp only [CollatzResearch.WordTrace]
  refine ⟨5799060531988383777486115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7732080709317845036648153 5799060531988383777486115)
  ·
    refine ⟨8698590797982575666229173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5799060531988383777486115 8698590797982575666229173)
    ·
      refine ⟨815492887310866468708985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8698590797982575666229173 815492887310866468708985)
      ·
        refine ⟨611619665483149851531739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 815492887310866468708985 611619665483149851531739)
        ·
          refine ⟨917429498224724777297609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 611619665483149851531739 917429498224724777297609)
          ·
            refine ⟨688072123668543582973207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 917429498224724777297609 688072123668543582973207)
            ·
              refine ⟨1032108185502815374459811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 688072123668543582973207 1032108185502815374459811)
              ·
                refine ⟨1548162278254223061689717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1032108185502815374459811 1548162278254223061689717)
                ·
                  refine ⟨145140213586333412033411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1548162278254223061689717 145140213586333412033411)
                  ·
                    rfl

theorem cell20_317992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 1, 5].length) (baseStart_317992 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_317992 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_317992 prefixEnd_317992 := by exact prefixLift 317992
  have htrace : WordTrace (prefixWord ++ tailWord_317992) baseStart_317992 baseEnd_317992 := by
    simpa [prefixWord, tailWord_317992, baseEnd_317992] using wordTrace_append hprefix tailTrace_317992
  have hstable : (prefixWord ++ tailWord_317992).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317992).length < 2 ^ (prefixWord ++ tailWord_317992).sum := by decide
  have hdescent : baseEnd_317992 < baseStart_317992 := by decide
  rcases family_descends (prefixWord ++ tailWord_317992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318023 : List Nat := [1, 1, 4, 1, 4, 3, 2, 4]
def baseStart_318023 : Nat := 118140960795 + 318023 * 2 ^ 59
def prefixEnd_318023 : Nat := 4983230072969 + 3 ^ 40 * 318023 * 2
def baseEnd_318023 : Nat := 48384787610345027333317

theorem tailTrace_318023 : CollatzResearch.WordTrace tailWord_318023 prefixEnd_318023 48384787610345027333317 := by
  unfold tailWord_318023
  simp only [CollatzResearch.WordTrace]
  refine ⟨11599251726864459849350723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7732834484576306566233815 11599251726864459849350723)
  ·
    refine ⟨17398877590296689774026085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11599251726864459849350723 17398877590296689774026085)
    ·
      refine ⟨3262289548180629332629891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17398877590296689774026085 3262289548180629332629891)
      ·
        refine ⟨4893434322270943998944837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3262289548180629332629891 4893434322270943998944837)
        ·
          refine ⟨917518935425801999802157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4893434322270943998944837 917518935425801999802157)
          ·
            refine ⟨344069600784675749925809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 917518935425801999802157 344069600784675749925809)
            ·
              refine ⟨258052200588506812444357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 344069600784675749925809 258052200588506812444357)
              ·
                refine ⟨48384787610345027333317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 258052200588506812444357 48384787610345027333317)
                ·
                  rfl

theorem cell20_318023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 2, 4].length) (baseStart_318023 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_318023 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_318023 prefixEnd_318023 := by exact prefixLift 318023
  have htrace : WordTrace (prefixWord ++ tailWord_318023) baseStart_318023 baseEnd_318023 := by
    simpa [prefixWord, tailWord_318023, baseEnd_318023] using wordTrace_append hprefix tailTrace_318023
  have hstable : (prefixWord ++ tailWord_318023).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318023).length < 2 ^ (prefixWord ++ tailWord_318023).sum := by decide
  have hdescent : baseEnd_318023 < baseStart_318023 := by decide
  rcases family_descends (prefixWord ++ tailWord_318023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318046 : List Nat := [4, 4, 1, 2, 1, 1, 3, 2, 2]
def baseStart_318046 : Nat := 118140960795 + 318046 * 2 ^ 59
def prefixEnd_318046 : Nat := 4983230072969 + 3 ^ 40 * 318046 * 2
def baseEnd_318046 : Nat := 145164860657749224233191

theorem tailTrace_318046 : CollatzResearch.WordTrace tailWord_318046 prefixEnd_318046 145164860657749224233191 := by
  unfold tailWord_318046
  simp only [CollatzResearch.WordTrace]
  refine ⟨1450011325722641847179749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7733393737187423184958661 1450011325722641847179749)
  ·
    refine ⟨271877123572995346346203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1450011325722641847179749 271877123572995346346203)
    ·
      refine ⟨407815685359493019519305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 271877123572995346346203 407815685359493019519305)
      ·
        refine ⟨305861764019619764639479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 407815685359493019519305 305861764019619764639479)
        ·
          refine ⟨458792646029429646959219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 305861764019619764639479 458792646029429646959219)
          ·
            refine ⟨688188969044144470438829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 458792646029429646959219 688188969044144470438829)
            ·
              refine ⟨258070863391554176414561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 688188969044144470438829 258070863391554176414561)
              ·
                refine ⟨193553147543665632310921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 258070863391554176414561 193553147543665632310921)
                ·
                  refine ⟨145164860657749224233191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 193553147543665632310921 145164860657749224233191)
                  ·
                    rfl

theorem cell20_318046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_318046 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_318046 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_318046 prefixEnd_318046 := by exact prefixLift 318046
  have htrace : WordTrace (prefixWord ++ tailWord_318046) baseStart_318046 baseEnd_318046 := by
    simpa [prefixWord, tailWord_318046, baseEnd_318046] using wordTrace_append hprefix tailTrace_318046
  have hstable : (prefixWord ++ tailWord_318046).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318046).length < 2 ^ (prefixWord ++ tailWord_318046).sum := by decide
  have hdescent : baseEnd_318046 < baseStart_318046 := by decide
  rcases family_descends (prefixWord ++ tailWord_318046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318050 : List Nat := [3, 3, 2, 3, 2, 1, 1, 1, 4]
def baseStart_318050 : Nat := 118140960795 + 318050 * 2 ^ 59
def prefixEnd_318050 : Nat := 4983230072969 + 3 ^ 40 * 318050 * 2
def baseEnd_318050 : Nat := 145166686366742988099841

theorem tailTrace_318050 : CollatzResearch.WordTrace tailWord_318050 prefixEnd_318050 145166686366742988099841 := by
  unfold tailWord_318050
  simp only [CollatzResearch.WordTrace]
  refine ⟨2900059124441660865145901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7733490998511095640389069 2900059124441660865145901)
  ·
    refine ⟨1087522171665622824429713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2900059124441660865145901 1087522171665622824429713)
    ·
      refine ⟨815641628749217118322285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1087522171665622824429713 815641628749217118322285)
      ·
        refine ⟨305865610780956419370857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 815641628749217118322285 305865610780956419370857)
        ·
          refine ⟨229399208085717314528143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 305865610780956419370857 229399208085717314528143)
          ·
            refine ⟨344098812128575971792215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 229399208085717314528143 344098812128575971792215)
            ·
              refine ⟨516148218192863957688323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 344098812128575971792215 516148218192863957688323)
              ·
                refine ⟨774222327289295936532485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 516148218192863957688323 774222327289295936532485)
                ·
                  refine ⟨145166686366742988099841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 774222327289295936532485 145166686366742988099841)
                  ·
                    rfl

theorem cell20_318050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 1, 1, 4].length) (baseStart_318050 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_318050 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_318050 prefixEnd_318050 := by exact prefixLift 318050
  have htrace : WordTrace (prefixWord ++ tailWord_318050) baseStart_318050 baseEnd_318050 := by
    simpa [prefixWord, tailWord_318050, baseEnd_318050] using wordTrace_append hprefix tailTrace_318050
  have hstable : (prefixWord ++ tailWord_318050).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318050).length < 2 ^ (prefixWord ++ tailWord_318050).sum := by decide
  have hdescent : baseEnd_318050 < baseStart_318050 := by decide
  rcases family_descends (prefixWord ++ tailWord_318050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318051 : List Nat := [1, 1, 1, 5, 1, 2, 2, 4, 3]
def baseStart_318051 : Nat := 118140960795 + 318051 * 2 ^ 59
def prefixEnd_318051 : Nat := 4983230072969 + 3 ^ 40 * 318051 * 2
def baseEnd_318051 : Nat := 145167142793991429066503

theorem tailTrace_318051 : CollatzResearch.WordTrace tailWord_318051 prefixEnd_318051 145167142793991429066503 := by
  unfold tailWord_318051
  simp only [CollatzResearch.WordTrace]
  refine ⟨11600272970763020631370007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7733515313842013754246671 11600272970763020631370007)
  ·
    refine ⟨17400409456144530947055011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11600272970763020631370007 17400409456144530947055011)
    ·
      refine ⟨26100614184216796420582517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17400409456144530947055011 26100614184216796420582517)
      ·
        refine ⟨2446932579770324664429611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26100614184216796420582517 2446932579770324664429611)
        ·
          refine ⟨3670398869655486996644417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2446932579770324664429611 3670398869655486996644417)
          ·
            refine ⟨2752799152241615247483313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3670398869655486996644417 2752799152241615247483313)
            ·
              refine ⟨2064599364181211435612485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2752799152241615247483313 2064599364181211435612485)
              ·
                refine ⟨387112380783977144177341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2064599364181211435612485 387112380783977144177341)
                ·
                  refine ⟨145167142793991429066503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 387112380783977144177341 145167142793991429066503)
                  ·
                    rfl

theorem cell20_318051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 4, 3].length) (baseStart_318051 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_318051 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_318051 prefixEnd_318051 := by exact prefixLift 318051
  have htrace : WordTrace (prefixWord ++ tailWord_318051) baseStart_318051 baseEnd_318051 := by
    simpa [prefixWord, tailWord_318051, baseEnd_318051] using wordTrace_append hprefix tailTrace_318051
  have hstable : (prefixWord ++ tailWord_318051).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318051).length < 2 ^ (prefixWord ++ tailWord_318051).sum := by decide
  have hdescent : baseEnd_318051 < baseStart_318051 := by decide
  rcases family_descends (prefixWord ++ tailWord_318051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318064 : List Nat := [2, 1, 1, 1, 8, 1, 2, 1, 3]
def baseStart_318064 : Nat := 118140960795 + 318064 * 2 ^ 59
def prefixEnd_318064 : Nat := 4983230072969 + 3 ^ 40 * 318064 * 2
def baseEnd_318064 : Nat := 145173076348221161633117

theorem tailTrace_318064 : CollatzResearch.WordTrace tailWord_318064 prefixEnd_318064 145173076348221161633117 := by
  unfold tailWord_318064
  simp only [CollatzResearch.WordTrace]
  refine ⟨5800373559857961925796623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7733831413143949234395497 5800373559857961925796623)
  ·
    refine ⟨8700560339786942888694935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5800373559857961925796623 8700560339786942888694935)
    ·
      refine ⟨13050840509680414333042403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8700560339786942888694935 13050840509680414333042403)
      ·
        refine ⟨19576260764520621499563605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13050840509680414333042403 19576260764520621499563605)
        ·
          refine ⟨229409305834226033198011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 19576260764520621499563605 229409305834226033198011)
          ·
            refine ⟨344113958751339049797017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 229409305834226033198011 344113958751339049797017)
            ·
              refine ⟨258085469063504287347763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 344113958751339049797017 258085469063504287347763)
              ·
                refine ⟨387128203595256431021645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 258085469063504287347763 387128203595256431021645)
                ·
                  refine ⟨145173076348221161633117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 387128203595256431021645 145173076348221161633117)
                  ·
                    rfl

theorem cell20_318064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 2, 1, 3].length) (baseStart_318064 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_318064 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_318064 prefixEnd_318064 := by exact prefixLift 318064
  have htrace : WordTrace (prefixWord ++ tailWord_318064) baseStart_318064 baseEnd_318064 := by
    simpa [prefixWord, tailWord_318064, baseEnd_318064] using wordTrace_append hprefix tailTrace_318064
  have hstable : (prefixWord ++ tailWord_318064).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318064).length < 2 ^ (prefixWord ++ tailWord_318064).sum := by decide
  have hdescent : baseEnd_318064 < baseStart_318064 := by decide
  rcases family_descends (prefixWord ++ tailWord_318064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318127 : List Nat := [1, 1, 2, 1, 2, 5, 2, 3, 3]
def baseStart_318127 : Nat := 118140960795 + 318127 * 2 ^ 59
def prefixEnd_318127 : Nat := 4983230072969 + 3 ^ 40 * 318127 * 2
def baseEnd_318127 : Nat := 145201831264872942532859

theorem tailTrace_318127 : CollatzResearch.WordTrace tailWord_318127 prefixEnd_318127 145201831264872942532859 := by
  unfold tailWord_318127
  simp only [CollatzResearch.WordTrace]
  refine ⟨11603044918487685611136635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7735363278991790407424423 11603044918487685611136635)
  ·
    refine ⟨17404567377731528416704953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11603044918487685611136635 17404567377731528416704953)
    ·
      refine ⟨13053425533298646312528715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17404567377731528416704953 13053425533298646312528715)
      ·
        refine ⟨19580138299947969468793073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13053425533298646312528715 19580138299947969468793073)
        ·
          refine ⟨14685103724960977101594805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19580138299947969468793073 14685103724960977101594805)
          ·
            refine ⟨1376728474215091603274513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14685103724960977101594805 1376728474215091603274513)
            ·
              refine ⟨1032546355661318702455885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1376728474215091603274513 1032546355661318702455885)
              ·
                refine ⟨387204883372994513420957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1032546355661318702455885 387204883372994513420957)
                ·
                  refine ⟨145201831264872942532859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 387204883372994513420957 145201831264872942532859)
                  ·
                    rfl

theorem cell20_318127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 3, 3].length) (baseStart_318127 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_318127 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_318127 prefixEnd_318127 := by exact prefixLift 318127
  have htrace : WordTrace (prefixWord ++ tailWord_318127) baseStart_318127 baseEnd_318127 := by
    simpa [prefixWord, tailWord_318127, baseEnd_318127] using wordTrace_append hprefix tailTrace_318127
  have hstable : (prefixWord ++ tailWord_318127).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318127).length < 2 ^ (prefixWord ++ tailWord_318127).sum := by decide
  have hdescent : baseEnd_318127 < baseStart_318127 := by decide
  rcases family_descends (prefixWord ++ tailWord_318127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318157 : List Nat := [1, 6, 2, 1, 3, 1, 1, 2, 3]
def baseStart_318157 : Nat := 118140960795 + 318157 * 2 ^ 59
def prefixEnd_318157 : Nat := 4983230072969 + 3 ^ 40 * 318157 * 2
def baseEnd_318157 : Nat := 145215524082326171532737

theorem tailTrace_318157 : CollatzResearch.WordTrace tailWord_318157 prefixEnd_318157 145215524082326171532737 := by
  unfold tailWord_318157
  simp only [CollatzResearch.WordTrace]
  refine ⟨11604139108379000734728725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7736092738919333823152483 11604139108379000734728725)
  ·
    refine ⟨543944020705265659440409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 11604139108379000734728725 543944020705265659440409)
    ·
      refine ⟨407958015528949244580307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 543944020705265659440409 407958015528949244580307)
      ·
        refine ⟨611937023293423866870461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 407958015528949244580307 611937023293423866870461)
        ·
          refine ⟨229476383735033950076423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 611937023293423866870461 229476383735033950076423)
          ·
            refine ⟨344214575602550925114635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 229476383735033950076423 344214575602550925114635)
            ·
              refine ⟨516321863403826387671953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 344214575602550925114635 516321863403826387671953)
              ·
                refine ⟨387241397552869790753965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 516321863403826387671953 387241397552869790753965)
                ·
                  refine ⟨145215524082326171532737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 387241397552869790753965 145215524082326171532737)
                  ·
                    rfl

theorem cell20_318157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 1, 2, 3].length) (baseStart_318157 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_318157 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_318157 prefixEnd_318157 := by exact prefixLift 318157
  have htrace : WordTrace (prefixWord ++ tailWord_318157) baseStart_318157 baseEnd_318157 := by
    simpa [prefixWord, tailWord_318157, baseEnd_318157] using wordTrace_append hprefix tailTrace_318157
  have hstable : (prefixWord ++ tailWord_318157).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318157).length < 2 ^ (prefixWord ++ tailWord_318157).sum := by decide
  have hdescent : baseEnd_318157 < baseStart_318157 := by decide
  rcases family_descends (prefixWord ++ tailWord_318157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318237 : List Nat := [1, 4, 2, 4, 1, 1, 1, 3, 3]
def baseStart_318237 : Nat := 118140960795 + 318237 * 2 ^ 59
def prefixEnd_318237 : Nat := 4983230072969 + 3 ^ 40 * 318237 * 2
def baseEnd_318237 : Nat := 145252038262201448865743

theorem tailTrace_318237 : CollatzResearch.WordTrace tailWord_318237 prefixEnd_318237 145252038262201448865743 := by
  unfold tailWord_318237
  simp only [CollatzResearch.WordTrace]
  refine ⟨11607056948089174397640965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7738037965392782931760643 11607056948089174397640965)
  ·
    refine ⟨2176323177766720199557681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11607056948089174397640965 2176323177766720199557681)
    ·
      refine ⟨1632242383325040149668261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2176323177766720199557681 1632242383325040149668261)
      ·
        refine ⟨306045446873445028062799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1632242383325040149668261 306045446873445028062799)
        ·
          refine ⟨459068170310167542094199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 306045446873445028062799 459068170310167542094199)
          ·
            refine ⟨688602255465251313141299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 459068170310167542094199 688602255465251313141299)
            ·
              refine ⟨1032903383197876969711949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 688602255465251313141299 1032903383197876969711949)
              ·
                refine ⟨387338768699203863641981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1032903383197876969711949 387338768699203863641981)
                ·
                  refine ⟨145252038262201448865743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 387338768699203863641981 145252038262201448865743)
                  ·
                    rfl

theorem cell20_318237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 3, 3].length) (baseStart_318237 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_318237 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_318237 prefixEnd_318237 := by exact prefixLift 318237
  have htrace : WordTrace (prefixWord ++ tailWord_318237) baseStart_318237 baseEnd_318237 := by
    simpa [prefixWord, tailWord_318237, baseEnd_318237] using wordTrace_append hprefix tailTrace_318237
  have hstable : (prefixWord ++ tailWord_318237).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318237).length < 2 ^ (prefixWord ++ tailWord_318237).sum := by decide
  have hdescent : baseEnd_318237 < baseStart_318237 := by decide
  rcases family_descends (prefixWord ++ tailWord_318237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318241 : List Nat := [1, 2, 3, 2, 1, 2, 3, 3, 3]
def baseStart_318241 : Nat := 118140960795 + 318241 * 2 ^ 59
def prefixEnd_318241 : Nat := 4983230072969 + 3 ^ 40 * 318241 * 2
def baseEnd_318241 : Nat := 145253863971195212732393

theorem tailTrace_318241 : CollatzResearch.WordTrace tailWord_318241 prefixEnd_318241 145253863971195212732393 := by
  unfold tailWord_318241
  simp only [CollatzResearch.WordTrace]
  refine ⟨11607202840074683080786577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7738135226716455387191051 11607202840074683080786577)
  ·
    refine ⟨8705402130056012310589933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11607202840074683080786577 8705402130056012310589933)
    ·
      refine ⟨3264525798771004616471225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8705402130056012310589933 3264525798771004616471225)
      ·
        refine ⟨2448394349078253462353419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3264525798771004616471225 2448394349078253462353419)
        ·
          refine ⟨3672591523617380193530129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2448394349078253462353419 3672591523617380193530129)
          ·
            refine ⟨2754443642713035145147597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3672591523617380193530129 2754443642713035145147597)
            ·
              refine ⟨1032916366017388179430349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2754443642713035145147597 1032916366017388179430349)
              ·
                refine ⟨387343637256520567286381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1032916366017388179430349 387343637256520567286381)
                ·
                  refine ⟨145253863971195212732393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 387343637256520567286381 145253863971195212732393)
                  ·
                    rfl

theorem cell20_318241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 3, 3].length) (baseStart_318241 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_318241 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_318241 prefixEnd_318241 := by exact prefixLift 318241
  have htrace : WordTrace (prefixWord ++ tailWord_318241) baseStart_318241 baseEnd_318241 := by
    simpa [prefixWord, tailWord_318241, baseEnd_318241] using wordTrace_append hprefix tailTrace_318241
  have hstable : (prefixWord ++ tailWord_318241).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318241).length < 2 ^ (prefixWord ++ tailWord_318241).sum := by decide
  have hdescent : baseEnd_318241 < baseStart_318241 := by decide
  rcases family_descends (prefixWord ++ tailWord_318241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318248 : List Nat := [2, 1, 5, 1, 1, 1, 2, 1, 6]
def baseStart_318248 : Nat := 118140960795 + 318248 * 2 ^ 59
def prefixEnd_318248 : Nat := 4983230072969 + 3 ^ 40 * 318248 * 2
def baseEnd_318248 : Nat := 145257058961934299499031

theorem tailTrace_318248 : CollatzResearch.WordTrace tailWord_318248 prefixEnd_318248 145257058961934299499031 := by
  unfold tailWord_318248
  simp only [CollatzResearch.WordTrace]
  refine ⟨5803729075524661638145699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7738305434032882184194265 5803729075524661638145699)
  ·
    refine ⟨8705593613286992457218549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5803729075524661638145699 8705593613286992457218549)
    ·
      refine ⟨816149401245655542864239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8705593613286992457218549 816149401245655542864239)
      ·
        refine ⟨1224224101868483314296359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 816149401245655542864239 1224224101868483314296359)
        ·
          refine ⟨1836336152802724971444539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1224224101868483314296359 1836336152802724971444539)
          ·
            refine ⟨2754504229204087457166809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1836336152802724971444539 2754504229204087457166809)
            ·
              refine ⟨2065878171903065592875107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2754504229204087457166809 2065878171903065592875107)
              ·
                refine ⟨3098817257854598389312661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2065878171903065592875107 3098817257854598389312661)
                ·
                  refine ⟨145257058961934299499031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3098817257854598389312661 145257058961934299499031)
                  ·
                    rfl

theorem cell20_318248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 1, 6].length) (baseStart_318248 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_318248 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_318248 prefixEnd_318248 := by exact prefixLift 318248
  have htrace : WordTrace (prefixWord ++ tailWord_318248) baseStart_318248 baseEnd_318248 := by
    simpa [prefixWord, tailWord_318248, baseEnd_318248] using wordTrace_append hprefix tailTrace_318248
  have hstable : (prefixWord ++ tailWord_318248).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318248).length < 2 ^ (prefixWord ++ tailWord_318248).sum := by decide
  have hdescent : baseEnd_318248 < baseStart_318248 := by decide
  rcases family_descends (prefixWord ++ tailWord_318248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318278 : List Nat := [6, 1, 1, 2, 2, 1, 1, 4, 2]
def baseStart_318278 : Nat := 118140960795 + 318278 * 2 ^ 59
def prefixEnd_318278 : Nat := 4983230072969 + 3 ^ 40 * 318278 * 2
def baseEnd_318278 : Nat := 145270751779387528498909

theorem tailTrace_318278 : CollatzResearch.WordTrace tailWord_318278 prefixEnd_318278 145270751779387528498909 := by
  unfold tailWord_318278
  simp only [CollatzResearch.WordTrace]
  refine ⟨362767260654394949996359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 7739034893960425599922325 362767260654394949996359)
  ·
    refine ⟨544150890981592424994539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 362767260654394949996359 544150890981592424994539)
    ·
      refine ⟨816226336472388637491809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 544150890981592424994539 816226336472388637491809)
      ·
        refine ⟨612169752354291478118857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 816226336472388637491809 612169752354291478118857)
        ·
          refine ⟨459127314265718608589143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 612169752354291478118857 459127314265718608589143)
          ·
            refine ⟨688690971398577912883715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 459127314265718608589143 688690971398577912883715)
            ·
              refine ⟨1033036457097866869325573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 688690971398577912883715 1033036457097866869325573)
              ·
                refine ⟨193694335705850037998545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1033036457097866869325573 193694335705850037998545)
                ·
                  refine ⟨145270751779387528498909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 193694335705850037998545 145270751779387528498909)
                  ·
                    rfl

theorem cell20_318278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 4, 2].length) (baseStart_318278 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_318278 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_318278 prefixEnd_318278 := by exact prefixLift 318278
  have htrace : WordTrace (prefixWord ++ tailWord_318278) baseStart_318278 baseEnd_318278 := by
    simpa [prefixWord, tailWord_318278, baseEnd_318278] using wordTrace_append hprefix tailTrace_318278
  have hstable : (prefixWord ++ tailWord_318278).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318278).length < 2 ^ (prefixWord ++ tailWord_318278).sum := by decide
  have hdescent : baseEnd_318278 < baseStart_318278 := by decide
  rcases family_descends (prefixWord ++ tailWord_318278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318289 : List Nat := [1, 2, 2, 1, 7, 1, 1, 5]
def baseStart_318289 : Nat := 118140960795 + 318289 * 2 ^ 59
def prefixEnd_318289 : Nat := 4983230072969 + 3 ^ 40 * 318289 * 2
def baseEnd_318289 : Nat := 48425257493040126377399

theorem tailTrace_318289 : CollatzResearch.WordTrace tailWord_318289 prefixEnd_318289 48425257493040126377399 := by
  unfold tailWord_318289
  simp only [CollatzResearch.WordTrace]
  refine ⟨11608953543900787278533921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7739302362600524852355947 11608953543900787278533921)
  ·
    refine ⟨8706715157925590458900441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11608953543900787278533921 8706715157925590458900441)
    ·
      refine ⟨6530036368444192844175331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8706715157925590458900441 6530036368444192844175331)
      ·
        refine ⟨9795054552666289266262997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6530036368444192844175331 9795054552666289266262997)
        ·
          refine ⟨229571591078116154678039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 9795054552666289266262997 229571591078116154678039)
          ·
            refine ⟨344357386617174232017059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 229571591078116154678039 344357386617174232017059)
            ·
              refine ⟨516536079925761348025589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 344357386617174232017059 516536079925761348025589)
              ·
                refine ⟨48425257493040126377399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 516536079925761348025589 48425257493040126377399)
                ·
                  rfl

theorem cell20_318289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 1, 5].length) (baseStart_318289 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_318289 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_318289 prefixEnd_318289 := by exact prefixLift 318289
  have htrace : WordTrace (prefixWord ++ tailWord_318289) baseStart_318289 baseEnd_318289 := by
    simpa [prefixWord, tailWord_318289, baseEnd_318289] using wordTrace_append hprefix tailTrace_318289
  have hstable : (prefixWord ++ tailWord_318289).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318289).length < 2 ^ (prefixWord ++ tailWord_318289).sum := by decide
  have hdescent : baseEnd_318289 < baseStart_318289 := by decide
  rcases family_descends (prefixWord ++ tailWord_318289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318341 : List Nat := [1, 3, 1, 1, 3, 3, 2, 4, 2]
def baseStart_318341 : Nat := 118140960795 + 318341 * 2 ^ 59
def prefixEnd_318341 : Nat := 4983230072969 + 3 ^ 40 * 318341 * 2
def baseEnd_318341 : Nat := 145299506696039309398651

theorem tailTrace_318341 : CollatzResearch.WordTrace tailWord_318341 prefixEnd_318341 145299506696039309398651 := by
  unfold tailWord_318341
  simp only [CollatzResearch.WordTrace]
  refine ⟨11610850139712400159426877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7740566759808266772951251 11610850139712400159426877)
  ·
    refine ⟨4354068802392150059785079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11610850139712400159426877 4354068802392150059785079)
    ·
      refine ⟨6531103203588225089677619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4354068802392150059785079 6531103203588225089677619)
      ·
        refine ⟨9796654805382337634516429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6531103203588225089677619 9796654805382337634516429)
        ·
          refine ⟨3673745552018376612943661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9796654805382337634516429 3673745552018376612943661)
          ·
            refine ⟨1377654582006891229853873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3673745552018376612943661 1377654582006891229853873)
            ·
              refine ⟨1033240936505168422390405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1377654582006891229853873 1033240936505168422390405)
              ·
                refine ⟨193732675594719079198201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1033240936505168422390405 193732675594719079198201)
                ·
                  refine ⟨145299506696039309398651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 193732675594719079198201 145299506696039309398651)
                  ·
                    rfl

theorem cell20_318341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 4, 2].length) (baseStart_318341 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_318341 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_318341 prefixEnd_318341 := by exact prefixLift 318341
  have htrace : WordTrace (prefixWord ++ tailWord_318341) baseStart_318341 baseEnd_318341 := by
    simpa [prefixWord, tailWord_318341, baseEnd_318341] using wordTrace_append hprefix tailTrace_318341
  have hstable : (prefixWord ++ tailWord_318341).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318341).length < 2 ^ (prefixWord ++ tailWord_318341).sum := by decide
  have hdescent : baseEnd_318341 < baseStart_318341 := by decide
  rcases family_descends (prefixWord ++ tailWord_318341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318375 : List Nat := [1, 1, 6, 1, 3, 2, 1, 3, 2]
def baseStart_318375 : Nat := 118140960795 + 318375 * 2 ^ 59
def prefixEnd_318375 : Nat := 4983230072969 + 3 ^ 40 * 318375 * 2
def baseEnd_318375 : Nat := 145315025222486302265179

theorem tailTrace_318375 : CollatzResearch.WordTrace tailWord_318375 prefixEnd_318375 145315025222486302265179 := by
  unfold tailWord_318375
  simp only [CollatzResearch.WordTrace]
  refine ⟨11612090221589223966164579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7741393481059482644109719 11612090221589223966164579)
  ·
    refine ⟨17418135332383835949246869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11612090221589223966164579 17418135332383835949246869)
    ·
      refine ⟨816475093705492310120947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 17418135332383835949246869 816475093705492310120947)
      ·
        refine ⟨1224712640558238465181421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 816475093705492310120947 1224712640558238465181421)
        ·
          refine ⟨459267240209339424443033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1224712640558238465181421 459267240209339424443033)
          ·
            refine ⟨344450430157004568332275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 459267240209339424443033 344450430157004568332275)
            ·
              refine ⟨516675645235506852498413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 344450430157004568332275 516675645235506852498413)
              ·
                refine ⟨193753366963315069686905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 516675645235506852498413 193753366963315069686905)
                ·
                  refine ⟨145315025222486302265179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 193753366963315069686905 145315025222486302265179)
                  ·
                    rfl

theorem cell20_318375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 1, 3, 2].length) (baseStart_318375 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_318375 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_318375 prefixEnd_318375 := by exact prefixLift 318375
  have htrace : WordTrace (prefixWord ++ tailWord_318375) baseStart_318375 baseEnd_318375 := by
    simpa [prefixWord, tailWord_318375, baseEnd_318375] using wordTrace_append hprefix tailTrace_318375
  have hstable : (prefixWord ++ tailWord_318375).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318375).length < 2 ^ (prefixWord ++ tailWord_318375).sum := by decide
  have hdescent : baseEnd_318375 < baseStart_318375 := by decide
  rcases family_descends (prefixWord ++ tailWord_318375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318400 : List Nat := [2, 1, 1, 2, 3, 3, 3, 1, 4]
def baseStart_318400 : Nat := 118140960795 + 318400 * 2 ^ 59
def prefixEnd_318400 : Nat := 4983230072969 + 3 ^ 40 * 318400 * 2
def baseEnd_318400 : Nat := 145326435903697326431743

theorem tailTrace_318400 : CollatzResearch.WordTrace tailWord_318400 prefixEnd_318400 145326435903697326431743 := by
  unfold tailWord_318400
  simp only [CollatzResearch.WordTrace]
  refine ⟨5806501023249326617912327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7742001364332435490549769 5806501023249326617912327)
  ·
    refine ⟨8709751534873989926868491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5806501023249326617912327 8709751534873989926868491)
    ·
      refine ⟨13064627302310984890302737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8709751534873989926868491 13064627302310984890302737)
      ·
        refine ⟨9798470476733238667727053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13064627302310984890302737 9798470476733238667727053)
        ·
          refine ⟨3674426428774964500397645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9798470476733238667727053 3674426428774964500397645)
          ·
            refine ⟨1377909910790611687649117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3674426428774964500397645 1377909910790611687649117)
            ·
              refine ⟨516716216546479382868419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1377909910790611687649117 516716216546479382868419)
              ·
                refine ⟨775074324819719074302629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 516716216546479382868419 775074324819719074302629)
                ·
                  refine ⟨145326435903697326431743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 775074324819719074302629 145326435903697326431743)
                  ·
                    rfl

theorem cell20_318400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 3, 1, 4].length) (baseStart_318400 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_318400 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_318400 prefixEnd_318400 := by exact prefixLift 318400
  have htrace : WordTrace (prefixWord ++ tailWord_318400) baseStart_318400 baseEnd_318400 := by
    simpa [prefixWord, tailWord_318400, baseEnd_318400] using wordTrace_append hprefix tailTrace_318400
  have hstable : (prefixWord ++ tailWord_318400).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318400).length < 2 ^ (prefixWord ++ tailWord_318400).sum := by decide
  have hdescent : baseEnd_318400 < baseStart_318400 := by decide
  rcases family_descends (prefixWord ++ tailWord_318400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318459 : List Nat := [1, 1, 1, 1, 1, 3, 3, 5, 4]
def baseStart_318459 : Nat := 118140960795 + 318459 * 2 ^ 59
def prefixEnd_318459 : Nat := 4983230072969 + 3 ^ 40 * 318459 * 2
def baseEnd_318459 : Nat := 145353365111355343464835

theorem tailTrace_318459 : CollatzResearch.WordTrace tailWord_318459 prefixEnd_318459 145353365111355343464835 := by
  unfold tailWord_318459
  simp only [CollatzResearch.WordTrace]
  refine ⟨11615153953284906312222431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7743435968856604208148287 11615153953284906312222431)
  ·
    refine ⟨17422730929927359468333647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11615153953284906312222431 17422730929927359468333647)
    ·
      refine ⟨26134096394891039202500471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17422730929927359468333647 26134096394891039202500471)
      ·
        refine ⟨39201144592336558803750707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26134096394891039202500471 39201144592336558803750707)
        ·
          refine ⟨58801716888504838205626061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39201144592336558803750707 58801716888504838205626061)
          ·
            refine ⟨22050643833189314327109773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58801716888504838205626061 22050643833189314327109773)
            ·
              refine ⟨8268991437445992872666165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22050643833189314327109773 8268991437445992872666165)
              ·
                refine ⟨775217947260561831812453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8268991437445992872666165 775217947260561831812453)
                ·
                  refine ⟨145353365111355343464835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 775217947260561831812453 145353365111355343464835)
                  ·
                    rfl

theorem cell20_318459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 5, 4].length) (baseStart_318459 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_318459 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_318459 prefixEnd_318459 := by exact prefixLift 318459
  have htrace : WordTrace (prefixWord ++ tailWord_318459) baseStart_318459 baseEnd_318459 := by
    simpa [prefixWord, tailWord_318459, baseEnd_318459] using wordTrace_append hprefix tailTrace_318459
  have hstable : (prefixWord ++ tailWord_318459).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318459).length < 2 ^ (prefixWord ++ tailWord_318459).sum := by decide
  have hdescent : baseEnd_318459 < baseStart_318459 := by decide
  rcases family_descends (prefixWord ++ tailWord_318459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318476 : List Nat := [2, 2, 1, 2, 3, 3, 1, 2, 4]
def baseStart_318476 : Nat := 118140960795 + 318476 * 2 ^ 59
def prefixEnd_318476 : Nat := 4983230072969 + 3 ^ 40 * 318476 * 2
def baseEnd_318476 : Nat := 145361124374578839898099

theorem tailTrace_318476 : CollatzResearch.WordTrace tailWord_318476 prefixEnd_318476 145361124374578839898099 := by
  unfold tailWord_318476
  simp only [CollatzResearch.WordTrace]
  refine ⟨5807886997111659107795641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7743849329482212143727521 5807886997111659107795641)
  ·
    refine ⟨4355915247833744330846731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5807886997111659107795641 4355915247833744330846731)
    ·
      refine ⟨6533872871750616496270097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4355915247833744330846731 6533872871750616496270097)
      ·
        refine ⟨4900404653812962372202573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6533872871750616496270097 4900404653812962372202573)
        ·
          refine ⟨1837651745179860889575965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4900404653812962372202573 1837651745179860889575965)
          ·
            refine ⟨689119404442447833590987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1837651745179860889575965 689119404442447833590987)
            ·
              refine ⟨1033679106663671750386481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 689119404442447833590987 1033679106663671750386481)
              ·
                refine ⟨775259329997753812789861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1033679106663671750386481 775259329997753812789861)
                ·
                  refine ⟨145361124374578839898099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 775259329997753812789861 145361124374578839898099)
                  ·
                    rfl

theorem cell20_318476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 2, 4].length) (baseStart_318476 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_318476 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_318476 prefixEnd_318476 := by exact prefixLift 318476
  have htrace : WordTrace (prefixWord ++ tailWord_318476) baseStart_318476 baseEnd_318476 := by
    simpa [prefixWord, tailWord_318476, baseEnd_318476] using wordTrace_append hprefix tailTrace_318476
  have hstable : (prefixWord ++ tailWord_318476).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318476).length < 2 ^ (prefixWord ++ tailWord_318476).sum := by decide
  have hdescent : baseEnd_318476 < baseStart_318476 := by decide
  rcases family_descends (prefixWord ++ tailWord_318476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318490 : List Nat := [3, 1, 1, 3, 1, 2, 2, 2, 5]
def baseStart_318490 : Nat := 118140960795 + 318490 * 2 ^ 59
def prefixEnd_318490 : Nat := 4983230072969 + 3 ^ 40 * 318490 * 2
def baseEnd_318490 : Nat := 145367514356057013431375

theorem tailTrace_318490 : CollatzResearch.WordTrace tailWord_318490 prefixEnd_318490 145367514356057013431375 := by
  unfold tailWord_318490
  simp only [CollatzResearch.WordTrace]
  refine ⟨2904071154043149651650231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7744189744115065737733949 2904071154043149651650231)
  ·
    refine ⟨4356106731064724477475347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2904071154043149651650231 4356106731064724477475347)
    ·
      refine ⟨6534160096597086716213021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4356106731064724477475347 6534160096597086716213021)
      ·
        refine ⟨2450310036223907518579883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6534160096597086716213021 2450310036223907518579883)
        ·
          refine ⟨3675465054335861277869825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2450310036223907518579883 3675465054335861277869825)
          ·
            refine ⟨2756598790751895958402369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3675465054335861277869825 2756598790751895958402369)
            ·
              refine ⟨2067449093063921968801777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2756598790751895958402369 2067449093063921968801777)
              ·
                refine ⟨1550586819797941476601333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2067449093063921968801777 1550586819797941476601333)
                ·
                  refine ⟨145367514356057013431375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1550586819797941476601333 145367514356057013431375)
                  ·
                    rfl

theorem cell20_318490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 2, 5].length) (baseStart_318490 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_318490 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_318490 prefixEnd_318490 := by exact prefixLift 318490
  have htrace : WordTrace (prefixWord ++ tailWord_318490) baseStart_318490 baseEnd_318490 := by
    simpa [prefixWord, tailWord_318490, baseEnd_318490] using wordTrace_append hprefix tailTrace_318490
  have hstable : (prefixWord ++ tailWord_318490).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318490).length < 2 ^ (prefixWord ++ tailWord_318490).sum := by decide
  have hdescent : baseEnd_318490 < baseStart_318490 := by decide
  rcases family_descends (prefixWord ++ tailWord_318490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318503 : List Nat := [1, 1, 7, 1, 1, 3, 1, 2, 3]
def baseStart_318503 : Nat := 118140960795 + 318503 * 2 ^ 59
def prefixEnd_318503 : Nat := 4983230072969 + 3 ^ 40 * 318503 * 2
def baseEnd_318503 : Nat := 145373447910286745997989

theorem tailTrace_318503 : CollatzResearch.WordTrace tailWord_318503 prefixEnd_318503 145373447910286745997989 := by
  unfold tailWord_318503
  simp only [CollatzResearch.WordTrace]
  refine ⟨11616758765125501826824163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7744505843417001217882775 11616758765125501826824163)
  ·
    refine ⟨17425138147688252740236245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11616758765125501826824163 17425138147688252740236245)
    ·
      refine ⟨408401675336443423599287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 17425138147688252740236245 408401675336443423599287)
      ·
        refine ⟨612602513004665135398931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 408401675336443423599287 612602513004665135398931)
        ·
          refine ⟨918903769506997703098397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 612602513004665135398931 918903769506997703098397)
          ·
            refine ⟨344588913565124138661899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 918903769506997703098397 344588913565124138661899)
            ·
              refine ⟨516883370347686207992849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 344588913565124138661899 516883370347686207992849)
              ·
                refine ⟨387662527760764655994637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 516883370347686207992849 387662527760764655994637)
                ·
                  refine ⟨145373447910286745997989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 387662527760764655994637 145373447910286745997989)
                  ·
                    rfl

theorem cell20_318503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 1, 2, 3].length) (baseStart_318503 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_318503 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_318503 prefixEnd_318503 := by exact prefixLift 318503
  have htrace : WordTrace (prefixWord ++ tailWord_318503) baseStart_318503 baseEnd_318503 := by
    simpa [prefixWord, tailWord_318503, baseEnd_318503] using wordTrace_append hprefix tailTrace_318503
  have hstable : (prefixWord ++ tailWord_318503).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318503).length < 2 ^ (prefixWord ++ tailWord_318503).sum := by decide
  have hdescent : baseEnd_318503 < baseStart_318503 := by decide
  rcases family_descends (prefixWord ++ tailWord_318503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318514 : List Nat := [3, 2, 1, 1, 2, 2, 4, 1, 4]
def baseStart_318514 : Nat := 118140960795 + 318514 * 2 ^ 59
def prefixEnd_318514 : Nat := 4983230072969 + 3 ^ 40 * 318514 * 2
def baseEnd_318514 : Nat := 145378468610019596631277

theorem tailTrace_318514 : CollatzResearch.WordTrace tailWord_318514 prefixEnd_318514 145378468610019596631277 := by
  unfold tailWord_318514
  simp only [CollatzResearch.WordTrace]
  refine ⟨2904289992021412676368649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7744773312057100470316397 2904289992021412676368649)
  ·
    refine ⟨2178217494016059507276487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2904289992021412676368649 2178217494016059507276487)
    ·
      refine ⟨3267326241024089260914731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2178217494016059507276487 3267326241024089260914731)
      ·
        refine ⟨4900989361536133891372097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3267326241024089260914731 4900989361536133891372097)
        ·
          refine ⟨3675742021152100418529073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4900989361536133891372097 3675742021152100418529073)
          ·
            refine ⟨2756806515864075313896805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3675742021152100418529073 2756806515864075313896805)
            ·
              refine ⟨516901221724514121355651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2756806515864075313896805 516901221724514121355651)
              ·
                refine ⟨775351832586771182033477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 516901221724514121355651 775351832586771182033477)
                ·
                  refine ⟨145378468610019596631277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 775351832586771182033477 145378468610019596631277)
                  ·
                    rfl

theorem cell20_318514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 4, 1, 4].length) (baseStart_318514 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_318514 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_318514 prefixEnd_318514 := by exact prefixLift 318514
  have htrace : WordTrace (prefixWord ++ tailWord_318514) baseStart_318514 baseEnd_318514 := by
    simpa [prefixWord, tailWord_318514, baseEnd_318514] using wordTrace_append hprefix tailTrace_318514
  have hstable : (prefixWord ++ tailWord_318514).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318514).length < 2 ^ (prefixWord ++ tailWord_318514).sum := by decide
  have hdescent : baseEnd_318514 < baseStart_318514 := by decide
  rcases family_descends (prefixWord ++ tailWord_318514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318524 : List Nat := [2, 2, 2, 2, 2, 3, 3, 1, 3]
def baseStart_318524 : Nat := 118140960795 + 318524 * 2 ^ 59
def prefixEnd_318524 : Nat := 4983230072969 + 3 ^ 40 * 318524 * 2
def baseEnd_318524 : Nat := 145383032882504006297903

theorem tailTrace_318524 : CollatzResearch.WordTrace tailWord_318524 prefixEnd_318524 145383032882504006297903 := by
  unfold tailWord_318524
  simp only [CollatzResearch.WordTrace]
  refine ⟨5808762349024711206669313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7745016465366281608892417 5808762349024711206669313)
  ·
    refine ⟨4356571761768533405001985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5808762349024711206669313 4356571761768533405001985)
    ·
      refine ⟨3267428821326400053751489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4356571761768533405001985 3267428821326400053751489)
      ·
        refine ⟨2450571615994800040313617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3267428821326400053751489 2450571615994800040313617)
        ·
          refine ⟨1837928711996100030235213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2450571615994800040313617 1837928711996100030235213)
          ·
            refine ⟨689223266998537511338205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1837928711996100030235213 689223266998537511338205)
            ·
              refine ⟨258458725124451566751827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 689223266998537511338205 258458725124451566751827)
              ·
                refine ⟨387688087686677350127741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 258458725124451566751827 387688087686677350127741)
                ·
                  refine ⟨145383032882504006297903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 387688087686677350127741 145383032882504006297903)
                  ·
                    rfl

theorem cell20_318524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 3, 1, 3].length) (baseStart_318524 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_318524 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_318524 prefixEnd_318524 := by exact prefixLift 318524
  have htrace : WordTrace (prefixWord ++ tailWord_318524) baseStart_318524 baseEnd_318524 := by
    simpa [prefixWord, tailWord_318524, baseEnd_318524] using wordTrace_append hprefix tailTrace_318524
  have hstable : (prefixWord ++ tailWord_318524).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318524).length < 2 ^ (prefixWord ++ tailWord_318524).sum := by decide
  have hdescent : baseEnd_318524 < baseStart_318524 := by decide
  rcases family_descends (prefixWord ++ tailWord_318524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318534 : List Nat := [6, 1, 1, 1, 1, 4, 2, 4]
def baseStart_318534 : Nat := 118140960795 + 318534 * 2 ^ 59
def prefixEnd_318534 : Nat := 4983230072969 + 3 ^ 40 * 318534 * 2
def baseEnd_318534 : Nat := 48462532384996138654843

theorem tailTrace_318534 : CollatzResearch.WordTrace tailWord_318534 prefixEnd_318534 48462532384996138654843 := by
  unfold tailWord_318534
  simp only [CollatzResearch.WordTrace]
  refine ⟨363059044625412316287583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 7745259618675462747468437 363059044625412316287583)
  ·
    refine ⟨544588566938118474431375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 363059044625412316287583 544588566938118474431375)
    ·
      refine ⟨816882850407177711647063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 544588566938118474431375 816882850407177711647063)
      ·
        refine ⟨1225324275610766567470595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 816882850407177711647063 1225324275610766567470595)
        ·
          refine ⟨1837986413416149851205893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1225324275610766567470595 1837986413416149851205893)
          ·
            refine ⟨344622452515528097101105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1837986413416149851205893 344622452515528097101105)
            ·
              refine ⟨258466839386646072825829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 344622452515528097101105 258466839386646072825829)
              ·
                refine ⟨48462532384996138654843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 258466839386646072825829 48462532384996138654843)
                ·
                  rfl

theorem cell20_318534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_318534 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_318534 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_318534 prefixEnd_318534 := by exact prefixLift 318534
  have htrace : WordTrace (prefixWord ++ tailWord_318534) baseStart_318534 baseEnd_318534 := by
    simpa [prefixWord, tailWord_318534, baseEnd_318534] using wordTrace_append hprefix tailTrace_318534
  have hstable : (prefixWord ++ tailWord_318534).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318534).length < 2 ^ (prefixWord ++ tailWord_318534).sum := by decide
  have hdescent : baseEnd_318534 < baseStart_318534 := by decide
  rcases family_descends (prefixWord ++ tailWord_318534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318621 : List Nat := [1, 4, 2, 1, 1, 2, 4, 2, 3]
def baseStart_318621 : Nat := 118140960795 + 318621 * 2 ^ 59
def prefixEnd_318621 : Nat := 4983230072969 + 3 ^ 40 * 318621 * 2
def baseEnd_318621 : Nat := 145427306325602780064173

theorem tailTrace_318621 : CollatzResearch.WordTrace tailWord_318621 prefixEnd_318621 145427306325602780064173 := by
  unfold tailWord_318621
  simp only [CollatzResearch.WordTrace]
  refine ⟨11621062578698007979619717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7747375052465338653079811 11621062578698007979619717)
  ·
    refine ⟨2178949233505876496178697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11621062578698007979619717 2178949233505876496178697)
    ·
      refine ⟨1634211925129407372134023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2178949233505876496178697 1634211925129407372134023)
      ·
        refine ⟨2451317887694111058201035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1634211925129407372134023 2451317887694111058201035)
        ·
          refine ⟨3676976831541166587301553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2451317887694111058201035 3676976831541166587301553)
          ·
            refine ⟨2757732623655874940476165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3676976831541166587301553 2757732623655874940476165)
            ·
              refine ⟨517074866935476551339281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2757732623655874940476165 517074866935476551339281)
              ·
                refine ⟨387806150201607413504461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 517074866935476551339281 387806150201607413504461)
                ·
                  refine ⟨145427306325602780064173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 387806150201607413504461 145427306325602780064173)
                  ·
                    rfl

theorem cell20_318621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 4, 2, 3].length) (baseStart_318621 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_318621 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_318621 prefixEnd_318621 := by exact prefixLift 318621
  have htrace : WordTrace (prefixWord ++ tailWord_318621) baseStart_318621 baseEnd_318621 := by
    simpa [prefixWord, tailWord_318621, baseEnd_318621] using wordTrace_append hprefix tailTrace_318621
  have hstable : (prefixWord ++ tailWord_318621).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318621).length < 2 ^ (prefixWord ++ tailWord_318621).sum := by decide
  have hdescent : baseEnd_318621 < baseStart_318621 := by decide
  rcases family_descends (prefixWord ++ tailWord_318621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318649 : List Nat := [1, 2, 1, 4, 1, 3, 1, 1, 6]
def baseStart_318649 : Nat := 118140960795 + 318649 * 2 ^ 59
def prefixEnd_318649 : Nat := 4983230072969 + 3 ^ 40 * 318649 * 2
def baseEnd_318649 : Nat := 145440086288559127130725

theorem tailTrace_318649 : CollatzResearch.WordTrace tailWord_318649 prefixEnd_318649 145440086288559127130725 := by
  unfold tailWord_318649
  simp only [CollatzResearch.WordTrace]
  refine ⟨11622083822596568761639001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7748055881731045841092667 11622083822596568761639001)
  ·
    refine ⟨8716562866947426571229251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11622083822596568761639001 8716562866947426571229251)
    ·
      refine ⟨13074844300421139856843877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8716562866947426571229251 13074844300421139856843877)
      ·
        refine ⟨2451533306328963723158227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13074844300421139856843877 2451533306328963723158227)
        ·
          refine ⟨3677299959493445584737341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2451533306328963723158227 3677299959493445584737341)
          ·
            refine ⟨1378987484810042094276503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3677299959493445584737341 1378987484810042094276503)
            ·
              refine ⟨2068481227215063141414755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1378987484810042094276503 2068481227215063141414755)
              ·
                refine ⟨3102721840822594712122133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2068481227215063141414755 3102721840822594712122133)
                ·
                  refine ⟨145440086288559127130725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3102721840822594712122133 145440086288559127130725)
                  ·
                    rfl

theorem cell20_318649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 1, 6].length) (baseStart_318649 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_318649 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_318649 prefixEnd_318649 := by exact prefixLift 318649
  have htrace : WordTrace (prefixWord ++ tailWord_318649) baseStart_318649 baseEnd_318649 := by
    simpa [prefixWord, tailWord_318649, baseEnd_318649] using wordTrace_append hprefix tailTrace_318649
  have hstable : (prefixWord ++ tailWord_318649).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318649).length < 2 ^ (prefixWord ++ tailWord_318649).sum := by decide
  have hdescent : baseEnd_318649 < baseStart_318649 := by decide
  rcases family_descends (prefixWord ++ tailWord_318649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318652 : List Nat := [2, 2, 2, 3, 2, 2, 3, 4]
def baseStart_318652 : Nat := 118140960795 + 318652 * 2 ^ 59
def prefixEnd_318652 : Nat := 4983230072969 + 3 ^ 40 * 318652 * 2
def baseEnd_318652 : Nat := 48480485190101483343571

theorem tailTrace_318652 : CollatzResearch.WordTrace tailWord_318652 prefixEnd_318652 48480485190101483343571 := by
  unfold tailWord_318652
  simp only [CollatzResearch.WordTrace]
  refine ⟨5811096620792850136999105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7748128827723800182665473 5811096620792850136999105)
  ·
    refine ⟨4358322465594637602749329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5811096620792850136999105 4358322465594637602749329)
    ·
      refine ⟨3268741849195978202061997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4358322465594637602749329 3268741849195978202061997)
      ·
        refine ⟨1225778193448491825773249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3268741849195978202061997 1225778193448491825773249)
        ·
          refine ⟨919333645086368869329937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1225778193448491825773249 919333645086368869329937)
          ·
            refine ⟨689500233814776651997453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 919333645086368869329937 689500233814776651997453)
            ·
              refine ⟨258562587680541244499045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 689500233814776651997453 258562587680541244499045)
              ·
                refine ⟨48480485190101483343571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 258562587680541244499045 48480485190101483343571)
                ·
                  rfl

theorem cell20_318652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 3, 4].length) (baseStart_318652 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_318652 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_318652 prefixEnd_318652 := by exact prefixLift 318652
  have htrace : WordTrace (prefixWord ++ tailWord_318652) baseStart_318652 baseEnd_318652 := by
    simpa [prefixWord, tailWord_318652, baseEnd_318652] using wordTrace_append hprefix tailTrace_318652
  have hstable : (prefixWord ++ tailWord_318652).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318652).length < 2 ^ (prefixWord ++ tailWord_318652).sum := by decide
  have hdescent : baseEnd_318652 < baseStart_318652 := by decide
  rcases family_descends (prefixWord ++ tailWord_318652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318658 : List Nat := [3, 5, 1, 1, 2, 1, 2, 3, 2]
def baseStart_318658 : Nat := 118140960795 + 318658 * 2 ^ 59
def prefixEnd_318658 : Nat := 4983230072969 + 3 ^ 40 * 318658 * 2
def baseEnd_318658 : Nat := 145444194133795095830689

theorem tailTrace_318658 : CollatzResearch.WordTrace tailWord_318658 prefixEnd_318658 145444194133795095830689 := by
  unfold tailWord_318658
  simp only [CollatzResearch.WordTrace]
  refine ⟨2905603019890990824679157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7748274719709308865811085 2905603019890990824679157)
  ·
    refine ⟨272400283114780389813671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2905603019890990824679157 272400283114780389813671)
    ·
      refine ⟨408600424672170584720507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272400283114780389813671 408600424672170584720507)
      ·
        refine ⟨612900637008255877080761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 408600424672170584720507 612900637008255877080761)
        ·
          refine ⟨459675477756191907810571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 612900637008255877080761 459675477756191907810571)
          ·
            refine ⟨689513216634287861715857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 459675477756191907810571 689513216634287861715857)
            ·
              refine ⟨517134912475715896286893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 689513216634287861715857 517134912475715896286893)
              ·
                refine ⟨193925592178393461107585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 517134912475715896286893 193925592178393461107585)
                ·
                  refine ⟨145444194133795095830689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 193925592178393461107585 145444194133795095830689)
                  ·
                    rfl

theorem cell20_318658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_318658 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_318658 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_318658 prefixEnd_318658 := by exact prefixLift 318658
  have htrace : WordTrace (prefixWord ++ tailWord_318658) baseStart_318658 baseEnd_318658 := by
    simpa [prefixWord, tailWord_318658, baseEnd_318658] using wordTrace_append hprefix tailTrace_318658
  have hstable : (prefixWord ++ tailWord_318658).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318658).length < 2 ^ (prefixWord ++ tailWord_318658).sum := by decide
  have hdescent : baseEnd_318658 < baseStart_318658 := by decide
  rcases family_descends (prefixWord ++ tailWord_318658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318669 : List Nat := [1, 6, 2, 2, 1, 1, 7]
def baseStart_318669 : Nat := 118140960795 + 318669 * 2 ^ 59
def prefixEnd_318669 : Nat := 4983230072969 + 3 ^ 40 * 318669 * 2
def baseEnd_318669 : Nat := 16161023870391994051553

theorem tailTrace_318669 : CollatzResearch.WordTrace tailWord_318669 prefixEnd_318669 16161023870391994051553 := by
  unfold tailWord_318669
  simp only [CollatzResearch.WordTrace]
  refine ⟨11622813282524112177367061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7748542188349408118244707 11622813282524112177367061)
  ·
    refine ⟨544819372618317758314081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 11622813282524112177367061 544819372618317758314081)
    ·
      refine ⟨408614529463738318735561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 544819372618317758314081 408614529463738318735561)
      ·
        refine ⟨306460897097803739051671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 408614529463738318735561 306460897097803739051671)
        ·
          refine ⟨459691345646705608577507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 306460897097803739051671 459691345646705608577507)
          ·
            refine ⟨689537018470058412866261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 459691345646705608577507 689537018470058412866261)
            ·
              refine ⟨16161023870391994051553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 689537018470058412866261 16161023870391994051553)
              ·
                rfl

theorem cell20_318669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 7].length) (baseStart_318669 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_318669 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_318669 prefixEnd_318669 := by exact prefixLift 318669
  have htrace : WordTrace (prefixWord ++ tailWord_318669) baseStart_318669 baseEnd_318669 := by
    simpa [prefixWord, tailWord_318669, baseEnd_318669] using wordTrace_append hprefix tailTrace_318669
  have hstable : (prefixWord ++ tailWord_318669).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318669).length < 2 ^ (prefixWord ++ tailWord_318669).sum := by decide
  have hdescent : baseEnd_318669 < baseStart_318669 := by decide
  rcases family_descends (prefixWord ++ tailWord_318669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318676 : List Nat := [2, 4, 1, 4, 1, 1, 1, 1, 5]
def baseStart_318676 : Nat := 118140960795 + 318676 * 2 ^ 59
def prefixEnd_318676 : Nat := 4983230072969 + 3 ^ 40 * 318676 * 2
def baseEnd_318676 : Nat := 145452409824267033230615

theorem tailTrace_318676 : CollatzResearch.WordTrace tailWord_318676 prefixEnd_318676 145452409824267033230615 := by
  unfold tailWord_318676
  simp only [CollatzResearch.WordTrace]
  refine ⟨5811534296749376186435941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7748712395665834915247921 5811534296749376186435941)
  ·
    refine ⟨1089662680640508034956739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5811534296749376186435941 1089662680640508034956739)
    ·
      refine ⟨1634494020960762052435109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1089662680640508034956739 1634494020960762052435109)
      ·
        refine ⟨306467628930142884831583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1634494020960762052435109 306467628930142884831583)
        ·
          refine ⟨459701443395214327247375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 306467628930142884831583 459701443395214327247375)
          ·
            refine ⟨689552165092821490871063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 459701443395214327247375 689552165092821490871063)
            ·
              refine ⟨1034328247639232236306595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 689552165092821490871063 1034328247639232236306595)
              ·
                refine ⟨1551492371458848354459893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1034328247639232236306595 1551492371458848354459893)
                ·
                  refine ⟨145452409824267033230615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1551492371458848354459893 145452409824267033230615)
                  ·
                    rfl

theorem cell20_318676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 1, 5].length) (baseStart_318676 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_318676 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_318676 prefixEnd_318676 := by exact prefixLift 318676
  have htrace : WordTrace (prefixWord ++ tailWord_318676) baseStart_318676 baseEnd_318676 := by
    simpa [prefixWord, tailWord_318676, baseEnd_318676] using wordTrace_append hprefix tailTrace_318676
  have hstable : (prefixWord ++ tailWord_318676).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318676).length < 2 ^ (prefixWord ++ tailWord_318676).sum := by decide
  have hdescent : baseEnd_318676 < baseStart_318676 := by decide
  rcases family_descends (prefixWord ++ tailWord_318676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318687 : List Nat := [1, 1, 2, 3, 2, 1, 3, 3, 4]
def baseStart_318687 : Nat := 118140960795 + 318687 * 2 ^ 59
def prefixEnd_318687 : Nat := 4983230072969 + 3 ^ 40 * 318687 * 2
def baseEnd_318687 : Nat := 145457430523999883863903

theorem tailTrace_318687 : CollatzResearch.WordTrace tailWord_318687 prefixEnd_318687 145457430523999883863903 := by
  unfold tailWord_318687
  simp only [CollatzResearch.WordTrace]
  refine ⟨11623469796458901251522315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7748979864305934167681543 11623469796458901251522315)
  ·
    refine ⟨17435204694688351877283473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11623469796458901251522315 17435204694688351877283473)
    ·
      refine ⟨13076403521016263907962605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17435204694688351877283473 13076403521016263907962605)
      ·
        refine ⟨4903651320381098965485977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13076403521016263907962605 4903651320381098965485977)
        ·
          refine ⟨3677738490285824224114483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4903651320381098965485977 3677738490285824224114483)
          ·
            refine ⟨5516607735428736336171725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3677738490285824224114483 5516607735428736336171725)
            ·
              refine ⟨2068727900785776126064397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5516607735428736336171725 2068727900785776126064397)
              ·
                refine ⟨775772962794666047274149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2068727900785776126064397 775772962794666047274149)
                ·
                  refine ⟨145457430523999883863903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 775772962794666047274149 145457430523999883863903)
                  ·
                    rfl

theorem cell20_318687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 3, 4].length) (baseStart_318687 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_318687 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_318687 prefixEnd_318687 := by exact prefixLift 318687
  have htrace : WordTrace (prefixWord ++ tailWord_318687) baseStart_318687 baseEnd_318687 := by
    simpa [prefixWord, tailWord_318687, baseEnd_318687] using wordTrace_append hprefix tailTrace_318687
  have hstable : (prefixWord ++ tailWord_318687).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318687).length < 2 ^ (prefixWord ++ tailWord_318687).sum := by decide
  have hdescent : baseEnd_318687 < baseStart_318687 := by decide
  rcases family_descends (prefixWord ++ tailWord_318687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318721 : List Nat := [1, 2, 4, 1, 1, 3, 3, 3, 2]
def baseStart_318721 : Nat := 118140960795 + 318721 * 2 ^ 59
def prefixEnd_318721 : Nat := 4983230072969 + 3 ^ 40 * 318721 * 2
def baseEnd_318721 : Nat := 145472949050446876730431

theorem tailTrace_318721 : CollatzResearch.WordTrace tailWord_318721 prefixEnd_318721 145472949050446876730431 := by
  unfold tailWord_318721
  simp only [CollatzResearch.WordTrace]
  refine ⟨11624709878335725058260017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7749806585557150038840011 11624709878335725058260017)
  ·
    refine ⟨8718532408751793793695013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11624709878335725058260017 8718532408751793793695013)
    ·
      refine ⟨1634724826640961336317815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8718532408751793793695013 1634724826640961336317815)
      ·
        refine ⟨2452087239961442004476723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1634724826640961336317815 2452087239961442004476723)
        ·
          refine ⟨3678130859942163006715085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2452087239961442004476723 3678130859942163006715085)
          ·
            refine ⟨1379299072478311127518157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3678130859942163006715085 1379299072478311127518157)
            ·
              refine ⟨517237152179366672819309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1379299072478311127518157 517237152179366672819309)
              ·
                refine ⟨193963932067262502307241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 517237152179366672819309 193963932067262502307241)
                ·
                  refine ⟨145472949050446876730431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 193963932067262502307241 145472949050446876730431)
                  ·
                    rfl

theorem cell20_318721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3, 3, 2].length) (baseStart_318721 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_318721 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_318721 prefixEnd_318721 := by exact prefixLift 318721
  have htrace : WordTrace (prefixWord ++ tailWord_318721) baseStart_318721 baseEnd_318721 := by
    simpa [prefixWord, tailWord_318721, baseEnd_318721] using wordTrace_append hprefix tailTrace_318721
  have hstable : (prefixWord ++ tailWord_318721).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318721).length < 2 ^ (prefixWord ++ tailWord_318721).sum := by decide
  have hdescent : baseEnd_318721 < baseStart_318721 := by decide
  rcases family_descends (prefixWord ++ tailWord_318721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318728 : List Nat := [2, 1, 3, 2, 5, 1, 6]
def baseStart_318728 : Nat := 118140960795 + 318728 * 2 ^ 59
def prefixEnd_318728 : Nat := 4983230072969 + 3 ^ 40 * 318728 * 2
def baseEnd_318728 : Nat := 16164016004576218166341

theorem tailTrace_318728 : CollatzResearch.WordTrace tailWord_318728 prefixEnd_318728 16164016004576218166341 := by
  unfold tailWord_318728
  simp only [CollatzResearch.WordTrace]
  refine ⟨5812482594655182626882419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7749976792873576835843225 5812482594655182626882419)
  ·
    refine ⟨8718723891982773940323629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5812482594655182626882419 8718723891982773940323629)
    ·
      refine ⟨3269521459493540227621361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8718723891982773940323629 3269521459493540227621361)
      ·
        refine ⟨2452141094620155170716021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3269521459493540227621361 2452141094620155170716021)
        ·
          refine ⟨229888227620639547254627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2452141094620155170716021 229888227620639547254627)
          ·
            refine ⟨344832341430959320881941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 229888227620639547254627 344832341430959320881941)
            ·
              refine ⟨16164016004576218166341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 344832341430959320881941 16164016004576218166341)
              ·
                rfl

theorem cell20_318728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 6].length) (baseStart_318728 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_318728 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_318728 prefixEnd_318728 := by exact prefixLift 318728
  have htrace : WordTrace (prefixWord ++ tailWord_318728) baseStart_318728 baseEnd_318728 := by
    simpa [prefixWord, tailWord_318728, baseEnd_318728] using wordTrace_append hprefix tailTrace_318728
  have hstable : (prefixWord ++ tailWord_318728).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318728).length < 2 ^ (prefixWord ++ tailWord_318728).sum := by decide
  have hdescent : baseEnd_318728 < baseStart_318728 := by decide
  rcases family_descends (prefixWord ++ tailWord_318728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318732 : List Nat := [2, 2, 1, 2, 2, 3, 8]
def baseStart_318732 : Nat := 118140960795 + 318732 * 2 ^ 59
def prefixEnd_318732 : Nat := 4983230072969 + 3 ^ 40 * 318732 * 2
def baseEnd_318732 : Nat := 16164218861131080818191

theorem tailTrace_318732 : CollatzResearch.WordTrace tailWord_318732 prefixEnd_318732 16164218861131080818191 := by
  unfold tailWord_318732
  simp only [CollatzResearch.WordTrace]
  refine ⟨5812555540647936968455225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7750074054197249291273633 5812555540647936968455225)
  ·
    refine ⟨4359416655485952726341419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5812555540647936968455225 4359416655485952726341419)
    ·
      refine ⟨6539124983228929089512129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4359416655485952726341419 6539124983228929089512129)
      ·
        refine ⟨4904343737421696817134097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6539124983228929089512129 4904343737421696817134097)
        ·
          refine ⟨3678257803066272612850573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4904343737421696817134097 3678257803066272612850573)
          ·
            refine ⟨1379346676149852229818965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3678257803066272612850573 1379346676149852229818965)
            ·
              refine ⟨16164218861131080818191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1379346676149852229818965 16164218861131080818191)
              ·
                rfl

theorem cell20_318732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 8].length) (baseStart_318732 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_318732 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_318732 prefixEnd_318732 := by exact prefixLift 318732
  have htrace : WordTrace (prefixWord ++ tailWord_318732) baseStart_318732 baseEnd_318732 := by
    simpa [prefixWord, tailWord_318732, baseEnd_318732] using wordTrace_append hprefix tailTrace_318732
  have hstable : (prefixWord ++ tailWord_318732).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318732).length < 2 ^ (prefixWord ++ tailWord_318732).sum := by decide
  have hdescent : baseEnd_318732 < baseStart_318732 := by decide
  rcases family_descends (prefixWord ++ tailWord_318732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318749 : List Nat := [1, 4, 2, 3, 1, 1, 1, 7]
def baseStart_318749 : Nat := 118140960795 + 318749 * 2 ^ 59
def prefixEnd_318749 : Nat := 4983230072969 + 3 ^ 40 * 318749 * 2
def baseEnd_318749 : Nat := 48495243004467741265661

theorem tailTrace_318749 : CollatzResearch.WordTrace tailWord_318749 prefixEnd_318749 48495243004467741265661 := by
  unfold tailWord_318749
  simp only [CollatzResearch.WordTrace]
  refine ⟨11625731122234285840279301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7750487414822857226852867 11625731122234285840279301)
  ·
    refine ⟨2179824585418928595052369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11625731122234285840279301 2179824585418928595052369)
    ·
      refine ⟨1634868439064196446289277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2179824585418928595052369 1634868439064196446289277)
      ·
        refine ⟨613075664649073667358479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1634868439064196446289277 613075664649073667358479)
        ·
          refine ⟨919613496973610501037719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 613075664649073667358479 919613496973610501037719)
          ·
            refine ⟨1379420245460415751556579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 919613496973610501037719 1379420245460415751556579)
            ·
              refine ⟨2069130368190623627334869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1379420245460415751556579 2069130368190623627334869)
              ·
                refine ⟨48495243004467741265661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2069130368190623627334869 48495243004467741265661)
                ·
                  rfl

theorem cell20_318749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 7].length) (baseStart_318749 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_318749 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_318749 prefixEnd_318749 := by exact prefixLift 318749
  have htrace : WordTrace (prefixWord ++ tailWord_318749) baseStart_318749 baseEnd_318749 := by
    simpa [prefixWord, tailWord_318749, baseEnd_318749] using wordTrace_append hprefix tailTrace_318749
  have hstable : (prefixWord ++ tailWord_318749).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318749).length < 2 ^ (prefixWord ++ tailWord_318749).sum := by decide
  have hdescent : baseEnd_318749 < baseStart_318749 := by decide
  rcases family_descends (prefixWord ++ tailWord_318749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318801 : List Nat := [1, 2, 2, 1, 4, 1, 2, 3, 4]
def baseStart_318801 : Nat := 118140960795 + 318801 * 2 ^ 59
def prefixEnd_318801 : Nat := 4983230072969 + 3 ^ 40 * 318801 * 2
def baseEnd_318801 : Nat := 145509463230322154063437

theorem tailTrace_318801 : CollatzResearch.WordTrace tailWord_318801 prefixEnd_318801 145509463230322154063437 := by
  unfold tailWord_318801
  simp only [CollatzResearch.WordTrace]
  refine ⟨11627627718045898721172257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7751751812030599147448171 11627627718045898721172257)
  ·
    refine ⟨8720720788534424040879193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11627627718045898721172257 8720720788534424040879193)
    ·
      refine ⟨6540540591400818030659395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8720720788534424040879193 6540540591400818030659395)
      ·
        refine ⟨9810810887101227045989093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6540540591400818030659395 9810810887101227045989093)
        ·
          refine ⟨1839527041331480071122955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9810810887101227045989093 1839527041331480071122955)
          ·
            refine ⟨2759290561997220106684433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1839527041331480071122955 2759290561997220106684433)
            ·
              refine ⟨2069467921497915080013325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2759290561997220106684433 2069467921497915080013325)
              ·
                refine ⟨776050470561718155004997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2069467921497915080013325 776050470561718155004997)
                ·
                  refine ⟨145509463230322154063437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 776050470561718155004997 145509463230322154063437)
                  ·
                    rfl

theorem cell20_318801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 3, 4].length) (baseStart_318801 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_318801 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_318801 prefixEnd_318801 := by exact prefixLift 318801
  have htrace : WordTrace (prefixWord ++ tailWord_318801) baseStart_318801 baseEnd_318801 := by
    simpa [prefixWord, tailWord_318801, baseEnd_318801] using wordTrace_append hprefix tailTrace_318801
  have hstable : (prefixWord ++ tailWord_318801).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318801).length < 2 ^ (prefixWord ++ tailWord_318801).sum := by decide
  have hdescent : baseEnd_318801 < baseStart_318801 := by decide
  rcases family_descends (prefixWord ++ tailWord_318801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318815 : List Nat := [1, 1, 2, 3, 1, 2, 1, 2, 7]
def baseStart_318815 : Nat := 118140960795 + 318815 * 2 ^ 59
def prefixEnd_318815 : Nat := 4983230072969 + 3 ^ 40 * 318815 * 2
def baseEnd_318815 : Nat := 145515853211800327596713

theorem tailTrace_318815 : CollatzResearch.WordTrace tailWord_318815 prefixEnd_318815 145515853211800327596713 := by
  unfold tailWord_318815
  simp only [CollatzResearch.WordTrace]
  refine ⟨11628138339995179112181899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7752092226663452741454599 11628138339995179112181899)
  ·
    refine ⟨17442207509992768668272849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11628138339995179112181899 17442207509992768668272849)
    ·
      refine ⟨13081655632494576501204637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17442207509992768668272849 13081655632494576501204637)
      ·
        refine ⟨4905620862185466187951739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13081655632494576501204637 4905620862185466187951739)
        ·
          refine ⟨7358431293278199281927609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4905620862185466187951739 7358431293278199281927609)
          ·
            refine ⟨5518823469958649461445707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7358431293278199281927609 5518823469958649461445707)
            ·
              refine ⟨8278235204937974192168561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5518823469958649461445707 8278235204937974192168561)
              ·
                refine ⟨6208676403703480644126421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8278235204937974192168561 6208676403703480644126421)
                ·
                  refine ⟨145515853211800327596713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6208676403703480644126421 145515853211800327596713)
                  ·
                    rfl

theorem cell20_318815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 7].length) (baseStart_318815 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_318815 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_318815 prefixEnd_318815 := by exact prefixLift 318815
  have htrace : WordTrace (prefixWord ++ tailWord_318815) baseStart_318815 baseEnd_318815 := by
    simpa [prefixWord, tailWord_318815, baseEnd_318815] using wordTrace_append hprefix tailTrace_318815
  have hstable : (prefixWord ++ tailWord_318815).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318815).length < 2 ^ (prefixWord ++ tailWord_318815).sum := by decide
  have hdescent : baseEnd_318815 < baseStart_318815 := by decide
  rcases family_descends (prefixWord ++ tailWord_318815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318818 : List Nat := [3, 3, 2, 1, 1, 1, 3, 2, 4]
def baseStart_318818 : Nat := 118140960795 + 318818 * 2 ^ 59
def prefixEnd_318818 : Nat := 4983230072969 + 3 ^ 40 * 318818 * 2
def baseEnd_318818 : Nat := 145517222493545650496701

theorem tailTrace_318818 : CollatzResearch.WordTrace tailWord_318818 prefixEnd_318818 145517222493545650496701 := by
  unfold tailWord_318818
  simp only [CollatzResearch.WordTrace]
  refine ⟨2907061939746077656135277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7752165172656207083027405 2907061939746077656135277)
  ·
    refine ⟨1090148227404779121050729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2907061939746077656135277 1090148227404779121050729)
    ·
      refine ⟨817611170553584340788047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1090148227404779121050729 817611170553584340788047)
      ·
        refine ⟨1226416755830376511182071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 817611170553584340788047 1226416755830376511182071)
        ·
          refine ⟨1839625133745564766773107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1226416755830376511182071 1839625133745564766773107)
          ·
            refine ⟨2759437700618347150159661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1839625133745564766773107 2759437700618347150159661)
            ·
              refine ⟨1034789137731880181309873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2759437700618347150159661 1034789137731880181309873)
              ·
                refine ⟨776091853298910135982405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1034789137731880181309873 776091853298910135982405)
                ·
                  refine ⟨145517222493545650496701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 776091853298910135982405 145517222493545650496701)
                  ·
                    rfl

theorem cell20_318818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_318818 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_318818 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_318818 prefixEnd_318818 := by exact prefixLift 318818
  have htrace : WordTrace (prefixWord ++ tailWord_318818) baseStart_318818 baseEnd_318818 := by
    simpa [prefixWord, tailWord_318818, baseEnd_318818] using wordTrace_append hprefix tailTrace_318818
  have hstable : (prefixWord ++ tailWord_318818).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318818).length < 2 ^ (prefixWord ++ tailWord_318818).sum := by decide
  have hdescent : baseEnd_318818 < baseStart_318818 := by decide
  rcases family_descends (prefixWord ++ tailWord_318818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318849 : List Nat := [1, 2, 4, 3, 2, 1, 1, 1, 5]
def baseStart_318849 : Nat := 118140960795 + 318849 * 2 ^ 59
def prefixEnd_318849 : Nat := 4983230072969 + 3 ^ 40 * 318849 * 2
def baseEnd_318849 : Nat := 145531371738247320463241

theorem tailTrace_318849 : CollatzResearch.WordTrace tailWord_318849 prefixEnd_318849 145531371738247320463241 := by
  unfold tailWord_318849
  simp only [CollatzResearch.WordTrace]
  refine ⟨11629378421872002918919601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7752918947914668612613067 11629378421872002918919601)
  ·
    refine ⟨8722033816404002189189701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11629378421872002918919601 8722033816404002189189701)
    ·
      refine ⟨1635381340575750410473069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8722033816404002189189701 1635381340575750410473069)
      ·
        refine ⟨613268002715906403927401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1635381340575750410473069 613268002715906403927401)
        ·
          refine ⟨459951002036929802945551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 613268002715906403927401 459951002036929802945551)
          ·
            refine ⟨689926503055394704418327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 459951002036929802945551 689926503055394704418327)
            ·
              refine ⟨1034889754583092056627491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 689926503055394704418327 1034889754583092056627491)
              ·
                refine ⟨1552334631874638084941237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1034889754583092056627491 1552334631874638084941237)
                ·
                  refine ⟨145531371738247320463241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1552334631874638084941237 145531371738247320463241)
                  ·
                    rfl

theorem cell20_318849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 1, 5].length) (baseStart_318849 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_318849 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_318849 prefixEnd_318849 := by exact prefixLift 318849
  have htrace : WordTrace (prefixWord ++ tailWord_318849) baseStart_318849 baseEnd_318849 := by
    simpa [prefixWord, tailWord_318849, baseEnd_318849] using wordTrace_append hprefix tailTrace_318849
  have hstable : (prefixWord ++ tailWord_318849).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318849).length < 2 ^ (prefixWord ++ tailWord_318849).sum := by decide
  have hdescent : baseEnd_318849 < baseStart_318849 := by decide
  rcases family_descends (prefixWord ++ tailWord_318849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318856 : List Nat := [2, 1, 3, 3, 1, 3, 2, 1, 4]
def baseStart_318856 : Nat := 118140960795 + 318856 * 2 ^ 59
def prefixEnd_318856 : Nat := 4983230072969 + 3 ^ 40 * 318856 * 2
def baseEnd_318856 : Nat := 145534566728986407229879

theorem tailTrace_318856 : CollatzResearch.WordTrace tailWord_318856 prefixEnd_318856 145534566728986407229879 := by
  unfold tailWord_318856
  simp only [CollatzResearch.WordTrace]
  refine ⟨5814816866423321557212211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7753089155231095409616281 5814816866423321557212211)
  ·
    refine ⟨8722225299634982335818317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5814816866423321557212211 8722225299634982335818317)
    ·
      refine ⟨3270834487363118375931869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8722225299634982335818317 3270834487363118375931869)
      ·
        refine ⟨1226562932761169390974451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3270834487363118375931869 1226562932761169390974451)
        ·
          refine ⟨1839844399141754086461677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1226562932761169390974451 1839844399141754086461677)
          ·
            refine ⟨689941649678157782423129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1839844399141754086461677 689941649678157782423129)
            ·
              refine ⟨517456237258618336817347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 689941649678157782423129 517456237258618336817347)
              ·
                refine ⟨776184355887927505226021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 517456237258618336817347 776184355887927505226021)
                ·
                  refine ⟨145534566728986407229879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 776184355887927505226021 145534566728986407229879)
                  ·
                    rfl

theorem cell20_318856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 2, 1, 4].length) (baseStart_318856 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_318856 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_318856 prefixEnd_318856 := by exact prefixLift 318856
  have htrace : WordTrace (prefixWord ++ tailWord_318856) baseStart_318856 baseEnd_318856 := by
    simpa [prefixWord, tailWord_318856, baseEnd_318856] using wordTrace_append hprefix tailTrace_318856
  have hstable : (prefixWord ++ tailWord_318856).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318856).length < 2 ^ (prefixWord ++ tailWord_318856).sum := by decide
  have hdescent : baseEnd_318856 < baseStart_318856 := by decide
  rcases family_descends (prefixWord ++ tailWord_318856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318876 : List Nat := [2, 2, 3, 4, 2, 1, 2, 4]
def baseStart_318876 : Nat := 118140960795 + 318876 * 2 ^ 59
def prefixEnd_318876 : Nat := 4983230072969 + 3 ^ 40 * 318876 * 2
def baseEnd_318876 : Nat := 48514565091318408854377

theorem tailTrace_318876 : CollatzResearch.WordTrace tailWord_318876 prefixEnd_318876 48514565091318408854377 := by
  unfold tailWord_318876
  simp only [CollatzResearch.WordTrace]
  refine ⟨5815181596387093265076241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7753575461849457686768321 5815181596387093265076241)
  ·
    refine ⟨4361386197290319948807181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5815181596387093265076241 4361386197290319948807181)
    ·
      refine ⟨1635519823983869980802693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4361386197290319948807181 1635519823983869980802693)
      ·
        refine ⟨306659966996975621400505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1635519823983869980802693 306659966996975621400505)
        ·
          refine ⟨229994975247731716050379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 306659966996975621400505 229994975247731716050379)
          ·
            refine ⟨344992462871597574075569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 229994975247731716050379 344992462871597574075569)
            ·
              refine ⟨258744347153698180556677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 344992462871597574075569 258744347153698180556677)
              ·
                refine ⟨48514565091318408854377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 258744347153698180556677 48514565091318408854377)
                ·
                  rfl

theorem cell20_318876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 2, 4].length) (baseStart_318876 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_318876 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_318876 prefixEnd_318876 := by exact prefixLift 318876
  have htrace : WordTrace (prefixWord ++ tailWord_318876) baseStart_318876 baseEnd_318876 := by
    simpa [prefixWord, tailWord_318876, baseEnd_318876] using wordTrace_append hprefix tailTrace_318876
  have hstable : (prefixWord ++ tailWord_318876).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318876).length < 2 ^ (prefixWord ++ tailWord_318876).sum := by decide
  have hdescent : baseEnd_318876 < baseStart_318876 := by decide
  rcases family_descends (prefixWord ++ tailWord_318876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318901 : List Nat := [1, 3, 3, 2, 2, 3, 6]
def baseStart_318901 : Nat := 118140960795 + 318901 * 2 ^ 59
def prefixEnd_318901 : Nat := 4983230072969 + 3 ^ 40 * 318901 * 2
def baseEnd_318901 : Nat := 16172789550574027858855

theorem tailTrace_318901 : CollatzResearch.WordTrace tailWord_318901 prefixEnd_318901 16172789550574027858855 := by
  unfold tailWord_318901
  simp only [CollatzResearch.WordTrace]
  refine ⟨11631275017683615799812557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7754183345122410533208371 11631275017683615799812557)
  ·
    refine ⟨4361728131631355924929709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11631275017683615799812557 4361728131631355924929709)
    ·
      refine ⟨1635648049361758471848641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4361728131631355924929709 1635648049361758471848641)
      ·
        refine ⟨1226736037021318853886481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1635648049361758471848641 1226736037021318853886481)
        ·
          refine ⟨920052027765989140414861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1226736037021318853886481 920052027765989140414861)
          ·
            refine ⟨345019510412245927655573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 920052027765989140414861 345019510412245927655573)
            ·
              refine ⟨16172789550574027858855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 345019510412245927655573 16172789550574027858855)
              ·
                rfl

theorem cell20_318901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 6].length) (baseStart_318901 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_318901 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_318901 prefixEnd_318901 := by exact prefixLift 318901
  have htrace : WordTrace (prefixWord ++ tailWord_318901) baseStart_318901 baseEnd_318901 := by
    simpa [prefixWord, tailWord_318901, baseEnd_318901] using wordTrace_append hprefix tailTrace_318901
  have hstable : (prefixWord ++ tailWord_318901).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318901).length < 2 ^ (prefixWord ++ tailWord_318901).sum := by decide
  have hdescent : baseEnd_318901 < baseStart_318901 := by decide
  rcases family_descends (prefixWord ++ tailWord_318901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318915 : List Nat := [1, 1, 1, 3, 1, 1, 7, 1, 4]
def baseStart_318915 : Nat := 118140960795 + 318915 * 2 ^ 59
def prefixEnd_318915 : Nat := 4983230072969 + 3 ^ 40 * 318915 * 2
def baseEnd_318915 : Nat := 145561495936644424262971

theorem tailTrace_318915 : CollatzResearch.WordTrace tailWord_318915 prefixEnd_318915 145561495936644424262971 := by
  unfold tailWord_318915
  simp only [CollatzResearch.WordTrace]
  refine ⟨11631785639632896190822199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7754523759755264127214799 11631785639632896190822199)
  ·
    refine ⟨17447678459449344286233299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11631785639632896190822199 17447678459449344286233299)
    ·
      refine ⟨26171517689174016429349949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17447678459449344286233299 26171517689174016429349949)
      ·
        refine ⟨9814319133440256161006231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26171517689174016429349949 9814319133440256161006231)
        ·
          refine ⟨14721478700160384241509347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9814319133440256161006231 14721478700160384241509347)
          ·
            refine ⟨22082218050240576362264021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14721478700160384241509347 22082218050240576362264021)
            ·
              refine ⟨517551985552513508490563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 22082218050240576362264021 517551985552513508490563)
              ·
                refine ⟨776327978328770262735845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 517551985552513508490563 776327978328770262735845)
                ·
                  refine ⟨145561495936644424262971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 776327978328770262735845 145561495936644424262971)
                  ·
                    rfl

theorem cell20_318915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 7, 1, 4].length) (baseStart_318915 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_318915 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_318915 prefixEnd_318915 := by exact prefixLift 318915
  have htrace : WordTrace (prefixWord ++ tailWord_318915) baseStart_318915 baseEnd_318915 := by
    simpa [prefixWord, tailWord_318915, baseEnd_318915] using wordTrace_append hprefix tailTrace_318915
  have hstable : (prefixWord ++ tailWord_318915).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318915).length < 2 ^ (prefixWord ++ tailWord_318915).sum := by decide
  have hdescent : baseEnd_318915 < baseStart_318915 := by decide
  rcases family_descends (prefixWord ++ tailWord_318915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318922 : List Nat := [3, 1, 2, 1, 2, 3, 1, 7]
def baseStart_318922 : Nat := 118140960795 + 318922 * 2 ^ 59
def prefixEnd_318922 : Nat := 4983230072969 + 3 ^ 40 * 318922 * 2
def baseEnd_318922 : Nat := 48521563642461170343203

theorem tailTrace_318922 : CollatzResearch.WordTrace tailWord_318922 prefixEnd_318922 48521563642461170343203 := by
  unfold tailWord_318922
  simp only [CollatzResearch.WordTrace]
  refine ⟨2908010237651884096581755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7754693967071690924218013 2908010237651884096581755)
  ·
    refine ⟨4362015356477826144872633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2908010237651884096581755 4362015356477826144872633)
    ·
      refine ⟨3271511517358369608654475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4362015356477826144872633 3271511517358369608654475)
      ·
        refine ⟨4907267276037554412981713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3271511517358369608654475 4907267276037554412981713)
        ·
          refine ⟨3680450457028165809736285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4907267276037554412981713 3680450457028165809736285)
          ·
            refine ⟨1380168921385562178651107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3680450457028165809736285 1380168921385562178651107)
            ·
              refine ⟨2070253382078343267976661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1380168921385562178651107 2070253382078343267976661)
              ·
                refine ⟨48521563642461170343203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2070253382078343267976661 48521563642461170343203)
                ·
                  rfl

theorem cell20_318922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 7].length) (baseStart_318922 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_318922 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_318922 prefixEnd_318922 := by exact prefixLift 318922
  have htrace : WordTrace (prefixWord ++ tailWord_318922) baseStart_318922 baseEnd_318922 := by
    simpa [prefixWord, tailWord_318922, baseEnd_318922] using wordTrace_append hprefix tailTrace_318922
  have hstable : (prefixWord ++ tailWord_318922).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318922).length < 2 ^ (prefixWord ++ tailWord_318922).sum := by decide
  have hdescent : baseEnd_318922 < baseStart_318922 := by decide
  rcases family_descends (prefixWord ++ tailWord_318922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318966 : List Nat := [5, 1, 1, 1, 2, 2, 4, 2, 2]
def baseStart_318966 : Nat := 118140960795 + 318966 * 2 ^ 59
def prefixEnd_318966 : Nat := 4983230072969 + 3 ^ 40 * 318966 * 2
def baseEnd_318966 : Nat := 145584773726314913562763

theorem tailTrace_318966 : CollatzResearch.WordTrace tailWord_318966 prefixEnd_318966 145584773726314913562763 := by
  unfold tailWord_318966
  simp only [CollatzResearch.WordTrace]
  refine ⟨727102860153008243808047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7755763841632087933952501 727102860153008243808047)
  ·
    refine ⟨1090654290229512365712071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 727102860153008243808047 1090654290229512365712071)
    ·
      refine ⟨1635981435344268548568107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1090654290229512365712071 1635981435344268548568107)
      ·
        refine ⟨2453972153016402822852161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1635981435344268548568107 2453972153016402822852161)
        ·
          refine ⟨1840479114762302117139121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2453972153016402822852161 1840479114762302117139121)
          ·
            refine ⟨1380359336071726587854341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1840479114762302117139121 1380359336071726587854341)
            ·
              refine ⟨258817375513448735222689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1380359336071726587854341 258817375513448735222689)
              ·
                refine ⟨194113031635086551417017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 258817375513448735222689 194113031635086551417017)
                ·
                  refine ⟨145584773726314913562763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 194113031635086551417017 145584773726314913562763)
                  ·
                    rfl

theorem cell20_318966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 4, 2, 2].length) (baseStart_318966 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_318966 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_318966 prefixEnd_318966 := by exact prefixLift 318966
  have htrace : WordTrace (prefixWord ++ tailWord_318966) baseStart_318966 baseEnd_318966 := by
    simpa [prefixWord, tailWord_318966, baseEnd_318966] using wordTrace_append hprefix tailTrace_318966
  have hstable : (prefixWord ++ tailWord_318966).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318966).length < 2 ^ (prefixWord ++ tailWord_318966).sum := by decide
  have hdescent : baseEnd_318966 < baseStart_318966 := by decide
  rcases family_descends (prefixWord ++ tailWord_318966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318970 : List Nat := [3, 1, 1, 1, 1, 2, 5, 4, 2]
def baseStart_318970 : Nat := 118140960795 + 318970 * 2 ^ 59
def prefixEnd_318970 : Nat := 4983230072969 + 3 ^ 40 * 318970 * 2
def baseEnd_318970 : Nat := 145586599435308677429413

theorem tailTrace_318970 : CollatzResearch.WordTrace tailWord_318970 prefixEnd_318970 145586599435308677429413 := by
  unfold tailWord_318970
  simp only [CollatzResearch.WordTrace]
  refine ⟨2908447913608410146018591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7755861102955760389382909 2908447913608410146018591)
  ·
    refine ⟨4362671870412615219027887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2908447913608410146018591 4362671870412615219027887)
    ·
      refine ⟨6544007805618922828541831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4362671870412615219027887 6544007805618922828541831)
      ·
        refine ⟨9816011708428384242812747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6544007805618922828541831 9816011708428384242812747)
        ·
          refine ⟨14724017562642576364219121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9816011708428384242812747 14724017562642576364219121)
          ·
            refine ⟨11043013171981932273164341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14724017562642576364219121 11043013171981932273164341)
            ·
              refine ⟨1035282484873306150609157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11043013171981932273164341 1035282484873306150609157)
              ·
                refine ⟨194115465913744903239217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1035282484873306150609157 194115465913744903239217)
                ·
                  refine ⟨145586599435308677429413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 194115465913744903239217 145586599435308677429413)
                  ·
                    rfl

theorem cell20_318970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 4, 2].length) (baseStart_318970 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_318970 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_318970 prefixEnd_318970 := by exact prefixLift 318970
  have htrace : WordTrace (prefixWord ++ tailWord_318970) baseStart_318970 baseEnd_318970 := by
    simpa [prefixWord, tailWord_318970, baseEnd_318970] using wordTrace_append hprefix tailTrace_318970
  have hstable : (prefixWord ++ tailWord_318970).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318970).length < 2 ^ (prefixWord ++ tailWord_318970).sum := by decide
  have hdescent : baseEnd_318970 < baseStart_318970 := by decide
  rcases family_descends (prefixWord ++ tailWord_318970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318984 : List Nat := [2, 1, 3, 2, 1, 1, 4, 3, 3]
def baseStart_318984 : Nat := 118140960795 + 318984 * 2 ^ 59
def prefixEnd_318984 : Nat := 4983230072969 + 3 ^ 40 * 318984 * 2
def baseEnd_318984 : Nat := 145592989416786850962689

theorem tailTrace_318984 : CollatzResearch.WordTrace tailWord_318984 prefixEnd_318984 145592989416786850962689 := by
  unfold tailWord_318984
  simp only [CollatzResearch.WordTrace]
  refine ⟨5817151138191460487542003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7756201517588613983389337 5817151138191460487542003)
  ·
    refine ⟨8725726707287190731313005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5817151138191460487542003 8725726707287190731313005)
    ·
      refine ⟨3272147515232696524242377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8725726707287190731313005 3272147515232696524242377)
      ·
        refine ⟨2454110636424522393181783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3272147515232696524242377 2454110636424522393181783)
        ·
          refine ⟨3681165954636783589772675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2454110636424522393181783 3681165954636783589772675)
          ·
            refine ⟨5521748931955175384659013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3681165954636783589772675 5521748931955175384659013)
            ·
              refine ⟨1035327924741595384623565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5521748931955175384659013 1035327924741595384623565)
              ·
                refine ⟨388247971778098269233837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1035327924741595384623565 388247971778098269233837)
                ·
                  refine ⟨145592989416786850962689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 388247971778098269233837 145592989416786850962689)
                  ·
                    rfl

theorem cell20_318984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 3, 3].length) (baseStart_318984 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_318984 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_318984 prefixEnd_318984 := by exact prefixLift 318984
  have htrace : WordTrace (prefixWord ++ tailWord_318984) baseStart_318984 baseEnd_318984 := by
    simpa [prefixWord, tailWord_318984, baseEnd_318984] using wordTrace_append hprefix tailTrace_318984
  have hstable : (prefixWord ++ tailWord_318984).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318984).length < 2 ^ (prefixWord ++ tailWord_318984).sum := by decide
  have hdescent : baseEnd_318984 < baseStart_318984 := by decide
  rcases family_descends (prefixWord ++ tailWord_318984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319029 : List Nat := [1, 3, 3, 1, 1, 3, 1, 3, 4]
def baseStart_319029 : Nat := 118140960795 + 319029 * 2 ^ 59
def prefixEnd_319029 : Nat := 4983230072969 + 3 ^ 40 * 319029 * 2
def baseEnd_319029 : Nat := 145613528642966694462505

theorem tailTrace_319029 : CollatzResearch.WordTrace tailWord_319029 prefixEnd_319029 145613528642966694462505 := by
  unfold tailWord_319029
  simp only [CollatzResearch.WordTrace]
  refine ⟨11635943561219893660472141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7757295707479929106981427 11635943561219893660472141)
  ·
    refine ⟨4363478835457460122677053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11635943561219893660472141 4363478835457460122677053)
    ·
      refine ⟨1636304563296547546003895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4363478835457460122677053 1636304563296547546003895)
      ·
        refine ⟨2454456844944821319005843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1636304563296547546003895 2454456844944821319005843)
        ·
          refine ⟨3681685267417231978508765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2454456844944821319005843 3681685267417231978508765)
          ·
            refine ⟨1380631975281461991940787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3681685267417231978508765 1380631975281461991940787)
            ·
              refine ⟨2070947962922192987911181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1380631975281461991940787 2070947962922192987911181)
              ·
                refine ⟨776605486095822370466693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2070947962922192987911181 776605486095822370466693)
                ·
                  refine ⟨145613528642966694462505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 776605486095822370466693 145613528642966694462505)
                  ·
                    rfl

theorem cell20_319029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 3, 4].length) (baseStart_319029 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_319029 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_319029 prefixEnd_319029 := by exact prefixLift 319029
  have htrace : WordTrace (prefixWord ++ tailWord_319029) baseStart_319029 baseEnd_319029 := by
    simpa [prefixWord, tailWord_319029, baseEnd_319029] using wordTrace_append hprefix tailTrace_319029
  have hstable : (prefixWord ++ tailWord_319029).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319029).length < 2 ^ (prefixWord ++ tailWord_319029).sum := by decide
  have hdescent : baseEnd_319029 < baseStart_319029 := by decide
  rcases family_descends (prefixWord ++ tailWord_319029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319039 : List Nat := [1, 1, 2, 2, 3, 4, 3, 1, 3]
def baseStart_319039 : Nat := 118140960795 + 319039 * 2 ^ 59
def prefixEnd_319039 : Nat := 4983230072969 + 3 ^ 40 * 319039 * 2
def baseEnd_319039 : Nat := 145618092915451104129131

theorem tailTrace_319039 : CollatzResearch.WordTrace tailWord_319039 prefixEnd_319039 145618092915451104129131 := by
  unfold tailWord_319039
  simp only [CollatzResearch.WordTrace]
  refine ⟨11636308291183665368336171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7757538860789110245557447 11636308291183665368336171)
  ·
    refine ⟨17454462436775498052504257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11636308291183665368336171 17454462436775498052504257)
    ·
      refine ⟨13090846827581623539378193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17454462436775498052504257 13090846827581623539378193)
      ·
        refine ⟨9818135120686217654533645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13090846827581623539378193 9818135120686217654533645)
        ·
          refine ⟨3681800670257331620450117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9818135120686217654533645 3681800670257331620450117)
          ·
            refine ⟨690337625673249678834397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3681800670257331620450117 690337625673249678834397)
            ·
              refine ⟨258876609627468629562899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 690337625673249678834397 258876609627468629562899)
              ·
                refine ⟨388314914441202944344349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 258876609627468629562899 388314914441202944344349)
                ·
                  refine ⟨145618092915451104129131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 388314914441202944344349 145618092915451104129131)
                  ·
                    rfl

theorem cell20_319039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 3, 1, 3].length) (baseStart_319039 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_319039 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_319039 prefixEnd_319039 := by exact prefixLift 319039
  have htrace : WordTrace (prefixWord ++ tailWord_319039) baseStart_319039 baseEnd_319039 := by
    simpa [prefixWord, tailWord_319039, baseEnd_319039] using wordTrace_append hprefix tailTrace_319039
  have hstable : (prefixWord ++ tailWord_319039).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319039).length < 2 ^ (prefixWord ++ tailWord_319039).sum := by decide
  have hdescent : baseEnd_319039 < baseStart_319039 := by decide
  rcases family_descends (prefixWord ++ tailWord_319039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319063 : List Nat := [1, 1, 3, 2, 2, 5, 1, 3, 2]
def baseStart_319063 : Nat := 118140960795 + 319063 * 2 ^ 59
def prefixEnd_319063 : Nat := 4983230072969 + 3 ^ 40 * 319063 * 2
def baseEnd_319063 : Nat := 145629047169413687329033

theorem tailTrace_319063 : CollatzResearch.WordTrace tailWord_319063 prefixEnd_319063 145629047169413687329033 := by
  unfold tailWord_319063
  simp only [CollatzResearch.WordTrace]
  refine ⟨11637183643096717467209843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7758122428731144978139895 11637183643096717467209843)
  ·
    refine ⟨17455775464645076200814765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11637183643096717467209843 17455775464645076200814765)
    ·
      refine ⟨6545915799241903575305537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17455775464645076200814765 6545915799241903575305537)
      ·
        refine ⟨4909436849431427681479153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6545915799241903575305537 4909436849431427681479153)
        ·
          refine ⟨3682077637073570761109365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4909436849431427681479153 3682077637073570761109365)
          ·
            refine ⟨345194778475647258854003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3682077637073570761109365 345194778475647258854003)
            ·
              refine ⟨517792167713470888281005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 345194778475647258854003 517792167713470888281005)
              ·
                refine ⟨194172062892551583105377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 517792167713470888281005 194172062892551583105377)
                ·
                  refine ⟨145629047169413687329033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 194172062892551583105377 145629047169413687329033)
                  ·
                    rfl

theorem cell20_319063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 1, 3, 2].length) (baseStart_319063 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_319063 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_319063 prefixEnd_319063 := by exact prefixLift 319063
  have htrace : WordTrace (prefixWord ++ tailWord_319063) baseStart_319063 baseEnd_319063 := by
    simpa [prefixWord, tailWord_319063, baseEnd_319063] using wordTrace_append hprefix tailTrace_319063
  have hstable : (prefixWord ++ tailWord_319063).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319063).length < 2 ^ (prefixWord ++ tailWord_319063).sum := by decide
  have hdescent : baseEnd_319063 < baseStart_319063 := by decide
  rcases family_descends (prefixWord ++ tailWord_319063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319080 : List Nat := [2, 1, 4, 3, 1, 2, 3, 2, 2]
def baseStart_319080 : Nat := 118140960795 + 319080 * 2 ^ 59
def prefixEnd_319080 : Nat := 4983230072969 + 3 ^ 40 * 319080 * 2
def baseEnd_319080 : Nat := 145636806432637183762297

theorem tailTrace_319080 : CollatzResearch.WordTrace tailWord_319080 prefixEnd_319080 145636806432637183762297 := by
  unfold tailWord_319080
  simp only [CollatzResearch.WordTrace]
  refine ⟨5818901842017564685289347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7758535789356752913719129 5818901842017564685289347)
  ·
    refine ⟨8728352763026347027934021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5818901842017564685289347 8728352763026347027934021)
    ·
      refine ⟨1636566143067440067737629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8728352763026347027934021 1636566143067440067737629)
      ·
        refine ⟨613712303650290025401611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1636566143067440067737629 613712303650290025401611)
        ·
          refine ⟨920568455475435038102417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 613712303650290025401611 920568455475435038102417)
          ·
            refine ⟨690426341606576278576813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 920568455475435038102417 690426341606576278576813)
            ·
              refine ⟨258909878102466104466305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 690426341606576278576813 258909878102466104466305)
              ·
                refine ⟨194182408576849578349729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 258909878102466104466305 194182408576849578349729)
                ·
                  refine ⟨145636806432637183762297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 194182408576849578349729 145636806432637183762297)
                  ·
                    rfl

theorem cell20_319080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 3, 2, 2].length) (baseStart_319080 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_319080 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_319080 prefixEnd_319080 := by exact prefixLift 319080
  have htrace : WordTrace (prefixWord ++ tailWord_319080) baseStart_319080 baseEnd_319080 := by
    simpa [prefixWord, tailWord_319080, baseEnd_319080] using wordTrace_append hprefix tailTrace_319080
  have hstable : (prefixWord ++ tailWord_319080).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319080).length < 2 ^ (prefixWord ++ tailWord_319080).sum := by decide
  have hdescent : baseEnd_319080 < baseStart_319080 := by decide
  rcases family_descends (prefixWord ++ tailWord_319080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319081 : List Nat := [1, 2, 1, 1, 1, 4, 4, 1, 5]
def baseStart_319081 : Nat := 118140960795 + 319081 * 2 ^ 59
def prefixEnd_319081 : Nat := 4983230072969 + 3 ^ 40 * 319081 * 2
def baseEnd_319081 : Nat := 145637262859885624728959

theorem tailTrace_319081 : CollatzResearch.WordTrace tailWord_319081 prefixEnd_319081 145637262859885624728959 := by
  unfold tailWord_319081
  simp only [CollatzResearch.WordTrace]
  refine ⟨11637840157031506541365097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7758560104687671027576731 11637840157031506541365097)
  ·
    refine ⟨8728380117773629906023823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11637840157031506541365097 8728380117773629906023823)
    ·
      refine ⟨13092570176660444859035735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8728380117773629906023823 13092570176660444859035735)
      ·
        refine ⟨19638855264990667288553603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13092570176660444859035735 19638855264990667288553603)
        ·
          refine ⟨29458282897486000932830405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19638855264990667288553603 29458282897486000932830405)
          ·
            refine ⟨5523428043278625174905701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29458282897486000932830405 5523428043278625174905701)
            ·
              refine ⟨1035642758114742220294819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5523428043278625174905701 1035642758114742220294819)
              ·
                refine ⟨1553464137172113330442229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1035642758114742220294819 1553464137172113330442229)
                ·
                  refine ⟨145637262859885624728959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1553464137172113330442229 145637262859885624728959)
                  ·
                    rfl

theorem cell20_319081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 1, 5].length) (baseStart_319081 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_319081 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_319081 prefixEnd_319081 := by exact prefixLift 319081
  have htrace : WordTrace (prefixWord ++ tailWord_319081) baseStart_319081 baseEnd_319081 := by
    simpa [prefixWord, tailWord_319081, baseEnd_319081] using wordTrace_append hprefix tailTrace_319081
  have hstable : (prefixWord ++ tailWord_319081).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319081).length < 2 ^ (prefixWord ++ tailWord_319081).sum := by decide
  have hdescent : baseEnd_319081 < baseStart_319081 := by decide
  rcases family_descends (prefixWord ++ tailWord_319081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319094 : List Nat := [5, 1, 1, 2, 2, 1, 4, 1, 3]
def baseStart_319094 : Nat := 118140960795 + 319094 * 2 ^ 59
def prefixEnd_319094 : Nat := 4983230072969 + 3 ^ 40 * 319094 * 2
def baseEnd_319094 : Nat := 145643196414115357295573

theorem tailTrace_319094 : CollatzResearch.WordTrace tailWord_319094 prefixEnd_319094 145643196414115357295573 := by
  unfold tailWord_319094
  simp only [CollatzResearch.WordTrace]
  refine ⟨727394644124025610099271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7758876203989606507725557 727394644124025610099271)
  ·
    refine ⟨1091091966186038415148907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 727394644124025610099271 1091091966186038415148907)
    ·
      refine ⟨1636637949279057622723361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1091091966186038415148907 1636637949279057622723361)
      ·
        refine ⟨1227478461959293217042521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1636637949279057622723361 1227478461959293217042521)
        ·
          refine ⟨920608846469469912781891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1227478461959293217042521 920608846469469912781891)
          ·
            refine ⟨1380913269704204869172837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 920608846469469912781891 1380913269704204869172837)
            ·
              refine ⟨258921238069538412969907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1380913269704204869172837 258921238069538412969907)
              ·
                refine ⟨388381857104307619454861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 258921238069538412969907 388381857104307619454861)
                ·
                  refine ⟨145643196414115357295573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 388381857104307619454861 145643196414115357295573)
                  ·
                    rfl

theorem cell20_319094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 4, 1, 3].length) (baseStart_319094 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_319094 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_319094 prefixEnd_319094 := by exact prefixLift 319094
  have htrace : WordTrace (prefixWord ++ tailWord_319094) baseStart_319094 baseEnd_319094 := by
    simpa [prefixWord, tailWord_319094, baseEnd_319094] using wordTrace_append hprefix tailTrace_319094
  have hstable : (prefixWord ++ tailWord_319094).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319094).length < 2 ^ (prefixWord ++ tailWord_319094).sum := by decide
  have hdescent : baseEnd_319094 < baseStart_319094 := by decide
  rcases family_descends (prefixWord ++ tailWord_319094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319135 : List Nat := [1, 1, 2, 7, 1, 2, 2, 2, 2]
def baseStart_319135 : Nat := 118140960795 + 319135 * 2 ^ 59
def prefixEnd_319135 : Nat := 4983230072969 + 3 ^ 40 * 319135 * 2
def baseEnd_319135 : Nat := 145661909931301436928739

theorem tailTrace_319135 : CollatzResearch.WordTrace tailWord_319135 prefixEnd_319135 145661909931301436928739 := by
  unfold tailWord_319135
  simp only [CollatzResearch.WordTrace]
  refine ⟨11639809698835873763830859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7759873132557249175887239 11639809698835873763830859)
  ·
    refine ⟨17459714548253810645746289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11639809698835873763830859 17459714548253810645746289)
    ·
      refine ⟨13094785911190357984309717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17459714548253810645746289 13094785911190357984309717)
      ·
        refine ⟨306909044793524015257259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 13094785911190357984309717 306909044793524015257259)
        ·
          refine ⟨460363567190286022885889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 306909044793524015257259 460363567190286022885889)
          ·
            refine ⟨345272675392714517164417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 460363567190286022885889 345272675392714517164417)
            ·
              refine ⟨258954506544535887873313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 345272675392714517164417 258954506544535887873313)
              ·
                refine ⟨194215879908401915904985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 258954506544535887873313 194215879908401915904985)
                ·
                  refine ⟨145661909931301436928739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 194215879908401915904985 145661909931301436928739)
                  ·
                    rfl

theorem cell20_319135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 2, 2, 2].length) (baseStart_319135 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_319135 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_319135 prefixEnd_319135 := by exact prefixLift 319135
  have htrace : WordTrace (prefixWord ++ tailWord_319135) baseStart_319135 baseEnd_319135 := by
    simpa [prefixWord, tailWord_319135, baseEnd_319135] using wordTrace_append hprefix tailTrace_319135
  have hstable : (prefixWord ++ tailWord_319135).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319135).length < 2 ^ (prefixWord ++ tailWord_319135).sum := by decide
  have hdescent : baseEnd_319135 < baseStart_319135 := by decide
  rcases family_descends (prefixWord ++ tailWord_319135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319136 : List Nat := [2, 1, 1, 4, 3, 1, 1, 4, 3]
def baseStart_319136 : Nat := 118140960795 + 319136 * 2 ^ 59
def prefixEnd_319136 : Nat := 4983230072969 + 3 ^ 40 * 319136 * 2
def baseEnd_319136 : Nat := 145662366358549877895401

theorem tailTrace_319136 : CollatzResearch.WordTrace tailWord_319136 prefixEnd_319136 145662366358549877895401 := by
  unfold tailWord_319136
  simp only [CollatzResearch.WordTrace]
  refine ⟨5819923085916125467308631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7759897447888167289744841 5819923085916125467308631)
  ·
    refine ⟨8729884628874188200962947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5819923085916125467308631 8729884628874188200962947)
    ·
      refine ⟨13094826943311282301444421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8729884628874188200962947 13094826943311282301444421)
      ·
        refine ⟨2455280051870865431520829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13094826943311282301444421 2455280051870865431520829)
        ·
          refine ⟨920730019451574536820311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2455280051870865431520829 920730019451574536820311)
          ·
            refine ⟨1381095029177361805230467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 920730019451574536820311 1381095029177361805230467)
            ·
              refine ⟨2071642543766042707845701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1381095029177361805230467 2071642543766042707845701)
              ·
                refine ⟨388432976956133007721069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2071642543766042707845701 388432976956133007721069)
                ·
                  refine ⟨145662366358549877895401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 388432976956133007721069 145662366358549877895401)
                  ·
                    rfl

theorem cell20_319136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 4, 3].length) (baseStart_319136 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_319136 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_319136 prefixEnd_319136 := by exact prefixLift 319136
  have htrace : WordTrace (prefixWord ++ tailWord_319136) baseStart_319136 baseEnd_319136 := by
    simpa [prefixWord, tailWord_319136, baseEnd_319136] using wordTrace_append hprefix tailTrace_319136
  have hstable : (prefixWord ++ tailWord_319136).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319136).length < 2 ^ (prefixWord ++ tailWord_319136).sum := by decide
  have hdescent : baseEnd_319136 < baseStart_319136 := by decide
  rcases family_descends (prefixWord ++ tailWord_319136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319209 : List Nat := [1, 2, 1, 1, 1, 2, 3, 9]
def baseStart_319209 : Nat := 118140960795 + 319209 * 2 ^ 59
def prefixEnd_319209 : Nat := 4983230072969 + 3 ^ 40 * 319209 * 2
def baseEnd_319209 : Nat := 48565228515895356153923

theorem tailTrace_319209 : CollatzResearch.WordTrace tailWord_319209 prefixEnd_319209 48565228515895356153923 := by
  unfold tailWord_319209
  simp only [CollatzResearch.WordTrace]
  refine ⟨11642508700567784402024681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7761672467045189601349787 11642508700567784402024681)
  ·
    refine ⟨8731881525425838301518511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11642508700567784402024681 8731881525425838301518511)
    ·
      refine ⟨13097822288138757452277767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8731881525425838301518511 13097822288138757452277767)
      ·
        refine ⟨19646733432208136178416651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13097822288138757452277767 19646733432208136178416651)
        ·
          refine ⟨29470100148312204267624977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19646733432208136178416651 29470100148312204267624977)
          ·
            refine ⟨22102575111234153200718733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29470100148312204267624977 22102575111234153200718733)
            ·
              refine ⟨8288465666712807450269525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22102575111234153200718733 8288465666712807450269525)
              ·
                refine ⟨48565228515895356153923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8288465666712807450269525 48565228515895356153923)
                ·
                  rfl

theorem cell20_319209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 9].length) (baseStart_319209 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_319209 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_319209 prefixEnd_319209 := by exact prefixLift 319209
  have htrace : WordTrace (prefixWord ++ tailWord_319209) baseStart_319209 baseEnd_319209 := by
    simpa [prefixWord, tailWord_319209, baseEnd_319209] using wordTrace_append hprefix tailTrace_319209
  have hstable : (prefixWord ++ tailWord_319209).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319209).length < 2 ^ (prefixWord ++ tailWord_319209).sum := by decide
  have hdescent : baseEnd_319209 < baseStart_319209 := by decide
  rcases family_descends (prefixWord ++ tailWord_319209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319222 : List Nat := [5, 1, 1, 1, 1, 5, 2, 4]
def baseStart_319222 : Nat := 118140960795 + 319222 * 2 ^ 59
def prefixEnd_319222 : Nat := 4983230072969 + 3 ^ 40 * 319222 * 2
def baseEnd_319222 : Nat := 48567206367305267009461

theorem tailTrace_319222 : CollatzResearch.WordTrace tailWord_319222 prefixEnd_319222 48567206367305267009461 := by
  unfold tailWord_319222
  simp only [CollatzResearch.WordTrace]
  refine ⟨727686428095042976390495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7761988566347125081498613 727686428095042976390495)
  ·
    refine ⟨1091529642142564464585743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 727686428095042976390495 1091529642142564464585743)
    ·
      refine ⟨1637294463213846696878615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1091529642142564464585743 1637294463213846696878615)
      ·
        refine ⟨2455941694820770045317923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1637294463213846696878615 2455941694820770045317923)
        ·
          refine ⟨3683912542231155067976885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2455941694820770045317923 3683912542231155067976885)
          ·
            refine ⟨345366800834170787622833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3683912542231155067976885 345366800834170787622833)
            ·
              refine ⟨259025100625628090717125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 345366800834170787622833 259025100625628090717125)
              ·
                refine ⟨48567206367305267009461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 259025100625628090717125 48567206367305267009461)
                ·
                  rfl

theorem cell20_319222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 2, 4].length) (baseStart_319222 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_319222 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_319222 prefixEnd_319222 := by exact prefixLift 319222
  have htrace : WordTrace (prefixWord ++ tailWord_319222) baseStart_319222 baseEnd_319222 := by
    simpa [prefixWord, tailWord_319222, baseEnd_319222] using wordTrace_append hprefix tailTrace_319222
  have hstable : (prefixWord ++ tailWord_319222).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319222).length < 2 ^ (prefixWord ++ tailWord_319222).sum := by decide
  have hdescent : baseEnd_319222 < baseStart_319222 := by decide
  rcases family_descends (prefixWord ++ tailWord_319222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319233 : List Nat := [1, 2, 4, 1, 1, 1, 3, 2, 5]
def baseStart_319233 : Nat := 118140960795 + 319233 * 2 ^ 59
def prefixEnd_319233 : Nat := 4983230072969 + 3 ^ 40 * 319233 * 2
def baseEnd_319233 : Nat := 145706639801648651661671

theorem tailTrace_319233 : CollatzResearch.WordTrace tailWord_319233 prefixEnd_319233 145706639801648651661671 := by
  unfold tailWord_319233
  simp only [CollatzResearch.WordTrace]
  refine ⟨11643384052480836500898353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7762256034987224333932235 11643384052480836500898353)
  ·
    refine ⟨8732538039360627375673765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11643384052480836500898353 8732538039360627375673765)
    ·
      refine ⟨1637350882380117632938831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8732538039360627375673765 1637350882380117632938831)
      ·
        refine ⟨2456026323570176449408247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1637350882380117632938831 2456026323570176449408247)
        ·
          refine ⟨3684039485355264674112371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2456026323570176449408247 3684039485355264674112371)
          ·
            refine ⟨5526059228032897011168557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3684039485355264674112371 5526059228032897011168557)
            ·
              refine ⟨2072272210512336379188209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5526059228032897011168557 2072272210512336379188209)
              ·
                refine ⟨1554204157884252284391157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2072272210512336379188209 1554204157884252284391157)
                ·
                  refine ⟨145706639801648651661671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1554204157884252284391157 145706639801648651661671)
                  ·
                    rfl

theorem cell20_319233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 2, 5].length) (baseStart_319233 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_319233 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_319233 prefixEnd_319233 := by exact prefixLift 319233
  have htrace : WordTrace (prefixWord ++ tailWord_319233) baseStart_319233 baseEnd_319233 := by
    simpa [prefixWord, tailWord_319233, baseEnd_319233] using wordTrace_append hprefix tailTrace_319233
  have hstable : (prefixWord ++ tailWord_319233).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319233).length < 2 ^ (prefixWord ++ tailWord_319233).sum := by decide
  have hdescent : baseEnd_319233 < baseStart_319233 := by decide
  rcases family_descends (prefixWord ++ tailWord_319233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319245 : List Nat := [1, 7, 2, 1, 1, 1, 3, 2, 2]
def baseStart_319245 : Nat := 118140960795 + 319245 * 2 ^ 59
def prefixEnd_319245 : Nat := 4983230072969 + 3 ^ 40 * 319245 * 2
def baseEnd_319245 : Nat := 145712116928629943261623

theorem tailTrace_319245 : CollatzResearch.WordTrace tailWord_319245 prefixEnd_319245 145712116928629943261623 := by
  unfold tailWord_319245
  simp only [CollatzResearch.WordTrace]
  refine ⟨11643821728437362550335189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7762547818958241700223459 11643821728437362550335189)
  ·
    refine ⟨272902071760250684773481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 11643821728437362550335189 272902071760250684773481)
    ·
      refine ⟨204676553820188013580111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 272902071760250684773481 204676553820188013580111)
      ·
        refine ⟨307014830730282020370167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204676553820188013580111 307014830730282020370167)
        ·
          refine ⟨460522246095423030555251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 307014830730282020370167 460522246095423030555251)
          ·
            refine ⟨690783369143134545832877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 460522246095423030555251 690783369143134545832877)
            ·
              refine ⟨259043763428675454687329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 690783369143134545832877 259043763428675454687329)
              ·
                refine ⟨194282822571506591015497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 259043763428675454687329 194282822571506591015497)
                ·
                  refine ⟨145712116928629943261623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 194282822571506591015497 145712116928629943261623)
                  ·
                    rfl

theorem cell20_319245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_319245 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_319245 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_319245 prefixEnd_319245 := by exact prefixLift 319245
  have htrace : WordTrace (prefixWord ++ tailWord_319245) baseStart_319245 baseEnd_319245 := by
    simpa [prefixWord, tailWord_319245, baseEnd_319245] using wordTrace_append hprefix tailTrace_319245
  have hstable : (prefixWord ++ tailWord_319245).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319245).length < 2 ^ (prefixWord ++ tailWord_319245).sum := by decide
  have hdescent : baseEnd_319245 < baseStart_319245 := by decide
  rcases family_descends (prefixWord ++ tailWord_319245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319253 : List Nat := [1, 3, 2, 1, 2, 4, 3, 2, 2]
def baseStart_319253 : Nat := 118140960795 + 319253 * 2 ^ 59
def prefixEnd_319253 : Nat := 4983230072969 + 3 ^ 40 * 319253 * 2
def baseEnd_319253 : Nat := 145715768346617470994923

theorem tailTrace_319253 : CollatzResearch.WordTrace tailWord_319253 prefixEnd_319253 145715768346617470994923 := by
  unfold tailWord_319253
  simp only [CollatzResearch.WordTrace]
  refine ⟨11644113512408379916626413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7762742341605586611084275 11644113512408379916626413)
  ·
    refine ⟨4366542567153142468734905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11644113512408379916626413 4366542567153142468734905)
    ·
      refine ⟨3274906925364856851551179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4366542567153142468734905 3274906925364856851551179)
      ·
        refine ⟨4912360388047285277326769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3274906925364856851551179 4912360388047285277326769)
        ·
          refine ⟨3684270291035463957995077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4912360388047285277326769 3684270291035463957995077)
          ·
            refine ⟨690800679569149492124077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3684270291035463957995077 690800679569149492124077)
            ·
              refine ⟨259050254838431059546529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 690800679569149492124077 259050254838431059546529)
              ·
                refine ⟨194287691128823294659897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 259050254838431059546529 194287691128823294659897)
                ·
                  refine ⟨145715768346617470994923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 194287691128823294659897 145715768346617470994923)
                  ·
                    rfl

theorem cell20_319253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 3, 2, 2].length) (baseStart_319253 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_319253 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_319253 prefixEnd_319253 := by exact prefixLift 319253
  have htrace : WordTrace (prefixWord ++ tailWord_319253) baseStart_319253 baseEnd_319253 := by
    simpa [prefixWord, tailWord_319253, baseEnd_319253] using wordTrace_append hprefix tailTrace_319253
  have hstable : (prefixWord ++ tailWord_319253).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319253).length < 2 ^ (prefixWord ++ tailWord_319253).sum := by decide
  have hdescent : baseEnd_319253 < baseStart_319253 := by decide
  rcases family_descends (prefixWord ++ tailWord_319253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319264 : List Nat := [2, 1, 1, 5, 1, 1, 4, 5]
def baseStart_319264 : Nat := 118140960795 + 319264 * 2 ^ 59
def prefixEnd_319264 : Nat := 4983230072969 + 3 ^ 40 * 319264 * 2
def baseEnd_319264 : Nat := 48573596348783440542737

theorem tailTrace_319264 : CollatzResearch.WordTrace tailWord_319264 prefixEnd_319264 48573596348783440542737 := by
  unfold tailWord_319264
  simp only [CollatzResearch.WordTrace]
  refine ⟨5822257357684264397638423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7763009810245685863517897 5822257357684264397638423)
  ·
    refine ⟨8733386036526396596457635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5822257357684264397638423 8733386036526396596457635)
    ·
      refine ⟨13100079054789594894686453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8733386036526396596457635 13100079054789594894686453)
      ·
        refine ⟨1228132411386524521376855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13100079054789594894686453 1228132411386524521376855)
        ·
          refine ⟨1842198617079786782065283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1228132411386524521376855 1842198617079786782065283)
          ·
            refine ⟨2763297925619680173097925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1842198617079786782065283 2763297925619680173097925)
            ·
              refine ⟨518118361053690032455861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2763297925619680173097925 518118361053690032455861)
              ·
                refine ⟨48573596348783440542737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 518118361053690032455861 48573596348783440542737)
                ·
                  rfl

theorem cell20_319264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 4, 5].length) (baseStart_319264 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_319264 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_319264 prefixEnd_319264 := by exact prefixLift 319264
  have htrace : WordTrace (prefixWord ++ tailWord_319264) baseStart_319264 baseEnd_319264 := by
    simpa [prefixWord, tailWord_319264, baseEnd_319264] using wordTrace_append hprefix tailTrace_319264
  have hstable : (prefixWord ++ tailWord_319264).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319264).length < 2 ^ (prefixWord ++ tailWord_319264).sum := by decide
  have hdescent : baseEnd_319264 < baseStart_319264 := by decide
  rcases family_descends (prefixWord ++ tailWord_319264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319308 : List Nat := [2, 2, 1, 3, 4, 2, 2, 2, 2]
def baseStart_319308 : Nat := 118140960795 + 319308 * 2 ^ 59
def prefixEnd_319308 : Nat := 4983230072969 + 3 ^ 40 * 319308 * 2
def baseEnd_319308 : Nat := 145740871845281724161365

theorem tailTrace_319308 : CollatzResearch.WordTrace tailWord_319308 prefixEnd_319308 145740871845281724161365 := by
  unfold tailWord_319308
  simp only [CollatzResearch.WordTrace]
  refine ⟨5823059763604562154939289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7764079684806082873252385 5823059763604562154939289)
  ·
    refine ⟨4367294822703421616204467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5823059763604562154939289 4367294822703421616204467)
    ·
      refine ⟨6550942234055132424306701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4367294822703421616204467 6550942234055132424306701)
      ·
        refine ⟨2456603337770674659115013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6550942234055132424306701 2456603337770674659115013)
        ·
          refine ⟨460613125832001498584065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2456603337770674659115013 460613125832001498584065)
          ·
            refine ⟨345459844374001123938049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 460613125832001498584065 345459844374001123938049)
            ·
              refine ⟨259094883280500842953537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 345459844374001123938049 259094883280500842953537)
              ·
                refine ⟨194321162460375632215153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 259094883280500842953537 194321162460375632215153)
                ·
                  refine ⟨145740871845281724161365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 194321162460375632215153 145740871845281724161365)
                  ·
                    rfl

theorem cell20_319308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 2, 2, 2].length) (baseStart_319308 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_319308 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_319308 prefixEnd_319308 := by exact prefixLift 319308
  have htrace : WordTrace (prefixWord ++ tailWord_319308) baseStart_319308 baseEnd_319308 := by
    simpa [prefixWord, tailWord_319308, baseEnd_319308] using wordTrace_append hprefix tailTrace_319308
  have hstable : (prefixWord ++ tailWord_319308).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319308).length < 2 ^ (prefixWord ++ tailWord_319308).sum := by decide
  have hdescent : baseEnd_319308 < baseStart_319308 := by decide
  rcases family_descends (prefixWord ++ tailWord_319308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319319 : List Nat := [1, 1, 3, 2, 5, 2, 1, 5]
def baseStart_319319 : Nat := 118140960795 + 319319 * 2 ^ 59
def prefixEnd_319319 : Nat := 4983230072969 + 3 ^ 40 * 319319 * 2
def baseEnd_319319 : Nat := 48581964181671524931551

theorem tailTrace_319319 : CollatzResearch.WordTrace tailWord_319319 prefixEnd_319319 48581964181671524931551 := by
  unfold tailWord_319319
  simp only [CollatzResearch.WordTrace]
  refine ⟨11646520730169273188529011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7764347153446182125686007 11646520730169273188529011)
  ·
    refine ⟨17469781095253909782793517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11646520730169273188529011 17469781095253909782793517)
    ·
      refine ⟨6551167910720216168547569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17469781095253909782793517 6551167910720216168547569)
      ·
        refine ⟨4913375933040162126410677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6551167910720216168547569 4913375933040162126410677)
        ·
          refine ⟨460628993722515199351001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4913375933040162126410677 460628993722515199351001)
          ·
            refine ⟨345471745291886399513251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 460628993722515199351001 345471745291886399513251)
            ·
              refine ⟨518207617937829599269877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 345471745291886399513251 518207617937829599269877)
              ·
                refine ⟨48581964181671524931551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 518207617937829599269877 48581964181671524931551)
                ·
                  rfl

theorem cell20_319319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 1, 5].length) (baseStart_319319 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_319319 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_319319 prefixEnd_319319 := by exact prefixLift 319319
  have htrace : WordTrace (prefixWord ++ tailWord_319319) baseStart_319319 baseEnd_319319 := by
    simpa [prefixWord, tailWord_319319, baseEnd_319319] using wordTrace_append hprefix tailTrace_319319
  have hstable : (prefixWord ++ tailWord_319319).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319319).length < 2 ^ (prefixWord ++ tailWord_319319).sum := by decide
  have hdescent : baseEnd_319319 < baseStart_319319 := by decide
  rcases family_descends (prefixWord ++ tailWord_319319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319364 : List Nat := [2, 3, 2, 1, 1, 1, 5, 2, 3]
def baseStart_319364 : Nat := 118140960795 + 319364 * 2 ^ 59
def prefixEnd_319364 : Nat := 4983230072969 + 3 ^ 40 * 319364 * 2
def baseEnd_319364 : Nat := 145766431771194418294469

theorem tailTrace_319364 : CollatzResearch.WordTrace tailWord_319364 prefixEnd_319364 145766431771194418294469 := by
  unfold tailWord_319364
  simp only [CollatzResearch.WordTrace]
  refine ⟨5824081007503122936958573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7765441343337497249278097 5824081007503122936958573)
  ·
    refine ⟨2184030377813671101359465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5824081007503122936958573 2184030377813671101359465)
    ·
      refine ⟨1638022783360253326019599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2184030377813671101359465 1638022783360253326019599)
      ·
        refine ⟨2457034175040379989029399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1638022783360253326019599 2457034175040379989029399)
        ·
          refine ⟨3685551262560569983544099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2457034175040379989029399 3685551262560569983544099)
          ·
            refine ⟨5528326893840854975316149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3685551262560569983544099 5528326893840854975316149)
            ·
              refine ⟨518280646297580153935889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5528326893840854975316149 518280646297580153935889)
              ·
                refine ⟨388710484723185115451917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 518280646297580153935889 388710484723185115451917)
                ·
                  refine ⟨145766431771194418294469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 388710484723185115451917 145766431771194418294469)
                  ·
                    rfl

theorem cell20_319364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5, 2, 3].length) (baseStart_319364 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_319364 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_319364 prefixEnd_319364 := by exact prefixLift 319364
  have htrace : WordTrace (prefixWord ++ tailWord_319364) baseStart_319364 baseEnd_319364 := by
    simpa [prefixWord, tailWord_319364, baseEnd_319364] using wordTrace_append hprefix tailTrace_319364
  have hstable : (prefixWord ++ tailWord_319364).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319364).length < 2 ^ (prefixWord ++ tailWord_319364).sum := by decide
  have hdescent : baseEnd_319364 < baseStart_319364 := by decide
  rcases family_descends (prefixWord ++ tailWord_319364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319385 : List Nat := [1, 2, 1, 2, 1, 3, 2, 5, 3]
def baseStart_319385 : Nat := 118140960795 + 319385 * 2 ^ 59
def prefixEnd_319385 : Nat := 4983230072969 + 3 ^ 40 * 319385 * 2
def baseEnd_319385 : Nat := 145776016743411678594383

theorem tailTrace_319385 : CollatzResearch.WordTrace tailWord_319385 prefixEnd_319385 145776016743411678594383 := by
  unfold tailWord_319385
  simp only [CollatzResearch.WordTrace]
  refine ⟨11648927947930166460431609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7765951965286777640287739 11648927947930166460431609)
  ·
    refine ⟨8736695960947624845323707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11648927947930166460431609 8736695960947624845323707)
    ·
      refine ⟨13105043941421437267985561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8736695960947624845323707 13105043941421437267985561)
      ·
        refine ⟨9828782956066077950989171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13105043941421437267985561 9828782956066077950989171)
        ·
          refine ⟨14743174434099116926483757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9828782956066077950989171 14743174434099116926483757)
          ·
            refine ⟨5528690412787168847431409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14743174434099116926483757 5528690412787168847431409)
            ·
              refine ⟨4146517809590376635573557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5528690412787168847431409 4146517809590376635573557)
              ·
                refine ⟨388736044649097809585021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4146517809590376635573557 388736044649097809585021)
                ·
                  refine ⟨145776016743411678594383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 388736044649097809585021 145776016743411678594383)
                  ·
                    rfl

theorem cell20_319385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 5, 3].length) (baseStart_319385 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_319385 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_319385 prefixEnd_319385 := by exact prefixLift 319385
  have htrace : WordTrace (prefixWord ++ tailWord_319385) baseStart_319385 baseEnd_319385 := by
    simpa [prefixWord, tailWord_319385, baseEnd_319385] using wordTrace_append hprefix tailTrace_319385
  have hstable : (prefixWord ++ tailWord_319385).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319385).length < 2 ^ (prefixWord ++ tailWord_319385).sum := by decide
  have hdescent : baseEnd_319385 < baseStart_319385 := by decide
  rcases family_descends (prefixWord ++ tailWord_319385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319412 : List Nat := [2, 5, 2, 1, 2, 2, 6]
def baseStart_319412 : Nat := 118140960795 + 319412 * 2 ^ 59
def prefixEnd_319412 : Nat := 4983230072969 + 3 ^ 40 * 319412 * 2
def baseEnd_319412 : Nat := 16198704475457731632697

theorem tailTrace_319412 : CollatzResearch.WordTrace tailWord_319412 prefixEnd_319412 16198704475457731632697 := by
  unfold tailWord_319412
  simp only [CollatzResearch.WordTrace]
  refine ⟨5824956359416175035832245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7766608479221566714442993 5824956359416175035832245)
  ·
    refine ⟨546089658695266409609273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5824956359416175035832245 546089658695266409609273)
    ·
      refine ⟨409567244021449807206955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 546089658695266409609273 409567244021449807206955)
      ·
        refine ⟨614350866032174710810433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 409567244021449807206955 614350866032174710810433)
        ·
          refine ⟨460763149524131033107825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 614350866032174710810433 460763149524131033107825)
          ·
            refine ⟨345572362143098274830869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 460763149524131033107825 345572362143098274830869)
            ·
              refine ⟨16198704475457731632697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 345572362143098274830869 16198704475457731632697)
              ·
                rfl

theorem cell20_319412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 6].length) (baseStart_319412 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_319412 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_319412 prefixEnd_319412 := by exact prefixLift 319412
  have htrace : WordTrace (prefixWord ++ tailWord_319412) baseStart_319412 baseEnd_319412 := by
    simpa [prefixWord, tailWord_319412, baseEnd_319412] using wordTrace_append hprefix tailTrace_319412
  have hstable : (prefixWord ++ tailWord_319412).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319412).length < 2 ^ (prefixWord ++ tailWord_319412).sum := by decide
  have hdescent : baseEnd_319412 < baseStart_319412 := by decide
  rcases family_descends (prefixWord ++ tailWord_319412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319423 : List Nat := [1, 1, 2, 2, 2, 1, 4, 4, 3]
def baseStart_319423 : Nat := 118140960795 + 319423 * 2 ^ 59
def prefixEnd_319423 : Nat := 4983230072969 + 3 ^ 40 * 319423 * 2
def baseEnd_319423 : Nat := 145793360978852435327561

theorem tailTrace_319423 : CollatzResearch.WordTrace tailWord_319423 prefixEnd_319423 145793360978852435327561 := by
  unfold tailWord_319423
  simp only [CollatzResearch.WordTrace]
  refine ⟨11650313921792498950314923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7766875947861665966876615 11650313921792498950314923)
  ·
    refine ⟨17475470882688748425472385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11650313921792498950314923 17475470882688748425472385)
    ·
      refine ⟨13106603162016561319104289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17475470882688748425472385 13106603162016561319104289)
      ·
        refine ⟨9829952371512420989328217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13106603162016561319104289 9829952371512420989328217)
        ·
          refine ⟨7372464278634315741996163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9829952371512420989328217 7372464278634315741996163)
          ·
            refine ⟨11058696417951473612994245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7372464278634315741996163 11058696417951473612994245)
            ·
              refine ⟨2073505578365901302436421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11058696417951473612994245 2073505578365901302436421)
              ·
                refine ⟨388782295943606494206829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2073505578365901302436421 388782295943606494206829)
                ·
                  refine ⟨145793360978852435327561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 388782295943606494206829 145793360978852435327561)
                  ·
                    rfl

theorem cell20_319423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 4, 3].length) (baseStart_319423 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_319423 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_319423 prefixEnd_319423 := by exact prefixLift 319423
  have htrace : WordTrace (prefixWord ++ tailWord_319423) baseStart_319423 baseEnd_319423 := by
    simpa [prefixWord, tailWord_319423, baseEnd_319423] using wordTrace_append hprefix tailTrace_319423
  have hstable : (prefixWord ++ tailWord_319423).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319423).length < 2 ^ (prefixWord ++ tailWord_319423).sum := by decide
  have hdescent : baseEnd_319423 < baseStart_319423 := by decide
  rcases family_descends (prefixWord ++ tailWord_319423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319440 : List Nat := [2, 1, 1, 1, 1, 2, 8, 1, 3]
def baseStart_319440 : Nat := 118140960795 + 319440 * 2 ^ 59
def prefixEnd_319440 : Nat := 4983230072969 + 3 ^ 40 * 319440 * 2
def baseEnd_319440 : Nat := 145801120242075931760825

theorem tailTrace_319440 : CollatzResearch.WordTrace tailWord_319440 prefixEnd_319440 145801120242075931760825 := by
  unfold tailWord_319440
  simp only [CollatzResearch.WordTrace]
  refine ⟨5825466981365455426841887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7767289308487273902455849 5825466981365455426841887)
  ·
    refine ⟨8738200472048183140262831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5825466981365455426841887 8738200472048183140262831)
    ·
      refine ⟨13107300708072274710394247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8738200472048183140262831 13107300708072274710394247)
      ·
        refine ⟨19660951062108412065591371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13107300708072274710394247 19660951062108412065591371)
        ·
          refine ⟨29491426593162618098387057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19660951062108412065591371 29491426593162618098387057)
          ·
            refine ⟨22118569944871963573790293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29491426593162618098387057 22118569944871963573790293)
            ·
              refine ⟨259201991541468323130355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 22118569944871963573790293 259201991541468323130355)
              ·
                refine ⟨388802987312202484695533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 259201991541468323130355 388802987312202484695533)
                ·
                  refine ⟨145801120242075931760825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 388802987312202484695533 145801120242075931760825)
                  ·
                    rfl

theorem cell20_319440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 8, 1, 3].length) (baseStart_319440 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_319440 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_319440 prefixEnd_319440 := by exact prefixLift 319440
  have htrace : WordTrace (prefixWord ++ tailWord_319440) baseStart_319440 baseEnd_319440 := by
    simpa [prefixWord, tailWord_319440, baseEnd_319440] using wordTrace_append hprefix tailTrace_319440
  have hstable : (prefixWord ++ tailWord_319440).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319440).length < 2 ^ (prefixWord ++ tailWord_319440).sum := by decide
  have hdescent : baseEnd_319440 < baseStart_319440 := by decide
  rcases family_descends (prefixWord ++ tailWord_319440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319481 : List Nat := [1, 2, 1, 3, 1, 6, 2, 2, 2]
def baseStart_319481 : Nat := 118140960795 + 319481 * 2 ^ 59
def prefixEnd_319481 : Nat := 4983230072969 + 3 ^ 40 * 319481 * 2
def baseEnd_319481 : Nat := 145819833759262011393991

theorem tailTrace_319481 : CollatzResearch.WordTrace tailWord_319481 prefixEnd_319481 145819833759262011393991 := by
  unfold tailWord_319481
  simp only [CollatzResearch.WordTrace]
  refine ⟨11652429355582374855926297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7768286237054916570617531 11652429355582374855926297)
  ·
    refine ⟨8739322016686781141944723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11652429355582374855926297 8739322016686781141944723)
    ·
      refine ⟨13108983025030171712917085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8739322016686781141944723 13108983025030171712917085)
      ·
        refine ⟨4915868634386314392343907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13108983025030171712917085 4915868634386314392343907)
        ·
          refine ⟨7373802951579471588515861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4915868634386314392343907 7373802951579471588515861)
          ·
            refine ⟨345647013355287730711681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 7373802951579471588515861 345647013355287730711681)
            ·
              refine ⟨259235260016465798033761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 345647013355287730711681 259235260016465798033761)
              ·
                refine ⟨194426445012349348525321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 259235260016465798033761 194426445012349348525321)
                ·
                  refine ⟨145819833759262011393991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 194426445012349348525321 145819833759262011393991)
                  ·
                    rfl

theorem cell20_319481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 2, 2, 2].length) (baseStart_319481 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_319481 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_319481 prefixEnd_319481 := by exact prefixLift 319481
  have htrace : WordTrace (prefixWord ++ tailWord_319481) baseStart_319481 baseEnd_319481 := by
    simpa [prefixWord, tailWord_319481, baseEnd_319481] using wordTrace_append hprefix tailTrace_319481
  have hstable : (prefixWord ++ tailWord_319481).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319481).length < 2 ^ (prefixWord ++ tailWord_319481).sum := by decide
  have hdescent : baseEnd_319481 < baseStart_319481 := by decide
  rcases family_descends (prefixWord ++ tailWord_319481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319499 : List Nat := [1, 1, 1, 1, 6, 1, 1, 5, 3]
def baseStart_319499 : Nat := 118140960795 + 319499 * 2 ^ 59
def prefixEnd_319499 : Nat := 4983230072969 + 3 ^ 40 * 319499 * 2
def baseEnd_319499 : Nat := 145828049449733948793917

theorem tailTrace_319499 : CollatzResearch.WordTrace tailWord_319499 prefixEnd_319499 145828049449733948793917 := by
  unfold tailWord_319499
  simp only [CollatzResearch.WordTrace]
  refine ⟨11653085869517163930081551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7768723913011442620054367 11653085869517163930081551)
  ·
    refine ⟨17479628804275745895122327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11653085869517163930081551 17479628804275745895122327)
    ·
      refine ⟨26219443206413618842683491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17479628804275745895122327 26219443206413618842683491)
      ·
        refine ⟨39329164809620428264025237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26219443206413618842683491 39329164809620428264025237)
        ·
          refine ⟨1843554600450957574876183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 39329164809620428264025237 1843554600450957574876183)
          ·
            refine ⟨2765331900676436362314275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1843554600450957574876183 2765331900676436362314275)
            ·
              refine ⟨4147997851014654543471413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2765331900676436362314275 4147997851014654543471413)
              ·
                refine ⟨388874798532623863450445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4147997851014654543471413 388874798532623863450445)
                ·
                  refine ⟨145828049449733948793917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 388874798532623863450445 145828049449733948793917)
                  ·
                    rfl

theorem cell20_319499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 5, 3].length) (baseStart_319499 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_319499 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_319499 prefixEnd_319499 := by exact prefixLift 319499
  have htrace : WordTrace (prefixWord ++ tailWord_319499) baseStart_319499 baseEnd_319499 := by
    simpa [prefixWord, tailWord_319499, baseEnd_319499] using wordTrace_append hprefix tailTrace_319499
  have hstable : (prefixWord ++ tailWord_319499).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319499).length < 2 ^ (prefixWord ++ tailWord_319499).sum := by decide
  have hdescent : baseEnd_319499 < baseStart_319499 := by decide
  rcases family_descends (prefixWord ++ tailWord_319499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319509 : List Nat := [1, 3, 2, 1, 5, 1, 3, 4]
def baseStart_319509 : Nat := 118140960795 + 319509 * 2 ^ 59
def prefixEnd_319509 : Nat := 4983230072969 + 3 ^ 40 * 319509 * 2
def baseEnd_319509 : Nat := 48610871240739452820181

theorem tailTrace_319509 : CollatzResearch.WordTrace tailWord_319509 prefixEnd_319509 48610871240739452820181 := by
  unfold tailWord_319509
  simp only [CollatzResearch.WordTrace]
  refine ⟨11653450599480935637945581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7768967066320623758630387 11653450599480935637945581)
  ·
    refine ⟨4370043974805350864229593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11653450599480935637945581 4370043974805350864229593)
    ·
      refine ⟨3277532981104013148172195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4370043974805350864229593 3277532981104013148172195)
      ·
        refine ⟨4916299471656019722258293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3277532981104013148172195 4916299471656019722258293)
        ·
          refine ⟨460903075467751848961715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4916299471656019722258293 460903075467751848961715)
          ·
            refine ⟨691354613201627773442573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 460903075467751848961715 691354613201627773442573)
            ·
              refine ⟨259257979950610415040965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 691354613201627773442573 259257979950610415040965)
              ·
                refine ⟨48610871240739452820181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 259257979950610415040965 48610871240739452820181)
                ·
                  rfl

theorem cell20_319509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 3, 4].length) (baseStart_319509 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_319509 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_319509 prefixEnd_319509 := by exact prefixLift 319509
  have htrace : WordTrace (prefixWord ++ tailWord_319509) baseStart_319509 baseEnd_319509 := by
    simpa [prefixWord, tailWord_319509, baseEnd_319509] using wordTrace_append hprefix tailTrace_319509
  have hstable : (prefixWord ++ tailWord_319509).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319509).length < 2 ^ (prefixWord ++ tailWord_319509).sum := by decide
  have hdescent : baseEnd_319509 < baseStart_319509 := by decide
  rcases family_descends (prefixWord ++ tailWord_319509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319530 : List Nat := [3, 1, 4, 1, 2, 2, 7]
def baseStart_319530 : Nat := 118140960795 + 319530 * 2 ^ 59
def prefixEnd_319530 : Nat := 4983230072969 + 3 ^ 40 * 319530 * 2
def baseEnd_319530 : Nat := 16204688743826179862273

theorem tailTrace_319530 : CollatzResearch.WordTrace tailWord_319530 prefixEnd_319530 16204688743826179862273 := by
  unfold tailWord_319530
  simp only [CollatzResearch.WordTrace]
  refine ⟨2913554133101214056115011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7769477688269904149640029 2913554133101214056115011)
  ·
    refine ⟨4370331199651821084172517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2913554133101214056115011 4370331199651821084172517)
    ·
      refine ⟨819437099934716453282347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4370331199651821084172517 819437099934716453282347)
      ·
        refine ⟨1229155649902074679923521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 819437099934716453282347 1229155649902074679923521)
        ·
          refine ⟨921866737426556009942641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1229155649902074679923521 921866737426556009942641)
          ·
            refine ⟨691400053069917007456981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 921866737426556009942641 691400053069917007456981)
            ·
              refine ⟨16204688743826179862273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 691400053069917007456981 16204688743826179862273)
              ·
                rfl

theorem cell20_319530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 7].length) (baseStart_319530 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_319530 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_319530 prefixEnd_319530 := by exact prefixLift 319530
  have htrace : WordTrace (prefixWord ++ tailWord_319530) baseStart_319530 baseEnd_319530 := by
    simpa [prefixWord, tailWord_319530, baseEnd_319530] using wordTrace_append hprefix tailTrace_319530
  have hstable : (prefixWord ++ tailWord_319530).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319530).length < 2 ^ (prefixWord ++ tailWord_319530).sum := by decide
  have hdescent : baseEnd_319530 < baseStart_319530 := by decide
  rcases family_descends (prefixWord ++ tailWord_319530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319537 : List Nat := [1, 2, 2, 3, 1, 4, 1, 1, 5]
def baseStart_319537 : Nat := 118140960795 + 319537 * 2 ^ 59
def prefixEnd_319537 : Nat := 4983230072969 + 3 ^ 40 * 319537 * 2
def baseEnd_319537 : Nat := 145845393685174705527095

theorem tailTrace_319537 : CollatzResearch.WordTrace tailWord_319537 prefixEnd_319537 145845393685174705527095 := by
  unfold tailWord_319537
  simp only [CollatzResearch.WordTrace]
  refine ⟨11654471843379496419964865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7769647895586330946643243 11654471843379496419964865)
  ·
    refine ⟨8740853882534622314973649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11654471843379496419964865 8740853882534622314973649)
    ·
      refine ⟨6555640411900966736230237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8740853882534622314973649 6555640411900966736230237)
      ·
        refine ⟨2458365154462862526086339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6555640411900966736230237 2458365154462862526086339)
        ·
          refine ⟨3687547731694293789129509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2458365154462862526086339 3687547731694293789129509)
          ·
            refine ⟨691415199692680085461783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3687547731694293789129509 691415199692680085461783)
            ·
              refine ⟨1037122799539020128192675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 691415199692680085461783 1037122799539020128192675)
              ·
                refine ⟨1555684199308530192289013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1037122799539020128192675 1555684199308530192289013)
                ·
                  refine ⟨145845393685174705527095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1555684199308530192289013 145845393685174705527095)
                  ·
                    rfl

theorem cell20_319537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 1, 5].length) (baseStart_319537 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_319537 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_319537 prefixEnd_319537 := by exact prefixLift 319537
  have htrace : WordTrace (prefixWord ++ tailWord_319537) baseStart_319537 baseEnd_319537 := by
    simpa [prefixWord, tailWord_319537, baseEnd_319537] using wordTrace_append hprefix tailTrace_319537
  have hstable : (prefixWord ++ tailWord_319537).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319537).length < 2 ^ (prefixWord ++ tailWord_319537).sum := by decide
  have hdescent : baseEnd_319537 < baseStart_319537 := by decide
  rcases family_descends (prefixWord ++ tailWord_319537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319550 : List Nat := [4, 2, 1, 3, 2, 1, 3, 1, 3]
def baseStart_319550 : Nat := 118140960795 + 319550 * 2 ^ 59
def prefixEnd_319550 : Nat := 4983230072969 + 3 ^ 40 * 319550 * 2
def baseEnd_319550 : Nat := 145851327239404438093709

theorem tailTrace_319550 : CollatzResearch.WordTrace tailWord_319550 prefixEnd_319550 145851327239404438093709 := by
  unfold tailWord_319550
  simp only [CollatzResearch.WordTrace]
  refine ⟨1456868249041549955023513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7769963994888266426792069 1456868249041549955023513)
  ·
    refine ⟨1092651186781162466267635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1456868249041549955023513 1092651186781162466267635)
    ·
      refine ⟨1638976780171743699401453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1092651186781162466267635 1638976780171743699401453)
      ·
        refine ⟨614616292564403887275545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1638976780171743699401453 614616292564403887275545)
        ·
          refine ⟨460962219423302915456659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 614616292564403887275545 460962219423302915456659)
          ·
            refine ⟨691443329134954373184989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 460962219423302915456659 691443329134954373184989)
            ·
              refine ⟨259291248425607889944371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 691443329134954373184989 259291248425607889944371)
              ·
                refine ⟨388936872638411834916557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 259291248425607889944371 388936872638411834916557)
                ·
                  refine ⟨145851327239404438093709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 388936872638411834916557 145851327239404438093709)
                  ·
                    rfl

theorem cell20_319550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 3, 1, 3].length) (baseStart_319550 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_319550 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_319550 prefixEnd_319550 := by exact prefixLift 319550
  have htrace : WordTrace (prefixWord ++ tailWord_319550) baseStart_319550 baseEnd_319550 := by
    simpa [prefixWord, tailWord_319550, baseEnd_319550] using wordTrace_append hprefix tailTrace_319550
  have hstable : (prefixWord ++ tailWord_319550).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319550).length < 2 ^ (prefixWord ++ tailWord_319550).sum := by decide
  have hdescent : baseEnd_319550 < baseStart_319550 := by decide
  rcases family_descends (prefixWord ++ tailWord_319550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319574 : List Nat := [5, 2, 2, 1, 1, 1, 3, 3, 2]
def baseStart_319574 : Nat := 118140960795 + 319574 * 2 ^ 59
def prefixEnd_319574 : Nat := 4983230072969 + 3 ^ 40 * 319574 * 2
def baseEnd_319574 : Nat := 145862281493367021293611

theorem tailTrace_319574 : CollatzResearch.WordTrace tailWord_319574 prefixEnd_319574 145862281493367021293611 := by
  unfold tailWord_319574
  simp only [CollatzResearch.WordTrace]
  refine ⟨728488834015340733691361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7770547562830301159374517 728488834015340733691361)
  ·
    refine ⟨546366625511505550268521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 728488834015340733691361 546366625511505550268521)
    ·
      refine ⟨409774969133629162701391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 546366625511505550268521 409774969133629162701391)
      ·
        refine ⟨614662453700443744052087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 409774969133629162701391 614662453700443744052087)
        ·
          refine ⟨921993680550665616078131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 614662453700443744052087 921993680550665616078131)
          ·
            refine ⟨1382990520825998424117197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 921993680550665616078131 1382990520825998424117197)
            ·
              refine ⟨518621445309749409043949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1382990520825998424117197 518621445309749409043949)
              ·
                refine ⟨194483041991156028391481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 518621445309749409043949 194483041991156028391481)
                ·
                  refine ⟨145862281493367021293611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 194483041991156028391481 145862281493367021293611)
                  ·
                    rfl

theorem cell20_319574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 3, 3, 2].length) (baseStart_319574 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_319574 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_319574 prefixEnd_319574 := by exact prefixLift 319574
  have htrace : WordTrace (prefixWord ++ tailWord_319574) baseStart_319574 baseEnd_319574 := by
    simpa [prefixWord, tailWord_319574, baseEnd_319574] using wordTrace_append hprefix tailTrace_319574
  have hstable : (prefixWord ++ tailWord_319574).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319574).length < 2 ^ (prefixWord ++ tailWord_319574).sum := by decide
  have hdescent : baseEnd_319574 < baseStart_319574 := by decide
  rcases family_descends (prefixWord ++ tailWord_319574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319589 : List Nat := [1, 3, 1, 3, 2, 2, 8]
def baseStart_319589 : Nat := 118140960795 + 319589 * 2 ^ 59
def prefixEnd_319589 : Nat := 4983230072969 + 3 ^ 40 * 319589 * 2
def baseEnd_319589 : Nat := 16207680878010403977061

theorem tailTrace_319589 : CollatzResearch.WordTrace tailWord_319589 prefixEnd_319589 16207680878010403977061 := by
  unfold tailWord_319589
  simp only [CollatzResearch.WordTrace]
  refine ⟨11656368439191109300857821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7770912292794072867238547 11656368439191109300857821)
  ·
    refine ⟨4371138164696665987821683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11656368439191109300857821 4371138164696665987821683)
    ·
      refine ⟨6556707247044998981732525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4371138164696665987821683 6556707247044998981732525)
      ·
        refine ⟨2458765217641874618149697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6556707247044998981732525 2458765217641874618149697)
        ·
          refine ⟨1844073913231405963612273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2458765217641874618149697 1844073913231405963612273)
          ·
            refine ⟨1383055434923554472709205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1844073913231405963612273 1383055434923554472709205)
            ·
              refine ⟨16207680878010403977061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1383055434923554472709205 16207680878010403977061)
              ·
                rfl

theorem cell20_319589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 8].length) (baseStart_319589 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_319589 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_319589 prefixEnd_319589 := by exact prefixLift 319589
  have htrace : WordTrace (prefixWord ++ tailWord_319589) baseStart_319589 baseEnd_319589 := by
    simpa [prefixWord, tailWord_319589, baseEnd_319589] using wordTrace_append hprefix tailTrace_319589
  have hstable : (prefixWord ++ tailWord_319589).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319589).length < 2 ^ (prefixWord ++ tailWord_319589).sum := by decide
  have hdescent : baseEnd_319589 < baseStart_319589 := by decide
  rcases family_descends (prefixWord ++ tailWord_319589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319599 : List Nat := [1, 1, 2, 1, 3, 6, 1, 1, 4]
def baseStart_319599 : Nat := 118140960795 + 319599 * 2 ^ 59
def prefixEnd_319599 : Nat := 4983230072969 + 3 ^ 40 * 319599 * 2
def baseEnd_319599 : Nat := 145873692174578045460175

theorem tailTrace_319599 : CollatzResearch.WordTrace tailWord_319599 prefixEnd_319599 145873692174578045460175 := by
  unfold tailWord_319599
  simp only [CollatzResearch.WordTrace]
  refine ⟨11656733169154881008721851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7771155446103254005814567 11656733169154881008721851)
  ·
    refine ⟨17485099753732321513082777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11656733169154881008721851 17485099753732321513082777)
    ·
      refine ⟨13113824815299241134812083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17485099753732321513082777 13113824815299241134812083)
      ·
        refine ⟨19670737222948861702218125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13113824815299241134812083 19670737222948861702218125)
        ·
          refine ⟨7376526458605823138331797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19670737222948861702218125 7376526458605823138331797)
          ·
            refine ⟨345774677747147959609303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 7376526458605823138331797 345774677747147959609303)
            ·
              refine ⟨518662016620721939413955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 345774677747147959609303 518662016620721939413955)
              ·
                refine ⟨777993024931082909120933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 518662016620721939413955 777993024931082909120933)
                ·
                  refine ⟨145873692174578045460175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 777993024931082909120933 145873692174578045460175)
                  ·
                    rfl

theorem cell20_319599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 1, 1, 4].length) (baseStart_319599 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_319599 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_319599 prefixEnd_319599 := by exact prefixLift 319599
  have htrace : WordTrace (prefixWord ++ tailWord_319599) baseStart_319599 baseEnd_319599 := by
    simpa [prefixWord, tailWord_319599, baseEnd_319599] using wordTrace_append hprefix tailTrace_319599
  have hstable : (prefixWord ++ tailWord_319599).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319599).length < 2 ^ (prefixWord ++ tailWord_319599).sum := by decide
  have hdescent : baseEnd_319599 < baseStart_319599 := by decide
  rcases family_descends (prefixWord ++ tailWord_319599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319606 : List Nat := [5, 1, 1, 2, 1, 2, 1, 7]
def baseStart_319606 : Nat := 118140960795 + 319606 * 2 ^ 59
def prefixEnd_319606 : Nat := 4983230072969 + 3 ^ 40 * 319606 * 2
def baseEnd_319606 : Nat := 48625629055105710742271

theorem tailTrace_319606 : CollatzResearch.WordTrace tailWord_319606 prefixEnd_319606 48625629055105710742271 := by
  unfold tailWord_319606
  simp only [CollatzResearch.WordTrace]
  refine ⟨728561780008095075264167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7771325653419680802817781 728561780008095075264167)
  ·
    refine ⟨1092842670012142612896251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 728561780008095075264167 1092842670012142612896251)
    ·
      refine ⟨1639264005018213919344377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1092842670012142612896251 1639264005018213919344377)
      ·
        refine ⟨1229448003763660439508283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1639264005018213919344377 1229448003763660439508283)
        ·
          refine ⟨1844172005645490659262425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1229448003763660439508283 1844172005645490659262425)
          ·
            refine ⟨1383129004234117994446819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1844172005645490659262425 1383129004234117994446819)
            ·
              refine ⟨2074693506351176991670229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1383129004234117994446819 2074693506351176991670229)
              ·
                refine ⟨48625629055105710742271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2074693506351176991670229 48625629055105710742271)
                ·
                  rfl

theorem cell20_319606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 7].length) (baseStart_319606 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_319606 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_319606 prefixEnd_319606 := by exact prefixLift 319606
  have htrace : WordTrace (prefixWord ++ tailWord_319606) baseStart_319606 baseEnd_319606 := by
    simpa [prefixWord, tailWord_319606, baseEnd_319606] using wordTrace_append hprefix tailTrace_319606
  have hstable : (prefixWord ++ tailWord_319606).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319606).length < 2 ^ (prefixWord ++ tailWord_319606).sum := by decide
  have hdescent : baseEnd_319606 < baseStart_319606 := by decide
  rcases family_descends (prefixWord ++ tailWord_319606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319609 : List Nat := [1, 2, 1, 3, 4, 3, 2, 1, 3]
def baseStart_319609 : Nat := 118140960795 + 319609 * 2 ^ 59
def prefixEnd_319609 : Nat := 4983230072969 + 3 ^ 40 * 319609 * 2
def baseEnd_319609 : Nat := 145878256447062455126801

theorem tailTrace_319609 : CollatzResearch.WordTrace tailWord_319609 prefixEnd_319609 145878256447062455126801 := by
  unfold tailWord_319609
  simp only [CollatzResearch.WordTrace]
  refine ⟨11657097899118652716585881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7771398599412435144390587 11657097899118652716585881)
  ·
    refine ⟨8742823424338989537439411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11657097899118652716585881 8742823424338989537439411)
    ·
      refine ⟨13114235136508484306159117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8742823424338989537439411 13114235136508484306159117)
      ·
        refine ⟨4917838176190681614809669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13114235136508484306159117 4917838176190681614809669)
        ·
          refine ⟨922094658035752802776813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4917838176190681614809669 922094658035752802776813)
          ·
            refine ⟨345785496763407301041305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 922094658035752802776813 345785496763407301041305)
            ·
              refine ⟨259339122572555475780979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 345785496763407301041305 259339122572555475780979)
              ·
                refine ⟨389008683858833213671469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 259339122572555475780979 389008683858833213671469)
                ·
                  refine ⟨145878256447062455126801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 389008683858833213671469 145878256447062455126801)
                  ·
                    rfl

theorem cell20_319609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 2, 1, 3].length) (baseStart_319609 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_319609 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_319609 prefixEnd_319609 := by exact prefixLift 319609
  have htrace : WordTrace (prefixWord ++ tailWord_319609) baseStart_319609 baseEnd_319609 := by
    simpa [prefixWord, tailWord_319609, baseEnd_319609] using wordTrace_append hprefix tailTrace_319609
  have hstable : (prefixWord ++ tailWord_319609).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319609).length < 2 ^ (prefixWord ++ tailWord_319609).sum := by decide
  have hdescent : baseEnd_319609 < baseStart_319609 := by decide
  rcases family_descends (prefixWord ++ tailWord_319609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319620 : List Nat := [2, 3, 2, 1, 2, 1, 2, 1, 6]
def baseStart_319620 : Nat := 118140960795 + 319620 * 2 ^ 59
def prefixEnd_319620 : Nat := 4983230072969 + 3 ^ 40 * 319620 * 2
def baseEnd_319620 : Nat := 145883277146795305760089

theorem tailTrace_319620 : CollatzResearch.WordTrace tailWord_319620 prefixEnd_319620 145883277146795305760089 := by
  unfold tailWord_319620
  simp only [CollatzResearch.WordTrace]
  refine ⟨5828749551039400797618157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7771666068052534396824209 5828749551039400797618157)
  ·
    refine ⟨2185781081639775299106809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5828749551039400797618157 2185781081639775299106809)
    ·
      refine ⟨1639335811229831474330107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2185781081639775299106809 1639335811229831474330107)
      ·
        refine ⟨2459003716844747211495161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1639335811229831474330107 2459003716844747211495161)
        ·
          refine ⟨1844252787633560408621371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2459003716844747211495161 1844252787633560408621371)
          ·
            refine ⟨2766379181450340612932057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1844252787633560408621371 2766379181450340612932057)
            ·
              refine ⟨2074784386087755459699043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2766379181450340612932057 2074784386087755459699043)
              ·
                refine ⟨3112176579131633189548565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2074784386087755459699043 3112176579131633189548565)
                ·
                  refine ⟨145883277146795305760089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3112176579131633189548565 145883277146795305760089)
                  ·
                    rfl

theorem cell20_319620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 1, 6].length) (baseStart_319620 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_319620 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_319620 prefixEnd_319620 := by exact prefixLift 319620
  have htrace : WordTrace (prefixWord ++ tailWord_319620) baseStart_319620 baseEnd_319620 := by
    simpa [prefixWord, tailWord_319620, baseEnd_319620] using wordTrace_append hprefix tailTrace_319620
  have hstable : (prefixWord ++ tailWord_319620).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319620).length < 2 ^ (prefixWord ++ tailWord_319620).sum := by decide
  have hdescent : baseEnd_319620 < baseStart_319620 := by decide
  rcases family_descends (prefixWord ++ tailWord_319620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319637 : List Nat := [1, 3, 2, 1, 1, 1, 4, 5, 2]
def baseStart_319637 : Nat := 118140960795 + 319637 * 2 ^ 59
def prefixEnd_319637 : Nat := 4983230072969 + 3 ^ 40 * 319637 * 2
def baseEnd_319637 : Nat := 145891036410018802193353

theorem tailTrace_319637 : CollatzResearch.WordTrace tailWord_319637 prefixEnd_319637 145891036410018802193353 := by
  unfold tailWord_319637
  simp only [CollatzResearch.WordTrace]
  refine ⟨11658119143017213498605165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7772079428678142332403443 11658119143017213498605165)
  ·
    refine ⟨4371794678631455061976937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11658119143017213498605165 4371794678631455061976937)
    ·
      refine ⟨3278846008973591296482703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4371794678631455061976937 3278846008973591296482703)
      ·
        refine ⟨4918269013460386944724055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3278846008973591296482703 4918269013460386944724055)
        ·
          refine ⟨7377403520190580417086083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4918269013460386944724055 7377403520190580417086083)
          ·
            refine ⟨11066105280285870625629125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7377403520190580417086083 11066105280285870625629125)
            ·
              refine ⟨2074894740053600742305461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11066105280285870625629125 2074894740053600742305461)
              ·
                refine ⟨194521381880025069591137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2074894740053600742305461 194521381880025069591137)
                ·
                  refine ⟨145891036410018802193353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 194521381880025069591137 145891036410018802193353)
                  ·
                    rfl

theorem cell20_319637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 5, 2].length) (baseStart_319637 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_319637 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_319637 prefixEnd_319637 := by exact prefixLift 319637
  have htrace : WordTrace (prefixWord ++ tailWord_319637) baseStart_319637 baseEnd_319637 := by
    simpa [prefixWord, tailWord_319637, baseEnd_319637] using wordTrace_append hprefix tailTrace_319637
  have hstable : (prefixWord ++ tailWord_319637).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319637).length < 2 ^ (prefixWord ++ tailWord_319637).sum := by decide
  have hdescent : baseEnd_319637 < baseStart_319637 := by decide
  rcases family_descends (prefixWord ++ tailWord_319637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319650 : List Nat := [3, 3, 1, 3, 1, 3, 2, 2, 2]
def baseStart_319650 : Nat := 118140960795 + 319650 * 2 ^ 59
def prefixEnd_319650 : Nat := 4983230072969 + 3 ^ 40 * 319650 * 2
def baseEnd_319650 : Nat := 145896969964248534759967

theorem tailTrace_319650 : CollatzResearch.WordTrace tailWord_319650 prefixEnd_319650 145896969964248534759967 := by
  unfold tailWord_319650
  simp only [CollatzResearch.WordTrace]
  refine ⟨2914648322992529179707101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7772395527980077812552269 2914648322992529179707101)
  ·
    refine ⟨1092993121122198442390163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2914648322992529179707101 1092993121122198442390163)
    ·
      refine ⟨1639489681683297663585245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1092993121122198442390163 1639489681683297663585245)
      ·
        refine ⟨614808630631236623844467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1639489681683297663585245 614808630631236623844467)
        ·
          refine ⟨922212945946854935766701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 614808630631236623844467 922212945946854935766701)
          ·
            refine ⟨345829854730070600912513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 922212945946854935766701 345829854730070600912513)
            ·
              refine ⟨259372391047552950684385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 345829854730070600912513 259372391047552950684385)
              ·
                refine ⟨194529293285664713013289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 259372391047552950684385 194529293285664713013289)
                ·
                  refine ⟨145896969964248534759967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 194529293285664713013289 145896969964248534759967)
                  ·
                    rfl

theorem cell20_319650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 2, 2, 2].length) (baseStart_319650 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_319650 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_319650 prefixEnd_319650 := by exact prefixLift 319650
  have htrace : WordTrace (prefixWord ++ tailWord_319650) baseStart_319650 baseEnd_319650 := by
    simpa [prefixWord, tailWord_319650, baseEnd_319650] using wordTrace_append hprefix tailTrace_319650
  have hstable : (prefixWord ++ tailWord_319650).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319650).length < 2 ^ (prefixWord ++ tailWord_319650).sum := by decide
  have hdescent : baseEnd_319650 < baseStart_319650 := by decide
  rcases family_descends (prefixWord ++ tailWord_319650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319661 : List Nat := [1, 5, 2, 1, 2, 3, 1, 5]
def baseStart_319661 : Nat := 118140960795 + 319661 * 2 ^ 59
def prefixEnd_319661 : Nat := 4983230072969 + 3 ^ 40 * 319661 * 2
def baseEnd_319661 : Nat := 48633996887993795131085

theorem tailTrace_319661 : CollatzResearch.WordTrace tailWord_319661 prefixEnd_319661 48633996887993795131085 := by
  unfold tailWord_319661
  simp only [CollatzResearch.WordTrace]
  refine ⟨11658994494930265597478837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7772662996620177064985891 11658994494930265597478837)
  ·
    refine ⟨1093030733899712399763641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11658994494930265597478837 1093030733899712399763641)
    ·
      refine ⟨819773050424784299822731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1093030733899712399763641 819773050424784299822731)
      ·
        refine ⟨1229659575637176449734097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 819773050424784299822731 1229659575637176449734097)
        ·
          refine ⟨922244681727882337300573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1229659575637176449734097 922244681727882337300573)
          ·
            refine ⟨345841755647955876487715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 922244681727882337300573 345841755647955876487715)
            ·
              refine ⟨518762633471933814731573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 345841755647955876487715 518762633471933814731573)
              ·
                refine ⟨48633996887993795131085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 518762633471933814731573 48633996887993795131085)
                ·
                  rfl

theorem cell20_319661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 1, 5].length) (baseStart_319661 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_319661 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_319661 prefixEnd_319661 := by exact prefixLift 319661
  have htrace : WordTrace (prefixWord ++ tailWord_319661) baseStart_319661 baseEnd_319661 := by
    simpa [prefixWord, tailWord_319661, baseEnd_319661] using wordTrace_append hprefix tailTrace_319661
  have hstable : (prefixWord ++ tailWord_319661).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319661).length < 2 ^ (prefixWord ++ tailWord_319661).sum := by decide
  have hdescent : baseEnd_319661 < baseStart_319661 := by decide
  rcases family_descends (prefixWord ++ tailWord_319661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319702 : List Nat := [5, 2, 1, 2, 1, 3, 1, 2, 3]
def baseStart_319702 : Nat := 118140960795 + 319702 * 2 ^ 59
def prefixEnd_319702 : Nat := 4983230072969 + 3 ^ 40 * 319702 * 2
def baseEnd_319702 : Nat := 145920704181167465026421

theorem tailTrace_319702 : CollatzResearch.WordTrace tailWord_319702 prefixEnd_319702 145920704181167465026421 := by
  unfold tailWord_319702
  simp only [CollatzResearch.WordTrace]
  refine ⟨728780617986358099982585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7773659925187819733147573 728780617986358099982585)
  ·
    refine ⟨546585463489768574986939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 728780617986358099982585 546585463489768574986939)
    ·
      refine ⟨819878195234652862480409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 546585463489768574986939 819878195234652862480409)
      ·
        refine ⟨614908646425989646860307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 819878195234652862480409 614908646425989646860307)
        ·
          refine ⟨922362969638984470290461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 614908646425989646860307 922362969638984470290461)
          ·
            refine ⟨345886113614619176358923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 922362969638984470290461 345886113614619176358923)
            ·
              refine ⟨518829170421928764538385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 345886113614619176358923 518829170421928764538385)
              ·
                refine ⟨389121877816446573403789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 518829170421928764538385 389121877816446573403789)
                ·
                  refine ⟨145920704181167465026421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 389121877816446573403789 145920704181167465026421)
                  ·
                    rfl

theorem cell20_319702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_319702 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_319702 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_319702 prefixEnd_319702 := by exact prefixLift 319702
  have htrace : WordTrace (prefixWord ++ tailWord_319702) baseStart_319702 baseEnd_319702 := by
    simpa [prefixWord, tailWord_319702, baseEnd_319702] using wordTrace_append hprefix tailTrace_319702
  have hstable : (prefixWord ++ tailWord_319702).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319702).length < 2 ^ (prefixWord ++ tailWord_319702).sum := by decide
  have hdescent : baseEnd_319702 < baseStart_319702 := by decide
  rcases family_descends (prefixWord ++ tailWord_319702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319713 : List Nat := [1, 2, 3, 1, 3, 1, 1, 6, 2]
def baseStart_319713 : Nat := 118140960795 + 319713 * 2 ^ 59
def prefixEnd_319713 : Nat := 4983230072969 + 3 ^ 40 * 319713 * 2
def baseEnd_319713 : Nat := 145925724880900315659709

theorem tailTrace_319713 : CollatzResearch.WordTrace tailWord_319713 prefixEnd_319713 145925724880900315659709 := by
  unfold tailWord_319713
  simp only [CollatzResearch.WordTrace]
  refine ⟨11660891090741878478371793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7773927393827918985581195 11660891090741878478371793)
  ·
    refine ⟨8745668318056408858778845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11660891090741878478371793 8745668318056408858778845)
    ·
      refine ⟨3279625619271153322042067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8745668318056408858778845 3279625619271153322042067)
      ·
        refine ⟨4919438428906729983063101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3279625619271153322042067 4919438428906729983063101)
        ·
          refine ⟨1844789410840023743648663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4919438428906729983063101 1844789410840023743648663)
          ·
            refine ⟨2767184116260035615472995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1844789410840023743648663 2767184116260035615472995)
            ·
              refine ⟨4150776174390053423209493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2767184116260035615472995 4150776174390053423209493)
              ·
                refine ⟨194567633174533754212945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4150776174390053423209493 194567633174533754212945)
                ·
                  refine ⟨145925724880900315659709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 194567633174533754212945 145925724880900315659709)
                  ·
                    rfl

theorem cell20_319713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 6, 2].length) (baseStart_319713 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_319713 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_319713 prefixEnd_319713 := by exact prefixLift 319713
  have htrace : WordTrace (prefixWord ++ tailWord_319713) baseStart_319713 baseEnd_319713 := by
    simpa [prefixWord, tailWord_319713, baseEnd_319713] using wordTrace_append hprefix tailTrace_319713
  have hstable : (prefixWord ++ tailWord_319713).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319713).length < 2 ^ (prefixWord ++ tailWord_319713).sum := by decide
  have hdescent : baseEnd_319713 < baseStart_319713 := by decide
  rcases family_descends (prefixWord ++ tailWord_319713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319768 : List Nat := [2, 1, 2, 3, 1, 2, 5, 2, 2]
def baseStart_319768 : Nat := 118140960795 + 319768 * 2 ^ 59
def prefixEnd_319768 : Nat := 4983230072969 + 3 ^ 40 * 319768 * 2
def baseEnd_319768 : Nat := 145950828379564568826151

theorem tailTrace_319768 : CollatzResearch.WordTrace tailWord_319768 prefixEnd_319768 145950828379564568826151 := by
  unfold tailWord_319768
  simp only [CollatzResearch.WordTrace]
  refine ⟨5831448552771311435811979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7775264737028415247749305 5831448552771311435811979)
  ·
    refine ⟨8747172829156967153717969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5831448552771311435811979 8747172829156967153717969)
    ·
      refine ⟨6560379621867725365288477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8747172829156967153717969 6560379621867725365288477)
      ·
        refine ⟨2460142358200397011983179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6560379621867725365288477 2460142358200397011983179)
        ·
          refine ⟨3690213537300595517974769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2460142358200397011983179 3690213537300595517974769)
          ·
            refine ⟨2767660152975446638481077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3690213537300595517974769 2767660152975446638481077)
            ·
              refine ⟨259468139341448122357601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2767660152975446638481077 259468139341448122357601)
              ·
                refine ⟨194601104506086091768201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 259468139341448122357601 194601104506086091768201)
                ·
                  refine ⟨145950828379564568826151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 194601104506086091768201 145950828379564568826151)
                  ·
                    rfl

theorem cell20_319768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 5, 2, 2].length) (baseStart_319768 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_319768 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_319768 prefixEnd_319768 := by exact prefixLift 319768
  have htrace : WordTrace (prefixWord ++ tailWord_319768) baseStart_319768 baseEnd_319768 := by
    simpa [prefixWord, tailWord_319768, baseEnd_319768] using wordTrace_append hprefix tailTrace_319768
  have hstable : (prefixWord ++ tailWord_319768).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319768).length < 2 ^ (prefixWord ++ tailWord_319768).sum := by decide
  have hdescent : baseEnd_319768 < baseStart_319768 := by decide
  rcases family_descends (prefixWord ++ tailWord_319768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319779 : List Nat := [1, 1, 1, 4, 2, 2, 4, 5]
def baseStart_319779 : Nat := 118140960795 + 319779 * 2 ^ 59
def prefixEnd_319779 : Nat := 4983230072969 + 3 ^ 40 * 319779 * 2
def baseEnd_319779 : Nat := 48651949693099139819813

theorem tailTrace_319779 : CollatzResearch.WordTrace tailWord_319779 prefixEnd_319779 48651949693099139819813 := by
  unfold tailWord_319779
  simp only [CollatzResearch.WordTrace]
  refine ⟨11663298308502771750274391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7775532205668514500182927 11663298308502771750274391)
  ·
    refine ⟨17494947462754157625411587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11663298308502771750274391 17494947462754157625411587)
    ·
      refine ⟨26242421194131236438117381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17494947462754157625411587 26242421194131236438117381)
      ·
        refine ⟨4920453973899606832147009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26242421194131236438117381 4920453973899606832147009)
        ·
          refine ⟨3690340480424705124110257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4920453973899606832147009 3690340480424705124110257)
          ·
            refine ⟨2767755360318528843082693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3690340480424705124110257 2767755360318528843082693)
            ·
              refine ⟨518954130059724158078005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2767755360318528843082693 518954130059724158078005)
              ·
                refine ⟨48651949693099139819813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 518954130059724158078005 48651949693099139819813)
                ·
                  rfl

theorem cell20_319779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 4, 5].length) (baseStart_319779 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_319779 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_319779 prefixEnd_319779 := by exact prefixLift 319779
  have htrace : WordTrace (prefixWord ++ tailWord_319779) baseStart_319779 baseEnd_319779 := by
    simpa [prefixWord, tailWord_319779, baseEnd_319779] using wordTrace_append hprefix tailTrace_319779
  have hstable : (prefixWord ++ tailWord_319779).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319779).length < 2 ^ (prefixWord ++ tailWord_319779).sum := by decide
  have hdescent : baseEnd_319779 < baseStart_319779 := by decide
  rcases family_descends (prefixWord ++ tailWord_319779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319796 : List Nat := [2, 5, 1, 1, 1, 2, 2, 6]
def baseStart_319796 : Nat := 118140960795 + 319796 * 2 ^ 59
def prefixEnd_319796 : Nat := 4983230072969 + 3 ^ 40 * 319796 * 2
def baseEnd_319796 : Nat := 48654536114173638630901

theorem tailTrace_319796 : CollatzResearch.WordTrace tailWord_319796 prefixEnd_319796 48654536114173638630901 := by
  unfold tailWord_319796
  simp only [CollatzResearch.WordTrace]
  refine ⟨5831959174720591826821621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7775945566294122435762161 5831959174720591826821621)
  ·
    refine ⟨546746172630055483764527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5831959174720591826821621 546746172630055483764527)
    ·
      refine ⟨820119258945083225646791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 546746172630055483764527 820119258945083225646791)
      ·
        refine ⟨1230178888417624838470187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 820119258945083225646791 1230178888417624838470187)
        ·
          refine ⟨1845268332626437257705281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1230178888417624838470187 1845268332626437257705281)
          ·
            refine ⟨1383951249469827943278961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1845268332626437257705281 1383951249469827943278961)
            ·
              refine ⟨1037963437102370957459221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1383951249469827943278961 1037963437102370957459221)
              ·
                refine ⟨48654536114173638630901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1037963437102370957459221 48654536114173638630901)
                ·
                  rfl

theorem cell20_319796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 6].length) (baseStart_319796 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_319796 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_319796 prefixEnd_319796 := by exact prefixLift 319796
  have htrace : WordTrace (prefixWord ++ tailWord_319796) baseStart_319796 baseEnd_319796 := by
    simpa [prefixWord, tailWord_319796, baseEnd_319796] using wordTrace_append hprefix tailTrace_319796
  have hstable : (prefixWord ++ tailWord_319796).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319796).length < 2 ^ (prefixWord ++ tailWord_319796).sum := by decide
  have hdescent : baseEnd_319796 < baseStart_319796 := by decide
  rcases family_descends (prefixWord ++ tailWord_319796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319848 : List Nat := [2, 1, 4, 2, 2, 1, 1, 1, 6]
def baseStart_319848 : Nat := 118140960795 + 319848 * 2 ^ 59
def prefixEnd_319848 : Nat := 4983230072969 + 3 ^ 40 * 319848 * 2
def baseEnd_319848 : Nat := 145987342559439846159157

theorem tailTrace_319848 : CollatzResearch.WordTrace tailWord_319848 prefixEnd_319848 145987342559439846159157 := by
  unfold tailWord_319848
  simp only [CollatzResearch.WordTrace]
  refine ⟨5832907472626398267268099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7777209963501864356357465 5832907472626398267268099)
  ·
    refine ⟨8749361208939597400902149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5832907472626398267268099 8749361208939597400902149)
    ·
      refine ⟨1640505226676174512669153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8749361208939597400902149 1640505226676174512669153)
      ·
        refine ⟨1230378920007130884501865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1640505226676174512669153 1230378920007130884501865)
        ·
          refine ⟨922784190005348163376399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1230378920007130884501865 922784190005348163376399)
          ·
            refine ⟨1384176285008022245064599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 922784190005348163376399 1384176285008022245064599)
            ·
              refine ⟨2076264427512033367596899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1384176285008022245064599 2076264427512033367596899)
              ·
                refine ⟨3114396641268050051395349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2076264427512033367596899 3114396641268050051395349)
                ·
                  refine ⟨145987342559439846159157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3114396641268050051395349 145987342559439846159157)
                  ·
                    rfl

theorem cell20_319848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 1, 6].length) (baseStart_319848 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_319848 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_319848 prefixEnd_319848 := by exact prefixLift 319848
  have htrace : WordTrace (prefixWord ++ tailWord_319848) baseStart_319848 baseEnd_319848 := by
    simpa [prefixWord, tailWord_319848, baseEnd_319848] using wordTrace_append hprefix tailTrace_319848
  have hstable : (prefixWord ++ tailWord_319848).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319848).length < 2 ^ (prefixWord ++ tailWord_319848).sum := by decide
  have hdescent : baseEnd_319848 < baseStart_319848 := by decide
  rcases family_descends (prefixWord ++ tailWord_319848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319875 : List Nat := [1, 1, 1, 3, 7, 1, 1, 2, 3]
def baseStart_319875 : Nat := 118140960795 + 319875 * 2 ^ 59
def prefixEnd_319875 : Nat := 4983230072969 + 3 ^ 40 * 319875 * 2
def baseEnd_319875 : Nat := 145999666095147752259047

theorem tailTrace_319875 : CollatzResearch.WordTrace tailWord_319875 prefixEnd_319875 145999666095147752259047 := by
  unfold tailWord_319875
  simp only [CollatzResearch.WordTrace]
  refine ⟨11666799716154980145769079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7777866477436653430512719 11666799716154980145769079)
  ·
    refine ⟨17500199574232470218653619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11666799716154980145769079 17500199574232470218653619)
    ·
      refine ⟨26250299361348705327980429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17500199574232470218653619 26250299361348705327980429)
      ·
        refine ⟨9843862260505764497992661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26250299361348705327980429 9843862260505764497992661)
        ·
          refine ⟨230715521730603855421703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 9843862260505764497992661 230715521730603855421703)
          ·
            refine ⟨346073282595905783132555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 230715521730603855421703 346073282595905783132555)
            ·
              refine ⟨519109923893858674698833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 346073282595905783132555 519109923893858674698833)
              ·
                refine ⟨389332442920394006024125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 519109923893858674698833 389332442920394006024125)
                ·
                  refine ⟨145999666095147752259047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 389332442920394006024125 145999666095147752259047)
                  ·
                    rfl

theorem cell20_319875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 1, 2, 3].length) (baseStart_319875 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_319875 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_319875 prefixEnd_319875 := by exact prefixLift 319875
  have htrace : WordTrace (prefixWord ++ tailWord_319875) baseStart_319875 baseEnd_319875 := by
    simpa [prefixWord, tailWord_319875, baseEnd_319875] using wordTrace_append hprefix tailTrace_319875
  have hstable : (prefixWord ++ tailWord_319875).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319875).length < 2 ^ (prefixWord ++ tailWord_319875).sum := by decide
  have hdescent : baseEnd_319875 < baseStart_319875 := by decide
  rcases family_descends (prefixWord ++ tailWord_319875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319882 : List Nat := [3, 1, 2, 5, 1, 1, 2, 1, 4]
def baseStart_319882 : Nat := 118140960795 + 319882 * 2 ^ 59
def prefixEnd_319882 : Nat := 4983230072969 + 3 ^ 40 * 319882 * 2
def baseEnd_319882 : Nat := 146002861085886839025685

theorem tailTrace_319882 : CollatzResearch.WordTrace tailWord_319882 prefixEnd_319882 146002861085886839025685 := by
  unfold tailWord_319882
  simp only [CollatzResearch.WordTrace]
  refine ⟨2916763756782405085318475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7778036684753080227515933 2916763756782405085318475)
  ·
    refine ⟨4375145635173607627977713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2916763756782405085318475 4375145635173607627977713)
    ·
      refine ⟨3281359226380205720983285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4375145635173607627977713 3281359226380205720983285)
      ·
        refine ⟨307627427473144286342183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3281359226380205720983285 307627427473144286342183)
        ·
          refine ⟨461441141209716429513275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 307627427473144286342183 461441141209716429513275)
          ·
            refine ⟨692161711814574644269913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 461441141209716429513275 692161711814574644269913)
            ·
              refine ⟨519121283860930983202435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 692161711814574644269913 519121283860930983202435)
              ·
                refine ⟨778681925791396474803653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 519121283860930983202435 778681925791396474803653)
                ·
                  refine ⟨146002861085886839025685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 778681925791396474803653 146002861085886839025685)
                  ·
                    rfl

theorem cell20_319882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 2, 1, 4].length) (baseStart_319882 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_319882 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_319882 prefixEnd_319882 := by exact prefixLift 319882
  have htrace : WordTrace (prefixWord ++ tailWord_319882) baseStart_319882 baseEnd_319882 := by
    simpa [prefixWord, tailWord_319882, baseEnd_319882] using wordTrace_append hprefix tailTrace_319882
  have hstable : (prefixWord ++ tailWord_319882).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319882).length < 2 ^ (prefixWord ++ tailWord_319882).sum := by decide
  have hdescent : baseEnd_319882 < baseStart_319882 := by decide
  rcases family_descends (prefixWord ++ tailWord_319882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319948 : List Nat := [2, 2, 1, 4, 3, 1, 2, 5]
def baseStart_319948 : Nat := 118140960795 + 319948 * 2 ^ 59
def prefixEnd_319948 : Nat := 4983230072969 + 3 ^ 40 * 319948 * 2
def baseEnd_319948 : Nat := 48677661761427980941805

theorem tailTrace_319948 : CollatzResearch.WordTrace tailWord_319948 prefixEnd_319948 48677661761427980941805 := by
  unfold tailWord_319948
  simp only [CollatzResearch.WordTrace]
  refine ⟨5834731122445256806588249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7779641496593675742117665 5834731122445256806588249)
  ·
    refine ⟨4376048341833942604941187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5834731122445256806588249 4376048341833942604941187)
    ·
      refine ⟨6564072512750913907411781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4376048341833942604941187 6564072512750913907411781)
      ·
        refine ⟨1230763596140796357639709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6564072512750913907411781 1230763596140796357639709)
        ·
          refine ⟨461536348552798634114891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1230763596140796357639709 461536348552798634114891)
          ·
            refine ⟨692304522829197951172337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 461536348552798634114891 692304522829197951172337)
            ·
              refine ⟨519228392121898463379253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 692304522829197951172337 519228392121898463379253)
              ·
                refine ⟨48677661761427980941805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 519228392121898463379253 48677661761427980941805)
                ·
                  rfl

theorem cell20_319948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 2, 5].length) (baseStart_319948 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_319948 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_319948 prefixEnd_319948 := by exact prefixLift 319948
  have htrace : WordTrace (prefixWord ++ tailWord_319948) baseStart_319948 baseEnd_319948 := by
    simpa [prefixWord, tailWord_319948, baseEnd_319948] using wordTrace_append hprefix tailTrace_319948
  have hstable : (prefixWord ++ tailWord_319948).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319948).length < 2 ^ (prefixWord ++ tailWord_319948).sum := by decide
  have hdescent : baseEnd_319948 < baseStart_319948 := by decide
  rcases family_descends (prefixWord ++ tailWord_319948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319986 : List Nat := [3, 2, 1, 4, 3, 7]
def baseStart_319986 : Nat := 118140960795 + 319986 * 2 ^ 59
def prefixEnd_319986 : Nat := 4983230072969 + 3 ^ 40 * 319986 * 2
def baseEnd_319986 : Nat := 5409271463693507391059

theorem tailTrace_319986 : CollatzResearch.WordTrace tailWord_319986 prefixEnd_319986 5409271463693507391059 := by
  unfold tailWord_319986
  simp only [CollatzResearch.WordTrace]
  refine ⟨2917712054688211525764953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7780565479168564068706541 2917712054688211525764953)
  ·
    refine ⟨2188284041016158644323715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2917712054688211525764953 2188284041016158644323715)
    ·
      refine ⟨3282426061524237966485573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2188284041016158644323715 3282426061524237966485573)
      ·
        refine ⟨615454886535794618716045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3282426061524237966485573 615454886535794618716045)
        ·
          refine ⟨230795582450922982018517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 615454886535794618716045 230795582450922982018517)
          ·
            refine ⟨5409271463693507391059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 230795582450922982018517 5409271463693507391059)
            ·
              rfl

theorem cell20_319986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 7].length) (baseStart_319986 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_319986 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_319986 prefixEnd_319986 := by exact prefixLift 319986
  have htrace : WordTrace (prefixWord ++ tailWord_319986) baseStart_319986 baseEnd_319986 := by
    simpa [prefixWord, tailWord_319986, baseEnd_319986] using wordTrace_append hprefix tailTrace_319986
  have hstable : (prefixWord ++ tailWord_319986).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319986).length < 2 ^ (prefixWord ++ tailWord_319986).sum := by decide
  have hdescent : baseEnd_319986 < baseStart_319986 := by decide
  rcases family_descends (prefixWord ++ tailWord_319986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319989 : List Nat := [1, 3, 5, 1, 2, 1, 2, 2, 3]
def baseStart_319989 : Nat := 118140960795 + 319989 * 2 ^ 59
def prefixEnd_319989 : Nat := 4983230072969 + 3 ^ 40 * 319989 * 2
def baseEnd_319989 : Nat := 146051698801470022458581

theorem tailTrace_319989 : CollatzResearch.WordTrace tailWord_319989 prefixEnd_319989 146051698801470022458581 := by
  unfold tailWord_319989
  simp only [CollatzResearch.WordTrace]
  refine ⟨11670957637741977615419021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7780638425161318410279347 11670957637741977615419021)
  ·
    refine ⟨4376609114153241605782133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11670957637741977615419021 4376609114153241605782133)
    ·
      refine ⟨410307104451866400542075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4376609114153241605782133 410307104451866400542075)
      ·
        refine ⟨615460656677799600813113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 410307104451866400542075 615460656677799600813113)
        ·
          refine ⟨461595492508349700609835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 615460656677799600813113 461595492508349700609835)
          ·
            refine ⟨692393238762524550914753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 461595492508349700609835 692393238762524550914753)
            ·
              refine ⟨519294929071893413186065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 692393238762524550914753 519294929071893413186065)
              ·
                refine ⟨389471196803920059889549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 519294929071893413186065 389471196803920059889549)
                ·
                  refine ⟨146051698801470022458581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 389471196803920059889549 146051698801470022458581)
                  ·
                    rfl

theorem cell20_319989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 2, 2, 3].length) (baseStart_319989 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_319989 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_319989 prefixEnd_319989 := by exact prefixLift 319989
  have htrace : WordTrace (prefixWord ++ tailWord_319989) baseStart_319989 baseEnd_319989 := by
    simpa [prefixWord, tailWord_319989, baseEnd_319989] using wordTrace_append hprefix tailTrace_319989
  have hstable : (prefixWord ++ tailWord_319989).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319989).length < 2 ^ (prefixWord ++ tailWord_319989).sum := by decide
  have hdescent : baseEnd_319989 < baseStart_319989 := by decide
  rcases family_descends (prefixWord ++ tailWord_319989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320006 : List Nat := [6, 2, 1, 1, 1, 1, 2, 3, 3]
def baseStart_320006 : Nat := 118140960795 + 320006 * 2 ^ 59
def prefixEnd_320006 : Nat := 4983230072969 + 3 ^ 40 * 320006 * 2
def baseEnd_320006 : Nat := 146059458064693518891845

theorem tailTrace_320006 : CollatzResearch.WordTrace tailWord_320006 prefixEnd_320006 146059458064693518891845 := by
  unfold tailWord_320006
  simp only [CollatzResearch.WordTrace]
  refine ⟨364736802458762172462121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 7781051785786926345858581 364736802458762172462121)
  ·
    refine ⟨273552601844071629346591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 364736802458762172462121 273552601844071629346591)
    ·
      refine ⟨410328902766107444019887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273552601844071629346591 410328902766107444019887)
      ·
        refine ⟨615493354149161166029831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 410328902766107444019887 615493354149161166029831)
        ·
          refine ⟨923240031223741749044747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 615493354149161166029831 923240031223741749044747)
          ·
            refine ⟨1384860046835612623567121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 923240031223741749044747 1384860046835612623567121)
            ·
              refine ⟨1038645035126709467675341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1384860046835612623567121 1038645035126709467675341)
              ·
                refine ⟨389491888172516050378253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1038645035126709467675341 389491888172516050378253)
                ·
                  refine ⟨146059458064693518891845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 389491888172516050378253 146059458064693518891845)
                  ·
                    rfl

theorem cell20_320006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_320006 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_320006 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_320006 prefixEnd_320006 := by exact prefixLift 320006
  have htrace : WordTrace (prefixWord ++ tailWord_320006) baseStart_320006 baseEnd_320006 := by
    simpa [prefixWord, tailWord_320006, baseEnd_320006] using wordTrace_append hprefix tailTrace_320006
  have hstable : (prefixWord ++ tailWord_320006).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320006).length < 2 ^ (prefixWord ++ tailWord_320006).sum := by decide
  have hdescent : baseEnd_320006 < baseStart_320006 := by decide
  rcases family_descends (prefixWord ++ tailWord_320006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320024 : List Nat := [2, 1, 2, 3, 3, 2, 3, 4]
def baseStart_320024 : Nat := 118140960795 + 320024 * 2 ^ 59
def prefixEnd_320024 : Nat := 4983230072969 + 3 ^ 40 * 320024 * 2
def baseEnd_320024 : Nat := 48689224585055152097257

theorem tailTrace_320024 : CollatzResearch.WordTrace tailWord_320024 prefixEnd_320024 48689224585055152097257 := by
  unfold tailWord_320024
  simp only [CollatzResearch.WordTrace]
  refine ⟨5836117096307589296471563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7781489461743452395295417 5836117096307589296471563)
  ·
    refine ⟨8754175644461383944707345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5836117096307589296471563 8754175644461383944707345)
    ·
      refine ⟨6565631733346037958530509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8754175644461383944707345 6565631733346037958530509)
      ·
        refine ⟨2462111900004764234448941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6565631733346037958530509 2462111900004764234448941)
        ·
          refine ⟨923291962501786587918353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2462111900004764234448941 923291962501786587918353)
          ·
            refine ⟨692468971876339940938765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 923291962501786587918353 692468971876339940938765)
            ·
              refine ⟨259675864453627477852037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 692468971876339940938765 259675864453627477852037)
              ·
                refine ⟨48689224585055152097257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 259675864453627477852037 48689224585055152097257)
                ·
                  rfl

theorem cell20_320024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 3, 4].length) (baseStart_320024 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_320024 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_320024 prefixEnd_320024 := by exact prefixLift 320024
  have htrace : WordTrace (prefixWord ++ tailWord_320024) baseStart_320024 baseEnd_320024 := by
    simpa [prefixWord, tailWord_320024, baseEnd_320024] using wordTrace_append hprefix tailTrace_320024
  have hstable : (prefixWord ++ tailWord_320024).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320024).length < 2 ^ (prefixWord ++ tailWord_320024).sum := by decide
  have hdescent : baseEnd_320024 < baseStart_320024 := by decide
  rcases family_descends (prefixWord ++ tailWord_320024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320121 : List Nat := [1, 2, 1, 3, 3, 3, 2, 5]
def baseStart_320121 : Nat := 118140960795 + 320121 * 2 ^ 59
def prefixEnd_320121 : Nat := 4983230072969 + 3 ^ 40 * 320121 * 2
def baseEnd_320121 : Nat := 48703982399421410019347

theorem tailTrace_320121 : CollatzResearch.WordTrace tailWord_320121 prefixEnd_320121 48703982399421410019347 := by
  unfold tailWord_320121
  simp only [CollatzResearch.WordTrace]
  refine ⟨11675772073263764159224217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7783848048842509439482811 11675772073263764159224217)
  ·
    refine ⟨8756829054947823119418163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11675772073263764159224217 8756829054947823119418163)
    ·
      refine ⟨13135243582421734679127245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8756829054947823119418163 13135243582421734679127245)
      ·
        refine ⟨4925716343408150504672717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13135243582421734679127245 4925716343408150504672717)
        ·
          refine ⟨1847143628778056439252269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4925716343408150504672717 1847143628778056439252269)
          ·
            refine ⟨692678860791771164719601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1847143628778056439252269 692678860791771164719601)
            ·
              refine ⟨519509145593828373539701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 692678860791771164719601 519509145593828373539701)
              ·
                refine ⟨48703982399421410019347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 519509145593828373539701 48703982399421410019347)
                ·
                  rfl

theorem cell20_320121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 2, 5].length) (baseStart_320121 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_320121 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_320121 prefixEnd_320121 := by exact prefixLift 320121
  have htrace : WordTrace (prefixWord ++ tailWord_320121) baseStart_320121 baseEnd_320121 := by
    simpa [prefixWord, tailWord_320121, baseEnd_320121] using wordTrace_append hprefix tailTrace_320121
  have hstable : (prefixWord ++ tailWord_320121).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320121).length < 2 ^ (prefixWord ++ tailWord_320121).sum := by decide
  have hdescent : baseEnd_320121 < baseStart_320121 := by decide
  rcases family_descends (prefixWord ++ tailWord_320121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320135 : List Nat := [1, 1, 4, 2, 1, 2, 2, 1, 6]
def baseStart_320135 : Nat := 118140960795 + 320135 * 2 ^ 59
def prefixEnd_320135 : Nat := 4983230072969 + 3 ^ 40 * 320135 * 2
def baseEnd_320135 : Nat := 146118337179742403591317

theorem tailTrace_320135 : CollatzResearch.WordTrace tailWord_320135 prefixEnd_320135 146118337179742403591317 := by
  unfold tailWord_320135
  simp only [CollatzResearch.WordTrace]
  refine ⟨11676282695213044550233859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7784188463475363033489239 11676282695213044550233859)
  ·
    refine ⟨17514424042819566825350789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11676282695213044550233859 17514424042819566825350789)
    ·
      refine ⟨3283954508028668779753273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17514424042819566825350789 3283954508028668779753273)
      ·
        refine ⟨2462965881021501584814955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3283954508028668779753273 2462965881021501584814955)
        ·
          refine ⟨3694448821532252377222433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2462965881021501584814955 3694448821532252377222433)
          ·
            refine ⟨2770836616149189282916825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3694448821532252377222433 2770836616149189282916825)
            ·
              refine ⟨2078127462111891962187619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2770836616149189282916825 2078127462111891962187619)
              ·
                refine ⟨3117191193167837943281429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2078127462111891962187619 3117191193167837943281429)
                ·
                  refine ⟨146118337179742403591317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3117191193167837943281429 146118337179742403591317)
                  ·
                    rfl

theorem cell20_320135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 1, 6].length) (baseStart_320135 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_320135 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_320135 prefixEnd_320135 := by exact prefixLift 320135
  have htrace : WordTrace (prefixWord ++ tailWord_320135) baseStart_320135 baseEnd_320135 := by
    simpa [prefixWord, tailWord_320135, baseEnd_320135] using wordTrace_append hprefix tailTrace_320135
  have hstable : (prefixWord ++ tailWord_320135).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320135).length < 2 ^ (prefixWord ++ tailWord_320135).sum := by decide
  have hdescent : baseEnd_320135 < baseStart_320135 := by decide
  rcases family_descends (prefixWord ++ tailWord_320135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320187 : List Nat := [1, 1, 1, 1, 1, 2, 3, 1, 9]
def baseStart_320187 : Nat := 118140960795 + 320187 * 2 ^ 59
def prefixEnd_320187 : Nat := 4983230072969 + 3 ^ 40 * 320187 * 2
def baseEnd_320187 : Nat := 146142071396661333857771

theorem tailTrace_320187 : CollatzResearch.WordTrace tailWord_320187 prefixEnd_320187 146142071396661333857771 := by
  unfold tailWord_320187
  simp only [CollatzResearch.WordTrace]
  refine ⟨11678179291024657431126815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7785452860683104954084543 11678179291024657431126815)
  ·
    refine ⟨17517268936536986146690223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11678179291024657431126815 17517268936536986146690223)
    ·
      refine ⟨26275903404805479220035335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17517268936536986146690223 26275903404805479220035335)
      ·
        refine ⟨39413855107208218830053003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26275903404805479220035335 39413855107208218830053003)
        ·
          refine ⟨59120782660812328245079505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39413855107208218830053003 59120782660812328245079505)
          ·
            refine ⟨44340586995609246183809629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59120782660812328245079505 44340586995609246183809629)
            ·
              refine ⟨16627720123353467318928611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44340586995609246183809629 16627720123353467318928611)
              ·
                refine ⟨24941580185030200978392917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16627720123353467318928611 24941580185030200978392917)
                ·
                  refine ⟨146142071396661333857771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 24941580185030200978392917 146142071396661333857771)
                  ·
                    rfl

theorem cell20_320187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 9].length) (baseStart_320187 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_320187 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_320187 prefixEnd_320187 := by exact prefixLift 320187
  have htrace : WordTrace (prefixWord ++ tailWord_320187) baseStart_320187 baseEnd_320187 := by
    simpa [prefixWord, tailWord_320187, baseEnd_320187] using wordTrace_append hprefix tailTrace_320187
  have hstable : (prefixWord ++ tailWord_320187).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320187).length < 2 ^ (prefixWord ++ tailWord_320187).sum := by decide
  have hdescent : baseEnd_320187 < baseStart_320187 := by decide
  rcases family_descends (prefixWord ++ tailWord_320187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320190 : List Nat := [4, 2, 1, 1, 2, 1, 3, 2, 4]
def baseStart_320190 : Nat := 118140960795 + 320190 * 2 ^ 59
def prefixEnd_320190 : Nat := 4983230072969 + 3 ^ 40 * 320190 * 2
def baseEnd_320190 : Nat := 146143440678406656757759

theorem tailTrace_320190 : CollatzResearch.WordTrace tailWord_320190 prefixEnd_320190 146143440678406656757759 := by
  unfold tailWord_320190
  simp only [CollatzResearch.WordTrace]
  refine ⟨1459786088751723617935753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7785525806675859295657349 1459786088751723617935753)
  ·
    refine ⟨1094839566563792713451815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1459786088751723617935753 1094839566563792713451815)
    ·
      refine ⟨1642259349845689070177723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1094839566563792713451815 1642259349845689070177723)
      ·
        refine ⟨2463389024768533605266585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1642259349845689070177723 2463389024768533605266585)
        ·
          refine ⟨1847541768576400203949939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2463389024768533605266585 1847541768576400203949939)
          ·
            refine ⟨2771312652864600305924909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1847541768576400203949939 2771312652864600305924909)
            ·
              refine ⟨1039242244824225114721841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2771312652864600305924909 1039242244824225114721841)
              ·
                refine ⟨779431683618168836041381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1039242244824225114721841 779431683618168836041381)
                ·
                  refine ⟨146143440678406656757759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 779431683618168836041381 146143440678406656757759)
                  ·
                    rfl

theorem cell20_320190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_320190 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_320190 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_320190 prefixEnd_320190 := by exact prefixLift 320190
  have htrace : WordTrace (prefixWord ++ tailWord_320190) baseStart_320190 baseEnd_320190 := by
    simpa [prefixWord, tailWord_320190, baseEnd_320190] using wordTrace_append hprefix tailTrace_320190
  have hstable : (prefixWord ++ tailWord_320190).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320190).length < 2 ^ (prefixWord ++ tailWord_320190).sum := by decide
  have hdescent : baseEnd_320190 < baseStart_320190 := by decide
  rcases family_descends (prefixWord ++ tailWord_320190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320218 : List Nat := [3, 1, 1, 2, 2, 2, 9]
def baseStart_320218 : Nat := 118140960795 + 320218 * 2 ^ 59
def prefixEnd_320218 : Nat := 4983230072969 + 3 ^ 40 * 320218 * 2
def baseEnd_320218 : Nat := 16239580071262555980479

theorem tailTrace_320218 : CollatzResearch.WordTrace tailWord_320218 prefixEnd_320218 16239580071262555980479 := by
  unfold tailWord_320218
  simp only [CollatzResearch.WordTrace]
  refine ⟨2919827488478087431376327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7786206635941566483670205 2919827488478087431376327)
  ·
    refine ⟨4379741232717131147064491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2919827488478087431376327 4379741232717131147064491)
    ·
      refine ⟨6569611849075696720596737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4379741232717131147064491 6569611849075696720596737)
      ·
        refine ⟨4927208886806772540447553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6569611849075696720596737 4927208886806772540447553)
        ·
          refine ⟨3695406665105079405335665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4927208886806772540447553 3695406665105079405335665)
          ·
            refine ⟨2771554998828809554001749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3695406665105079405335665 2771554998828809554001749)
            ·
              refine ⟨16239580071262555980479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2771554998828809554001749 16239580071262555980479)
              ·
                rfl

theorem cell20_320218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 9].length) (baseStart_320218 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_320218 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_320218 prefixEnd_320218 := by exact prefixLift 320218
  have htrace : WordTrace (prefixWord ++ tailWord_320218) baseStart_320218 baseEnd_320218 := by
    simpa [prefixWord, tailWord_320218, baseEnd_320218] using wordTrace_append hprefix tailTrace_320218
  have hstable : (prefixWord ++ tailWord_320218).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320218).length < 2 ^ (prefixWord ++ tailWord_320218).sum := by decide
  have hdescent : baseEnd_320218 < baseStart_320218 := by decide
  rcases family_descends (prefixWord ++ tailWord_320218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320228 : List Nat := [2, 3, 1, 1, 1, 5, 2, 1, 4]
def baseStart_320228 : Nat := 118140960795 + 320228 * 2 ^ 59
def prefixEnd_320228 : Nat := 4983230072969 + 3 ^ 40 * 320228 * 2
def baseEnd_320228 : Nat := 146160784913847413490937

theorem tailTrace_320228 : CollatzResearch.WordTrace tailWord_320228 prefixEnd_320228 146160784913847413490937 := by
  unfold tailWord_320228
  simp only [CollatzResearch.WordTrace]
  refine ⟨5839837341938060716684669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7786449789250747622246225 5839837341938060716684669)
  ·
    refine ⟨2189939003226772768756751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5839837341938060716684669 2189939003226772768756751)
    ·
      refine ⟨3284908504840159153135127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2189939003226772768756751 3284908504840159153135127)
      ·
        refine ⟨4927362757260238729702691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3284908504840159153135127 4927362757260238729702691)
        ·
          refine ⟨7391044135890358094554037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4927362757260238729702691 7391044135890358094554037)
          ·
            refine ⟨692910387739721071364441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7391044135890358094554037 692910387739721071364441)
            ·
              refine ⟨519682790804790803523331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 692910387739721071364441 519682790804790803523331)
              ·
                refine ⟨779524186207186205284997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 519682790804790803523331 779524186207186205284997)
                ·
                  refine ⟨146160784913847413490937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 779524186207186205284997 146160784913847413490937)
                  ·
                    rfl

theorem cell20_320228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 2, 1, 4].length) (baseStart_320228 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_320228 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_320228 prefixEnd_320228 := by exact prefixLift 320228
  have htrace : WordTrace (prefixWord ++ tailWord_320228) baseStart_320228 baseEnd_320228 := by
    simpa [prefixWord, tailWord_320228, baseEnd_320228] using wordTrace_append hprefix tailTrace_320228
  have hstable : (prefixWord ++ tailWord_320228).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320228).length < 2 ^ (prefixWord ++ tailWord_320228).sum := by decide
  have hdescent : baseEnd_320228 < baseStart_320228 := by decide
  rcases family_descends (prefixWord ++ tailWord_320228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320238 : List Nat := [4, 1, 2, 1, 1, 4, 3, 1, 3]
def baseStart_320238 : Nat := 118140960795 + 320238 * 2 ^ 59
def prefixEnd_320238 : Nat := 4983230072969 + 3 ^ 40 * 320238 * 2
def baseEnd_320238 : Nat := 146165349186331823157563

theorem tailTrace_320238 : CollatzResearch.WordTrace tailWord_320238 prefixEnd_320238 146165349186331823157563 := by
  unfold tailWord_320238
  simp only [CollatzResearch.WordTrace]
  refine ⟨1460004926729986642654171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7786692942559928760822245 1460004926729986642654171)
  ·
    refine ⟨2190007390094979963981257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1460004926729986642654171 2190007390094979963981257)
    ·
      refine ⟨1642505542571234972985943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2190007390094979963981257 1642505542571234972985943)
      ·
        refine ⟨2463758313856852459478915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1642505542571234972985943 2463758313856852459478915)
        ·
          refine ⟨3695637470785278689218373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2463758313856852459478915 3695637470785278689218373)
          ·
            refine ⟨692932025772239754228445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3695637470785278689218373 692932025772239754228445)
            ·
              refine ⟨259849509664589907835667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 692932025772239754228445 259849509664589907835667)
              ·
                refine ⟨389774264496884861753501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 259849509664589907835667 389774264496884861753501)
                ·
                  refine ⟨146165349186331823157563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 389774264496884861753501 146165349186331823157563)
                  ·
                    rfl

theorem cell20_320238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 3, 1, 3].length) (baseStart_320238 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_320238 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_320238 prefixEnd_320238 := by exact prefixLift 320238
  have htrace : WordTrace (prefixWord ++ tailWord_320238) baseStart_320238 baseEnd_320238 := by
    simpa [prefixWord, tailWord_320238, baseEnd_320238] using wordTrace_append hprefix tailTrace_320238
  have hstable : (prefixWord ++ tailWord_320238).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320238).length < 2 ^ (prefixWord ++ tailWord_320238).sum := by decide
  have hdescent : baseEnd_320238 < baseStart_320238 := by decide
  rcases family_descends (prefixWord ++ tailWord_320238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320252 : List Nat := [2, 2, 2, 1, 3, 4, 2, 4]
def baseStart_320252 : Nat := 118140960795 + 320252 * 2 ^ 59
def prefixEnd_320252 : Nat := 4983230072969 + 3 ^ 40 * 320252 * 2
def baseEnd_320252 : Nat := 48723913055936665563613

theorem tailTrace_320252 : CollatzResearch.WordTrace tailWord_320252 prefixEnd_320252 48723913055936665563613 := by
  unfold tailWord_320252
  simp only [CollatzResearch.WordTrace]
  refine ⟨5840275017894586766121505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7787033357192782354828673 5840275017894586766121505)
  ·
    refine ⟨4380206263420940074591129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5840275017894586766121505 4380206263420940074591129)
    ·
      refine ⟨3285154697565705055943347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4380206263420940074591129 3285154697565705055943347)
      ·
        refine ⟨4927732046348557583915021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3285154697565705055943347 4927732046348557583915021)
        ·
          refine ⟨1847899517380709093968133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4927732046348557583915021 1847899517380709093968133)
          ·
            refine ⟨346481159508882955119025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1847899517380709093968133 346481159508882955119025)
            ·
              refine ⟨259860869631662216339269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 346481159508882955119025 259860869631662216339269)
              ·
                refine ⟨48723913055936665563613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 259860869631662216339269 48723913055936665563613)
                ·
                  rfl

theorem cell20_320252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 2, 4].length) (baseStart_320252 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_320252 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_320252 prefixEnd_320252 := by exact prefixLift 320252
  have htrace : WordTrace (prefixWord ++ tailWord_320252) baseStart_320252 baseEnd_320252 := by
    simpa [prefixWord, tailWord_320252, baseEnd_320252] using wordTrace_append hprefix tailTrace_320252
  have hstable : (prefixWord ++ tailWord_320252).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320252).length < 2 ^ (prefixWord ++ tailWord_320252).sum := by decide
  have hdescent : baseEnd_320252 < baseStart_320252 := by decide
  rcases family_descends (prefixWord ++ tailWord_320252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320280 : List Nat := [2, 1, 2, 3, 1, 1, 1, 6, 3]
def baseStart_320280 : Nat := 118140960795 + 320280 * 2 ^ 59
def prefixEnd_320280 : Nat := 4983230072969 + 3 ^ 40 * 320280 * 2
def baseEnd_320280 : Nat := 146184519130766343757391

theorem tailTrace_320280 : CollatzResearch.WordTrace tailWord_320280 prefixEnd_320280 146184519130766343757391 := by
  unfold tailWord_320280
  simp only [CollatzResearch.WordTrace]
  refine ⟨5840785639843867157131147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7787714186458489542841529 5840785639843867157131147)
  ·
    refine ⟨8761178459765800735696721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5840785639843867157131147 8761178459765800735696721)
    ·
      refine ⟨6570883844824350551772541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8761178459765800735696721 6570883844824350551772541)
      ·
        refine ⟨2464081441809131456914703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6570883844824350551772541 2464081441809131456914703)
        ·
          refine ⟨3696122162713697185372055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2464081441809131456914703 3696122162713697185372055)
          ·
            refine ⟨5544183244070545778058083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3696122162713697185372055 5544183244070545778058083)
            ·
              refine ⟨8316274866105818667087125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5544183244070545778058083 8316274866105818667087125)
              ·
                refine ⟨389825384348710250019709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8316274866105818667087125 389825384348710250019709)
                ·
                  refine ⟨146184519130766343757391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 389825384348710250019709 146184519130766343757391)
                  ·
                    rfl

theorem cell20_320280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 6, 3].length) (baseStart_320280 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_320280 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_320280 prefixEnd_320280 := by exact prefixLift 320280
  have htrace : WordTrace (prefixWord ++ tailWord_320280) baseStart_320280 baseEnd_320280 := by
    simpa [prefixWord, tailWord_320280, baseEnd_320280] using wordTrace_append hprefix tailTrace_320280
  have hstable : (prefixWord ++ tailWord_320280).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320280).length < 2 ^ (prefixWord ++ tailWord_320280).sum := by decide
  have hdescent : baseEnd_320280 < baseStart_320280 := by decide
  rcases family_descends (prefixWord ++ tailWord_320280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320332 : List Nat := [2, 2, 1, 3, 3, 9]
def baseStart_320332 : Nat := 118140960795 + 320332 * 2 ^ 59
def prefixEnd_320332 : Nat := 4983230072969 + 3 ^ 40 * 320332 * 2
def baseEnd_320332 : Nat := 5415120494358713852735

theorem tailTrace_320332 : CollatzResearch.WordTrace tailWord_320332 prefixEnd_320332 5415120494358713852735 := by
  unfold tailWord_320332
  simp only [CollatzResearch.WordTrace]
  refine ⟨5841733937749673597577625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7788978583666231463436833 5841733937749673597577625)
  ·
    refine ⟨4381300453312255198183219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5841733937749673597577625 4381300453312255198183219)
    ·
      refine ⟨6571950679968382797274829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4381300453312255198183219 6571950679968382797274829)
      ·
        refine ⟨2464481504988143548978061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6571950679968382797274829 2464481504988143548978061)
        ·
          refine ⟨924180564370553830866773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2464481504988143548978061 924180564370553830866773)
          ·
            refine ⟨5415120494358713852735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 924180564370553830866773 5415120494358713852735)
            ·
              rfl

theorem cell20_320332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 9].length) (baseStart_320332 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_320332 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_320332 prefixEnd_320332 := by exact prefixLift 320332
  have htrace : WordTrace (prefixWord ++ tailWord_320332) baseStart_320332 baseEnd_320332 := by
    simpa [prefixWord, tailWord_320332, baseEnd_320332] using wordTrace_append hprefix tailTrace_320332
  have hstable : (prefixWord ++ tailWord_320332).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320332).length < 2 ^ (prefixWord ++ tailWord_320332).sum := by decide
  have hdescent : baseEnd_320332 < baseStart_320332 := by decide
  rcases family_descends (prefixWord ++ tailWord_320332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320339 : List Nat := [1, 1, 1, 2, 1, 1, 3, 5, 5]
def baseStart_320339 : Nat := 118140960795 + 320339 * 2 ^ 59
def prefixEnd_320339 : Nat := 4983230072969 + 3 ^ 40 * 320339 * 2
def baseEnd_320339 : Nat := 146211448338424360790483

theorem tailTrace_320339 : CollatzResearch.WordTrace tailWord_320339 prefixEnd_320339 146211448338424360790483 := by
  unfold tailWord_320339
  simp only [CollatzResearch.WordTrace]
  refine ⟨11683723186473987390660071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7789148790982658260440047 11683723186473987390660071)
  ·
    refine ⟨17525584779710981085990107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11683723186473987390660071 17525584779710981085990107)
    ·
      refine ⟨26288377169566471628985161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17525584779710981085990107 26288377169566471628985161)
      ·
        refine ⟨19716282877174853721738871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26288377169566471628985161 19716282877174853721738871)
        ·
          refine ⟨29574424315762280582608307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19716282877174853721738871 29574424315762280582608307)
          ·
            refine ⟨44361636473643420873912461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29574424315762280582608307 44361636473643420873912461)
            ·
              refine ⟨16635613677616282827717173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44361636473643420873912461 16635613677616282827717173)
              ·
                refine ⟨1559588782276526515098485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16635613677616282827717173 1559588782276526515098485)
                ·
                  refine ⟨146211448338424360790483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1559588782276526515098485 146211448338424360790483)
                  ·
                    rfl

theorem cell20_320339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 5, 5].length) (baseStart_320339 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_320339 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_320339 prefixEnd_320339 := by exact prefixLift 320339
  have htrace : WordTrace (prefixWord ++ tailWord_320339) baseStart_320339 baseEnd_320339 := by
    simpa [prefixWord, tailWord_320339, baseEnd_320339] using wordTrace_append hprefix tailTrace_320339
  have hstable : (prefixWord ++ tailWord_320339).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320339).length < 2 ^ (prefixWord ++ tailWord_320339).sum := by decide
  have hdescent : baseEnd_320339 < baseStart_320339 := by decide
  rcases family_descends (prefixWord ++ tailWord_320339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320370 : List Nat := [3, 2, 1, 2, 1, 1, 2, 8]
def baseStart_320370 : Nat := 118140960795 + 320370 * 2 ^ 59
def prefixEnd_320370 : Nat := 4983230072969 + 3 ^ 40 * 320370 * 2
def baseEnd_320370 : Nat := 48741865861042010252341

theorem tailTrace_320370 : CollatzResearch.WordTrace tailWord_320370 prefixEnd_320370 48741865861042010252341 := by
  unfold tailWord_320370
  simp only [CollatzResearch.WordTrace]
  refine ⟨2921213462340419921259641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7789902566241119790025709 2921213462340419921259641)
  ·
    refine ⟨2190910096755314940944731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2921213462340419921259641 2190910096755314940944731)
    ·
      refine ⟨3286365145132972411417097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2190910096755314940944731 3286365145132972411417097)
      ·
        refine ⟨2464773858849729308562823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3286365145132972411417097 2464773858849729308562823)
        ·
          refine ⟨3697160788274593962844235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2464773858849729308562823 3697160788274593962844235)
          ·
            refine ⟨5545741182411890944266353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3697160788274593962844235 5545741182411890944266353)
            ·
              refine ⟨4159305886808918208199765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5545741182411890944266353 4159305886808918208199765)
              ·
                refine ⟨48741865861042010252341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4159305886808918208199765 48741865861042010252341)
                ·
                  rfl

theorem cell20_320370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 8].length) (baseStart_320370 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_320370 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_320370 prefixEnd_320370 := by exact prefixLift 320370
  have htrace : WordTrace (prefixWord ++ tailWord_320370) baseStart_320370 baseEnd_320370 := by
    simpa [prefixWord, tailWord_320370, baseEnd_320370] using wordTrace_append hprefix tailTrace_320370
  have hstable : (prefixWord ++ tailWord_320370).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320370).length < 2 ^ (prefixWord ++ tailWord_320370).sum := by decide
  have hdescent : baseEnd_320370 < baseStart_320370 := by decide
  rcases family_descends (prefixWord ++ tailWord_320370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320386 : List Nat := [3, 4, 2, 2, 1, 2, 1, 2, 3]
def baseStart_320386 : Nat := 118140960795 + 320386 * 2 ^ 59
def prefixEnd_320386 : Nat := 4983230072969 + 3 ^ 40 * 320386 * 2
def baseEnd_320386 : Nat := 146232900419101086223625

theorem tailTrace_320386 : CollatzResearch.WordTrace tailWord_320386 prefixEnd_320386 146232900419101086223625 := by
  unfold tailWord_320386
  simp only [CollatzResearch.WordTrace]
  refine ⟨2921359354325928604405253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7790291611535809611747341 2921359354325928604405253)
  ·
    refine ⟨547754878936111613325985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2921359354325928604405253 547754878936111613325985)
    ·
      refine ⟨410816159202083709994489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 547754878936111613325985 410816159202083709994489)
      ·
        refine ⟨308112119401562782495867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 410816159202083709994489 308112119401562782495867)
        ·
          refine ⟨462168179102344173743801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 308112119401562782495867 462168179102344173743801)
          ·
            refine ⟨346626134326758130307851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 462168179102344173743801 346626134326758130307851)
            ·
              refine ⟨519939201490137195461777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 346626134326758130307851 519939201490137195461777)
              ·
                refine ⟨389954401117602896596333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 519939201490137195461777 389954401117602896596333)
                ·
                  refine ⟨146232900419101086223625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 389954401117602896596333 146232900419101086223625)
                  ·
                    rfl

theorem cell20_320386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_320386 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_320386 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_320386 prefixEnd_320386 := by exact prefixLift 320386
  have htrace : WordTrace (prefixWord ++ tailWord_320386) baseStart_320386 baseEnd_320386 := by
    simpa [prefixWord, tailWord_320386, baseEnd_320386] using wordTrace_append hprefix tailTrace_320386
  have hstable : (prefixWord ++ tailWord_320386).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320386).length < 2 ^ (prefixWord ++ tailWord_320386).sum := by decide
  have hdescent : baseEnd_320386 < baseStart_320386 := by decide
  rcases family_descends (prefixWord ++ tailWord_320386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320418 : List Nat := [3, 3, 1, 2, 2, 1, 2, 2, 4]
def baseStart_320418 : Nat := 118140960795 + 320418 * 2 ^ 59
def prefixEnd_320418 : Nat := 4983230072969 + 3 ^ 40 * 320418 * 2
def baseEnd_320418 : Nat := 146247506091051197156827

theorem tailTrace_320418 : CollatzResearch.WordTrace tailWord_320418 prefixEnd_320418 146247506091051197156827 := by
  unfold tailWord_320418
  simp only [CollatzResearch.WordTrace]
  refine ⟨2921651138296945970696477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7791069702125189255190605 2921651138296945970696477)
  ·
    refine ⟨1095619176861354739011179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2921651138296945970696477 1095619176861354739011179)
    ·
      refine ⟨1643428765292032108516769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1095619176861354739011179 1643428765292032108516769)
      ·
        refine ⟨1232571573969024081387577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1643428765292032108516769 1232571573969024081387577)
        ·
          refine ⟨924428680476768061040683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1232571573969024081387577 924428680476768061040683)
          ·
            refine ⟨1386643020715152091561025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 924428680476768061040683 1386643020715152091561025)
            ·
              refine ⟨1039982265536364068670769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1386643020715152091561025 1039982265536364068670769)
              ·
                refine ⟨779986699152273051503077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1039982265536364068670769 779986699152273051503077)
                ·
                  refine ⟨146247506091051197156827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 779986699152273051503077 146247506091051197156827)
                  ·
                    rfl

theorem cell20_320418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_320418 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_320418 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_320418 prefixEnd_320418 := by exact prefixLift 320418
  have htrace : WordTrace (prefixWord ++ tailWord_320418) baseStart_320418 baseEnd_320418 := by
    simpa [prefixWord, tailWord_320418, baseEnd_320418] using wordTrace_append hprefix tailTrace_320418
  have hstable : (prefixWord ++ tailWord_320418).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320418).length < 2 ^ (prefixWord ++ tailWord_320418).sum := by decide
  have hdescent : baseEnd_320418 < baseStart_320418 := by decide
  rcases family_descends (prefixWord ++ tailWord_320418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320438 : List Nat := [5, 1, 4, 1, 1, 2, 6]
def baseStart_320438 : Nat := 118140960795 + 320438 * 2 ^ 59
def prefixEnd_320438 : Nat := 4983230072969 + 3 ^ 40 * 320438 * 2
def baseEnd_320438 : Nat := 16250737181780001832231

theorem tailTrace_320438 : CollatzResearch.WordTrace tailWord_320438 prefixEnd_320438 16250737181780001832231 := by
  unfold tailWord_320438
  simp only [CollatzResearch.WordTrace]
  refine ⟨730458375819707956157123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7791556008743551532342645 730458375819707956157123)
  ·
    refine ⟨1095687563729561934235685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 730458375819707956157123 1095687563729561934235685)
    ·
      refine ⟨205441418199292862669191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1095687563729561934235685 205441418199292862669191)
      ·
        refine ⟨308162127298939294003787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205441418199292862669191 308162127298939294003787)
        ·
          refine ⟨462243190948408941005681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 308162127298939294003787 462243190948408941005681)
          ·
            refine ⟨346682393211306705754261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 462243190948408941005681 346682393211306705754261)
            ·
              refine ⟨16250737181780001832231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 346682393211306705754261 16250737181780001832231)
              ·
                rfl

theorem cell20_320438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 6].length) (baseStart_320438 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_320438 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_320438 prefixEnd_320438 := by exact prefixLift 320438
  have htrace : WordTrace (prefixWord ++ tailWord_320438) baseStart_320438 baseEnd_320438 := by
    simpa [prefixWord, tailWord_320438, baseEnd_320438] using wordTrace_append hprefix tailTrace_320438
  have hstable : (prefixWord ++ tailWord_320438).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320438).length < 2 ^ (prefixWord ++ tailWord_320438).sum := by decide
  have hdescent : baseEnd_320438 < baseStart_320438 := by decide
  rcases family_descends (prefixWord ++ tailWord_320438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320452 : List Nat := [2, 3, 3, 3, 1, 2, 1, 1, 4]
def baseStart_320452 : Nat := 118140960795 + 320452 * 2 ^ 59
def prefixEnd_320452 : Nat := 4983230072969 + 3 ^ 40 * 320452 * 2
def baseEnd_320452 : Nat := 146263024617498190023355

theorem tailTrace_320452 : CollatzResearch.WordTrace tailWord_320452 prefixEnd_320452 146263024617498190023355 := by
  unfold tailWord_320452
  simp only [CollatzResearch.WordTrace]
  refine ⟨5843922317532303844761805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7791896423376405126349073 5843922317532303844761805)
  ·
    refine ⟨2191470869074613941785677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5843922317532303844761805 2191470869074613941785677)
    ·
      refine ⟨821801575902980228169629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2191470869074613941785677 821801575902980228169629)
      ·
        refine ⟨308175590963617585563611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 821801575902980228169629 308175590963617585563611)
        ·
          refine ⟨462263386445426378345417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 308175590963617585563611 462263386445426378345417)
          ·
            refine ⟨346697539834069783759063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 462263386445426378345417 346697539834069783759063)
            ·
              refine ⟨520046309751104675638595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 346697539834069783759063 520046309751104675638595)
              ·
                refine ⟨780069464626657013457893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 520046309751104675638595 780069464626657013457893)
                ·
                  refine ⟨146263024617498190023355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 780069464626657013457893 146263024617498190023355)
                  ·
                    rfl

theorem cell20_320452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 1, 1, 4].length) (baseStart_320452 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_320452 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_320452 prefixEnd_320452 := by exact prefixLift 320452
  have htrace : WordTrace (prefixWord ++ tailWord_320452) baseStart_320452 baseEnd_320452 := by
    simpa [prefixWord, tailWord_320452, baseEnd_320452] using wordTrace_append hprefix tailTrace_320452
  have hstable : (prefixWord ++ tailWord_320452).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320452).length < 2 ^ (prefixWord ++ tailWord_320452).sum := by decide
  have hdescent : baseEnd_320452 < baseStart_320452 := by decide
  rcases family_descends (prefixWord ++ tailWord_320452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320466 : List Nat := [3, 2, 2, 3, 1, 1, 4, 1, 3]
def baseStart_320466 : Nat := 118140960795 + 320466 * 2 ^ 59
def prefixEnd_320466 : Nat := 4983230072969 + 3 ^ 40 * 320466 * 2
def baseEnd_320466 : Nat := 146269414598976363556631

theorem tailTrace_320466 : CollatzResearch.WordTrace tailWord_320466 prefixEnd_320466 146269414598976363556631 := by
  unfold tailWord_320466
  simp only [CollatzResearch.WordTrace]
  refine ⟨2922088814253472020133313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7792236838009258720355501 2922088814253472020133313)
  ·
    refine ⟨2191566610690104015099985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2922088814253472020133313 2191566610690104015099985)
    ·
      refine ⟨1643674958017578011324989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2191566610690104015099985 1643674958017578011324989)
      ·
        refine ⟨616378109256591754246871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1643674958017578011324989 616378109256591754246871)
        ·
          refine ⟨924567163884887631370307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 616378109256591754246871 924567163884887631370307)
          ·
            refine ⟨1386850745827331447055461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 924567163884887631370307 1386850745827331447055461)
            ·
              refine ⟨260034514842624646322899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1386850745827331447055461 260034514842624646322899)
              ·
                refine ⟨390051772263936969484349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 260034514842624646322899 390051772263936969484349)
                ·
                  refine ⟨146269414598976363556631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 390051772263936969484349 146269414598976363556631)
                  ·
                    rfl

theorem cell20_320466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 4, 1, 3].length) (baseStart_320466 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_320466 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_320466 prefixEnd_320466 := by exact prefixLift 320466
  have htrace : WordTrace (prefixWord ++ tailWord_320466) baseStart_320466 baseEnd_320466 := by
    simpa [prefixWord, tailWord_320466, baseEnd_320466] using wordTrace_append hprefix tailTrace_320466
  have hstable : (prefixWord ++ tailWord_320466).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320466).length < 2 ^ (prefixWord ++ tailWord_320466).sum := by decide
  have hdescent : baseEnd_320466 < baseStart_320466 := by decide
  rcases family_descends (prefixWord ++ tailWord_320466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320501 : List Nat := [1, 3, 5, 2, 9]
def baseStart_320501 : Nat := 118140960795 + 320501 * 2 ^ 59
def prefixEnd_320501 : Nat := 4983230072969 + 3 ^ 40 * 320501 * 2
def baseEnd_320501 : Nat := 1805992463613232066541

theorem tailTrace_320501 : CollatzResearch.WordTrace tailWord_320501 prefixEnd_320501 1805992463613232066541 := by
  unfold tailWord_320501
  simp only [CollatzResearch.WordTrace]
  refine ⟨11689631811887089058057357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7793087874591392705371571 11689631811887089058057357)
  ·
    refine ⟨4383611929457658396771509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11689631811887089058057357 4383611929457658396771509)
    ·
      refine ⟨410963618386655474697329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4383611929457658396771509 410963618386655474697329)
      ·
        refine ⟨308222713789991606022997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 410963618386655474697329 308222713789991606022997)
        ·
          refine ⟨1805992463613232066541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 308222713789991606022997 1805992463613232066541)
          ·
            rfl

theorem cell20_320501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 9].length) (baseStart_320501 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_320501 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_320501 prefixEnd_320501 := by exact prefixLift 320501
  have htrace : WordTrace (prefixWord ++ tailWord_320501) baseStart_320501 baseEnd_320501 := by
    simpa [prefixWord, tailWord_320501, baseEnd_320501] using wordTrace_append hprefix tailTrace_320501
  have hstable : (prefixWord ++ tailWord_320501).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320501).length < 2 ^ (prefixWord ++ tailWord_320501).sum := by decide
  have hdescent : baseEnd_320501 < baseStart_320501 := by decide
  rcases family_descends (prefixWord ++ tailWord_320501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320508 : List Nat := [2, 2, 2, 1, 2, 3, 1, 4, 3]
def baseStart_320508 : Nat := 118140960795 + 320508 * 2 ^ 59
def prefixEnd_320508 : Nat := 4983230072969 + 3 ^ 40 * 320508 * 2
def baseEnd_320508 : Nat := 146288584543410884156459

theorem tailTrace_320508 : CollatzResearch.WordTrace tailWord_320508 prefixEnd_320508 146288584543410884156459 := by
  unfold tailWord_320508
  simp only [CollatzResearch.WordTrace]
  refine ⟨5844943561430864626781089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7793258081907819502374785 5844943561430864626781089)
  ·
    refine ⟨4383707671073148470085817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5844943561430864626781089 4383707671073148470085817)
    ·
      refine ⟨3287780753304861352564363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4383707671073148470085817 3287780753304861352564363)
      ·
        refine ⟨4931671129957292028846545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3287780753304861352564363 4931671129957292028846545)
        ·
          refine ⟨3698753347467969021634909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4931671129957292028846545 3698753347467969021634909)
          ·
            refine ⟨1387032505300488383113091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3698753347467969021634909 1387032505300488383113091)
            ·
              refine ⟨2080548757950732574669637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1387032505300488383113091 2080548757950732574669637)
              ·
                refine ⟨390102892115762357750557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2080548757950732574669637 390102892115762357750557)
                ·
                  refine ⟨146288584543410884156459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 390102892115762357750557 146288584543410884156459)
                  ·
                    rfl

theorem cell20_320508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 4, 3].length) (baseStart_320508 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_320508 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_320508 prefixEnd_320508 := by exact prefixLift 320508
  have htrace : WordTrace (prefixWord ++ tailWord_320508) baseStart_320508 baseEnd_320508 := by
    simpa [prefixWord, tailWord_320508, baseEnd_320508] using wordTrace_append hprefix tailTrace_320508
  have hstable : (prefixWord ++ tailWord_320508).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320508).length < 2 ^ (prefixWord ++ tailWord_320508).sum := by decide
  have hdescent : baseEnd_320508 < baseStart_320508 := by decide
  rcases family_descends (prefixWord ++ tailWord_320508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320514 : List Nat := [3, 4, 1, 3, 2, 1, 1, 5]
def baseStart_320514 : Nat := 118140960795 + 320514 * 2 ^ 59
def prefixEnd_320514 : Nat := 4983230072969 + 3 ^ 40 * 320514 * 2
def baseEnd_320514 : Nat := 48763774368967176652145

theorem tailTrace_320514 : CollatzResearch.WordTrace tailWord_320514 prefixEnd_320514 48763774368967176652145 := by
  unfold tailWord_320514
  simp only [CollatzResearch.WordTrace]
  refine ⟨2922526490209998069570149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7793403973893328185520397 2922526490209998069570149)
  ·
    refine ⟨547973716914374638044403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2922526490209998069570149 547973716914374638044403)
    ·
      refine ⟨821960575371561957066605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 547973716914374638044403 821960575371561957066605)
      ·
        refine ⟨308235215764335733899977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 821960575371561957066605 308235215764335733899977)
        ·
          refine ⟨231176411823251800424983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 308235215764335733899977 231176411823251800424983)
          ·
            refine ⟨346764617734877700637475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 231176411823251800424983 346764617734877700637475)
            ·
              refine ⟨520146926602316550956213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 346764617734877700637475 520146926602316550956213)
              ·
                refine ⟨48763774368967176652145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 520146926602316550956213 48763774368967176652145)
                ·
                  rfl

theorem cell20_320514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 1, 5].length) (baseStart_320514 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_320514 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_320514 prefixEnd_320514 := by exact prefixLift 320514
  have htrace : WordTrace (prefixWord ++ tailWord_320514) baseStart_320514 baseEnd_320514 := by
    simpa [prefixWord, tailWord_320514, baseEnd_320514] using wordTrace_append hprefix tailTrace_320514
  have hstable : (prefixWord ++ tailWord_320514).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320514).length < 2 ^ (prefixWord ++ tailWord_320514).sum := by decide
  have hdescent : baseEnd_320514 < baseStart_320514 := by decide
  rcases family_descends (prefixWord ++ tailWord_320514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320570 : List Nat := [3, 1, 1, 1, 3, 1, 4, 4, 2]
def baseStart_320570 : Nat := 118140960795 + 320570 * 2 ^ 59
def prefixEnd_320570 : Nat := 4983230072969 + 3 ^ 40 * 320570 * 2
def baseEnd_320570 : Nat := 146316883032814224089539

theorem tailTrace_320570 : CollatzResearch.WordTrace tailWord_320570 prefixEnd_320570 146316883032814224089539 := by
  unfold tailWord_320570
  simp only [CollatzResearch.WordTrace]
  refine ⟨2923037112159278460579791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7794765632424742561546109 2923037112159278460579791)
  ·
    refine ⟨4384555668238917690869687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2923037112159278460579791 4384555668238917690869687)
    ·
      refine ⟨6576833502358376536304531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4384555668238917690869687 6576833502358376536304531)
      ·
        refine ⟨9865250253537564804456797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6576833502358376536304531 9865250253537564804456797)
        ·
          refine ⟨3699468845076586801671299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9865250253537564804456797 3699468845076586801671299)
          ·
            refine ⟨5549203267614880202506949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3699468845076586801671299 5549203267614880202506949)
            ·
              refine ⟨1040475612677790037970053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5549203267614880202506949 1040475612677790037970053)
              ·
                refine ⟨195089177377085632119385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1040475612677790037970053 195089177377085632119385)
                ·
                  refine ⟨146316883032814224089539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 195089177377085632119385 146316883032814224089539)
                  ·
                    rfl

theorem cell20_320570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 4, 2].length) (baseStart_320570 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_320570 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_320570 prefixEnd_320570 := by exact prefixLift 320570
  have htrace : WordTrace (prefixWord ++ tailWord_320570) baseStart_320570 baseEnd_320570 := by
    simpa [prefixWord, tailWord_320570, baseEnd_320570] using wordTrace_append hprefix tailTrace_320570
  have hstable : (prefixWord ++ tailWord_320570).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320570).length < 2 ^ (prefixWord ++ tailWord_320570).sum := by decide
  have hdescent : baseEnd_320570 < baseStart_320570 := by decide
  rcases family_descends (prefixWord ++ tailWord_320570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320594 : List Nat := [3, 2, 2, 1, 3, 3, 2, 4]
def baseStart_320594 : Nat := 118140960795 + 320594 * 2 ^ 59
def prefixEnd_320594 : Nat := 4983230072969 + 3 ^ 40 * 320594 * 2
def baseEnd_320594 : Nat := 48775945762258935763147

theorem tailTrace_320594 : CollatzResearch.WordTrace tailWord_320594 prefixEnd_320594 48775945762258935763147 := by
  unfold tailWord_320594
  simp only [CollatzResearch.WordTrace]
  refine ⟨2923255950137541485298209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7795349200366777294128557 2923255950137541485298209)
  ·
    refine ⟨2192441962603156113973657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2923255950137541485298209 2192441962603156113973657)
    ·
      refine ⟨1644331471952367085480243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2192441962603156113973657 1644331471952367085480243)
      ·
        refine ⟨2466497207928550628220365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1644331471952367085480243 2466497207928550628220365)
        ·
          refine ⟨924936452973206485582637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2466497207928550628220365 924936452973206485582637)
          ·
            refine ⟨346851169864952432093489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 924936452973206485582637 346851169864952432093489)
            ·
              refine ⟨260138377398714324070117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 346851169864952432093489 260138377398714324070117)
              ·
                refine ⟨48775945762258935763147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 260138377398714324070117 48775945762258935763147)
                ·
                  rfl

theorem cell20_320594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 2, 4].length) (baseStart_320594 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_320594 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_320594 prefixEnd_320594 := by exact prefixLift 320594
  have htrace : WordTrace (prefixWord ++ tailWord_320594) baseStart_320594 baseEnd_320594 := by
    simpa [prefixWord, tailWord_320594, baseEnd_320594] using wordTrace_append hprefix tailTrace_320594
  have hstable : (prefixWord ++ tailWord_320594).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320594).length < 2 ^ (prefixWord ++ tailWord_320594).sum := by decide
  have hdescent : baseEnd_320594 < baseStart_320594 := by decide
  rcases family_descends (prefixWord ++ tailWord_320594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320622 : List Nat := [4, 1, 2, 2, 1, 2, 2, 1, 5]
def baseStart_320622 : Nat := 118140960795 + 320622 * 2 ^ 59
def prefixEnd_320622 : Nat := 4983230072969 + 3 ^ 40 * 320622 * 2
def baseEnd_320622 : Nat := 146340617249733154355993

theorem tailTrace_320622 : CollatzResearch.WordTrace tailWord_320622 prefixEnd_320622 146340617249733154355993 := by
  unfold tailWord_320622
  simp only [CollatzResearch.WordTrace]
  refine ⟨1461755630556090840401515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7796030029632484482141413 1461755630556090840401515)
  ·
    refine ⟨2192633445834136260602273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1461755630556090840401515 2192633445834136260602273)
    ·
      refine ⟨1644475084375602195451705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2192633445834136260602273 1644475084375602195451705)
      ·
        refine ⟨1233356313281701646588779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1644475084375602195451705 1233356313281701646588779)
        ·
          refine ⟨1850034469922552469883169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1233356313281701646588779 1850034469922552469883169)
          ·
            refine ⟨1387525852441914352412377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1850034469922552469883169 1387525852441914352412377)
            ·
              refine ⟨1040644389331435764309283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1387525852441914352412377 1040644389331435764309283)
              ·
                refine ⟨1560966583997153646463925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1040644389331435764309283 1560966583997153646463925)
                ·
                  refine ⟨146340617249733154355993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1560966583997153646463925 146340617249733154355993)
                  ·
                    rfl

theorem cell20_320622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 1, 5].length) (baseStart_320622 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_320622 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_320622 prefixEnd_320622 := by exact prefixLift 320622
  have htrace : WordTrace (prefixWord ++ tailWord_320622) baseStart_320622 baseEnd_320622 := by
    simpa [prefixWord, tailWord_320622, baseEnd_320622] using wordTrace_append hprefix tailTrace_320622
  have hstable : (prefixWord ++ tailWord_320622).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320622).length < 2 ^ (prefixWord ++ tailWord_320622).sum := by decide
  have hdescent : baseEnd_320622 < baseStart_320622 := by decide
  rcases family_descends (prefixWord ++ tailWord_320622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320636 : List Nat := [2, 2, 2, 1, 1, 3, 4, 5]
def baseStart_320636 : Nat := 118140960795 + 320636 * 2 ^ 59
def prefixEnd_320636 : Nat := 4983230072969 + 3 ^ 40 * 320636 * 2
def baseEnd_320636 : Nat := 48782335743737109296423

theorem tailTrace_320636 : CollatzResearch.WordTrace tailWord_320636 prefixEnd_320636 48782335743737109296423 := by
  unfold tailWord_320636
  simp only [CollatzResearch.WordTrace]
  refine ⟨5847277833199003557110881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7796370444265338076147841 5847277833199003557110881)
  ·
    refine ⟨4385458374899252667833161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5847277833199003557110881 4385458374899252667833161)
    ·
      refine ⟨3289093781174439500874871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4385458374899252667833161 3289093781174439500874871)
      ·
        refine ⟨4933640671761659251312307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3289093781174439500874871 4933640671761659251312307)
        ·
          refine ⟨7400461007642488876968461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4933640671761659251312307 7400461007642488876968461)
          ·
            refine ⟨2775172877865933328863173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7400461007642488876968461 2775172877865933328863173)
            ·
              refine ⟨520344914599862499161845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2775172877865933328863173 520344914599862499161845)
              ·
                refine ⟨48782335743737109296423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 520344914599862499161845 48782335743737109296423)
                ·
                  rfl

theorem cell20_320636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 4, 5].length) (baseStart_320636 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_320636 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_320636 prefixEnd_320636 := by exact prefixLift 320636
  have htrace : WordTrace (prefixWord ++ tailWord_320636) baseStart_320636 baseEnd_320636 := by
    simpa [prefixWord, tailWord_320636, baseEnd_320636] using wordTrace_append hprefix tailTrace_320636
  have hstable : (prefixWord ++ tailWord_320636).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320636).length < 2 ^ (prefixWord ++ tailWord_320636).sum := by decide
  have hdescent : baseEnd_320636 < baseStart_320636 := by decide
  rcases family_descends (prefixWord ++ tailWord_320636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320674 : List Nat := [3, 3, 1, 3, 10]
def baseStart_320674 : Nat := 118140960795 + 320674 * 2 ^ 59
def prefixEnd_320674 : Nat := 4983230072969 + 3 ^ 40 * 320674 * 2
def baseEnd_320674 : Nat := 1806967302057433143487

theorem tailTrace_320674 : CollatzResearch.WordTrace tailWord_320674 prefixEnd_320674 1806967302057433143487 := by
  unfold tailWord_320674
  simp only [CollatzResearch.WordTrace]
  refine ⟨2923985410065084901026269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7797294426840226402736717 2923985410065084901026269)
  ·
    refine ⟨1096494528774406837884851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2923985410065084901026269 1096494528774406837884851)
    ·
      refine ⟨1644741793161610256827277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1096494528774406837884851 1644741793161610256827277)
      ·
        refine ⟨616778172435603846310229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1644741793161610256827277 616778172435603846310229)
        ·
          refine ⟨1806967302057433143487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 616778172435603846310229 1806967302057433143487)
          ·
            rfl

theorem cell20_320674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 10].length) (baseStart_320674 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_320674 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_320674 prefixEnd_320674 := by exact prefixLift 320674
  have htrace : WordTrace (prefixWord ++ tailWord_320674) baseStart_320674 baseEnd_320674 := by
    simpa [prefixWord, tailWord_320674, baseEnd_320674] using wordTrace_append hprefix tailTrace_320674
  have hstable : (prefixWord ++ tailWord_320674).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320674).length < 2 ^ (prefixWord ++ tailWord_320674).sum := by decide
  have hdescent : baseEnd_320674 < baseStart_320674 := by decide
  rcases family_descends (prefixWord ++ tailWord_320674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320708 : List Nat := [2, 3, 3, 1, 3, 1, 3, 4]
def baseStart_320708 : Nat := 118140960795 + 320708 * 2 ^ 59
def prefixEnd_320708 : Nat := 4983230072969 + 3 ^ 40 * 320708 * 2
def baseEnd_320708 : Nat := 48793289997699692496325

theorem tailTrace_320708 : CollatzResearch.WordTrace tailWord_320708 prefixEnd_320708 48793289997699692496325 := by
  unfold tailWord_320708
  simp only [CollatzResearch.WordTrace]
  refine ⟨5848590861068581705421389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7798121148091442273895185 5848590861068581705421389)
  ·
    refine ⟨2193221572900718139533021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5848590861068581705421389 2193221572900718139533021)
    ·
      refine ⟨822458089837769302324883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2193221572900718139533021 822458089837769302324883)
      ·
        refine ⟨1233687134756653953487325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 822458089837769302324883 1233687134756653953487325)
        ·
          refine ⟨462632675533745232557747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1233687134756653953487325 462632675533745232557747)
          ·
            refine ⟨693949013300617848836621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 462632675533745232557747 693949013300617848836621)
            ·
              refine ⟨260230879987731693313733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 693949013300617848836621 260230879987731693313733)
              ·
                refine ⟨48793289997699692496325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 260230879987731693313733 48793289997699692496325)
                ·
                  rfl

theorem cell20_320708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 3, 4].length) (baseStart_320708 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_320708 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_320708 prefixEnd_320708 := by exact prefixLift 320708
  have htrace : WordTrace (prefixWord ++ tailWord_320708) baseStart_320708 baseEnd_320708 := by
    simpa [prefixWord, tailWord_320708, baseEnd_320708] using wordTrace_append hprefix tailTrace_320708
  have hstable : (prefixWord ++ tailWord_320708).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320708).length < 2 ^ (prefixWord ++ tailWord_320708).sum := by decide
  have hdescent : baseEnd_320708 < baseStart_320708 := by decide
  rcases family_descends (prefixWord ++ tailWord_320708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320736 : List Nat := [2, 1, 1, 3, 1, 4, 3, 2, 3]
def baseStart_320736 : Nat := 118140960795 + 320736 * 2 ^ 59
def prefixEnd_320736 : Nat := 4983230072969 + 3 ^ 40 * 320736 * 2
def baseEnd_320736 : Nat := 146392649956055424555527

theorem tailTrace_320736 : CollatzResearch.WordTrace tailWord_320736 prefixEnd_320736 146392649956055424555527 := by
  unfold tailWord_320736
  simp only [CollatzResearch.WordTrace]
  refine ⟨5849101483017862096431031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7798801977357149461908041 5849101483017862096431031)
  ·
    refine ⟨8773652224526793144646547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5849101483017862096431031 8773652224526793144646547)
    ·
      refine ⟨13160478336790189716969821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8773652224526793144646547 13160478336790189716969821)
      ·
        refine ⟨4935179376296321143863683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13160478336790189716969821 4935179376296321143863683)
        ·
          refine ⟨7402769064444481715795525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4935179376296321143863683 7402769064444481715795525)
          ·
            refine ⟨1388019199583340321711661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7402769064444481715795525 1388019199583340321711661)
            ·
              refine ⟨520507199843752620641873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1388019199583340321711661 520507199843752620641873)
              ·
                refine ⟨390380399882814465481405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 520507199843752620641873 390380399882814465481405)
                ·
                  refine ⟨146392649956055424555527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 390380399882814465481405 146392649956055424555527)
                  ·
                    rfl

theorem cell20_320736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 3, 2, 3].length) (baseStart_320736 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_320736 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_320736 prefixEnd_320736 := by exact prefixLift 320736
  have htrace : WordTrace (prefixWord ++ tailWord_320736) baseStart_320736 baseEnd_320736 := by
    simpa [prefixWord, tailWord_320736, baseEnd_320736] using wordTrace_append hprefix tailTrace_320736
  have hstable : (prefixWord ++ tailWord_320736).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320736).length < 2 ^ (prefixWord ++ tailWord_320736).sum := by decide
  have hdescent : baseEnd_320736 < baseStart_320736 := by decide
  rcases family_descends (prefixWord ++ tailWord_320736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320767 : List Nat := [1, 1, 2, 2, 1, 7, 2, 4]
def baseStart_320767 : Nat := 118140960795 + 320767 * 2 ^ 59
def prefixEnd_320767 : Nat := 4983230072969 + 3 ^ 40 * 320767 * 2
def baseEnd_320767 : Nat := 48802266400252364840689

theorem tailTrace_320767 : CollatzResearch.WordTrace tailWord_320767 prefixEnd_320767 48802266400252364840689 := by
  unfold tailWord_320767
  simp only [CollatzResearch.WordTrace]
  refine ⟨11699333628923416487240555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7799555752615610991493703 11699333628923416487240555)
  ·
    refine ⟨17549000443385124730860833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11699333628923416487240555 17549000443385124730860833)
    ·
      refine ⟨13161750332538843548145625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17549000443385124730860833 13161750332538843548145625)
      ·
        refine ⟨9871312749404132661109219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13161750332538843548145625 9871312749404132661109219)
        ·
          refine ⟨14806969124106198991663829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9871312749404132661109219 14806969124106198991663829)
          ·
            refine ⟨347038338846239038867121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 14806969124106198991663829 347038338846239038867121)
            ·
              refine ⟨260278754134679279150341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 347038338846239038867121 260278754134679279150341)
              ·
                refine ⟨48802266400252364840689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 260278754134679279150341 48802266400252364840689)
                ·
                  rfl

theorem cell20_320767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 2, 4].length) (baseStart_320767 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_320767 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_320767 prefixEnd_320767 := by exact prefixLift 320767
  have htrace : WordTrace (prefixWord ++ tailWord_320767) baseStart_320767 baseEnd_320767 := by
    simpa [prefixWord, tailWord_320767, baseEnd_320767] using wordTrace_append hprefix tailTrace_320767
  have hstable : (prefixWord ++ tailWord_320767).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320767).length < 2 ^ (prefixWord ++ tailWord_320767).sum := by decide
  have hdescent : baseEnd_320767 < baseStart_320767 := by decide
  rcases family_descends (prefixWord ++ tailWord_320767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320795 : List Nat := [1, 1, 1, 1, 1, 1, 5, 6, 3]
def baseStart_320795 : Nat := 118140960795 + 320795 * 2 ^ 59
def prefixEnd_320795 : Nat := 4983230072969 + 3 ^ 40 * 320795 * 2
def baseEnd_320795 : Nat := 146419579163713441588619

theorem tailTrace_320795 : CollatzResearch.WordTrace tailWord_320795 prefixEnd_320795 146419579163713441588619 := by
  unfold tailWord_320795
  simp only [CollatzResearch.WordTrace]
  refine ⟨11700354872821977269259839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7800236581881318179506559 11700354872821977269259839)
  ·
    refine ⟨17550532309232965903889759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11700354872821977269259839 17550532309232965903889759)
    ·
      refine ⟨26325798463849448855834639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17550532309232965903889759 26325798463849448855834639)
      ·
        refine ⟨39488697695774173283751959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26325798463849448855834639 39488697695774173283751959)
        ·
          refine ⟨59233046543661259925627939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39488697695774173283751959 59233046543661259925627939)
          ·
            refine ⟨88849569815491889888441909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59233046543661259925627939 88849569815491889888441909)
            ·
              refine ⟨8329647170202364677041429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 88849569815491889888441909 8329647170202364677041429)
              ·
                refine ⟨390452211103235844236317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8329647170202364677041429 390452211103235844236317)
                ·
                  refine ⟨146419579163713441588619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 390452211103235844236317 146419579163713441588619)
                  ·
                    rfl

theorem cell20_320795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 6, 3].length) (baseStart_320795 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_320795 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_320795 prefixEnd_320795 := by exact prefixLift 320795
  have htrace : WordTrace (prefixWord ++ tailWord_320795) baseStart_320795 baseEnd_320795 := by
    simpa [prefixWord, tailWord_320795, baseEnd_320795] using wordTrace_append hprefix tailTrace_320795
  have hstable : (prefixWord ++ tailWord_320795).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320795).length < 2 ^ (prefixWord ++ tailWord_320795).sum := by decide
  have hdescent : baseEnd_320795 < baseStart_320795 := by decide
  rcases family_descends (prefixWord ++ tailWord_320795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320808 : List Nat := [2, 1, 5, 1, 2, 3, 2, 1, 3]
def baseStart_320808 : Nat := 118140960795 + 320808 * 2 ^ 59
def prefixEnd_320808 : Nat := 4983230072969 + 3 ^ 40 * 320808 * 2
def baseEnd_320808 : Nat := 146425512717943174155233

theorem tailTrace_320808 : CollatzResearch.WordTrace tailWord_320808 prefixEnd_320808 146425512717943174155233 := by
  unfold tailWord_320808
  simp only [CollatzResearch.WordTrace]
  refine ⟨5850414510887440244741539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7800552681183253659655385 5850414510887440244741539)
  ·
    refine ⟨8775621766331160367112309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5850414510887440244741539 8775621766331160367112309)
    ·
      refine ⟨822714540593546284416779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8775621766331160367112309 822714540593546284416779)
      ·
        refine ⟨1234071810890319426625169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 822714540593546284416779 1234071810890319426625169)
        ·
          refine ⟨925553858167739569968877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1234071810890319426625169 925553858167739569968877)
          ·
            refine ⟨347082696812902338738329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 925553858167739569968877 347082696812902338738329)
            ·
              refine ⟨260312022609676754053747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 347082696812902338738329 260312022609676754053747)
              ·
                refine ⟨390468033914515131080621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 260312022609676754053747 390468033914515131080621)
                ·
                  refine ⟨146425512717943174155233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 390468033914515131080621 146425512717943174155233)
                  ·
                    rfl

theorem cell20_320808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 2, 1, 3].length) (baseStart_320808 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_320808 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_320808 prefixEnd_320808 := by exact prefixLift 320808
  have htrace : WordTrace (prefixWord ++ tailWord_320808) baseStart_320808 baseEnd_320808 := by
    simpa [prefixWord, tailWord_320808, baseEnd_320808] using wordTrace_append hprefix tailTrace_320808
  have hstable : (prefixWord ++ tailWord_320808).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320808).length < 2 ^ (prefixWord ++ tailWord_320808).sum := by decide
  have hdescent : baseEnd_320808 < baseStart_320808 := by decide
  rcases family_descends (prefixWord ++ tailWord_320808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320853 : List Nat := [1, 3, 2, 2, 3, 1, 4, 2, 2]
def baseStart_320853 : Nat := 118140960795 + 320853 * 2 ^ 59
def prefixEnd_320853 : Nat := 4983230072969 + 3 ^ 40 * 320853 * 2
def baseEnd_320853 : Nat := 146446051944123017655049

theorem tailTrace_320853 : CollatzResearch.WordTrace tailWord_320853 prefixEnd_320853 146446051944123017655049 := by
  unfold tailWord_320853
  simp only [CollatzResearch.WordTrace]
  refine ⟨11702470306611853174871213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7801646871074568783247475 11702470306611853174871213)
  ·
    refine ⟨4388426364979444940576705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11702470306611853174871213 4388426364979444940576705)
    ·
      refine ⟨3291319773734583705432529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4388426364979444940576705 3291319773734583705432529)
      ·
        refine ⟨2468489830300937779074397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3291319773734583705432529 2468489830300937779074397)
        ·
          refine ⟨925683686362851667152899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2468489830300937779074397 925683686362851667152899)
          ·
            refine ⟨1388525529544277500729349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 925683686362851667152899 1388525529544277500729349)
            ·
              refine ⟨260348536789552031386753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1388525529544277500729349 260348536789552031386753)
              ·
                refine ⟨195261402592164023540065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 260348536789552031386753 195261402592164023540065)
                ·
                  refine ⟨146446051944123017655049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 195261402592164023540065 146446051944123017655049)
                  ·
                    rfl

theorem cell20_320853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 4, 2, 2].length) (baseStart_320853 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_320853 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_320853 prefixEnd_320853 := by exact prefixLift 320853
  have htrace : WordTrace (prefixWord ++ tailWord_320853) baseStart_320853 baseEnd_320853 := by
    simpa [prefixWord, tailWord_320853, baseEnd_320853] using wordTrace_append hprefix tailTrace_320853
  have hstable : (prefixWord ++ tailWord_320853).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320853).length < 2 ^ (prefixWord ++ tailWord_320853).sum := by decide
  have hdescent : baseEnd_320853 < baseStart_320853 := by decide
  rcases family_descends (prefixWord ++ tailWord_320853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320864 : List Nat := [2, 1, 1, 3, 4, 1, 3, 5]
def baseStart_320864 : Nat := 118140960795 + 320864 * 2 ^ 59
def prefixEnd_320864 : Nat := 4983230072969 + 3 ^ 40 * 320864 * 2
def baseEnd_320864 : Nat := 48817024214618622762779

theorem tailTrace_320864 : CollatzResearch.WordTrace tailWord_320864 prefixEnd_320864 48817024214618622762779 := by
  unfold tailWord_320864
  simp only [CollatzResearch.WordTrace]
  refine ⟨5851435754786001026760823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7801914339714668035681097 5851435754786001026760823)
  ·
    refine ⟨8777153632179001540141235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5851435754786001026760823 8777153632179001540141235)
    ·
      refine ⟨13165730448268502310211853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8777153632179001540141235 13165730448268502310211853)
      ·
        refine ⟨4937148918100688366329445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13165730448268502310211853 4937148918100688366329445)
        ·
          refine ⟨925715422143879068686771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4937148918100688366329445 925715422143879068686771)
          ·
            refine ⟨1388573133215818603030157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 925715422143879068686771 1388573133215818603030157)
            ·
              refine ⟨520714924955931976136309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1388573133215818603030157 520714924955931976136309)
              ·
                refine ⟨48817024214618622762779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 520714924955931976136309 48817024214618622762779)
                ·
                  rfl

theorem cell20_320864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 3, 5].length) (baseStart_320864 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_320864 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_320864 prefixEnd_320864 := by exact prefixLift 320864
  have htrace : WordTrace (prefixWord ++ tailWord_320864) baseStart_320864 baseEnd_320864 := by
    simpa [prefixWord, tailWord_320864, baseEnd_320864] using wordTrace_append hprefix tailTrace_320864
  have hstable : (prefixWord ++ tailWord_320864).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320864).length < 2 ^ (prefixWord ++ tailWord_320864).sum := by decide
  have hdescent : baseEnd_320864 < baseStart_320864 := by decide
  rcases family_descends (prefixWord ++ tailWord_320864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320874 : List Nat := [3, 1, 3, 3, 2, 1, 1, 2, 4]
def baseStart_320874 : Nat := 118140960795 + 320874 * 2 ^ 59
def prefixEnd_320874 : Nat := 4983230072969 + 3 ^ 40 * 320874 * 2
def baseEnd_320874 : Nat := 146455636916340277954963

theorem tailTrace_320874 : CollatzResearch.WordTrace tailWord_320874 prefixEnd_320874 146455636916340277954963 := by
  unfold tailWord_320874
  simp only [CollatzResearch.WordTrace]
  refine ⟨2925809059883943440346419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7802157493023849174257117 2925809059883943440346419)
  ·
    refine ⟨4388713589825915160519629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2925809059883943440346419 4388713589825915160519629)
    ·
      refine ⟨1645767596184718185194861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4388713589825915160519629 1645767596184718185194861)
      ·
        refine ⟨617162848569269319448073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1645767596184718185194861 617162848569269319448073)
        ·
          refine ⟨462872136426951989586055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 617162848569269319448073 462872136426951989586055)
          ·
            refine ⟨694308204640427984379083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 462872136426951989586055 694308204640427984379083)
            ·
              refine ⟨1041462306960641976568625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 694308204640427984379083 1041462306960641976568625)
              ·
                refine ⟨781096730220481482426469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1041462306960641976568625 781096730220481482426469)
                ·
                  refine ⟨146455636916340277954963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 781096730220481482426469 146455636916340277954963)
                  ·
                    rfl

theorem cell20_320874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 2, 4].length) (baseStart_320874 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_320874 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_320874 prefixEnd_320874 := by exact prefixLift 320874
  have htrace : WordTrace (prefixWord ++ tailWord_320874) baseStart_320874 baseEnd_320874 := by
    simpa [prefixWord, tailWord_320874, baseEnd_320874] using wordTrace_append hprefix tailTrace_320874
  have hstable : (prefixWord ++ tailWord_320874).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320874).length < 2 ^ (prefixWord ++ tailWord_320874).sum := by decide
  have hdescent : baseEnd_320874 < baseStart_320874 := by decide
  rcases family_descends (prefixWord ++ tailWord_320874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320905 : List Nat := [1, 2, 1, 1, 7, 2, 1, 2, 3]
def baseStart_320905 : Nat := 118140960795 + 320905 * 2 ^ 59
def prefixEnd_320905 : Nat := 4983230072969 + 3 ^ 40 * 320905 * 2
def baseEnd_320905 : Nat := 146469786161041947921503

theorem tailTrace_320905 : CollatzResearch.WordTrace tailWord_320905 prefixEnd_320905 146469786161041947921503 := by
  unfold tailWord_320905
  simp only [CollatzResearch.WordTrace]
  refine ⟨11704366902423466055764169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7802911268282310703842779 11704366902423466055764169)
  ·
    refine ⟨8778275176817599541823127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11704366902423466055764169 8778275176817599541823127)
    ·
      refine ⟨13167412765226399312734691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8778275176817599541823127 13167412765226399312734691)
      ·
        refine ⟨19751119147839598969102037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13167412765226399312734691 19751119147839598969102037)
        ·
          refine ⟨462916855027490600838329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 19751119147839598969102037 462916855027490600838329)
          ·
            refine ⟨347187641270617950628747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 462916855027490600838329 347187641270617950628747)
            ·
              refine ⟨520781461905926925943121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 347187641270617950628747 520781461905926925943121)
              ·
                refine ⟨390586096429445194457341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 520781461905926925943121 390586096429445194457341)
                ·
                  refine ⟨146469786161041947921503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 390586096429445194457341 146469786161041947921503)
                  ·
                    rfl

theorem cell20_320905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 1, 2, 3].length) (baseStart_320905 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_320905 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_320905 prefixEnd_320905 := by exact prefixLift 320905
  have htrace : WordTrace (prefixWord ++ tailWord_320905) baseStart_320905 baseEnd_320905 := by
    simpa [prefixWord, tailWord_320905, baseEnd_320905] using wordTrace_append hprefix tailTrace_320905
  have hstable : (prefixWord ++ tailWord_320905).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320905).length < 2 ^ (prefixWord ++ tailWord_320905).sum := by decide
  have hdescent : baseEnd_320905 < baseStart_320905 := by decide
  rcases family_descends (prefixWord ++ tailWord_320905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320940 : List Nat := [2, 2, 1, 1, 1, 1, 8, 4]
def baseStart_320940 : Nat := 118140960795 + 320940 * 2 ^ 59
def prefixEnd_320940 : Nat := 4983230072969 + 3 ^ 40 * 320940 * 2
def baseEnd_320940 : Nat := 48828587038245793918231

theorem tailTrace_320940 : CollatzResearch.WordTrace tailWord_320940 prefixEnd_320940 48828587038245793918231 := by
  unfold tailWord_320940
  simp only [CollatzResearch.WordTrace]
  refine ⟨5852821728648333516644137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7803762304864444688858849 5852821728648333516644137)
  ·
    refine ⟨4389616296486250137483103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5852821728648333516644137 4389616296486250137483103)
    ·
      refine ⟨6584424444729375206224655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4389616296486250137483103 6584424444729375206224655)
      ·
        refine ⟨9876636667094062809336983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6584424444729375206224655 9876636667094062809336983)
        ·
          refine ⟨14814955000641094214005475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9876636667094062809336983 14814955000641094214005475)
          ·
            refine ⟨22222432500961641321008213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14814955000641094214005475 22222432500961641321008213)
            ·
              refine ⟨260419130870644234230565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 22222432500961641321008213 260419130870644234230565)
              ·
                refine ⟨48828587038245793918231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 260419130870644234230565 48828587038245793918231)
                ·
                  rfl

theorem cell20_320940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 8, 4].length) (baseStart_320940 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_320940 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_320940 prefixEnd_320940 := by exact prefixLift 320940
  have htrace : WordTrace (prefixWord ++ tailWord_320940) baseStart_320940 baseEnd_320940 := by
    simpa [prefixWord, tailWord_320940, baseEnd_320940] using wordTrace_append hprefix tailTrace_320940
  have hstable : (prefixWord ++ tailWord_320940).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320940).length < 2 ^ (prefixWord ++ tailWord_320940).sum := by decide
  have hdescent : baseEnd_320940 < baseStart_320940 := by decide
  rcases family_descends (prefixWord ++ tailWord_320940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320964 : List Nat := [2, 3, 3, 2, 1, 1, 2, 1, 5]
def baseStart_320964 : Nat := 118140960795 + 320964 * 2 ^ 59
def prefixEnd_320964 : Nat := 4983230072969 + 3 ^ 40 * 320964 * 2
def baseEnd_320964 : Nat := 146496715368699964954595

theorem tailTrace_320964 : CollatzResearch.WordTrace tailWord_320964 prefixEnd_320964 146496715368699964954595 := by
  unfold tailWord_320964
  simp only [CollatzResearch.WordTrace]
  refine ⟨5853259404604859566080973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7804345872806479421441297 5853259404604859566080973)
  ·
    refine ⟨2194972276726822337280365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5853259404604859566080973 2194972276726822337280365)
    ·
      refine ⟨823114603772558376480137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2194972276726822337280365 823114603772558376480137)
      ·
        refine ⟨617335952829418782360103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 823114603772558376480137 617335952829418782360103)
        ·
          refine ⟨926003929244128173540155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 617335952829418782360103 926003929244128173540155)
          ·
            refine ⟨1389005893866192260310233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 926003929244128173540155 1389005893866192260310233)
            ·
              refine ⟨1041754420399644195232675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1389005893866192260310233 1041754420399644195232675)
              ·
                refine ⟨1562631630599466292849013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1041754420399644195232675 1562631630599466292849013)
                ·
                  refine ⟨146496715368699964954595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1562631630599466292849013 146496715368699964954595)
                  ·
                    rfl

theorem cell20_320964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 1, 5].length) (baseStart_320964 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_320964 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_320964 prefixEnd_320964 := by exact prefixLift 320964
  have htrace : WordTrace (prefixWord ++ tailWord_320964) baseStart_320964 baseEnd_320964 := by
    simpa [prefixWord, tailWord_320964, baseEnd_320964] using wordTrace_append hprefix tailTrace_320964
  have hstable : (prefixWord ++ tailWord_320964).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320964).length < 2 ^ (prefixWord ++ tailWord_320964).sum := by decide
  have hdescent : baseEnd_320964 < baseStart_320964 := by decide
  rcases family_descends (prefixWord ++ tailWord_320964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320971 : List Nat := [1, 1, 1, 1, 3, 3, 2, 6, 2]
def baseStart_320971 : Nat := 118140960795 + 320971 * 2 ^ 59
def prefixEnd_320971 : Nat := 4983230072969 + 3 ^ 40 * 320971 * 2
def baseEnd_320971 : Nat := 146499910359439051721233

theorem tailTrace_320971 : CollatzResearch.WordTrace tailWord_320971 prefixEnd_320971 146499910359439051721233 := by
  unfold tailWord_320971
  simp only [CollatzResearch.WordTrace]
  refine ⟨11706774120184359327666767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7804516080122906218444511 11706774120184359327666767)
  ·
    refine ⟨17560161180276538991500151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11706774120184359327666767 17560161180276538991500151)
    ·
      refine ⟨26340241770414808487250227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17560161180276538991500151 26340241770414808487250227)
      ·
        refine ⟨39510362655622212730875341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26340241770414808487250227 39510362655622212730875341)
        ·
          refine ⟨14816385995858329774078253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39510362655622212730875341 14816385995858329774078253)
          ·
            refine ⟨5556144748446873665279345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14816385995858329774078253 5556144748446873665279345)
            ·
              refine ⟨4167108561335155248959509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5556144748446873665279345 4167108561335155248959509)
              ·
                refine ⟨195333213812585402294977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4167108561335155248959509 195333213812585402294977)
                ·
                  refine ⟨146499910359439051721233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 195333213812585402294977 146499910359439051721233)
                  ·
                    rfl

theorem cell20_320971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 6, 2].length) (baseStart_320971 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_320971 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_320971 prefixEnd_320971 := by exact prefixLift 320971
  have htrace : WordTrace (prefixWord ++ tailWord_320971) baseStart_320971 baseEnd_320971 := by
    simpa [prefixWord, tailWord_320971, baseEnd_320971] using wordTrace_append hprefix tailTrace_320971
  have hstable : (prefixWord ++ tailWord_320971).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320971).length < 2 ^ (prefixWord ++ tailWord_320971).sum := by decide
  have hdescent : baseEnd_320971 < baseStart_320971 := by decide
  rcases family_descends (prefixWord ++ tailWord_320971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321022 : List Nat := [4, 2, 2, 3, 1, 1, 1, 4, 2]
def baseStart_321022 : Nat := 118140960795 + 321022 * 2 ^ 59
def prefixEnd_321022 : Nat := 4983230072969 + 3 ^ 40 * 321022 * 2
def baseEnd_321022 : Nat := 146523188149109541021025

theorem tailTrace_321022 : CollatzResearch.WordTrace tailWord_321022 prefixEnd_321022 146523188149109541021025 := by
  unfold tailWord_321022
  simp only [CollatzResearch.WordTrace]
  refine ⟨1463579280374949379721665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7805756161999730025182213 1463579280374949379721665)
  ·
    refine ⟨1097684460281212034791249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1463579280374949379721665 1097684460281212034791249)
    ·
      refine ⟨823263345210909026093437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1097684460281212034791249 823263345210909026093437)
      ·
        refine ⟨308723754454090884785039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 823263345210909026093437 308723754454090884785039)
        ·
          refine ⟨463085631681136327177559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 308723754454090884785039 463085631681136327177559)
          ·
            refine ⟨694628447521704490766339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 463085631681136327177559 694628447521704490766339)
            ·
              refine ⟨1041942671282556736149509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 694628447521704490766339 1041942671282556736149509)
              ·
                refine ⟨195364250865479388028033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1041942671282556736149509 195364250865479388028033)
                ·
                  refine ⟨146523188149109541021025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 195364250865479388028033 146523188149109541021025)
                  ·
                    rfl

theorem cell20_321022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 4, 2].length) (baseStart_321022 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_321022 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_321022 prefixEnd_321022 := by exact prefixLift 321022
  have htrace : WordTrace (prefixWord ++ tailWord_321022) baseStart_321022 baseEnd_321022 := by
    simpa [prefixWord, tailWord_321022, baseEnd_321022] using wordTrace_append hprefix tailTrace_321022
  have hstable : (prefixWord ++ tailWord_321022).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321022).length < 2 ^ (prefixWord ++ tailWord_321022).sum := by decide
  have hdescent : baseEnd_321022 < baseStart_321022 := by decide
  rcases family_descends (prefixWord ++ tailWord_321022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321075 : List Nat := [1, 1, 1, 2, 4, 4, 7]
def baseStart_321075 : Nat := 118140960795 + 321075 * 2 ^ 59
def prefixEnd_321075 : Nat := 4983230072969 + 3 ^ 40 * 321075 * 2
def baseEnd_321075 : Nat := 16283042088141879139349

theorem tailTrace_321075 : CollatzResearch.WordTrace tailWord_321075 prefixEnd_321075 16283042088141879139349 := by
  unfold tailWord_321075
  simp only [CollatzResearch.WordTrace]
  refine ⟨11710567311807585089452679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7807044874538390059635119 11710567311807585089452679)
  ·
    refine ⟨17565850967711377634179019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11710567311807585089452679 17565850967711377634179019)
    ·
      refine ⟨26348776451567066451268529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17565850967711377634179019 26348776451567066451268529)
      ·
        refine ⟨19761582338675299838451397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26348776451567066451268529 19761582338675299838451397)
        ·
          refine ⟨3705296688501618719709637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19761582338675299838451397 3705296688501618719709637)
          ·
            refine ⟨694743129094053509945557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3705296688501618719709637 694743129094053509945557)
            ·
              refine ⟨16283042088141879139349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 694743129094053509945557 16283042088141879139349)
              ·
                rfl

theorem cell20_321075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 7].length) (baseStart_321075 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_321075 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_321075 prefixEnd_321075 := by exact prefixLift 321075
  have htrace : WordTrace (prefixWord ++ tailWord_321075) baseStart_321075 baseEnd_321075 := by
    simpa [prefixWord, tailWord_321075, baseEnd_321075] using wordTrace_append hprefix tailTrace_321075
  have hstable : (prefixWord ++ tailWord_321075).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321075).length < 2 ^ (prefixWord ++ tailWord_321075).sum := by decide
  have hdescent : baseEnd_321075 < baseStart_321075 := by decide
  rcases family_descends (prefixWord ++ tailWord_321075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321095 : List Nat := [1, 1, 4, 1, 5, 1, 3, 1, 3]
def baseStart_321095 : Nat := 118140960795 + 321095 * 2 ^ 59
def prefixEnd_321095 : Nat := 4983230072969 + 3 ^ 40 * 321095 * 2
def baseEnd_321095 : Nat := 146556507338245731587393

theorem tailTrace_321095 : CollatzResearch.WordTrace tailWord_321095 prefixEnd_321095 146556507338245731587393 := by
  unfold tailWord_321095
  simp only [CollatzResearch.WordTrace]
  refine ⟨11711296771735128505180739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7807531181156752336787159 11711296771735128505180739)
  ·
    refine ⟨17566945157602692757771109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11711296771735128505180739 17566945157602692757771109)
    ·
      refine ⟨3293802217050504892082083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17566945157602692757771109 3293802217050504892082083)
      ·
        refine ⟨4940703325575757338123125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3293802217050504892082083 4940703325575757338123125)
        ·
          refine ⟨463190936772727250449043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4940703325575757338123125 463190936772727250449043)
          ·
            refine ⟨694786405159090875673565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 463190936772727250449043 694786405159090875673565)
            ·
              refine ⟨260544901934659078377587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 694786405159090875673565 260544901934659078377587)
              ·
                refine ⟨390817352901988617566381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 260544901934659078377587 390817352901988617566381)
                ·
                  refine ⟨146556507338245731587393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 390817352901988617566381 146556507338245731587393)
                  ·
                    rfl

theorem cell20_321095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 3, 1, 3].length) (baseStart_321095 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_321095 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_321095 prefixEnd_321095 := by exact prefixLift 321095
  have htrace : WordTrace (prefixWord ++ tailWord_321095) baseStart_321095 baseEnd_321095 := by
    simpa [prefixWord, tailWord_321095, baseEnd_321095] using wordTrace_append hprefix tailTrace_321095
  have hstable : (prefixWord ++ tailWord_321095).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321095).length < 2 ^ (prefixWord ++ tailWord_321095).sum := by decide
  have hdescent : baseEnd_321095 < baseStart_321095 := by decide
  rcases family_descends (prefixWord ++ tailWord_321095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321130 : List Nat := [3, 1, 3, 2, 1, 4, 6]
def baseStart_321130 : Nat := 118140960795 + 321130 * 2 ^ 59
def prefixEnd_321130 : Nat := 4983230072969 + 3 ^ 40 * 321130 * 2
def baseEnd_321130 : Nat := 16285831365771240602287

theorem tailTrace_321130 : CollatzResearch.WordTrace tailWord_321130 prefixEnd_321130 16285831365771240602287 := by
  unfold tailWord_321130
  simp only [CollatzResearch.WordTrace]
  refine ⟨2928143331652082370676211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7808382217738886321803229 2928143331652082370676211)
  ·
    refine ⟨4392214997478123556014317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2928143331652082370676211 4392214997478123556014317)
    ·
      refine ⟨1647080624054296333505369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4392214997478123556014317 1647080624054296333505369)
      ·
        refine ⟨1235310468040722250129027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1647080624054296333505369 1235310468040722250129027)
        ·
          refine ⟨1852965702061083375193541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1235310468040722250129027 1852965702061083375193541)
          ·
            refine ⟨347431069136453132848789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1852965702061083375193541 347431069136453132848789)
            ·
              refine ⟨16285831365771240602287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 347431069136453132848789 16285831365771240602287)
              ·
                rfl

theorem cell20_321130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 6].length) (baseStart_321130 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_321130 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_321130 prefixEnd_321130 := by exact prefixLift 321130
  have htrace : WordTrace (prefixWord ++ tailWord_321130) baseStart_321130 baseEnd_321130 := by
    simpa [prefixWord, tailWord_321130, baseEnd_321130] using wordTrace_append hprefix tailTrace_321130
  have hstable : (prefixWord ++ tailWord_321130).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321130).length < 2 ^ (prefixWord ++ tailWord_321130).sum := by decide
  have hdescent : baseEnd_321130 < baseStart_321130 := by decide
  rcases family_descends (prefixWord ++ tailWord_321130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321199 : List Nat := [1, 1, 2, 1, 2, 4, 3, 4, 2]
def baseStart_321199 : Nat := 118140960795 + 321199 * 2 ^ 59
def prefixEnd_321199 : Nat := 4983230072969 + 3 ^ 40 * 321199 * 2
def baseEnd_321199 : Nat := 146603975772083592120301

theorem tailTrace_321199 : CollatzResearch.WordTrace tailWord_321199 prefixEnd_321199 146603975772083592120301 := by
  unfold tailWord_321199
  simp only [CollatzResearch.WordTrace]
  refine ⟨11715089963358354266966651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7810059975572236177977767 11715089963358354266966651)
  ·
    refine ⟨17572634945037531400449977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11715089963358354266966651 17572634945037531400449977)
    ·
      refine ⟨13179476208778148550337483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17572634945037531400449977 13179476208778148550337483)
      ·
        refine ⟨19769214313167222825506225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13179476208778148550337483 19769214313167222825506225)
        ·
          refine ⟨14826910734875417119129669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19769214313167222825506225 14826910734875417119129669)
          ·
            refine ⟨2780045762789140709836813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14826910734875417119129669 2780045762789140709836813)
            ·
              refine ⟨1042517161045927766188805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2780045762789140709836813 1042517161045927766188805)
              ·
                refine ⟨195471967696111456160401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1042517161045927766188805 195471967696111456160401)
                ·
                  refine ⟨146603975772083592120301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 195471967696111456160401 146603975772083592120301)
                  ·
                    rfl

theorem cell20_321199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 4, 2].length) (baseStart_321199 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_321199 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_321199 prefixEnd_321199 := by exact prefixLift 321199
  have htrace : WordTrace (prefixWord ++ tailWord_321199) baseStart_321199 baseEnd_321199 := by
    simpa [prefixWord, tailWord_321199, baseEnd_321199] using wordTrace_append hprefix tailTrace_321199
  have hstable : (prefixWord ++ tailWord_321199).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321199).length < 2 ^ (prefixWord ++ tailWord_321199).sum := by decide
  have hdescent : baseEnd_321199 < baseStart_321199 := by decide
  rcases family_descends (prefixWord ++ tailWord_321199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321213 : List Nat := [1, 4, 1, 2, 1, 2, 1, 5, 3]
def baseStart_321213 : Nat := 118140960795 + 321213 * 2 ^ 59
def prefixEnd_321213 : Nat := 4983230072969 + 3 ^ 40 * 321213 * 2
def baseEnd_321213 : Nat := 146610365753561765653577

theorem tailTrace_321213 : CollatzResearch.WordTrace tailWord_321213 prefixEnd_321213 146610365753561765653577 := by
  unfold tailWord_321213
  simp only [CollatzResearch.WordTrace]
  refine ⟨11715600585307634657976293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7810400390205089771984195 11715600585307634657976293)
  ·
    refine ⟨2196675109745181498370555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11715600585307634657976293 2196675109745181498370555)
    ·
      refine ⟨3295012664617772247555833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2196675109745181498370555 3295012664617772247555833)
      ·
        refine ⟨2471259498463329185666875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3295012664617772247555833 2471259498463329185666875)
        ·
          refine ⟨3706889247694993778500313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2471259498463329185666875 3706889247694993778500313)
          ·
            refine ⟨2780166935771245333875235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3706889247694993778500313 2780166935771245333875235)
            ·
              refine ⟨4170250403656868000812853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2780166935771245333875235 4170250403656868000812853)
              ·
                refine ⟨390960975342831375076205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4170250403656868000812853 390960975342831375076205)
                ·
                  refine ⟨146610365753561765653577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 390960975342831375076205 146610365753561765653577)
                  ·
                    rfl

theorem cell20_321213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 5, 3].length) (baseStart_321213 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_321213 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_321213 prefixEnd_321213 := by exact prefixLift 321213
  have htrace : WordTrace (prefixWord ++ tailWord_321213) baseStart_321213 baseEnd_321213 := by
    simpa [prefixWord, tailWord_321213, baseEnd_321213] using wordTrace_append hprefix tailTrace_321213
  have hstable : (prefixWord ++ tailWord_321213).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321213).length < 2 ^ (prefixWord ++ tailWord_321213).sum := by decide
  have hdescent : baseEnd_321213 < baseStart_321213 := by decide
  rcases family_descends (prefixWord ++ tailWord_321213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321258 : List Nat := [3, 1, 3, 1, 1, 1, 3, 3, 4]
def baseStart_321258 : Nat := 118140960795 + 321258 * 2 ^ 59
def prefixEnd_321258 : Nat := 4983230072969 + 3 ^ 40 * 321258 * 2
def baseEnd_321258 : Nat := 146630904979741609153393

theorem tailTrace_321258 : CollatzResearch.WordTrace tailWord_321258 prefixEnd_321258 146630904979741609153393 := by
  unfold tailWord_321258
  simp only [CollatzResearch.WordTrace]
  refine ⟨2929310467536151835841107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7811494580096404895576285 2929310467536151835841107)
  ·
    refine ⟨4393965701304227753761661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2929310467536151835841107 4393965701304227753761661)
    ·
      refine ⟨1647737137989085407660623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4393965701304227753761661 1647737137989085407660623)
      ·
        refine ⟨2471605706983628111490935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1647737137989085407660623 2471605706983628111490935)
        ·
          refine ⟨3707408560475442167236403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2471605706983628111490935 3707408560475442167236403)
          ·
            refine ⟨5561112840713163250854605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3707408560475442167236403 5561112840713163250854605)
            ·
              refine ⟨2085417315267436219070477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5561112840713163250854605 2085417315267436219070477)
              ·
                refine ⟨782031493225288582151429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2085417315267436219070477 782031493225288582151429)
                ·
                  refine ⟨146630904979741609153393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 782031493225288582151429 146630904979741609153393)
                  ·
                    rfl

theorem cell20_321258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 3, 4].length) (baseStart_321258 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_321258 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_321258 prefixEnd_321258 := by exact prefixLift 321258
  have htrace : WordTrace (prefixWord ++ tailWord_321258) baseStart_321258 baseEnd_321258 := by
    simpa [prefixWord, tailWord_321258, baseEnd_321258] using wordTrace_append hprefix tailTrace_321258
  have hstable : (prefixWord ++ tailWord_321258).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321258).length < 2 ^ (prefixWord ++ tailWord_321258).sum := by decide
  have hdescent : baseEnd_321258 < baseStart_321258 := by decide
  rcases family_descends (prefixWord ++ tailWord_321258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321278 : List Nat := [4, 2, 2, 1, 3, 2, 2, 4]
def baseStart_321278 : Nat := 118140960795 + 321278 * 2 ^ 59
def prefixEnd_321278 : Nat := 4983230072969 + 3 ^ 40 * 321278 * 2
def baseEnd_321278 : Nat := 48880011174903476162215

theorem tailTrace_321278 : CollatzResearch.WordTrace tailWord_321278 prefixEnd_321278 48880011174903476162215 := by
  unfold tailWord_321278
  simp only [CollatzResearch.WordTrace]
  refine ⟨1464746416259018844886561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7811980886714767172728325 1464746416259018844886561)
  ·
    refine ⟨1098559812194264133664921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1464746416259018844886561 1098559812194264133664921)
    ·
      refine ⟨823919859145698100248691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1098559812194264133664921 823919859145698100248691)
      ·
        refine ⟨1235879788718547150373037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 823919859145698100248691 1235879788718547150373037)
        ·
          refine ⟨463454920769455181389889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1235879788718547150373037 463454920769455181389889)
          ·
            refine ⟨347591190577091386042417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 463454920769455181389889 347591190577091386042417)
            ·
              refine ⟨260693392932818539531813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 347591190577091386042417 260693392932818539531813)
              ·
                refine ⟨48880011174903476162215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 260693392932818539531813 48880011174903476162215)
                ·
                  rfl

theorem cell20_321278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 2, 4].length) (baseStart_321278 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_321278 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_321278 prefixEnd_321278 := by exact prefixLift 321278
  have htrace : WordTrace (prefixWord ++ tailWord_321278) baseStart_321278 baseEnd_321278 := by
    simpa [prefixWord, tailWord_321278, baseEnd_321278] using wordTrace_append hprefix tailTrace_321278
  have hstable : (prefixWord ++ tailWord_321278).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321278).length < 2 ^ (prefixWord ++ tailWord_321278).sum := by decide
  have hdescent : baseEnd_321278 < baseStart_321278 := by decide
  rcases family_descends (prefixWord ++ tailWord_321278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321282 : List Nat := [3, 4, 1, 1, 1, 1, 3, 6]
def baseStart_321282 : Nat := 118140960795 + 321282 * 2 ^ 59
def prefixEnd_321282 : Nat := 4983230072969 + 3 ^ 40 * 321282 * 2
def baseEnd_321282 : Nat := 48880619744568064117765

theorem tailTrace_321282 : CollatzResearch.WordTrace tailWord_321282 prefixEnd_321282 48880619744568064117765 := by
  unfold tailWord_321282
  simp only [CollatzResearch.WordTrace]
  refine ⟨2929529305514414860559525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7812078148038439628158733 2929529305514414860559525)
  ·
    refine ⟨549286744783952786354911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2929529305514414860559525 549286744783952786354911)
    ·
      refine ⟨823930117175929179532367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 549286744783952786354911 823930117175929179532367)
      ·
        refine ⟨1235895175763893769298551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 823930117175929179532367 1235895175763893769298551)
        ·
          refine ⟨1853842763645840653947827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1235895175763893769298551 1853842763645840653947827)
          ·
            refine ⟨2780764145468760980921741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1853842763645840653947827 2780764145468760980921741)
            ·
              refine ⟨1042786554550785367845653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2780764145468760980921741 1042786554550785367845653)
              ·
                refine ⟨48880619744568064117765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1042786554550785367845653 48880619744568064117765)
                ·
                  rfl

theorem cell20_321282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 6].length) (baseStart_321282 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_321282 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_321282 prefixEnd_321282 := by exact prefixLift 321282
  have htrace : WordTrace (prefixWord ++ tailWord_321282) baseStart_321282 baseEnd_321282 := by
    simpa [prefixWord, tailWord_321282, baseEnd_321282] using wordTrace_append hprefix tailTrace_321282
  have hstable : (prefixWord ++ tailWord_321282).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321282).length < 2 ^ (prefixWord ++ tailWord_321282).sum := by decide
  have hdescent : baseEnd_321282 < baseStart_321282 := by decide
  rcases family_descends (prefixWord ++ tailWord_321282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321303 : List Nat := [1, 1, 3, 4, 2, 1, 8]
def baseStart_321303 : Nat := 118140960795 + 321303 * 2 ^ 59
def prefixEnd_321303 : Nat := 4983230072969 + 3 ^ 40 * 321303 * 2
def baseEnd_321303 : Nat := 16294604911769050294801

theorem tailTrace_321303 : CollatzResearch.WordTrace tailWord_321303 prefixEnd_321303 16294604911769050294801 := by
  unfold tailWord_321303
  simp only [CollatzResearch.WordTrace]
  refine ⟨11718883154981580028752563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7812588769987720019168375 11718883154981580028752563)
  ·
    refine ⟨17578324732472370043128845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11718883154981580028752563 17578324732472370043128845)
    ·
      refine ⟨6591871774677138766173317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17578324732472370043128845 6591871774677138766173317)
      ·
        refine ⟨1235975957751963518657497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6591871774677138766173317 1235975957751963518657497)
        ·
          refine ⟨926981968313972638993123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1235975957751963518657497 926981968313972638993123)
          ·
            refine ⟨1390472952470958958489685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 926981968313972638993123 1390472952470958958489685)
            ·
              refine ⟨16294604911769050294801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1390472952470958958489685 16294604911769050294801)
              ·
                rfl

theorem cell20_321303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 8].length) (baseStart_321303 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_321303 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_321303 prefixEnd_321303 := by exact prefixLift 321303
  have htrace : WordTrace (prefixWord ++ tailWord_321303) baseStart_321303 baseEnd_321303 := by
    simpa [prefixWord, tailWord_321303, baseEnd_321303] using wordTrace_append hprefix tailTrace_321303
  have hstable : (prefixWord ++ tailWord_321303).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321303).length < 2 ^ (prefixWord ++ tailWord_321303).sum := by decide
  have hdescent : baseEnd_321303 < baseStart_321303 := by decide
  rcases family_descends (prefixWord ++ tailWord_321303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321313 : List Nat := [1, 2, 3, 2, 1, 5, 1, 1, 4]
def baseStart_321313 : Nat := 118140960795 + 321313 * 2 ^ 59
def prefixEnd_321313 : Nat := 4983230072969 + 3 ^ 40 * 321313 * 2
def baseEnd_321313 : Nat := 146656008478405862319835

theorem tailTrace_321313 : CollatzResearch.WordTrace tailWord_321313 prefixEnd_321313 146656008478405862319835 := by
  unfold tailWord_321313
  simp only [CollatzResearch.WordTrace]
  refine ⟨11719247884945351736616593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7812831923296901157744395 11719247884945351736616593)
  ·
    refine ⟨8789435913709013802462445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11719247884945351736616593 8789435913709013802462445)
    ·
      refine ⟨3296038467640880175923417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8789435913709013802462445 3296038467640880175923417)
      ·
        refine ⟨2472028850730660131942563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3296038467640880175923417 2472028850730660131942563)
        ·
          refine ⟨3708043276095990197913845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2472028850730660131942563 3708043276095990197913845)
          ·
            refine ⟨347629057133999081054423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3708043276095990197913845 347629057133999081054423)
            ·
              refine ⟨521443585700998621581635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 347629057133999081054423 521443585700998621581635)
              ·
                refine ⟨782165378551497932372453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 521443585700998621581635 782165378551497932372453)
                ·
                  refine ⟨146656008478405862319835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 782165378551497932372453 146656008478405862319835)
                  ·
                    rfl

theorem cell20_321313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 1, 1, 4].length) (baseStart_321313 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_321313 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_321313 prefixEnd_321313 := by exact prefixLift 321313
  have htrace : WordTrace (prefixWord ++ tailWord_321313) baseStart_321313 baseEnd_321313 := by
    simpa [prefixWord, tailWord_321313, baseEnd_321313] using wordTrace_append hprefix tailTrace_321313
  have hstable : (prefixWord ++ tailWord_321313).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321313).length < 2 ^ (prefixWord ++ tailWord_321313).sum := by decide
  have hdescent : baseEnd_321313 < baseStart_321313 := by decide
  rcases family_descends (prefixWord ++ tailWord_321313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321320 : List Nat := [2, 1, 5, 1, 1, 3, 2, 5]
def baseStart_321320 : Nat := 118140960795 + 321320 * 2 ^ 59
def prefixEnd_321320 : Nat := 4983230072969 + 3 ^ 40 * 321320 * 2
def baseEnd_321320 : Nat := 48886401156381649695491

theorem tailTrace_321320 : CollatzResearch.WordTrace tailWord_321320 prefixEnd_321320 48886401156381649695491 := by
  unfold tailWord_321320
  simp only [CollatzResearch.WordTrace]
  refine ⟨5859751597959995966060707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7813002130613327954747609 5859751597959995966060707)
  ·
    refine ⟨8789627396939993949091061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5859751597959995966060707 8789627396939993949091061)
    ·
      refine ⟨824027568463124432727287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8789627396939993949091061 824027568463124432727287)
      ·
        refine ⟨1236041352694686649090931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 824027568463124432727287 1236041352694686649090931)
        ·
          refine ⟨1854062029042029973636397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1236041352694686649090931 1854062029042029973636397)
          ·
            refine ⟨695273260890761240113649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1854062029042029973636397 695273260890761240113649)
            ·
              refine ⟨521454945668070930085237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 695273260890761240113649 521454945668070930085237)
              ·
                refine ⟨48886401156381649695491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 521454945668070930085237 48886401156381649695491)
                ·
                  rfl

theorem cell20_321320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 2, 5].length) (baseStart_321320 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_321320 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_321320 prefixEnd_321320 := by exact prefixLift 321320
  have htrace : WordTrace (prefixWord ++ tailWord_321320) baseStart_321320 baseEnd_321320 := by
    simpa [prefixWord, tailWord_321320, baseEnd_321320] using wordTrace_append hprefix tailTrace_321320
  have hstable : (prefixWord ++ tailWord_321320).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321320).length < 2 ^ (prefixWord ++ tailWord_321320).sum := by decide
  have hdescent : baseEnd_321320 < baseStart_321320 := by decide
  rcases family_descends (prefixWord ++ tailWord_321320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321365 : List Nat := [1, 3, 2, 2, 2, 2, 1, 4, 3]
def baseStart_321365 : Nat := 118140960795 + 321365 * 2 ^ 59
def prefixEnd_321365 : Nat := 4983230072969 + 3 ^ 40 * 321365 * 2
def baseEnd_321365 : Nat := 146679742695324792586289

theorem tailTrace_321365 : CollatzResearch.WordTrace tailWord_321365 prefixEnd_321365 146679742695324792586289 := by
  unfold tailWord_321365
  simp only [CollatzResearch.WordTrace]
  refine ⟨11721144480756964617509549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7814096320504643078339699 11721144480756964617509549)
  ·
    refine ⟨4395429180283861731566081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11721144480756964617509549 4395429180283861731566081)
    ·
      refine ⟨3296571885212896298674561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4395429180283861731566081 3296571885212896298674561)
      ·
        refine ⟨2472428913909672224005921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3296571885212896298674561 2472428913909672224005921)
        ·
          refine ⟨1854321685432254168004441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2472428913909672224005921 1854321685432254168004441)
          ·
            refine ⟨1390741264074190626003331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1854321685432254168004441 1390741264074190626003331)
            ·
              refine ⟨2086111896111285939004997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1390741264074190626003331 2086111896111285939004997)
              ·
                refine ⟨391145980520866113563437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2086111896111285939004997 391145980520866113563437)
                ·
                  refine ⟨146679742695324792586289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 391145980520866113563437 146679742695324792586289)
                  ·
                    rfl

theorem cell20_321365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 4, 3].length) (baseStart_321365 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_321365 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_321365 prefixEnd_321365 := by exact prefixLift 321365
  have htrace : WordTrace (prefixWord ++ tailWord_321365) baseStart_321365 baseEnd_321365 := by
    simpa [prefixWord, tailWord_321365, baseEnd_321365] using wordTrace_append hprefix tailTrace_321365
  have hstable : (prefixWord ++ tailWord_321365).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321365).length < 2 ^ (prefixWord ++ tailWord_321365).sum := by decide
  have hdescent : baseEnd_321365 < baseStart_321365 := by decide
  rcases family_descends (prefixWord ++ tailWord_321365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321493 : List Nat := [1, 3, 2, 3, 2, 1, 1, 7]
def baseStart_321493 : Nat := 118140960795 + 321493 * 2 ^ 59
def prefixEnd_321493 : Nat := 4983230072969 + 3 ^ 40 * 321493 * 2
def baseEnd_321493 : Nat := 48912721794375078773033

theorem tailTrace_321493 : CollatzResearch.WordTrace tailWord_321493 prefixEnd_321493 48912721794375078773033 := by
  unfold tailWord_321493
  simp only [CollatzResearch.WordTrace]
  refine ⟨11725813024293242478169133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7817208682862161652112755 11725813024293242478169133)
  ·
    refine ⟨4397179884109965929313425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11725813024293242478169133 4397179884109965929313425)
    ·
      refine ⟨3297884913082474446985069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4397179884109965929313425 3297884913082474446985069)
      ·
        refine ⟨1236706842405927917619401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3297884913082474446985069 1236706842405927917619401)
        ·
          refine ⟨927530131804445938214551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1236706842405927917619401 927530131804445938214551)
          ·
            refine ⟨1391295197706668907321827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 927530131804445938214551 1391295197706668907321827)
            ·
              refine ⟨2086942796560003360982741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1391295197706668907321827 2086942796560003360982741)
              ·
                refine ⟨48912721794375078773033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2086942796560003360982741 48912721794375078773033)
                ·
                  rfl

theorem cell20_321493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 7].length) (baseStart_321493 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_321493 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_321493 prefixEnd_321493 := by exact prefixLift 321493
  have htrace : WordTrace (prefixWord ++ tailWord_321493) baseStart_321493 baseEnd_321493 := by
    simpa [prefixWord, tailWord_321493, baseEnd_321493] using wordTrace_append hprefix tailTrace_321493
  have hstable : (prefixWord ++ tailWord_321493).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321493).length < 2 ^ (prefixWord ++ tailWord_321493).sum := by decide
  have hdescent : baseEnd_321493 < baseStart_321493 := by decide
  rcases family_descends (prefixWord ++ tailWord_321493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321534 : List Nat := [4, 2, 2, 2, 1, 1, 1, 4, 3]
def baseStart_321534 : Nat := 118140960795 + 321534 * 2 ^ 59
def prefixEnd_321534 : Nat := 4983230072969 + 3 ^ 40 * 321534 * 2
def baseEnd_321534 : Nat := 146756878900311315952265

theorem tailTrace_321534 : CollatzResearch.WordTrace tailWord_321534 prefixEnd_321534 146756878900311315952265 := by
  unfold tailWord_321534
  simp only [CollatzResearch.WordTrace]
  refine ⟨1465913552143088310051457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7818205611429804320274437 1465913552143088310051457)
  ·
    refine ⟨1099435164107316232538593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1465913552143088310051457 1099435164107316232538593)
    ·
      refine ⟨824576373080487174403945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1099435164107316232538593 824576373080487174403945)
      ·
        refine ⟨618432279810365380802959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 824576373080487174403945 618432279810365380802959)
        ·
          refine ⟨927648419715548071204439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 618432279810365380802959 927648419715548071204439)
          ·
            refine ⟨1391472629573322106806659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 927648419715548071204439 1391472629573322106806659)
            ·
              refine ⟨2087208944359983160209989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1391472629573322106806659 2087208944359983160209989)
              ·
                refine ⟨391351677067496842539373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2087208944359983160209989 391351677067496842539373)
                ·
                  refine ⟨146756878900311315952265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 391351677067496842539373 146756878900311315952265)
                  ·
                    rfl

theorem cell20_321534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 4, 3].length) (baseStart_321534 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_321534 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_321534 prefixEnd_321534 := by exact prefixLift 321534
  have htrace : WordTrace (prefixWord ++ tailWord_321534) baseStart_321534 baseEnd_321534 := by
    simpa [prefixWord, tailWord_321534, baseEnd_321534] using wordTrace_append hprefix tailTrace_321534
  have hstable : (prefixWord ++ tailWord_321534).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321534).length < 2 ^ (prefixWord ++ tailWord_321534).sum := by decide
  have hdescent : baseEnd_321534 < baseStart_321534 := by decide
  rcases family_descends (prefixWord ++ tailWord_321534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321541 : List Nat := [1, 3, 1, 1, 2, 5, 1, 4, 2]
def baseStart_321541 : Nat := 118140960795 + 321541 * 2 ^ 59
def prefixEnd_321541 : Nat := 4983230072969 + 3 ^ 40 * 321541 * 2
def baseEnd_321541 : Nat := 146760073891050402718903

theorem tailTrace_321541 : CollatzResearch.WordTrace tailWord_321541 prefixEnd_321541 146760073891050402718903 := by
  unfold tailWord_321541
  simp only [CollatzResearch.WordTrace]
  refine ⟨11727563728119346675916477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7818375818746231117277651 11727563728119346675916477)
  ·
    refine ⟨4397836398044755003468679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11727563728119346675916477 4397836398044755003468679)
    ·
      refine ⟨6596754597067132505203019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4397836398044755003468679 6596754597067132505203019)
      ·
        refine ⟨9895131895600698757804529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6596754597067132505203019 9895131895600698757804529)
        ·
          refine ⟨7421348921700524068353397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9895131895600698757804529 7421348921700524068353397)
          ·
            refine ⟨695751461409424131408131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7421348921700524068353397 695751461409424131408131)
            ·
              refine ⟨1043627192114136197112197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 695751461409424131408131 1043627192114136197112197)
              ·
                refine ⟨195680098521400536958537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1043627192114136197112197 195680098521400536958537)
                ·
                  refine ⟨146760073891050402718903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 195680098521400536958537 146760073891050402718903)
                  ·
                    rfl

theorem cell20_321541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 4, 2].length) (baseStart_321541 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_321541 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_321541 prefixEnd_321541 := by exact prefixLift 321541
  have htrace : WordTrace (prefixWord ++ tailWord_321541) baseStart_321541 baseEnd_321541 := by
    simpa [prefixWord, tailWord_321541, baseEnd_321541] using wordTrace_append hprefix tailTrace_321541
  have hstable : (prefixWord ++ tailWord_321541).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321541).length < 2 ^ (prefixWord ++ tailWord_321541).sum := by decide
  have hdescent : baseEnd_321541 < baseStart_321541 := by decide
  rcases family_descends (prefixWord ++ tailWord_321541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321562 : List Nat := [3, 1, 1, 3, 1, 4, 1, 2, 4]
def baseStart_321562 : Nat := 118140960795 + 321562 * 2 ^ 59
def prefixEnd_321562 : Nat := 4983230072969 + 3 ^ 40 * 321562 * 2
def baseEnd_321562 : Nat := 146769658863267663018817

theorem tailTrace_321562 : CollatzResearch.WordTrace tailWord_321562 prefixEnd_321562 146769658863267663018817 := by
  unfold tailWord_321562
  simp only [CollatzResearch.WordTrace]
  refine ⟨2932082415260816815607735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7818886440695511508287293 2932082415260816815607735)
  ·
    refine ⟨4398123622891225223411603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2932082415260816815607735 4398123622891225223411603)
    ·
      refine ⟨6597185434336837835117405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4398123622891225223411603 6597185434336837835117405)
      ·
        refine ⟨2473944537876314188169027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6597185434336837835117405 2473944537876314188169027)
        ·
          refine ⟨3710916806814471282253541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2473944537876314188169027 3710916806814471282253541)
          ·
            refine ⟨695796901277713365422539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3710916806814471282253541 695796901277713365422539)
            ·
              refine ⟨1043695351916570048133809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 695796901277713365422539 1043695351916570048133809)
              ·
                refine ⟨782771513937427536100357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1043695351916570048133809 782771513937427536100357)
                ·
                  refine ⟨146769658863267663018817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 782771513937427536100357 146769658863267663018817)
                  ·
                    rfl

theorem cell20_321562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 2, 4].length) (baseStart_321562 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_321562 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_321562 prefixEnd_321562 := by exact prefixLift 321562
  have htrace : WordTrace (prefixWord ++ tailWord_321562) baseStart_321562 baseEnd_321562 := by
    simpa [prefixWord, tailWord_321562, baseEnd_321562] using wordTrace_append hprefix tailTrace_321562
  have hstable : (prefixWord ++ tailWord_321562).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321562).length < 2 ^ (prefixWord ++ tailWord_321562).sum := by decide
  have hdescent : baseEnd_321562 < baseStart_321562 := by decide
  rcases family_descends (prefixWord ++ tailWord_321562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321575 : List Nat := [1, 1, 7, 1, 2, 1, 2, 3, 2]
def baseStart_321575 : Nat := 118140960795 + 321575 * 2 ^ 59
def prefixEnd_321575 : Nat := 4983230072969 + 3 ^ 40 * 321575 * 2
def baseEnd_321575 : Nat := 146775592417497395585431

theorem tailTrace_321575 : CollatzResearch.WordTrace tailWord_321575 prefixEnd_321575 146775592417497395585431 := by
  unfold tailWord_321575
  simp only [CollatzResearch.WordTrace]
  refine ⟨11728803809996170482654179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7819202539997446988436119 11728803809996170482654179)
  ·
    refine ⟨17593205714994255723981269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11728803809996170482654179 17593205714994255723981269)
    ·
      refine ⟨412340758945177868530811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 17593205714994255723981269 412340758945177868530811)
      ·
        refine ⟨618511138417766802796217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 412340758945177868530811 618511138417766802796217)
        ·
          refine ⟨463883353813325102097163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 618511138417766802796217 463883353813325102097163)
          ·
            refine ⟨695825030719987653145745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 463883353813325102097163 695825030719987653145745)
            ·
              refine ⟨521868773039990739859309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 695825030719987653145745 521868773039990739859309)
              ·
                refine ⟨195700789889996527447241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 521868773039990739859309 195700789889996527447241)
                ·
                  refine ⟨146775592417497395585431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 195700789889996527447241 146775592417497395585431)
                  ·
                    rfl

theorem cell20_321575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 2, 3, 2].length) (baseStart_321575 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_321575 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_321575 prefixEnd_321575 := by exact prefixLift 321575
  have htrace : WordTrace (prefixWord ++ tailWord_321575) baseStart_321575 baseEnd_321575 := by
    simpa [prefixWord, tailWord_321575, baseEnd_321575] using wordTrace_append hprefix tailTrace_321575
  have hstable : (prefixWord ++ tailWord_321575).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321575).length < 2 ^ (prefixWord ++ tailWord_321575).sum := by decide
  have hdescent : baseEnd_321575 < baseStart_321575 := by decide
  rcases family_descends (prefixWord ++ tailWord_321575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321593 : List Nat := [1, 2, 1, 5, 3, 1, 1, 1, 5]
def baseStart_321593 : Nat := 118140960795 + 321593 * 2 ^ 59
def prefixEnd_321593 : Nat := 4983230072969 + 3 ^ 40 * 321593 * 2
def baseEnd_321593 : Nat := 146783808107969332985357

theorem tailTrace_321593 : CollatzResearch.WordTrace tailWord_321593 prefixEnd_321593 146783808107969332985357 := by
  unfold tailWord_321593
  simp only [CollatzResearch.WordTrace]
  refine ⟨11729460323930959556809433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7819640215953973037872955 11729460323930959556809433)
  ·
    refine ⟨8797095242948219667607075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11729460323930959556809433 8797095242948219667607075)
    ·
      refine ⟨13195642864422329501410613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8797095242948219667607075 13195642864422329501410613)
      ·
        refine ⟨1237091518539593390757245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13195642864422329501410613 1237091518539593390757245)
        ·
          refine ⟨463909319452347521533967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1237091518539593390757245 463909319452347521533967)
          ·
            refine ⟨695863979178521282300951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 463909319452347521533967 695863979178521282300951)
            ·
              refine ⟨1043795968767781923451427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 695863979178521282300951 1043795968767781923451427)
              ·
                refine ⟨1565693953151672885177141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1043795968767781923451427 1565693953151672885177141)
                ·
                  refine ⟨146783808107969332985357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1565693953151672885177141 146783808107969332985357)
                  ·
                    rfl

theorem cell20_321593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 1, 5].length) (baseStart_321593 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_321593 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_321593 prefixEnd_321593 := by exact prefixLift 321593
  have htrace : WordTrace (prefixWord ++ tailWord_321593) baseStart_321593 baseEnd_321593 := by
    simpa [prefixWord, tailWord_321593, baseEnd_321593] using wordTrace_append hprefix tailTrace_321593
  have hstable : (prefixWord ++ tailWord_321593).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321593).length < 2 ^ (prefixWord ++ tailWord_321593).sum := by decide
  have hdescent : baseEnd_321593 < baseStart_321593 := by decide
  rcases family_descends (prefixWord ++ tailWord_321593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321600 : List Nat := [2, 1, 1, 2, 2, 5, 2, 1, 4]
def baseStart_321600 : Nat := 118140960795 + 321600 * 2 ^ 59
def prefixEnd_321600 : Nat := 4983230072969 + 3 ^ 40 * 321600 * 2
def baseEnd_321600 : Nat := 146787003098708419751995

theorem tailTrace_321600 : CollatzResearch.WordTrace tailWord_321600 prefixEnd_321600 146787003098708419751995 := by
  unfold tailWord_321600
  simp only [CollatzResearch.WordTrace]
  refine ⟨5864857817452799876157127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7819810423270399834876169 5864857817452799876157127)
  ·
    refine ⟨8797286726179199814235691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5864857817452799876157127 8797286726179199814235691)
    ·
      refine ⟨13195930089268799721353537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8797286726179199814235691 13195930089268799721353537)
      ·
        refine ⟨9896947566951599791015153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13195930089268799721353537 9896947566951599791015153)
        ·
          refine ⟨7422710675213699843261365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9896947566951599791015153 7422710675213699843261365)
          ·
            refine ⟨695879125801284360305753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7422710675213699843261365 695879125801284360305753)
            ·
              refine ⟨521909344350963270229315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 695879125801284360305753 521909344350963270229315)
              ·
                refine ⟨782864016526444905343973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 521909344350963270229315 782864016526444905343973)
                ·
                  refine ⟨146787003098708419751995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 782864016526444905343973 146787003098708419751995)
                  ·
                    rfl

theorem cell20_321600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 2, 1, 4].length) (baseStart_321600 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_321600 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_321600 prefixEnd_321600 := by exact prefixLift 321600
  have htrace : WordTrace (prefixWord ++ tailWord_321600) baseStart_321600 baseEnd_321600 := by
    simpa [prefixWord, tailWord_321600, baseEnd_321600] using wordTrace_append hprefix tailTrace_321600
  have hstable : (prefixWord ++ tailWord_321600).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321600).length < 2 ^ (prefixWord ++ tailWord_321600).sum := by decide
  have hdescent : baseEnd_321600 < baseStart_321600 := by decide
  rcases family_descends (prefixWord ++ tailWord_321600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321624 : List Nat := [2, 1, 2, 2, 1, 6, 2, 4]
def baseStart_321624 : Nat := 118140960795 + 321624 * 2 ^ 59
def prefixEnd_321624 : Nat := 4983230072969 + 3 ^ 40 * 321624 * 2
def baseEnd_321624 : Nat := 48932652450890334317299

theorem tailTrace_321624 : CollatzResearch.WordTrace tailWord_321624 prefixEnd_321624 48932652450890334317299 := by
  unfold tailWord_321624
  simp only [CollatzResearch.WordTrace]
  refine ⟨5865295493409325925593963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7820393991212434567458617 5865295493409325925593963)
  ·
    refine ⟨8797943240113988888390945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5865295493409325925593963 8797943240113988888390945)
    ·
      refine ⟨6598457430085491666293209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8797943240113988888390945 6598457430085491666293209)
      ·
        refine ⟨4948843072564118749719907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6598457430085491666293209 4948843072564118749719907)
        ·
          refine ⟨7423264608846178124579861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4948843072564118749719907 7423264608846178124579861)
          ·
            refine ⟨347965528539664599589681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 7423264608846178124579861 347965528539664599589681)
            ·
              refine ⟨260974146404748449692261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 347965528539664599589681 260974146404748449692261)
              ·
                refine ⟨48932652450890334317299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 260974146404748449692261 48932652450890334317299)
                ·
                  rfl

theorem cell20_321624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 2, 4].length) (baseStart_321624 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_321624 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_321624 prefixEnd_321624 := by exact prefixLift 321624
  have htrace : WordTrace (prefixWord ++ tailWord_321624) baseStart_321624 baseEnd_321624 := by
    simpa [prefixWord, tailWord_321624, baseEnd_321624] using wordTrace_append hprefix tailTrace_321624
  have hstable : (prefixWord ++ tailWord_321624).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321624).length < 2 ^ (prefixWord ++ tailWord_321624).sum := by decide
  have hdescent : baseEnd_321624 < baseStart_321624 := by decide
  rcases family_descends (prefixWord ++ tailWord_321624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321665 : List Nat := [1, 2, 4, 2, 3, 2, 2, 1, 3]
def baseStart_321665 : Nat := 118140960795 + 321665 * 2 ^ 59
def prefixEnd_321665 : Nat := 4983230072969 + 3 ^ 40 * 321665 * 2
def baseEnd_321665 : Nat := 146816670869857082585063

theorem tailTrace_321665 : CollatzResearch.WordTrace tailWord_321665 prefixEnd_321665 146816670869857082585063 := by
  unfold tailWord_321665
  simp only [CollatzResearch.WordTrace]
  refine ⟨11732086379670115853430449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7821390919780077235620299 11732086379670115853430449)
  ·
    refine ⟨8799064784752586890072837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11732086379670115853430449 8799064784752586890072837)
    ·
      refine ⟨1649824647141110041888657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8799064784752586890072837 1649824647141110041888657)
      ·
        refine ⟨1237368485355832531416493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1649824647141110041888657 1237368485355832531416493)
        ·
          refine ⟨464013182008437199281185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1237368485355832531416493 464013182008437199281185)
          ·
            refine ⟨348009886506327899460889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 464013182008437199281185 348009886506327899460889)
            ·
              refine ⟨261007414879745924595667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 348009886506327899460889 261007414879745924595667)
              ·
                refine ⟨391511122319618886893501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 261007414879745924595667 391511122319618886893501)
                ·
                  refine ⟨146816670869857082585063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 391511122319618886893501 146816670869857082585063)
                  ·
                    rfl

theorem cell20_321665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 2, 1, 3].length) (baseStart_321665 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_321665 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_321665 prefixEnd_321665 := by exact prefixLift 321665
  have htrace : WordTrace (prefixWord ++ tailWord_321665) baseStart_321665 baseEnd_321665 := by
    simpa [prefixWord, tailWord_321665, baseEnd_321665] using wordTrace_append hprefix tailTrace_321665
  have hstable : (prefixWord ++ tailWord_321665).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321665).length < 2 ^ (prefixWord ++ tailWord_321665).sum := by decide
  have hdescent : baseEnd_321665 < baseStart_321665 := by decide
  rcases family_descends (prefixWord ++ tailWord_321665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321669 : List Nat := [1, 3, 1, 1, 5, 2, 1, 3, 3]
def baseStart_321669 : Nat := 118140960795 + 321669 * 2 ^ 59
def prefixEnd_321669 : Nat := 4983230072969 + 3 ^ 40 * 321669 * 2
def baseEnd_321669 : Nat := 146818496578850846451713

theorem tailTrace_321669 : CollatzResearch.WordTrace tailWord_321669 prefixEnd_321669 146818496578850846451713 := by
  unfold tailWord_321669
  simp only [CollatzResearch.WordTrace]
  refine ⟨11732232271655624536576061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7821488181103749691050707 11732232271655624536576061)
  ·
    refine ⟨4399587101870859201216023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11732232271655624536576061 4399587101870859201216023)
    ·
      refine ⟨6599380652806288801824035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4399587101870859201216023 6599380652806288801824035)
      ·
        refine ⟨9899070979209433202736053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6599380652806288801824035 9899070979209433202736053)
        ·
          refine ⟨928037904300884362756505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9899070979209433202736053 928037904300884362756505)
          ·
            refine ⟨696028428225663272067379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 928037904300884362756505 696028428225663272067379)
            ·
              refine ⟨1044042642338494908101069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 696028428225663272067379 1044042642338494908101069)
              ·
                refine ⟨391515990876935590537901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1044042642338494908101069 391515990876935590537901)
                ·
                  refine ⟨146818496578850846451713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 391515990876935590537901 146818496578850846451713)
                  ·
                    rfl

theorem cell20_321669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 3, 3].length) (baseStart_321669 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_321669 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_321669 prefixEnd_321669 := by exact prefixLift 321669
  have htrace : WordTrace (prefixWord ++ tailWord_321669) baseStart_321669 baseEnd_321669 := by
    simpa [prefixWord, tailWord_321669, baseEnd_321669] using wordTrace_append hprefix tailTrace_321669
  have hstable : (prefixWord ++ tailWord_321669).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321669).length < 2 ^ (prefixWord ++ tailWord_321669).sum := by decide
  have hdescent : baseEnd_321669 < baseStart_321669 := by decide
  rcases family_descends (prefixWord ++ tailWord_321669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321706 : List Nat := [3, 1, 5, 1, 2, 2, 2, 2, 2]
def baseStart_321706 : Nat := 118140960795 + 321706 * 2 ^ 59
def prefixEnd_321706 : Nat := 4983230072969 + 3 ^ 40 * 321706 * 2
def baseEnd_321706 : Nat := 146835384387043162218229

theorem tailTrace_321706 : CollatzResearch.WordTrace tailWord_321706 prefixEnd_321706 146835384387043162218229 := by
  unfold tailWord_321706
  simp only [CollatzResearch.WordTrace]
  refine ⟨2933395443130394963918243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7822387848347719903781981 2933395443130394963918243)
  ·
    refine ⟨4400093164695592445877365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2933395443130394963918243 4400093164695592445877365)
    ·
      refine ⟨412508734190211791801003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4400093164695592445877365 412508734190211791801003)
      ·
        refine ⟨618763101285317687701505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 412508734190211791801003 618763101285317687701505)
        ·
          refine ⟨464072325963988265776129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 618763101285317687701505 464072325963988265776129)
          ·
            refine ⟨348054244472991199332097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 464072325963988265776129 348054244472991199332097)
            ·
              refine ⟨261040683354743399499073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 348054244472991199332097 261040683354743399499073)
              ·
                refine ⟨195780512516057549624305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 261040683354743399499073 195780512516057549624305)
                ·
                  refine ⟨146835384387043162218229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 195780512516057549624305 146835384387043162218229)
                  ·
                    rfl

theorem cell20_321706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 2, 2, 2].length) (baseStart_321706 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_321706 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_321706 prefixEnd_321706 := by exact prefixLift 321706
  have htrace : WordTrace (prefixWord ++ tailWord_321706) baseStart_321706 baseEnd_321706 := by
    simpa [prefixWord, tailWord_321706, baseEnd_321706] using wordTrace_append hprefix tailTrace_321706
  have hstable : (prefixWord ++ tailWord_321706).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321706).length < 2 ^ (prefixWord ++ tailWord_321706).sum := by decide
  have hdescent : baseEnd_321706 < baseStart_321706 := by decide
  rcases family_descends (prefixWord ++ tailWord_321706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321717 : List Nat := [1, 3, 3, 4, 1, 2, 1, 5]
def baseStart_321717 : Nat := 118140960795 + 321717 * 2 ^ 59
def prefixEnd_321717 : Nat := 4983230072969 + 3 ^ 40 * 321717 * 2
def baseEnd_321717 : Nat := 48946801695592004283839

theorem tailTrace_321717 : CollatzResearch.WordTrace tailWord_321717 prefixEnd_321717 48946801695592004283839 := by
  unfold tailWord_321717
  simp only [CollatzResearch.WordTrace]
  refine ⟨11733982975481728734323405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7822655316987819156215603 11733982975481728734323405)
  ·
    refine ⟨4400243615805648275371277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11733982975481728734323405 4400243615805648275371277)
    ·
      refine ⟨1650091355927118103264229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4400243615805648275371277 1650091355927118103264229)
      ·
        refine ⟨309392129236334644362043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1650091355927118103264229 309392129236334644362043)
        ·
          refine ⟨464088193854501966543065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 309392129236334644362043 464088193854501966543065)
          ·
            refine ⟨348066145390876474907299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 464088193854501966543065 348066145390876474907299)
            ·
              refine ⟨522099218086314712360949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 348066145390876474907299 522099218086314712360949)
              ·
                refine ⟨48946801695592004283839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 522099218086314712360949 48946801695592004283839)
                ·
                  rfl

theorem cell20_321717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 1, 5].length) (baseStart_321717 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_321717 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_321717 prefixEnd_321717 := by exact prefixLift 321717
  have htrace : WordTrace (prefixWord ++ tailWord_321717) baseStart_321717 baseEnd_321717 := by
    simpa [prefixWord, tailWord_321717, baseEnd_321717] using wordTrace_append hprefix tailTrace_321717
  have hstable : (prefixWord ++ tailWord_321717).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321717).length < 2 ^ (prefixWord ++ tailWord_321717).sum := by decide
  have hdescent : baseEnd_321717 < baseStart_321717 := by decide
  rcases family_descends (prefixWord ++ tailWord_321717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321790 : List Nat := [4, 2, 2, 1, 1, 1, 1, 4, 4]
def baseStart_321790 : Nat := 118140960795 + 321790 * 2 ^ 59
def prefixEnd_321790 : Nat := 4983230072969 + 3 ^ 40 * 321790 * 2
def baseEnd_321790 : Nat := 146873724275912203417885

theorem tailTrace_321790 : CollatzResearch.WordTrace tailWord_321790 prefixEnd_321790 146873724275912203417885 := by
  unfold tailWord_321790
  simp only [CollatzResearch.WordTrace]
  refine ⟨1467080688027157775216353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7824430336144841467820549 1467080688027157775216353)
  ·
    refine ⟨1100310516020368331412265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1467080688027157775216353 1100310516020368331412265)
    ·
      refine ⟨825232887015276248559199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1100310516020368331412265 825232887015276248559199)
      ·
        refine ⟨1237849330522914372838799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 825232887015276248559199 1237849330522914372838799)
        ·
          refine ⟨1856773995784371559258199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1237849330522914372838799 1856773995784371559258199)
          ·
            refine ⟨2785160993676557338887299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1856773995784371559258199 2785160993676557338887299)
            ·
              refine ⟨4177741490514836008330949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2785160993676557338887299 4177741490514836008330949)
              ·
                refine ⟨783326529471531751562053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4177741490514836008330949 783326529471531751562053)
                ·
                  refine ⟨146873724275912203417885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 783326529471531751562053 146873724275912203417885)
                  ·
                    rfl

theorem cell20_321790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_321790 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_321790 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_321790 prefixEnd_321790 := by exact prefixLift 321790
  have htrace : WordTrace (prefixWord ++ tailWord_321790) baseStart_321790 baseEnd_321790 := by
    simpa [prefixWord, tailWord_321790, baseEnd_321790] using wordTrace_append hprefix tailTrace_321790
  have hstable : (prefixWord ++ tailWord_321790).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321790).length < 2 ^ (prefixWord ++ tailWord_321790).sum := by decide
  have hdescent : baseEnd_321790 < baseStart_321790 := by decide
  rcases family_descends (prefixWord ++ tailWord_321790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321824 : List Nat := [2, 1, 1, 5, 2, 2, 3, 2, 2]
def baseStart_321824 : Nat := 118140960795 + 321824 * 2 ^ 59
def prefixEnd_321824 : Nat := 4983230072969 + 3 ^ 40 * 321824 * 2
def baseEnd_321824 : Nat := 146889242802359196284413

theorem tailTrace_321824 : CollatzResearch.WordTrace tailWord_321824 prefixEnd_321824 146889242802359196284413 := by
  unfold tailWord_321824
  simp only [CollatzResearch.WordTrace]
  refine ⟨5868942793047043004234263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7825257057396057338979017 5868942793047043004234263)
  ·
    refine ⟨8803414189570564506351395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5868942793047043004234263 8803414189570564506351395)
    ·
      refine ⟨13205121284355846759527093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8803414189570564506351395 13205121284355846759527093)
      ·
        refine ⟨1237980120408360633705665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13205121284355846759527093 1237980120408360633705665)
        ·
          refine ⟨928485090306270475279249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1237980120408360633705665 928485090306270475279249)
          ·
            refine ⟨696363817729702856459437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 928485090306270475279249 696363817729702856459437)
            ·
              refine ⟨261136431648638571172289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 696363817729702856459437 261136431648638571172289)
              ·
                refine ⟨195852323736478928379217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 261136431648638571172289 195852323736478928379217)
                ·
                  refine ⟨146889242802359196284413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 195852323736478928379217 146889242802359196284413)
                  ·
                    rfl

theorem cell20_321824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 3, 2, 2].length) (baseStart_321824 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_321824 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_321824 prefixEnd_321824 := by exact prefixLift 321824
  have htrace : WordTrace (prefixWord ++ tailWord_321824) baseStart_321824 baseEnd_321824 := by
    simpa [prefixWord, tailWord_321824, baseEnd_321824] using wordTrace_append hprefix tailTrace_321824
  have hstable : (prefixWord ++ tailWord_321824).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321824).length < 2 ^ (prefixWord ++ tailWord_321824).sum := by decide
  have hdescent : baseEnd_321824 < baseStart_321824 := by decide
  rcases family_descends (prefixWord ++ tailWord_321824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321828 : List Nat := [2, 3, 1, 3, 1, 2, 3, 1, 4]
def baseStart_321828 : Nat := 118140960795 + 321828 * 2 ^ 59
def prefixEnd_321828 : Nat := 4983230072969 + 3 ^ 40 * 321828 * 2
def baseEnd_321828 : Nat := 146891068511352960151063

theorem tailTrace_321828 : CollatzResearch.WordTrace tailWord_321828 prefixEnd_321828 146891068511352960151063 := by
  unfold tailWord_321828
  simp only [CollatzResearch.WordTrace]
  refine ⟨5869015739039797345807069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7825354318719729794409425 5869015739039797345807069)
  ·
    refine ⟨2200880902139924004677651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5869015739039797345807069 2200880902139924004677651)
    ·
      refine ⟨3301321353209886007016477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2200880902139924004677651 3301321353209886007016477)
      ·
        refine ⟨1237995507453707252631179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3301321353209886007016477 1237995507453707252631179)
        ·
          refine ⟨1856993261180560878946769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1237995507453707252631179 1856993261180560878946769)
          ·
            refine ⟨1392744945885420659210077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1856993261180560878946769 1392744945885420659210077)
            ·
              refine ⟨522279354707032747203779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1392744945885420659210077 522279354707032747203779)
              ·
                refine ⟨783419032060549120805669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 522279354707032747203779 783419032060549120805669)
                ·
                  refine ⟨146891068511352960151063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 783419032060549120805669 146891068511352960151063)
                  ·
                    rfl

theorem cell20_321828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 3, 1, 4].length) (baseStart_321828 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_321828 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_321828 prefixEnd_321828 := by exact prefixLift 321828
  have htrace : WordTrace (prefixWord ++ tailWord_321828) baseStart_321828 baseEnd_321828 := by
    simpa [prefixWord, tailWord_321828, baseEnd_321828] using wordTrace_append hprefix tailTrace_321828
  have hstable : (prefixWord ++ tailWord_321828).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321828).length < 2 ^ (prefixWord ++ tailWord_321828).sum := by decide
  have hdescent : baseEnd_321828 < baseStart_321828 := by decide
  rcases family_descends (prefixWord ++ tailWord_321828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321834 : List Nat := [3, 1, 4, 2, 3, 1, 2, 1, 3]
def baseStart_321834 : Nat := 118140960795 + 321834 * 2 ^ 59
def prefixEnd_321834 : Nat := 4983230072969 + 3 ^ 40 * 321834 * 2
def baseEnd_321834 : Nat := 146893807074843605951039

theorem tailTrace_321834 : CollatzResearch.WordTrace tailWord_321834 prefixEnd_321834 146893807074843605951039 := by
  unfold tailWord_321834
  simp only [CollatzResearch.WordTrace]
  refine ⟨2934562579014464429083139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7825500210705238477555037 2934562579014464429083139)
  ·
    refine ⟨4401843868521696643624709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2934562579014464429083139 4401843868521696643624709)
    ·
      refine ⟨825345725347818120679633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4401843868521696643624709 825345725347818120679633)
      ·
        refine ⟨619009294010863590509725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 825345725347818120679633 619009294010863590509725)
        ·
          refine ⟨232128485254073846441147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 619009294010863590509725 232128485254073846441147)
          ·
            refine ⟨348192727881110769661721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 232128485254073846441147 348192727881110769661721)
            ·
              refine ⟨261144545910833077246291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 348192727881110769661721 261144545910833077246291)
              ·
                refine ⟨391716818866249615869437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 261144545910833077246291 391716818866249615869437)
                ·
                  refine ⟨146893807074843605951039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 391716818866249615869437 146893807074843605951039)
                  ·
                    rfl

theorem cell20_321834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 2, 1, 3].length) (baseStart_321834 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_321834 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_321834 prefixEnd_321834 := by exact prefixLift 321834
  have htrace : WordTrace (prefixWord ++ tailWord_321834) baseStart_321834 baseEnd_321834 := by
    simpa [prefixWord, tailWord_321834, baseEnd_321834] using wordTrace_append hprefix tailTrace_321834
  have hstable : (prefixWord ++ tailWord_321834).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321834).length < 2 ^ (prefixWord ++ tailWord_321834).sum := by decide
  have hdescent : baseEnd_321834 < baseStart_321834 := by decide
  rcases family_descends (prefixWord ++ tailWord_321834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321890 : List Nat := [3, 3, 2, 1, 1, 4, 1, 5]
def baseStart_321890 : Nat := 118140960795 + 321890 * 2 ^ 59
def prefixEnd_321890 : Nat := 4983230072969 + 3 ^ 40 * 321890 * 2
def baseEnd_321890 : Nat := 48973122333585433361381

theorem tailTrace_321890 : CollatzResearch.WordTrace tailWord_321890 prefixEnd_321890 48973122333585433361381 := by
  unfold tailWord_321890
  simp only [CollatzResearch.WordTrace]
  refine ⟨2935073200963744820092781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7826861869236652853580749 2935073200963744820092781)
  ·
    refine ⟨1100652450361404307534793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2935073200963744820092781 1100652450361404307534793)
    ·
      refine ⟨825489337771053230651095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1100652450361404307534793 825489337771053230651095)
      ·
        refine ⟨1238234006656579845976643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 825489337771053230651095 1238234006656579845976643)
        ·
          refine ⟨1857351009984869768964965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1238234006656579845976643 1857351009984869768964965)
          ·
            refine ⟨348253314372163081680931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1857351009984869768964965 348253314372163081680931)
            ·
              refine ⟨522379971558244622521397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 348253314372163081680931 522379971558244622521397)
              ·
                refine ⟨48973122333585433361381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 522379971558244622521397 48973122333585433361381)
                ·
                  rfl

theorem cell20_321890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 1, 5].length) (baseStart_321890 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_321890 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_321890 prefixEnd_321890 := by exact prefixLift 321890
  have htrace : WordTrace (prefixWord ++ tailWord_321890) baseStart_321890 baseEnd_321890 := by
    simpa [prefixWord, tailWord_321890, baseEnd_321890] using wordTrace_append hprefix tailTrace_321890
  have hstable : (prefixWord ++ tailWord_321890).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321890).length < 2 ^ (prefixWord ++ tailWord_321890).sum := by decide
  have hdescent : baseEnd_321890 < baseStart_321890 := by decide
  rcases family_descends (prefixWord ++ tailWord_321890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321921 : List Nat := [1, 2, 4, 3, 1, 1, 1, 5, 2]
def baseStart_321921 : Nat := 118140960795 + 321921 * 2 ^ 59
def prefixEnd_321921 : Nat := 4983230072969 + 3 ^ 40 * 321921 * 2
def baseEnd_321921 : Nat := 146933516245457970050683

theorem tailTrace_321921 : CollatzResearch.WordTrace tailWord_321921 prefixEnd_321921 146933516245457970050683 := by
  unfold tailWord_321921
  simp only [CollatzResearch.WordTrace]
  refine ⟨11741423466742671574749617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7827615644495114383166411 11741423466742671574749617)
  ·
    refine ⟨8806067600057003681062213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11741423466742671574749617 8806067600057003681062213)
    ·
      refine ⟨1651137675010688190199165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8806067600057003681062213 1651137675010688190199165)
      ·
        refine ⟨619176628129008071324687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1651137675010688190199165 619176628129008071324687)
        ·
          refine ⟨928764942193512106987031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 619176628129008071324687 928764942193512106987031)
          ·
            refine ⟨1393147413290268160480547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 928764942193512106987031 1393147413290268160480547)
            ·
              refine ⟨2089721119935402240720821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1393147413290268160480547 2089721119935402240720821)
              ·
                refine ⟨195911354993943960067577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2089721119935402240720821 195911354993943960067577)
                ·
                  refine ⟨146933516245457970050683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 195911354993943960067577 146933516245457970050683)
                  ·
                    rfl

theorem cell20_321921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 5, 2].length) (baseStart_321921 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_321921 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_321921 prefixEnd_321921 := by exact prefixLift 321921
  have htrace : WordTrace (prefixWord ++ tailWord_321921) baseStart_321921 baseEnd_321921 := by
    simpa [prefixWord, tailWord_321921, baseEnd_321921] using wordTrace_append hprefix tailTrace_321921
  have hstable : (prefixWord ++ tailWord_321921).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321921).length < 2 ^ (prefixWord ++ tailWord_321921).sum := by decide
  have hdescent : baseEnd_321921 < baseStart_321921 := by decide
  rcases family_descends (prefixWord ++ tailWord_321921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321932 : List Nat := [2, 2, 1, 2, 1, 5, 7]
def baseStart_321932 : Nat := 118140960795 + 321932 * 2 ^ 59
def prefixEnd_321932 : Nat := 4983230072969 + 3 ^ 40 * 321932 * 2
def baseEnd_321932 : Nat := 16326504105021202298219

theorem tailTrace_321932 : CollatzResearch.WordTrace tailWord_321932 prefixEnd_321932 16326504105021202298219 := by
  unfold tailWord_321932
  simp only [CollatzResearch.WordTrace]
  refine ⟨5870912334851410226700025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7827883113135213635600033 5870912334851410226700025)
  ·
    refine ⟨4403184251138557670025019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5870912334851410226700025 4403184251138557670025019)
    ·
      refine ⟨6604776376707836505037529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4403184251138557670025019 6604776376707836505037529)
      ·
        refine ⟨4953582282530877378778147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6604776376707836505037529 4953582282530877378778147)
        ·
          refine ⟨7430373423796316068167221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4953582282530877378778147 7430373423796316068167221)
          ·
            refine ⟨696597508480904631390677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7430373423796316068167221 696597508480904631390677)
            ·
              refine ⟨16326504105021202298219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 696597508480904631390677 16326504105021202298219)
              ·
                rfl

theorem cell20_321932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 7].length) (baseStart_321932 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_321932 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_321932 prefixEnd_321932 := by exact prefixLift 321932
  have htrace : WordTrace (prefixWord ++ tailWord_321932) baseStart_321932 baseEnd_321932 := by
    simpa [prefixWord, tailWord_321932, baseEnd_321932] using wordTrace_append hprefix tailTrace_321932
  have hstable : (prefixWord ++ tailWord_321932).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321932).length < 2 ^ (prefixWord ++ tailWord_321932).sum := by decide
  have hdescent : baseEnd_321932 < baseStart_321932 := by decide
  rcases family_descends (prefixWord ++ tailWord_321932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321956 : List Nat := [2, 3, 1, 2, 1, 1, 2, 5, 3]
def baseStart_321956 : Nat := 118140960795 + 321956 * 2 ^ 59
def prefixEnd_321956 : Nat := 4983230072969 + 3 ^ 40 * 321956 * 2
def baseEnd_321956 : Nat := 146949491199153403883873

theorem tailTrace_321956 : CollatzResearch.WordTrace tailWord_321956 prefixEnd_321956 146949491199153403883873 := by
  unfold tailWord_321956
  simp only [CollatzResearch.WordTrace]
  refine ⟨5871350010807936276136861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7828466681077248368182481 5871350010807936276136861)
  ·
    refine ⟨2201756254052976103551323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5871350010807936276136861 2201756254052976103551323)
    ·
      refine ⟨3302634381079464155326985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2201756254052976103551323 3302634381079464155326985)
      ·
        refine ⟨2476975785809598116495239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3302634381079464155326985 2476975785809598116495239)
        ·
          refine ⟨3715463678714397174742859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2476975785809598116495239 3715463678714397174742859)
          ·
            refine ⟨5573195518071595762114289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3715463678714397174742859 5573195518071595762114289)
            ·
              refine ⟨4179896638553696821585717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5573195518071595762114289 4179896638553696821585717)
              ·
                refine ⟨391865309864409077023661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4179896638553696821585717 391865309864409077023661)
                ·
                  refine ⟨146949491199153403883873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 391865309864409077023661 146949491199153403883873)
                  ·
                    rfl

theorem cell20_321956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 5, 3].length) (baseStart_321956 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_321956 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_321956 prefixEnd_321956 := by exact prefixLift 321956
  have htrace : WordTrace (prefixWord ++ tailWord_321956) baseStart_321956 baseEnd_321956 := by
    simpa [prefixWord, tailWord_321956, baseEnd_321956] using wordTrace_append hprefix tailTrace_321956
  have hstable : (prefixWord ++ tailWord_321956).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321956).length < 2 ^ (prefixWord ++ tailWord_321956).sum := by decide
  have hdescent : baseEnd_321956 < baseStart_321956 := by decide
  rcases family_descends (prefixWord ++ tailWord_321956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321970 : List Nat := [3, 2, 1, 1, 1, 1, 5, 6]
def baseStart_321970 : Nat := 118140960795 + 321970 * 2 ^ 59
def prefixEnd_321970 : Nat := 4983230072969 + 3 ^ 40 * 321970 * 2
def baseEnd_321970 : Nat := 48985293726877192472383

theorem tailTrace_321970 : CollatzResearch.WordTrace tailWord_321970 prefixEnd_321970 48985293726877192472383 := by
  unfold tailWord_321970
  simp only [CollatzResearch.WordTrace]
  refine ⟨2935802660891288235820841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7828807095710101962188909 2935802660891288235820841)
  ·
    refine ⟨2201851995668466176865631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2935802660891288235820841 2201851995668466176865631)
    ·
      refine ⟨3302777993502699265298447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2201851995668466176865631 3302777993502699265298447)
      ·
        refine ⟨4954166990254048897947671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3302777993502699265298447 4954166990254048897947671)
        ·
          refine ⟨7431250485381073346921507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4954166990254048897947671 7431250485381073346921507)
          ·
            refine ⟨11146875728071610020382261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7431250485381073346921507 11146875728071610020382261)
            ·
              refine ⟨1045019599506713439410837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11146875728071610020382261 1045019599506713439410837)
              ·
                refine ⟨48985293726877192472383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1045019599506713439410837 48985293726877192472383)
                ·
                  rfl

theorem cell20_321970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 6].length) (baseStart_321970 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_321970 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_321970 prefixEnd_321970 := by exact prefixLift 321970
  have htrace : WordTrace (prefixWord ++ tailWord_321970) baseStart_321970 baseEnd_321970 := by
    simpa [prefixWord, tailWord_321970, baseEnd_321970] using wordTrace_append hprefix tailTrace_321970
  have hstable : (prefixWord ++ tailWord_321970).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321970).length < 2 ^ (prefixWord ++ tailWord_321970).sum := by decide
  have hdescent : baseEnd_321970 < baseStart_321970 := by decide
  rcases family_descends (prefixWord ++ tailWord_321970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321972 : List Nat := [2, 5, 2, 2, 1, 2, 1, 3, 2]
def baseStart_321972 : Nat := 118140960795 + 321972 * 2 ^ 59
def prefixEnd_321972 : Nat := 4983230072969 + 3 ^ 40 * 321972 * 2
def baseEnd_321972 : Nat := 146956794035128459350475

theorem tailTrace_321972 : CollatzResearch.WordTrace tailWord_321972 prefixEnd_321972 146956794035128459350475 := by
  unfold tailWord_321972
  simp only [CollatzResearch.WordTrace]
  refine ⟨5871641794778953642428085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7828855726371938189904113 5871641794778953642428085)
  ·
    refine ⟨550466418260526903977633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5871641794778953642428085 550466418260526903977633)
    ·
      refine ⟨412849813695395177983225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 550466418260526903977633 412849813695395177983225)
      ·
        refine ⟨309637360271546383487419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 412849813695395177983225 309637360271546383487419)
        ·
          refine ⟨464456040407319575231129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 309637360271546383487419 464456040407319575231129)
          ·
            refine ⟨348342030305489681423347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 464456040407319575231129 348342030305489681423347)
            ·
              refine ⟨522513045458234522135021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 348342030305489681423347 522513045458234522135021)
              ·
                refine ⟨195942392046837945800633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 522513045458234522135021 195942392046837945800633)
                ·
                  refine ⟨146956794035128459350475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 195942392046837945800633 146956794035128459350475)
                  ·
                    rfl

theorem cell20_321972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 1, 3, 2].length) (baseStart_321972 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_321972 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_321972 prefixEnd_321972 := by exact prefixLift 321972
  have htrace : WordTrace (prefixWord ++ tailWord_321972) baseStart_321972 baseEnd_321972 := by
    simpa [prefixWord, tailWord_321972, baseEnd_321972] using wordTrace_append hprefix tailTrace_321972
  have hstable : (prefixWord ++ tailWord_321972).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321972).length < 2 ^ (prefixWord ++ tailWord_321972).sum := by decide
  have hdescent : baseEnd_321972 < baseStart_321972 := by decide
  rcases family_descends (prefixWord ++ tailWord_321972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321994 : List Nat := [3, 1, 2, 1, 2, 2, 2, 4, 3]
def baseStart_321994 : Nat := 118140960795 + 321994 * 2 ^ 59
def prefixEnd_321994 : Nat := 4983230072969 + 3 ^ 40 * 321994 * 2
def baseEnd_321994 : Nat := 146966835434594160617051

theorem tailTrace_321994 : CollatzResearch.WordTrace tailWord_321994 prefixEnd_321994 146966835434594160617051 := by
  unfold tailWord_321994
  simp only [CollatzResearch.WordTrace]
  refine ⟨2936021498869551260539259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7829390663652136694771357 2936021498869551260539259)
  ·
    refine ⟨4404032248304326890808889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2936021498869551260539259 4404032248304326890808889)
    ·
      refine ⟨3303024186228245168106667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4404032248304326890808889 3303024186228245168106667)
      ·
        refine ⟨4954536279342367752160001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3303024186228245168106667 4954536279342367752160001)
        ·
          refine ⟨3715902209506775814120001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4954536279342367752160001 3715902209506775814120001)
          ·
            refine ⟨2786926657130081860590001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3715902209506775814120001 2786926657130081860590001)
            ·
              refine ⟨2090194992847561395442501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2786926657130081860590001 2090194992847561395442501)
              ·
                refine ⟨391911561158917761645469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2090194992847561395442501 391911561158917761645469)
                ·
                  refine ⟨146966835434594160617051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 391911561158917761645469 146966835434594160617051)
                  ·
                    rfl

theorem cell20_321994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 4, 3].length) (baseStart_321994 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_321994 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_321994 prefixEnd_321994 := by exact prefixLift 321994
  have htrace : WordTrace (prefixWord ++ tailWord_321994) baseStart_321994 baseEnd_321994 := by
    simpa [prefixWord, tailWord_321994, baseEnd_321994] using wordTrace_append hprefix tailTrace_321994
  have hstable : (prefixWord ++ tailWord_321994).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321994).length < 2 ^ (prefixWord ++ tailWord_321994).sum := by decide
  have hdescent : baseEnd_321994 < baseStart_321994 := by decide
  rcases family_descends (prefixWord ++ tailWord_321994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322046 : List Nat := [4, 2, 2, 12]
def baseStart_322046 : Nat := 118140960795 + 322046 * 2 ^ 59
def prefixEnd_322046 : Nat := 4983230072969 + 3 ^ 40 * 322046 * 2
def baseEnd_322046 : Nat := 604899463586473625035

theorem tailTrace_322046 : CollatzResearch.WordTrace tailWord_322046 prefixEnd_322046 604899463586473625035 := by
  unfold tailWord_322046
  simp only [CollatzResearch.WordTrace]
  refine ⟨1468247823911227240381249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7830655060859878615366661 1468247823911227240381249)
  ·
    refine ⟨1101185867933420430285937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1468247823911227240381249 1101185867933420430285937)
    ·
      refine ⟨825889400950065322714453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1101185867933420430285937 825889400950065322714453)
      ·
        refine ⟨604899463586473625035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 12 825889400950065322714453 604899463586473625035)
        ·
          rfl

theorem cell20_322046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 12].length) (baseStart_322046 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_322046 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_322046 prefixEnd_322046 := by exact prefixLift 322046
  have htrace : WordTrace (prefixWord ++ tailWord_322046) baseStart_322046 baseEnd_322046 := by
    simpa [prefixWord, tailWord_322046, baseEnd_322046] using wordTrace_append hprefix tailTrace_322046
  have hstable : (prefixWord ++ tailWord_322046).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322046).length < 2 ^ (prefixWord ++ tailWord_322046).sum := by decide
  have hdescent : baseEnd_322046 < baseStart_322046 := by decide
  rcases family_descends (prefixWord ++ tailWord_322046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322049 : List Nat := [1, 2, 4, 1, 3, 2, 2, 2, 3]
def baseStart_322049 : Nat := 118140960795 + 322049 * 2 ^ 59
def prefixEnd_322049 : Nat := 4983230072969 + 3 ^ 40 * 322049 * 2
def baseEnd_322049 : Nat := 146991938933258413783493

theorem tailTrace_322049 : CollatzResearch.WordTrace tailWord_322049 prefixEnd_322049 146991938933258413783493 := by
  unfold tailWord_322049
  simp only [CollatzResearch.WordTrace]
  refine ⟨11746092010278949435409201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7830728006852632956939467 11746092010278949435409201)
  ·
    refine ⟨8809569007709212076556901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11746092010278949435409201 8809569007709212076556901)
    ·
      refine ⟨1651794188945477264354419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8809569007709212076556901 1651794188945477264354419)
      ·
        refine ⟨2477691283418215896531629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1651794188945477264354419 2477691283418215896531629)
        ·
          refine ⟨929134231281830961199361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2477691283418215896531629 929134231281830961199361)
          ·
            refine ⟨696850673461373220899521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 929134231281830961199361 696850673461373220899521)
            ·
              refine ⟨522638005096029915674641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 696850673461373220899521 522638005096029915674641)
              ·
                refine ⟨391978503822022436755981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 522638005096029915674641 391978503822022436755981)
                ·
                  refine ⟨146991938933258413783493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 391978503822022436755981 146991938933258413783493)
                  ·
                    rfl

theorem cell20_322049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 2, 2, 3].length) (baseStart_322049 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_322049 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_322049 prefixEnd_322049 := by exact prefixLift 322049
  have htrace : WordTrace (prefixWord ++ tailWord_322049) baseStart_322049 baseEnd_322049 := by
    simpa [prefixWord, tailWord_322049, baseEnd_322049] using wordTrace_append hprefix tailTrace_322049
  have hstable : (prefixWord ++ tailWord_322049).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322049).length < 2 ^ (prefixWord ++ tailWord_322049).sum := by decide
  have hdescent : baseEnd_322049 < baseStart_322049 := by decide
  rcases family_descends (prefixWord ++ tailWord_322049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322052 : List Nat := [2, 3, 2, 3, 1, 1, 4, 2, 2]
def baseStart_322052 : Nat := 118140960795 + 322052 * 2 ^ 59
def prefixEnd_322052 : Nat := 4983230072969 + 3 ^ 40 * 322052 * 2
def baseEnd_322052 : Nat := 146993308215003736683481

theorem tailTrace_322052 : CollatzResearch.WordTrace tailWord_322052 prefixEnd_322052 146993308215003736683481 := by
  unfold tailWord_322052
  simp only [CollatzResearch.WordTrace]
  refine ⟨5873100714634040473884205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7830800952845387298512273 5873100714634040473884205)
  ·
    refine ⟨2202412767987765177706577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5873100714634040473884205 2202412767987765177706577)
    ·
      refine ⟨1651809575990823883279933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2202412767987765177706577 1651809575990823883279933)
      ·
        refine ⟨619428590996558956229975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1651809575990823883279933 619428590996558956229975)
        ·
          refine ⟨929142886494838434344963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 619428590996558956229975 929142886494838434344963)
          ·
            refine ⟨1393714329742257651517445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 929142886494838434344963 1393714329742257651517445)
            ·
              refine ⟨261321436826673309659521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1393714329742257651517445 261321436826673309659521)
              ·
                refine ⟨195991077620004982244641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 261321436826673309659521 195991077620004982244641)
                ·
                  refine ⟨146993308215003736683481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 195991077620004982244641 146993308215003736683481)
                  ·
                    rfl

theorem cell20_322052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 4, 2, 2].length) (baseStart_322052 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_322052 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_322052 prefixEnd_322052 := by exact prefixLift 322052
  have htrace : WordTrace (prefixWord ++ tailWord_322052) baseStart_322052 baseEnd_322052 := by
    simpa [prefixWord, tailWord_322052, baseEnd_322052] using wordTrace_append hprefix tailTrace_322052
  have hstable : (prefixWord ++ tailWord_322052).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322052).length < 2 ^ (prefixWord ++ tailWord_322052).sum := by decide
  have hdescent : baseEnd_322052 < baseStart_322052 := by decide
  rcases family_descends (prefixWord ++ tailWord_322052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322053 : List Nat := [1, 3, 1, 1, 2, 2, 2, 3, 5]
def baseStart_322053 : Nat := 118140960795 + 322053 * 2 ^ 59
def prefixEnd_322053 : Nat := 4983230072969 + 3 ^ 40 * 322053 * 2
def baseEnd_322053 : Nat := 146993764642252177650143

theorem tailTrace_322053 : CollatzResearch.WordTrace tailWord_322053 prefixEnd_322053 146993764642252177650143 := by
  unfold tailWord_322053
  simp only [CollatzResearch.WordTrace]
  refine ⟨11746237902264458118554813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7830825268176305412369875 11746237902264458118554813)
  ·
    refine ⟨4404839213349171794458055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11746237902264458118554813 4404839213349171794458055)
    ·
      refine ⟨6607258820023757691687083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4404839213349171794458055 6607258820023757691687083)
      ·
        refine ⟨9910888230035636537530625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6607258820023757691687083 9910888230035636537530625)
        ·
          refine ⟨7433166172526727403147969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9910888230035636537530625 7433166172526727403147969)
          ·
            refine ⟨5574874629395045552360977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7433166172526727403147969 5574874629395045552360977)
            ·
              refine ⟨4181155972046284164270733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5574874629395045552360977 4181155972046284164270733)
              ·
                refine ⟨1567933489517356561601525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4181155972046284164270733 1567933489517356561601525)
                ·
                  refine ⟨146993764642252177650143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1567933489517356561601525 146993764642252177650143)
                  ·
                    rfl

theorem cell20_322053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 3, 5].length) (baseStart_322053 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_322053 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_322053 prefixEnd_322053 := by exact prefixLift 322053
  have htrace : WordTrace (prefixWord ++ tailWord_322053) baseStart_322053 baseEnd_322053 := by
    simpa [prefixWord, tailWord_322053, baseEnd_322053] using wordTrace_append hprefix tailTrace_322053
  have hstable : (prefixWord ++ tailWord_322053).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322053).length < 2 ^ (prefixWord ++ tailWord_322053).sum := by decide
  have hdescent : baseEnd_322053 < baseStart_322053 := by decide
  rcases family_descends (prefixWord ++ tailWord_322053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322077 : List Nat := [1, 4, 2, 2, 1, 2, 1, 1, 6]
def baseStart_322077 : Nat := 118140960795 + 322077 * 2 ^ 59
def prefixEnd_322077 : Nat := 4983230072969 + 3 ^ 40 * 322077 * 2
def baseEnd_322077 : Nat := 147004718896214760850045

theorem tailTrace_322077 : CollatzResearch.WordTrace tailWord_322077 prefixEnd_322077 147004718896214760850045 := by
  unfold tailWord_322077
  simp only [CollatzResearch.WordTrace]
  refine ⟨11747113254177510217428485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7831408836118340144952323 11747113254177510217428485)
  ·
    refine ⟨2202583735158283165767841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11747113254177510217428485 2202583735158283165767841)
    ·
      refine ⟨1651937801368712374325881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2202583735158283165767841 1651937801368712374325881)
      ·
        refine ⟨1238953351026534280744411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1651937801368712374325881 1238953351026534280744411)
        ·
          refine ⟨1858430026539801421116617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1238953351026534280744411 1858430026539801421116617)
          ·
            refine ⟨1393822519904851065837463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1858430026539801421116617 1393822519904851065837463)
            ·
              refine ⟨2090733779857276598756195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1393822519904851065837463 2090733779857276598756195)
              ·
                refine ⟨3136100669785914898134293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2090733779857276598756195 3136100669785914898134293)
                ·
                  refine ⟨147004718896214760850045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3136100669785914898134293 147004718896214760850045)
                  ·
                    rfl

theorem cell20_322077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 1, 6].length) (baseStart_322077 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_322077 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_322077 prefixEnd_322077 := by exact prefixLift 322077
  have htrace : WordTrace (prefixWord ++ tailWord_322077) baseStart_322077 baseEnd_322077 := by
    simpa [prefixWord, tailWord_322077, baseEnd_322077] using wordTrace_append hprefix tailTrace_322077
  have hstable : (prefixWord ++ tailWord_322077).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322077).length < 2 ^ (prefixWord ++ tailWord_322077).sum := by decide
  have hdescent : baseEnd_322077 < baseStart_322077 := by decide
  rcases family_descends (prefixWord ++ tailWord_322077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322080 : List Nat := [2, 1, 1, 6, 2, 1, 3, 4]
def baseStart_322080 : Nat := 118140960795 + 322080 * 2 ^ 59
def prefixEnd_322080 : Nat := 4983230072969 + 3 ^ 40 * 322080 * 2
def baseEnd_322080 : Nat := 49002029392653361250011

theorem tailTrace_322080 : CollatzResearch.WordTrace tailWord_322080 prefixEnd_322080 49002029392653361250011 := by
  unfold tailWord_322080
  simp only [CollatzResearch.WordTrace]
  refine ⟨5873611336583320864893847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7831481782111094486525129 5873611336583320864893847)
  ·
    refine ⟨8810417004874981297340771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5873611336583320864893847 8810417004874981297340771)
    ·
      refine ⟨13215625507312471946011157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8810417004874981297340771 13215625507312471946011157)
      ·
        refine ⟨619482445655272122469273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 13215625507312471946011157 619482445655272122469273)
        ·
          refine ⟨464611834241454091851955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 619482445655272122469273 464611834241454091851955)
          ·
            refine ⟨696917751362181137777933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 464611834241454091851955 696917751362181137777933)
            ·
              refine ⟨261344156760817926666725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 696917751362181137777933 261344156760817926666725)
              ·
                refine ⟨49002029392653361250011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 261344156760817926666725 49002029392653361250011)
                ·
                  rfl

theorem cell20_322080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 3, 4].length) (baseStart_322080 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_322080 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_322080 prefixEnd_322080 := by exact prefixLift 322080
  have htrace : WordTrace (prefixWord ++ tailWord_322080) baseStart_322080 baseEnd_322080 := by
    simpa [prefixWord, tailWord_322080, baseEnd_322080] using wordTrace_append hprefix tailTrace_322080
  have hstable : (prefixWord ++ tailWord_322080).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322080).length < 2 ^ (prefixWord ++ tailWord_322080).sum := by decide
  have hdescent : baseEnd_322080 < baseStart_322080 := by decide
  rcases family_descends (prefixWord ++ tailWord_322080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322100 : List Nat := [2, 5, 1, 3, 2, 1, 1, 2, 3]
def baseStart_322100 : Nat := 118140960795 + 322100 * 2 ^ 59
def prefixEnd_322100 : Nat := 4983230072969 + 3 ^ 40 * 322100 * 2
def baseEnd_322100 : Nat := 147015216722928903083285

theorem tailTrace_322100 : CollatzResearch.WordTrace tailWord_322100 prefixEnd_322100 147015216722928903083285 := by
  unfold tailWord_322100
  simp only [CollatzResearch.WordTrace]
  refine ⟨5873976066547092572757877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7831968088729456763677169 5873976066547092572757877)
  ·
    refine ⟨550685256238789928696051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5873976066547092572757877 550685256238789928696051)
    ·
      refine ⟨826027884358184893044077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 550685256238789928696051 826027884358184893044077)
      ·
        refine ⟨309760456634319334891529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 826027884358184893044077 309760456634319334891529)
        ·
          refine ⟨232320342475739501168647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 309760456634319334891529 232320342475739501168647)
          ·
            refine ⟨348480513713609251752971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 232320342475739501168647 348480513713609251752971)
            ·
              refine ⟨522720770570413877629457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 348480513713609251752971 522720770570413877629457)
              ·
                refine ⟨392040577927810408222093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 522720770570413877629457 392040577927810408222093)
                ·
                  refine ⟨147015216722928903083285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 392040577927810408222093 147015216722928903083285)
                  ·
                    rfl

theorem cell20_322100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 1, 2, 3].length) (baseStart_322100 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_322100 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_322100 prefixEnd_322100 := by exact prefixLift 322100
  have htrace : WordTrace (prefixWord ++ tailWord_322100) baseStart_322100 baseEnd_322100 := by
    simpa [prefixWord, tailWord_322100, baseEnd_322100] using wordTrace_append hprefix tailTrace_322100
  have hstable : (prefixWord ++ tailWord_322100).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322100).length < 2 ^ (prefixWord ++ tailWord_322100).sum := by decide
  have hdescent : baseEnd_322100 < baseStart_322100 := by decide
  rcases family_descends (prefixWord ++ tailWord_322100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322108 : List Nat := [2, 2, 2, 2, 3, 2, 1, 1, 5]
def baseStart_322108 : Nat := 118140960795 + 322108 * 2 ^ 59
def prefixEnd_322108 : Nat := 4983230072969 + 3 ^ 40 * 322108 * 2
def baseEnd_322108 : Nat := 147018868140916430816585

theorem tailTrace_322108 : CollatzResearch.WordTrace tailWord_322108 prefixEnd_322108 147018868140916430816585 := by
  unfold tailWord_322108
  simp only [CollatzResearch.WordTrace]
  refine ⟨5874121958532601255903489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7832162611376801674537985 5874121958532601255903489)
  ·
    refine ⟨4405591468899450941927617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5874121958532601255903489 4405591468899450941927617)
    ·
      refine ⟨3304193601674588206445713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4405591468899450941927617 3304193601674588206445713)
      ·
        refine ⟨2478145201255941154834285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3304193601674588206445713 2478145201255941154834285)
        ·
          refine ⟨929304450470977933062857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2478145201255941154834285 929304450470977933062857)
          ·
            refine ⟨696978337853233449797143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 929304450470977933062857 696978337853233449797143)
            ·
              refine ⟨1045467506779850174695715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 696978337853233449797143 1045467506779850174695715)
              ·
                refine ⟨1568201260169775262043573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1045467506779850174695715 1568201260169775262043573)
                ·
                  refine ⟨147018868140916430816585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1568201260169775262043573 147018868140916430816585)
                  ·
                    rfl

theorem cell20_322108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 1, 5].length) (baseStart_322108 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_322108 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_322108 prefixEnd_322108 := by exact prefixLift 322108
  have htrace : WordTrace (prefixWord ++ tailWord_322108) baseStart_322108 baseEnd_322108 := by
    simpa [prefixWord, tailWord_322108, baseEnd_322108] using wordTrace_append hprefix tailTrace_322108
  have hstable : (prefixWord ++ tailWord_322108).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322108).length < 2 ^ (prefixWord ++ tailWord_322108).sum := by decide
  have hdescent : baseEnd_322108 < baseStart_322108 := by decide
  rcases family_descends (prefixWord ++ tailWord_322108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322166 : List Nat := [5, 1, 1, 2, 4, 1, 1, 1, 4]
def baseStart_322166 : Nat := 118140960795 + 322166 * 2 ^ 59
def prefixEnd_322166 : Nat := 4983230072969 + 3 ^ 40 * 322166 * 2
def baseEnd_322166 : Nat := 147045340921326006883015

theorem tailTrace_322166 : CollatzResearch.WordTrace tailWord_322166 prefixEnd_322166 147045340921326006883015 := by
  unfold tailWord_322166
  simp only [CollatzResearch.WordTrace]
  refine ⟨734397459428442401088647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7833572900570052278278901 734397459428442401088647)
  ·
    refine ⟨1101596189142663601632971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 734397459428442401088647 1101596189142663601632971)
    ·
      refine ⟨1652394283713995402449457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1101596189142663601632971 1652394283713995402449457)
      ·
        refine ⟨1239295712785496551837093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1652394283713995402449457 1239295712785496551837093)
        ·
          refine ⟨232367946147280603469455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1239295712785496551837093 232367946147280603469455)
          ·
            refine ⟨348551919220920905204183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 232367946147280603469455 348551919220920905204183)
            ·
              refine ⟨522827878831381357806275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 348551919220920905204183 522827878831381357806275)
              ·
                refine ⟨784241818247072036709413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 522827878831381357806275 784241818247072036709413)
                ·
                  refine ⟨147045340921326006883015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 784241818247072036709413 147045340921326006883015)
                  ·
                    rfl

theorem cell20_322166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 1, 1, 4].length) (baseStart_322166 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_322166 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_322166 prefixEnd_322166 := by exact prefixLift 322166
  have htrace : WordTrace (prefixWord ++ tailWord_322166) baseStart_322166 baseEnd_322166 := by
    simpa [prefixWord, tailWord_322166, baseEnd_322166] using wordTrace_append hprefix tailTrace_322166
  have hstable : (prefixWord ++ tailWord_322166).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322166).length < 2 ^ (prefixWord ++ tailWord_322166).sum := by decide
  have hdescent : baseEnd_322166 < baseStart_322166 := by decide
  rcases family_descends (prefixWord ++ tailWord_322166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322167 : List Nat := [1, 1, 3, 1, 1, 3, 4, 1, 5]
def baseStart_322167 : Nat := 118140960795 + 322167 * 2 ^ 59
def prefixEnd_322167 : Nat := 4983230072969 + 3 ^ 40 * 322167 * 2
def baseEnd_322167 : Nat := 147045797348574447849677

theorem tailTrace_322167 : CollatzResearch.WordTrace tailWord_322167 prefixEnd_322167 147045797348574447849677 := by
  unfold tailWord_322167
  simp only [CollatzResearch.WordTrace]
  refine ⟨11750395823851455588204755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7833597215900970392136503 11750395823851455588204755)
  ·
    refine ⟨17625593735777183382307133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11750395823851455588204755 17625593735777183382307133)
    ·
      refine ⟨6609597650916443768365175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17625593735777183382307133 6609597650916443768365175)
      ·
        refine ⟨9914396476374665652547763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6609597650916443768365175 9914396476374665652547763)
        ·
          refine ⟨14871594714561998478821645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9914396476374665652547763 14871594714561998478821645)
          ·
            refine ⟨5576848017960749429558117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14871594714561998478821645 5576848017960749429558117)
            ·
              refine ⟨1045659003367640518042147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5576848017960749429558117 1045659003367640518042147)
              ·
                refine ⟨1568488505051460777063221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1045659003367640518042147 1568488505051460777063221)
                ·
                  refine ⟨147045797348574447849677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1568488505051460777063221 147045797348574447849677)
                  ·
                    rfl

theorem cell20_322167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 1, 5].length) (baseStart_322167 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_322167 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_322167 prefixEnd_322167 := by exact prefixLift 322167
  have htrace : WordTrace (prefixWord ++ tailWord_322167) baseStart_322167 baseEnd_322167 := by
    simpa [prefixWord, tailWord_322167, baseEnd_322167] using wordTrace_append hprefix tailTrace_322167
  have hstable : (prefixWord ++ tailWord_322167).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322167).length < 2 ^ (prefixWord ++ tailWord_322167).sum := by decide
  have hdescent : baseEnd_322167 < baseStart_322167 := by decide
  rcases family_descends (prefixWord ++ tailWord_322167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322180 : List Nat := [2, 3, 2, 1, 3, 3, 2, 1, 3]
def baseStart_322180 : Nat := 118140960795 + 322180 * 2 ^ 59
def prefixEnd_322180 : Nat := 4983230072969 + 3 ^ 40 * 322180 * 2
def baseEnd_322180 : Nat := 147051730902804180416291

theorem tailTrace_322180 : CollatzResearch.WordTrace tailWord_322180 prefixEnd_322180 147051730902804180416291 := by
  unfold tailWord_322180
  simp only [CollatzResearch.WordTrace]
  refine ⟨5875434986402179404213997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7833913315202905872285329 5875434986402179404213997)
  ·
    refine ⟨2203288119900817276580249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5875434986402179404213997 2203288119900817276580249)
    ·
      refine ⟨1652466089925612957435187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2203288119900817276580249 1652466089925612957435187)
      ·
        refine ⟨2478699134888419436152781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1652466089925612957435187 2478699134888419436152781)
        ·
          refine ⟨929512175583157288557293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2478699134888419436152781 929512175583157288557293)
          ·
            refine ⟨348567065843683983208985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 929512175583157288557293 348567065843683983208985)
            ·
              refine ⟨261425299382762987406739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 348567065843683983208985 261425299382762987406739)
              ·
                refine ⟨392137949074144481110109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 261425299382762987406739 392137949074144481110109)
                ·
                  refine ⟨147051730902804180416291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 392137949074144481110109 147051730902804180416291)
                  ·
                    rfl

theorem cell20_322180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 2, 1, 3].length) (baseStart_322180 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_322180 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_322180 prefixEnd_322180 := by exact prefixLift 322180
  have htrace : WordTrace (prefixWord ++ tailWord_322180) baseStart_322180 baseEnd_322180 := by
    simpa [prefixWord, tailWord_322180, baseEnd_322180] using wordTrace_append hprefix tailTrace_322180
  have hstable : (prefixWord ++ tailWord_322180).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322180).length < 2 ^ (prefixWord ++ tailWord_322180).sum := by decide
  have hdescent : baseEnd_322180 < baseStart_322180 := by decide
  rcases family_descends (prefixWord ++ tailWord_322180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322205 : List Nat := [1, 4, 2, 1, 1, 1, 2, 1, 7]
def baseStart_322205 : Nat := 118140960795 + 322205 * 2 ^ 59
def prefixEnd_322205 : Nat := 4983230072969 + 3 ^ 40 * 322205 * 2
def baseEnd_322205 : Nat := 147063141584015204582855

theorem tailTrace_322205 : CollatzResearch.WordTrace tailWord_322205 prefixEnd_322205 147063141584015204582855 := by
  unfold tailWord_322205
  simp only [CollatzResearch.WordTrace]
  refine ⟨11751781797713788078088069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7834521198475858718725379 11751781797713788078088069)
  ·
    refine ⟨2203459087071335264641513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11751781797713788078088069 2203459087071335264641513)
    ·
      refine ⟨1652594315303501448481135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2203459087071335264641513 1652594315303501448481135)
      ·
        refine ⟨2478891472955252172721703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1652594315303501448481135 2478891472955252172721703)
        ·
          refine ⟨3718337209432878259082555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2478891472955252172721703 3718337209432878259082555)
          ·
            refine ⟨5577505814149317388623833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3718337209432878259082555 5577505814149317388623833)
            ·
              refine ⟨4183129360611988041467875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5577505814149317388623833 4183129360611988041467875)
              ·
                refine ⟨6274694040917982062201813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4183129360611988041467875 6274694040917982062201813)
                ·
                  refine ⟨147063141584015204582855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6274694040917982062201813 147063141584015204582855)
                  ·
                    rfl

theorem cell20_322205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 7].length) (baseStart_322205 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_322205 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_322205 prefixEnd_322205 := by exact prefixLift 322205
  have htrace : WordTrace (prefixWord ++ tailWord_322205) baseStart_322205 baseEnd_322205 := by
    simpa [prefixWord, tailWord_322205, baseEnd_322205] using wordTrace_append hprefix tailTrace_322205
  have hstable : (prefixWord ++ tailWord_322205).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322205).length < 2 ^ (prefixWord ++ tailWord_322205).sum := by decide
  have hdescent : baseEnd_322205 < baseStart_322205 := by decide
  rcases family_descends (prefixWord ++ tailWord_322205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322215 : List Nat := [1, 1, 6, 3, 1, 8]
def baseStart_322215 : Nat := 118140960795 + 322215 * 2 ^ 59
def prefixEnd_322215 : Nat := 4983230072969 + 3 ^ 40 * 322215 * 2
def baseEnd_322215 : Nat := 5446952068759244972203

theorem tailTrace_322215 : CollatzResearch.WordTrace tailWord_322215 prefixEnd_322215 5446952068759244972203 := by
  unfold tailWord_322215
  simp only [CollatzResearch.WordTrace]
  refine ⟨11752146527677559785952099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7834764351785039857301399 11752146527677559785952099)
  ·
    refine ⟨17628219791516339678928149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11752146527677559785952099 17628219791516339678928149)
    ·
      refine ⟨826322802727328422449757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 17628219791516339678928149 826322802727328422449757)
      ·
        refine ⟨309871051022748158418659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 826322802727328422449757 309871051022748158418659)
        ·
          refine ⟨464806576534122237627989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 309871051022748158418659 464806576534122237627989)
          ·
            refine ⟨5446952068759244972203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 464806576534122237627989 5446952068759244972203)
            ·
              rfl

theorem cell20_322215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 8].length) (baseStart_322215 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_322215 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_322215 prefixEnd_322215 := by exact prefixLift 322215
  have htrace : WordTrace (prefixWord ++ tailWord_322215) baseStart_322215 baseEnd_322215 := by
    simpa [prefixWord, tailWord_322215, baseEnd_322215] using wordTrace_append hprefix tailTrace_322215
  have hstable : (prefixWord ++ tailWord_322215).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322215).length < 2 ^ (prefixWord ++ tailWord_322215).sum := by decide
  have hdescent : baseEnd_322215 < baseStart_322215 := by decide
  rcases family_descends (prefixWord ++ tailWord_322215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322277 : List Nat := [1, 3, 1, 4, 1, 4, 1, 2, 3]
def baseStart_322277 : Nat := 118140960795 + 322277 * 2 ^ 59
def prefixEnd_322277 : Nat := 4983230072969 + 3 ^ 40 * 322277 * 2
def baseEnd_322277 : Nat := 147096004345902954182561

theorem tailTrace_322277 : CollatzResearch.WordTrace tailWord_322277 prefixEnd_322277 147096004345902954182561 := by
  unfold tailWord_322277
  simp only [CollatzResearch.WordTrace]
  refine ⟨11754407853452944374709085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7836271902301962916472723 11754407853452944374709085)
  ·
    refine ⟨4407902945044854140515907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11754407853452944374709085 4407902945044854140515907)
    ·
      refine ⟨6611854417567281210773861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4407902945044854140515907 6611854417567281210773861)
      ·
        refine ⟨1239722703293865227020099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6611854417567281210773861 1239722703293865227020099)
        ·
          refine ⟨1859584054940797840530149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1239722703293865227020099 1859584054940797840530149)
          ·
            refine ⟨348672010301399595099403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1859584054940797840530149 348672010301399595099403)
            ·
              refine ⟨523008015452099392649105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 348672010301399595099403 523008015452099392649105)
              ·
                refine ⟨392256011589074544486829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 523008015452099392649105 392256011589074544486829)
                ·
                  refine ⟨147096004345902954182561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 392256011589074544486829 147096004345902954182561)
                  ·
                    rfl

theorem cell20_322277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 1, 2, 3].length) (baseStart_322277 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_322277 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_322277 prefixEnd_322277 := by exact prefixLift 322277
  have htrace : WordTrace (prefixWord ++ tailWord_322277) baseStart_322277 baseEnd_322277 := by
    simpa [prefixWord, tailWord_322277, baseEnd_322277] using wordTrace_append hprefix tailTrace_322277
  have hstable : (prefixWord ++ tailWord_322277).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322277).length < 2 ^ (prefixWord ++ tailWord_322277).sum := by decide
  have hdescent : baseEnd_322277 < baseStart_322277 := by decide
  rcases family_descends (prefixWord ++ tailWord_322277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322295 : List Nat := [1, 1, 3, 1, 1, 1, 3, 9]
def baseStart_322295 : Nat := 118140960795 + 322295 * 2 ^ 59
def prefixEnd_322295 : Nat := 4983230072969 + 3 ^ 40 * 322295 * 2
def baseEnd_322295 : Nat := 49034740012124963860829

theorem tailTrace_322295 : CollatzResearch.WordTrace tailWord_322295 prefixEnd_322295 49034740012124963860829 := by
  unfold tailWord_322295
  simp only [CollatzResearch.WordTrace]
  refine ⟨11755064367387733448864339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7836709578258488965909559 11755064367387733448864339)
  ·
    refine ⟨17632596551081600173296509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11755064367387733448864339 17632596551081600173296509)
    ·
      refine ⟨6612223706655600064986191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17632596551081600173296509 6612223706655600064986191)
      ·
        refine ⟨9918335559983400097479287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6612223706655600064986191 9918335559983400097479287)
        ·
          refine ⟨14877503339975100146218931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9918335559983400097479287 14877503339975100146218931)
          ·
            refine ⟨22316255009962650219328397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14877503339975100146218931 22316255009962650219328397)
            ·
              refine ⟨8368595628735993832248149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22316255009962650219328397 8368595628735993832248149)
              ·
                refine ⟨49034740012124963860829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8368595628735993832248149 49034740012124963860829)
                ·
                  rfl

theorem cell20_322295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 9].length) (baseStart_322295 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_322295 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_322295 prefixEnd_322295 := by exact prefixLift 322295
  have htrace : WordTrace (prefixWord ++ tailWord_322295) baseStart_322295 baseEnd_322295 := by
    simpa [prefixWord, tailWord_322295, baseEnd_322295] using wordTrace_append hprefix tailTrace_322295
  have hstable : (prefixWord ++ tailWord_322295).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322295).length < 2 ^ (prefixWord ++ tailWord_322295).sum := by decide
  have hdescent : baseEnd_322295 < baseStart_322295 := by decide
  rcases family_descends (prefixWord ++ tailWord_322295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322312 : List Nat := [2, 1, 3, 2, 2, 3, 1, 6]
def baseStart_322312 : Nat := 118140960795 + 322312 * 2 ^ 59
def prefixEnd_322312 : Nat := 4983230072969 + 3 ^ 40 * 322312 * 2
def baseEnd_322312 : Nat := 49037326433199462671917

theorem tailTrace_322312 : CollatzResearch.WordTrace tailWord_322312 prefixEnd_322312 49037326433199462671917 := by
  unfold tailWord_322312
  simp only [CollatzResearch.WordTrace]
  refine ⟨5877842204163072676116595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7837122938884096901488793 5877842204163072676116595)
  ·
    refine ⟨8816763306244609014174893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5877842204163072676116595 8816763306244609014174893)
    ·
      refine ⟨3306286239841728380315585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8816763306244609014174893 3306286239841728380315585)
      ·
        refine ⟨2479714679881296285236689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3306286239841728380315585 2479714679881296285236689)
        ·
          refine ⟨1859786009910972213927517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2479714679881296285236689 1859786009910972213927517)
          ·
            refine ⟨697419753716614580222819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1859786009910972213927517 697419753716614580222819)
            ·
              refine ⟨1046129630574921870334229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 697419753716614580222819 1046129630574921870334229)
              ·
                refine ⟨49037326433199462671917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1046129630574921870334229 49037326433199462671917)
                ·
                  rfl

theorem cell20_322312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 6].length) (baseStart_322312 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_322312 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_322312 prefixEnd_322312 := by exact prefixLift 322312
  have htrace : WordTrace (prefixWord ++ tailWord_322312) baseStart_322312 baseEnd_322312 := by
    simpa [prefixWord, tailWord_322312, baseEnd_322312] using wordTrace_append hprefix tailTrace_322312
  have hstable : (prefixWord ++ tailWord_322312).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322312).length < 2 ^ (prefixWord ++ tailWord_322312).sum := by decide
  have hdescent : baseEnd_322312 < baseStart_322312 := by decide
  rcases family_descends (prefixWord ++ tailWord_322312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322346 : List Nat := [3, 1, 4, 3, 1, 1, 2, 5]
def baseStart_322346 : Nat := 118140960795 + 322346 * 2 ^ 59
def prefixEnd_322346 : Nat := 4983230072969 + 3 ^ 40 * 322346 * 2
def baseEnd_322346 : Nat := 49042499275348460294093

theorem tailTrace_322346 : CollatzResearch.WordTrace tailWord_322346 prefixEnd_322346 49042499275348460294093 := by
  unfold tailWord_322346
  simp only [CollatzResearch.WordTrace]
  refine ⟨2939231122550742289742723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7837949660135312772647261 2939231122550742289742723)
  ·
    refine ⟨4408846683826113434614085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2939231122550742289742723 4408846683826113434614085)
    ·
      refine ⟨826658753217396268990141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4408846683826113434614085 826658753217396268990141)
      ·
        refine ⟨309997032456523600871303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 826658753217396268990141 309997032456523600871303)
        ·
          refine ⟨464995548684785401306955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 309997032456523600871303 464995548684785401306955)
          ·
            refine ⟨697493323027178101960433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 464995548684785401306955 697493323027178101960433)
            ·
              refine ⟨523119992270383576470325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 697493323027178101960433 523119992270383576470325)
              ·
                refine ⟨49042499275348460294093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 523119992270383576470325 49042499275348460294093)
                ·
                  rfl

theorem cell20_322346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 2, 5].length) (baseStart_322346 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_322346 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_322346 prefixEnd_322346 := by exact prefixLift 322346
  have htrace : WordTrace (prefixWord ++ tailWord_322346) baseStart_322346 baseEnd_322346 := by
    simpa [prefixWord, tailWord_322346, baseEnd_322346] using wordTrace_append hprefix tailTrace_322346
  have hstable : (prefixWord ++ tailWord_322346).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322346).length < 2 ^ (prefixWord ++ tailWord_322346).sum := by decide
  have hdescent : baseEnd_322346 < baseStart_322346 := by decide
  rcases family_descends (prefixWord ++ tailWord_322346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322364 : List Nat := [2, 2, 2, 2, 1, 1, 1, 3, 6]
def baseStart_322364 : Nat := 118140960795 + 322364 * 2 ^ 59
def prefixEnd_322364 : Nat := 4983230072969 + 3 ^ 40 * 322364 * 2
def baseEnd_322364 : Nat := 147135713516517318282205

theorem tailTrace_322364 : CollatzResearch.WordTrace tailWord_322364 prefixEnd_322364 147135713516517318282205 := by
  unfold tailWord_322364
  simp only [CollatzResearch.WordTrace]
  refine ⟨5878790502068879116563073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7838387336091838822084097 5878790502068879116563073)
  ·
    refine ⟨4409092876551659337422305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5878790502068879116563073 4409092876551659337422305)
    ·
      refine ⟨3306819657413744503066729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4409092876551659337422305 3306819657413744503066729)
      ·
        refine ⟨2480114743060308377300047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3306819657413744503066729 2480114743060308377300047)
        ·
          refine ⟨3720172114590462565950071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2480114743060308377300047 3720172114590462565950071)
          ·
            refine ⟨5580258171885693848925107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3720172114590462565950071 5580258171885693848925107)
            ·
              refine ⟨8370387257828540773387661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5580258171885693848925107 8370387257828540773387661)
              ·
                refine ⟨3138895221685702790020373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8370387257828540773387661 3138895221685702790020373)
                ·
                  refine ⟨147135713516517318282205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3138895221685702790020373 147135713516517318282205)
                  ·
                    rfl

theorem cell20_322364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 3, 6].length) (baseStart_322364 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_322364 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_322364 prefixEnd_322364 := by exact prefixLift 322364
  have htrace : WordTrace (prefixWord ++ tailWord_322364) baseStart_322364 baseEnd_322364 := by
    simpa [prefixWord, tailWord_322364, baseEnd_322364] using wordTrace_append hprefix tailTrace_322364
  have hstable : (prefixWord ++ tailWord_322364).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322364).length < 2 ^ (prefixWord ++ tailWord_322364).sum := by decide
  have hdescent : baseEnd_322364 < baseStart_322364 := by decide
  rcases family_descends (prefixWord ++ tailWord_322364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322371 : List Nat := [1, 1, 1, 3, 1, 4, 1, 8]
def baseStart_322371 : Nat := 118140960795 + 322371 * 2 ^ 59
def prefixEnd_322371 : Nat := 4983230072969 + 3 ^ 40 * 322371 * 2
def baseEnd_322371 : Nat := 49046302835752135016281

theorem tailTrace_322371 : CollatzResearch.WordTrace tailWord_322371 prefixEnd_322371 49046302835752135016281 := by
  unfold tailWord_322371
  simp only [CollatzResearch.WordTrace]
  refine ⟨11757836315112398428630967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7838557543408265619087311 11757836315112398428630967)
  ·
    refine ⟨17636754472668597642946451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11757836315112398428630967 17636754472668597642946451)
    ·
      refine ⟨26455131709002896464419677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17636754472668597642946451 26455131709002896464419677)
      ·
        refine ⟨9920674390876086174157379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26455131709002896464419677 9920674390876086174157379)
        ·
          refine ⟨14881011586314129261236069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9920674390876086174157379 14881011586314129261236069)
          ·
            refine ⟨2790189672433899236481763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14881011586314129261236069 2790189672433899236481763)
            ·
              refine ⟨4185284508650848854722645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2790189672433899236481763 4185284508650848854722645)
              ·
                refine ⟨49046302835752135016281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4185284508650848854722645 49046302835752135016281)
                ·
                  rfl

theorem cell20_322371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 8].length) (baseStart_322371 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_322371 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_322371 prefixEnd_322371 := by exact prefixLift 322371
  have htrace : WordTrace (prefixWord ++ tailWord_322371) baseStart_322371 baseEnd_322371 := by
    simpa [prefixWord, tailWord_322371, baseEnd_322371] using wordTrace_append hprefix tailTrace_322371
  have hstable : (prefixWord ++ tailWord_322371).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322371).length < 2 ^ (prefixWord ++ tailWord_322371).sum := by decide
  have hdescent : baseEnd_322371 < baseStart_322371 := by decide
  rcases family_descends (prefixWord ++ tailWord_322371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322388 : List Nat := [2, 4, 1, 1, 4, 8]
def baseStart_322388 : Nat := 118140960795 + 322388 * 2 ^ 59
def prefixEnd_322388 : Nat := 4983230072969 + 3 ^ 40 * 322388 * 2
def baseEnd_322388 : Nat := 5449876584091848203041

theorem tailTrace_322388 : CollatzResearch.WordTrace tailWord_322388 prefixEnd_322388 5449876584091848203041 := by
  unfold tailWord_322388
  simp only [CollatzResearch.WordTrace]
  refine ⟨5879228178025405165999909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7838970904033873554666545 5879228178025405165999909)
  ·
    refine ⟨1102355283379763468624983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5879228178025405165999909 1102355283379763468624983)
    ·
      refine ⟨1653532925069645202937475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1102355283379763468624983 1653532925069645202937475)
      ·
        refine ⟨2480299387604467804406213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1653532925069645202937475 2480299387604467804406213)
        ·
          refine ⟨465056135175837713326165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2480299387604467804406213 465056135175837713326165)
          ·
            refine ⟨5449876584091848203041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 465056135175837713326165 5449876584091848203041)
            ·
              rfl

theorem cell20_322388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 8].length) (baseStart_322388 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_322388 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_322388 prefixEnd_322388 := by exact prefixLift 322388
  have htrace : WordTrace (prefixWord ++ tailWord_322388) baseStart_322388 baseEnd_322388 := by
    simpa [prefixWord, tailWord_322388, baseEnd_322388] using wordTrace_append hprefix tailTrace_322388
  have hstable : (prefixWord ++ tailWord_322388).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322388).length < 2 ^ (prefixWord ++ tailWord_322388).sum := by decide
  have hdescent : baseEnd_322388 < baseStart_322388 := by decide
  rcases family_descends (prefixWord ++ tailWord_322388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322422 : List Nat := [5, 1, 1, 3, 1, 2, 3, 4]
def baseStart_322422 : Nat := 118140960795 + 322422 * 2 ^ 59
def prefixEnd_322422 : Nat := 4983230072969 + 3 ^ 40 * 322422 * 2
def baseEnd_322422 : Nat := 49054062098975631449545

theorem tailTrace_322422 : CollatzResearch.WordTrace tailWord_322422 prefixEnd_322422 49054062098975631449545 := by
  unfold tailWord_322422
  simp only [CollatzResearch.WordTrace]
  refine ⟨734981027370477133671095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7839797625285089425825013 734981027370477133671095)
  ·
    refine ⟨1102471541055715700506643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 734981027370477133671095 1102471541055715700506643)
    ·
      refine ⟨1653707311583573550759965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1102471541055715700506643 1653707311583573550759965)
      ·
        refine ⟨620140241843840081534987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1653707311583573550759965 620140241843840081534987)
        ·
          refine ⟨930210362765760122302481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 620140241843840081534987 930210362765760122302481)
          ·
            refine ⟨697657772074320091726861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 930210362765760122302481 697657772074320091726861)
            ·
              refine ⟨261621664527870034397573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 697657772074320091726861 261621664527870034397573)
              ·
                refine ⟨49054062098975631449545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 261621664527870034397573 49054062098975631449545)
                ·
                  rfl

theorem cell20_322422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 3, 4].length) (baseStart_322422 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_322422 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_322422 prefixEnd_322422 := by exact prefixLift 322422
  have htrace : WordTrace (prefixWord ++ tailWord_322422) baseStart_322422 baseEnd_322422 := by
    simpa [prefixWord, tailWord_322422, baseEnd_322422] using wordTrace_append hprefix tailTrace_322422
  have hstable : (prefixWord ++ tailWord_322422).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322422).length < 2 ^ (prefixWord ++ tailWord_322422).sum := by decide
  have hdescent : baseEnd_322422 < baseStart_322422 := by decide
  rcases family_descends (prefixWord ++ tailWord_322422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322477 : List Nat := [1, 5, 2, 3, 1, 2, 2, 4]
def baseStart_322477 : Nat := 118140960795 + 322477 * 2 ^ 59
def prefixEnd_322477 : Nat := 4983230072969 + 3 ^ 40 * 322477 * 2
def baseEnd_322477 : Nat := 49062429931863715838359

theorem tailTrace_322477 : CollatzResearch.WordTrace tailWord_322477 prefixEnd_322477 49062429931863715838359 := by
  unfold tailWord_322477
  simp only [CollatzResearch.WordTrace]
  refine ⟨11761702452728378531989685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7841134968485585687993123 11761702452728378531989685)
  ·
    refine ⟨1102659604943285487374033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11761702452728378531989685 1102659604943285487374033)
    ·
      refine ⟨826994703707464115530525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1102659604943285487374033 826994703707464115530525)
      ·
        refine ⟨310123013890299043323947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 826994703707464115530525 310123013890299043323947)
        ·
          refine ⟨465184520835448564985921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 310123013890299043323947 465184520835448564985921)
          ·
            refine ⟨348888390626586423739441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 465184520835448564985921 348888390626586423739441)
            ·
              refine ⟨261666292969939817804581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 348888390626586423739441 261666292969939817804581)
              ·
                refine ⟨49062429931863715838359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 261666292969939817804581 49062429931863715838359)
                ·
                  rfl

theorem cell20_322477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 2, 4].length) (baseStart_322477 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_322477 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_322477 prefixEnd_322477 := by exact prefixLift 322477
  have htrace : WordTrace (prefixWord ++ tailWord_322477) baseStart_322477 baseEnd_322477 := by
    simpa [prefixWord, tailWord_322477, baseEnd_322477] using wordTrace_append hprefix tailTrace_322477
  have hstable : (prefixWord ++ tailWord_322477).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322477).length < 2 ^ (prefixWord ++ tailWord_322477).sum := by decide
  have hdescent : baseEnd_322477 < baseStart_322477 := by decide
  rcases family_descends (prefixWord ++ tailWord_322477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322495 : List Nat := [1, 1, 2, 2, 2, 1, 2, 7, 2]
def baseStart_322495 : Nat := 118140960795 + 322495 * 2 ^ 59
def prefixEnd_322495 : Nat := 4983230072969 + 3 ^ 40 * 322495 * 2
def baseEnd_322495 : Nat := 147195505486063084915003

theorem tailTrace_322495 : CollatzResearch.WordTrace tailWord_322495 prefixEnd_322495 147195505486063084915003 := by
  unfold tailWord_322495
  simp only [CollatzResearch.WordTrace]
  refine ⟨11762358966663167606144939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7841572644442111737429959 11762358966663167606144939)
  ·
    refine ⟨17643538449994751409217409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11762358966663167606144939 17643538449994751409217409)
    ·
      refine ⟨13232653837496063556913057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17643538449994751409217409 13232653837496063556913057)
      ·
        refine ⟨9924490378122047667684793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13232653837496063556913057 9924490378122047667684793)
        ·
          refine ⟨7443367783591535750763595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9924490378122047667684793 7443367783591535750763595)
          ·
            refine ⟨11165051675387303626145393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7443367783591535750763595 11165051675387303626145393)
            ·
              refine ⟨8373788756540477719609045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11165051675387303626145393 8373788756540477719609045)
              ·
                refine ⟨196260673981417446553337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 8373788756540477719609045 196260673981417446553337)
                ·
                  refine ⟨147195505486063084915003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 196260673981417446553337 147195505486063084915003)
                  ·
                    rfl

theorem cell20_322495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 7, 2].length) (baseStart_322495 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_322495 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_322495 prefixEnd_322495 := by exact prefixLift 322495
  have htrace : WordTrace (prefixWord ++ tailWord_322495) baseStart_322495 baseEnd_322495 := by
    simpa [prefixWord, tailWord_322495, baseEnd_322495] using wordTrace_append hprefix tailTrace_322495
  have hstable : (prefixWord ++ tailWord_322495).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322495).length < 2 ^ (prefixWord ++ tailWord_322495).sum := by decide
  have hdescent : baseEnd_322495 < baseStart_322495 := by decide
  rcases family_descends (prefixWord ++ tailWord_322495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322561 : List Nat := [1, 2, 4, 1, 2, 10]
def baseStart_322561 : Nat := 118140960795 + 322561 * 2 ^ 59
def prefixEnd_322561 : Nat := 4983230072969 + 3 ^ 40 * 322561 * 2
def baseEnd_322561 : Nat := 5452801099424451433879

theorem tailTrace_322561 : CollatzResearch.WordTrace tailWord_322561 prefixEnd_322561 5452801099424451433879 := by
  unfold tailWord_322561
  simp only [CollatzResearch.WordTrace]
  refine ⟨11764766184424060878047537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7843177456282707252031691 11764766184424060878047537)
  ·
    refine ⟨8823574638318045658535653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11764766184424060878047537 8823574638318045658535653)
    ·
      refine ⟨1654420244684633560975435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8823574638318045658535653 1654420244684633560975435)
      ·
        refine ⟨2481630367026950341463153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1654420244684633560975435 2481630367026950341463153)
        ·
          refine ⟨1861222775270212756097365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2481630367026950341463153 1861222775270212756097365)
          ·
            refine ⟨5452801099424451433879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1861222775270212756097365 5452801099424451433879)
            ·
              rfl

theorem cell20_322561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 10].length) (baseStart_322561 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_322561 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_322561 prefixEnd_322561 := by exact prefixLift 322561
  have htrace : WordTrace (prefixWord ++ tailWord_322561) baseStart_322561 baseEnd_322561 := by
    simpa [prefixWord, tailWord_322561, baseEnd_322561] using wordTrace_append hprefix tailTrace_322561
  have hstable : (prefixWord ++ tailWord_322561).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322561).length < 2 ^ (prefixWord ++ tailWord_322561).sum := by decide
  have hdescent : baseEnd_322561 < baseStart_322561 := by decide
  rcases family_descends (prefixWord ++ tailWord_322561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322585 : List Nat := [1, 2, 1, 2, 1, 1, 6, 3, 3]
def baseStart_322585 : Nat := 118140960795 + 322585 * 2 ^ 59
def prefixEnd_322585 : Nat := 4983230072969 + 3 ^ 40 * 322585 * 2
def baseEnd_322585 : Nat := 147236583938422771914635

theorem tailTrace_322585 : CollatzResearch.WordTrace tailWord_322585 prefixEnd_322585 147236583938422771914635 := by
  unfold tailWord_322585
  simp only [CollatzResearch.WordTrace]
  refine ⟨11765641536337112976921209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7843761024224741984614139 11765641536337112976921209)
  ·
    refine ⟨8824231152252834732690907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11765641536337112976921209 8824231152252834732690907)
    ·
      refine ⟨13236346728379252099036361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8824231152252834732690907 13236346728379252099036361)
      ·
        refine ⟨9927260046284439074277271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13236346728379252099036361 9927260046284439074277271)
        ·
          refine ⟨14890890069426658611415907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9927260046284439074277271 14890890069426658611415907)
          ·
            refine ⟨22336335104139987917123861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14890890069426658611415907 22336335104139987917123861)
            ·
              refine ⟨1047015708006561933615181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 22336335104139987917123861 1047015708006561933615181)
              ·
                refine ⟨392630890502460725105693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1047015708006561933615181 392630890502460725105693)
                ·
                  refine ⟨147236583938422771914635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 392630890502460725105693 147236583938422771914635)
                  ·
                    rfl

theorem cell20_322585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 3, 3].length) (baseStart_322585 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_322585 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_322585 prefixEnd_322585 := by exact prefixLift 322585
  have htrace : WordTrace (prefixWord ++ tailWord_322585) baseStart_322585 baseEnd_322585 := by
    simpa [prefixWord, tailWord_322585, baseEnd_322585] using wordTrace_append hprefix tailTrace_322585
  have hstable : (prefixWord ++ tailWord_322585).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322585).length < 2 ^ (prefixWord ++ tailWord_322585).sum := by decide
  have hdescent : baseEnd_322585 < baseStart_322585 := by decide
  rcases family_descends (prefixWord ++ tailWord_322585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322646 : List Nat := [5, 2, 2, 1, 3, 1, 2, 4]
def baseStart_322646 : Nat := 118140960795 + 322646 * 2 ^ 59
def prefixEnd_322646 : Nat := 4983230072969 + 3 ^ 40 * 322646 * 2
def baseEnd_322646 : Nat := 49088142000192556960351

theorem tailTrace_322646 : CollatzResearch.WordTrace tailWord_322646 prefixEnd_322646 49088142000192556960351 := by
  unfold tailWord_322646
  simp only [CollatzResearch.WordTrace]
  refine ⟨735491649319757524680737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7845244259410746929927861 735491649319757524680737)
  ·
    refine ⟨551618736989818143510553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 735491649319757524680737 551618736989818143510553)
    ·
      refine ⟨413714052742363607632915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 551618736989818143510553 413714052742363607632915)
      ·
        refine ⟨620571079113545411449373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 413714052742363607632915 620571079113545411449373)
        ·
          refine ⟨232714154667579529293515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 620571079113545411449373 232714154667579529293515)
          ·
            refine ⟨349071232001369293940273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 232714154667579529293515 349071232001369293940273)
            ·
              refine ⟨261803424001026970455205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 349071232001369293940273 261803424001026970455205)
              ·
                refine ⟨49088142000192556960351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 261803424001026970455205 49088142000192556960351)
                ·
                  rfl

theorem cell20_322646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 2, 4].length) (baseStart_322646 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_322646 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_322646 prefixEnd_322646 := by exact prefixLift 322646
  have htrace : WordTrace (prefixWord ++ tailWord_322646) baseStart_322646 baseEnd_322646 := by
    simpa [prefixWord, tailWord_322646, baseEnd_322646] using wordTrace_append hprefix tailTrace_322646
  have hstable : (prefixWord ++ tailWord_322646).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322646).length < 2 ^ (prefixWord ++ tailWord_322646).sum := by decide
  have hdescent : baseEnd_322646 < baseStart_322646 := by decide
  rcases family_descends (prefixWord ++ tailWord_322646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322678 : List Nat := [5, 1, 1, 2, 1, 1, 2, 4, 3]
def baseStart_322678 : Nat := 118140960795 + 322678 * 2 ^ 59
def prefixEnd_322678 : Nat := 4983230072969 + 3 ^ 40 * 322678 * 2
def baseEnd_322678 : Nat := 147279031672527781814255

theorem tailTrace_322678 : CollatzResearch.WordTrace tailWord_322678 prefixEnd_322678 147279031672527781814255 := by
  unfold tailWord_322678
  simp only [CollatzResearch.WordTrace]
  refine ⟨735564595312511866253543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7846022350000126573371125 735564595312511866253543)
  ·
    refine ⟨1103346892968767799380315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 735564595312511866253543 1103346892968767799380315)
    ·
      refine ⟨1655020339453151699070473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1103346892968767799380315 1655020339453151699070473)
      ·
        refine ⟨1241265254589863774302855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1655020339453151699070473 1241265254589863774302855)
        ·
          refine ⟨1861897881884795661454283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1241265254589863774302855 1861897881884795661454283)
          ·
            refine ⟨2792846822827193492181425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1861897881884795661454283 2792846822827193492181425)
            ·
              refine ⟨2094635117120395119136069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2792846822827193492181425 2094635117120395119136069)
              ·
                refine ⟨392744084460074084838013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2094635117120395119136069 392744084460074084838013)
                ·
                  refine ⟨147279031672527781814255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 392744084460074084838013 147279031672527781814255)
                  ·
                    rfl

theorem cell20_322678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 4, 3].length) (baseStart_322678 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_322678 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_322678 prefixEnd_322678 := by exact prefixLift 322678
  have htrace : WordTrace (prefixWord ++ tailWord_322678) baseStart_322678 baseEnd_322678 := by
    simpa [prefixWord, tailWord_322678, baseEnd_322678] using wordTrace_append hprefix tailTrace_322678
  have hstable : (prefixWord ++ tailWord_322678).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322678).length < 2 ^ (prefixWord ++ tailWord_322678).sum := by decide
  have hdescent : baseEnd_322678 < baseStart_322678 := by decide
  rcases family_descends (prefixWord ++ tailWord_322678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322681 : List Nat := [1, 2, 1, 3, 5, 1, 3, 2, 2]
def baseStart_322681 : Nat := 118140960795 + 322681 * 2 ^ 59
def prefixEnd_322681 : Nat := 4983230072969 + 3 ^ 40 * 322681 * 2
def baseEnd_322681 : Nat := 147280400954273104714243

theorem tailTrace_322681 : CollatzResearch.WordTrace tailWord_322681 prefixEnd_322681 147280400954273104714243 := by
  unfold tailWord_322681
  simp only [CollatzResearch.WordTrace]
  refine ⟨11769142943989321372415897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7846095295992880914943931 11769142943989321372415897)
  ·
    refine ⟨8826857207991991029311923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11769142943989321372415897 8826857207991991029311923)
    ·
      refine ⟨13240285811987986543967885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8826857207991991029311923 13240285811987986543967885)
      ·
        refine ⟨4965107179495494953987957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13240285811987986543967885 4965107179495494953987957)
        ·
          refine ⟨465478798077702651936371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4965107179495494953987957 465478798077702651936371)
          ·
            refine ⟨698218197116553977904557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 465478798077702651936371 698218197116553977904557)
            ·
              refine ⟨261831823918707741714209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 698218197116553977904557 261831823918707741714209)
              ·
                refine ⟨196373867939030806285657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 261831823918707741714209 196373867939030806285657)
                ·
                  refine ⟨147280400954273104714243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 196373867939030806285657 147280400954273104714243)
                  ·
                    rfl

theorem cell20_322681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 3, 2, 2].length) (baseStart_322681 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_322681 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_322681 prefixEnd_322681 := by exact prefixLift 322681
  have htrace : WordTrace (prefixWord ++ tailWord_322681) baseStart_322681 baseEnd_322681 := by
    simpa [prefixWord, tailWord_322681, baseEnd_322681] using wordTrace_append hprefix tailTrace_322681
  have hstable : (prefixWord ++ tailWord_322681).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322681).length < 2 ^ (prefixWord ++ tailWord_322681).sum := by decide
  have hdescent : baseEnd_322681 < baseStart_322681 := by decide
  rcases family_descends (prefixWord ++ tailWord_322681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322692 : List Nat := [2, 3, 2, 1, 2, 3, 2, 5]
def baseStart_322692 : Nat := 118140960795 + 322692 * 2 ^ 59
def prefixEnd_322692 : Nat := 4983230072969 + 3 ^ 40 * 322692 * 2
def baseEnd_322692 : Nat := 49095140551335318449177

theorem tailTrace_322692 : CollatzResearch.WordTrace tailWord_322692 prefixEnd_322692 49095140551335318449177 := by
  unfold tailWord_322692
  simp only [CollatzResearch.WordTrace]
  refine ⟨5884772073474735125533165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7846362764632980167377553 5884772073474735125533165)
  ·
    refine ⟨2206789527553025672074937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5884772073474735125533165 2206789527553025672074937)
    ·
      refine ⟨1655092145664769254056203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2206789527553025672074937 1655092145664769254056203)
      ·
        refine ⟨2482638218497153881084305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1655092145664769254056203 2482638218497153881084305)
        ·
          refine ⟨1861978663872865410813229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2482638218497153881084305 1861978663872865410813229)
          ·
            refine ⟨698241998952324529054961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1861978663872865410813229 698241998952324529054961)
            ·
              refine ⟨523681499214243396791221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 698241998952324529054961 523681499214243396791221)
              ·
                refine ⟨49095140551335318449177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 523681499214243396791221 49095140551335318449177)
                ·
                  rfl

theorem cell20_322692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 2, 5].length) (baseStart_322692 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_322692 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_322692 prefixEnd_322692 := by exact prefixLift 322692
  have htrace : WordTrace (prefixWord ++ tailWord_322692) baseStart_322692 baseEnd_322692 := by
    simpa [prefixWord, tailWord_322692, baseEnd_322692] using wordTrace_append hprefix tailTrace_322692
  have hstable : (prefixWord ++ tailWord_322692).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322692).length < 2 ^ (prefixWord ++ tailWord_322692).sum := by decide
  have hdescent : baseEnd_322692 < baseStart_322692 := by decide
  rcases family_descends (prefixWord ++ tailWord_322692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
