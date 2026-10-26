import V185TrunkScan23Chunk0571

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3382130 : List Nat := [3, 2, 1, 2, 1, 1, 3, 2, 1, 7]
def baseStart_3382130 : Nat := 118140960795 + 3382130 * 2 ^ 59
def prefixEnd_3382130 : Nat := 4983230072969 + 3 ^ 40 * 3382130 * 2
def baseEnd_3382130 : Nat := 578886108663652544840291

theorem tailTrace_3382130 : CollatzResearch.WordTrace tailWord_3382130 prefixEnd_3382130 578886108663652544840291 := by
  unfold tailWord_3382130
  simp only [CollatzResearch.WordTrace]
  refine ⟨30839103809282026665571961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82237610158085404441525229 30839103809282026665571961)
  ·
    refine ⟨23129327856961519999178971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30839103809282026665571961 23129327856961519999178971)
    ·
      refine ⟨34693991785442279998768457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23129327856961519999178971 34693991785442279998768457)
      ·
        refine ⟨26020493839081709999076343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34693991785442279998768457 26020493839081709999076343)
        ·
          refine ⟨39030740758622564998614515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26020493839081709999076343 39030740758622564998614515)
          ·
            refine ⟨58546111137933847497921773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39030740758622564998614515 58546111137933847497921773)
            ·
              refine ⟨21954791676725192811720665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58546111137933847497921773 21954791676725192811720665)
              ·
                refine ⟨16466093757543894608790499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21954791676725192811720665 16466093757543894608790499)
                ·
                  refine ⟨24699140636315841913185749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16466093757543894608790499 24699140636315841913185749)
                  ·
                    refine ⟨578886108663652544840291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24699140636315841913185749 578886108663652544840291)
                    ·
                      rfl

theorem cell23_3382130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 2, 1, 7].length) (baseStart_3382130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3382130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3382130 prefixEnd_3382130 := by exact prefixLift 3382130
  have htrace : WordTrace (prefixWord ++ tailWord_3382130) baseStart_3382130 baseEnd_3382130 := by
    simpa [prefixWord, tailWord_3382130, baseEnd_3382130] using wordTrace_append hprefix tailTrace_3382130
  have hstable : (prefixWord ++ tailWord_3382130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3382130).length < 2 ^ (prefixWord ++ tailWord_3382130).sum := by decide
  have hdescent : baseEnd_3382130 < baseStart_3382130 := by decide
  rcases family_descends (prefixWord ++ tailWord_3382130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3382167 : List Nat := [1, 1, 3, 3, 1, 2, 3, 2, 2, 1, 4]
def baseStart_3382167 : Nat := 118140960795 + 3382167 * 2 ^ 59
def prefixEnd_3382167 : Nat := 4983230072969 + 3 ^ 40 * 3382167 * 2
def baseEnd_3382167 : Nat := 1736677324775173989758203

theorem tailTrace_3382167 : CollatzResearch.WordTrace tailWord_3382167 prefixEnd_3382167 1736677324775173989758203 := by
  unfold tailWord_3382167
  simp only [CollatzResearch.WordTrace]
  refine ⟨123357764737994061981384755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82238509825329374654256503 123357764737994061981384755)
  ·
    refine ⟨185036647106991092972077133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123357764737994061981384755 185036647106991092972077133)
    ·
      refine ⟨69388742665121659864528925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185036647106991092972077133 69388742665121659864528925)
      ·
        refine ⟨26020778499420622449198347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69388742665121659864528925 26020778499420622449198347)
        ·
          refine ⟨39031167749130933673797521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26020778499420622449198347 39031167749130933673797521)
          ·
            refine ⟨29273375811848200255348141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39031167749130933673797521 29273375811848200255348141)
            ·
              refine ⟨10977515929443075095755553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29273375811848200255348141 10977515929443075095755553)
              ·
                refine ⟨8233136947082306321816665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10977515929443075095755553 8233136947082306321816665)
                ·
                  refine ⟨6174852710311729741362499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8233136947082306321816665 6174852710311729741362499)
                  ·
                    refine ⟨9262279065467594612043749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6174852710311729741362499 9262279065467594612043749)
                    ·
                      refine ⟨1736677324775173989758203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9262279065467594612043749 1736677324775173989758203)
                      ·
                        rfl

theorem cell23_3382167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 2, 2, 1, 4].length) (baseStart_3382167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3382167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3382167 prefixEnd_3382167 := by exact prefixLift 3382167
  have htrace : WordTrace (prefixWord ++ tailWord_3382167) baseStart_3382167 baseEnd_3382167 := by
    simpa [prefixWord, tailWord_3382167, baseEnd_3382167] using wordTrace_append hprefix tailTrace_3382167
  have hstable : (prefixWord ++ tailWord_3382167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3382167).length < 2 ^ (prefixWord ++ tailWord_3382167).sum := by decide
  have hdescent : baseEnd_3382167 < baseStart_3382167 := by decide
  rcases family_descends (prefixWord ++ tailWord_3382167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3382228 : List Nat := [2, 4, 1, 2, 1, 2, 4, 2, 1, 4]
def baseStart_3382228 : Nat := 118140960795 + 3382228 * 2 ^ 59
def prefixEnd_3382228 : Nat := 4983230072969 + 3 ^ 40 * 3382228 * 2
def baseEnd_3382228 : Nat := 578902882365032750365141

theorem tailTrace_3382228 : CollatzResearch.WordTrace tailWord_3382228 prefixEnd_3382228 578902882365032750365141 := by
  unfold tailWord_3382228
  simp only [CollatzResearch.WordTrace]
  refine ⟨61679994795386534699677669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82239993060515379599570225 61679994795386534699677669)
  ·
    refine ⟨11564999024134975256189563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61679994795386534699677669 11564999024134975256189563)
    ·
      refine ⟨17347498536202462884284345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11564999024134975256189563 17347498536202462884284345)
      ·
        refine ⟨13010623902151847163213259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17347498536202462884284345 13010623902151847163213259)
        ·
          refine ⟨19515935853227770744819889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13010623902151847163213259 19515935853227770744819889)
          ·
            refine ⟨14636951889920828058614917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19515935853227770744819889 14636951889920828058614917)
            ·
              refine ⟨2744428479360155260990297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14636951889920828058614917 2744428479360155260990297)
              ·
                refine ⟨2058321359520116445742723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2744428479360155260990297 2058321359520116445742723)
                ·
                  refine ⟨3087482039280174668614085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2058321359520116445742723 3087482039280174668614085)
                  ·
                    refine ⟨578902882365032750365141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3087482039280174668614085 578902882365032750365141)
                    ·
                      rfl

theorem cell23_3382228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 4, 2, 1, 4].length) (baseStart_3382228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3382228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3382228 prefixEnd_3382228 := by exact prefixLift 3382228
  have htrace : WordTrace (prefixWord ++ tailWord_3382228) baseStart_3382228 baseEnd_3382228 := by
    simpa [prefixWord, tailWord_3382228, baseEnd_3382228] using wordTrace_append hprefix tailTrace_3382228
  have hstable : (prefixWord ++ tailWord_3382228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3382228).length < 2 ^ (prefixWord ++ tailWord_3382228).sum := by decide
  have hdescent : baseEnd_3382228 < baseStart_3382228 := by decide
  rcases family_descends (prefixWord ++ tailWord_3382228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3382267 : List Nat := [1, 1, 1, 1, 1, 3, 3, 4, 4, 4]
def baseStart_3382267 : Nat := 118140960795 + 3382267 * 2 ^ 59
def prefixEnd_3382267 : Nat := 4983230072969 + 3 ^ 40 * 3382267 * 2
def baseEnd_3382267 : Nat := 578909557613541199502581

theorem tailTrace_3382267 : CollatzResearch.WordTrace tailWord_3382267 prefixEnd_3382267 578909557613541199502581 := by
  unfold tailWord_3382267
  simp only [CollatzResearch.WordTrace]
  refine ⟨123361412037631779060025055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82240941358421186040016703 123361412037631779060025055)
  ·
    refine ⟨185042118056447668590037583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123361412037631779060025055 185042118056447668590037583)
    ·
      refine ⟨277563177084671502885056375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185042118056447668590037583 277563177084671502885056375)
      ·
        refine ⟨416344765627007254327584563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277563177084671502885056375 416344765627007254327584563)
        ·
          refine ⟨624517148440510881491376845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 416344765627007254327584563 624517148440510881491376845)
          ·
            refine ⟨234193930665191580559266317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 624517148440510881491376845 234193930665191580559266317)
            ·
              refine ⟨87822723999446842709724869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 234193930665191580559266317 87822723999446842709724869)
              ·
                refine ⟨16466760749896283008073413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87822723999446842709724869 16466760749896283008073413)
                ·
                  refine ⟨3087517640605553064013765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16466760749896283008073413 3087517640605553064013765)
                  ·
                    refine ⟨578909557613541199502581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3087517640605553064013765 578909557613541199502581)
                    ·
                      rfl

theorem cell23_3382267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4, 4, 4].length) (baseStart_3382267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3382267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3382267 prefixEnd_3382267 := by exact prefixLift 3382267
  have htrace : WordTrace (prefixWord ++ tailWord_3382267) baseStart_3382267 baseEnd_3382267 := by
    simpa [prefixWord, tailWord_3382267, baseEnd_3382267] using wordTrace_append hprefix tailTrace_3382267
  have hstable : (prefixWord ++ tailWord_3382267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3382267).length < 2 ^ (prefixWord ++ tailWord_3382267).sum := by decide
  have hdescent : baseEnd_3382267 < baseStart_3382267 := by decide
  rcases family_descends (prefixWord ++ tailWord_3382267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3382268 : List Nat := [2, 2, 2, 1, 2, 4, 2, 3, 1, 1, 3]
def baseStart_3382268 : Nat := 118140960795 + 3382268 * 2 ^ 59
def prefixEnd_3382268 : Nat := 4983230072969 + 3 ^ 40 * 3382268 * 2
def baseEnd_3382268 : Nat := 1736729186321278094595239

theorem tailTrace_3382268 : CollatzResearch.WordTrace tailWord_3382268 prefixEnd_3382268 1736729186321278094595239 := by
  unfold tailWord_3382268
  simp only [CollatzResearch.WordTrace]
  refine ⟨61680724255314078115405729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82240965673752104153874305 61680724255314078115405729)
  ·
    refine ⟨46260543191485558586554297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61680724255314078115405729 46260543191485558586554297)
    ·
      refine ⟨34695407393614168939915723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46260543191485558586554297 34695407393614168939915723)
      ·
        refine ⟨52043111090421253409873585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34695407393614168939915723 52043111090421253409873585)
        ·
          refine ⟨39032333317815940057405189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52043111090421253409873585 39032333317815940057405189)
          ·
            refine ⟨7318562497090488760763473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39032333317815940057405189 7318562497090488760763473)
            ·
              refine ⟨5488921872817866570572605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7318562497090488760763473 5488921872817866570572605)
              ·
                refine ⟨2058345702306699963964727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5488921872817866570572605 2058345702306699963964727)
                ·
                  refine ⟨3087518553460049945947091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2058345702306699963964727 3087518553460049945947091)
                  ·
                    refine ⟨4631277830190074918920637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3087518553460049945947091 4631277830190074918920637)
                    ·
                      refine ⟨1736729186321278094595239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4631277830190074918920637 1736729186321278094595239)
                      ·
                        rfl

theorem cell23_3382268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 2, 3, 1, 1, 3].length) (baseStart_3382268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3382268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3382268 prefixEnd_3382268 := by exact prefixLift 3382268
  have htrace : WordTrace (prefixWord ++ tailWord_3382268) baseStart_3382268 baseEnd_3382268 := by
    simpa [prefixWord, tailWord_3382268, baseEnd_3382268] using wordTrace_append hprefix tailTrace_3382268
  have hstable : (prefixWord ++ tailWord_3382268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3382268).length < 2 ^ (prefixWord ++ tailWord_3382268).sum := by decide
  have hdescent : baseEnd_3382268 < baseStart_3382268 := by decide
  rcases family_descends (prefixWord ++ tailWord_3382268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3382277 : List Nat := [1, 3, 1, 1, 2, 3, 2, 3, 1, 1, 5]
def baseStart_3382277 : Nat := 118140960795 + 3382277 * 2 ^ 59
def prefixEnd_3382277 : Nat := 4983230072969 + 3 ^ 40 * 3382277 * 2
def baseEnd_3382277 : Nat := 1736733807647168559382697

theorem tailTrace_3382277 : CollatzResearch.WordTrace tailWord_3382277 prefixEnd_3382277 1736733807647168559382697 := by
  unfold tailWord_3382277
  simp only [CollatzResearch.WordTrace]
  refine ⟨123361776767595550767889085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82241184511730367178592723 123361776767595550767889085)
  ·
    refine ⟨46260666287848331537958407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123361776767595550767889085 46260666287848331537958407)
    ·
      refine ⟨69390999431772497306937611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46260666287848331537958407 69390999431772497306937611)
      ·
        refine ⟨104086499147658745960406417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69390999431772497306937611 104086499147658745960406417)
        ·
          refine ⟨78064874360744059470304813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104086499147658745960406417 78064874360744059470304813)
          ·
            refine ⟨29274327885279022301364305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78064874360744059470304813 29274327885279022301364305)
            ·
              refine ⟨21955745913959266726023229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29274327885279022301364305 21955745913959266726023229)
              ·
                refine ⟨8233404717734725022258711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21955745913959266726023229 8233404717734725022258711)
                ·
                  refine ⟨12350107076602087533388067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8233404717734725022258711 12350107076602087533388067)
                  ·
                    refine ⟨18525160614903131300082101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12350107076602087533388067 18525160614903131300082101)
                    ·
                      refine ⟨1736733807647168559382697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18525160614903131300082101 1736733807647168559382697)
                      ·
                        rfl

theorem cell23_3382277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 3, 1, 1, 5].length) (baseStart_3382277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3382277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3382277 prefixEnd_3382277 := by exact prefixLift 3382277
  have htrace : WordTrace (prefixWord ++ tailWord_3382277) baseStart_3382277 baseEnd_3382277 := by
    simpa [prefixWord, tailWord_3382277, baseEnd_3382277] using wordTrace_append hprefix tailTrace_3382277
  have hstable : (prefixWord ++ tailWord_3382277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3382277).length < 2 ^ (prefixWord ++ tailWord_3382277).sum := by decide
  have hdescent : baseEnd_3382277 < baseStart_3382277 := by decide
  rcases family_descends (prefixWord ++ tailWord_3382277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3382284 : List Nat := [2, 2, 1, 2, 3, 3, 1, 1, 4, 4]
def baseStart_3382284 : Nat := 118140960795 + 3382284 * 2 ^ 59
def prefixEnd_3382284 : Nat := 4983230072969 + 3 ^ 40 * 3382284 * 2
def baseEnd_3382284 : Nat := 578912467337250010665055

theorem tailTrace_3382284 : CollatzResearch.WordTrace tailWord_3382284 prefixEnd_3382284 578912467337250010665055 := by
  unfold tailWord_3382284
  simp only [CollatzResearch.WordTrace]
  refine ⟨61681016039285095481696953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82241354719046793975595937 61681016039285095481696953)
  ·
    refine ⟨46260762029463821611272715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61681016039285095481696953 46260762029463821611272715)
    ·
      refine ⟨69391143044195732416909073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46260762029463821611272715 69391143044195732416909073)
      ·
        refine ⟨52043357283146799312681805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69391143044195732416909073 52043357283146799312681805)
        ·
          refine ⟨19516258981180049742255677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52043357283146799312681805 19516258981180049742255677)
          ·
            refine ⟨7318597117942518653345879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19516258981180049742255677 7318597117942518653345879)
            ·
              refine ⟨10977895676913777980018819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7318597117942518653345879 10977895676913777980018819)
              ·
                refine ⟨16466843515370666970028229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10977895676913777980018819 16466843515370666970028229)
                ·
                  refine ⟨3087533159132000056880293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16466843515370666970028229 3087533159132000056880293)
                  ·
                    refine ⟨578912467337250010665055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3087533159132000056880293 578912467337250010665055)
                    ·
                      rfl

theorem cell23_3382284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 1, 4, 4].length) (baseStart_3382284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3382284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3382284 prefixEnd_3382284 := by exact prefixLift 3382284
  have htrace : WordTrace (prefixWord ++ tailWord_3382284) baseStart_3382284 baseEnd_3382284 := by
    simpa [prefixWord, tailWord_3382284, baseEnd_3382284] using wordTrace_append hprefix tailTrace_3382284
  have hstable : (prefixWord ++ tailWord_3382284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3382284).length < 2 ^ (prefixWord ++ tailWord_3382284).sum := by decide
  have hdescent : baseEnd_3382284 < baseStart_3382284 := by decide
  rcases family_descends (prefixWord ++ tailWord_3382284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3382301 : List Nat := [1, 4, 2, 2, 3, 2, 1, 1, 1, 6]
def baseStart_3382301 : Nat := 118140960795 + 3382301 * 2 ^ 59
def prefixEnd_3382301 : Nat := 4983230072969 + 3 ^ 40 * 3382301 * 2
def baseEnd_3382301 : Nat := 578915377060958821827529

theorem tailTrace_3382301 : CollatzResearch.WordTrace tailWord_3382301 prefixEnd_3382301 578915377060958821827529 := by
  unfold tailWord_3382301
  simp only [CollatzResearch.WordTrace]
  refine ⟨123362652119508602866762757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82241768079672401911175171 123362652119508602866762757)
  ·
    refine ⟨23130497272407863037518017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123362652119508602866762757 23130497272407863037518017)
    ·
      refine ⟨17347872954305897278138513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23130497272407863037518017 17347872954305897278138513)
      ·
        refine ⟨13010904715729422958603885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17347872954305897278138513 13010904715729422958603885)
        ·
          refine ⟨4879089268398533609476457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13010904715729422958603885 4879089268398533609476457)
          ·
            refine ⟨3659316951298900207107343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4879089268398533609476457 3659316951298900207107343)
            ·
              refine ⟨5488975426948350310661015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3659316951298900207107343 5488975426948350310661015)
              ·
                refine ⟨8233463140422525465991523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5488975426948350310661015 8233463140422525465991523)
                ·
                  refine ⟨12350194710633788198987285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8233463140422525465991523 12350194710633788198987285)
                  ·
                    refine ⟨578915377060958821827529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12350194710633788198987285 578915377060958821827529)
                    ·
                      rfl

theorem cell23_3382301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 1, 1, 1, 6].length) (baseStart_3382301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3382301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3382301 prefixEnd_3382301 := by exact prefixLift 3382301
  have htrace : WordTrace (prefixWord ++ tailWord_3382301) baseStart_3382301 baseEnd_3382301 := by
    simpa [prefixWord, tailWord_3382301, baseEnd_3382301] using wordTrace_append hprefix tailTrace_3382301
  have hstable : (prefixWord ++ tailWord_3382301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3382301).length < 2 ^ (prefixWord ++ tailWord_3382301).sum := by decide
  have hdescent : baseEnd_3382301 < baseStart_3382301 := by decide
  rcases family_descends (prefixWord ++ tailWord_3382301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3382308 : List Nat := [2, 3, 1, 4, 1, 1, 2, 2, 3, 2, 2]
def baseStart_3382308 : Nat := 118140960795 + 3382308 * 2 ^ 59
def prefixEnd_3382308 : Nat := 4983230072969 + 3 ^ 40 * 3382308 * 2
def baseEnd_3382308 : Nat := 1736749725547457938095055

theorem tailTrace_3382308 : CollatzResearch.WordTrace tailWord_3382308 prefixEnd_3382308 1736749725547457938095055 := by
  unfold tailWord_3382308
  simp only [CollatzResearch.WordTrace]
  refine ⟨61681453715241621531133789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82241938286988828708178385 61681453715241621531133789)
  ·
    refine ⟨23130545143215608074175171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61681453715241621531133789 23130545143215608074175171)
    ·
      refine ⟨34695817714823412111262757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23130545143215608074175171 34695817714823412111262757)
      ·
        refine ⟨6505465821529389770861767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34695817714823412111262757 6505465821529389770861767)
        ·
          refine ⟨9758198732294084656292651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6505465821529389770861767 9758198732294084656292651)
          ·
            refine ⟨14637298098441126984438977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9758198732294084656292651 14637298098441126984438977)
            ·
              refine ⟨10977973573830845238329233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14637298098441126984438977 10977973573830845238329233)
              ·
                refine ⟨8233480180373133928746925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10977973573830845238329233 8233480180373133928746925)
                ·
                  refine ⟨3087555067639925223280097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8233480180373133928746925 3087555067639925223280097)
                  ·
                    refine ⟨2315666300729943917460073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3087555067639925223280097 2315666300729943917460073)
                    ·
                      refine ⟨1736749725547457938095055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2315666300729943917460073 1736749725547457938095055)
                      ·
                        rfl

theorem cell23_3382308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 2, 3, 2, 2].length) (baseStart_3382308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3382308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3382308 prefixEnd_3382308 := by exact prefixLift 3382308
  have htrace : WordTrace (prefixWord ++ tailWord_3382308) baseStart_3382308 baseEnd_3382308 := by
    simpa [prefixWord, tailWord_3382308, baseEnd_3382308] using wordTrace_append hprefix tailTrace_3382308
  have hstable : (prefixWord ++ tailWord_3382308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3382308).length < 2 ^ (prefixWord ++ tailWord_3382308).sum := by decide
  have hdescent : baseEnd_3382308 < baseStart_3382308 := by decide
  rcases family_descends (prefixWord ++ tailWord_3382308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3382314 : List Nat := [3, 1, 4, 1, 3, 1, 1, 9]
def baseStart_3382314 : Nat := 118140960795 + 3382314 * 2 ^ 59
def prefixEnd_3382314 : Nat := 4983230072969 + 3 ^ 40 * 3382314 * 2
def baseEnd_3382314 : Nat := 64324178015977219060001

theorem tailTrace_3382314 : CollatzResearch.WordTrace tailWord_3382314 prefixEnd_3382314 64324178015977219060001 := by
  unfold tailWord_3382314
  simp only [CollatzResearch.WordTrace]
  refine ⟨30840781567115376521746499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82242084178974337391323997 30840781567115376521746499)
  ·
    refine ⟨46261172350673064782619749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30840781567115376521746499 46261172350673064782619749)
    ·
      refine ⟨8673969815751199646741203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46261172350673064782619749 8673969815751199646741203)
      ·
        refine ⟨13010954723626799470111805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8673969815751199646741203 13010954723626799470111805)
        ·
          refine ⟨4879108021360049801291927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13010954723626799470111805 4879108021360049801291927)
          ·
            refine ⟨7318662032040074701937891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4879108021360049801291927 7318662032040074701937891)
            ·
              refine ⟨10977993048060112052906837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7318662032040074701937891 10977993048060112052906837)
              ·
                refine ⟨64324178015977219060001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10977993048060112052906837 64324178015977219060001)
                ·
                  rfl

theorem cell23_3382314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 9].length) (baseStart_3382314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3382314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3382314 prefixEnd_3382314 := by exact prefixLift 3382314
  have htrace : WordTrace (prefixWord ++ tailWord_3382314) baseStart_3382314 baseEnd_3382314 := by
    simpa [prefixWord, tailWord_3382314, baseEnd_3382314] using wordTrace_append hprefix tailTrace_3382314
  have hstable : (prefixWord ++ tailWord_3382314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3382314).length < 2 ^ (prefixWord ++ tailWord_3382314).sum := by decide
  have hdescent : baseEnd_3382314 < baseStart_3382314 := by decide
  rcases family_descends (prefixWord ++ tailWord_3382314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3382342 : List Nat := [6, 1, 1, 1, 1, 4, 1, 1, 3, 2, 2]
def baseStart_3382342 : Nat := 118140960795 + 3382342 * 2 ^ 59
def prefixEnd_3382342 : Nat := 4983230072969 + 3 ^ 40 * 3382342 * 2
def baseEnd_3382342 : Nat := 1736767183889710805069899

theorem tailTrace_3382342 : CollatzResearch.WordTrace tailWord_3382342 prefixEnd_3382342 1736767183889710805069899 := by
  unfold tailWord_3382342
  simp only [CollatzResearch.WordTrace]
  refine ⟨3855129609761252089656415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 82242765008240044579336853 3855129609761252089656415)
  ·
    refine ⟨5782694414641878134484623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3855129609761252089656415 5782694414641878134484623)
    ·
      refine ⟨8674041621962817201726935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5782694414641878134484623 8674041621962817201726935)
      ·
        refine ⟨13011062432944225802590403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8674041621962817201726935 13011062432944225802590403)
        ·
          refine ⟨19516593649416338703885605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13011062432944225802590403 19516593649416338703885605)
          ·
            refine ⟨3659361309265563506978551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19516593649416338703885605 3659361309265563506978551)
            ·
              refine ⟨5489041963898345260467827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3659361309265563506978551 5489041963898345260467827)
              ·
                refine ⟨8233562945847517890701741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5489041963898345260467827 8233562945847517890701741)
                ·
                  refine ⟨3087586104692819209013153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8233562945847517890701741 3087586104692819209013153)
                  ·
                    refine ⟨2315689578519614406759865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3087586104692819209013153 2315689578519614406759865)
                    ·
                      refine ⟨1736767183889710805069899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2315689578519614406759865 1736767183889710805069899)
                      ·
                        rfl

theorem cell23_3382342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 1, 1, 3, 2, 2].length) (baseStart_3382342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3382342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3382342 prefixEnd_3382342 := by exact prefixLift 3382342
  have htrace : WordTrace (prefixWord ++ tailWord_3382342) baseStart_3382342 baseEnd_3382342 := by
    simpa [prefixWord, tailWord_3382342, baseEnd_3382342] using wordTrace_append hprefix tailTrace_3382342
  have hstable : (prefixWord ++ tailWord_3382342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3382342).length < 2 ^ (prefixWord ++ tailWord_3382342).sum := by decide
  have hdescent : baseEnd_3382342 < baseStart_3382342 := by decide
  rcases family_descends (prefixWord ++ tailWord_3382342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3382357 : List Nat := [1, 3, 2, 2, 1, 2, 2, 1, 1, 8]
def baseStart_3382357 : Nat := 118140960795 + 3382357 * 2 ^ 59
def prefixEnd_3382357 : Nat := 4983230072969 + 3 ^ 40 * 3382357 * 2
def baseEnd_3382357 : Nat := 578924962033176082127443

theorem tailTrace_3382357 : CollatzResearch.WordTrace tailWord_3382357 prefixEnd_3382357 578924962033176082127443 := by
  unfold tailWord_3382357
  simp only [CollatzResearch.WordTrace]
  refine ⟨123364694607305724430801325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82243129738203816287200883 123364694607305724430801325)
  ·
    refine ⟨46261760477739646661550497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123364694607305724430801325 46261760477739646661550497)
    ·
      refine ⟨34696320358304734996162873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46261760477739646661550497 34696320358304734996162873)
      ·
        refine ⟨26022240268728551247122155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34696320358304734996162873 26022240268728551247122155)
        ·
          refine ⟨39033360403092826870683233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26022240268728551247122155 39033360403092826870683233)
          ·
            refine ⟨29275020302319620153012425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39033360403092826870683233 29275020302319620153012425)
            ·
              refine ⟨21956265226739715114759319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29275020302319620153012425 21956265226739715114759319)
              ·
                refine ⟨32934397840109572672138979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21956265226739715114759319 32934397840109572672138979)
                ·
                  refine ⟨49401596760164359008208469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32934397840109572672138979 49401596760164359008208469)
                  ·
                    refine ⟨578924962033176082127443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 49401596760164359008208469 578924962033176082127443)
                    ·
                      rfl

theorem cell23_3382357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 1, 1, 8].length) (baseStart_3382357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3382357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3382357 prefixEnd_3382357 := by exact prefixLift 3382357
  have htrace : WordTrace (prefixWord ++ tailWord_3382357) baseStart_3382357 baseEnd_3382357 := by
    simpa [prefixWord, tailWord_3382357, baseEnd_3382357] using wordTrace_append hprefix tailTrace_3382357
  have hstable : (prefixWord ++ tailWord_3382357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3382357).length < 2 ^ (prefixWord ++ tailWord_3382357).sum := by decide
  have hdescent : baseEnd_3382357 < baseStart_3382357 := by decide
  rcases family_descends (prefixWord ++ tailWord_3382357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3382367 : List Nat := [1, 1, 2, 3, 1, 1, 3, 1, 4, 1, 5]
def baseStart_3382367 : Nat := 118140960795 + 3382367 * 2 ^ 59
def prefixEnd_3382367 : Nat := 4983230072969 + 3 ^ 40 * 3382367 * 2
def baseEnd_3382367 : Nat := 1736780020906073207257283

theorem tailTrace_3382367 : CollatzResearch.WordTrace tailWord_3382367 prefixEnd_3382367 1736780020906073207257283 := by
  unfold tailWord_3382367
  simp only [CollatzResearch.WordTrace]
  refine ⟨123365059337269496138665355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82243372891512997425776903 123365059337269496138665355)
  ·
    refine ⟨185047589005904244207998033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123365059337269496138665355 185047589005904244207998033)
    ·
      refine ⟨138785691754428183155998525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185047589005904244207998033 138785691754428183155998525)
      ·
        refine ⟨52044634407910568683499447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138785691754428183155998525 52044634407910568683499447)
        ·
          refine ⟨78066951611865853025249171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52044634407910568683499447 78066951611865853025249171)
          ·
            refine ⟨117100427417798779537873757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78066951611865853025249171 117100427417798779537873757)
            ·
              refine ⟨43912660281674542326702659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117100427417798779537873757 43912660281674542326702659)
              ·
                refine ⟨65868990422511813490053989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43912660281674542326702659 65868990422511813490053989)
                ·
                  refine ⟨12350435704220965029385123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65868990422511813490053989 12350435704220965029385123)
                  ·
                    refine ⟨18525653556331447544077685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12350435704220965029385123 18525653556331447544077685)
                    ·
                      refine ⟨1736780020906073207257283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18525653556331447544077685 1736780020906073207257283)
                      ·
                        rfl

theorem cell23_3382367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 4, 1, 5].length) (baseStart_3382367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3382367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3382367 prefixEnd_3382367 := by exact prefixLift 3382367
  have htrace : WordTrace (prefixWord ++ tailWord_3382367) baseStart_3382367 baseEnd_3382367 := by
    simpa [prefixWord, tailWord_3382367, baseEnd_3382367] using wordTrace_append hprefix tailTrace_3382367
  have hstable : (prefixWord ++ tailWord_3382367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3382367).length < 2 ^ (prefixWord ++ tailWord_3382367).sum := by decide
  have hdescent : baseEnd_3382367 < baseStart_3382367 := by decide
  rcases family_descends (prefixWord ++ tailWord_3382367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3382381 : List Nat := [1, 5, 1, 1, 2, 2, 1, 1, 3, 4, 2]
def baseStart_3382381 : Nat := 118140960795 + 3382381 * 2 ^ 59
def prefixEnd_3382381 : Nat := 4983230072969 + 3 ^ 40 * 3382381 * 2
def baseEnd_3382381 : Nat := 1736787209635236152482219

theorem tailTrace_3382381 : CollatzResearch.WordTrace tailWord_3382381 prefixEnd_3382381 1736787209635236152482219 := by
  unfold tailWord_3382381
  simp only [CollatzResearch.WordTrace]
  refine ⟨123365569959218776529674997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82243713306145851019783331 123365569959218776529674997)
  ·
    refine ⟨11565522183676760299657031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 123365569959218776529674997 11565522183676760299657031)
    ·
      refine ⟨17348283275515140449485547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11565522183676760299657031 17348283275515140449485547)
      ·
        refine ⟨26022424913272710674228321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17348283275515140449485547 26022424913272710674228321)
        ·
          refine ⟨19516818684954533005671241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26022424913272710674228321 19516818684954533005671241)
          ·
            refine ⟨14637614013715899754253431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19516818684954533005671241 14637614013715899754253431)
            ·
              refine ⟨21956421020573849631380147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14637614013715899754253431 21956421020573849631380147)
              ·
                refine ⟨32934631530860774447070221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21956421020573849631380147 32934631530860774447070221)
                ·
                  refine ⟨12350486824072790417651333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32934631530860774447070221 12350486824072790417651333)
                  ·
                    refine ⟨2315716279513648203309625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12350486824072790417651333 2315716279513648203309625)
                    ·
                      refine ⟨1736787209635236152482219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2315716279513648203309625 1736787209635236152482219)
                      ·
                        rfl

theorem cell23_3382381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 1, 3, 4, 2].length) (baseStart_3382381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3382381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3382381 prefixEnd_3382381 := by exact prefixLift 3382381
  have htrace : WordTrace (prefixWord ++ tailWord_3382381) baseStart_3382381 baseEnd_3382381 := by
    simpa [prefixWord, tailWord_3382381, baseEnd_3382381] using wordTrace_append hprefix tailTrace_3382381
  have hstable : (prefixWord ++ tailWord_3382381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3382381).length < 2 ^ (prefixWord ++ tailWord_3382381).sum := by decide
  have hdescent : baseEnd_3382381 < baseStart_3382381 := by decide
  rcases family_descends (prefixWord ++ tailWord_3382381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3382407 : List Nat := [1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 8]
def baseStart_3382407 : Nat := 118140960795 + 3382407 * 2 ^ 59
def prefixEnd_3382407 : Nat := 4983230072969 + 3 ^ 40 * 3382407 * 2
def baseEnd_3382407 : Nat := 1736800560132253050757099

theorem tailTrace_3382407 : CollatzResearch.WordTrace tailWord_3382407 prefixEnd_3382407 1736800560132253050757099 := by
  unfold tailWord_3382407
  simp only [CollatzResearch.WordTrace]
  refine ⟨123366518257124582970121475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82244345504749721980080983 123366518257124582970121475)
  ·
    refine ⟨185049777385686874455182213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123366518257124582970121475 185049777385686874455182213)
    ·
      refine ⟨34696833259816288960346665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 185049777385686874455182213 34696833259816288960346665)
      ·
        refine ⟨26022624944862216720259999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34696833259816288960346665 26022624944862216720259999)
        ·
          refine ⟨39033937417293325080389999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26022624944862216720259999 39033937417293325080389999)
          ·
            refine ⟨58550906125939987620584999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39033937417293325080389999 58550906125939987620584999)
            ·
              refine ⟨87826359188909981430877499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58550906125939987620584999 87826359188909981430877499)
              ·
                refine ⟨131739538783364972146316249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87826359188909981430877499 131739538783364972146316249)
                ·
                  refine ⟨98804654087523729109737187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 131739538783364972146316249 98804654087523729109737187)
                  ·
                    refine ⟨148206981131285593664605781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 98804654087523729109737187 148206981131285593664605781)
                    ·
                      refine ⟨1736800560132253050757099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 148206981131285593664605781 1736800560132253050757099)
                      ·
                        rfl

theorem cell23_3382407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 8].length) (baseStart_3382407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3382407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3382407 prefixEnd_3382407 := by exact prefixLift 3382407
  have htrace : WordTrace (prefixWord ++ tailWord_3382407) baseStart_3382407 baseEnd_3382407 := by
    simpa [prefixWord, tailWord_3382407, baseEnd_3382407] using wordTrace_append hprefix tailTrace_3382407
  have hstable : (prefixWord ++ tailWord_3382407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3382407).length < 2 ^ (prefixWord ++ tailWord_3382407).sum := by decide
  have hdescent : baseEnd_3382407 < baseStart_3382407 := by decide
  rcases family_descends (prefixWord ++ tailWord_3382407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3382427 : List Nat := [1, 1, 1, 1, 1, 1, 2, 3, 5, 2, 5]
def baseStart_3382427 : Nat := 118140960795 + 3382427 * 2 ^ 59
def prefixEnd_3382427 : Nat := 4983230072969 + 3 ^ 40 * 3382427 * 2
def baseEnd_3382427 : Nat := 1736810829745342972507007

theorem tailTrace_3382427 : CollatzResearch.WordTrace tailWord_3382427 prefixEnd_3382427 1736810829745342972507007 := by
  unfold tailWord_3382427
  simp only [CollatzResearch.WordTrace]
  refine ⟨123367247717052126385849535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82244831811368084257233023 123367247717052126385849535)
  ·
    refine ⟨185050871575578189578774303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123367247717052126385849535 185050871575578189578774303)
    ·
      refine ⟨277576307363367284368161455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185050871575578189578774303 277576307363367284368161455)
      ·
        refine ⟨416364461045050926552242183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277576307363367284368161455 416364461045050926552242183)
        ·
          refine ⟨624546691567576389828363275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 416364461045050926552242183 624546691567576389828363275)
          ·
            refine ⟨936820037351364584742544913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 624546691567576389828363275 936820037351364584742544913)
            ·
              refine ⟨702615028013523438556908685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 936820037351364584742544913 702615028013523438556908685)
              ·
                refine ⟨263480635505071289458840757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 702615028013523438556908685 263480635505071289458840757)
                ·
                  refine ⟨24701309578600433386766321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 263480635505071289458840757 24701309578600433386766321)
                  ·
                    refine ⟨18525982183950325040074741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24701309578600433386766321 18525982183950325040074741)
                    ·
                      refine ⟨1736810829745342972507007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18525982183950325040074741 1736810829745342972507007)
                      ·
                        rfl

theorem cell23_3382427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 5, 2, 5].length) (baseStart_3382427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3382427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3382427 prefixEnd_3382427 := by exact prefixLift 3382427
  have htrace : WordTrace (prefixWord ++ tailWord_3382427) baseStart_3382427 baseEnd_3382427 := by
    simpa [prefixWord, tailWord_3382427, baseEnd_3382427] using wordTrace_append hprefix tailTrace_3382427
  have hstable : (prefixWord ++ tailWord_3382427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3382427).length < 2 ^ (prefixWord ++ tailWord_3382427).sum := by decide
  have hdescent : baseEnd_3382427 < baseStart_3382427 := by decide
  rcases family_descends (prefixWord ++ tailWord_3382427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3382466 : List Nat := [3, 5, 1, 1, 2, 1, 3, 1, 2, 2, 2]
def baseStart_3382466 : Nat := 118140960795 + 3382466 * 2 ^ 59
def prefixEnd_3382466 : Nat := 4983230072969 + 3 ^ 40 * 3382466 * 2
def baseEnd_3382466 : Nat := 1736830855490868319919329

theorem tailTrace_3382466 : CollatzResearch.WordTrace tailWord_3382466 prefixEnd_3382466 1736830855490868319919329 := by
  unfold tailWord_3382466
  simp only [CollatzResearch.WordTrace]
  refine ⟨30842167540977709011629813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82245780109273890697679501 30842167540977709011629813)
  ·
    refine ⟨2891453206966660219840295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30842167540977709011629813 2891453206966660219840295)
    ·
      refine ⟨4337179810449990329760443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2891453206966660219840295 4337179810449990329760443)
      ·
        refine ⟨6505769715674985494640665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4337179810449990329760443 6505769715674985494640665)
        ·
          refine ⟨4879327286756239120980499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6505769715674985494640665 4879327286756239120980499)
          ·
            refine ⟨7318990930134358681470749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4879327286756239120980499 7318990930134358681470749)
            ·
              refine ⟨2744621598800384505551531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7318990930134358681470749 2744621598800384505551531)
              ·
                refine ⟨4116932398200576758327297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2744621598800384505551531 4116932398200576758327297)
                ·
                  refine ⟨3087699298650432568745473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4116932398200576758327297 3087699298650432568745473)
                  ·
                    refine ⟨2315774473987824426559105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3087699298650432568745473 2315774473987824426559105)
                    ·
                      refine ⟨1736830855490868319919329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2315774473987824426559105 1736830855490868319919329)
                      ·
                        rfl

theorem cell23_3382466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 3, 1, 2, 2, 2].length) (baseStart_3382466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3382466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3382466 prefixEnd_3382466 := by exact prefixLift 3382466
  have htrace : WordTrace (prefixWord ++ tailWord_3382466) baseStart_3382466 baseEnd_3382466 := by
    simpa [prefixWord, tailWord_3382466, baseEnd_3382466] using wordTrace_append hprefix tailTrace_3382466
  have hstable : (prefixWord ++ tailWord_3382466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3382466).length < 2 ^ (prefixWord ++ tailWord_3382466).sum := by decide
  have hdescent : baseEnd_3382466 < baseStart_3382466 := by decide
  rcases family_descends (prefixWord ++ tailWord_3382466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3382515 : List Nat := [1, 1, 1, 2, 2, 6, 3, 2, 1, 4]
def baseStart_3382515 : Nat := 118140960795 + 3382515 * 2 ^ 59
def prefixEnd_3382515 : Nat := 4983230072969 + 3 ^ 40 * 3382515 * 2
def baseEnd_3382515 : Nat := 578952005347646209402201

theorem tailTrace_3382515 : CollatzResearch.WordTrace tailWord_3382515 prefixEnd_3382515 578952005347646209402201 := by
  unfold tailWord_3382515
  simp only [CollatzResearch.WordTrace]
  refine ⟨123370457340733317415052999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82246971560488878276701999 123370457340733317415052999)
  ·
    refine ⟨185055686011099976122579499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123370457340733317415052999 185055686011099976122579499)
    ·
      refine ⟨277583529016649964183869249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185055686011099976122579499 277583529016649964183869249)
      ·
        refine ⟨208187646762487473137901937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 277583529016649964183869249 208187646762487473137901937)
        ·
          refine ⟨156140735071865604853426453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208187646762487473137901937 156140735071865604853426453)
          ·
            refine ⟨7319096956493700227504365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 156140735071865604853426453 7319096956493700227504365)
            ·
              refine ⟨2744661358685137585314137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7319096956493700227504365 2744661358685137585314137)
              ·
                refine ⟨2058496019013853188985603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2744661358685137585314137 2058496019013853188985603)
                ·
                  refine ⟨3087744028520779783478405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2058496019013853188985603 3087744028520779783478405)
                  ·
                    refine ⟨578952005347646209402201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3087744028520779783478405 578952005347646209402201)
                    ·
                      rfl

theorem cell23_3382515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 3, 2, 1, 4].length) (baseStart_3382515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3382515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3382515 prefixEnd_3382515 := by exact prefixLift 3382515
  have htrace : WordTrace (prefixWord ++ tailWord_3382515) baseStart_3382515 baseEnd_3382515 := by
    simpa [prefixWord, tailWord_3382515, baseEnd_3382515] using wordTrace_append hprefix tailTrace_3382515
  have hstable : (prefixWord ++ tailWord_3382515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3382515).length < 2 ^ (prefixWord ++ tailWord_3382515).sum := by decide
  have hdescent : baseEnd_3382515 < baseStart_3382515 := by decide
  rcases family_descends (prefixWord ++ tailWord_3382515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3382588 : List Nat := [2, 2, 2, 2, 1, 3, 2, 3, 2, 4]
def baseStart_3382588 : Nat := 118140960795 + 3382588 * 2 ^ 59
def prefixEnd_3382588 : Nat := 4983230072969 + 3 ^ 40 * 3382588 * 2
def baseEnd_3382588 : Nat := 578964500043572280864589

theorem tailTrace_3382588 : CollatzResearch.WordTrace tailWord_3382588 prefixEnd_3382588 578964500043572280864589 := by
  unfold tailWord_3382588
  simp only [CollatzResearch.WordTrace]
  refine ⟨61686559934734425441230209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82248746579645900588306945 61686559934734425441230209)
  ·
    refine ⟨46264919951050819080922657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61686559934734425441230209 46264919951050819080922657)
    ·
      refine ⟨34698689963288114310691993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46264919951050819080922657 34698689963288114310691993)
      ·
        refine ⟨26024017472466085733018995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34698689963288114310691993 26024017472466085733018995)
        ·
          refine ⟨39036026208699128599528493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26024017472466085733018995 39036026208699128599528493)
          ·
            refine ⟨14638509828262173224823185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39036026208699128599528493 14638509828262173224823185)
            ·
              refine ⟨10978882371196629918617389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14638509828262173224823185 10978882371196629918617389)
              ·
                refine ⟨4117080889198736219481521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10978882371196629918617389 4117080889198736219481521)
                ·
                  refine ⟨3087810666899052164611141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4117080889198736219481521 3087810666899052164611141)
                  ·
                    refine ⟨578964500043572280864589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3087810666899052164611141 578964500043572280864589)
                    ·
                      rfl

theorem cell23_3382588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 3, 2, 4].length) (baseStart_3382588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3382588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3382588 prefixEnd_3382588 := by exact prefixLift 3382588
  have htrace : WordTrace (prefixWord ++ tailWord_3382588) baseStart_3382588 baseEnd_3382588 := by
    simpa [prefixWord, tailWord_3382588, baseEnd_3382588] using wordTrace_append hprefix tailTrace_3382588
  have hstable : (prefixWord ++ tailWord_3382588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3382588).length < 2 ^ (prefixWord ++ tailWord_3382588).sum := by decide
  have hdescent : baseEnd_3382588 < baseStart_3382588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3382588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3382591 : List Nat := [1, 1, 2, 2, 4, 2, 1, 3, 1, 2, 4]
def baseStart_3382591 : Nat := 118140960795 + 3382591 * 2 ^ 59
def prefixEnd_3382591 : Nat := 4983230072969 + 3 ^ 40 * 3382591 * 2
def baseEnd_3382591 : Nat := 1736895040572680330856253

theorem tailTrace_3382591 : CollatzResearch.WordTrace tailWord_3382591 prefixEnd_3382591 1736895040572680330856253 := by
  unfold tailWord_3382591
  simp only [CollatzResearch.WordTrace]
  refine ⟨123373229288457982394819627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82248819525638654929879751 123373229288457982394819627)
  ·
    refine ⟨185059843932686973592229441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123373229288457982394819627 185059843932686973592229441)
    ·
      refine ⟨138794882949515230194172081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185059843932686973592229441 138794882949515230194172081)
      ·
        refine ⟨104096162212136422645629061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138794882949515230194172081 104096162212136422645629061)
        ·
          refine ⟨19518030414775579246055449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104096162212136422645629061 19518030414775579246055449)
          ·
            refine ⟨14638522811081684434541587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19518030414775579246055449 14638522811081684434541587)
            ·
              refine ⟨21957784216622526651812381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14638522811081684434541587 21957784216622526651812381)
              ·
                refine ⟨8234169081233447494429643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21957784216622526651812381 8234169081233447494429643)
                ·
                  refine ⟨12351253621850171241644465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8234169081233447494429643 12351253621850171241644465)
                  ·
                    refine ⟨9263440216387628431233349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12351253621850171241644465 9263440216387628431233349)
                    ·
                      refine ⟨1736895040572680330856253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9263440216387628431233349 1736895040572680330856253)
                      ·
                        rfl

theorem cell23_3382591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 3, 1, 2, 4].length) (baseStart_3382591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3382591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3382591 prefixEnd_3382591 := by exact prefixLift 3382591
  have htrace : WordTrace (prefixWord ++ tailWord_3382591) baseStart_3382591 baseEnd_3382591 := by
    simpa [prefixWord, tailWord_3382591, baseEnd_3382591] using wordTrace_append hprefix tailTrace_3382591
  have hstable : (prefixWord ++ tailWord_3382591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3382591).length < 2 ^ (prefixWord ++ tailWord_3382591).sum := by decide
  have hdescent : baseEnd_3382591 < baseStart_3382591 := by decide
  rcases family_descends (prefixWord ++ tailWord_3382591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3382611 : List Nat := [1, 1, 1, 2, 1, 1, 5, 4, 1, 3, 3]
def baseStart_3382611 : Nat := 118140960795 + 3382611 * 2 ^ 59
def prefixEnd_3382611 : Nat := 4983230072969 + 3 ^ 40 * 3382611 * 2
def baseEnd_3382611 : Nat := 1736905310185770252606161

theorem tailTrace_3382611 : CollatzResearch.WordTrace tailWord_3382611 prefixEnd_3382611 1736905310185770252606161 := by
  unfold tailWord_3382611
  simp only [CollatzResearch.WordTrace]
  refine ⟨123373958748385525810547687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82249305832257017207031791 123373958748385525810547687)
  ·
    refine ⟨185060938122578288715821531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123373958748385525810547687 185060938122578288715821531)
    ·
      refine ⟨277591407183867433073732297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185060938122578288715821531 277591407183867433073732297)
      ·
        refine ⟨208193555387900574805299223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 277591407183867433073732297 208193555387900574805299223)
        ·
          refine ⟨312290333081850862207948835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208193555387900574805299223 312290333081850862207948835)
          ·
            refine ⟨468435499622776293311923253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 312290333081850862207948835 468435499622776293311923253)
            ·
              refine ⟨43915828089635277497992805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 468435499622776293311923253 43915828089635277497992805)
              ·
                refine ⟨8234217766806614530873651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43915828089635277497992805 8234217766806614530873651)
                ·
                  refine ⟨12351326650209921796310477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8234217766806614530873651 12351326650209921796310477)
                  ·
                    refine ⟨4631747493828720673616429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12351326650209921796310477 4631747493828720673616429)
                    ·
                      refine ⟨1736905310185770252606161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4631747493828720673616429 1736905310185770252606161)
                      ·
                        rfl

theorem cell23_3382611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 4, 1, 3, 3].length) (baseStart_3382611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3382611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3382611 prefixEnd_3382611 := by exact prefixLift 3382611
  have htrace : WordTrace (prefixWord ++ tailWord_3382611) baseStart_3382611 baseEnd_3382611 := by
    simpa [prefixWord, tailWord_3382611, baseEnd_3382611] using wordTrace_append hprefix tailTrace_3382611
  have hstable : (prefixWord ++ tailWord_3382611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3382611).length < 2 ^ (prefixWord ++ tailWord_3382611).sum := by decide
  have hdescent : baseEnd_3382611 < baseStart_3382611 := by decide
  rcases family_descends (prefixWord ++ tailWord_3382611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3382615 : List Nat := [1, 1, 3, 2, 3, 2, 4, 1, 1, 2, 3]
def baseStart_3382615 : Nat := 118140960795 + 3382615 * 2 ^ 59
def prefixEnd_3382615 : Nat := 4983230072969 + 3 ^ 40 * 3382615 * 2
def baseEnd_3382615 : Nat := 1736907364108388236956143

theorem tailTrace_3382615 : CollatzResearch.WordTrace tailWord_3382615 prefixEnd_3382615 1736907364108388236956143 := by
  unfold tailWord_3382615
  simp only [CollatzResearch.WordTrace]
  refine ⟨123374104640371034493693299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82249403093580689662462199 123374104640371034493693299)
  ·
    refine ⟨185061156960556551740539949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123374104640371034493693299 185061156960556551740539949)
    ·
      refine ⟨69397933860208706902702481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185061156960556551740539949 69397933860208706902702481)
      ·
        refine ⟨52048450395156530177026861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69397933860208706902702481 52048450395156530177026861)
        ·
          refine ⟨19518168898183698816385073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52048450395156530177026861 19518168898183698816385073)
          ·
            refine ⟨14638626673637774112288805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19518168898183698816385073 14638626673637774112288805)
            ·
              refine ⟨2744742501307082646054151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14638626673637774112288805 2744742501307082646054151)
              ·
                refine ⟨4117113751960623969081227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2744742501307082646054151 4117113751960623969081227)
                ·
                  refine ⟨6175670627940935953621841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4117113751960623969081227 6175670627940935953621841)
                  ·
                    refine ⟨4631752970955701965216381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6175670627940935953621841 4631752970955701965216381)
                    ·
                      refine ⟨1736907364108388236956143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4631752970955701965216381 1736907364108388236956143)
                      ·
                        rfl

theorem cell23_3382615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 4, 1, 1, 2, 3].length) (baseStart_3382615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3382615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3382615 prefixEnd_3382615 := by exact prefixLift 3382615
  have htrace : WordTrace (prefixWord ++ tailWord_3382615) baseStart_3382615 baseEnd_3382615 := by
    simpa [prefixWord, tailWord_3382615, baseEnd_3382615] using wordTrace_append hprefix tailTrace_3382615
  have hstable : (prefixWord ++ tailWord_3382615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3382615).length < 2 ^ (prefixWord ++ tailWord_3382615).sum := by decide
  have hdescent : baseEnd_3382615 < baseStart_3382615 := by decide
  rcases family_descends (prefixWord ++ tailWord_3382615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3382668 : List Nat := [2, 2, 1, 2, 1, 3, 2, 1, 3, 4, 2]
def baseStart_3382668 : Nat := 118140960795 + 3382668 * 2 ^ 59
def prefixEnd_3382668 : Nat := 4983230072969 + 3 ^ 40 * 3382668 * 2
def baseEnd_3382668 : Nat := 1736934578583076529593399

theorem tailTrace_3382668 : CollatzResearch.WordTrace tailWord_3382668 prefixEnd_3382668 1736934578583076529593399 := by
  unfold tailWord_3382668
  simp only [CollatzResearch.WordTrace]
  refine ⟨61688018854589512272686329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82250691806119349696915105 61688018854589512272686329)
  ·
    refine ⟨46266014140942134204514747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61688018854589512272686329 46266014140942134204514747)
    ·
      refine ⟨69399021211413201306772121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46266014140942134204514747 69399021211413201306772121)
      ·
        refine ⟨52049265908559900980079091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69399021211413201306772121 52049265908559900980079091)
        ·
          refine ⟨78073898862839851470118637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52049265908559900980079091 78073898862839851470118637)
          ·
            refine ⟨29277712073564944301294489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78073898862839851470118637 29277712073564944301294489)
            ·
              refine ⟨21958284055173708225970867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29277712073564944301294489 21958284055173708225970867)
              ·
                refine ⟨32937426082760562338956301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21958284055173708225970867 32937426082760562338956301)
                ·
                  refine ⟨12351534781035210877108613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32937426082760562338956301 12351534781035210877108613)
                  ·
                    refine ⟨2315912771444102039457865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12351534781035210877108613 2315912771444102039457865)
                    ·
                      refine ⟨1736934578583076529593399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2315912771444102039457865 1736934578583076529593399)
                      ·
                        rfl

theorem cell23_3382668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 1, 3, 4, 2].length) (baseStart_3382668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3382668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3382668 prefixEnd_3382668 := by exact prefixLift 3382668
  have htrace : WordTrace (prefixWord ++ tailWord_3382668) baseStart_3382668 baseEnd_3382668 := by
    simpa [prefixWord, tailWord_3382668, baseEnd_3382668] using wordTrace_append hprefix tailTrace_3382668
  have hstable : (prefixWord ++ tailWord_3382668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3382668).length < 2 ^ (prefixWord ++ tailWord_3382668).sum := by decide
  have hdescent : baseEnd_3382668 < baseStart_3382668 := by decide
  rcases family_descends (prefixWord ++ tailWord_3382668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3382696 : List Nat := [2, 1, 6, 1, 2, 2, 2, 1, 2, 1, 3]
def baseStart_3382696 : Nat := 118140960795 + 3382696 * 2 ^ 59
def prefixEnd_3382696 : Nat := 4983230072969 + 3 ^ 40 * 3382696 * 2
def baseEnd_3382696 : Nat := 1736948956041402420043271

theorem tailTrace_3382696 : CollatzResearch.WordTrace tailWord_3382696 prefixEnd_3382696 1736948956041402420043271 := by
  unfold tailWord_3382696
  simp only [CollatzResearch.WordTrace]
  refine ⟨61688529476538792663695971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82251372635385056884927961 61688529476538792663695971)
  ·
    refine ⟨92532794214808188995543957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61688529476538792663695971 92532794214808188995543957)
    ·
      refine ⟨4337474728819133859166123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 92532794214808188995543957 4337474728819133859166123)
      ·
        refine ⟨6506212093228700788749185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4337474728819133859166123 6506212093228700788749185)
        ·
          refine ⟨4879659069921525591561889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6506212093228700788749185 4879659069921525591561889)
          ·
            refine ⟨3659744302441144193671417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4879659069921525591561889 3659744302441144193671417)
            ·
              refine ⟨2744808226830858145253563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3659744302441144193671417 2744808226830858145253563)
              ·
                refine ⟨4117212340246287217880345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2744808226830858145253563 4117212340246287217880345)
                ·
                  refine ⟨3087909255184715413410259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4117212340246287217880345 3087909255184715413410259)
                  ·
                    refine ⟨4631863882777073120115389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3087909255184715413410259 4631863882777073120115389)
                    ·
                      refine ⟨1736948956041402420043271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4631863882777073120115389 1736948956041402420043271)
                      ·
                        rfl

theorem cell23_3382696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 2, 1, 2, 1, 3].length) (baseStart_3382696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3382696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3382696 prefixEnd_3382696 := by exact prefixLift 3382696
  have htrace : WordTrace (prefixWord ++ tailWord_3382696) baseStart_3382696 baseEnd_3382696 := by
    simpa [prefixWord, tailWord_3382696, baseEnd_3382696] using wordTrace_append hprefix tailTrace_3382696
  have hstable : (prefixWord ++ tailWord_3382696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3382696).length < 2 ^ (prefixWord ++ tailWord_3382696).sum := by decide
  have hdescent : baseEnd_3382696 < baseStart_3382696 := by decide
  rcases family_descends (prefixWord ++ tailWord_3382696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3382718 : List Nat := [4, 2, 1, 1, 1, 1, 1, 2, 4, 3, 3]
def baseStart_3382718 : Nat := 118140960795 + 3382718 * 2 ^ 59
def prefixEnd_3382718 : Nat := 4983230072969 + 3 ^ 40 * 3382718 * 2
def baseEnd_3382718 : Nat := 1736960252615801333968169

theorem tailTrace_3382718 : CollatzResearch.WordTrace tailWord_3382718 prefixEnd_3382718 1736960252615801333968169 := by
  unfold tailWord_3382718
  simp only [CollatzResearch.WordTrace]
  refine ⟨15422232669874735385586601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82251907572665255389795205 15422232669874735385586601)
  ·
    refine ⟨11566674502406051539189951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15422232669874735385586601 11566674502406051539189951)
    ·
      refine ⟨17350011753609077308784927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11566674502406051539189951 17350011753609077308784927)
      ·
        refine ⟨26025017630413615963177391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17350011753609077308784927 26025017630413615963177391)
        ·
          refine ⟨39037526445620423944766087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26025017630413615963177391 39037526445620423944766087)
          ·
            refine ⟨58556289668430635917149131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39037526445620423944766087 58556289668430635917149131)
            ·
              refine ⟨87834434502645953875723697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58556289668430635917149131 87834434502645953875723697)
              ·
                refine ⟨65875825876984465406792773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87834434502645953875723697 65875825876984465406792773)
                ·
                  refine ⟨12351717351934587263773645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65875825876984465406792773 12351717351934587263773645)
                  ·
                    refine ⟨4631894006975470223915117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12351717351934587263773645 4631894006975470223915117)
                    ·
                      refine ⟨1736960252615801333968169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4631894006975470223915117 1736960252615801333968169)
                      ·
                        rfl

theorem cell23_3382718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 4, 3, 3].length) (baseStart_3382718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3382718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3382718 prefixEnd_3382718 := by exact prefixLift 3382718
  have htrace : WordTrace (prefixWord ++ tailWord_3382718) baseStart_3382718 baseEnd_3382718 := by
    simpa [prefixWord, tailWord_3382718, baseEnd_3382718] using wordTrace_append hprefix tailTrace_3382718
  have hstable : (prefixWord ++ tailWord_3382718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3382718).length < 2 ^ (prefixWord ++ tailWord_3382718).sum := by decide
  have hdescent : baseEnd_3382718 < baseStart_3382718 := by decide
  rcases family_descends (prefixWord ++ tailWord_3382718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3382731 : List Nat := [1, 1, 1, 1, 3, 3, 3, 2, 1, 2, 5]
def baseStart_3382731 : Nat := 118140960795 + 3382731 * 2 ^ 59
def prefixEnd_3382731 : Nat := 4983230072969 + 3 ^ 40 * 3382731 * 2
def baseEnd_3382731 : Nat := 1736966927864309783105609

theorem tailTrace_3382731 : CollatzResearch.WordTrace tailWord_3382731 prefixEnd_3382731 1736966927864309783105609 := by
  unfold tailWord_3382731
  simp only [CollatzResearch.WordTrace]
  refine ⟨123378335507950786304916047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82252223671967190869944031 123378335507950786304916047)
  ·
    refine ⟨185067503261926179457374071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123378335507950786304916047 185067503261926179457374071)
    ·
      refine ⟨277601254892889269186061107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185067503261926179457374071 277601254892889269186061107)
      ·
        refine ⟨416401882339333903779091661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277601254892889269186061107 416401882339333903779091661)
        ·
          refine ⟨156150705877250213917159373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 416401882339333903779091661 156150705877250213917159373)
          ·
            refine ⟨58556514703968830218934765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 156150705877250213917159373 58556514703968830218934765)
            ·
              refine ⟨21958693013988311332100537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58556514703968830218934765 21958693013988311332100537)
              ·
                refine ⟨16469019760491233499075403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21958693013988311332100537 16469019760491233499075403)
                ·
                  refine ⟨24703529640736850248613105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16469019760491233499075403 24703529640736850248613105)
                  ·
                    refine ⟨18527647230552637686459829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24703529640736850248613105 18527647230552637686459829)
                    ·
                      refine ⟨1736966927864309783105609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18527647230552637686459829 1736966927864309783105609)
                      ·
                        rfl

theorem cell23_3382731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 2, 1, 2, 5].length) (baseStart_3382731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3382731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3382731 prefixEnd_3382731 := by exact prefixLift 3382731
  have htrace : WordTrace (prefixWord ++ tailWord_3382731) baseStart_3382731 baseEnd_3382731 := by
    simpa [prefixWord, tailWord_3382731, baseEnd_3382731] using wordTrace_append hprefix tailTrace_3382731
  have hstable : (prefixWord ++ tailWord_3382731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3382731).length < 2 ^ (prefixWord ++ tailWord_3382731).sum := by decide
  have hdescent : baseEnd_3382731 < baseStart_3382731 := by decide
  rcases family_descends (prefixWord ++ tailWord_3382731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3382742 : List Nat := [5, 2, 1, 1, 1, 3, 1, 4, 5]
def baseStart_3382742 : Nat := 118140960795 + 3382742 * 2 ^ 59
def prefixEnd_3382742 : Nat := 4983230072969 + 3 ^ 40 * 3382742 * 2
def baseEnd_3382742 : Nat := 192996952905723248896451

theorem tailTrace_3382742 : CollatzResearch.WordTrace tailWord_3382742 prefixEnd_3382742 192996952905723248896451 := by
  unfold tailWord_3382742
  simp only [CollatzResearch.WordTrace]
  refine ⟨7711171044431933448972905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 82252491140607290122377653 7711171044431933448972905)
  ·
    refine ⟨5783378283323950086729679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7711171044431933448972905 5783378283323950086729679)
    ·
      refine ⟨8675067424985925130094519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5783378283323950086729679 8675067424985925130094519)
      ·
        refine ⟨13012601137478887695141779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8675067424985925130094519 13012601137478887695141779)
        ·
          refine ⟨19518901706218331542712669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13012601137478887695141779 19518901706218331542712669)
          ·
            refine ⟨7319588139831874328517251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19518901706218331542712669 7319588139831874328517251)
            ·
              refine ⟨10979382209747811492775877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7319588139831874328517251 10979382209747811492775877)
              ·
                refine ⟨2058634164327714654895477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10979382209747811492775877 2058634164327714654895477)
                ·
                  refine ⟨192996952905723248896451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2058634164327714654895477 192996952905723248896451)
                  ·
                    rfl

theorem cell23_3382742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 4, 5].length) (baseStart_3382742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3382742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3382742 prefixEnd_3382742 := by exact prefixLift 3382742
  have htrace : WordTrace (prefixWord ++ tailWord_3382742) baseStart_3382742 baseEnd_3382742 := by
    simpa [prefixWord, tailWord_3382742, baseEnd_3382742] using wordTrace_append hprefix tailTrace_3382742
  have hstable : (prefixWord ++ tailWord_3382742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3382742).length < 2 ^ (prefixWord ++ tailWord_3382742).sum := by decide
  have hdescent : baseEnd_3382742 < baseStart_3382742 := by decide
  rcases family_descends (prefixWord ++ tailWord_3382742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3382768 : List Nat := [2, 1, 1, 1, 3, 4, 1, 1, 5, 4]
def baseStart_3382768 : Nat := 118140960795 + 3382768 * 2 ^ 59
def prefixEnd_3382768 : Nat := 4983230072969 + 3 ^ 40 * 3382768 * 2
def baseEnd_3382768 : Nat := 578995308882842046114313

theorem tailTrace_3382768 : CollatzResearch.WordTrace tailWord_3382768 prefixEnd_3382768 578995308882842046114313 := by
  unfold tailWord_3382768
  simp only [CollatzResearch.WordTrace]
  refine ⟨61689842504408370812006479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82253123339211161082675305 61689842504408370812006479)
  ·
    refine ⟨92534763756612556218009719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61689842504408370812006479 92534763756612556218009719)
    ·
      refine ⟨138802145634918834327014579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92534763756612556218009719 138802145634918834327014579)
      ·
        refine ⟨208203218452378251490521869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138802145634918834327014579 208203218452378251490521869)
        ·
          refine ⟨78076206919641844308945701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 208203218452378251490521869 78076206919641844308945701)
          ·
            refine ⟨14639288797432845807927319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78076206919641844308945701 14639288797432845807927319)
            ·
              refine ⟨21958933196149268711890979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14639288797432845807927319 21958933196149268711890979)
              ·
                refine ⟨32938399794223903067836469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21958933196149268711890979 32938399794223903067836469)
                ·
                  refine ⟨3087974980708490912609669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32938399794223903067836469 3087974980708490912609669)
                  ·
                    refine ⟨578995308882842046114313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3087974980708490912609669 578995308882842046114313)
                    ·
                      rfl

theorem cell23_3382768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 1, 5, 4].length) (baseStart_3382768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3382768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3382768 prefixEnd_3382768 := by exact prefixLift 3382768
  have htrace : WordTrace (prefixWord ++ tailWord_3382768) baseStart_3382768 baseEnd_3382768 := by
    simpa [prefixWord, tailWord_3382768, baseEnd_3382768] using wordTrace_append hprefix tailTrace_3382768
  have hstable : (prefixWord ++ tailWord_3382768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3382768).length < 2 ^ (prefixWord ++ tailWord_3382768).sum := by decide
  have hdescent : baseEnd_3382768 < baseStart_3382768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3382768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3382771 : List Nat := [1, 1, 1, 2, 2, 2, 2, 1, 1, 6, 4]
def baseStart_3382771 : Nat := 118140960795 + 3382771 * 2 ^ 59
def prefixEnd_3382771 : Nat := 4983230072969 + 3 ^ 40 * 3382771 * 2
def baseEnd_3382771 : Nat := 1736987467090489626605425

theorem tailTrace_3382771 : CollatzResearch.WordTrace tailWord_3382771 prefixEnd_3382771 1736987467090489626605425 := by
  unfold tailWord_3382771
  simp only [CollatzResearch.WordTrace]
  refine ⟨123379794427805873136372167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82253196285203915424248111 123379794427805873136372167)
  ·
    refine ⟨185069691641708809704558251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123379794427805873136372167 185069691641708809704558251)
    ·
      refine ⟨277604537462563214556837377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185069691641708809704558251 277604537462563214556837377)
      ·
        refine ⟨208203403096922410917628033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 277604537462563214556837377 208203403096922410917628033)
        ·
          refine ⟨156152552322691808188221025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208203403096922410917628033 156152552322691808188221025)
          ·
            refine ⟨117114414242018856141165769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156152552322691808188221025 117114414242018856141165769)
            ·
              refine ⟨87835810681514142105874327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117114414242018856141165769 87835810681514142105874327)
              ·
                refine ⟨131753716022271213158811491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87835810681514142105874327 131753716022271213158811491)
                ·
                  refine ⟨197630574033406819738217237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 131753716022271213158811491 197630574033406819738217237)
                  ·
                    refine ⟨9263933157815944675228933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 197630574033406819738217237 9263933157815944675228933)
                    ·
                      refine ⟨1736987467090489626605425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9263933157815944675228933 1736987467090489626605425)
                      ·
                        rfl

theorem cell23_3382771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 6, 4].length) (baseStart_3382771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3382771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3382771 prefixEnd_3382771 := by exact prefixLift 3382771
  have htrace : WordTrace (prefixWord ++ tailWord_3382771) baseStart_3382771 baseEnd_3382771 := by
    simpa [prefixWord, tailWord_3382771, baseEnd_3382771] using wordTrace_append hprefix tailTrace_3382771
  have hstable : (prefixWord ++ tailWord_3382771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3382771).length < 2 ^ (prefixWord ++ tailWord_3382771).sum := by decide
  have hdescent : baseEnd_3382771 < baseStart_3382771 := by decide
  rcases family_descends (prefixWord ++ tailWord_3382771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3382778 : List Nat := [3, 1, 1, 1, 1, 2, 5, 1, 1, 4, 3]
def baseStart_3382778 : Nat := 118140960795 + 3382778 * 2 ^ 59
def prefixEnd_3382778 : Nat := 4983230072969 + 3 ^ 40 * 3382778 * 2
def baseEnd_3382778 : Nat := 1736991061455071099217893

theorem tailTrace_3382778 : CollatzResearch.WordTrace tailWord_3382778 prefixEnd_3382778 1736991061455071099217893 := by
  unfold tailWord_3382778
  simp only [CollatzResearch.WordTrace]
  refine ⟨30845012434695128332969247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82253366492520342221251325 30845012434695128332969247)
  ·
    refine ⟨46267518652042692499453871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30845012434695128332969247 46267518652042692499453871)
    ·
      refine ⟨69401277978064038749180807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46267518652042692499453871 69401277978064038749180807)
      ·
        refine ⟨104101916967096058123771211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69401277978064038749180807 104101916967096058123771211)
        ·
          refine ⟨156152875450644087185656817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104101916967096058123771211 156152875450644087185656817)
          ·
            refine ⟨117114656587983065389242613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156152875450644087185656817 117114656587983065389242613)
            ·
              refine ⟨10979499055123412380241495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 117114656587983065389242613 10979499055123412380241495)
              ·
                refine ⟨16469248582685118570362243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10979499055123412380241495 16469248582685118570362243)
                ·
                  refine ⟨24703872874027677855543365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16469248582685118570362243 24703872874027677855543365)
                  ·
                    refine ⟨4631976163880189597914381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24703872874027677855543365 4631976163880189597914381)
                    ·
                      refine ⟨1736991061455071099217893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4631976163880189597914381 1736991061455071099217893)
                      ·
                        rfl

theorem cell23_3382778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 1, 1, 4, 3].length) (baseStart_3382778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3382778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3382778 prefixEnd_3382778 := by exact prefixLift 3382778
  have htrace : WordTrace (prefixWord ++ tailWord_3382778) baseStart_3382778 baseEnd_3382778 := by
    simpa [prefixWord, tailWord_3382778, baseEnd_3382778] using wordTrace_append hprefix tailTrace_3382778
  have hstable : (prefixWord ++ tailWord_3382778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3382778).length < 2 ^ (prefixWord ++ tailWord_3382778).sum := by decide
  have hdescent : baseEnd_3382778 < baseStart_3382778 := by decide
  rcases family_descends (prefixWord ++ tailWord_3382778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3382801 : List Nat := [1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 8]
def baseStart_3382801 : Nat := 118140960795 + 3382801 * 2 ^ 59
def prefixEnd_3382801 : Nat := 4983230072969 + 3 ^ 40 * 3382801 * 2
def baseEnd_3382801 : Nat := 1737002871510124509230287

theorem tailTrace_3382801 : CollatzResearch.WordTrace tailWord_3382801 prefixEnd_3382801 1737002871510124509230287 := by
  unfold tailWord_3382801
  simp only [CollatzResearch.WordTrace]
  refine ⟨123380888617697188259964257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82253925745131458839976171 123380888617697188259964257)
  ·
    refine ⟨92535666463272891194973193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123380888617697188259964257 92535666463272891194973193)
    ·
      refine ⟨69401749847454668396229895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92535666463272891194973193 69401749847454668396229895)
      ·
        refine ⟨104102624771182002594344843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69401749847454668396229895 104102624771182002594344843)
        ·
          refine ⟨156153937156773003891517265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104102624771182002594344843 156153937156773003891517265)
          ·
            refine ⟨117115452867579752918637949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156153937156773003891517265 117115452867579752918637949)
            ·
              refine ⟨43918294825342407344489231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117115452867579752918637949 43918294825342407344489231)
              ·
                refine ⟨65877442238013611016733847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43918294825342407344489231 65877442238013611016733847)
                ·
                  refine ⟨98816163357020416525100771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65877442238013611016733847 98816163357020416525100771)
                  ·
                    refine ⟨148224245035530624787651157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 98816163357020416525100771 148224245035530624787651157)
                    ·
                      refine ⟨1737002871510124509230287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 148224245035530624787651157 1737002871510124509230287)
                      ·
                        rfl

theorem cell23_3382801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 8].length) (baseStart_3382801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3382801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3382801 prefixEnd_3382801 := by exact prefixLift 3382801
  have htrace : WordTrace (prefixWord ++ tailWord_3382801) baseStart_3382801 baseEnd_3382801 := by
    simpa [prefixWord, tailWord_3382801, baseEnd_3382801] using wordTrace_append hprefix tailTrace_3382801
  have hstable : (prefixWord ++ tailWord_3382801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3382801).length < 2 ^ (prefixWord ++ tailWord_3382801).sum := by decide
  have hdescent : baseEnd_3382801 < baseStart_3382801 := by decide
  rcases family_descends (prefixWord ++ tailWord_3382801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3382835 : List Nat := [1, 1, 1, 2, 4, 3, 2, 1, 1, 5, 2]
def baseStart_3382835 : Nat := 118140960795 + 3382835 * 2 ^ 59
def prefixEnd_3382835 : Nat := 4983230072969 + 3 ^ 40 * 3382835 * 2
def baseEnd_3382835 : Nat := 1737020329852377376205131

theorem tailTrace_3382835 : CollatzResearch.WordTrace tailWord_3382835 prefixEnd_3382835 1737020329852377376205131 := by
  unfold tailWord_3382835
  simp only [CollatzResearch.WordTrace]
  refine ⟨123382128699574012066701959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82254752466382674711134639 123382128699574012066701959)
  ·
    refine ⟨185073193049361018100052939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123382128699574012066701959 185073193049361018100052939)
    ·
      refine ⟨277609789574041527150079409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185073193049361018100052939 277609789574041527150079409)
      ·
        refine ⟨208207342180531145362559557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 277609789574041527150079409 208207342180531145362559557)
        ·
          refine ⟨39038876658849589755479917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 208207342180531145362559557 39038876658849589755479917)
          ·
            refine ⟨14639578747068596158304969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39038876658849589755479917 14639578747068596158304969)
            ·
              refine ⟨10979684060301447118728727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14639578747068596158304969 10979684060301447118728727)
              ·
                refine ⟨16469526090452170678093091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10979684060301447118728727 16469526090452170678093091)
                ·
                  refine ⟨24704289135678256017139637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16469526090452170678093091 24704289135678256017139637)
                  ·
                    refine ⟨2316027106469836501606841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24704289135678256017139637 2316027106469836501606841)
                    ·
                      refine ⟨1737020329852377376205131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2316027106469836501606841 1737020329852377376205131)
                      ·
                        rfl

theorem cell23_3382835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 1, 1, 5, 2].length) (baseStart_3382835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3382835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3382835 prefixEnd_3382835 := by exact prefixLift 3382835
  have htrace : WordTrace (prefixWord ++ tailWord_3382835) baseStart_3382835 baseEnd_3382835 := by
    simpa [prefixWord, tailWord_3382835, baseEnd_3382835] using wordTrace_append hprefix tailTrace_3382835
  have hstable : (prefixWord ++ tailWord_3382835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3382835).length < 2 ^ (prefixWord ++ tailWord_3382835).sum := by decide
  have hdescent : baseEnd_3382835 < baseStart_3382835 := by decide
  rcases family_descends (prefixWord ++ tailWord_3382835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3382848 : List Nat := [2, 1, 1, 2, 2, 2, 1, 2, 5, 1, 4]
def baseStart_3382848 : Nat := 118140960795 + 3382848 * 2 ^ 59
def prefixEnd_3382848 : Nat := 4983230072969 + 3 ^ 40 * 3382848 * 2
def baseEnd_3382848 : Nat := 1737027005100885825342571

theorem tailTrace_3382848 : CollatzResearch.WordTrace tailWord_3382848 prefixEnd_3382848 1737027005100885825342571 := by
  unfold tailWord_3382848
  simp only [CollatzResearch.WordTrace]
  refine ⟨61691301424263457643462599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82255068565684610191283465 61691301424263457643462599)
  ·
    refine ⟨92536952136395186465193899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61691301424263457643462599 92536952136395186465193899)
    ·
      refine ⟨138805428204592779697790849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92536952136395186465193899 138805428204592779697790849)
      ·
        refine ⟨104104071153444584773343137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138805428204592779697790849 104104071153444584773343137)
        ·
          refine ⟨78078053365083438580007353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104104071153444584773343137 78078053365083438580007353)
          ·
            refine ⟨58558540023812578935005515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78078053365083438580007353 58558540023812578935005515)
            ·
              refine ⟨87837810035718868402508273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58558540023812578935005515 87837810035718868402508273)
              ·
                refine ⟨65878357526789151301881205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87837810035718868402508273 65878357526789151301881205)
                ·
                  refine ⟨6176096018136482934551363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65878357526789151301881205 6176096018136482934551363)
                  ·
                    refine ⟨9264144027204724401827045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6176096018136482934551363 9264144027204724401827045)
                    ·
                      refine ⟨1737027005100885825342571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9264144027204724401827045 1737027005100885825342571)
                      ·
                        rfl

theorem cell23_3382848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 5, 1, 4].length) (baseStart_3382848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3382848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3382848 prefixEnd_3382848 := by exact prefixLift 3382848
  have htrace : WordTrace (prefixWord ++ tailWord_3382848) baseStart_3382848 baseEnd_3382848 := by
    simpa [prefixWord, tailWord_3382848, baseEnd_3382848] using wordTrace_append hprefix tailTrace_3382848
  have hstable : (prefixWord ++ tailWord_3382848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3382848).length < 2 ^ (prefixWord ++ tailWord_3382848).sum := by decide
  have hdescent : baseEnd_3382848 < baseStart_3382848 := by decide
  rcases family_descends (prefixWord ++ tailWord_3382848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3382902 : List Nat := [5, 1, 1, 2, 2, 1, 3, 1, 1, 1, 5]
def baseStart_3382902 : Nat := 118140960795 + 3382902 * 2 ^ 59
def prefixEnd_3382902 : Nat := 4983230072969 + 3 ^ 40 * 3382902 * 2
def baseEnd_3382902 : Nat := 1737054733056228614067323

theorem tailTrace_3382902 : CollatzResearch.WordTrace tailWord_3382902 prefixEnd_3382902 1737054733056228614067323 := by
  unfold tailWord_3382902
  simp only [CollatzResearch.WordTrace]
  refine ⟨7711535774395705156836935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 82256381593554188339593973 7711535774395705156836935)
  ·
    refine ⟨11567303661593557735255403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7711535774395705156836935 11567303661593557735255403)
    ·
      refine ⟨17350955492390336602883105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11567303661593557735255403 17350955492390336602883105)
      ·
        refine ⟨13013216619292752452162329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17350955492390336602883105 13013216619292752452162329)
        ·
          refine ⟨9759912464469564339121747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13013216619292752452162329 9759912464469564339121747)
          ·
            refine ⟨14639868696704346508682621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9759912464469564339121747 14639868696704346508682621)
            ·
              refine ⟨5489950761264129940755983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14639868696704346508682621 5489950761264129940755983)
              ·
                refine ⟨8234926141896194911133975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5489950761264129940755983 8234926141896194911133975)
                ·
                  refine ⟨12352389212844292366700963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8234926141896194911133975 12352389212844292366700963)
                  ·
                    refine ⟨18528583819266438550051445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12352389212844292366700963 18528583819266438550051445)
                    ·
                      refine ⟨1737054733056228614067323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18528583819266438550051445 1737054733056228614067323)
                      ·
                        rfl

theorem cell23_3382902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 3, 1, 1, 1, 5].length) (baseStart_3382902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3382902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3382902 prefixEnd_3382902 := by exact prefixLift 3382902
  have htrace : WordTrace (prefixWord ++ tailWord_3382902) baseStart_3382902 baseEnd_3382902 := by
    simpa [prefixWord, tailWord_3382902, baseEnd_3382902] using wordTrace_append hprefix tailTrace_3382902
  have hstable : (prefixWord ++ tailWord_3382902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3382902).length < 2 ^ (prefixWord ++ tailWord_3382902).sum := by decide
  have hdescent : baseEnd_3382902 < baseStart_3382902 := by decide
  rcases family_descends (prefixWord ++ tailWord_3382902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3382966 : List Nat := [5, 1, 3, 1, 1, 2, 1, 1, 4, 1, 3]
def baseStart_3382966 : Nat := 118140960795 + 3382966 * 2 ^ 59
def prefixEnd_3382966 : Nat := 4983230072969 + 3 ^ 40 * 3382966 * 2
def baseEnd_3382966 : Nat := 1737087595818116363667029

theorem tailTrace_3382966 : CollatzResearch.WordTrace tailWord_3382966 prefixEnd_3382966 1737087595818116363667029 := by
  unfold tailWord_3382966
  simp only [CollatzResearch.WordTrace]
  refine ⟨7711681666381213839982547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 82257937774732947626480501 7711681666381213839982547)
  ·
    refine ⟨11567522499571820759973821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7711681666381213839982547 11567522499571820759973821)
    ·
      refine ⟨4337820937339432784990183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11567522499571820759973821 4337820937339432784990183)
      ·
        refine ⟨6506731406009149177485275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4337820937339432784990183 6506731406009149177485275)
        ·
          refine ⟨9760097109013723766227913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6506731406009149177485275 9760097109013723766227913)
          ·
            refine ⟨7320072831760292824670935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9760097109013723766227913 7320072831760292824670935)
            ·
              refine ⟨10980109247640439237006403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7320072831760292824670935 10980109247640439237006403)
              ·
                refine ⟨16470163871460658855509605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10980109247640439237006403 16470163871460658855509605)
                ·
                  refine ⟨3088155725898873535408051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16470163871460658855509605 3088155725898873535408051)
                  ·
                    refine ⟨4632233588848310303112077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3088155725898873535408051 4632233588848310303112077)
                    ·
                      refine ⟨1737087595818116363667029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4632233588848310303112077 1737087595818116363667029)
                      ·
                        rfl

theorem cell23_3382966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_3382966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3382966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3382966 prefixEnd_3382966 := by exact prefixLift 3382966
  have htrace : WordTrace (prefixWord ++ tailWord_3382966) baseStart_3382966 baseEnd_3382966 := by
    simpa [prefixWord, tailWord_3382966, baseEnd_3382966] using wordTrace_append hprefix tailTrace_3382966
  have hstable : (prefixWord ++ tailWord_3382966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3382966).length < 2 ^ (prefixWord ++ tailWord_3382966).sum := by decide
  have hdescent : baseEnd_3382966 < baseStart_3382966 := by decide
  rcases family_descends (prefixWord ++ tailWord_3382966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3383025 : List Nat := [1, 2, 2, 2, 2, 3, 1, 1, 4, 5]
def baseStart_3383025 : Nat := 118140960795 + 3383025 * 2 ^ 59
def prefixEnd_3383025 : Nat := 4983230072969 + 3 ^ 40 * 3383025 * 2
def baseEnd_3383025 : Nat := 579039297058910544276419

theorem tailTrace_3383025 : CollatzResearch.WordTrace tailWord_3383025 prefixEnd_3383025 579039297058910544276419 := by
  unfold tailWord_3383025
  simp only [CollatzResearch.WordTrace]
  refine ⟨123389058568885674516118529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82259372379257116344079019 123389058568885674516118529)
  ·
    refine ⟨92541793926664255887088897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123389058568885674516118529 92541793926664255887088897)
    ·
      refine ⟨69406345444998191915316673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92541793926664255887088897 69406345444998191915316673)
      ·
        refine ⟨52054759083748643936487505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69406345444998191915316673 52054759083748643936487505)
        ·
          refine ⟨39041069312811482952365629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52054759083748643936487505 39041069312811482952365629)
          ·
            refine ⟨14640400992304306107137111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39041069312811482952365629 14640400992304306107137111)
            ·
              refine ⟨21960601488456459160705667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14640400992304306107137111 21960601488456459160705667)
              ·
                refine ⟨32940902232684688741058501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21960601488456459160705667 32940902232684688741058501)
                ·
                  refine ⟨6176419168628379138948469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32940902232684688741058501 6176419168628379138948469)
                  ·
                    refine ⟨579039297058910544276419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6176419168628379138948469 579039297058910544276419)
                    ·
                      rfl

theorem cell23_3383025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 1, 4, 5].length) (baseStart_3383025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3383025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3383025 prefixEnd_3383025 := by exact prefixLift 3383025
  have htrace : WordTrace (prefixWord ++ tailWord_3383025) baseStart_3383025 baseEnd_3383025 := by
    simpa [prefixWord, tailWord_3383025, baseEnd_3383025] using wordTrace_append hprefix tailTrace_3383025
  have hstable : (prefixWord ++ tailWord_3383025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3383025).length < 2 ^ (prefixWord ++ tailWord_3383025).sum := by decide
  have hdescent : baseEnd_3383025 < baseStart_3383025 := by decide
  rcases family_descends (prefixWord ++ tailWord_3383025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3383042 : List Nat := [3, 4, 1, 1, 1, 1, 1, 2, 4, 5]
def baseStart_3383042 : Nat := 118140960795 + 3383042 * 2 ^ 59
def prefixEnd_3383042 : Nat := 4983230072969 + 3 ^ 40 * 3383042 * 2
def baseEnd_3383042 : Nat := 579042206782619355438893

theorem tailTrace_3383042 : CollatzResearch.WordTrace tailWord_3383042 prefixEnd_3383042 579042206782619355438893 := by
  unfold tailWord_3383042
  simp only [CollatzResearch.WordTrace]
  refine ⟨30847419652456021604871845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82259785739882724279658253 30847419652456021604871845)
  ·
    refine ⟨5783891184835504050913471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30847419652456021604871845 5783891184835504050913471)
    ·
      refine ⟨8675836777253256076370207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5783891184835504050913471 8675836777253256076370207)
      ·
        refine ⟨13013755165879884114555311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8675836777253256076370207 13013755165879884114555311)
        ·
          refine ⟨19520632748819826171832967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13013755165879884114555311 19520632748819826171832967)
          ·
            refine ⟨29280949123229739257749451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19520632748819826171832967 29280949123229739257749451)
            ·
              refine ⟨43921423684844608886624177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29280949123229739257749451 43921423684844608886624177)
              ·
                refine ⟨32941067763633456664968133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43921423684844608886624177 32941067763633456664968133)
                ·
                  refine ⟨6176450205681273124681525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32941067763633456664968133 6176450205681273124681525)
                  ·
                    refine ⟨579042206782619355438893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6176450205681273124681525 579042206782619355438893)
                    ·
                      rfl

theorem cell23_3383042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 2, 4, 5].length) (baseStart_3383042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3383042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3383042 prefixEnd_3383042 := by exact prefixLift 3383042
  have htrace : WordTrace (prefixWord ++ tailWord_3383042) baseStart_3383042 baseEnd_3383042 := by
    simpa [prefixWord, tailWord_3383042, baseEnd_3383042] using wordTrace_append hprefix tailTrace_3383042
  have hstable : (prefixWord ++ tailWord_3383042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3383042).length < 2 ^ (prefixWord ++ tailWord_3383042).sum := by decide
  have hdescent : baseEnd_3383042 < baseStart_3383042 := by decide
  rcases family_descends (prefixWord ++ tailWord_3383042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3383065 : List Nat := [1, 2, 1, 2, 1, 1, 1, 2, 5, 4, 3]
def baseStart_3383065 : Nat := 118140960795 + 3383065 * 2 ^ 59
def prefixEnd_3383065 : Nat := 4983230072969 + 3 ^ 40 * 3383065 * 2
def baseEnd_3383065 : Nat := 1737138430402911476329073

theorem tailTrace_3383065 : CollatzResearch.WordTrace tailWord_3383065 prefixEnd_3383065 1737138430402911476329073 := by
  unfold tailWord_3383065
  simp only [CollatzResearch.WordTrace]
  refine ⟨123390517488740761347574649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82260344992493840898383099 123390517488740761347574649)
  ·
    refine ⟨92542888116555571010680987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123390517488740761347574649 92542888116555571010680987)
    ·
      refine ⟨138814332174833356516021481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92542888116555571010680987 138814332174833356516021481)
      ·
        refine ⟨104110749131125017387016111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138814332174833356516021481 104110749131125017387016111)
        ·
          refine ⟨156166123696687526080524167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104110749131125017387016111 156166123696687526080524167)
          ·
            refine ⟨234249185545031289120786251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156166123696687526080524167 234249185545031289120786251)
            ·
              refine ⟨351373778317546933681179377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 234249185545031289120786251 351373778317546933681179377)
              ·
                refine ⟨263530333738160200260884533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 351373778317546933681179377 263530333738160200260884533)
                ·
                  refine ⟨24705968787952518774457925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 263530333738160200260884533 24705968787952518774457925)
                  ·
                    refine ⟨4632369147741097270210861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24705968787952518774457925 4632369147741097270210861)
                    ·
                      refine ⟨1737138430402911476329073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4632369147741097270210861 1737138430402911476329073)
                      ·
                        rfl

theorem cell23_3383065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 5, 4, 3].length) (baseStart_3383065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3383065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3383065 prefixEnd_3383065 := by exact prefixLift 3383065
  have htrace : WordTrace (prefixWord ++ tailWord_3383065) baseStart_3383065 baseEnd_3383065 := by
    simpa [prefixWord, tailWord_3383065, baseEnd_3383065] using wordTrace_append hprefix tailTrace_3383065
  have hstable : (prefixWord ++ tailWord_3383065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3383065).length < 2 ^ (prefixWord ++ tailWord_3383065).sum := by decide
  have hdescent : baseEnd_3383065 < baseStart_3383065 := by decide
  rcases family_descends (prefixWord ++ tailWord_3383065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3383116 : List Nat := [2, 2, 1, 3, 4, 2, 1, 1, 2, 2, 3]
def baseStart_3383116 : Nat := 118140960795 + 3383116 * 2 ^ 59
def prefixEnd_3383116 : Nat := 4983230072969 + 3 ^ 40 * 3383116 * 2
def baseEnd_3383116 : Nat := 1737164617916290776791339

theorem tailTrace_3383116 : CollatzResearch.WordTrace tailWord_3383116 prefixEnd_3383116 1737164617916290776791339 := by
  unfold tailWord_3383116
  simp only [CollatzResearch.WordTrace]
  refine ⟨61696188805777998528840601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82261585074370664705120801 61696188805777998528840601)
  ·
    refine ⟨46272141604333498896630451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61696188805777998528840601 46272141604333498896630451)
    ·
      refine ⟨69408212406500248344945677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46272141604333498896630451 69408212406500248344945677)
      ·
        refine ⟨26028079652437593129354629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69408212406500248344945677 26028079652437593129354629)
        ·
          refine ⟨4880264934832048711753993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26028079652437593129354629 4880264934832048711753993)
          ·
            refine ⟨3660198701124036533815495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4880264934832048711753993 3660198701124036533815495)
            ·
              refine ⟨5490298051686054800723243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3660198701124036533815495 5490298051686054800723243)
              ·
                refine ⟨8235447077529082201084865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5490298051686054800723243 8235447077529082201084865)
                ·
                  refine ⟨6176585308146811650813649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8235447077529082201084865 6176585308146811650813649)
                  ·
                    refine ⟨4632438981110108738110237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6176585308146811650813649 4632438981110108738110237)
                    ·
                      refine ⟨1737164617916290776791339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4632438981110108738110237 1737164617916290776791339)
                      ·
                        rfl

theorem cell23_3383116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 1, 1, 2, 2, 3].length) (baseStart_3383116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3383116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3383116 prefixEnd_3383116 := by exact prefixLift 3383116
  have htrace : WordTrace (prefixWord ++ tailWord_3383116) baseStart_3383116 baseEnd_3383116 := by
    simpa [prefixWord, tailWord_3383116, baseEnd_3383116] using wordTrace_append hprefix tailTrace_3383116
  have hstable : (prefixWord ++ tailWord_3383116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3383116).length < 2 ^ (prefixWord ++ tailWord_3383116).sum := by decide
  have hdescent : baseEnd_3383116 < baseStart_3383116 := by decide
  rcases family_descends (prefixWord ++ tailWord_3383116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3383145 : List Nat := [1, 2, 1, 1, 1, 3, 1, 4, 3, 6]
def baseStart_3383145 : Nat := 118140960795 + 3383145 * 2 ^ 59
def prefixEnd_3383145 : Nat := 4983230072969 + 3 ^ 40 * 3383145 * 2
def baseEnd_3383145 : Nat := 579059836285090387776235

theorem tailTrace_3383145 : CollatzResearch.WordTrace tailWord_3383145 prefixEnd_3383145 579059836285090387776235 := by
  unfold tailWord_3383145
  simp only [CollatzResearch.WordTrace]
  refine ⟨123393435328450935010486889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82262290218967290006991259 123393435328450935010486889)
  ·
    refine ⟨92545076496338201257865167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123393435328450935010486889 92545076496338201257865167)
    ·
      refine ⟨138817614744507301886797751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92545076496338201257865167 138817614744507301886797751)
      ·
        refine ⟨208226422116760952830196627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138817614744507301886797751 208226422116760952830196627)
        ·
          refine ⟨312339633175141429245294941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208226422116760952830196627 312339633175141429245294941)
          ·
            refine ⟨117127362440678035966985603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 312339633175141429245294941 117127362440678035966985603)
            ·
              refine ⟨175691043661017053950478405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117127362440678035966985603 175691043661017053950478405)
              ·
                refine ⟨32942070686440697615714701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 175691043661017053950478405 32942070686440697615714701)
                ·
                  refine ⟨12353276507415261605893013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32942070686440697615714701 12353276507415261605893013)
                  ·
                    refine ⟨579059836285090387776235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12353276507415261605893013 579059836285090387776235)
                    ·
                      rfl

theorem cell23_3383145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 4, 3, 6].length) (baseStart_3383145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3383145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3383145 prefixEnd_3383145 := by exact prefixLift 3383145
  have htrace : WordTrace (prefixWord ++ tailWord_3383145) baseStart_3383145 baseEnd_3383145 := by
    simpa [prefixWord, tailWord_3383145, baseEnd_3383145] using wordTrace_append hprefix tailTrace_3383145
  have hstable : (prefixWord ++ tailWord_3383145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3383145).length < 2 ^ (prefixWord ++ tailWord_3383145).sum := by decide
  have hdescent : baseEnd_3383145 < baseStart_3383145 := by decide
  rcases family_descends (prefixWord ++ tailWord_3383145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3383162 : List Nat := [3, 1, 1, 1, 1, 1, 7, 1, 1, 6]
def baseStart_3383162 : Nat := 118140960795 + 3383162 * 2 ^ 59
def prefixEnd_3383162 : Nat := 4983230072969 + 3 ^ 40 * 3383162 * 2
def baseEnd_3383162 : Nat := 579062746008799198938709

theorem tailTrace_3383162 : CollatzResearch.WordTrace tailWord_3383162 prefixEnd_3383162 579062746008799198938709 := by
  unfold tailWord_3383162
  simp only [CollatzResearch.WordTrace]
  refine ⟨30848513842347336728463935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82262703579592897942570493 30848513842347336728463935)
  ·
    refine ⟨46272770763521005092695903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30848513842347336728463935 46272770763521005092695903)
    ·
      refine ⟨69409156145281507639043855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46272770763521005092695903 69409156145281507639043855)
      ·
        refine ⟨104113734217922261458565783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69409156145281507639043855 104113734217922261458565783)
        ·
          refine ⟨156170601326883392187848675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104113734217922261458565783 156170601326883392187848675)
          ·
            refine ⟨234255901990325088281773013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156170601326883392187848675 234255901990325088281773013)
            ·
              refine ⟨5490372702898244256604055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 234255901990325088281773013 5490372702898244256604055)
              ·
                refine ⟨8235559054347366384906083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5490372702898244256604055 8235559054347366384906083)
                ·
                  refine ⟨12353338581521049577359125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8235559054347366384906083 12353338581521049577359125)
                  ·
                    refine ⟨579062746008799198938709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12353338581521049577359125 579062746008799198938709)
                    ·
                      rfl

theorem cell23_3383162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 7, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 7, 1, 1, 6].length) (baseStart_3383162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3383162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3383162 prefixEnd_3383162 := by exact prefixLift 3383162
  have htrace : WordTrace (prefixWord ++ tailWord_3383162) baseStart_3383162 baseEnd_3383162 := by
    simpa [prefixWord, tailWord_3383162, baseEnd_3383162] using wordTrace_append hprefix tailTrace_3383162
  have hstable : (prefixWord ++ tailWord_3383162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3383162).length < 2 ^ (prefixWord ++ tailWord_3383162).sum := by decide
  have hdescent : baseEnd_3383162 < baseStart_3383162 := by decide
  rcases family_descends (prefixWord ++ tailWord_3383162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3383166 : List Nat := [4, 2, 3, 1, 1, 1, 1, 4, 1, 5]
def baseStart_3383166 : Nat := 118140960795 + 3383166 * 2 ^ 59
def prefixEnd_3383166 : Nat := 4983230072969 + 3 ^ 40 * 3383166 * 2
def baseEnd_3383166 : Nat := 579063430649671860388703

theorem tailTrace_3383166 : CollatzResearch.WordTrace tailWord_3383166 prefixEnd_3383166 579063430649671860388703 := by
  unfold tailWord_3383166
  simp only [CollatzResearch.WordTrace]
  refine ⟨15424275157671856949625169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82262800840916570398000901 15424275157671856949625169)
  ·
    refine ⟨11568206368253892712218877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15424275157671856949625169 11568206368253892712218877)
    ·
      refine ⟨4338077388095209767082079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11568206368253892712218877 4338077388095209767082079)
      ·
        refine ⟨6507116082142814650623119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4338077388095209767082079 6507116082142814650623119)
        ·
          refine ⟨9760674123214221975934679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6507116082142814650623119 9760674123214221975934679)
          ·
            refine ⟨14641011184821332963902019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9760674123214221975934679 14641011184821332963902019)
            ·
              refine ⟨21961516777231999445853029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14641011184821332963902019 21961516777231999445853029)
              ·
                refine ⟨4117784395730999896097443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21961516777231999445853029 4117784395730999896097443)
                ·
                  refine ⟨6176676593596499844146165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4117784395730999896097443 6176676593596499844146165)
                  ·
                    refine ⟨579063430649671860388703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6176676593596499844146165 579063430649671860388703)
                    ·
                      rfl

theorem cell23_3383166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_3383166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3383166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3383166 prefixEnd_3383166 := by exact prefixLift 3383166
  have htrace : WordTrace (prefixWord ++ tailWord_3383166) baseStart_3383166 baseEnd_3383166 := by
    simpa [prefixWord, tailWord_3383166, baseEnd_3383166] using wordTrace_append hprefix tailTrace_3383166
  have hstable : (prefixWord ++ tailWord_3383166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3383166).length < 2 ^ (prefixWord ++ tailWord_3383166).sum := by decide
  have hdescent : baseEnd_3383166 < baseStart_3383166 := by decide
  rcases family_descends (prefixWord ++ tailWord_3383166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3383186 : List Nat := [3, 2, 3, 2, 1, 1, 2, 3, 1, 1, 4]
def baseStart_3383186 : Nat := 118140960795 + 3383186 * 2 ^ 59
def prefixEnd_3383186 : Nat := 4983230072969 + 3 ^ 40 * 3383186 * 2
def baseEnd_3383186 : Nat := 1737200561562105502916017

theorem tailTrace_3383186 : CollatzResearch.WordTrace tailWord_3383186 prefixEnd_3383186 1737200561562105502916017 := by
  unfold tailWord_3383186
  simp only [CollatzResearch.WordTrace]
  refine ⟨30848732680325599753182353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82263287147534932675152941 30848732680325599753182353)
  ·
    refine ⟨23136549510244199814886765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30848732680325599753182353 23136549510244199814886765)
    ·
      refine ⟨8676206066341574930582537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23136549510244199814886765 8676206066341574930582537)
      ·
        refine ⟨6507154549756181197936903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8676206066341574930582537 6507154549756181197936903)
        ·
          refine ⟨9760731824634271796905355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6507154549756181197936903 9760731824634271796905355)
          ·
            refine ⟨14641097736951407695358033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9760731824634271796905355 14641097736951407695358033)
            ·
              refine ⟨10980823302713555771518525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14641097736951407695358033 10980823302713555771518525)
              ·
                refine ⟨4117808738517583414319447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10980823302713555771518525 4117808738517583414319447)
                ·
                  refine ⟨6176713107776375121479171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4117808738517583414319447 6176713107776375121479171)
                  ·
                    refine ⟨9265069661664562682218757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6176713107776375121479171 9265069661664562682218757)
                    ·
                      refine ⟨1737200561562105502916017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9265069661664562682218757 1737200561562105502916017)
                      ·
                        rfl

theorem cell23_3383186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_3383186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3383186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3383186 prefixEnd_3383186 := by exact prefixLift 3383186
  have htrace : WordTrace (prefixWord ++ tailWord_3383186) baseStart_3383186 baseEnd_3383186 := by
    simpa [prefixWord, tailWord_3383186, baseEnd_3383186] using wordTrace_append hprefix tailTrace_3383186
  have hstable : (prefixWord ++ tailWord_3383186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3383186).length < 2 ^ (prefixWord ++ tailWord_3383186).sum := by decide
  have hdescent : baseEnd_3383186 < baseStart_3383186 := by decide
  rcases family_descends (prefixWord ++ tailWord_3383186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3383189 : List Nat := [1, 3, 2, 1, 1, 3, 1, 5, 1, 2, 3]
def baseStart_3383189 : Nat := 118140960795 + 3383189 * 2 ^ 59
def prefixEnd_3383189 : Nat := 4983230072969 + 3 ^ 40 * 3383189 * 2
def baseEnd_3383189 : Nat := 1737202102004068991178503

theorem tailTrace_3383189 : CollatzResearch.WordTrace tailWord_3383189 prefixEnd_3383189 1737202102004068991178503 := by
  unfold tailWord_3383189
  simp only [CollatzResearch.WordTrace]
  refine ⟨123395040140291530525088621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82263360093527687016725747 123395040140291530525088621)
  ·
    refine ⟨46273140052609323946908233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123395040140291530525088621 46273140052609323946908233)
    ·
      refine ⟨34704855039456992960181175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46273140052609323946908233 34704855039456992960181175)
      ·
        refine ⟨52057282559185489440271763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34704855039456992960181175 52057282559185489440271763)
        ·
          refine ⟨78085923838778234160407645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52057282559185489440271763 78085923838778234160407645)
          ·
            refine ⟨29282221439541837810152867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78085923838778234160407645 29282221439541837810152867)
            ·
              refine ⟨43923332159312756715229301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29282221439541837810152867 43923332159312756715229301)
              ·
                refine ⟨4117812389935570942052747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43923332159312756715229301 4117812389935570942052747)
                ·
                  refine ⟨6176718584903356413079121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4117812389935570942052747 6176718584903356413079121)
                  ·
                    refine ⟨4632538938677517309809341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6176718584903356413079121 4632538938677517309809341)
                    ·
                      refine ⟨1737202102004068991178503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4632538938677517309809341 1737202102004068991178503)
                      ·
                        rfl

theorem cell23_3383189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 5, 1, 2, 3].length) (baseStart_3383189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3383189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3383189 prefixEnd_3383189 := by exact prefixLift 3383189
  have htrace : WordTrace (prefixWord ++ tailWord_3383189) baseStart_3383189 baseEnd_3383189 := by
    simpa [prefixWord, tailWord_3383189, baseEnd_3383189] using wordTrace_append hprefix tailTrace_3383189
  have hstable : (prefixWord ++ tailWord_3383189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3383189).length < 2 ^ (prefixWord ++ tailWord_3383189).sum := by decide
  have hdescent : baseEnd_3383189 < baseStart_3383189 := by decide
  rcases family_descends (prefixWord ++ tailWord_3383189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3383220 : List Nat := [2, 5, 2, 1, 2, 2, 1, 2, 1, 1, 4]
def baseStart_3383220 : Nat := 118140960795 + 3383220 * 2 ^ 59
def prefixEnd_3383220 : Nat := 4983230072969 + 3 ^ 40 * 3383220 * 2
def baseEnd_3383220 : Nat := 1737218019904358369890861

theorem tailTrace_3383220 : CollatzResearch.WordTrace tailWord_3383220 prefixEnd_3383220 1737218019904358369890861 := by
  unfold tailWord_3383220
  simp only [CollatzResearch.WordTrace]
  refine ⟨61698085401589611409733557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82264113868786148546311409 61698085401589611409733557)
  ·
    refine ⟨5784195506399026069662521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 61698085401589611409733557 5784195506399026069662521)
    ·
      refine ⟨4338146629799269552246891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5784195506399026069662521 4338146629799269552246891)
      ·
        refine ⟨6507219944698904328370337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4338146629799269552246891 6507219944698904328370337)
        ·
          refine ⟨4880414958524178246277753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6507219944698904328370337 4880414958524178246277753)
          ·
            refine ⟨3660311218893133684708315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4880414958524178246277753 3660311218893133684708315)
            ·
              refine ⟨5490466828339700527062473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3660311218893133684708315 5490466828339700527062473)
              ·
                refine ⟨4117850121254775395296855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5490466828339700527062473 4117850121254775395296855)
                ·
                  refine ⟨6176775181882163092945283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4117850121254775395296855 6176775181882163092945283)
                  ·
                    refine ⟨9265162772823244639417925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6176775181882163092945283 9265162772823244639417925)
                    ·
                      refine ⟨1737218019904358369890861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9265162772823244639417925 1737218019904358369890861)
                      ·
                        rfl

theorem cell23_3383220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_3383220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3383220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3383220 prefixEnd_3383220 := by exact prefixLift 3383220
  have htrace : WordTrace (prefixWord ++ tailWord_3383220) baseStart_3383220 baseEnd_3383220 := by
    simpa [prefixWord, tailWord_3383220, baseEnd_3383220] using wordTrace_append hprefix tailTrace_3383220
  have hstable : (prefixWord ++ tailWord_3383220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3383220).length < 2 ^ (prefixWord ++ tailWord_3383220).sum := by decide
  have hdescent : baseEnd_3383220 < baseStart_3383220 := by decide
  rcases family_descends (prefixWord ++ tailWord_3383220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3383253 : List Nat := [1, 3, 2, 3, 2, 2, 2, 2, 2, 1, 3]
def baseStart_3383253 : Nat := 118140960795 + 3383253 * 2 ^ 59
def prefixEnd_3383253 : Nat := 4983230072969 + 3 ^ 40 * 3383253 * 2
def baseEnd_3383253 : Nat := 1737234964765956740778209

theorem tailTrace_3383253 : CollatzResearch.WordTrace tailWord_3383253 prefixEnd_3383253 1737234964765956740778209 := by
  unfold tailWord_3383253
  simp only [CollatzResearch.WordTrace]
  refine ⟨123397374412059669455418413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82264916274706446303612275 123397374412059669455418413)
  ·
    refine ⟨46274015404522376045781905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123397374412059669455418413 46274015404522376045781905)
    ·
      refine ⟨34705511553391782034336429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46274015404522376045781905 34705511553391782034336429)
      ·
        refine ⟨13014566832521918262876161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34705511553391782034336429 13014566832521918262876161)
        ·
          refine ⟨9760925124391438697157121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13014566832521918262876161 9760925124391438697157121)
          ·
            refine ⟨7320693843293579022867841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9760925124391438697157121 7320693843293579022867841)
            ·
              refine ⟨5490520382470184267150881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7320693843293579022867841 5490520382470184267150881)
              ·
                refine ⟨4117890286852638200363161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5490520382470184267150881 4117890286852638200363161)
                ·
                  refine ⟨3088417715139478650272371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4117890286852638200363161 3088417715139478650272371)
                  ·
                    refine ⟨4632626572709217975408557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3088417715139478650272371 4632626572709217975408557)
                    ·
                      refine ⟨1737234964765956740778209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4632626572709217975408557 1737234964765956740778209)
                      ·
                        rfl

theorem cell23_3383253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 2, 2, 2, 1, 3].length) (baseStart_3383253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3383253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3383253 prefixEnd_3383253 := by exact prefixLift 3383253
  have htrace : WordTrace (prefixWord ++ tailWord_3383253) baseStart_3383253 baseEnd_3383253 := by
    simpa [prefixWord, tailWord_3383253, baseEnd_3383253] using wordTrace_append hprefix tailTrace_3383253
  have hstable : (prefixWord ++ tailWord_3383253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3383253).length < 2 ^ (prefixWord ++ tailWord_3383253).sum := by decide
  have hdescent : baseEnd_3383253 < baseStart_3383253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3383253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3383260 : List Nat := [2, 2, 6, 1, 2, 1, 1, 8]
def baseStart_3383260 : Nat := 118140960795 + 3383260 * 2 ^ 59
def prefixEnd_3383260 : Nat := 4983230072969 + 3 ^ 40 * 3383260 * 2
def baseEnd_3383260 : Nat := 64342168856686600495951

theorem tailTrace_3383260 : CollatzResearch.WordTrace tailWord_3383260 prefixEnd_3383260 64342168856686600495951 := by
  unfold tailWord_3383260
  simp only [CollatzResearch.WordTrace]
  refine ⟨61698814861517154825461617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82265086482022873100615489 61698814861517154825461617)
  ·
    refine ⟨46274111146137866119096213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61698814861517154825461617 46274111146137866119096213)
    ·
      refine ⟨2169098959975212474332635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 46274111146137866119096213 2169098959975212474332635)
      ·
        refine ⟨3253648439962818711498953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2169098959975212474332635 3253648439962818711498953)
        ·
          refine ⟨2440236329972114033624215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3253648439962818711498953 2440236329972114033624215)
          ·
            refine ⟨3660354494958171050436323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2440236329972114033624215 3660354494958171050436323)
            ·
              refine ⟨5490531742437256575654485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3660354494958171050436323 5490531742437256575654485)
              ·
                refine ⟨64342168856686600495951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5490531742437256575654485 64342168856686600495951)
                ·
                  rfl

theorem cell23_3383260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 1, 8].length) (baseStart_3383260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3383260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3383260 prefixEnd_3383260 := by exact prefixLift 3383260
  have htrace : WordTrace (prefixWord ++ tailWord_3383260) baseStart_3383260 baseEnd_3383260 := by
    simpa [prefixWord, tailWord_3383260, baseEnd_3383260] using wordTrace_append hprefix tailTrace_3383260
  have hstable : (prefixWord ++ tailWord_3383260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3383260).length < 2 ^ (prefixWord ++ tailWord_3383260).sum := by decide
  have hdescent : baseEnd_3383260 < baseStart_3383260 := by decide
  rcases family_descends (prefixWord ++ tailWord_3383260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3383349 : List Nat := [1, 3, 3, 1, 1, 1, 4, 1, 1, 3, 4]
def baseStart_3383349 : Nat := 118140960795 + 3383349 * 2 ^ 59
def prefixEnd_3383349 : Nat := 4983230072969 + 3 ^ 40 * 3383349 * 2
def baseEnd_3383349 : Nat := 1737284258908788365177767

theorem tailTrace_3383349 : CollatzResearch.WordTrace tailWord_3383349 prefixEnd_3383349 1737284258908788365177767 := by
  unfold tailWord_3383349
  simp only [CollatzResearch.WordTrace]
  refine ⟨123400875819711877850913101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82267250546474585233942067 123400875819711877850913101)
  ·
    refine ⟨46275328432391954194092413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123400875819711877850913101 46275328432391954194092413)
    ·
      refine ⟨17353248162146982822784655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46275328432391954194092413 17353248162146982822784655)
      ·
        refine ⟨26029872243220474234176983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17353248162146982822784655 26029872243220474234176983)
        ·
          refine ⟨39044808364830711351265475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26029872243220474234176983 39044808364830711351265475)
          ·
            refine ⟨58567212547246067026898213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39044808364830711351265475 58567212547246067026898213)
            ·
              refine ⟨10981352352608637567543415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58567212547246067026898213 10981352352608637567543415)
              ·
                refine ⟨16472028528912956351315123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10981352352608637567543415 16472028528912956351315123)
                ·
                  refine ⟨24708042793369434526972685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16472028528912956351315123 24708042793369434526972685)
                  ·
                    refine ⟨9265516047513537947614757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24708042793369434526972685 9265516047513537947614757)
                    ·
                      refine ⟨1737284258908788365177767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9265516047513537947614757 1737284258908788365177767)
                      ·
                        rfl

theorem cell23_3383349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 1, 1, 3, 4].length) (baseStart_3383349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3383349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3383349 prefixEnd_3383349 := by exact prefixLift 3383349
  have htrace : WordTrace (prefixWord ++ tailWord_3383349) baseStart_3383349 baseEnd_3383349 := by
    simpa [prefixWord, tailWord_3383349, baseEnd_3383349] using wordTrace_append hprefix tailTrace_3383349
  have hstable : (prefixWord ++ tailWord_3383349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3383349).length < 2 ^ (prefixWord ++ tailWord_3383349).sum := by decide
  have hdescent : baseEnd_3383349 < baseStart_3383349 := by decide
  rcases family_descends (prefixWord ++ tailWord_3383349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3383359 : List Nat := [1, 1, 2, 2, 3, 1, 2, 2, 5, 4]
def baseStart_3383359 : Nat := 118140960795 + 3383359 * 2 ^ 59
def prefixEnd_3383359 : Nat := 4983230072969 + 3 ^ 40 * 3383359 * 2
def baseEnd_3383359 : Nat := 579096464571777775350907

theorem tailTrace_3383359 : CollatzResearch.WordTrace tailWord_3383359 prefixEnd_3383359 579096464571777775350907 := by
  unfold tailWord_3383359
  simp only [CollatzResearch.WordTrace]
  refine ⟨123401240549675649558777131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82267493699783766372518087 123401240549675649558777131)
  ·
    refine ⟨185101860824513474338165697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123401240549675649558777131 185101860824513474338165697)
    ·
      refine ⟨138826395618385105753624273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185101860824513474338165697 138826395618385105753624273)
      ·
        refine ⟨104119796713788829315218205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138826395618385105753624273 104119796713788829315218205)
        ·
          refine ⟨39044923767670810993206827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104119796713788829315218205 39044923767670810993206827)
          ·
            refine ⟨58567385651506216489810241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39044923767670810993206827 58567385651506216489810241)
            ·
              refine ⟨43925539238629662367357681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58567385651506216489810241 43925539238629662367357681)
              ·
                refine ⟨32944154428972246775518261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43925539238629662367357681 32944154428972246775518261)
                ·
                  refine ⟨3088514477716148135204837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32944154428972246775518261 3088514477716148135204837)
                  ·
                    refine ⟨579096464571777775350907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3088514477716148135204837 579096464571777775350907)
                    ·
                      rfl

theorem cell23_3383359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 2, 5, 4].length) (baseStart_3383359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3383359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3383359 prefixEnd_3383359 := by exact prefixLift 3383359
  have htrace : WordTrace (prefixWord ++ tailWord_3383359) baseStart_3383359 baseEnd_3383359 := by
    simpa [prefixWord, tailWord_3383359, baseEnd_3383359] using wordTrace_append hprefix tailTrace_3383359
  have hstable : (prefixWord ++ tailWord_3383359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3383359).length < 2 ^ (prefixWord ++ tailWord_3383359).sum := by decide
  have hdescent : baseEnd_3383359 < baseStart_3383359 := by decide
  rcases family_descends (prefixWord ++ tailWord_3383359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3383450 : List Nat := [3, 1, 1, 5, 2, 1, 1, 2, 3, 1, 3]
def baseStart_3383450 : Nat := 118140960795 + 3383450 * 2 ^ 59
def prefixEnd_3383450 : Nat := 4983230072969 + 3 ^ 40 * 3383450 * 2
def baseEnd_3383450 : Nat := 1737336120454892470014803

theorem tailTrace_3383450 : CollatzResearch.WordTrace tailWord_3383450 prefixEnd_3383450 1737336120454892470014803 := by
  unfold tailWord_3383450
  simp only [CollatzResearch.WordTrace]
  refine ⟨30851139898086493025084951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82269706394897314733559869 30851139898086493025084951)
  ·
    refine ⟨46276709847129739537627427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30851139898086493025084951 46276709847129739537627427)
    ·
      refine ⟨69415064770694609306441141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46276709847129739537627427 69415064770694609306441141)
      ·
        refine ⟨6507662322252619622478857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 69415064770694609306441141 6507662322252619622478857)
        ·
          refine ⟨4880746741689464716859143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6507662322252619622478857 4880746741689464716859143)
          ·
            refine ⟨7321120112534197075288715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4880746741689464716859143 7321120112534197075288715)
            ·
              refine ⟨10981680168801295612933073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7321120112534197075288715 10981680168801295612933073)
              ·
                refine ⟨8236260126600971709699805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10981680168801295612933073 8236260126600971709699805)
                ·
                  refine ⟨3088597547475364391137427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8236260126600971709699805 3088597547475364391137427)
                  ·
                    refine ⟨4632896321213046586706141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3088597547475364391137427 4632896321213046586706141)
                    ·
                      refine ⟨1737336120454892470014803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4632896321213046586706141 1737336120454892470014803)
                      ·
                        rfl

theorem cell23_3383450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_3383450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3383450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3383450 prefixEnd_3383450 := by exact prefixLift 3383450
  have htrace : WordTrace (prefixWord ++ tailWord_3383450) baseStart_3383450 baseEnd_3383450 := by
    simpa [prefixWord, tailWord_3383450, baseEnd_3383450] using wordTrace_append hprefix tailTrace_3383450
  have hstable : (prefixWord ++ tailWord_3383450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3383450).length < 2 ^ (prefixWord ++ tailWord_3383450).sum := by decide
  have hdescent : baseEnd_3383450 < baseStart_3383450 := by decide
  rcases family_descends (prefixWord ++ tailWord_3383450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3383456 : List Nat := [2, 1, 1, 4, 2, 2, 2, 1, 3, 1, 4]
def baseStart_3383456 : Nat := 118140960795 + 3383456 * 2 ^ 59
def prefixEnd_3383456 : Nat := 4983230072969 + 3 ^ 40 * 3383456 * 2
def baseEnd_3383456 : Nat := 1737339201338819446539775

theorem tailTrace_3383456 : CollatzResearch.WordTrace tailWord_3383456 prefixEnd_3383456 1737339201338819446539775 := by
  unfold tailWord_3383456
  simp only [CollatzResearch.WordTrace]
  refine ⟨61702389215162117562529111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82269852286882823416705481 61702389215162117562529111)
  ·
    refine ⟨92553583822743176343793667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61702389215162117562529111 92553583822743176343793667)
    ·
      refine ⟨138830375734114764515690501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92553583822743176343793667 138830375734114764515690501)
      ·
        refine ⟨26030695450146518346691969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 138830375734114764515690501 26030695450146518346691969)
        ·
          refine ⟨19523021587609888760018977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26030695450146518346691969 19523021587609888760018977)
          ·
            refine ⟨14642266190707416570014233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19523021587609888760018977 14642266190707416570014233)
            ·
              refine ⟨10981699643030562427510675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14642266190707416570014233 10981699643030562427510675)
              ·
                refine ⟨16472549464545843641266013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10981699643030562427510675 16472549464545843641266013)
                ·
                  refine ⟨6177206049204691365474755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16472549464545843641266013 6177206049204691365474755)
                  ·
                    refine ⟨9265809073807037048212133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6177206049204691365474755 9265809073807037048212133)
                    ·
                      refine ⟨1737339201338819446539775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9265809073807037048212133 1737339201338819446539775)
                      ·
                        rfl

theorem cell23_3383456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 1, 3, 1, 4].length) (baseStart_3383456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3383456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3383456 prefixEnd_3383456 := by exact prefixLift 3383456
  have htrace : WordTrace (prefixWord ++ tailWord_3383456) baseStart_3383456 baseEnd_3383456 := by
    simpa [prefixWord, tailWord_3383456, baseEnd_3383456] using wordTrace_append hprefix tailTrace_3383456
  have hstable : (prefixWord ++ tailWord_3383456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3383456).length < 2 ^ (prefixWord ++ tailWord_3383456).sum := by decide
  have hdescent : baseEnd_3383456 < baseStart_3383456 := by decide
  rcases family_descends (prefixWord ++ tailWord_3383456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3383479 : List Nat := [1, 1, 3, 1, 4, 3, 10]
def baseStart_3383479 : Nat := 118140960795 + 3383479 * 2 ^ 59
def prefixEnd_3383479 : Nat := 4983230072969 + 3 ^ 40 * 3383479 * 2
def baseEnd_3383479 : Nat := 21448777918442874772249

theorem tailTrace_3383479 : CollatzResearch.WordTrace tailWord_3383479 prefixEnd_3383479 21448777918442874772249 := by
  unfold tailWord_3383479
  simp only [CollatzResearch.WordTrace]
  refine ⟨123405617309240910053145491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82270411539493940035430327 123405617309240910053145491)
  ·
    refine ⟨185108425963861365079718237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123405617309240910053145491 185108425963861365079718237)
    ·
      refine ⟨69415659736448011904894339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185108425963861365079718237 69415659736448011904894339)
      ·
        refine ⟨104123489604672017857341509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69415659736448011904894339 104123489604672017857341509)
        ·
          refine ⟨19523154300876003348251533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104123489604672017857341509 19523154300876003348251533)
          ·
            refine ⟨7321182862828501255594325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19523154300876003348251533 7321182862828501255594325)
            ·
              refine ⟨21448777918442874772249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7321182862828501255594325 21448777918442874772249)
              ·
                rfl

theorem cell23_3383479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 10].length) (baseStart_3383479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3383479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3383479 prefixEnd_3383479 := by exact prefixLift 3383479
  have htrace : WordTrace (prefixWord ++ tailWord_3383479) baseStart_3383479 baseEnd_3383479 := by
    simpa [prefixWord, tailWord_3383479, baseEnd_3383479] using wordTrace_append hprefix tailTrace_3383479
  have hstable : (prefixWord ++ tailWord_3383479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3383479).length < 2 ^ (prefixWord ++ tailWord_3383479).sum := by decide
  have hdescent : baseEnd_3383479 < baseStart_3383479 := by decide
  rcases family_descends (prefixWord ++ tailWord_3383479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3383500 : List Nat := [2, 2, 1, 6, 1, 2, 1, 1, 1, 6]
def baseStart_3383500 : Nat := 118140960795 + 3383500 * 2 ^ 59
def prefixEnd_3383500 : Nat := 4983230072969 + 3 ^ 40 * 3383500 * 2
def baseEnd_3383500 : Nat := 579120598162539091463191

theorem tailTrace_3383500 : CollatzResearch.WordTrace tailWord_3383500 prefixEnd_3383500 579120598162539091463191 := by
  unfold tailWord_3383500
  simp only [CollatzResearch.WordTrace]
  refine ⟨61703191621082415319829977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82270922161443220426439969 61703191621082415319829977)
  ·
    refine ⟨46277393715811811489872483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61703191621082415319829977 46277393715811811489872483)
    ·
      refine ⟨69416090573717717234808725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46277393715811811489872483 69416090573717717234808725)
      ·
        refine ⟨3253879245643017995381659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 69416090573717717234808725 3253879245643017995381659)
        ·
          refine ⟨4880818868464526993072489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3253879245643017995381659 4880818868464526993072489)
          ·
            refine ⟨3660614151348395244804367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4880818868464526993072489 3660614151348395244804367)
            ·
              refine ⟨5490921227022592867206551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3660614151348395244804367 5490921227022592867206551)
              ·
                refine ⟨8236381840533889300809827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5490921227022592867206551 8236381840533889300809827)
                ·
                  refine ⟨12354572760800833951214741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8236381840533889300809827 12354572760800833951214741)
                  ·
                    refine ⟨579120598162539091463191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12354572760800833951214741 579120598162539091463191)
                    ·
                      rfl

theorem cell23_3383500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 1, 1, 1, 6].length) (baseStart_3383500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3383500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3383500 prefixEnd_3383500 := by exact prefixLift 3383500
  have htrace : WordTrace (prefixWord ++ tailWord_3383500) baseStart_3383500 baseEnd_3383500 := by
    simpa [prefixWord, tailWord_3383500, baseEnd_3383500] using wordTrace_append hprefix tailTrace_3383500
  have hstable : (prefixWord ++ tailWord_3383500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3383500).length < 2 ^ (prefixWord ++ tailWord_3383500).sum := by decide
  have hdescent : baseEnd_3383500 < baseStart_3383500 := by decide
  rcases family_descends (prefixWord ++ tailWord_3383500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3383550 : List Nat := [4, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2]
def baseStart_3383550 : Nat := 118140960795 + 3383550 * 2 ^ 59
def prefixEnd_3383550 : Nat := 4983230072969 + 3 ^ 40 * 3383550 * 2
def baseEnd_3383550 : Nat := 1737387468520342078764343

theorem tailTrace_3383550 : CollatzResearch.WordTrace tailWord_3383550 prefixEnd_3383550 1737387468520342078764343 := by
  unfold tailWord_3383550
  simp only [CollatzResearch.WordTrace]
  refine ⟨15426025861497961147372513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82272137927989126119320069 15426025861497961147372513)
  ·
    refine ⟨11569519396123470860529385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15426025861497961147372513 11569519396123470860529385)
    ·
      refine ⟨8677139547092603145397039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11569519396123470860529385 8677139547092603145397039)
      ·
        refine ⟨13015709320638904718095559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8677139547092603145397039 13015709320638904718095559)
        ·
          refine ⟨19523563980958357077143339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13015709320638904718095559 19523563980958357077143339)
          ·
            refine ⟨29285345971437535615715009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19523563980958357077143339 29285345971437535615715009)
            ·
              refine ⟨21964009478578151711786257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29285345971437535615715009 21964009478578151711786257)
              ·
                refine ⟨16473007108933613783839693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21964009478578151711786257 16473007108933613783839693)
                ·
                  refine ⟨6177377665850105168939885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16473007108933613783839693 6177377665850105168939885)
                  ·
                    refine ⟨2316516624693789438352457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6177377665850105168939885 2316516624693789438352457)
                    ·
                      refine ⟨1737387468520342078764343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2316516624693789438352457 1737387468520342078764343)
                      ·
                        rfl

theorem cell23_3383550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2].length) (baseStart_3383550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3383550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3383550 prefixEnd_3383550 := by exact prefixLift 3383550
  have htrace : WordTrace (prefixWord ++ tailWord_3383550) baseStart_3383550 baseEnd_3383550 := by
    simpa [prefixWord, tailWord_3383550, baseEnd_3383550] using wordTrace_append hprefix tailTrace_3383550
  have hstable : (prefixWord ++ tailWord_3383550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3383550).length < 2 ^ (prefixWord ++ tailWord_3383550).sum := by decide
  have hdescent : baseEnd_3383550 < baseStart_3383550 := by decide
  rcases family_descends (prefixWord ++ tailWord_3383550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3383563 : List Nat := [1, 1, 1, 1, 5, 2, 2, 3, 1, 4, 2]
def baseStart_3383563 : Nat := 118140960795 + 3383563 * 2 ^ 59
def prefixEnd_3383563 : Nat := 4983230072969 + 3 ^ 40 * 3383563 * 2
def baseEnd_3383563 : Nat := 1737394143768850527901783

theorem tailTrace_3383563 : CollatzResearch.WordTrace tailWord_3383563 prefixEnd_3383563 1737394143768850527901783 := by
  unfold tailWord_3383563
  simp only [CollatzResearch.WordTrace]
  refine ⟨123408681040936592399203343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82272454027291061599468895 123408681040936592399203343)
  ·
    refine ⟨185113021561404888598805015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123408681040936592399203343 185113021561404888598805015)
    ·
      refine ⟨277669532342107332898207523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185113021561404888598805015 277669532342107332898207523)
      ·
        refine ⟨416504298513160999347311285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277669532342107332898207523 416504298513160999347311285)
        ·
          refine ⟨39047277985608843688810433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 416504298513160999347311285 39047277985608843688810433)
          ·
            refine ⟨29285458489206632766607825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39047277985608843688810433 29285458489206632766607825)
            ·
              refine ⟨21964093866904974574955869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29285458489206632766607825 21964093866904974574955869)
              ·
                refine ⟨8236535200089365465608451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21964093866904974574955869 8236535200089365465608451)
                ·
                  refine ⟨12354802800134048198412677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8236535200089365465608451 12354802800134048198412677)
                  ·
                    refine ⟨2316525525025134037202377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12354802800134048198412677 2316525525025134037202377)
                    ·
                      refine ⟨1737394143768850527901783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2316525525025134037202377 1737394143768850527901783)
                      ·
                        rfl

theorem cell23_3383563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 3, 1, 4, 2].length) (baseStart_3383563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3383563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3383563 prefixEnd_3383563 := by exact prefixLift 3383563
  have htrace : WordTrace (prefixWord ++ tailWord_3383563) baseStart_3383563 baseEnd_3383563 := by
    simpa [prefixWord, tailWord_3383563, baseEnd_3383563] using wordTrace_append hprefix tailTrace_3383563
  have hstable : (prefixWord ++ tailWord_3383563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3383563).length < 2 ^ (prefixWord ++ tailWord_3383563).sum := by decide
  have hdescent : baseEnd_3383563 < baseStart_3383563 := by decide
  rcases family_descends (prefixWord ++ tailWord_3383563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3383566 : List Nat := [4, 1, 1, 2, 1, 2, 1, 1, 4, 1, 5]
def baseStart_3383566 : Nat := 118140960795 + 3383566 * 2 ^ 59
def prefixEnd_3383566 : Nat := 4983230072969 + 3 ^ 40 * 3383566 * 2
def baseEnd_3383566 : Nat := 1737395684210814016164269

theorem tailTrace_3383566 : CollatzResearch.WordTrace tailWord_3383566 prefixEnd_3383566 1737395684210814016164269 := by
  unfold tailWord_3383566
  simp only [CollatzResearch.WordTrace]
  refine ⟨15426098807490715488945319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82272526973283815941041701 15426098807490715488945319)
  ·
    refine ⟨23139148211236073233417979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15426098807490715488945319 23139148211236073233417979)
    ·
      refine ⟨34708722316854109850126969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23139148211236073233417979 34708722316854109850126969)
      ·
        refine ⟨26031541737640582387595227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34708722316854109850126969 26031541737640582387595227)
        ·
          refine ⟨39047312606460873581392841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26031541737640582387595227 39047312606460873581392841)
          ·
            refine ⟨29285484454845655186044631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39047312606460873581392841 29285484454845655186044631)
            ·
              refine ⟨43928226682268482779066947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29285484454845655186044631 43928226682268482779066947)
              ·
                refine ⟨65892340023402724168600421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43928226682268482779066947 65892340023402724168600421)
                ·
                  refine ⟨12354813754388010781612579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65892340023402724168600421 12354813754388010781612579)
                  ·
                    refine ⟨18532220631582016172418869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12354813754388010781612579 18532220631582016172418869)
                    ·
                      refine ⟨1737395684210814016164269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18532220631582016172418869 1737395684210814016164269)
                      ·
                        rfl

theorem cell23_3383566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 4, 1, 5].length) (baseStart_3383566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3383566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3383566 prefixEnd_3383566 := by exact prefixLift 3383566
  have htrace : WordTrace (prefixWord ++ tailWord_3383566) baseStart_3383566 baseEnd_3383566 := by
    simpa [prefixWord, tailWord_3383566, baseEnd_3383566] using wordTrace_append hprefix tailTrace_3383566
  have hstable : (prefixWord ++ tailWord_3383566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3383566).length < 2 ^ (prefixWord ++ tailWord_3383566).sum := by decide
  have hdescent : baseEnd_3383566 < baseStart_3383566 := by decide
  rcases family_descends (prefixWord ++ tailWord_3383566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3383591 : List Nat := [1, 1, 8, 1, 1, 1, 2, 2, 2, 1, 3]
def baseStart_3383591 : Nat := 118140960795 + 3383591 * 2 ^ 59
def prefixEnd_3383591 : Nat := 4983230072969 + 3 ^ 40 * 3383591 * 2
def baseEnd_3383591 : Nat := 1737408521227176418351655

theorem tailTrace_3383591 : CollatzResearch.WordTrace tailWord_3383591 prefixEnd_3383591 1737408521227176418351655 := by
  unfold tailWord_3383591
  simp only [CollatzResearch.WordTrace]
  refine ⟨123409702284835153181222627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82273134856556768787481751 123409702284835153181222627)
  ·
    refine ⟨185114553427252729771833941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123409702284835153181222627 185114553427252729771833941)
    ·
      refine ⟨2169311172975617927013679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 185114553427252729771833941 2169311172975617927013679)
      ·
        refine ⟨3253966759463426890520519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2169311172975617927013679 3253966759463426890520519)
        ·
          refine ⟨4880950139195140335780779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3253966759463426890520519 4880950139195140335780779)
          ·
            refine ⟨7321425208792710503671169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4880950139195140335780779 7321425208792710503671169)
            ·
              refine ⟨5491068906594532877753377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7321425208792710503671169 5491068906594532877753377)
              ·
                refine ⟨4118301679945899658315033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5491068906594532877753377 4118301679945899658315033)
                ·
                  refine ⟨3088726259959424743736275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4118301679945899658315033 3088726259959424743736275)
                  ·
                    refine ⟨4633089389939137115604413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3088726259959424743736275 4633089389939137115604413)
                    ·
                      refine ⟨1737408521227176418351655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4633089389939137115604413 1737408521227176418351655)
                      ·
                        rfl

theorem cell23_3383591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_3383591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3383591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3383591 prefixEnd_3383591 := by exact prefixLift 3383591
  have htrace : WordTrace (prefixWord ++ tailWord_3383591) baseStart_3383591 baseEnd_3383591 := by
    simpa [prefixWord, tailWord_3383591, baseEnd_3383591] using wordTrace_append hprefix tailTrace_3383591
  have hstable : (prefixWord ++ tailWord_3383591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3383591).length < 2 ^ (prefixWord ++ tailWord_3383591).sum := by decide
  have hdescent : baseEnd_3383591 < baseStart_3383591 := by decide
  rcases family_descends (prefixWord ++ tailWord_3383591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3383603 : List Nat := [1, 1, 1, 2, 5, 1, 3, 4, 5]
def baseStart_3383603 : Nat := 118140960795 + 3383603 * 2 ^ 59
def prefixEnd_3383603 : Nat := 4983230072969 + 3 ^ 40 * 3383603 * 2
def baseEnd_3383603 : Nat := 193046075888336707933511

theorem tailTrace_3383603 : CollatzResearch.WordTrace tailWord_3383603 prefixEnd_3383603 193046075888336707933511 := by
  unfold tailWord_3383603
  simp only [CollatzResearch.WordTrace]
  refine ⟨123410139960791679230659463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82273426640527786153772975 123410139960791679230659463)
  ·
    refine ⟨185115209941187518845989195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123410139960791679230659463 185115209941187518845989195)
    ·
      refine ⟨277672814911781278268983793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185115209941187518845989195 277672814911781278268983793)
      ·
        refine ⟨208254611183835958701737845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 277672814911781278268983793 208254611183835958701737845)
        ·
          refine ⟨19523869798484621128287923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 208254611183835958701737845 19523869798484621128287923)
          ·
            refine ⟨29285804697726931692431885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19523869798484621128287923 29285804697726931692431885)
            ·
              refine ⟨10982176761647599384661957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29285804697726931692431885 10982176761647599384661957)
              ·
                refine ⟨2059158142808924884624117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10982176761647599384661957 2059158142808924884624117)
                ·
                  refine ⟨193046075888336707933511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2059158142808924884624117 193046075888336707933511)
                  ·
                    rfl

theorem cell23_3383603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 4, 5].length) (baseStart_3383603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3383603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3383603 prefixEnd_3383603 := by exact prefixLift 3383603
  have htrace : WordTrace (prefixWord ++ tailWord_3383603) baseStart_3383603 baseEnd_3383603 := by
    simpa [prefixWord, tailWord_3383603, baseEnd_3383603] using wordTrace_append hprefix tailTrace_3383603
  have hstable : (prefixWord ++ tailWord_3383603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3383603).length < 2 ^ (prefixWord ++ tailWord_3383603).sum := by decide
  have hdescent : baseEnd_3383603 < baseStart_3383603 := by decide
  rcases family_descends (prefixWord ++ tailWord_3383603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3383620 : List Nat := [2, 3, 4, 1, 2, 1, 1, 2, 7]
def baseStart_3383620 : Nat := 118140960795 + 3383620 * 2 ^ 59
def prefixEnd_3383620 : Nat := 4983230072969 + 3 ^ 40 * 3383620 * 2
def baseEnd_3383620 : Nat := 193047045796239644987669

theorem tailTrace_3383620 : CollatzResearch.WordTrace tailWord_3383620 prefixEnd_3383620 193047045796239644987669 := by
  unfold tailWord_3383620
  simp only [CollatzResearch.WordTrace]
  refine ⟨61705380000865045567014157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82273840001153394089352209 61705380000865045567014157)
  ·
    refine ⟨23139517500324392087630309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61705380000865045567014157 23139517500324392087630309)
    ·
      refine ⟨4338659531310823516430683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23139517500324392087630309 4338659531310823516430683)
      ·
        refine ⟨6507989296966235274646025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4338659531310823516430683 6507989296966235274646025)
        ·
          refine ⟨4880991972724676455984519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6507989296966235274646025 4880991972724676455984519)
          ·
            refine ⟨7321487959087014683976779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4880991972724676455984519 7321487959087014683976779)
            ·
              refine ⟨10982231938630522025965169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7321487959087014683976779 10982231938630522025965169)
              ·
                refine ⟨8236673953972891519473877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10982231938630522025965169 8236673953972891519473877)
                ·
                  refine ⟨193047045796239644987669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8236673953972891519473877 193047045796239644987669)
                  ·
                    rfl

theorem cell23_3383620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 2, 7].length) (baseStart_3383620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3383620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3383620 prefixEnd_3383620 := by exact prefixLift 3383620
  have htrace : WordTrace (prefixWord ++ tailWord_3383620) baseStart_3383620 baseEnd_3383620 := by
    simpa [prefixWord, tailWord_3383620, baseEnd_3383620] using wordTrace_append hprefix tailTrace_3383620
  have hstable : (prefixWord ++ tailWord_3383620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3383620).length < 2 ^ (prefixWord ++ tailWord_3383620).sum := by decide
  have hdescent : baseEnd_3383620 < baseStart_3383620 := by decide
  rcases family_descends (prefixWord ++ tailWord_3383620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3383623 : List Nat := [1, 1, 4, 1, 2, 2, 1, 2, 2, 5, 2]
def baseStart_3383623 : Nat := 118140960795 + 3383623 * 2 ^ 59
def prefixEnd_3383623 : Nat := 4983230072969 + 3 ^ 40 * 3383623 * 2
def baseEnd_3383623 : Nat := 1737424952608120293151507

theorem tailTrace_3383623 : CollatzResearch.WordTrace tailWord_3383623 prefixEnd_3383623 1737424952608120293151507 := by
  unfold tailWord_3383623
  simp only [CollatzResearch.WordTrace]
  refine ⟨123410869420719222646387523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82273912947146148430925015 123410869420719222646387523)
  ·
    refine ⟨185116304131078833969581285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123410869420719222646387523 185116304131078833969581285)
    ·
      refine ⟨34709307024577281369296491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 185116304131078833969581285 34709307024577281369296491)
      ·
        refine ⟨52063960536865922053944737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34709307024577281369296491 52063960536865922053944737)
        ·
          refine ⟨39047970402649441540458553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52063960536865922053944737 39047970402649441540458553)
          ·
            refine ⟨29285977801987081155343915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39047970402649441540458553 29285977801987081155343915)
            ·
              refine ⟨43928966702980621733015873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29285977801987081155343915 43928966702980621733015873)
              ·
                refine ⟨32946725027235466299761905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43928966702980621733015873 32946725027235466299761905)
                ·
                  refine ⟨24710043770426599724821429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32946725027235466299761905 24710043770426599724821429)
                  ·
                    refine ⟨2316566603477493724202009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24710043770426599724821429 2316566603477493724202009)
                    ·
                      refine ⟨1737424952608120293151507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2316566603477493724202009 1737424952608120293151507)
                      ·
                        rfl

theorem cell23_3383623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 2, 2, 5, 2].length) (baseStart_3383623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3383623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3383623 prefixEnd_3383623 := by exact prefixLift 3383623
  have htrace : WordTrace (prefixWord ++ tailWord_3383623) baseStart_3383623 baseEnd_3383623 := by
    simpa [prefixWord, tailWord_3383623, baseEnd_3383623] using wordTrace_append hprefix tailTrace_3383623
  have hstable : (prefixWord ++ tailWord_3383623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3383623).length < 2 ^ (prefixWord ++ tailWord_3383623).sum := by decide
  have hdescent : baseEnd_3383623 < baseStart_3383623 := by decide
  rcases family_descends (prefixWord ++ tailWord_3383623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3383633 : List Nat := [1, 2, 2, 1, 4, 2, 3, 1, 2, 5]
def baseStart_3383633 : Nat := 118140960795 + 3383633 * 2 ^ 59
def prefixEnd_3383633 : Nat := 4983230072969 + 3 ^ 40 * 3383633 * 2
def baseEnd_3383633 : Nat := 579143362471555084675487

theorem tailTrace_3383633 : CollatzResearch.WordTrace tailWord_3383633 prefixEnd_3383633 579143362471555084675487 := by
  unfold tailWord_3383633
  simp only [CollatzResearch.WordTrace]
  refine ⟨123411234150682994354251553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82274156100455329569501035 123411234150682994354251553)
  ·
    refine ⟨92558425613012245765688665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123411234150682994354251553 92558425613012245765688665)
    ·
      refine ⟨69418819209759184324266499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92558425613012245765688665 69418819209759184324266499)
      ·
        refine ⟨104128228814638776486399749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69418819209759184324266499 104128228814638776486399749)
        ·
          refine ⟨19524042902744770591199953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104128228814638776486399749 19524042902744770591199953)
          ·
            refine ⟨14643032177058577943399965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19524042902744770591199953 14643032177058577943399965)
            ·
              refine ⟨5491137066396966728774987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14643032177058577943399965 5491137066396966728774987)
              ·
                refine ⟨8236705599595450093162481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5491137066396966728774987 8236705599595450093162481)
                ·
                  refine ⟨6177529199696587569871861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8236705599595450093162481 6177529199696587569871861)
                  ·
                    refine ⟨579143362471555084675487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6177529199696587569871861 579143362471555084675487)
                    ·
                      rfl

theorem cell23_3383633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 3, 1, 2, 5].length) (baseStart_3383633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3383633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3383633 prefixEnd_3383633 := by exact prefixLift 3383633
  have htrace : WordTrace (prefixWord ++ tailWord_3383633) baseStart_3383633 baseEnd_3383633 := by
    simpa [prefixWord, tailWord_3383633, baseEnd_3383633] using wordTrace_append hprefix tailTrace_3383633
  have hstable : (prefixWord ++ tailWord_3383633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3383633).length < 2 ^ (prefixWord ++ tailWord_3383633).sum := by decide
  have hdescent : baseEnd_3383633 < baseStart_3383633 := by decide
  rcases family_descends (prefixWord ++ tailWord_3383633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3383710 : List Nat := [4, 3, 1, 2, 1, 1, 2, 1, 8]
def baseStart_3383710 : Nat := 118140960795 + 3383710 * 2 ^ 59
def prefixEnd_3383710 : Nat := 4983230072969 + 3 ^ 40 * 3383710 * 2
def baseEnd_3383710 : Nat := 193052180602784605862623

theorem tailTrace_3383710 : CollatzResearch.WordTrace tailWord_3383710 prefixEnd_3383710 193052180602784605862623 := by
  unfold tailWord_3383710
  simp only [CollatzResearch.WordTrace]
  refine ⟨15426755321425504563100573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82276028380936024336536389 15426755321425504563100573)
  ·
    refine ⟨5785033245534564211162715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15426755321425504563100573 5785033245534564211162715)
    ·
      refine ⟨8677549868301846316744073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5785033245534564211162715 8677549868301846316744073)
      ·
        refine ⟨6508162401226384737558055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8677549868301846316744073 6508162401226384737558055)
        ·
          refine ⟨9762243601839577106337083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6508162401226384737558055 9762243601839577106337083)
          ·
            refine ⟨14643365402759365659505625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9762243601839577106337083 14643365402759365659505625)
            ·
              refine ⟨10982524052069524244629219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14643365402759365659505625 10982524052069524244629219)
              ·
                refine ⟨16473786078104286366943829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10982524052069524244629219 16473786078104286366943829)
                ·
                  refine ⟨193052180602784605862623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16473786078104286366943829 193052180602784605862623)
                  ·
                    rfl

theorem cell23_3383710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 1, 8].length) (baseStart_3383710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3383710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3383710 prefixEnd_3383710 := by exact prefixLift 3383710
  have htrace : WordTrace (prefixWord ++ tailWord_3383710) baseStart_3383710 baseEnd_3383710 := by
    simpa [prefixWord, tailWord_3383710, baseEnd_3383710] using wordTrace_append hprefix tailTrace_3383710
  have hstable : (prefixWord ++ tailWord_3383710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3383710).length < 2 ^ (prefixWord ++ tailWord_3383710).sum := by decide
  have hdescent : baseEnd_3383710 < baseStart_3383710 := by decide
  rcases family_descends (prefixWord ++ tailWord_3383710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3383714 : List Nat := [3, 3, 1, 2, 1, 1, 5, 2, 1, 4]
def baseStart_3383714 : Nat := 118140960795 + 3383714 * 2 ^ 59
def prefixEnd_3383714 : Nat := 4983230072969 + 3 ^ 40 * 3383714 * 2
def baseEnd_3383714 : Nat := 579157226449226479037863

theorem tailTrace_3383714 : CollatzResearch.WordTrace tailWord_3383714 prefixEnd_3383714 579157226449226479037863 := by
  unfold tailWord_3383714
  simp only [CollatzResearch.WordTrace]
  refine ⟨30853547115847386296987549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82276125642259696791966797 30853547115847386296987549)
  ·
    refine ⟨11570080168442769861370331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30853547115847386296987549 11570080168442769861370331)
    ·
      refine ⟨17355120252664154792055497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11570080168442769861370331 17355120252664154792055497)
      ·
        refine ⟨13016340189498116094041623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17355120252664154792055497 13016340189498116094041623)
        ·
          refine ⟨19524510284247174141062435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13016340189498116094041623 19524510284247174141062435)
          ·
            refine ⟨29286765426370761211593653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19524510284247174141062435 29286765426370761211593653)
            ·
              refine ⟨2745634258722258863586905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29286765426370761211593653 2745634258722258863586905)
              ·
                refine ⟨2059225694041694147690179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2745634258722258863586905 2059225694041694147690179)
                ·
                  refine ⟨3088838541062541221535269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2059225694041694147690179 3088838541062541221535269)
                  ·
                    refine ⟨579157226449226479037863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3088838541062541221535269 579157226449226479037863)
                    ·
                      rfl

theorem cell23_3383714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 5, 2, 1, 4].length) (baseStart_3383714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3383714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3383714 prefixEnd_3383714 := by exact prefixLift 3383714
  have htrace : WordTrace (prefixWord ++ tailWord_3383714) baseStart_3383714 baseEnd_3383714 := by
    simpa [prefixWord, tailWord_3383714, baseEnd_3383714] using wordTrace_append hprefix tailTrace_3383714
  have hstable : (prefixWord ++ tailWord_3383714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3383714).length < 2 ^ (prefixWord ++ tailWord_3383714).sum := by decide
  have hdescent : baseEnd_3383714 < baseStart_3383714 := by decide
  rcases family_descends (prefixWord ++ tailWord_3383714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3383730 : List Nat := [3, 2, 1, 1, 1, 1, 3, 2, 4, 3, 2]
def baseStart_3383730 : Nat := 118140960795 + 3383730 * 2 ^ 59
def prefixEnd_3383730 : Nat := 4983230072969 + 3 ^ 40 * 3383730 * 2
def baseEnd_3383730 : Nat := 1737479895038151374513515

theorem tailTrace_3383730 : CollatzResearch.WordTrace tailWord_3383730 prefixEnd_3383730 1737479895038151374513515 := by
  unfold tailWord_3383730
  simp only [CollatzResearch.WordTrace]
  refine ⟨30853693007832894980133161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82276514687554386613688429 30853693007832894980133161)
  ·
    refine ⟨23140269755874671235099871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30853693007832894980133161 23140269755874671235099871)
    ·
      refine ⟨34710404633812006852649807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23140269755874671235099871 34710404633812006852649807)
      ·
        refine ⟨52065606950718010278974711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34710404633812006852649807 52065606950718010278974711)
        ·
          refine ⟨78098410426077015418462067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52065606950718010278974711 78098410426077015418462067)
          ·
            refine ⟨117147615639115523127693101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78098410426077015418462067 117147615639115523127693101)
            ·
              refine ⟨43930355864668321172884913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117147615639115523127693101 43930355864668321172884913)
              ·
                refine ⟨32947766898501240879663685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43930355864668321172884913 32947766898501240879663685)
                ·
                  refine ⟨6177706293468982664936941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32947766898501240879663685 6177706293468982664936941)
                  ·
                    refine ⟨2316639860050868499351353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6177706293468982664936941 2316639860050868499351353)
                    ·
                      refine ⟨1737479895038151374513515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2316639860050868499351353 1737479895038151374513515)
                      ·
                        rfl

theorem cell23_3383730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 2, 4, 3, 2].length) (baseStart_3383730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3383730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3383730 prefixEnd_3383730 := by exact prefixLift 3383730
  have htrace : WordTrace (prefixWord ++ tailWord_3383730) baseStart_3383730 baseEnd_3383730 := by
    simpa [prefixWord, tailWord_3383730, baseEnd_3383730] using wordTrace_append hprefix tailTrace_3383730
  have hstable : (prefixWord ++ tailWord_3383730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3383730).length < 2 ^ (prefixWord ++ tailWord_3383730).sum := by decide
  have hdescent : baseEnd_3383730 < baseStart_3383730 := by decide
  rcases family_descends (prefixWord ++ tailWord_3383730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3383740 : List Nat := [2, 2, 2, 4, 1, 2, 1, 1, 3, 5]
def baseStart_3383740 : Nat := 118140960795 + 3383740 * 2 ^ 59
def prefixEnd_3383740 : Nat := 4983230072969 + 3 ^ 40 * 3383740 * 2
def baseEnd_3383740 : Nat := 579161676614898778462823

theorem tailTrace_3383740 : CollatzResearch.WordTrace tailWord_3383740 prefixEnd_3383740 579161676614898778462823 := by
  unfold tailWord_3383740
  simp only [CollatzResearch.WordTrace]
  refine ⟨61707568380647675814198337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82276757840863567752264449 61707568380647675814198337)
  ·
    refine ⟨46280676285485756860648753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61707568380647675814198337 46280676285485756860648753)
    ·
      refine ⟨34710507214114317645486565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46280676285485756860648753 34710507214114317645486565)
      ·
        refine ⟨6508220102646434558528731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34710507214114317645486565 6508220102646434558528731)
        ·
          refine ⟨9762330153969651837793097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6508220102646434558528731 9762330153969651837793097)
          ·
            refine ⟨7321747615477238878344823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9762330153969651837793097 7321747615477238878344823)
            ·
              refine ⟨10982621423215858317517235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7321747615477238878344823 10982621423215858317517235)
              ·
                refine ⟨16473932134823787476275853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10982621423215858317517235 16473932134823787476275853)
                ·
                  refine ⟨6177724550558920303603445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16473932134823787476275853 6177724550558920303603445)
                  ·
                    refine ⟨579161676614898778462823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6177724550558920303603445 579161676614898778462823)
                    ·
                      rfl

theorem cell23_3383740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 1, 3, 5].length) (baseStart_3383740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3383740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3383740 prefixEnd_3383740 := by exact prefixLift 3383740
  have htrace : WordTrace (prefixWord ++ tailWord_3383740) baseStart_3383740 baseEnd_3383740 := by
    simpa [prefixWord, tailWord_3383740, baseEnd_3383740] using wordTrace_append hprefix tailTrace_3383740
  have hstable : (prefixWord ++ tailWord_3383740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3383740).length < 2 ^ (prefixWord ++ tailWord_3383740).sum := by decide
  have hdescent : baseEnd_3383740 < baseStart_3383740 := by decide
  rcases family_descends (prefixWord ++ tailWord_3383740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3383753 : List Nat := [1, 2, 1, 1, 2, 1, 4, 1, 6, 4]
def baseStart_3383753 : Nat := 118140960795 + 3383753 * 2 ^ 59
def prefixEnd_3383753 : Nat := 4983230072969 + 3 ^ 40 * 3383753 * 2
def baseEnd_3383753 : Nat := 579163901697734928175303

theorem tailTrace_3383753 : CollatzResearch.WordTrace tailWord_3383753 prefixEnd_3383753 579163901697734928175303 := by
  unfold tailWord_3383753
  simp only [CollatzResearch.WordTrace]
  refine ⟨123415610910248254848619913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82277073940165503232413275 123415610910248254848619913)
  ·
    refine ⟨92561708182686191136464935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123415610910248254848619913 92561708182686191136464935)
    ·
      refine ⟨138842562274029286704697403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92561708182686191136464935 138842562274029286704697403)
      ·
        refine ⟨208263843411043930057046105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138842562274029286704697403 208263843411043930057046105)
        ·
          refine ⟨156197882558282947542784579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208263843411043930057046105 156197882558282947542784579)
          ·
            refine ⟨234296823837424421314176869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156197882558282947542784579 234296823837424421314176869)
            ·
              refine ⟨43930654469517078996408163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 234296823837424421314176869 43930654469517078996408163)
              ·
                refine ⟨65895981704275618494612245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43930654469517078996408163 65895981704275618494612245)
                ·
                  refine ⟨3088874142387919616934949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 65895981704275618494612245 3088874142387919616934949)
                  ·
                    refine ⟨579163901697734928175303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3088874142387919616934949 579163901697734928175303)
                    ·
                      rfl

theorem cell23_3383753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 6, 4].length) (baseStart_3383753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3383753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3383753 prefixEnd_3383753 := by exact prefixLift 3383753
  have htrace : WordTrace (prefixWord ++ tailWord_3383753) baseStart_3383753 baseEnd_3383753 := by
    simpa [prefixWord, tailWord_3383753, baseEnd_3383753] using wordTrace_append hprefix tailTrace_3383753
  have hstable : (prefixWord ++ tailWord_3383753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3383753).length < 2 ^ (prefixWord ++ tailWord_3383753).sum := by decide
  have hdescent : baseEnd_3383753 < baseStart_3383753 := by decide
  rcases family_descends (prefixWord ++ tailWord_3383753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3383777 : List Nat := [1, 2, 3, 1, 2, 2, 2, 3, 3, 2, 2]
def baseStart_3383777 : Nat := 118140960795 + 3383777 * 2 ^ 59
def prefixEnd_3383777 : Nat := 4983230072969 + 3 ^ 40 * 3383777 * 2
def baseEnd_3383777 : Nat := 1737504028628912690625799

theorem tailTrace_3383777 : CollatzResearch.WordTrace tailWord_3383777 prefixEnd_3383777 1737504028628912690625799 := by
  unfold tailWord_3383777
  simp only [CollatzResearch.WordTrace]
  refine ⟨123416486262161306947493585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82277657508107537964995723 123416486262161306947493585)
  ·
    refine ⟨92562364696620980210620189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123416486262161306947493585 92562364696620980210620189)
    ·
      refine ⟨34710886761232867578982571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92562364696620980210620189 34710886761232867578982571)
      ·
        refine ⟨52066330141849301368473857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34710886761232867578982571 52066330141849301368473857)
        ·
          refine ⟨39049747606386976026355393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52066330141849301368473857 39049747606386976026355393)
          ·
            refine ⟨29287310704790232019766545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39049747606386976026355393 29287310704790232019766545)
            ·
              refine ⟨21965483028592674014824909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29287310704790232019766545 21965483028592674014824909)
              ·
                refine ⟨8237056135722252755559341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21965483028592674014824909 8237056135722252755559341)
                ·
                  refine ⟨3088896050895844783334753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8237056135722252755559341 3088896050895844783334753)
                  ·
                    refine ⟨2316672038171883587501065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3088896050895844783334753 2316672038171883587501065)
                    ·
                      refine ⟨1737504028628912690625799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2316672038171883587501065 1737504028628912690625799)
                      ·
                        rfl

theorem cell23_3383777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 3, 3, 2, 2].length) (baseStart_3383777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3383777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3383777 prefixEnd_3383777 := by exact prefixLift 3383777
  have htrace : WordTrace (prefixWord ++ tailWord_3383777) baseStart_3383777 baseEnd_3383777 := by
    simpa [prefixWord, tailWord_3383777, baseEnd_3383777] using wordTrace_append hprefix tailTrace_3383777
  have hstable : (prefixWord ++ tailWord_3383777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3383777).length < 2 ^ (prefixWord ++ tailWord_3383777).sum := by decide
  have hdescent : baseEnd_3383777 < baseStart_3383777 := by decide
  rcases family_descends (prefixWord ++ tailWord_3383777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3383790 : List Nat := [4, 1, 2, 1, 2, 2, 1, 3, 1, 2, 4]
def baseStart_3383790 : Nat := 118140960795 + 3383790 * 2 ^ 59
def prefixEnd_3383790 : Nat := 4983230072969 + 3 ^ 40 * 3383790 * 2
def baseEnd_3383790 : Nat := 1737510703877421139763239

theorem tailTrace_3383790 : CollatzResearch.WordTrace tailWord_3383790 prefixEnd_3383790 1737510703877421139763239 := by
  unfold tailWord_3383790
  simp only [CollatzResearch.WordTrace]
  refine ⟨15427120051389276270964603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82277973607409473445144549 15427120051389276270964603)
  ·
    refine ⟨23140680077083914406446905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15427120051389276270964603 23140680077083914406446905)
    ·
      refine ⟨17355510057812935804835179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23140680077083914406446905 17355510057812935804835179)
      ·
        refine ⟨26033265086719403707252769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17355510057812935804835179 26033265086719403707252769)
        ·
          refine ⟨19524948815039552780439577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26033265086719403707252769 19524948815039552780439577)
          ·
            refine ⟨14643711611279664585329683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19524948815039552780439577 14643711611279664585329683)
            ·
              refine ⟨21965567416919496877994525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14643711611279664585329683 21965567416919496877994525)
              ·
                refine ⟨8237087781344811329247947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21965567416919496877994525 8237087781344811329247947)
                ·
                  refine ⟨12355631672017216993871921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8237087781344811329247947 12355631672017216993871921)
                  ·
                    refine ⟨9266723754012912745403941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12355631672017216993871921 9266723754012912745403941)
                    ·
                      refine ⟨1737510703877421139763239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9266723754012912745403941 1737510703877421139763239)
                      ·
                        rfl

theorem cell23_3383790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 3, 1, 2, 4].length) (baseStart_3383790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3383790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3383790 prefixEnd_3383790 := by exact prefixLift 3383790
  have htrace : WordTrace (prefixWord ++ tailWord_3383790) baseStart_3383790 baseEnd_3383790 := by
    simpa [prefixWord, tailWord_3383790, baseEnd_3383790] using wordTrace_append hprefix tailTrace_3383790
  have hstable : (prefixWord ++ tailWord_3383790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3383790).length < 2 ^ (prefixWord ++ tailWord_3383790).sum := by decide
  have hdescent : baseEnd_3383790 < baseStart_3383790 := by decide
  rcases family_descends (prefixWord ++ tailWord_3383790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3383821 : List Nat := [1, 7, 1, 1, 1, 1, 3, 2, 2, 4]
def baseStart_3383821 : Nat := 118140960795 + 3383821 * 2 ^ 59
def prefixEnd_3383821 : Nat := 4983230072969 + 3 ^ 40 * 3383821 * 2
def baseEnd_3383821 : Nat := 579175540592570172825199

theorem tailTrace_3383821 : CollatzResearch.WordTrace tailWord_3383821 prefixEnd_3383821 579175540592570172825199 := by
  unfold tailWord_3383821
  simp only [CollatzResearch.WordTrace]
  refine ⟨123418091074001902462095317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82278727382667934974730211 123418091074001902462095317)
  ·
    refine ⟨2892611509546919588955359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 123418091074001902462095317 2892611509546919588955359)
    ·
      refine ⟨4338917264320379383433039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2892611509546919588955359 4338917264320379383433039)
      ·
        refine ⟨6508375896480569075149559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4338917264320379383433039 6508375896480569075149559)
        ·
          refine ⟨9762563844720853612724339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6508375896480569075149559 9762563844720853612724339)
          ·
            refine ⟨14643845767081280419086509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9762563844720853612724339 14643845767081280419086509)
            ·
              refine ⟨5491442162655480157157441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14643845767081280419086509 5491442162655480157157441)
              ·
                refine ⟨4118581621991610117868081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5491442162655480157157441 4118581621991610117868081)
                ·
                  refine ⟨3088936216493707588401061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4118581621991610117868081 3088936216493707588401061)
                  ·
                    refine ⟨579175540592570172825199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3088936216493707588401061 579175540592570172825199)
                    ·
                      rfl

theorem cell23_3383821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_3383821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3383821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3383821 prefixEnd_3383821 := by exact prefixLift 3383821
  have htrace : WordTrace (prefixWord ++ tailWord_3383821) baseStart_3383821 baseEnd_3383821 := by
    simpa [prefixWord, tailWord_3383821, baseEnd_3383821] using wordTrace_append hprefix tailTrace_3383821
  have hstable : (prefixWord ++ tailWord_3383821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3383821).length < 2 ^ (prefixWord ++ tailWord_3383821).sum := by decide
  have hdescent : baseEnd_3383821 < baseStart_3383821 := by decide
  rcases family_descends (prefixWord ++ tailWord_3383821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3383828 : List Nat := [2, 4, 3, 1, 1, 1, 2, 4, 1, 2, 2]
def baseStart_3383828 : Nat := 118140960795 + 3383828 * 2 ^ 59
def prefixEnd_3383828 : Nat := 4983230072969 + 3 ^ 40 * 3383828 * 2
def baseEnd_3383828 : Nat := 1737530216142291991088065

theorem tailTrace_3383828 : CollatzResearch.WordTrace tailWord_3383828 prefixEnd_3383828 1737530216142291991088065 := by
  unfold tailWord_3383828
  simp only [CollatzResearch.WordTrace]
  refine ⟨61709173192488271328800069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82278897589984361771733425 61709173192488271328800069)
  ·
    refine ⟨11570469973591550874150013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61709173192488271328800069 11570469973591550874150013)
    ·
      refine ⟨4338926240096831577806255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11570469973591550874150013 4338926240096831577806255)
      ·
        refine ⟨6508389360145247366709383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4338926240096831577806255 6508389360145247366709383)
        ·
          refine ⟨9762584040217871050064075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6508389360145247366709383 9762584040217871050064075)
          ·
            refine ⟨14643876060326806575096113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9762584040217871050064075 14643876060326806575096113)
            ·
              refine ⟨10982907045245104931322085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14643876060326806575096113 10982907045245104931322085)
              ·
                refine ⟨2059295070983457174622891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10982907045245104931322085 2059295070983457174622891)
                ·
                  refine ⟨3088942606475185761934337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2059295070983457174622891 3088942606475185761934337)
                  ·
                    refine ⟨2316706954856389321450753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3088942606475185761934337 2316706954856389321450753)
                    ·
                      refine ⟨1737530216142291991088065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2316706954856389321450753 1737530216142291991088065)
                      ·
                        rfl

theorem cell23_3383828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 4, 1, 2, 2].length) (baseStart_3383828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3383828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3383828 prefixEnd_3383828 := by exact prefixLift 3383828
  have htrace : WordTrace (prefixWord ++ tailWord_3383828) baseStart_3383828 baseEnd_3383828 := by
    simpa [prefixWord, tailWord_3383828, baseEnd_3383828] using wordTrace_append hprefix tailTrace_3383828
  have hstable : (prefixWord ++ tailWord_3383828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3383828).length < 2 ^ (prefixWord ++ tailWord_3383828).sum := by decide
  have hdescent : baseEnd_3383828 < baseStart_3383828 := by decide
  rcases family_descends (prefixWord ++ tailWord_3383828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3383884 : List Nat := [2, 2, 1, 3, 1, 2, 2, 4, 2, 2, 2]
def baseStart_3383884 : Nat := 118140960795 + 3383884 * 2 ^ 59
def prefixEnd_3383884 : Nat := 4983230072969 + 3 ^ 40 * 3383884 * 2
def baseEnd_3383884 : Nat := 1737558971058943771987807

theorem tailTrace_3383884 : CollatzResearch.WordTrace tailWord_3383884 prefixEnd_3383884 1737558971058943771987807 := by
  unfold tailWord_3383884
  simp only [CollatzResearch.WordTrace]
  refine ⟨61710194436386832110819353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82280259248515776147759137 61710194436386832110819353)
  ·
    refine ⟨46282645827290124083114515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61710194436386832110819353 46282645827290124083114515)
    ·
      refine ⟨69423968740935186124671773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46282645827290124083114515 69423968740935186124671773)
      ·
        refine ⟨26033988277850694796751915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69423968740935186124671773 26033988277850694796751915)
        ·
          refine ⟨39050982416776042195127873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26033988277850694796751915 39050982416776042195127873)
          ·
            refine ⟨29288236812582031646345905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39050982416776042195127873 29288236812582031646345905)
            ·
              refine ⟨21966177609436523734759429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29288236812582031646345905 21966177609436523734759429)
              ·
                refine ⟨4118658301769348200267393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21966177609436523734759429 4118658301769348200267393)
                ·
                  refine ⟨3088993726327011150200545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4118658301769348200267393 3088993726327011150200545)
                  ·
                    refine ⟨2316745294745258362650409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3088993726327011150200545 2316745294745258362650409)
                    ·
                      refine ⟨1737558971058943771987807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2316745294745258362650409 1737558971058943771987807)
                      ·
                        rfl

theorem cell23_3383884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 4, 2, 2, 2].length) (baseStart_3383884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3383884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3383884 prefixEnd_3383884 := by exact prefixLift 3383884
  have htrace : WordTrace (prefixWord ++ tailWord_3383884) baseStart_3383884 baseEnd_3383884 := by
    simpa [prefixWord, tailWord_3383884, baseEnd_3383884] using wordTrace_append hprefix tailTrace_3383884
  have hstable : (prefixWord ++ tailWord_3383884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3383884).length < 2 ^ (prefixWord ++ tailWord_3383884).sum := by decide
  have hdescent : baseEnd_3383884 < baseStart_3383884 := by decide
  rcases family_descends (prefixWord ++ tailWord_3383884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3383903 : List Nat := [1, 1, 2, 3, 1, 1, 1, 3, 3, 7]
def baseStart_3383903 : Nat := 118140960795 + 3383903 * 2 ^ 59
def prefixEnd_3383903 : Nat := 4983230072969 + 3 ^ 40 * 3383903 * 2
def baseEnd_3383903 : Nat := 579189575730459732550073

theorem tailTrace_3383903 : CollatzResearch.WordTrace tailWord_3383903 prefixEnd_3383903 579189575730459732550073 := by
  unfold tailWord_3383903
  simp only [CollatzResearch.WordTrace]
  refine ⟨123421081859704830466580363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82280721239803220311053575 123421081859704830466580363)
  ·
    refine ⟨185131622789557245699870545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123421081859704830466580363 185131622789557245699870545)
    ·
      refine ⟨138848717092167934274902909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185131622789557245699870545 138848717092167934274902909)
      ·
        refine ⟨52068268909562975353088591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138848717092167934274902909 52068268909562975353088591)
        ·
          refine ⟨78102403364344463029632887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52068268909562975353088591 78102403364344463029632887)
          ·
            refine ⟨117153605046516694544449331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78102403364344463029632887 117153605046516694544449331)
            ·
              refine ⟨175730407569775041816673997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117153605046516694544449331 175730407569775041816673997)
              ·
                refine ⟨65898902838665640681252749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 175730407569775041816673997 65898902838665640681252749)
                ·
                  refine ⟨24712088564499615255469781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65898902838665640681252749 24712088564499615255469781)
                  ·
                    refine ⟨579189575730459732550073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24712088564499615255469781 579189575730459732550073)
                    ·
                      rfl

theorem cell23_3383903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 3, 7].length) (baseStart_3383903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3383903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3383903 prefixEnd_3383903 := by exact prefixLift 3383903
  have htrace : WordTrace (prefixWord ++ tailWord_3383903) baseStart_3383903 baseEnd_3383903 := by
    simpa [prefixWord, tailWord_3383903, baseEnd_3383903] using wordTrace_append hprefix tailTrace_3383903
  have hstable : (prefixWord ++ tailWord_3383903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3383903).length < 2 ^ (prefixWord ++ tailWord_3383903).sum := by decide
  have hdescent : baseEnd_3383903 < baseStart_3383903 := by decide
  rcases family_descends (prefixWord ++ tailWord_3383903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3383913 : List Nat := [1, 2, 1, 1, 1, 4, 1, 1, 3, 1, 7]
def baseStart_3383913 : Nat := 118140960795 + 3383913 * 2 ^ 59
def prefixEnd_3383913 : Nat := 4983230072969 + 3 ^ 40 * 3383913 * 2
def baseEnd_3383913 : Nat := 1737573861997924158525173

theorem tailTrace_3383913 : CollatzResearch.WordTrace tailWord_3383913 prefixEnd_3383913 1737573861997924158525173 := by
  unfold tailWord_3383913
  simp only [CollatzResearch.WordTrace]
  refine ⟨123421446589668602174444393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82280964393112401449629595 123421446589668602174444393)
  ·
    refine ⟨92566084942251451630833295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123421446589668602174444393 92566084942251451630833295)
    ·
      refine ⟨138849127413377177446249943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92566084942251451630833295 138849127413377177446249943)
      ·
        refine ⟨208273691120065766169374915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138849127413377177446249943 208273691120065766169374915)
        ·
          refine ⟨312410536680098649254062373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208273691120065766169374915 312410536680098649254062373)
          ·
            refine ⟨58576975627518496735136695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 312410536680098649254062373 58576975627518496735136695)
            ·
              refine ⟨87865463441277745102705043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58576975627518496735136695 87865463441277745102705043)
              ·
                refine ⟨131798195161916617654057565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87865463441277745102705043 131798195161916617654057565)
                ·
                  refine ⟨49424323185718731620271587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 131798195161916617654057565 49424323185718731620271587)
                  ·
                    refine ⟨74136484778578097430407381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49424323185718731620271587 74136484778578097430407381)
                    ·
                      refine ⟨1737573861997924158525173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 74136484778578097430407381 1737573861997924158525173)
                      ·
                        rfl

theorem cell23_3383913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 3, 1, 7].length) (baseStart_3383913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3383913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3383913 prefixEnd_3383913 := by exact prefixLift 3383913
  have htrace : WordTrace (prefixWord ++ tailWord_3383913) baseStart_3383913 baseEnd_3383913 := by
    simpa [prefixWord, tailWord_3383913, baseEnd_3383913] using wordTrace_append hprefix tailTrace_3383913
  have hstable : (prefixWord ++ tailWord_3383913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3383913).length < 2 ^ (prefixWord ++ tailWord_3383913).sum := by decide
  have hdescent : baseEnd_3383913 < baseStart_3383913 := by decide
  rcases family_descends (prefixWord ++ tailWord_3383913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3383997 : List Nat := [1, 4, 1, 2, 1, 3, 3, 2, 6]
def baseStart_3383997 : Nat := 118140960795 + 3383997 * 2 ^ 59
def prefixEnd_3383997 : Nat := 4983230072969 + 3 ^ 40 * 3383997 * 2
def baseEnd_3383997 : Nat := 193068554930322425541643

theorem tailTrace_3383997 : CollatzResearch.WordTrace tailWord_3383997 prefixEnd_3383997 193068554930322425541643 := by
  unfold tailWord_3383997
  simp only [CollatzResearch.WordTrace]
  refine ⟨123424510321364284520502245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82283006880909523013668163 123424510321364284520502245)
  ·
    refine ⟨23142095685255803347594171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123424510321364284520502245 23142095685255803347594171)
    ·
      refine ⟨34713143527883705021391257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23142095685255803347594171 34713143527883705021391257)
      ·
        refine ⟨26034857645912778766043443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34713143527883705021391257 26034857645912778766043443)
        ·
          refine ⟨39052286468869168149065165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26034857645912778766043443 39052286468869168149065165)
          ·
            refine ⟨14644607425825938055899437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39052286468869168149065165 14644607425825938055899437)
            ·
              refine ⟨5491727784684726770962289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14644607425825938055899437 5491727784684726770962289)
              ·
                refine ⟨4118795838513545078221717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5491727784684726770962289 4118795838513545078221717)
                ·
                  refine ⟨193068554930322425541643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4118795838513545078221717 193068554930322425541643)
                  ·
                    rfl

theorem cell23_3383997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 3, 2, 6].length) (baseStart_3383997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3383997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3383997 prefixEnd_3383997 := by exact prefixLift 3383997
  have htrace : WordTrace (prefixWord ++ tailWord_3383997) baseStart_3383997 baseEnd_3383997 := by
    simpa [prefixWord, tailWord_3383997, baseEnd_3383997] using wordTrace_append hprefix tailTrace_3383997
  have hstable : (prefixWord ++ tailWord_3383997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3383997).length < 2 ^ (prefixWord ++ tailWord_3383997).sum := by decide
  have hdescent : baseEnd_3383997 < baseStart_3383997 := by decide
  rcases family_descends (prefixWord ++ tailWord_3383997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3384000 : List Nat := [2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 6]
def baseStart_3384000 : Nat := 118140960795 + 3384000 * 2 ^ 59
def prefixEnd_3384000 : Nat := 4983230072969 + 3 ^ 40 * 3384000 * 2
def baseEnd_3384000 : Nat := 1737618534814865318137273

theorem tailTrace_3384000 : CollatzResearch.WordTrace tailWord_3384000 prefixEnd_3384000 1737618534814865318137273 := by
  unfold tailWord_3384000
  simp only [CollatzResearch.WordTrace]
  refine ⟨61712309870176708016430727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82283079826902277355240969 61712309870176708016430727)
  ·
    refine ⟨92568464805265062024646091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61712309870176708016430727 92568464805265062024646091)
    ·
      refine ⟨138852697207897593036969137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92568464805265062024646091 138852697207897593036969137)
      ·
        refine ⟨104139522905923194777726853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138852697207897593036969137 104139522905923194777726853)
        ·
          refine ⟨19526160544860599020823785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104139522905923194777726853 19526160544860599020823785)
          ·
            refine ⟨14644620408645449265617839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19526160544860599020823785 14644620408645449265617839)
            ·
              refine ⟨21966930612968173898426759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14644620408645449265617839 21966930612968173898426759)
              ·
                refine ⟨32950395919452260847640139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21966930612968173898426759 32950395919452260847640139)
                ·
                  refine ⟨49425593879178391271460209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32950395919452260847640139 49425593879178391271460209)
                  ·
                    refine ⟨37069195409383793453595157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49425593879178391271460209 37069195409383793453595157)
                    ·
                      refine ⟨1737618534814865318137273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37069195409383793453595157 1737618534814865318137273)
                      ·
                        rfl

theorem cell23_3384000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 6].length) (baseStart_3384000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3384000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3384000 prefixEnd_3384000 := by exact prefixLift 3384000
  have htrace : WordTrace (prefixWord ++ tailWord_3384000) baseStart_3384000 baseEnd_3384000 := by
    simpa [prefixWord, tailWord_3384000, baseEnd_3384000] using wordTrace_append hprefix tailTrace_3384000
  have hstable : (prefixWord ++ tailWord_3384000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3384000).length < 2 ^ (prefixWord ++ tailWord_3384000).sum := by decide
  have hdescent : baseEnd_3384000 < baseStart_3384000 := by decide
  rcases family_descends (prefixWord ++ tailWord_3384000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3384014 : List Nat := [4, 1, 1, 1, 3, 3, 3, 1, 6]
def baseStart_3384014 : Nat := 118140960795 + 3384014 * 2 ^ 59
def prefixEnd_3384014 : Nat := 4983230072969 + 3 ^ 40 * 3384014 * 2
def baseEnd_3384014 : Nat := 193069524838225362595801

theorem tailTrace_3384014 : CollatzResearch.WordTrace tailWord_3384014 prefixEnd_3384014 193069524838225362595801 := by
  unfold tailWord_3384014
  simp only [CollatzResearch.WordTrace]
  refine ⟨15428141295287837052983887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82283420241535130949247397 15428141295287837052983887)
  ·
    refine ⟨23142211942931755579475831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15428141295287837052983887 23142211942931755579475831)
    ·
      refine ⟨34713317914397633369213747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23142211942931755579475831 34713317914397633369213747)
      ·
        refine ⟨52069976871596450053820621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34713317914397633369213747 52069976871596450053820621)
        ·
          refine ⟨19526241326848668770182733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52069976871596450053820621 19526241326848668770182733)
          ·
            refine ⟨7322340497568250788818525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19526241326848668770182733 7322340497568250788818525)
            ·
              refine ⟨2745877686588094045806947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7322340497568250788818525 2745877686588094045806947)
              ·
                refine ⟨4118816529882141068710421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2745877686588094045806947 4118816529882141068710421)
                ·
                  refine ⟨193069524838225362595801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4118816529882141068710421 193069524838225362595801)
                  ·
                    rfl

theorem cell23_3384014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 3, 1, 6].length) (baseStart_3384014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3384014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3384014 prefixEnd_3384014 := by exact prefixLift 3384014
  have htrace : WordTrace (prefixWord ++ tailWord_3384014) baseStart_3384014 baseEnd_3384014 := by
    simpa [prefixWord, tailWord_3384014, baseEnd_3384014] using wordTrace_append hprefix tailTrace_3384014
  have hstable : (prefixWord ++ tailWord_3384014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3384014).length < 2 ^ (prefixWord ++ tailWord_3384014).sum := by decide
  have hdescent : baseEnd_3384014 < baseStart_3384014 := by decide
  rcases family_descends (prefixWord ++ tailWord_3384014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3384017 : List Nat := [1, 2, 2, 1, 2, 3, 1, 1, 3, 5, 2]
def baseStart_3384017 : Nat := 118140960795 + 3384017 * 2 ^ 59
def prefixEnd_3384017 : Nat := 4983230072969 + 3 ^ 40 * 3384017 * 2
def baseEnd_3384017 : Nat := 1737627263985991751624695

theorem tailTrace_3384017 : CollatzResearch.WordTrace tailWord_3384017 prefixEnd_3384017 1737627263985991751624695 := by
  unfold tailWord_3384017
  simp only [CollatzResearch.WordTrace]
  refine ⟨123425239781291827936230305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82283493187527885290820203 123425239781291827936230305)
  ·
    refine ⟨92568929835968870952172729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123425239781291827936230305 92568929835968870952172729)
    ·
      refine ⟨69426697376976653214129547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92568929835968870952172729 69426697376976653214129547)
      ·
        refine ⟨104140046065464979821194321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69426697376976653214129547 104140046065464979821194321)
        ·
          refine ⟨78105034549098734865895741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104140046065464979821194321 78105034549098734865895741)
          ·
            refine ⟨29289387955912025574710903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78105034549098734865895741 29289387955912025574710903)
            ·
              refine ⟨43934081933868038362066355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29289387955912025574710903 43934081933868038362066355)
              ·
                refine ⟨65901122900802057543099533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43934081933868038362066355 65901122900802057543099533)
                ·
                  refine ⟨24712921087800771578662325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65901122900802057543099533 24712921087800771578662325)
                  ·
                    refine ⟨2316836351981322335499593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24712921087800771578662325 2316836351981322335499593)
                    ·
                      refine ⟨1737627263985991751624695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2316836351981322335499593 1737627263985991751624695)
                      ·
                        rfl

theorem cell23_3384017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 3, 5, 2].length) (baseStart_3384017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3384017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3384017 prefixEnd_3384017 := by exact prefixLift 3384017
  have htrace : WordTrace (prefixWord ++ tailWord_3384017) baseStart_3384017 baseEnd_3384017 := by
    simpa [prefixWord, tailWord_3384017, baseEnd_3384017] using wordTrace_append hprefix tailTrace_3384017
  have hstable : (prefixWord ++ tailWord_3384017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3384017).length < 2 ^ (prefixWord ++ tailWord_3384017).sum := by decide
  have hdescent : baseEnd_3384017 < baseStart_3384017 := by decide
  rcases family_descends (prefixWord ++ tailWord_3384017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3384024 : List Nat := [2, 1, 2, 2, 3, 2, 2, 2, 3, 1, 3]
def baseStart_3384024 : Nat := 118140960795 + 3384024 * 2 ^ 59
def prefixEnd_3384024 : Nat := 4983230072969 + 3 ^ 40 * 3384024 * 2
def baseEnd_3384024 : Nat := 1737630858350573224237163

theorem tailTrace_3384024 : CollatzResearch.WordTrace tailWord_3384024 prefixEnd_3384024 1737630858350573224237163 := by
  unfold tailWord_3384024
  simp only [CollatzResearch.WordTrace]
  refine ⟨61712747546133234065867563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82283663394844312087823417 61712747546133234065867563)
  ·
    refine ⟨92569121319199851098801345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61712747546133234065867563 92569121319199851098801345)
    ·
      refine ⟨69426840989399888324101009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92569121319199851098801345 69426840989399888324101009)
      ·
        refine ⟨52070130742049916243075757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69426840989399888324101009 52070130742049916243075757)
        ·
          refine ⟨19526299028268718591153409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52070130742049916243075757 19526299028268718591153409)
          ·
            refine ⟨14644724271201538943365057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19526299028268718591153409 14644724271201538943365057)
            ·
              refine ⟨10983543203401154207523793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14644724271201538943365057 10983543203401154207523793)
              ·
                refine ⟨8237657402550865655642845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10983543203401154207523793 8237657402550865655642845)
                ·
                  refine ⟨3089121525956574620866067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8237657402550865655642845 3089121525956574620866067)
                  ·
                    refine ⟨4633682288934861931299101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3089121525956574620866067 4633682288934861931299101)
                    ·
                      refine ⟨1737630858350573224237163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4633682288934861931299101 1737630858350573224237163)
                      ·
                        rfl

theorem cell23_3384024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 2, 3, 1, 3].length) (baseStart_3384024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3384024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3384024 prefixEnd_3384024 := by exact prefixLift 3384024
  have htrace : WordTrace (prefixWord ++ tailWord_3384024) baseStart_3384024 baseEnd_3384024 := by
    simpa [prefixWord, tailWord_3384024, baseEnd_3384024] using wordTrace_append hprefix tailTrace_3384024
  have hstable : (prefixWord ++ tailWord_3384024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3384024).length < 2 ^ (prefixWord ++ tailWord_3384024).sum := by decide
  have hdescent : baseEnd_3384024 < baseStart_3384024 := by decide
  rcases family_descends (prefixWord ++ tailWord_3384024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3384041 : List Nat := [1, 2, 1, 1, 1, 2, 7, 3, 1, 1, 3]
def baseStart_3384041 : Nat := 118140960795 + 3384041 * 2 ^ 59
def prefixEnd_3384041 : Nat := 4983230072969 + 3 ^ 40 * 3384041 * 2
def baseEnd_3384041 : Nat := 1737639587521699657724585

theorem tailTrace_3384041 : CollatzResearch.WordTrace tailWord_3384041 prefixEnd_3384041 1737639587521699657724585 := by
  unfold tailWord_3384041
  simp only [CollatzResearch.WordTrace]
  refine ⟨123426115133204880035103977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82284076755469920023402651 123426115133204880035103977)
  ·
    refine ⟨92569586349903660026327983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123426115133204880035103977 92569586349903660026327983)
    ·
      refine ⟨138854379524855490039491975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92569586349903660026327983 138854379524855490039491975)
      ·
        refine ⟨208281569287283235059237963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138854379524855490039491975 208281569287283235059237963)
        ·
          refine ⟨312422353930924852588856945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208281569287283235059237963 312422353930924852588856945)
          ·
            refine ⟨234316765448193639441642709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 312422353930924852588856945 234316765448193639441642709)
            ·
              refine ⟨5491799190192038424413501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 234316765448193639441642709 5491799190192038424413501)
              ·
                refine ⟨2059424696322014409155063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5491799190192038424413501 2059424696322014409155063)
                ·
                  refine ⟨3089137044483021613732595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2059424696322014409155063 3089137044483021613732595)
                  ·
                    refine ⟨4633705566724532420598893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3089137044483021613732595 4633705566724532420598893)
                    ·
                      refine ⟨1737639587521699657724585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4633705566724532420598893 1737639587521699657724585)
                      ·
                        rfl

theorem cell23_3384041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 7, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 7, 3, 1, 1, 3].length) (baseStart_3384041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3384041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3384041 prefixEnd_3384041 := by exact prefixLift 3384041
  have htrace : WordTrace (prefixWord ++ tailWord_3384041) baseStart_3384041 baseEnd_3384041 := by
    simpa [prefixWord, tailWord_3384041, baseEnd_3384041] using wordTrace_append hprefix tailTrace_3384041
  have hstable : (prefixWord ++ tailWord_3384041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3384041).length < 2 ^ (prefixWord ++ tailWord_3384041).sum := by decide
  have hdescent : baseEnd_3384041 < baseStart_3384041 := by decide
  rcases family_descends (prefixWord ++ tailWord_3384041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3384052 : List Nat := [2, 6, 1, 1, 2, 1, 3, 2, 1, 4]
def baseStart_3384052 : Nat := 118140960795 + 3384052 * 2 ^ 59
def prefixEnd_3384052 : Nat := 4983230072969 + 3 ^ 40 * 3384052 * 2
def baseEnd_3384052 : Nat := 579215078602966371562345

theorem tailTrace_3384052 : CollatzResearch.WordTrace tailWord_3384052 prefixEnd_3384052 579215078602966371562345 := by
  unfold tailWord_3384052
  simp only [CollatzResearch.WordTrace]
  refine ⟨61713258168082514456877205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82284344224110019275836273 61713258168082514456877205)
  ·
    refine ⟨2892808976628867865166119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 61713258168082514456877205 2892808976628867865166119)
    ·
      refine ⟨4339213464943301797749179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2892808976628867865166119 4339213464943301797749179)
      ·
        refine ⟨6508820197414952696623769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4339213464943301797749179 6508820197414952696623769)
        ·
          refine ⟨4881615148061214522467827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6508820197414952696623769 4881615148061214522467827)
          ·
            refine ⟨7322422722091821783701741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4881615148061214522467827 7322422722091821783701741)
            ·
              refine ⟨2745908520784433168888153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7322422722091821783701741 2745908520784433168888153)
              ·
                refine ⟨2059431390588324876666115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2745908520784433168888153 2059431390588324876666115)
                ·
                  refine ⟨3089147085882487314999173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2059431390588324876666115 3089147085882487314999173)
                  ·
                    refine ⟨579215078602966371562345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3089147085882487314999173 579215078602966371562345)
                    ·
                      rfl

theorem cell23_3384052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_3384052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3384052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3384052 prefixEnd_3384052 := by exact prefixLift 3384052
  have htrace : WordTrace (prefixWord ++ tailWord_3384052) baseStart_3384052 baseEnd_3384052 := by
    simpa [prefixWord, tailWord_3384052, baseEnd_3384052] using wordTrace_append hprefix tailTrace_3384052
  have hstable : (prefixWord ++ tailWord_3384052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3384052).length < 2 ^ (prefixWord ++ tailWord_3384052).sum := by decide
  have hdescent : baseEnd_3384052 < baseStart_3384052 := by decide
  rcases family_descends (prefixWord ++ tailWord_3384052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3384067 : List Nat := [1, 1, 1, 3, 2, 2, 1, 4, 3, 2, 3]
def baseStart_3384067 : Nat := 118140960795 + 3384067 * 2 ^ 59
def prefixEnd_3384067 : Nat := 4983230072969 + 3 ^ 40 * 3384067 * 2
def baseEnd_3384067 : Nat := 1737652938018716555999465

theorem tailTrace_3384067 : CollatzResearch.WordTrace tailWord_3384067 prefixEnd_3384067 1737652938018716555999465 := by
  unfold tailWord_3384067
  simp only [CollatzResearch.WordTrace]
  refine ⟨123427063431110686475550455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82284708954073790983700303 123427063431110686475550455)
  ·
    refine ⟨185140595146666029713325683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123427063431110686475550455 185140595146666029713325683)
    ·
      refine ⟨277710892719999044569988525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185140595146666029713325683 277710892719999044569988525)
      ·
        refine ⟨104141584769999641713745697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 277710892719999044569988525 104141584769999641713745697)
        ·
          refine ⟨78106188577499731285309273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104141584769999641713745697 78106188577499731285309273)
          ·
            refine ⟨58579641433124798463981955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78106188577499731285309273 58579641433124798463981955)
            ·
              refine ⟨87869462149687197695972933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58579641433124798463981955 87869462149687197695972933)
              ·
                refine ⟨16475524153066349567994925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87869462149687197695972933 16475524153066349567994925)
                ·
                  refine ⟨6178321557399881087998097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16475524153066349567994925 6178321557399881087998097)
                  ·
                    refine ⟨4633741168049910815998573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6178321557399881087998097 4633741168049910815998573)
                    ·
                      refine ⟨1737652938018716555999465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4633741168049910815998573 1737652938018716555999465)
                      ·
                        rfl

theorem cell23_3384067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 4, 3, 2, 3].length) (baseStart_3384067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3384067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3384067 prefixEnd_3384067 := by exact prefixLift 3384067
  have htrace : WordTrace (prefixWord ++ tailWord_3384067) baseStart_3384067 baseEnd_3384067 := by
    simpa [prefixWord, tailWord_3384067, baseEnd_3384067] using wordTrace_append hprefix tailTrace_3384067
  have hstable : (prefixWord ++ tailWord_3384067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3384067).length < 2 ^ (prefixWord ++ tailWord_3384067).sum := by decide
  have hdescent : baseEnd_3384067 < baseStart_3384067 := by decide
  rcases family_descends (prefixWord ++ tailWord_3384067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3384074 : List Nat := [3, 1, 2, 2, 1, 2, 3, 3, 2, 4]
def baseStart_3384074 : Nat := 118140960795 + 3384074 * 2 ^ 59
def prefixEnd_3384074 : Nat := 4983230072969 + 3 ^ 40 * 3384074 * 2
def baseEnd_3384074 : Nat := 579218844127766009537311

theorem tailTrace_3384074 : CollatzResearch.WordTrace tailWord_3384074 prefixEnd_3384074 579218844127766009537311 := by
  unfold tailWord_3384074
  simp only [CollatzResearch.WordTrace]
  refine ⟨30856829685521331667763819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82284879161390217780703517 30856829685521331667763819)
  ·
    refine ⟨46285244528281997501645729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30856829685521331667763819 46285244528281997501645729)
    ·
      refine ⟨34713933396211498126234297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46285244528281997501645729 34713933396211498126234297)
      ·
        refine ⟨26035450047158623594675723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34713933396211498126234297 26035450047158623594675723)
        ·
          refine ⟨39053175070737935392013585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26035450047158623594675723 39053175070737935392013585)
          ·
            refine ⟨29289881303053451544010189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39053175070737935392013585 29289881303053451544010189)
            ·
              refine ⟨10983705488645044329003821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29289881303053451544010189 10983705488645044329003821)
              ·
                refine ⟨4118889558241891623376433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10983705488645044329003821 4118889558241891623376433)
                ·
                  refine ⟨3089167168681418717532325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4118889558241891623376433 3089167168681418717532325)
                  ·
                    refine ⟨579218844127766009537311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3089167168681418717532325 579218844127766009537311)
                    ·
                      rfl

theorem cell23_3384074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 3, 2, 4].length) (baseStart_3384074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3384074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3384074 prefixEnd_3384074 := by exact prefixLift 3384074
  have htrace : WordTrace (prefixWord ++ tailWord_3384074) baseStart_3384074 baseEnd_3384074 := by
    simpa [prefixWord, tailWord_3384074, baseEnd_3384074] using wordTrace_append hprefix tailTrace_3384074
  have hstable : (prefixWord ++ tailWord_3384074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3384074).length < 2 ^ (prefixWord ++ tailWord_3384074).sum := by decide
  have hdescent : baseEnd_3384074 < baseStart_3384074 := by decide
  rcases family_descends (prefixWord ++ tailWord_3384074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3384101 : List Nat := [1, 3, 1, 2, 3, 1, 5, 1, 1, 2, 3]
def baseStart_3384101 : Nat := 118140960795 + 3384101 * 2 ^ 59
def prefixEnd_3384101 : Nat := 4983230072969 + 3 ^ 40 * 3384101 * 2
def baseEnd_3384101 : Nat := 1737670396360969422974309

theorem tailTrace_3384101 : CollatzResearch.WordTrace tailWord_3384101 prefixEnd_3384101 1737670396360969422974309 := by
  unfold tailWord_3384101
  simp only [CollatzResearch.WordTrace]
  refine ⟨123428303512987510282288157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82285535675325006854858771 123428303512987510282288157)
  ·
    refine ⟨46285613817370316355858059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123428303512987510282288157 46285613817370316355858059)
    ·
      refine ⟨69428420726055474533787089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46285613817370316355858059 69428420726055474533787089)
      ·
        refine ⟨52071315544541605900340317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69428420726055474533787089 52071315544541605900340317)
        ·
          refine ⟨19526743329203102212627619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52071315544541605900340317 19526743329203102212627619)
          ·
            refine ⟨29290114993804653318941429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19526743329203102212627619 29290114993804653318941429)
            ·
              refine ⟨2745948280669186248650759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29290114993804653318941429 2745948280669186248650759)
              ·
                refine ⟨4118922421003779372976139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2745948280669186248650759 4118922421003779372976139)
                ·
                  refine ⟨6178383631505669059464209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4118922421003779372976139 6178383631505669059464209)
                  ·
                    refine ⟨4633787723629251794598157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6178383631505669059464209 4633787723629251794598157)
                    ·
                      refine ⟨1737670396360969422974309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4633787723629251794598157 1737670396360969422974309)
                      ·
                        rfl

theorem cell23_3384101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 5, 1, 1, 2, 3].length) (baseStart_3384101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3384101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3384101 prefixEnd_3384101 := by exact prefixLift 3384101
  have htrace : WordTrace (prefixWord ++ tailWord_3384101) baseStart_3384101 baseEnd_3384101 := by
    simpa [prefixWord, tailWord_3384101, baseEnd_3384101] using wordTrace_append hprefix tailTrace_3384101
  have hstable : (prefixWord ++ tailWord_3384101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3384101).length < 2 ^ (prefixWord ++ tailWord_3384101).sum := by decide
  have hdescent : baseEnd_3384101 < baseStart_3384101 := by decide
  rcases family_descends (prefixWord ++ tailWord_3384101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3384109 : List Nat := [1, 5, 3, 2, 1, 2, 2, 2, 1, 1, 3]
def baseStart_3384109 : Nat := 118140960795 + 3384109 * 2 ^ 59
def prefixEnd_3384109 : Nat := 4983230072969 + 3 ^ 40 * 3384109 * 2
def baseEnd_3384109 : Nat := 1737674504206205391674273

theorem tailTrace_3384109 : CollatzResearch.WordTrace tailWord_3384109 prefixEnd_3384109 1737674504206205391674273 := by
  unfold tailWord_3384109
  simp only [CollatzResearch.WordTrace]
  refine ⟨123428595296958527648579381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82285730197972351765719587 123428595296958527648579381)
  ·
    refine ⟨11571430809089861967054317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 123428595296958527648579381 11571430809089861967054317)
    ·
      refine ⟨4339286553408698237645369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11571430809089861967054317 4339286553408698237645369)
      ·
        refine ⟨3254464915056523678234027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4339286553408698237645369 3254464915056523678234027)
        ·
          refine ⟨4881697372584785517351041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3254464915056523678234027 4881697372584785517351041)
          ·
            refine ⟨3661273029438589138013281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4881697372584785517351041 3661273029438589138013281)
            ·
              refine ⟨2745954772078941853509961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3661273029438589138013281 2745954772078941853509961)
              ·
                refine ⟨2059466079059206390132471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2745954772078941853509961 2059466079059206390132471)
                ·
                  refine ⟨3089199118588809585198707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2059466079059206390132471 3089199118588809585198707)
                  ·
                    refine ⟨4633798677883214377798061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3089199118588809585198707 4633798677883214377798061)
                    ·
                      refine ⟨1737674504206205391674273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4633798677883214377798061 1737674504206205391674273)
                      ·
                        rfl

theorem cell23_3384109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_3384109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3384109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3384109 prefixEnd_3384109 := by exact prefixLift 3384109
  have htrace : WordTrace (prefixWord ++ tailWord_3384109) baseStart_3384109 baseEnd_3384109 := by
    simpa [prefixWord, tailWord_3384109, baseEnd_3384109] using wordTrace_append hprefix tailTrace_3384109
  have hstable : (prefixWord ++ tailWord_3384109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3384109).length < 2 ^ (prefixWord ++ tailWord_3384109).sum := by decide
  have hdescent : baseEnd_3384109 < baseStart_3384109 := by decide
  rcases family_descends (prefixWord ++ tailWord_3384109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3384115 : List Nat := [1, 1, 1, 2, 6, 1, 4, 2, 1, 2, 2]
def baseStart_3384115 : Nat := 118140960795 + 3384115 * 2 ^ 59
def prefixEnd_3384115 : Nat := 4983230072969 + 3 ^ 40 * 3384115 * 2
def baseEnd_3384115 : Nat := 1737677585090132368199245

theorem tailTrace_3384115 : CollatzResearch.WordTrace tailWord_3384115 prefixEnd_3384115 1737677585090132368199245 := by
  unfold tailWord_3384115
  simp only [CollatzResearch.WordTrace]
  refine ⟨123428814134936790673297799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82285876089957860448865199 123428814134936790673297799)
  ·
    refine ⟨185143221202405186009946699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123428814134936790673297799 185143221202405186009946699)
    ·
      refine ⟨277714831803607779014920049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185143221202405186009946699 277714831803607779014920049)
      ·
        refine ⟨208286123852705834261190037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 277714831803607779014920049 208286123852705834261190037)
        ·
          refine ⟨9763412055595585980993283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 208286123852705834261190037 9763412055595585980993283)
          ·
            refine ⟨14645118083393378971489925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9763412055595585980993283 14645118083393378971489925)
            ·
              refine ⟨2745959640636258557154361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14645118083393378971489925 2745959640636258557154361)
              ·
                refine ⟨2059469730477193917865771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2745959640636258557154361 2059469730477193917865771)
                ·
                  refine ⟨3089204595715790876798657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2059469730477193917865771 3089204595715790876798657)
                  ·
                    refine ⟨2316903446786843157598993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3089204595715790876798657 2316903446786843157598993)
                    ·
                      refine ⟨1737677585090132368199245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2316903446786843157598993 1737677585090132368199245)
                      ·
                        rfl

theorem cell23_3384115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 4, 2, 1, 2, 2].length) (baseStart_3384115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3384115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3384115 prefixEnd_3384115 := by exact prefixLift 3384115
  have htrace : WordTrace (prefixWord ++ tailWord_3384115) baseStart_3384115 baseEnd_3384115 := by
    simpa [prefixWord, tailWord_3384115, baseEnd_3384115] using wordTrace_append hprefix tailTrace_3384115
  have hstable : (prefixWord ++ tailWord_3384115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3384115).length < 2 ^ (prefixWord ++ tailWord_3384115).sum := by decide
  have hdescent : baseEnd_3384115 < baseStart_3384115 := by decide
  rcases family_descends (prefixWord ++ tailWord_3384115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3384117 : List Nat := [1, 3, 3, 1, 3, 1, 1, 1, 2, 7]
def baseStart_3384117 : Nat := 118140960795 + 3384117 * 2 ^ 59
def prefixEnd_3384117 : Nat := 4983230072969 + 3 ^ 40 * 3384117 * 2
def baseEnd_3384117 : Nat := 579226204017147120124745

theorem tailTrace_3384117 : CollatzResearch.WordTrace tailWord_3384117 prefixEnd_3384117 579226204017147120124745 := by
  unfold tailWord_3384117
  simp only [CollatzResearch.WordTrace]
  refine ⟨123428887080929545014870605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82285924720619696676580403 123428887080929545014870605)
  ·
    refine ⟨46285832655348579380576477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123428887080929545014870605 46285832655348579380576477)
    ·
      refine ⟨17357187245755717267716179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46285832655348579380576477 17357187245755717267716179)
      ·
        refine ⟨26035780868633575901574269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17357187245755717267716179 26035780868633575901574269)
        ·
          refine ⟨9763417825737590963090351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26035780868633575901574269 9763417825737590963090351)
          ·
            refine ⟨14645126738606386444635527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9763417825737590963090351 14645126738606386444635527)
            ·
              refine ⟨21967690107909579666953291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14645126738606386444635527 21967690107909579666953291)
              ·
                refine ⟨32951535161864369500429937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21967690107909579666953291 32951535161864369500429937)
                ·
                  refine ⟨24713651371398277125322453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32951535161864369500429937 24713651371398277125322453)
                  ·
                    refine ⟨579226204017147120124745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24713651371398277125322453 579226204017147120124745)
                    ·
                      rfl

theorem cell23_3384117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 1, 2, 7].length) (baseStart_3384117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3384117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3384117 prefixEnd_3384117 := by exact prefixLift 3384117
  have htrace : WordTrace (prefixWord ++ tailWord_3384117) baseStart_3384117 baseEnd_3384117 := by
    simpa [prefixWord, tailWord_3384117, baseEnd_3384117] using wordTrace_append hprefix tailTrace_3384117
  have hstable : (prefixWord ++ tailWord_3384117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3384117).length < 2 ^ (prefixWord ++ tailWord_3384117).sum := by decide
  have hdescent : baseEnd_3384117 < baseStart_3384117 := by decide
  rcases family_descends (prefixWord ++ tailWord_3384117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3384177 : List Nat := [1, 2, 2, 2, 1, 4, 1, 3, 7]
def baseStart_3384177 : Nat := 118140960795 + 3384177 * 2 ^ 59
def prefixEnd_3384177 : Nat := 4983230072969 + 3 ^ 40 * 3384177 * 2
def baseEnd_3384177 : Nat := 193078824543412347291551

theorem tailTrace_3384177 : CollatzResearch.WordTrace tailWord_3384177 prefixEnd_3384177 193078824543412347291551 := by
  unfold tailWord_3384177
  simp only [CollatzResearch.WordTrace]
  refine ⟨123431075460712175262054785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82287383640474783508036523 123431075460712175262054785)
  ·
    refine ⟨92573306595534131446541089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123431075460712175262054785 92573306595534131446541089)
    ·
      refine ⟨69429979946650598584905817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92573306595534131446541089 69429979946650598584905817)
      ·
        refine ⟨52072484959987948938679363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69429979946650598584905817 52072484959987948938679363)
        ·
          refine ⟨78108727439981923408019045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52072484959987948938679363 78108727439981923408019045)
          ·
            refine ⟨14645386394996610639003571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78108727439981923408019045 14645386394996610639003571)
            ·
              refine ⟨21968079592494915958505357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14645386394996610639003571 21968079592494915958505357)
              ·
                refine ⟨8238029847185593484439509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21968079592494915958505357 8238029847185593484439509)
                ·
                  refine ⟨193078824543412347291551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8238029847185593484439509 193078824543412347291551)
                  ·
                    rfl

theorem cell23_3384177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 3, 7].length) (baseStart_3384177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3384177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3384177 prefixEnd_3384177 := by exact prefixLift 3384177
  have htrace : WordTrace (prefixWord ++ tailWord_3384177) baseStart_3384177 baseEnd_3384177 := by
    simpa [prefixWord, tailWord_3384177, baseEnd_3384177] using wordTrace_append hprefix tailTrace_3384177
  have hstable : (prefixWord ++ tailWord_3384177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3384177).length < 2 ^ (prefixWord ++ tailWord_3384177).sum := by decide
  have hdescent : baseEnd_3384177 < baseStart_3384177 := by decide
  rcases family_descends (prefixWord ++ tailWord_3384177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3384217 : List Nat := [1, 2, 1, 2, 1, 3, 1, 4, 1, 2, 5]
def baseStart_3384217 : Nat := 118140960795 + 3384217 * 2 ^ 59
def prefixEnd_3384217 : Nat := 4983230072969 + 3 ^ 40 * 3384217 * 2
def baseEnd_3384217 : Nat := 1737729960116890969123775

theorem tailTrace_3384217 : CollatzResearch.WordTrace tailWord_3384217 prefixEnd_3384217 1737729960116890969123775 := by
  unfold tailWord_3384217
  simp only [CollatzResearch.WordTrace]
  refine ⟨123432534380567262093510905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82288356253711508062340603 123432534380567262093510905)
  ·
    refine ⟨92574400785425446570133179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123432534380567262093510905 92574400785425446570133179)
    ·
      refine ⟨138861601178138169855199769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92574400785425446570133179 138861601178138169855199769)
      ·
        refine ⟨104146200883603627391399827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138861601178138169855199769 104146200883603627391399827)
        ·
          refine ⟨156219301325405441087099741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104146200883603627391399827 156219301325405441087099741)
          ·
            refine ⟨58582237997027040407662403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 156219301325405441087099741 58582237997027040407662403)
            ·
              refine ⟨87873356995540560611493605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58582237997027040407662403 87873356995540560611493605)
              ·
                refine ⟨16476254436663855114655051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87873356995540560611493605 16476254436663855114655051)
                ·
                  refine ⟨24714381654995782671982577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16476254436663855114655051 24714381654995782671982577)
                  ·
                    refine ⟨18535786241246837003986933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24714381654995782671982577 18535786241246837003986933)
                    ·
                      refine ⟨1737729960116890969123775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18535786241246837003986933 1737729960116890969123775)
                      ·
                        rfl

theorem cell23_3384217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 4, 1, 2, 5].length) (baseStart_3384217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3384217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3384217 prefixEnd_3384217 := by exact prefixLift 3384217
  have htrace : WordTrace (prefixWord ++ tailWord_3384217) baseStart_3384217 baseEnd_3384217 := by
    simpa [prefixWord, tailWord_3384217, baseEnd_3384217] using wordTrace_append hprefix tailTrace_3384217
  have hstable : (prefixWord ++ tailWord_3384217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3384217).length < 2 ^ (prefixWord ++ tailWord_3384217).sum := by decide
  have hdescent : baseEnd_3384217 < baseStart_3384217 := by decide
  rcases family_descends (prefixWord ++ tailWord_3384217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3384278 : List Nat := [5, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4]
def baseStart_3384278 : Nat := 118140960795 + 3384278 * 2 ^ 59
def prefixEnd_3384278 : Nat := 4983230072969 + 3 ^ 40 * 3384278 * 2
def baseEnd_3384278 : Nat := 1737761282436815230460995

theorem tailTrace_3384278 : CollatzResearch.WordTrace tailWord_3384278 prefixEnd_3384278 1737761282436815230460995 := by
  unfold tailWord_3384278
  simp only [CollatzResearch.WordTrace]
  refine ⟨7714672452084141844467593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 82289839488897513007654325 7714672452084141844467593)
  ·
    refine ⟨5786004339063106383350695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7714672452084141844467593 5786004339063106383350695)
    ·
      refine ⟨8679006508594659575026043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5786004339063106383350695 8679006508594659575026043)
      ·
        refine ⟨13018509762891989362539065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8679006508594659575026043 13018509762891989362539065)
        ·
          refine ⟨9763882322168992021904299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13018509762891989362539065 9763882322168992021904299)
          ·
            refine ⟨14645823483253488032856449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9763882322168992021904299 14645823483253488032856449)
            ·
              refine ⟨10984367612440116024642337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14645823483253488032856449 10984367612440116024642337)
              ·
                refine ⟨8238275709330087018481753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10984367612440116024642337 8238275709330087018481753)
                ·
                  refine ⟨6178706781997565263861315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8238275709330087018481753 6178706781997565263861315)
                  ·
                    refine ⟨9268060172996347895791973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6178706781997565263861315 9268060172996347895791973)
                    ·
                      refine ⟨1737761282436815230460995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9268060172996347895791973 1737761282436815230460995)
                      ·
                        rfl

theorem cell23_3384278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_3384278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3384278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3384278 prefixEnd_3384278 := by exact prefixLift 3384278
  have htrace : WordTrace (prefixWord ++ tailWord_3384278) baseStart_3384278 baseEnd_3384278 := by
    simpa [prefixWord, tailWord_3384278, baseEnd_3384278] using wordTrace_append hprefix tailTrace_3384278
  have hstable : (prefixWord ++ tailWord_3384278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3384278).length < 2 ^ (prefixWord ++ tailWord_3384278).sum := by decide
  have hdescent : baseEnd_3384278 < baseStart_3384278 := by decide
  rcases family_descends (prefixWord ++ tailWord_3384278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3384281 : List Nat := [1, 2, 1, 2, 5, 1, 2, 2, 2, 2, 3]
def baseStart_3384281 : Nat := 118140960795 + 3384281 * 2 ^ 59
def prefixEnd_3384281 : Nat := 4983230072969 + 3 ^ 40 * 3384281 * 2
def baseEnd_3384281 : Nat := 1737762822878778718723481

theorem tailTrace_3384281 : CollatzResearch.WordTrace tailWord_3384281 prefixEnd_3384281 1737762822878778718723481 := by
  unfold tailWord_3384281
  simp only [CollatzResearch.WordTrace]
  refine ⟨123434868652335401023840697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82289912434890267349227131 123434868652335401023840697)
  ·
    refine ⟨92576151489251550767880523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123434868652335401023840697 92576151489251550767880523)
    ·
      refine ⟨138864227233877326151820785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92576151489251550767880523 138864227233877326151820785)
      ·
        refine ⟨104148170425407994613865589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138864227233877326151820785 104148170425407994613865589)
        ·
          refine ⟨9763890977381999495049899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 104148170425407994613865589 9763890977381999495049899)
          ·
            refine ⟨14645836466072999242574849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9763890977381999495049899 14645836466072999242574849)
            ·
              refine ⟨10984377349554749431931137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14645836466072999242574849 10984377349554749431931137)
              ·
                refine ⟨8238283012166062073948353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10984377349554749431931137 8238283012166062073948353)
                ·
                  refine ⟨6178712259124546555461265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8238283012166062073948353 6178712259124546555461265)
                  ·
                    refine ⟨4634034194343409916595949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6178712259124546555461265 4634034194343409916595949)
                    ·
                      refine ⟨1737762822878778718723481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4634034194343409916595949 1737762822878778718723481)
                      ·
                        rfl

theorem cell23_3384281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 2, 2, 2, 3].length) (baseStart_3384281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3384281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3384281 prefixEnd_3384281 := by exact prefixLift 3384281
  have htrace : WordTrace (prefixWord ++ tailWord_3384281) baseStart_3384281 baseEnd_3384281 := by
    simpa [prefixWord, tailWord_3384281, baseEnd_3384281] using wordTrace_append hprefix tailTrace_3384281
  have hstable : (prefixWord ++ tailWord_3384281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3384281).length < 2 ^ (prefixWord ++ tailWord_3384281).sum := by decide
  have hdescent : baseEnd_3384281 < baseStart_3384281 := by decide
  rcases family_descends (prefixWord ++ tailWord_3384281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3384331 : List Nat := [1, 1, 1, 1, 6, 3, 1, 3, 1, 5]
def baseStart_3384331 : Nat := 118140960795 + 3384331 * 2 ^ 59
def prefixEnd_3384331 : Nat := 4983230072969 + 3 ^ 40 * 3384331 * 2
def baseEnd_3384331 : Nat := 579262832303834507699417

theorem tailTrace_3384331 : CollatzResearch.WordTrace tailWord_3384331 prefixEnd_3384331 579262832303834507699417 := by
  unfold tailWord_3384331
  simp only [CollatzResearch.WordTrace]
  refine ⟨123436692302154259563160847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82291128201436173042107231 123436692302154259563160847)
  ·
    refine ⟨185155038453231389344741271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123436692302154259563160847 185155038453231389344741271)
    ·
      refine ⟨277732557679847084017111907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185155038453231389344741271 277732557679847084017111907)
      ·
        refine ⟨416598836519770626025667861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277732557679847084017111907 416598836519770626025667861)
        ·
          refine ⟨19528070461864248094953181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 416598836519770626025667861 19528070461864248094953181)
          ·
            refine ⟨7323026423199093035607443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19528070461864248094953181 7323026423199093035607443)
            ·
              refine ⟨10984539634798639553411165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7323026423199093035607443 10984539634798639553411165)
              ·
                refine ⟨4119202363049489832529187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10984539634798639553411165 4119202363049489832529187)
                ·
                  refine ⟨6178803544574234748793781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4119202363049489832529187 6178803544574234748793781)
                  ·
                    refine ⟨579262832303834507699417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6178803544574234748793781 579262832303834507699417)
                    ·
                      rfl

theorem cell23_3384331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 3, 1, 5].length) (baseStart_3384331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3384331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3384331 prefixEnd_3384331 := by exact prefixLift 3384331
  have htrace : WordTrace (prefixWord ++ tailWord_3384331) baseStart_3384331 baseEnd_3384331 := by
    simpa [prefixWord, tailWord_3384331, baseEnd_3384331] using wordTrace_append hprefix tailTrace_3384331
  have hstable : (prefixWord ++ tailWord_3384331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3384331).length < 2 ^ (prefixWord ++ tailWord_3384331).sum := by decide
  have hdescent : baseEnd_3384331 < baseStart_3384331 := by decide
  rcases family_descends (prefixWord ++ tailWord_3384331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3384364 : List Nat := [2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 6]
def baseStart_3384364 : Nat := 118140960795 + 3384364 * 2 ^ 59
def prefixEnd_3384364 : Nat := 4983230072969 + 3 ^ 40 * 3384364 * 2
def baseEnd_3384364 : Nat := 1737805441773101893985599

theorem tailTrace_3384364 : CollatzResearch.WordTrace tailWord_3384364 prefixEnd_3384364 1737805441773101893985599 := by
  unfold tailWord_3384364
  simp only [CollatzResearch.WordTrace]
  refine ⟨61718947955517353099556073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82291930607356470799408097 61718947955517353099556073)
  ·
    refine ⟨46289210966638014824667055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61718947955517353099556073 46289210966638014824667055)
    ·
      refine ⟨69433816449957022237000583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46289210966638014824667055 69433816449957022237000583)
      ·
        refine ⟨104150724674935533355500875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69433816449957022237000583 104150724674935533355500875)
        ·
          refine ⟨156226087012403300033251313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104150724674935533355500875 156226087012403300033251313)
          ·
            refine ⟨117169565259302475024938485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156226087012403300033251313 117169565259302475024938485)
            ·
              refine ⟨10984646743059607033587983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 117169565259302475024938485 10984646743059607033587983)
              ·
                refine ⟨16476970114589410550381975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10984646743059607033587983 16476970114589410550381975)
                ·
                  refine ⟨24715455171884115825572963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16476970114589410550381975 24715455171884115825572963)
                  ·
                    refine ⟨37073182757826173738359445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24715455171884115825572963 37073182757826173738359445)
                    ·
                      refine ⟨1737805441773101893985599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37073182757826173738359445 1737805441773101893985599)
                      ·
                        rfl

theorem cell23_3384364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 6].length) (baseStart_3384364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3384364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3384364 prefixEnd_3384364 := by exact prefixLift 3384364
  have htrace : WordTrace (prefixWord ++ tailWord_3384364) baseStart_3384364 baseEnd_3384364 := by
    simpa [prefixWord, tailWord_3384364, baseEnd_3384364] using wordTrace_append hprefix tailTrace_3384364
  have hstable : (prefixWord ++ tailWord_3384364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3384364).length < 2 ^ (prefixWord ++ tailWord_3384364).sum := by decide
  have hdescent : baseEnd_3384364 < baseStart_3384364 := by decide
  rcases family_descends (prefixWord ++ tailWord_3384364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3384368 : List Nat := [2, 1, 1, 1, 2, 4, 1, 4, 3, 2, 2]
def baseStart_3384368 : Nat := 118140960795 + 3384368 * 2 ^ 59
def prefixEnd_3384368 : Nat := 4983230072969 + 3 ^ 40 * 3384368 * 2
def baseEnd_3384368 : Nat := 1737807495695719878335581

theorem tailTrace_3384368 : CollatzResearch.WordTrace tailWord_3384368 prefixEnd_3384368 1737807495695719878335581 := by
  unfold tailWord_3384368
  simp only [CollatzResearch.WordTrace]
  refine ⟨61719020901510107441128879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82292027868680143254838505 61719020901510107441128879)
  ·
    refine ⟨92578531352265161161693319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61719020901510107441128879 92578531352265161161693319)
    ·
      refine ⟨138867797028397741742539979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92578531352265161161693319 138867797028397741742539979)
      ·
        refine ⟨208301695542596612613809969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138867797028397741742539979 208301695542596612613809969)
        ·
          refine ⟨156226271656947459460357477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208301695542596612613809969 156226271656947459460357477)
          ·
            refine ⟨29292425935677648648817027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 156226271656947459460357477 29292425935677648648817027)
            ·
              refine ⟨43938638903516472973225541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29292425935677648648817027 43938638903516472973225541)
              ·
                refine ⟨8238494794409338682479789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43938638903516472973225541 8238494794409338682479789)
                ·
                  refine ⟨3089435547903502005929921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8238494794409338682479789 3089435547903502005929921)
                  ·
                    refine ⟨2317076660927626504447441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3089435547903502005929921 2317076660927626504447441)
                    ·
                      refine ⟨1737807495695719878335581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2317076660927626504447441 1737807495695719878335581)
                      ·
                        rfl

theorem cell23_3384368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 4, 3, 2, 2].length) (baseStart_3384368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3384368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3384368 prefixEnd_3384368 := by exact prefixLift 3384368
  have htrace : WordTrace (prefixWord ++ tailWord_3384368) baseStart_3384368 baseEnd_3384368 := by
    simpa [prefixWord, tailWord_3384368, baseEnd_3384368] using wordTrace_append hprefix tailTrace_3384368
  have hstable : (prefixWord ++ tailWord_3384368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3384368).length < 2 ^ (prefixWord ++ tailWord_3384368).sum := by decide
  have hdescent : baseEnd_3384368 < baseStart_3384368 := by decide
  rcases family_descends (prefixWord ++ tailWord_3384368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3384402 : List Nat := [3, 2, 2, 1, 3, 3, 1, 1, 3, 2, 2]
def baseStart_3384402 : Nat := 118140960795 + 3384402 * 2 ^ 59
def prefixEnd_3384402 : Nat := 4983230072969 + 3 ^ 40 * 3384402 * 2
def baseEnd_3384402 : Nat := 1737824954037972745310425

theorem tailTrace_3384402 : CollatzResearch.WordTrace tailWord_3384402 prefixEnd_3384402 1737824954037972745310425 := by
  unfold tailWord_3384402
  simp only [CollatzResearch.WordTrace]
  refine ⟨30859820471224259672248865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82292854589931359125996973 30859820471224259672248865)
  ·
    refine ⟨23144865353418194754186649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30859820471224259672248865 23144865353418194754186649)
    ·
      refine ⟨17358649015063646065639987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23144865353418194754186649 17358649015063646065639987)
      ·
        refine ⟨26037973522595469098459981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17358649015063646065639987 26037973522595469098459981)
        ·
          refine ⟨9764240070973300911922493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26037973522595469098459981 9764240070973300911922493)
          ·
            refine ⟨3661590026614987841970935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9764240070973300911922493 3661590026614987841970935)
            ·
              refine ⟨5492385039922481762956403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3661590026614987841970935 5492385039922481762956403)
              ·
                refine ⟨8238577559883722644434605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5492385039922481762956403 8238577559883722644434605)
                ·
                  refine ⟨3089466584956395991662977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8238577559883722644434605 3089466584956395991662977)
                  ·
                    refine ⟨2317099938717296993747233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3089466584956395991662977 2317099938717296993747233)
                    ·
                      refine ⟨1737824954037972745310425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2317099938717296993747233 1737824954037972745310425)
                      ·
                        rfl

theorem cell23_3384402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 1, 1, 3, 2, 2].length) (baseStart_3384402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3384402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3384402 prefixEnd_3384402 := by exact prefixLift 3384402
  have htrace : WordTrace (prefixWord ++ tailWord_3384402) baseStart_3384402 baseEnd_3384402 := by
    simpa [prefixWord, tailWord_3384402, baseEnd_3384402] using wordTrace_append hprefix tailTrace_3384402
  have hstable : (prefixWord ++ tailWord_3384402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3384402).length < 2 ^ (prefixWord ++ tailWord_3384402).sum := by decide
  have hdescent : baseEnd_3384402 < baseStart_3384402 := by decide
  rcases family_descends (prefixWord ++ tailWord_3384402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3384428 : List Nat := [2, 2, 1, 1, 3, 2, 3, 1, 3, 3, 2]
def baseStart_3384428 : Nat := 118140960795 + 3384428 * 2 ^ 59
def prefixEnd_3384428 : Nat := 4983230072969 + 3 ^ 40 * 3384428 * 2
def baseEnd_3384428 : Nat := 1737838304534989643585305

theorem tailTrace_3384428 : CollatzResearch.WordTrace tailWord_3384428 prefixEnd_3384428 1737838304534989643585305 := by
  unfold tailWord_3384428
  simp only [CollatzResearch.WordTrace]
  refine ⟨61720115091401422564720969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82293486788535230086294625 61720115091401422564720969)
  ·
    refine ⟨46290086318551066923540727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61720115091401422564720969 46290086318551066923540727)
    ·
      refine ⟨69435129477826600385311091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46290086318551066923540727 69435129477826600385311091)
      ·
        refine ⟨104152694216739900577966637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69435129477826600385311091 104152694216739900577966637)
        ·
          refine ⟨39057260331277462716737489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104152694216739900577966637 39057260331277462716737489)
          ·
            refine ⟨29292945248458097037553117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39057260331277462716737489 29292945248458097037553117)
            ·
              refine ⟨10984854468171786389082419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29292945248458097037553117 10984854468171786389082419)
              ·
                refine ⟨16477281702257679583623629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10984854468171786389082419 16477281702257679583623629)
                ·
                  refine ⟨6178980638346629843858861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16477281702257679583623629 6178980638346629843858861)
                  ·
                    refine ⟨2317117739379986191447073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6178980638346629843858861 2317117739379986191447073)
                    ·
                      refine ⟨1737838304534989643585305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2317117739379986191447073 1737838304534989643585305)
                      ·
                        rfl

theorem cell23_3384428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 3, 2].length) (baseStart_3384428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3384428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3384428 prefixEnd_3384428 := by exact prefixLift 3384428
  have htrace : WordTrace (prefixWord ++ tailWord_3384428) baseStart_3384428 baseEnd_3384428 := by
    simpa [prefixWord, tailWord_3384428, baseEnd_3384428] using wordTrace_append hprefix tailTrace_3384428
  have hstable : (prefixWord ++ tailWord_3384428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3384428).length < 2 ^ (prefixWord ++ tailWord_3384428).sum := by decide
  have hdescent : baseEnd_3384428 < baseStart_3384428 := by decide
  rcases family_descends (prefixWord ++ tailWord_3384428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3384458 : List Nat := [3, 1, 2, 3, 1, 1, 1, 2, 3, 4, 2]
def baseStart_3384458 : Nat := 118140960795 + 3384458 * 2 ^ 59
def prefixEnd_3384458 : Nat := 4983230072969 + 3 ^ 40 * 3384458 * 2
def baseEnd_3384458 : Nat := 1737853708954624526210167

theorem tailTrace_3384458 : CollatzResearch.WordTrace tailWord_3384458 prefixEnd_3384458 1737853708954624526210167 := by
  unfold tailWord_3384458
  simp only [CollatzResearch.WordTrace]
  refine ⟨30860331093173540063258507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82294216248462773502022685 30860331093173540063258507)
  ·
    refine ⟨46290496639760310094887761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30860331093173540063258507 46290496639760310094887761)
    ·
      refine ⟨34717872479820232571165821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46290496639760310094887761 34717872479820232571165821)
      ·
        refine ⟨13019202179932587214187183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34717872479820232571165821 13019202179932587214187183)
        ·
          refine ⟨19528803269898880821280775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13019202179932587214187183 19528803269898880821280775)
          ·
            refine ⟨29293204904848321231921163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19528803269898880821280775 29293204904848321231921163)
            ·
              refine ⟨43939807357272481847881745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29293204904848321231921163 43939807357272481847881745)
              ·
                refine ⟨32954855517954361385911309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43939807357272481847881745 32954855517954361385911309)
                ·
                  refine ⟨12358070819232885519716741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32954855517954361385911309 12358070819232885519716741)
                  ·
                    refine ⟨2317138278606166034946889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12358070819232885519716741 2317138278606166034946889)
                    ·
                      refine ⟨1737853708954624526210167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2317138278606166034946889 1737853708954624526210167)
                      ·
                        rfl

theorem cell23_3384458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 2, 3, 4, 2].length) (baseStart_3384458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3384458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3384458 prefixEnd_3384458 := by exact prefixLift 3384458
  have htrace : WordTrace (prefixWord ++ tailWord_3384458) baseStart_3384458 baseEnd_3384458 := by
    simpa [prefixWord, tailWord_3384458, baseEnd_3384458] using wordTrace_append hprefix tailTrace_3384458
  have hstable : (prefixWord ++ tailWord_3384458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3384458).length < 2 ^ (prefixWord ++ tailWord_3384458).sum := by decide
  have hdescent : baseEnd_3384458 < baseStart_3384458 := by decide
  rcases family_descends (prefixWord ++ tailWord_3384458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3384471 : List Nat := [1, 1, 3, 3, 3, 1, 1, 1, 1, 4, 4]
def baseStart_3384471 : Nat := 118140960795 + 3384471 * 2 ^ 59
def prefixEnd_3384471 : Nat := 4983230072969 + 3 ^ 40 * 3384471 * 2
def baseEnd_3384471 : Nat := 1737860384203132975347607

theorem tailTrace_3384471 : CollatzResearch.WordTrace tailWord_3384471 prefixEnd_3384471 1737860384203132975347607 := by
  unfold tailWord_3384471
  simp only [CollatzResearch.WordTrace]
  refine ⟨123441798521647063473257267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82294532347764708982171511 123441798521647063473257267)
  ·
    refine ⟨185162697782470595209885901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123441798521647063473257267 185162697782470595209885901)
    ·
      refine ⟨69436011668426473203707213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185162697782470595209885901 69436011668426473203707213)
      ·
        refine ⟨26038504375659927451390205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69436011668426473203707213 26038504375659927451390205)
        ·
          refine ⟨9764439140872472794271327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26038504375659927451390205 9764439140872472794271327)
          ·
            refine ⟨14646658711308709191406991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9764439140872472794271327 14646658711308709191406991)
            ·
              refine ⟨21969988066963063787110487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14646658711308709191406991 21969988066963063787110487)
              ·
                refine ⟨32954982100444595680665731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21969988066963063787110487 32954982100444595680665731)
                ·
                  refine ⟨49432473150666893520998597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32954982100444595680665731 49432473150666893520998597)
                  ·
                    refine ⟨9268588715750042535187237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49432473150666893520998597 9268588715750042535187237)
                    ·
                      refine ⟨1737860384203132975347607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9268588715750042535187237 1737860384203132975347607)
                      ·
                        rfl

theorem cell23_3384471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 1, 1, 4, 4].length) (baseStart_3384471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3384471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3384471 prefixEnd_3384471 := by exact prefixLift 3384471
  have htrace : WordTrace (prefixWord ++ tailWord_3384471) baseStart_3384471 baseEnd_3384471 := by
    simpa [prefixWord, tailWord_3384471, baseEnd_3384471] using wordTrace_append hprefix tailTrace_3384471
  have hstable : (prefixWord ++ tailWord_3384471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3384471).length < 2 ^ (prefixWord ++ tailWord_3384471).sum := by decide
  have hdescent : baseEnd_3384471 < baseStart_3384471 := by decide
  rcases family_descends (prefixWord ++ tailWord_3384471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3384481 : List Nat := [1, 2, 3, 3, 1, 1, 3, 2, 7]
def baseStart_3384481 : Nat := 118140960795 + 3384481 * 2 ^ 59
def prefixEnd_3384481 : Nat := 4983230072969 + 3 ^ 40 * 3384481 * 2
def baseEnd_3384481 : Nat := 193096168778853104024729

theorem tailTrace_3384481 : CollatzResearch.WordTrace tailWord_3384481 prefixEnd_3384481 193096168778853104024729 := by
  unfold tailWord_3384481
  simp only [CollatzResearch.WordTrace]
  refine ⟨123442163251610835181121297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82294775501073890120747531 123442163251610835181121297)
  ·
    refine ⟨92581622438708126385840973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123442163251610835181121297 92581622438708126385840973)
    ·
      refine ⟨34718108414515547394690365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92581622438708126385840973 34718108414515547394690365)
      ·
        refine ⟨13019290655443330273008887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34718108414515547394690365 13019290655443330273008887)
        ·
          refine ⟨19528935983164995409513331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13019290655443330273008887 19528935983164995409513331)
          ·
            refine ⟨29293403974747493114269997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19528935983164995409513331 29293403974747493114269997)
            ·
              refine ⟨10985026490530309917851249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29293403974747493114269997 10985026490530309917851249)
              ·
                refine ⟨8238769867897732438388437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10985026490530309917851249 8238769867897732438388437)
                ·
                  refine ⟨193096168778853104024729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8238769867897732438388437 193096168778853104024729)
                  ·
                    rfl

theorem cell23_3384481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 2, 7].length) (baseStart_3384481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3384481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3384481 prefixEnd_3384481 := by exact prefixLift 3384481
  have htrace : WordTrace (prefixWord ++ tailWord_3384481) baseStart_3384481 baseEnd_3384481 := by
    simpa [prefixWord, tailWord_3384481, baseEnd_3384481] using wordTrace_append hprefix tailTrace_3384481
  have hstable : (prefixWord ++ tailWord_3384481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3384481).length < 2 ^ (prefixWord ++ tailWord_3384481).sum := by decide
  have hdescent : baseEnd_3384481 < baseStart_3384481 := by decide
  rcases family_descends (prefixWord ++ tailWord_3384481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3384498 : List Nat := [3, 2, 1, 1, 1, 4, 1, 5, 5]
def baseStart_3384498 : Nat := 118140960795 + 3384498 * 2 ^ 59
def prefixEnd_3384498 : Nat := 4983230072969 + 3 ^ 40 * 3384498 * 2
def baseEnd_3384498 : Nat := 193097138686756041078887

theorem tailTrace_3384498 : CollatzResearch.WordTrace tailWord_3384498 prefixEnd_3384498 193097138686756041078887 := by
  unfold tailWord_3384498
  simp only [CollatzResearch.WordTrace]
  refine ⟨30860695823137311771122537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82295188861699498056326765 30860695823137311771122537)
  ·
    refine ⟨23145521867352983828341903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30860695823137311771122537 23145521867352983828341903)
    ·
      refine ⟨34718282801029475742512855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23145521867352983828341903 34718282801029475742512855)
      ·
        refine ⟨52077424201544213613769283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34718282801029475742512855 52077424201544213613769283)
        ·
          refine ⟨78116136302316320420653925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52077424201544213613769283 78116136302316320420653925)
          ·
            refine ⟨14646775556684310078872611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78116136302316320420653925 14646775556684310078872611)
            ·
              refine ⟨21970163335026465118308917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14646775556684310078872611 21970163335026465118308917)
              ·
                refine ⟨2059702812658731104841461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21970163335026465118308917 2059702812658731104841461)
                ·
                  refine ⟨193097138686756041078887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2059702812658731104841461 193097138686756041078887)
                  ·
                    rfl

theorem cell23_3384498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 5, 5].length) (baseStart_3384498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3384498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3384498 prefixEnd_3384498 := by exact prefixLift 3384498
  have htrace : WordTrace (prefixWord ++ tailWord_3384498) baseStart_3384498 baseEnd_3384498 := by
    simpa [prefixWord, tailWord_3384498, baseEnd_3384498] using wordTrace_append hprefix tailTrace_3384498
  have hstable : (prefixWord ++ tailWord_3384498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3384498).length < 2 ^ (prefixWord ++ tailWord_3384498).sum := by decide
  have hdescent : baseEnd_3384498 < baseStart_3384498 := by decide
  rcases family_descends (prefixWord ++ tailWord_3384498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3384508 : List Nat := [2, 2, 2, 3, 2, 1, 1, 2, 2, 3, 3]
def baseStart_3384508 : Nat := 118140960795 + 3384508 * 2 ^ 59
def prefixEnd_3384508 : Nat := 4983230072969 + 3 ^ 40 * 3384508 * 2
def baseEnd_3384508 : Nat := 1737879382987349330584937

theorem tailTrace_3384508 : CollatzResearch.WordTrace tailWord_3384508 prefixEnd_3384508 1737879382987349330584937 := by
  unfold tailWord_3384508
  simp only [CollatzResearch.WordTrace]
  refine ⟨61721574011256509396177089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82295432015008679194902785 61721574011256509396177089)
  ·
    refine ⟨46291180508442382047132817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61721574011256509396177089 46291180508442382047132817)
    ·
      refine ⟨34718385381331786535349613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46291180508442382047132817 34718385381331786535349613)
      ·
        refine ⟨13019394517999419950756105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34718385381331786535349613 13019394517999419950756105)
        ·
          refine ⟨9764545888499564963067079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13019394517999419950756105 9764545888499564963067079)
          ·
            refine ⟨14646818832749347444600619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9764545888499564963067079 14646818832749347444600619)
            ·
              refine ⟨21970228249124021166900929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14646818832749347444600619 21970228249124021166900929)
              ·
                refine ⟨16477671186843015875175697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21970228249124021166900929 16477671186843015875175697)
                ·
                  refine ⟨12358253390132261906381773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16477671186843015875175697 12358253390132261906381773)
                  ·
                    refine ⟨4634345021299598214893165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12358253390132261906381773 4634345021299598214893165)
                    ·
                      refine ⟨1737879382987349330584937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4634345021299598214893165 1737879382987349330584937)
                      ·
                        rfl

theorem cell23_3384508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 2, 2, 3, 3].length) (baseStart_3384508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3384508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3384508 prefixEnd_3384508 := by exact prefixLift 3384508
  have htrace : WordTrace (prefixWord ++ tailWord_3384508) baseStart_3384508 baseEnd_3384508 := by
    simpa [prefixWord, tailWord_3384508, baseEnd_3384508] using wordTrace_append hprefix tailTrace_3384508
  have hstable : (prefixWord ++ tailWord_3384508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3384508).length < 2 ^ (prefixWord ++ tailWord_3384508).sum := by decide
  have hdescent : baseEnd_3384508 < baseStart_3384508 := by decide
  rcases family_descends (prefixWord ++ tailWord_3384508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3384511 : List Nat := [1, 1, 2, 2, 2, 2, 2, 4, 2, 5]
def baseStart_3384511 : Nat := 118140960795 + 3384511 * 2 ^ 59
def prefixEnd_3384511 : Nat := 4983230072969 + 3 ^ 40 * 3384511 * 2
def baseEnd_3384511 : Nat := 579293641143104272949141

theorem tailTrace_3384511 : CollatzResearch.WordTrace tailWord_3384511 prefixEnd_3384511 579293641143104272949141 := by
  unfold tailWord_3384511
  simp only [CollatzResearch.WordTrace]
  refine ⟨123443257441502150304713387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82295504961001433536475591 123443257441502150304713387)
  ·
    refine ⟨185164886162253225457070081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123443257441502150304713387 185164886162253225457070081)
    ·
      refine ⟨138873664621689919092802561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185164886162253225457070081 138873664621689919092802561)
      ·
        refine ⟨104155248466267439319601921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138873664621689919092802561 104155248466267439319601921)
        ·
          refine ⟨78116436349700579489701441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104155248466267439319601921 78116436349700579489701441)
          ·
            refine ⟨58587327262275434617276081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78116436349700579489701441 58587327262275434617276081)
            ·
              refine ⟨43940495446706575962957061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58587327262275434617276081 43940495446706575962957061)
              ·
                refine ⟨8238842896257482993054449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43940495446706575962957061 8238842896257482993054449)
                ·
                  refine ⟨6179132172193112244790837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8238842896257482993054449 6179132172193112244790837)
                  ·
                    refine ⟨579293641143104272949141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6179132172193112244790837 579293641143104272949141)
                    ·
                      rfl

theorem cell23_3384511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 4, 2, 5].length) (baseStart_3384511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3384511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3384511 prefixEnd_3384511 := by exact prefixLift 3384511
  have htrace : WordTrace (prefixWord ++ tailWord_3384511) baseStart_3384511 baseEnd_3384511 := by
    simpa [prefixWord, tailWord_3384511, baseEnd_3384511] using wordTrace_append hprefix tailTrace_3384511
  have hstable : (prefixWord ++ tailWord_3384511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3384511).length < 2 ^ (prefixWord ++ tailWord_3384511).sum := by decide
  have hdescent : baseEnd_3384511 < baseStart_3384511 := by decide
  rcases family_descends (prefixWord ++ tailWord_3384511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3384531 : List Nat := [1, 1, 1, 2, 1, 1, 1, 6, 4, 1, 4]
def baseStart_3384531 : Nat := 118140960795 + 3384531 * 2 ^ 59
def prefixEnd_3384531 : Nat := 4983230072969 + 3 ^ 40 * 3384531 * 2
def baseEnd_3384531 : Nat := 1737891193042402740597331

theorem tailTrace_3384531 : CollatzResearch.WordTrace tailWord_3384531 prefixEnd_3384531 1737891193042402740597331 := by
  unfold tailWord_3384531
  simp only [CollatzResearch.WordTrace]
  refine ⟨123443986901429693720441447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82295991267619795813627631 123443986901429693720441447)
  ·
    refine ⟨185165980352144540580662171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123443986901429693720441447 185165980352144540580662171)
    ·
      refine ⟨277748970528216810870993257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185165980352144540580662171 277748970528216810870993257)
      ·
        refine ⟨208311727896162608153244943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 277748970528216810870993257 208311727896162608153244943)
        ·
          refine ⟨312467591844243912229867415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208311727896162608153244943 312467591844243912229867415)
          ·
            refine ⟨468701387766365868344801123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 312467591844243912229867415 468701387766365868344801123)
            ·
              refine ⟨703052081649548802517201685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 468701387766365868344801123 703052081649548802517201685)
              ·
                refine ⟨32955566327322600117993829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 703052081649548802517201685 32955566327322600117993829)
                ·
                  refine ⟨6179168686372987522123843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32955566327322600117993829 6179168686372987522123843)
                  ·
                    refine ⟨9268753029559481283185765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6179168686372987522123843 9268753029559481283185765)
                    ·
                      refine ⟨1737891193042402740597331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9268753029559481283185765 1737891193042402740597331)
                      ·
                        rfl

theorem cell23_3384531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 6, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 6, 4, 1, 4].length) (baseStart_3384531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3384531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3384531 prefixEnd_3384531 := by exact prefixLift 3384531
  have htrace : WordTrace (prefixWord ++ tailWord_3384531) baseStart_3384531 baseEnd_3384531 := by
    simpa [prefixWord, tailWord_3384531, baseEnd_3384531] using wordTrace_append hprefix tailTrace_3384531
  have hstable : (prefixWord ++ tailWord_3384531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3384531).length < 2 ^ (prefixWord ++ tailWord_3384531).sum := by decide
  have hdescent : baseEnd_3384531 < baseStart_3384531 := by decide
  rcases family_descends (prefixWord ++ tailWord_3384531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3384548 : List Nat := [2, 3, 1, 1, 1, 2, 2, 2, 1, 6, 2]
def baseStart_3384548 : Nat := 118140960795 + 3384548 * 2 ^ 59
def prefixEnd_3384548 : Nat := 4983230072969 + 3 ^ 40 * 3384548 * 2
def baseEnd_3384548 : Nat := 1737899922213529174084753

theorem tailTrace_3384548 : CollatzResearch.WordTrace tailWord_3384548 prefixEnd_3384548 1737899922213529174084753 := by
  unfold tailWord_3384548
  simp only [CollatzResearch.WordTrace]
  refine ⟨61722303471184052811905149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82296404628245403749206865 61722303471184052811905149)
  ·
    refine ⟨23145863801694019804464431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61722303471184052811905149 23145863801694019804464431)
    ·
      refine ⟨34718795702541029706696647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23145863801694019804464431 34718795702541029706696647)
      ·
        refine ⟨52078193553811544560044971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34718795702541029706696647 52078193553811544560044971)
        ·
          refine ⟨78117290330717316840067457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52078193553811544560044971 78117290330717316840067457)
          ·
            refine ⟨58587967748037987630050593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78117290330717316840067457 58587967748037987630050593)
            ·
              refine ⟨43940975811028490722537945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58587967748037987630050593 43940975811028490722537945)
              ·
                refine ⟨32955731858271368041903459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43940975811028490722537945 32955731858271368041903459)
                ·
                  refine ⟨49433597787407052062855189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32955731858271368041903459 49433597787407052062855189)
                  ·
                    refine ⟨2317199896284705565446337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 49433597787407052062855189 2317199896284705565446337)
                    ·
                      refine ⟨1737899922213529174084753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2317199896284705565446337 1737899922213529174084753)
                      ·
                        rfl

theorem cell23_3384548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 2, 1, 6, 2].length) (baseStart_3384548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3384548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3384548 prefixEnd_3384548 := by exact prefixLift 3384548
  have htrace : WordTrace (prefixWord ++ tailWord_3384548) baseStart_3384548 baseEnd_3384548 := by
    simpa [prefixWord, tailWord_3384548, baseEnd_3384548] using wordTrace_append hprefix tailTrace_3384548
  have hstable : (prefixWord ++ tailWord_3384548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3384548).length < 2 ^ (prefixWord ++ tailWord_3384548).sum := by decide
  have hdescent : baseEnd_3384548 < baseStart_3384548 := by decide
  rcases family_descends (prefixWord ++ tailWord_3384548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3384558 : List Nat := [4, 1, 2, 1, 1, 1, 2, 2, 5, 4]
def baseStart_3384558 : Nat := 118140960795 + 3384558 * 2 ^ 59
def prefixEnd_3384558 : Nat := 4983230072969 + 3 ^ 40 * 3384558 * 2
def baseEnd_3384558 : Nat := 579301685673358044986569

theorem tailTrace_3384558 : CollatzResearch.WordTrace tailWord_3384558 prefixEnd_3384558 579301685673358044986569 := by
  unfold tailWord_3384558
  simp only [CollatzResearch.WordTrace]
  refine ⟨15430621459041484666459291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82296647781554584887782885 15430621459041484666459291)
  ·
    refine ⟨23145932188562226999688937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15430621459041484666459291 23145932188562226999688937)
    ·
      refine ⟨17359449141421670249766703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23145932188562226999688937 17359449141421670249766703)
      ·
        refine ⟨26039173712132505374650055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17359449141421670249766703 26039173712132505374650055)
        ·
          refine ⟨39058760568198758061975083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26039173712132505374650055 39058760568198758061975083)
          ·
            refine ⟨58588140852298137092962625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39058760568198758061975083 58588140852298137092962625)
            ·
              refine ⟨43941105639223602819721969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58588140852298137092962625 43941105639223602819721969)
              ·
                refine ⟨32955829229417702114791477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43941105639223602819721969 32955829229417702114791477)
                ·
                  refine ⟨3089608990257909573261701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32955829229417702114791477 3089608990257909573261701)
                  ·
                    refine ⟨579301685673358044986569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3089608990257909573261701 579301685673358044986569)
                    ·
                      rfl

theorem cell23_3384558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 2, 5, 4].length) (baseStart_3384558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3384558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3384558 prefixEnd_3384558 := by exact prefixLift 3384558
  have htrace : WordTrace (prefixWord ++ tailWord_3384558) baseStart_3384558 baseEnd_3384558 := by
    simpa [prefixWord, tailWord_3384558, baseEnd_3384558] using wordTrace_append hprefix tailTrace_3384558
  have hstable : (prefixWord ++ tailWord_3384558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3384558).length < 2 ^ (prefixWord ++ tailWord_3384558).sum := by decide
  have hdescent : baseEnd_3384558 < baseStart_3384558 := by decide
  rcases family_descends (prefixWord ++ tailWord_3384558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3384575 : List Nat := [1, 1, 2, 2, 1, 7, 1, 1, 3, 4]
def baseStart_3384575 : Nat := 118140960795 + 3384575 * 2 ^ 59
def prefixEnd_3384575 : Nat := 4983230072969 + 3 ^ 40 * 3384575 * 2
def baseEnd_3384575 : Nat := 579304595397066856149043

theorem tailTrace_3384575 : CollatzResearch.WordTrace tailWord_3384575 prefixEnd_3384575 579304595397066856149043 := by
  unfold tailWord_3384575
  simp only [CollatzResearch.WordTrace]
  refine ⟨123445591713270289235043179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82297061142180192823362119 123445591713270289235043179)
  ·
    refine ⟨185168387569905433852564769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123445591713270289235043179 185168387569905433852564769)
    ·
      refine ⟨138876290677429075389423577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185168387569905433852564769 138876290677429075389423577)
      ·
        refine ⟨104157218008071806542067683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138876290677429075389423577 104157218008071806542067683)
        ·
          refine ⟨156235827012107709813101525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104157218008071806542067683 156235827012107709813101525)
          ·
            refine ⟨3661777195596274448744567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 156235827012107709813101525 3661777195596274448744567)
            ·
              refine ⟨5492665793394411673116851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3661777195596274448744567 5492665793394411673116851)
              ·
                refine ⟨8238998690091617509675277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5492665793394411673116851 8238998690091617509675277)
                ·
                  refine ⟨3089624508784356566128229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8238998690091617509675277 3089624508784356566128229)
                  ·
                    refine ⟨579304595397066856149043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3089624508784356566128229 579304595397066856149043)
                    ·
                      rfl

theorem cell23_3384575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 1, 1, 3, 4].length) (baseStart_3384575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3384575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3384575 prefixEnd_3384575 := by exact prefixLift 3384575
  have htrace : WordTrace (prefixWord ++ tailWord_3384575) baseStart_3384575 baseEnd_3384575 := by
    simpa [prefixWord, tailWord_3384575, baseEnd_3384575] using wordTrace_append hprefix tailTrace_3384575
  have hstable : (prefixWord ++ tailWord_3384575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3384575).length < 2 ^ (prefixWord ++ tailWord_3384575).sum := by decide
  have hdescent : baseEnd_3384575 < baseStart_3384575 := by decide
  rcases family_descends (prefixWord ++ tailWord_3384575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3384588 : List Nat := [2, 2, 1, 2, 2, 4, 1, 3, 6]
def baseStart_3384588 : Nat := 118140960795 + 3384588 * 2 ^ 59
def prefixEnd_3384588 : Nat := 4983230072969 + 3 ^ 40 * 3384588 * 2
def baseEnd_3384588 : Nat := 193102273493301001953841

theorem tailTrace_3384588 : CollatzResearch.WordTrace tailWord_3384588 prefixEnd_3384588 193102273493301001953841 := by
  unfold tailWord_3384588
  simp only [CollatzResearch.WordTrace]
  refine ⟨61723032931111596227633209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82297377241482128303510945 61723032931111596227633209)
  ·
    refine ⟨46292274698333697170724907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61723032931111596227633209 46292274698333697170724907)
    ·
      refine ⟨69438412047500545756087361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46292274698333697170724907 69438412047500545756087361)
      ·
        refine ⟨52078809035625409317065521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69438412047500545756087361 52078809035625409317065521)
        ·
          refine ⟨39059106776719056987799141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52078809035625409317065521 39059106776719056987799141)
          ·
            refine ⟨7323582520634823185212339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39059106776719056987799141 7323582520634823185212339)
            ·
              refine ⟨10985373780952234777818509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7323582520634823185212339 10985373780952234777818509)
              ·
                refine ⟨4119515167857088041681941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10985373780952234777818509 4119515167857088041681941)
                ·
                  refine ⟨193102273493301001953841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4119515167857088041681941 193102273493301001953841)
                  ·
                    rfl

theorem cell23_3384588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 3, 6].length) (baseStart_3384588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3384588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3384588 prefixEnd_3384588 := by exact prefixLift 3384588
  have htrace : WordTrace (prefixWord ++ tailWord_3384588) baseStart_3384588 baseEnd_3384588 := by
    simpa [prefixWord, tailWord_3384588, baseEnd_3384588] using wordTrace_append hprefix tailTrace_3384588
  have hstable : (prefixWord ++ tailWord_3384588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3384588).length < 2 ^ (prefixWord ++ tailWord_3384588).sum := by decide
  have hdescent : baseEnd_3384588 < baseStart_3384588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3384588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3384648 : List Nat := [2, 1, 3, 1, 1, 2, 1, 2, 6, 4]
def baseStart_3384648 : Nat := 118140960795 + 3384648 * 2 ^ 59
def prefixEnd_3384648 : Nat := 4983230072969 + 3 ^ 40 * 3384648 * 2
def baseEnd_3384648 : Nat := 579317090092992927611431

theorem tailTrace_3384648 : CollatzResearch.WordTrace tailWord_3384648 prefixEnd_3384648 579317090092992927611431 := by
  unfold tailWord_3384648
  simp only [CollatzResearch.WordTrace]
  refine ⟨61724127121002911351225299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82298836161337215134967065 61724127121002911351225299)
  ·
    refine ⟨92586190681504367026837949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61724127121002911351225299 92586190681504367026837949)
    ·
      refine ⟨34719821505564137635064231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92586190681504367026837949 34719821505564137635064231)
      ·
        refine ⟨52079732258346206452596347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34719821505564137635064231 52079732258346206452596347)
        ·
          refine ⟨78119598387519309678894521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52079732258346206452596347 78119598387519309678894521)
          ·
            refine ⟨58589698790639482259170891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78119598387519309678894521 58589698790639482259170891)
            ·
              refine ⟨87884548185959223388756337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58589698790639482259170891 87884548185959223388756337)
              ·
                refine ⟨65913411139469417541567253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87884548185959223388756337 65913411139469417541567253)
                ·
                  refine ⟨3089691147162628947260965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 65913411139469417541567253 3089691147162628947260965)
                  ·
                    refine ⟨579317090092992927611431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3089691147162628947260965 579317090092992927611431)
                    ·
                      rfl

theorem cell23_3384648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 6, 4].length) (baseStart_3384648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3384648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3384648 prefixEnd_3384648 := by exact prefixLift 3384648
  have htrace : WordTrace (prefixWord ++ tailWord_3384648) baseStart_3384648 baseEnd_3384648 := by
    simpa [prefixWord, tailWord_3384648, baseEnd_3384648] using wordTrace_append hprefix tailTrace_3384648
  have hstable : (prefixWord ++ tailWord_3384648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3384648).length < 2 ^ (prefixWord ++ tailWord_3384648).sum := by decide
  have hdescent : baseEnd_3384648 < baseStart_3384648 := by decide
  rcases family_descends (prefixWord ++ tailWord_3384648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3384651 : List Nat := [1, 1, 1, 1, 3, 1, 1, 2, 5, 1, 6]
def baseStart_3384651 : Nat := 118140960795 + 3384651 * 2 ^ 59
def prefixEnd_3384651 : Nat := 4983230072969 + 3 ^ 40 * 3384651 * 2
def baseEnd_3384651 : Nat := 1737952810720942271096779

theorem tailTrace_3384651 : CollatzResearch.WordTrace tailWord_3384651 prefixEnd_3384651 1737952810720942271096779 := by
  unfold tailWord_3384651
  simp only [CollatzResearch.WordTrace]
  refine ⟨123448363660994954214809807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82298909107329969476539871 123448363660994954214809807)
  ·
    refine ⟨185172545491492431322214711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123448363660994954214809807 185172545491492431322214711)
    ·
      refine ⟨277758818237238646983322067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185172545491492431322214711 277758818237238646983322067)
      ·
        refine ⟨416638227355857970474983101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277758818237238646983322067 416638227355857970474983101)
        ·
          refine ⟨156239335258446738928118663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 416638227355857970474983101 156239335258446738928118663)
          ·
            refine ⟨234359002887670108392177995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156239335258446738928118663 234359002887670108392177995)
            ·
              refine ⟨351538504331505162588266993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 234359002887670108392177995 351538504331505162588266993)
              ·
                refine ⟨263653878248628871941200245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 351538504331505162588266993 263653878248628871941200245)
                ·
                  refine ⟨24717551085808956744487523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 263653878248628871941200245 24717551085808956744487523)
                  ·
                    refine ⟨37076326628713435116731285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24717551085808956744487523 37076326628713435116731285)
                    ·
                      refine ⟨1737952810720942271096779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37076326628713435116731285 1737952810720942271096779)
                      ·
                        rfl

theorem cell23_3384651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 5, 1, 6].length) (baseStart_3384651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3384651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3384651 prefixEnd_3384651 := by exact prefixLift 3384651
  have htrace : WordTrace (prefixWord ++ tailWord_3384651) baseStart_3384651 baseEnd_3384651 := by
    simpa [prefixWord, tailWord_3384651, baseEnd_3384651] using wordTrace_append hprefix tailTrace_3384651
  have hstable : (prefixWord ++ tailWord_3384651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3384651).length < 2 ^ (prefixWord ++ tailWord_3384651).sum := by decide
  have hdescent : baseEnd_3384651 < baseStart_3384651 := by decide
  rcases family_descends (prefixWord ++ tailWord_3384651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3384672 : List Nat := [2, 1, 1, 3, 4, 1, 4, 1, 1, 1, 4]
def baseStart_3384672 : Nat := 118140960795 + 3384672 * 2 ^ 59
def prefixEnd_3384672 : Nat := 4983230072969 + 3 ^ 40 * 3384672 * 2
def baseEnd_3384672 : Nat := 1737963593814686688934183

theorem tailTrace_3384672 : CollatzResearch.WordTrace tailWord_3384672 prefixEnd_3384672 1737963593814686688934183 := by
  unfold tailWord_3384672
  simp only [CollatzResearch.WordTrace]
  refine ⟨61724564796959437400662135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82299419729279249867549513 61724564796959437400662135)
  ·
    refine ⟨92586847195439156100993203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61724564796959437400662135 92586847195439156100993203)
    ·
      refine ⟨138880270793158734151489805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92586847195439156100993203 138880270793158734151489805)
      ·
        refine ⟨52080101547434525306808677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138880270793158734151489805 52080101547434525306808677)
        ·
          refine ⟨9765019040143973495026627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52080101547434525306808677 9765019040143973495026627)
          ·
            refine ⟨14647528560215960242539941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9765019040143973495026627 14647528560215960242539941)
            ·
              refine ⟨2746411605040492545476239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14647528560215960242539941 2746411605040492545476239)
              ·
                refine ⟨4119617407560738818214359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2746411605040492545476239 4119617407560738818214359)
                ·
                  refine ⟨6179426111341108227321539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4119617407560738818214359 6179426111341108227321539)
                  ·
                    refine ⟨9269139167011662340982309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6179426111341108227321539 9269139167011662340982309)
                    ·
                      refine ⟨1737963593814686688934183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9269139167011662340982309 1737963593814686688934183)
                      ·
                        rfl

theorem cell23_3384672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 4, 1, 1, 1, 4].length) (baseStart_3384672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3384672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3384672 prefixEnd_3384672 := by exact prefixLift 3384672
  have htrace : WordTrace (prefixWord ++ tailWord_3384672) baseStart_3384672 baseEnd_3384672 := by
    simpa [prefixWord, tailWord_3384672, baseEnd_3384672] using wordTrace_append hprefix tailTrace_3384672
  have hstable : (prefixWord ++ tailWord_3384672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3384672).length < 2 ^ (prefixWord ++ tailWord_3384672).sum := by decide
  have hdescent : baseEnd_3384672 < baseStart_3384672 := by decide
  rcases family_descends (prefixWord ++ tailWord_3384672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3384682 : List Nat := [3, 1, 3, 3, 2, 1, 1, 1, 4, 4]
def baseStart_3384682 : Nat := 118140960795 + 3384682 * 2 ^ 59
def prefixEnd_3384682 : Nat := 4983230072969 + 3 ^ 40 * 3384682 * 2
def baseEnd_3384682 : Nat := 579322909540410549936379

theorem tailTrace_3384682 : CollatzResearch.WordTrace tailWord_3384682 prefixEnd_3384682 579322909540410549936379 := by
  unfold tailWord_3384682
  simp only [CollatzResearch.WordTrace]
  refine ⟨30862373580970661627297075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82299662882588431006125533 30862373580970661627297075)
  ·
    refine ⟨46293560371455992440945613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30862373580970661627297075 46293560371455992440945613)
    ·
      refine ⟨17360085139295997165354605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46293560371455992440945613 17360085139295997165354605)
      ·
        refine ⟨6510031927235998937007977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17360085139295997165354605 6510031927235998937007977)
        ·
          refine ⟨4882523945426999202755983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6510031927235998937007977 4882523945426999202755983)
          ·
            refine ⟨7323785918140498804133975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4882523945426999202755983 7323785918140498804133975)
            ·
              refine ⟨10985678877210748206200963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7323785918140498804133975 10985678877210748206200963)
              ·
                refine ⟨16478518315816122309301445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10985678877210748206200963 16478518315816122309301445)
                ·
                  refine ⟨3089722184215522932994021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16478518315816122309301445 3089722184215522932994021)
                  ·
                    refine ⟨579322909540410549936379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3089722184215522932994021 579322909540410549936379)
                    ·
                      rfl

theorem cell23_3384682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 1, 4, 4].length) (baseStart_3384682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3384682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3384682 prefixEnd_3384682 := by exact prefixLift 3384682
  have htrace : WordTrace (prefixWord ++ tailWord_3384682) baseStart_3384682 baseEnd_3384682 := by
    simpa [prefixWord, tailWord_3384682, baseEnd_3384682] using wordTrace_append hprefix tailTrace_3384682
  have hstable : (prefixWord ++ tailWord_3384682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3384682).length < 2 ^ (prefixWord ++ tailWord_3384682).sum := by decide
  have hdescent : baseEnd_3384682 < baseStart_3384682 := by decide
  rcases family_descends (prefixWord ++ tailWord_3384682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3384689 : List Nat := [1, 2, 2, 2, 1, 2, 4, 4, 1, 2, 2]
def baseStart_3384689 : Nat := 118140960795 + 3384689 * 2 ^ 59
def prefixEnd_3384689 : Nat := 4983230072969 + 3 ^ 40 * 3384689 * 2
def baseEnd_3384689 : Nat := 1737972322985813122421605

theorem tailTrace_3384689 : CollatzResearch.WordTrace tailWord_3384689 prefixEnd_3384689 1737972322985813122421605 := by
  unfold tailWord_3384689
  simp only [CollatzResearch.WordTrace]
  refine ⟨123449749634857286704693121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82299833089904857803128747 123449749634857286704693121)
  ·
    refine ⟨92587312226142965028519841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123449749634857286704693121 92587312226142965028519841)
    ·
      refine ⟨69440484169607223771389881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92587312226142965028519841 69440484169607223771389881)
      ·
        refine ⟨52080363127205417828542411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69440484169607223771389881 52080363127205417828542411)
        ·
          refine ⟨78120544690808126742813617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52080363127205417828542411 78120544690808126742813617)
          ·
            refine ⟨58590408518106095057110213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78120544690808126742813617 58590408518106095057110213)
            ·
              refine ⟨10985701597144892823208165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58590408518106095057110213 10985701597144892823208165)
              ·
                refine ⟨2059819049464667404351531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10985701597144892823208165 2059819049464667404351531)
                ·
                  refine ⟨3089728574197001106527297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2059819049464667404351531 3089728574197001106527297)
                  ·
                    refine ⟨2317296430647750829895473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3089728574197001106527297 2317296430647750829895473)
                    ·
                      refine ⟨1737972322985813122421605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2317296430647750829895473 1737972322985813122421605)
                      ·
                        rfl

theorem cell23_3384689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 4, 1, 2, 2].length) (baseStart_3384689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3384689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3384689 prefixEnd_3384689 := by exact prefixLift 3384689
  have htrace : WordTrace (prefixWord ++ tailWord_3384689) baseStart_3384689 baseEnd_3384689 := by
    simpa [prefixWord, tailWord_3384689, baseEnd_3384689] using wordTrace_append hprefix tailTrace_3384689
  have hstable : (prefixWord ++ tailWord_3384689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3384689).length < 2 ^ (prefixWord ++ tailWord_3384689).sum := by decide
  have hdescent : baseEnd_3384689 < baseStart_3384689 := by decide
  rcases family_descends (prefixWord ++ tailWord_3384689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3384706 : List Nat := [3, 4, 2, 1, 1, 1, 2, 2, 3, 2, 2]
def baseStart_3384706 : Nat := 118140960795 + 3384706 * 2 ^ 59
def prefixEnd_3384706 : Nat := 4983230072969 + 3 ^ 40 * 3384706 * 2
def baseEnd_3384706 : Nat := 1737981052156939555909027

theorem tailTrace_3384706 : CollatzResearch.WordTrace tailWord_3384706 prefixEnd_3384706 1737981052156939555909027 := by
  unfold tailWord_3384706
  simp only [CollatzResearch.WordTrace]
  refine ⟨30862592418948924652015493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82300246450530465738707981 30862592418948924652015493)
  ·
    refine ⟨5786736078552923372252905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30862592418948924652015493 5786736078552923372252905)
    ·
      refine ⟨4340052058914692529189679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5786736078552923372252905 4340052058914692529189679)
      ·
        refine ⟨6510078088372038793784519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4340052058914692529189679 6510078088372038793784519)
        ·
          refine ⟨9765117132558058190676779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6510078088372038793784519 9765117132558058190676779)
          ·
            refine ⟨14647675698837087286015169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9765117132558058190676779 14647675698837087286015169)
            ·
              refine ⟨10985756774127815464511377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14647675698837087286015169 10985756774127815464511377)
              ·
                refine ⟨8239317580595861598383533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10985756774127815464511377 8239317580595861598383533)
                ·
                  refine ⟨3089744092723448099393825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8239317580595861598383533 3089744092723448099393825)
                  ·
                    refine ⟨2317308069542586074545369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3089744092723448099393825 2317308069542586074545369)
                    ·
                      refine ⟨1737981052156939555909027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2317308069542586074545369 1737981052156939555909027)
                      ·
                        rfl

theorem cell23_3384706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 2, 3, 2, 2].length) (baseStart_3384706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3384706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3384706 prefixEnd_3384706 := by exact prefixLift 3384706
  have htrace : WordTrace (prefixWord ++ tailWord_3384706) baseStart_3384706 baseEnd_3384706 := by
    simpa [prefixWord, tailWord_3384706, baseEnd_3384706] using wordTrace_append hprefix tailTrace_3384706
  have hstable : (prefixWord ++ tailWord_3384706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3384706).length < 2 ^ (prefixWord ++ tailWord_3384706).sum := by decide
  have hdescent : baseEnd_3384706 < baseStart_3384706 := by decide
  rcases family_descends (prefixWord ++ tailWord_3384706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3384768 : List Nat := [2, 1, 1, 2, 3, 1, 2, 4, 7]
def baseStart_3384768 : Nat := 118140960795 + 3384768 * 2 ^ 59
def prefixEnd_3384768 : Nat := 4983230072969 + 3 ^ 40 * 3384768 * 2
def baseEnd_3384768 : Nat := 193112543106390923703749

theorem tailTrace_3384768 : CollatzResearch.WordTrace tailWord_3384768 prefixEnd_3384768 193112543106390923703749 := by
  unfold tailWord_3384768
  simp only [CollatzResearch.WordTrace]
  refine ⟨61726315500785541598409479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82301754001047388797879305 61726315500785541598409479)
  ·
    refine ⟨92589473251178312397614219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61726315500785541598409479 92589473251178312397614219)
    ·
      refine ⟨138884209876767468596421329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92589473251178312397614219 138884209876767468596421329)
      ·
        refine ⟨104163157407575601447315997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138884209876767468596421329 104163157407575601447315997)
        ·
          refine ⟨39061184027840850542743499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104163157407575601447315997 39061184027840850542743499)
          ·
            refine ⟨58591776041761275814115249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39061184027840850542743499 58591776041761275814115249)
            ·
              refine ⟨43943832031320956860586437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58591776041761275814115249 43943832031320956860586437)
              ·
                refine ⟨8239468505872679411359957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43943832031320956860586437 8239468505872679411359957)
                ·
                  refine ⟨193112543106390923703749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8239468505872679411359957 193112543106390923703749)
                  ·
                    rfl

theorem cell23_3384768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 4, 7].length) (baseStart_3384768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3384768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3384768 prefixEnd_3384768 := by exact prefixLift 3384768
  have htrace : WordTrace (prefixWord ++ tailWord_3384768) baseStart_3384768 baseEnd_3384768 := by
    simpa [prefixWord, tailWord_3384768, baseEnd_3384768] using wordTrace_append hprefix tailTrace_3384768
  have hstable : (prefixWord ++ tailWord_3384768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3384768).length < 2 ^ (prefixWord ++ tailWord_3384768).sum := by decide
  have hdescent : baseEnd_3384768 < baseStart_3384768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3384768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3384835 : List Nat := [1, 1, 1, 3, 2, 1, 2, 5, 2, 1, 4]
def baseStart_3384835 : Nat := 118140960795 + 3384835 * 2 ^ 59
def prefixEnd_3384835 : Nat := 4983230072969 + 3 ^ 40 * 3384835 * 2
def baseEnd_3384835 : Nat := 1738047291161369551195933

theorem tailTrace_3384835 : CollatzResearch.WordTrace tailWord_3384835 prefixEnd_3384835 1738047291161369551195933 := by
  unfold tailWord_3384835
  simp only [CollatzResearch.WordTrace]
  refine ⟨123455074692328353639507959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82303383128218902426338639 123455074692328353639507959)
  ·
    refine ⟨185182612038492530459261939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123455074692328353639507959 185182612038492530459261939)
    ·
      refine ⟨277773918057738795688892909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185182612038492530459261939 277773918057738795688892909)
      ·
        refine ⟨104165219271652048383334841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 277773918057738795688892909 104165219271652048383334841)
        ·
          refine ⟨78123914453739036287501131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104165219271652048383334841 78123914453739036287501131)
          ·
            refine ⟨117185871680608554431251697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78123914453739036287501131 117185871680608554431251697)
            ·
              refine ⟨87889403760456415823438773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117185871680608554431251697 87889403760456415823438773)
              ·
                refine ⟨8239631602542788983447385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 87889403760456415823438773 8239631602542788983447385)
                ·
                  refine ⟨6179723701907091737585539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8239631602542788983447385 6179723701907091737585539)
                  ·
                    refine ⟨9269585552860637606378309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6179723701907091737585539 9269585552860637606378309)
                    ·
                      refine ⟨1738047291161369551195933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9269585552860637606378309 1738047291161369551195933)
                      ·
                        rfl

theorem cell23_3384835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 5, 2, 1, 4].length) (baseStart_3384835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3384835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3384835 prefixEnd_3384835 := by exact prefixLift 3384835
  have htrace : WordTrace (prefixWord ++ tailWord_3384835) baseStart_3384835 baseEnd_3384835 := by
    simpa [prefixWord, tailWord_3384835, baseEnd_3384835] using wordTrace_append hprefix tailTrace_3384835
  have hstable : (prefixWord ++ tailWord_3384835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3384835).length < 2 ^ (prefixWord ++ tailWord_3384835).sum := by decide
  have hdescent : baseEnd_3384835 < baseStart_3384835 := by decide
  rcases family_descends (prefixWord ++ tailWord_3384835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3384919 : List Nat := [1, 1, 3, 2, 2, 3, 3, 1, 3, 1, 3]
def baseStart_3384919 : Nat := 118140960795 + 3384919 * 2 ^ 59
def prefixEnd_3384919 : Nat := 4983230072969 + 3 ^ 40 * 3384919 * 2
def baseEnd_3384919 : Nat := 1738090423536347222545547

theorem tailTrace_3384919 : CollatzResearch.WordTrace tailWord_3384919 prefixEnd_3384919 1738090423536347222545547 := by
  unfold tailWord_3384919
  simp only [CollatzResearch.WordTrace]
  refine ⟨123458138424024035985565811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82305425616016023990377207 123458138424024035985565811)
  ·
    refine ⟨185187207636036053978348717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123458138424024035985565811 185187207636036053978348717)
    ·
      refine ⟨69445202863513520241880769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185187207636036053978348717 69445202863513520241880769)
      ·
        refine ⟨52083902147635140181410577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69445202863513520241880769 52083902147635140181410577)
        ·
          refine ⟨39062926610726355136057933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52083902147635140181410577 39062926610726355136057933)
          ·
            refine ⟨14648597479022383176021725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39062926610726355136057933 14648597479022383176021725)
            ·
              refine ⟨5493224054633393691008147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14648597479022383176021725 5493224054633393691008147)
              ·
                refine ⟨8239836081950090536512221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5493224054633393691008147 8239836081950090536512221)
                ·
                  refine ⟨3089938530731283951192083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8239836081950090536512221 3089938530731283951192083)
                  ·
                    refine ⟨4634907796096925926788125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3089938530731283951192083 4634907796096925926788125)
                    ·
                      refine ⟨1738090423536347222545547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4634907796096925926788125 1738090423536347222545547)
                      ·
                        rfl

theorem cell23_3384919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 3, 1, 3, 1, 3].length) (baseStart_3384919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3384919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3384919 prefixEnd_3384919 := by exact prefixLift 3384919
  have htrace : WordTrace (prefixWord ++ tailWord_3384919) baseStart_3384919 baseEnd_3384919 := by
    simpa [prefixWord, tailWord_3384919, baseEnd_3384919] using wordTrace_append hprefix tailTrace_3384919
  have hstable : (prefixWord ++ tailWord_3384919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3384919).length < 2 ^ (prefixWord ++ tailWord_3384919).sum := by decide
  have hdescent : baseEnd_3384919 < baseStart_3384919 := by decide
  rcases family_descends (prefixWord ++ tailWord_3384919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3384945 : List Nat := [1, 2, 2, 2, 1, 1, 1, 4, 3, 1, 5]
def baseStart_3384945 : Nat := 118140960795 + 3384945 * 2 ^ 59
def prefixEnd_3384945 : Nat := 4983230072969 + 3 ^ 40 * 3384945 * 2
def baseEnd_3384945 : Nat := 1738103774033364120820427

theorem tailTrace_3384945 : CollatzResearch.WordTrace tailWord_3384945 prefixEnd_3384945 1738103774033364120820427 := by
  unfold tailWord_3384945
  simp only [CollatzResearch.WordTrace]
  refine ⟨123459086721929842426012289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82306057814619894950674859 123459086721929842426012289)
  ·
    refine ⟨92594315041447381819509217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123459086721929842426012289 92594315041447381819509217)
    ·
      refine ⟨69445736281085536364631913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92594315041447381819509217 69445736281085536364631913)
      ·
        refine ⟨52084302210814152273473935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69445736281085536364631913 52084302210814152273473935)
        ·
          refine ⟨78126453316221228410210903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52084302210814152273473935 78126453316221228410210903)
          ·
            refine ⟨117189679974331842615316355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78126453316221228410210903 117189679974331842615316355)
            ·
              refine ⟨175784519961497763922974533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117189679974331842615316355 175784519961497763922974533)
              ·
                refine ⟨32959597492780830735557725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 175784519961497763922974533 32959597492780830735557725)
                ·
                  refine ⟨12359849059792811525834147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32959597492780830735557725 12359849059792811525834147)
                  ·
                    refine ⟨18539773589689217288751221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12359849059792811525834147 18539773589689217288751221)
                    ·
                      refine ⟨1738103774033364120820427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18539773589689217288751221 1738103774033364120820427)
                      ·
                        rfl

theorem cell23_3384945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 4, 3, 1, 5].length) (baseStart_3384945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3384945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3384945 prefixEnd_3384945 := by exact prefixLift 3384945
  have htrace : WordTrace (prefixWord ++ tailWord_3384945) baseStart_3384945 baseEnd_3384945 := by
    simpa [prefixWord, tailWord_3384945, baseEnd_3384945] using wordTrace_append hprefix tailTrace_3384945
  have hstable : (prefixWord ++ tailWord_3384945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3384945).length < 2 ^ (prefixWord ++ tailWord_3384945).sum := by decide
  have hdescent : baseEnd_3384945 < baseStart_3384945 := by decide
  rcases family_descends (prefixWord ++ tailWord_3384945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3384946 : List Nat := [3, 2, 1, 2, 3, 2, 2, 1, 2, 3, 2]
def baseStart_3384946 : Nat := 118140960795 + 3384946 * 2 ^ 59
def prefixEnd_3384946 : Nat := 4983230072969 + 3 ^ 40 * 3384946 * 2
def baseEnd_3384946 : Nat := 1738104287514018616907923

theorem tailTrace_3384946 : CollatzResearch.WordTrace tailWord_3384946 prefixEnd_3384946 1738104287514018616907923 := by
  unfold tailWord_3384946
  simp only [CollatzResearch.WordTrace]
  refine ⟨30864780798731554899199673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82306082129950813064532461 30864780798731554899199673)
  ·
    refine ⟨23148585599048666174399755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30864780798731554899199673 23148585599048666174399755)
    ·
      refine ⟨34722878398572999261599633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23148585599048666174399755 34722878398572999261599633)
      ·
        refine ⟨26042158798929749446199725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34722878398572999261599633 26042158798929749446199725)
        ·
          refine ⟨9765809549598656042324897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26042158798929749446199725 9765809549598656042324897)
          ·
            refine ⟨7324357162198992031743673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9765809549598656042324897 7324357162198992031743673)
            ·
              refine ⟨5493267871649244023807755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7324357162198992031743673 5493267871649244023807755)
              ·
                refine ⟨8239901807473866035711633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5493267871649244023807755 8239901807473866035711633)
                ·
                  refine ⟨6179926355605399526783725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8239901807473866035711633 6179926355605399526783725)
                  ·
                    refine ⟨2317472383352024822543897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6179926355605399526783725 2317472383352024822543897)
                    ·
                      refine ⟨1738104287514018616907923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2317472383352024822543897 1738104287514018616907923)
                      ·
                        rfl

theorem cell23_3384946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 2, 1, 2, 3, 2].length) (baseStart_3384946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3384946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3384946 prefixEnd_3384946 := by exact prefixLift 3384946
  have htrace : WordTrace (prefixWord ++ tailWord_3384946) baseStart_3384946 baseEnd_3384946 := by
    simpa [prefixWord, tailWord_3384946, baseEnd_3384946] using wordTrace_append hprefix tailTrace_3384946
  have hstable : (prefixWord ++ tailWord_3384946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3384946).length < 2 ^ (prefixWord ++ tailWord_3384946).sum := by decide
  have hdescent : baseEnd_3384946 < baseStart_3384946 := by decide
  rcases family_descends (prefixWord ++ tailWord_3384946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3384970 : List Nat := [3, 1, 2, 3, 2, 3, 2, 2, 1, 1, 3]
def baseStart_3384970 : Nat := 118140960795 + 3384970 * 2 ^ 59
def prefixEnd_3384970 : Nat := 4983230072969 + 3 ^ 40 * 3384970 * 2
def baseEnd_3384970 : Nat := 1738116611049726523007813

theorem tailTrace_3384970 : CollatzResearch.WordTrace tailWord_3384970 prefixEnd_3384970 1738116611049726523007813 := by
  unfold tailWord_3384970
  simp only [CollatzResearch.WordTrace]
  refine ⟨30864999636709817923918091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82306665697892847797114909 30864999636709817923918091)
  ·
    refine ⟨46297499455064726885877137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30864999636709817923918091 46297499455064726885877137)
    ·
      refine ⟨34723124591298545164407853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46297499455064726885877137 34723124591298545164407853)
      ·
        refine ⟨13021171721736954436652945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34723124591298545164407853 13021171721736954436652945)
        ·
          refine ⟨9765878791302715827489709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13021171721736954436652945 9765878791302715827489709)
          ·
            refine ⟨3662204546738518435308641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9765878791302715827489709 3662204546738518435308641)
            ·
              refine ⟨2746653410053888826481481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3662204546738518435308641 2746653410053888826481481)
              ·
                refine ⟨2059990057540416619861111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2746653410053888826481481 2059990057540416619861111)
                ·
                  refine ⟨3089985086310624929791667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2059990057540416619861111 3089985086310624929791667)
                  ·
                    refine ⟨4634977629465937394687501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3089985086310624929791667 4634977629465937394687501)
                    ·
                      refine ⟨1738116611049726523007813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4634977629465937394687501 1738116611049726523007813)
                      ·
                        rfl

theorem cell23_3384970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 2, 2, 1, 1, 3].length) (baseStart_3384970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3384970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3384970 prefixEnd_3384970 := by exact prefixLift 3384970
  have htrace : WordTrace (prefixWord ++ tailWord_3384970) baseStart_3384970 baseEnd_3384970 := by
    simpa [prefixWord, tailWord_3384970, baseEnd_3384970] using wordTrace_append hprefix tailTrace_3384970
  have hstable : (prefixWord ++ tailWord_3384970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3384970).length < 2 ^ (prefixWord ++ tailWord_3384970).sum := by decide
  have hdescent : baseEnd_3384970 < baseStart_3384970 := by decide
  rcases family_descends (prefixWord ++ tailWord_3384970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3384995 : List Nat := [1, 1, 1, 4, 1, 1, 3, 2, 2, 7]
def baseStart_3384995 : Nat := 118140960795 + 3384995 * 2 ^ 59
def prefixEnd_3384995 : Nat := 4983230072969 + 3 ^ 40 * 3384995 * 2
def baseEnd_3384995 : Nat := 579376482688696308398399

theorem tailTrace_3384995 : CollatzResearch.WordTrace tailWord_3384995 prefixEnd_3384995 579376482688696308398399 := by
  unfold tailWord_3384995
  simp only [CollatzResearch.WordTrace]
  refine ⟨123460910371748700965332439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82307273581165800643554959 123460910371748700965332439)
  ·
    refine ⟨185191365557623051447998659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123460910371748700965332439 185191365557623051447998659)
    ·
      refine ⟨277787048336434577171997989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185191365557623051447998659 277787048336434577171997989)
      ·
        refine ⟨52085071563081483219749623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 277787048336434577171997989 52085071563081483219749623)
        ·
          refine ⟨78127607344622224829624435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52085071563081483219749623 78127607344622224829624435)
          ·
            refine ⟨117191411016933337244436653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78127607344622224829624435 117191411016933337244436653)
            ·
              refine ⟨43946779131350001466663745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117191411016933337244436653 43946779131350001466663745)
              ·
                refine ⟨32960084348512501099997809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43946779131350001466663745 32960084348512501099997809)
                ·
                  refine ⟨24720063261384375824998357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32960084348512501099997809 24720063261384375824998357)
                  ·
                    refine ⟨579376482688696308398399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24720063261384375824998357 579376482688696308398399)
                    ·
                      rfl

theorem cell23_3384995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 2, 2, 7].length) (baseStart_3384995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3384995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3384995 prefixEnd_3384995 := by exact prefixLift 3384995
  have htrace : WordTrace (prefixWord ++ tailWord_3384995) baseStart_3384995 baseEnd_3384995 := by
    simpa [prefixWord, tailWord_3384995, baseEnd_3384995] using wordTrace_append hprefix tailTrace_3384995
  have hstable : (prefixWord ++ tailWord_3384995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3384995).length < 2 ^ (prefixWord ++ tailWord_3384995).sum := by decide
  have hdescent : baseEnd_3384995 < baseStart_3384995 := by decide
  rcases family_descends (prefixWord ++ tailWord_3384995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3385066 : List Nat := [3, 1, 3, 1, 1, 1, 3, 2, 4, 2, 2]
def baseStart_3385066 : Nat := 118140960795 + 3385066 * 2 ^ 59
def prefixEnd_3385066 : Nat := 4983230072969 + 3 ^ 40 * 3385066 * 2
def baseEnd_3385066 : Nat := 1738165905192558147407371

theorem tailTrace_3385066 : CollatzResearch.WordTrace tailWord_3385066 prefixEnd_3385066 1738165905192558147407371 := by
  unfold tailWord_3385066
  simp only [CollatzResearch.WordTrace]
  refine ⟨30865874988622870022791763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82308999969660986727444701 30865874988622870022791763)
  ·
    refine ⟨46298812482934305034187645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30865874988622870022791763 46298812482934305034187645)
    ·
      refine ⟨17362054681100364387820367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46298812482934305034187645 17362054681100364387820367)
      ·
        refine ⟨26043082021650546581730551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17362054681100364387820367 26043082021650546581730551)
        ·
          refine ⟨39064623032475819872595827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26043082021650546581730551 39064623032475819872595827)
          ·
            refine ⟨58596934548713729808893741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39064623032475819872595827 58596934548713729808893741)
            ·
              refine ⟨21973850455767648678335153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58596934548713729808893741 21973850455767648678335153)
              ·
                refine ⟨16480387841825736508751365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21973850455767648678335153 16480387841825736508751365)
                ·
                  refine ⟨3090072720342325595390881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16480387841825736508751365 3090072720342325595390881)
                  ·
                    refine ⟨2317554540256744196543161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3090072720342325595390881 2317554540256744196543161)
                    ·
                      refine ⟨1738165905192558147407371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2317554540256744196543161 1738165905192558147407371)
                      ·
                        rfl

theorem cell23_3385066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 2, 4, 2, 2].length) (baseStart_3385066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3385066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3385066 prefixEnd_3385066 := by exact prefixLift 3385066
  have htrace : WordTrace (prefixWord ++ tailWord_3385066) baseStart_3385066 baseEnd_3385066 := by
    simpa [prefixWord, tailWord_3385066, baseEnd_3385066] using wordTrace_append hprefix tailTrace_3385066
  have hstable : (prefixWord ++ tailWord_3385066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3385066).length < 2 ^ (prefixWord ++ tailWord_3385066).sum := by decide
  have hdescent : baseEnd_3385066 < baseStart_3385066 := by decide
  rcases family_descends (prefixWord ++ tailWord_3385066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3385069 : List Nat := [1, 5, 1, 2, 1, 3, 1, 1, 2, 1, 5]
def baseStart_3385069 : Nat := 118140960795 + 3385069 * 2 ^ 59
def prefixEnd_3385069 : Nat := 4983230072969 + 3 ^ 40 * 3385069 * 2
def baseEnd_3385069 : Nat := 1738167445634521635669857

theorem tailTrace_3385069 : CollatzResearch.WordTrace tailWord_3385069 prefixEnd_3385069 1738167445634521635669857 := by
  unfold tailWord_3385069
  simp only [CollatzResearch.WordTrace]
  refine ⟨123463609373480611603526261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82309072915653741069017507 123463609373480611603526261)
  ·
    refine ⟨11574713378763807337830587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 123463609373480611603526261 11574713378763807337830587)
    ·
      refine ⟨17362070068145711006745881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11574713378763807337830587 17362070068145711006745881)
      ·
        refine ⟨13021552551109283255059411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17362070068145711006745881 13021552551109283255059411)
        ·
          refine ⟨19532328826663924882589117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13021552551109283255059411 19532328826663924882589117)
          ·
            refine ⟨7324623309998971830970919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19532328826663924882589117 7324623309998971830970919)
            ·
              refine ⟨10986934964998457746456379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7324623309998971830970919 10986934964998457746456379)
              ·
                refine ⟨16480402447497686619684569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10986934964998457746456379 16480402447497686619684569)
                ·
                  refine ⟨12360301835623264964763427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16480402447497686619684569 12360301835623264964763427)
                  ·
                    refine ⟨18540452753434897447145141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12360301835623264964763427 18540452753434897447145141)
                    ·
                      refine ⟨1738167445634521635669857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18540452753434897447145141 1738167445634521635669857)
                      ·
                        rfl

theorem cell23_3385069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_3385069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3385069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3385069 prefixEnd_3385069 := by exact prefixLift 3385069
  have htrace : WordTrace (prefixWord ++ tailWord_3385069) baseStart_3385069 baseEnd_3385069 := by
    simpa [prefixWord, tailWord_3385069, baseEnd_3385069] using wordTrace_append hprefix tailTrace_3385069
  have hstable : (prefixWord ++ tailWord_3385069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3385069).length < 2 ^ (prefixWord ++ tailWord_3385069).sum := by decide
  have hdescent : baseEnd_3385069 < baseStart_3385069 := by decide
  rcases family_descends (prefixWord ++ tailWord_3385069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3385089 : List Nat := [1, 2, 4, 1, 1, 1, 2, 6, 5]
def baseStart_3385089 : Nat := 118140960795 + 3385089 * 2 ^ 59
def prefixEnd_3385089 : Nat := 4983230072969 + 3 ^ 40 * 3385089 * 2
def baseEnd_3385089 : Nat := 193130857249734617491085

theorem tailTrace_3385089 : CollatzResearch.WordTrace tailWord_3385089 prefixEnd_3385089 193130857249734617491085 := by
  unfold tailWord_3385089
  simp only [CollatzResearch.WordTrace]
  refine ⟨123464338833408155019254321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82309559222272103346169547 123464338833408155019254321)
  ·
    refine ⟨92598254125056116264440741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123464338833408155019254321 92598254125056116264440741)
    ·
      refine ⟨17362172648448021799582639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92598254125056116264440741 17362172648448021799582639)
      ·
        refine ⟨26043258972672032699373959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17362172648448021799582639 26043258972672032699373959)
        ·
          refine ⟨39064888459008049049060939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26043258972672032699373959 39064888459008049049060939)
          ·
            refine ⟨58597332688512073573591409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39064888459008049049060939 58597332688512073573591409)
            ·
              refine ⟨43947999516384055180193557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58597332688512073573591409 43947999516384055180193557)
              ·
                refine ⟨2060062477330502586571573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 43947999516384055180193557 2060062477330502586571573)
                ·
                  refine ⟨193130857249734617491085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2060062477330502586571573 193130857249734617491085)
                  ·
                    rfl

theorem cell23_3385089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 6, 5].length) (baseStart_3385089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3385089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3385089 prefixEnd_3385089 := by exact prefixLift 3385089
  have htrace : WordTrace (prefixWord ++ tailWord_3385089) baseStart_3385089 baseEnd_3385089 := by
    simpa [prefixWord, tailWord_3385089, baseEnd_3385089] using wordTrace_append hprefix tailTrace_3385089
  have hstable : (prefixWord ++ tailWord_3385089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3385089).length < 2 ^ (prefixWord ++ tailWord_3385089).sum := by decide
  have hdescent : baseEnd_3385089 < baseStart_3385089 := by decide
  rcases family_descends (prefixWord ++ tailWord_3385089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3385102 : List Nat := [4, 1, 1, 2, 1, 1, 2, 1, 3, 7]
def baseStart_3385102 : Nat := 118140960795 + 3385102 * 2 ^ 59
def prefixEnd_3385102 : Nat := 4983230072969 + 3 ^ 40 * 3385102 * 2
def baseEnd_3385102 : Nat := 579394796832040002185735

theorem tailTrace_3385102 : CollatzResearch.WordTrace tailWord_3385102 prefixEnd_3385102 579394796832040002185735 := by
  unfold tailWord_3385102
  simp only [CollatzResearch.WordTrace]
  refine ⟨15433101622795132279934695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82309875321574038826318373 15433101622795132279934695)
  ·
    refine ⟨23149652434192698419902043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15433101622795132279934695 23149652434192698419902043)
    ·
      refine ⟨34724478651289047629853065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23149652434192698419902043 34724478651289047629853065)
      ·
        refine ⟨26043358988466785722389799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34724478651289047629853065 26043358988466785722389799)
        ·
          refine ⟨39065038482700178583584699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26043358988466785722389799 39065038482700178583584699)
          ·
            refine ⟨58597557724050267875377049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39065038482700178583584699 58597557724050267875377049)
            ·
              refine ⟨43948168293037700906532787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58597557724050267875377049 43948168293037700906532787)
              ·
                refine ⟨65922252439556551359799181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43948168293037700906532787 65922252439556551359799181)
                ·
                  refine ⟨24720844664833706759924693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65922252439556551359799181 24720844664833706759924693)
                  ·
                    refine ⟨579394796832040002185735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24720844664833706759924693 579394796832040002185735)
                    ·
                      rfl

theorem cell23_3385102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 3, 7].length) (baseStart_3385102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3385102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3385102 prefixEnd_3385102 := by exact prefixLift 3385102
  have htrace : WordTrace (prefixWord ++ tailWord_3385102) baseStart_3385102 baseEnd_3385102 := by
    simpa [prefixWord, tailWord_3385102, baseEnd_3385102] using wordTrace_append hprefix tailTrace_3385102
  have hstable : (prefixWord ++ tailWord_3385102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3385102).length < 2 ^ (prefixWord ++ tailWord_3385102).sum := by decide
  have hdescent : baseEnd_3385102 < baseStart_3385102 := by decide
  rcases family_descends (prefixWord ++ tailWord_3385102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3385119 : List Nat := [1, 1, 2, 4, 2, 1, 4, 1, 2, 5]
def baseStart_3385119 : Nat := 118140960795 + 3385119 * 2 ^ 59
def prefixEnd_3385119 : Nat := 4983230072969 + 3 ^ 40 * 3385119 * 2
def baseEnd_3385119 : Nat := 579397706555748813348209

theorem tailTrace_3385119 : CollatzResearch.WordTrace tailWord_3385119 prefixEnd_3385119 579397706555748813348209 := by
  unfold tailWord_3385119
  simp only [CollatzResearch.WordTrace]
  refine ⟨123465433023299470142846411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82310288682199646761897607 123465433023299470142846411)
  ·
    refine ⟨185198149534949205214269617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123465433023299470142846411 185198149534949205214269617)
    ·
      refine ⟨138898612151211903910702213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185198149534949205214269617 138898612151211903910702213)
      ·
        refine ⟨26043489778352231983256665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 138898612151211903910702213 26043489778352231983256665)
        ·
          refine ⟨19532617333764173987442499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26043489778352231983256665 19532617333764173987442499)
          ·
            refine ⟨29298926000646260981163749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19532617333764173987442499 29298926000646260981163749)
            ·
              refine ⟨5493548625121173933968203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29298926000646260981163749 5493548625121173933968203)
              ·
                refine ⟨8240322937681760900952305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5493548625121173933968203 8240322937681760900952305)
                ·
                  refine ⟨6180242203261320675714229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8240322937681760900952305 6180242203261320675714229)
                  ·
                    refine ⟨579397706555748813348209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6180242203261320675714229 579397706555748813348209)
                    ·
                      rfl

theorem cell23_3385119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 4, 1, 2, 5].length) (baseStart_3385119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3385119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3385119 prefixEnd_3385119 := by exact prefixLift 3385119
  have htrace : WordTrace (prefixWord ++ tailWord_3385119) baseStart_3385119 baseEnd_3385119 := by
    simpa [prefixWord, tailWord_3385119, baseEnd_3385119] using wordTrace_append hprefix tailTrace_3385119
  have hstable : (prefixWord ++ tailWord_3385119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3385119).length < 2 ^ (prefixWord ++ tailWord_3385119).sum := by decide
  have hdescent : baseEnd_3385119 < baseStart_3385119 := by decide
  rcases family_descends (prefixWord ++ tailWord_3385119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3385140 : List Nat := [2, 5, 1, 1, 2, 3, 2, 2, 5]
def baseStart_3385140 : Nat := 118140960795 + 3385140 * 2 ^ 59
def prefixEnd_3385140 : Nat := 4983230072969 + 3 ^ 40 * 3385140 * 2
def baseEnd_3385140 : Nat := 193133766973443428653559

theorem tailTrace_3385140 : CollatzResearch.WordTrace tailWord_3385140 prefixEnd_3385140 193133766973443428653559 := by
  unfold tailWord_3385140
  simp only [CollatzResearch.WordTrace]
  refine ⟨61733099478111695364680437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82310799304148927152907249 61733099478111695364680437)
  ·
    refine ⟨5787478076072971440438791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 61733099478111695364680437 5787478076072971440438791)
    ·
      refine ⟨8681217114109457160658187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5787478076072971440438791 8681217114109457160658187)
      ·
        refine ⟨13021825671164185740987281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8681217114109457160658187 13021825671164185740987281)
        ·
          refine ⟨9766369253373139305740461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13021825671164185740987281 9766369253373139305740461)
          ·
            refine ⟨3662388470014927239652673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9766369253373139305740461 3662388470014927239652673)
            ·
              refine ⟨2746791352511195429739505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3662388470014927239652673 2746791352511195429739505)
              ·
                refine ⟨2060093514383396572304629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2746791352511195429739505 2060093514383396572304629)
                ·
                  refine ⟨193133766973443428653559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2060093514383396572304629 193133766973443428653559)
                  ·
                    rfl

theorem cell23_3385140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 2, 2, 5].length) (baseStart_3385140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3385140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3385140 prefixEnd_3385140 := by exact prefixLift 3385140
  have htrace : WordTrace (prefixWord ++ tailWord_3385140) baseStart_3385140 baseEnd_3385140 := by
    simpa [prefixWord, tailWord_3385140, baseEnd_3385140] using wordTrace_append hprefix tailTrace_3385140
  have hstable : (prefixWord ++ tailWord_3385140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3385140).length < 2 ^ (prefixWord ++ tailWord_3385140).sum := by decide
  have hdescent : baseEnd_3385140 < baseStart_3385140 := by decide
  rcases family_descends (prefixWord ++ tailWord_3385140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3385152 : List Nat := [2, 1, 1, 2, 2, 1, 1, 1, 4, 4, 4]
def baseStart_3385152 : Nat := 118140960795 + 3385152 * 2 ^ 59
def prefixEnd_3385152 : Nat := 4983230072969 + 3 ^ 40 * 3385152 * 2
def baseEnd_3385152 : Nat := 1738210064528844810931975

theorem tailTrace_3385152 : CollatzResearch.WordTrace tailWord_3385152 prefixEnd_3385152 1738210064528844810931975 := by
  unfold tailWord_3385152
  simp only [CollatzResearch.WordTrace]
  refine ⟨61733318316089958389398855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82311091088119944519198473 61733318316089958389398855)
  ·
    refine ⟨92599977474134937584098283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61733318316089958389398855 92599977474134937584098283)
    ·
      refine ⟨138899966211202406376147425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92599977474134937584098283 138899966211202406376147425)
      ·
        refine ⟨104174974658401804782110569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138899966211202406376147425 104174974658401804782110569)
        ·
          refine ⟨78131230993801353586582927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104174974658401804782110569 78131230993801353586582927)
          ·
            refine ⟨117196846490702030379874391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78131230993801353586582927 117196846490702030379874391)
            ·
              refine ⟨175795269736053045569811587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117196846490702030379874391 175795269736053045569811587)
              ·
                refine ⟨263692904604079568354717381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 175795269736053045569811587 263692904604079568354717381)
                ·
                  refine ⟨49442419613264919066509509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 263692904604079568354717381 49442419613264919066509509)
                  ·
                    refine ⟨9270453677487172324970533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49442419613264919066509509 9270453677487172324970533)
                    ·
                      refine ⟨1738210064528844810931975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9270453677487172324970533 1738210064528844810931975)
                      ·
                        rfl

theorem cell23_3385152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 4, 4, 4].length) (baseStart_3385152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3385152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3385152 prefixEnd_3385152 := by exact prefixLift 3385152
  have htrace : WordTrace (prefixWord ++ tailWord_3385152) baseStart_3385152 baseEnd_3385152 := by
    simpa [prefixWord, tailWord_3385152, baseEnd_3385152] using wordTrace_append hprefix tailTrace_3385152
  have hstable : (prefixWord ++ tailWord_3385152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3385152).length < 2 ^ (prefixWord ++ tailWord_3385152).sum := by decide
  have hdescent : baseEnd_3385152 < baseStart_3385152 := by decide
  rcases family_descends (prefixWord ++ tailWord_3385152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3385159 : List Nat := [1, 1, 4, 1, 2, 1, 2, 2, 4, 2, 3]
def baseStart_3385159 : Nat := 118140960795 + 3385159 * 2 ^ 59
def prefixEnd_3385159 : Nat := 4983230072969 + 3 ^ 40 * 3385159 * 2
def baseEnd_3385159 : Nat := 1738213658893426283544443

theorem tailTrace_3385159 : CollatzResearch.WordTrace tailWord_3385159 prefixEnd_3385159 1738213658893426283544443 := by
  unfold tailWord_3385159
  simp only [CollatzResearch.WordTrace]
  refine ⟨123466891943154556974302531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82311261295436371316201687 123466891943154556974302531)
  ·
    refine ⟨185200337914731835461453797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123466891943154556974302531 185200337914731835461453797)
    ·
      refine ⟨34725063359012219149022587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 185200337914731835461453797 34725063359012219149022587)
      ·
        refine ⟨52087595038518328723533881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34725063359012219149022587 52087595038518328723533881)
        ·
          refine ⟨39065696278888746542650411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52087595038518328723533881 39065696278888746542650411)
          ·
            refine ⟨58598544418333119813975617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39065696278888746542650411 58598544418333119813975617)
            ·
              refine ⟨43948908313749839860481713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58598544418333119813975617 43948908313749839860481713)
              ·
                refine ⟨32961681235312379895361285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43948908313749839860481713 32961681235312379895361285)
                ·
                  refine ⟨6180315231621071230380241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32961681235312379895361285 6180315231621071230380241)
                  ·
                    refine ⟨4635236423715803422785181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6180315231621071230380241 4635236423715803422785181)
                    ·
                      refine ⟨1738213658893426283544443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4635236423715803422785181 1738213658893426283544443)
                      ·
                        rfl

theorem cell23_3385159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 2, 4, 2, 3].length) (baseStart_3385159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3385159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3385159 prefixEnd_3385159 := by exact prefixLift 3385159
  have htrace : WordTrace (prefixWord ++ tailWord_3385159) baseStart_3385159 baseEnd_3385159 := by
    simpa [prefixWord, tailWord_3385159, baseEnd_3385159] using wordTrace_append hprefix tailTrace_3385159
  have hstable : (prefixWord ++ tailWord_3385159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3385159).length < 2 ^ (prefixWord ++ tailWord_3385159).sum := by decide
  have hdescent : baseEnd_3385159 < baseStart_3385159 := by decide
  rcases family_descends (prefixWord ++ tailWord_3385159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3385183 : List Nat := [1, 1, 2, 3, 1, 5, 2, 3, 1, 4]
def baseStart_3385183 : Nat := 118140960795 + 3385183 * 2 ^ 59
def prefixEnd_3385183 : Nat := 4983230072969 + 3 ^ 40 * 3385183 * 2
def baseEnd_3385183 : Nat := 579408660809711396548111

theorem tailTrace_3385183 : CollatzResearch.WordTrace tailWord_3385183 prefixEnd_3385183 579408660809711396548111 := by
  unfold tailWord_3385183
  simp only [CollatzResearch.WordTrace]
  refine ⟨123467767295067609073176203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82311844863378406048784135 123467767295067609073176203)
  ·
    refine ⟨185201650942601413609764305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123467767295067609073176203 185201650942601413609764305)
    ·
      refine ⟨138901238206951060207323229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185201650942601413609764305 138901238206951060207323229)
      ·
        refine ⟨52087964327606647577746211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138901238206951060207323229 52087964327606647577746211)
        ·
          refine ⟨78131946491409971366619317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52087964327606647577746211 78131946491409971366619317)
          ·
            refine ⟨7324869983569684815620561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 78131946491409971366619317 7324869983569684815620561)
            ·
              refine ⟨5493652487677263611715421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7324869983569684815620561 5493652487677263611715421)
              ·
                refine ⟨2060119682878973854393283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5493652487677263611715421 2060119682878973854393283)
                ·
                  refine ⟨3090179524318460781589925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2060119682878973854393283 3090179524318460781589925)
                  ·
                    refine ⟨579408660809711396548111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3090179524318460781589925 579408660809711396548111)
                    ·
                      rfl

theorem cell23_3385183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 2, 3, 1, 4].length) (baseStart_3385183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3385183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3385183 prefixEnd_3385183 := by exact prefixLift 3385183
  have htrace : WordTrace (prefixWord ++ tailWord_3385183) baseStart_3385183 baseEnd_3385183 := by
    simpa [prefixWord, tailWord_3385183, baseEnd_3385183] using wordTrace_append hprefix tailTrace_3385183
  have hstable : (prefixWord ++ tailWord_3385183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3385183).length < 2 ^ (prefixWord ++ tailWord_3385183).sum := by decide
  have hdescent : baseEnd_3385183 < baseStart_3385183 := by decide
  rcases family_descends (prefixWord ++ tailWord_3385183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3385196 : List Nat := [2, 2, 1, 1, 4, 4, 1, 2, 6]
def baseStart_3385196 : Nat := 118140960795 + 3385196 * 2 ^ 59
def prefixEnd_3385196 : Nat := 4983230072969 + 3 ^ 40 * 3385196 * 2
def baseEnd_3385196 : Nat := 193136961964182515420197

theorem tailTrace_3385196 : CollatzResearch.WordTrace tailWord_3385196 prefixEnd_3385196 193136961964182515420197 := by
  unfold tailWord_3385196
  simp only [CollatzResearch.WordTrace]
  refine ⟨61734120722010256146699721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82312160962680341528932961 61734120722010256146699721)
  ·
    refine ⟨46300590541507692110024791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61734120722010256146699721 46300590541507692110024791)
    ·
      refine ⟨69450885812261538165037187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46300590541507692110024791 69450885812261538165037187)
      ·
        refine ⟨104176328718392307247555781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69450885812261538165037187 104176328718392307247555781)
        ·
          refine ⟨19533061634698557608916709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104176328718392307247555781 19533061634698557608916709)
          ·
            refine ⟨3662449056505979551671883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19533061634698557608916709 3662449056505979551671883)
            ·
              refine ⟨5493673584758969327507825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3662449056505979551671883 5493673584758969327507825)
              ·
                refine ⟨4120255188569226995630869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5493673584758969327507825 4120255188569226995630869)
                ·
                  refine ⟨193136961964182515420197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4120255188569226995630869 193136961964182515420197)
                  ·
                    rfl

theorem cell23_3385196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 6].length) (baseStart_3385196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3385196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3385196 prefixEnd_3385196 := by exact prefixLift 3385196
  have htrace : WordTrace (prefixWord ++ tailWord_3385196) baseStart_3385196 baseEnd_3385196 := by
    simpa [prefixWord, tailWord_3385196, baseEnd_3385196] using wordTrace_append hprefix tailTrace_3385196
  have hstable : (prefixWord ++ tailWord_3385196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3385196).length < 2 ^ (prefixWord ++ tailWord_3385196).sum := by decide
  have hdescent : baseEnd_3385196 < baseStart_3385196 := by decide
  rcases family_descends (prefixWord ++ tailWord_3385196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3385250 : List Nat := [3, 3, 1, 2, 3, 1, 1, 2, 2, 3, 2]
def baseStart_3385250 : Nat := 118140960795 + 3385250 * 2 ^ 59
def prefixEnd_3385250 : Nat := 4983230072969 + 3 ^ 40 * 3385250 * 2
def baseEnd_3385250 : Nat := 1738260385632985427506525

theorem tailTrace_3385250 : CollatzResearch.WordTrace tailWord_3385250 prefixEnd_3385250 1738260385632985427506525 := by
  unfold tailWord_3385250
  simp only [CollatzResearch.WordTrace]
  refine ⟨30867552746456219878966301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82313473990549919677243469 30867552746456219878966301)
  ·
    refine ⟨11575332279921082454612363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30867552746456219878966301 11575332279921082454612363)
    ·
      refine ⟨17362998419881623681918545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11575332279921082454612363 17362998419881623681918545)
      ·
        refine ⟨13022248814911217761438909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17362998419881623681918545 13022248814911217761438909)
        ·
          refine ⟨4883343305591706660539591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13022248814911217761438909 4883343305591706660539591)
          ·
            refine ⟨7325014958387559990809387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4883343305591706660539591 7325014958387559990809387)
            ·
              refine ⟨10987522437581339986214081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7325014958387559990809387 10987522437581339986214081)
              ·
                refine ⟨8240641828186004989660561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10987522437581339986214081 8240641828186004989660561)
                ·
                  refine ⟨6180481371139503742245421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8240641828186004989660561 6180481371139503742245421)
                  ·
                    refine ⟨2317680514177313903342033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6180481371139503742245421 2317680514177313903342033)
                    ·
                      refine ⟨1738260385632985427506525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2317680514177313903342033 1738260385632985427506525)
                      ·
                        rfl

theorem cell23_3385250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 2, 2, 3, 2].length) (baseStart_3385250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3385250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3385250 prefixEnd_3385250 := by exact prefixLift 3385250
  have htrace : WordTrace (prefixWord ++ tailWord_3385250) baseStart_3385250 baseEnd_3385250 := by
    simpa [prefixWord, tailWord_3385250, baseEnd_3385250] using wordTrace_append hprefix tailTrace_3385250
  have hstable : (prefixWord ++ tailWord_3385250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3385250).length < 2 ^ (prefixWord ++ tailWord_3385250).sum := by decide
  have hdescent : baseEnd_3385250 < baseStart_3385250 := by decide
  rcases family_descends (prefixWord ++ tailWord_3385250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3385269 : List Nat := [1, 3, 3, 2, 1, 2, 1, 10]
def baseStart_3385269 : Nat := 118140960795 + 3385269 * 2 ^ 59
def prefixEnd_3385269 : Nat := 4983230072969 + 3 ^ 40 * 3385269 * 2
def baseEnd_3385269 : Nat := 64380375620941513080331

theorem tailTrace_3385269 : CollatzResearch.WordTrace tailWord_3385269 prefixEnd_3385269 64380375620941513080331 := by
  unfold tailWord_3385269
  simp only [CollatzResearch.WordTrace]
  refine ⟨123470903972756045760806861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82313935981837363840537907 123470903972756045760806861)
  ·
    refine ⟨46301588989783517160302573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123470903972756045760806861 46301588989783517160302573)
    ·
      refine ⟨17363095871168818935113465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46301588989783517160302573 17363095871168818935113465)
      ·
        refine ⟨13022321903376614201335099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17363095871168818935113465 13022321903376614201335099)
        ·
          refine ⟨19533482855064921302002649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13022321903376614201335099 19533482855064921302002649)
          ·
            refine ⟨14650112141298690976501987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19533482855064921302002649 14650112141298690976501987)
            ·
              refine ⟨21975168211948036464752981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14650112141298690976501987 21975168211948036464752981)
              ·
                refine ⟨64380375620941513080331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 21975168211948036464752981 64380375620941513080331)
                ·
                  rfl

theorem cell23_3385269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 10].length) (baseStart_3385269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3385269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3385269 prefixEnd_3385269 := by exact prefixLift 3385269
  have htrace : WordTrace (prefixWord ++ tailWord_3385269) baseStart_3385269 baseEnd_3385269 := by
    simpa [prefixWord, tailWord_3385269, baseEnd_3385269] using wordTrace_append hprefix tailTrace_3385269
  have hstable : (prefixWord ++ tailWord_3385269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3385269).length < 2 ^ (prefixWord ++ tailWord_3385269).sum := by decide
  have hdescent : baseEnd_3385269 < baseStart_3385269 := by decide
  rcases family_descends (prefixWord ++ tailWord_3385269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3385296 : List Nat := [2, 1, 1, 1, 1, 2, 4, 1, 6, 1, 3]
def baseStart_3385296 : Nat := 118140960795 + 3385296 * 2 ^ 59
def prefixEnd_3385296 : Nat := 4983230072969 + 3 ^ 40 * 3385296 * 2
def baseEnd_3385296 : Nat := 1738284005743092247531313

theorem tailTrace_3385296 : CollatzResearch.WordTrace tailWord_3385296 prefixEnd_3385296 1738284005743092247531313 := by
  unfold tailWord_3385296
  simp only [CollatzResearch.WordTrace]
  refine ⟨61735944371829114686019871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82314592495772152914693161 61735944371829114686019871)
  ·
    refine ⟨92603916557743672029029807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61735944371829114686019871 92603916557743672029029807)
    ·
      refine ⟨138905874836615508043544711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92603916557743672029029807 138905874836615508043544711)
      ·
        refine ⟨208358812254923262065317067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138905874836615508043544711 208358812254923262065317067)
        ·
          refine ⟨312538218382384893097975601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208358812254923262065317067 312538218382384893097975601)
          ·
            refine ⟨234403663786788669823481701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 312538218382384893097975601 234403663786788669823481701)
            ·
              refine ⟨43950686960022875591902819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 234403663786788669823481701 43950686960022875591902819)
              ·
                refine ⟨65926030440034313387854229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43950686960022875591902819 65926030440034313387854229)
                ·
                  refine ⟨3090282676876608440055667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 65926030440034313387854229 3090282676876608440055667)
                  ·
                    refine ⟨4635424015314912660083501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3090282676876608440055667 4635424015314912660083501)
                    ·
                      refine ⟨1738284005743092247531313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4635424015314912660083501 1738284005743092247531313)
                      ·
                        rfl

theorem cell23_3385296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 6, 1, 3].length) (baseStart_3385296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3385296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3385296 prefixEnd_3385296 := by exact prefixLift 3385296
  have htrace : WordTrace (prefixWord ++ tailWord_3385296) baseStart_3385296 baseEnd_3385296 := by
    simpa [prefixWord, tailWord_3385296, baseEnd_3385296] using wordTrace_append hprefix tailTrace_3385296
  have hstable : (prefixWord ++ tailWord_3385296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3385296).length < 2 ^ (prefixWord ++ tailWord_3385296).sum := by decide
  have hdescent : baseEnd_3385296 < baseStart_3385296 := by decide
  rcases family_descends (prefixWord ++ tailWord_3385296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3385300 : List Nat := [2, 4, 1, 2, 1, 1, 5, 1, 1, 2, 3]
def baseStart_3385300 : Nat := 118140960795 + 3385300 * 2 ^ 59
def prefixEnd_3385300 : Nat := 4983230072969 + 3 ^ 40 * 3385300 * 2
def baseEnd_3385300 : Nat := 1738286059665710231881295

theorem tailTrace_3385300 : CollatzResearch.WordTrace tailWord_3385300 prefixEnd_3385300 1738286059665710231881295 := by
  unfold tailWord_3385300
  simp only [CollatzResearch.WordTrace]
  refine ⟨61736017317821869027592677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82314689757095825370123569 61736017317821869027592677)
  ·
    refine ⟨11575503247091600442673627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61736017317821869027592677 11575503247091600442673627)
    ·
      refine ⟨17363254870637400664010441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11575503247091600442673627 17363254870637400664010441)
      ·
        refine ⟨13022441152978050498007831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17363254870637400664010441 13022441152978050498007831)
        ·
          refine ⟨19533661729467075747011747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13022441152978050498007831 19533661729467075747011747)
          ·
            refine ⟨29300492594200613620517621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19533661729467075747011747 29300492594200613620517621)
            ·
              refine ⟨2746921180706307526923527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29300492594200613620517621 2746921180706307526923527)
              ·
                refine ⟨4120381771059461290385291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2746921180706307526923527 4120381771059461290385291)
                ·
                  refine ⟨6180572656589191935577937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4120381771059461290385291 6180572656589191935577937)
                  ·
                    refine ⟨4635429492441893951683453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6180572656589191935577937 4635429492441893951683453)
                    ·
                      refine ⟨1738286059665710231881295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4635429492441893951683453 1738286059665710231881295)
                      ·
                        rfl

theorem cell23_3385300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 5, 1, 1, 2, 3].length) (baseStart_3385300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3385300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3385300 prefixEnd_3385300 := by exact prefixLift 3385300
  have htrace : WordTrace (prefixWord ++ tailWord_3385300) baseStart_3385300 baseEnd_3385300 := by
    simpa [prefixWord, tailWord_3385300, baseEnd_3385300] using wordTrace_append hprefix tailTrace_3385300
  have hstable : (prefixWord ++ tailWord_3385300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3385300).length < 2 ^ (prefixWord ++ tailWord_3385300).sum := by decide
  have hdescent : baseEnd_3385300 < baseStart_3385300 := by decide
  rcases family_descends (prefixWord ++ tailWord_3385300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3385308 : List Nat := [2, 2, 6, 1, 1, 2, 2, 2, 1, 1, 3]
def baseStart_3385308 : Nat := 118140960795 + 3385308 * 2 ^ 59
def prefixEnd_3385308 : Nat := 4983230072969 + 3 ^ 40 * 3385308 * 2
def baseEnd_3385308 : Nat := 1738290167510946200581259

theorem tailTrace_3385308 : CollatzResearch.WordTrace tailWord_3385308 prefixEnd_3385308 1738290167510946200581259 := by
  unfold tailWord_3385308
  simp only [CollatzResearch.WordTrace]
  refine ⟨61736163209807377710738289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82314884279743170280984385 61736163209807377710738289)
  ·
    refine ⟨46302122407355533283053717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61736163209807377710738289 46302122407355533283053717)
    ·
      refine ⟨2170411987844790622643143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 46302122407355533283053717 2170411987844790622643143)
      ·
        refine ⟨3255617981767185933964715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2170411987844790622643143 3255617981767185933964715)
        ·
          refine ⟨4883426972650778900947073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3255617981767185933964715 4883426972650778900947073)
          ·
            refine ⟨3662570229488084175710305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4883426972650778900947073 3662570229488084175710305)
            ·
              refine ⟨2746927672116063131782729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3662570229488084175710305 2746927672116063131782729)
              ·
                refine ⟨2060195754087047348837047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2746927672116063131782729 2060195754087047348837047)
                ·
                  refine ⟨3090293631130571023255571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2060195754087047348837047 3090293631130571023255571)
                  ·
                    refine ⟨4635440446695856534883357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3090293631130571023255571 4635440446695856534883357)
                    ·
                      refine ⟨1738290167510946200581259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4635440446695856534883357 1738290167510946200581259)
                      ·
                        rfl

theorem cell23_3385308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_3385308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3385308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3385308 prefixEnd_3385308 := by exact prefixLift 3385308
  have htrace : WordTrace (prefixWord ++ tailWord_3385308) baseStart_3385308 baseEnd_3385308 := by
    simpa [prefixWord, tailWord_3385308, baseEnd_3385308] using wordTrace_append hprefix tailTrace_3385308
  have hstable : (prefixWord ++ tailWord_3385308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3385308).length < 2 ^ (prefixWord ++ tailWord_3385308).sum := by decide
  have hdescent : baseEnd_3385308 < baseStart_3385308 := by decide
  rcases family_descends (prefixWord ++ tailWord_3385308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3385313 : List Nat := [1, 2, 3, 1, 2, 1, 3, 4, 2, 1, 3]
def baseStart_3385313 : Nat := 118140960795 + 3385313 * 2 ^ 59
def prefixEnd_3385313 : Nat := 4983230072969 + 3 ^ 40 * 3385313 * 2
def baseEnd_3385313 : Nat := 1738292734914218681018735

theorem tailTrace_3385313 : CollatzResearch.WordTrace tailWord_3385313 prefixEnd_3385313 1738292734914218681018735 := by
  unfold tailWord_3385313
  simp only [CollatzResearch.WordTrace]
  refine ⟨123472508784596641275408593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82315005856397760850272395 123472508784596641275408593)
  ·
    refine ⟨92604381588447480956556445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123472508784596641275408593 92604381588447480956556445)
    ·
      refine ⟨34726643095667805358708667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92604381588447480956556445 34726643095667805358708667)
      ·
        refine ⟨52089964643501708038063001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34726643095667805358708667 52089964643501708038063001)
        ·
          refine ⟨39067473482626281028547251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52089964643501708038063001 39067473482626281028547251)
          ·
            refine ⟨58601210223939421542820877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39067473482626281028547251 58601210223939421542820877)
            ·
              refine ⟨21975453833977283078557829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58601210223939421542820877 21975453833977283078557829)
              ·
                refine ⟨4120397593870740577229593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21975453833977283078557829 4120397593870740577229593)
                ·
                  refine ⟨3090298195403055432922195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4120397593870740577229593 3090298195403055432922195)
                  ·
                    refine ⟨4635447293104583149383293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3090298195403055432922195 4635447293104583149383293)
                    ·
                      refine ⟨1738292734914218681018735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4635447293104583149383293 1738292734914218681018735)
                      ·
                        rfl

theorem cell23_3385313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 4, 2, 1, 3].length) (baseStart_3385313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3385313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3385313 prefixEnd_3385313 := by exact prefixLift 3385313
  have htrace : WordTrace (prefixWord ++ tailWord_3385313) baseStart_3385313 baseEnd_3385313 := by
    simpa [prefixWord, tailWord_3385313, baseEnd_3385313] using wordTrace_append hprefix tailTrace_3385313
  have hstable : (prefixWord ++ tailWord_3385313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3385313).length < 2 ^ (prefixWord ++ tailWord_3385313).sum := by decide
  have hdescent : baseEnd_3385313 < baseStart_3385313 := by decide
  rcases family_descends (prefixWord ++ tailWord_3385313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3385339 : List Nat := [1, 1, 1, 1, 1, 3, 4, 1, 4, 1, 5]
def baseStart_3385339 : Nat := 118140960795 + 3385339 * 2 ^ 59
def prefixEnd_3385339 : Nat := 4983230072969 + 3 ^ 40 * 3385339 * 2
def baseEnd_3385339 : Nat := 1738306085411235579293615

theorem tailTrace_3385339 : CollatzResearch.WordTrace tailWord_3385339 prefixEnd_3385339 1738306085411235579293615 := by
  unfold tailWord_3385339
  simp only [CollatzResearch.WordTrace]
  refine ⟨123473457082502447715855071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82315638055001631810570047 123473457082502447715855071)
  ·
    refine ⟨185210185623753671573782607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123473457082502447715855071 185210185623753671573782607)
    ·
      refine ⟨277815278435630507360673911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185210185623753671573782607 277815278435630507360673911)
      ·
        refine ⟨416722917653445761041010867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277815278435630507360673911 416722917653445761041010867)
        ·
          refine ⟨625084376480168641561516301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 416722917653445761041010867 625084376480168641561516301)
          ·
            refine ⟨234406641180063240585568613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 625084376480168641561516301 234406641180063240585568613)
            ·
              refine ⟨43951245221261857609794115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 234406641180063240585568613 43951245221261857609794115)
              ·
                refine ⟨65926867831892786414691173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43951245221261857609794115 65926867831892786414691173)
                ·
                  refine ⟨12361287718479897452754595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65926867831892786414691173 12361287718479897452754595)
                  ·
                    refine ⟨18541931577719846179131893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12361287718479897452754595 18541931577719846179131893)
                    ·
                      refine ⟨1738306085411235579293615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18541931577719846179131893 1738306085411235579293615)
                      ·
                        rfl

theorem cell23_3385339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 1, 5].length) (baseStart_3385339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3385339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3385339 prefixEnd_3385339 := by exact prefixLift 3385339
  have htrace : WordTrace (prefixWord ++ tailWord_3385339) baseStart_3385339 baseEnd_3385339 := by
    simpa [prefixWord, tailWord_3385339, baseEnd_3385339] using wordTrace_append hprefix tailTrace_3385339
  have hstable : (prefixWord ++ tailWord_3385339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3385339).length < 2 ^ (prefixWord ++ tailWord_3385339).sum := by decide
  have hdescent : baseEnd_3385339 < baseStart_3385339 := by decide
  rcases family_descends (prefixWord ++ tailWord_3385339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3385370 : List Nat := [3, 1, 1, 3, 1, 4, 1, 1, 4, 2, 2]
def baseStart_3385370 : Nat := 118140960795 + 3385370 * 2 ^ 59
def prefixEnd_3385370 : Nat := 4983230072969 + 3 ^ 40 * 3385370 * 2
def baseEnd_3385370 : Nat := 1738322003311524958005973

theorem tailTrace_3385370 : CollatzResearch.WordTrace tailWord_3385370 prefixEnd_3385370 1738322003311524958005973 := by
  unfold tailWord_3385370
  simp only [CollatzResearch.WordTrace]
  refine ⟨30868646936347535002558391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82316391830260093340155709 30868646936347535002558391)
  ·
    refine ⟨46302970404521302503837587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30868646936347535002558391 46302970404521302503837587)
    ·
      refine ⟨69454455606781953755756381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46302970404521302503837587 69454455606781953755756381)
      ·
        refine ⟨26045420852543232658408643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69454455606781953755756381 26045420852543232658408643)
        ·
          refine ⟨39068131278814848987612965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26045420852543232658408643 39068131278814848987612965)
          ·
            refine ⟨7325274614777784185177431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39068131278814848987612965 7325274614777784185177431)
            ·
              refine ⟨10987911922166676277766147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7325274614777784185177431 10987911922166676277766147)
              ·
                refine ⟨16481867883250014416649221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10987911922166676277766147 16481867883250014416649221)
                ·
                  refine ⟨3090350228109377703121729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16481867883250014416649221 3090350228109377703121729)
                  ·
                    refine ⟨2317762671082033277341297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3090350228109377703121729 2317762671082033277341297)
                    ·
                      refine ⟨1738322003311524958005973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2317762671082033277341297 1738322003311524958005973)
                      ·
                        rfl

theorem cell23_3385370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 1, 4, 2, 2].length) (baseStart_3385370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3385370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3385370 prefixEnd_3385370 := by exact prefixLift 3385370
  have htrace : WordTrace (prefixWord ++ tailWord_3385370) baseStart_3385370 baseEnd_3385370 := by
    simpa [prefixWord, tailWord_3385370, baseEnd_3385370] using wordTrace_append hprefix tailTrace_3385370
  have hstable : (prefixWord ++ tailWord_3385370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3385370).length < 2 ^ (prefixWord ++ tailWord_3385370).sum := by decide
  have hdescent : baseEnd_3385370 < baseStart_3385370 := by decide
  rcases family_descends (prefixWord ++ tailWord_3385370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3385419 : List Nat := [1, 1, 1, 1, 3, 1, 2, 2, 1, 10]
def baseStart_3385419 : Nat := 118140960795 + 3385419 * 2 ^ 59
def prefixEnd_3385419 : Nat := 4983230072969 + 3 ^ 40 * 3385419 * 2
def baseEnd_3385419 : Nat := 579449054621198422097749

theorem tailTrace_3385419 : CollatzResearch.WordTrace tailWord_3385419 prefixEnd_3385419 579449054621198422097749 := by
  unfold tailWord_3385419
  simp only [CollatzResearch.WordTrace]
  refine ⟨123476374922212621378767311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82317583281475080919178207 123476374922212621378767311)
  ·
    refine ⟨185214562383318932068150967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123476374922212621378767311 185214562383318932068150967)
    ·
      refine ⟨277821843574978398102226451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185214562383318932068150967 277821843574978398102226451)
      ·
        refine ⟨416732765362467597153339677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277821843574978398102226451 416732765362467597153339677)
        ·
          refine ⟨156274787010925348932502379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 416732765362467597153339677 156274787010925348932502379)
          ·
            refine ⟨234412180516388023398753569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156274787010925348932502379 234412180516388023398753569)
            ·
              refine ⟨175809135387291017549065177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 234412180516388023398753569 175809135387291017549065177)
              ·
                refine ⟨131856851540468263161798883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 175809135387291017549065177 131856851540468263161798883)
                ·
                  refine ⟨197785277310702394742698325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 131856851540468263161798883 197785277310702394742698325)
                  ·
                    refine ⟨579449054621198422097749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 197785277310702394742698325 579449054621198422097749)
                    ·
                      rfl

theorem cell23_3385419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 10].length) (baseStart_3385419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3385419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3385419 prefixEnd_3385419 := by exact prefixLift 3385419
  have htrace : WordTrace (prefixWord ++ tailWord_3385419) baseStart_3385419 baseEnd_3385419 := by
    simpa [prefixWord, tailWord_3385419, baseEnd_3385419] using wordTrace_append hprefix tailTrace_3385419
  have hstable : (prefixWord ++ tailWord_3385419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3385419).length < 2 ^ (prefixWord ++ tailWord_3385419).sum := by decide
  have hdescent : baseEnd_3385419 < baseStart_3385419 := by decide
  rcases family_descends (prefixWord ++ tailWord_3385419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3385443 : List Nat := [1, 1, 1, 5, 1, 1, 2, 3, 2, 4, 2]
def baseStart_3385443 : Nat := 118140960795 + 3385443 * 2 ^ 59
def prefixEnd_3385443 : Nat := 4983230072969 + 3 ^ 40 * 3385443 * 2
def baseEnd_3385443 : Nat := 1738359487399303172393137

theorem tailTrace_3385443 : CollatzResearch.WordTrace tailWord_3385443 prefixEnd_3385443 1738359487399303172393137 := by
  unfold tailWord_3385443
  simp only [CollatzResearch.WordTrace]
  refine ⟨123477250274125673477640983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82318166849417115651760655 123477250274125673477640983)
  ·
    refine ⟨185215875411188510216461475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123477250274125673477640983 185215875411188510216461475)
    ·
      refine ⟨277823813116782765324692213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185215875411188510216461475 277823813116782765324692213)
      ·
        refine ⟨26045982479698384249189895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 277823813116782765324692213 26045982479698384249189895)
        ·
          refine ⟨39068973719547576373784843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26045982479698384249189895 39068973719547576373784843)
          ·
            refine ⟨58603460579321364560677265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39068973719547576373784843 58603460579321364560677265)
            ·
              refine ⟨43952595434491023420507949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58603460579321364560677265 43952595434491023420507949)
              ·
                refine ⟨16482223287934133782690481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43952595434491023420507949 16482223287934133782690481)
                ·
                  refine ⟨12361667465950600337017861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16482223287934133782690481 12361667465950600337017861)
                  ·
                    refine ⟨2317812649865737563190849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12361667465950600337017861 2317812649865737563190849)
                    ·
                      refine ⟨1738359487399303172393137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2317812649865737563190849 1738359487399303172393137)
                      ·
                        rfl

theorem cell23_3385443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 3, 2, 4, 2].length) (baseStart_3385443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3385443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3385443 prefixEnd_3385443 := by exact prefixLift 3385443
  have htrace : WordTrace (prefixWord ++ tailWord_3385443) baseStart_3385443 baseEnd_3385443 := by
    simpa [prefixWord, tailWord_3385443, baseEnd_3385443] using wordTrace_append hprefix tailTrace_3385443
  have hstable : (prefixWord ++ tailWord_3385443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3385443).length < 2 ^ (prefixWord ++ tailWord_3385443).sum := by decide
  have hdescent : baseEnd_3385443 < baseStart_3385443 := by decide
  rcases family_descends (prefixWord ++ tailWord_3385443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3385453 : List Nat := [1, 5, 1, 1, 2, 1, 2, 1, 5, 4]
def baseStart_3385453 : Nat := 118140960795 + 3385453 * 2 ^ 59
def prefixEnd_3385453 : Nat := 4983230072969 + 3 ^ 40 * 3385453 * 2
def baseEnd_3385453 : Nat := 579454874068616044422697

theorem tailTrace_3385453 : CollatzResearch.WordTrace tailWord_3385453 prefixEnd_3385453 579454874068616044422697 := by
  unfold tailWord_3385453
  simp only [CollatzResearch.WordTrace]
  refine ⟨123477615004089445185505013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82318410002726296790336675 123477615004089445185505013)
  ·
    refine ⟨11576026406633385486141095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 123477615004089445185505013 11576026406633385486141095)
    ·
      refine ⟨17364039609950078229211643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11576026406633385486141095 17364039609950078229211643)
      ·
        refine ⟨26046059414925117343817465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17364039609950078229211643 26046059414925117343817465)
        ·
          refine ⟨19534544561193838007863099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26046059414925117343817465 19534544561193838007863099)
          ·
            refine ⟨29301816841790757011794649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19534544561193838007863099 29301816841790757011794649)
            ·
              refine ⟨21976362631343067758845987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29301816841790757011794649 21976362631343067758845987)
              ·
                refine ⟨32964543947014601638268981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21976362631343067758845987 32964543947014601638268981)
                ·
                  refine ⟨3090425995032618903587717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32964543947014601638268981 3090425995032618903587717)
                  ·
                    refine ⟨579454874068616044422697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3090425995032618903587717 579454874068616044422697)
                    ·
                      rfl

theorem cell23_3385453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 1, 5, 4].length) (baseStart_3385453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3385453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3385453 prefixEnd_3385453 := by exact prefixLift 3385453
  have htrace : WordTrace (prefixWord ++ tailWord_3385453) baseStart_3385453 baseEnd_3385453 := by
    simpa [prefixWord, tailWord_3385453, baseEnd_3385453] using wordTrace_append hprefix tailTrace_3385453
  have hstable : (prefixWord ++ tailWord_3385453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3385453).length < 2 ^ (prefixWord ++ tailWord_3385453).sum := by decide
  have hdescent : baseEnd_3385453 < baseStart_3385453 := by decide
  rcases family_descends (prefixWord ++ tailWord_3385453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3385463 : List Nat := [1, 1, 3, 1, 1, 5, 1, 3, 2, 2, 3]
def baseStart_3385463 : Nat := 118140960795 + 3385463 * 2 ^ 59
def prefixEnd_3385463 : Nat := 4983230072969 + 3 ^ 40 * 3385463 * 2
def baseEnd_3385463 : Nat := 1738369757012393094143045

theorem tailTrace_3385463 : CollatzResearch.WordTrace tailWord_3385463 prefixEnd_3385463 1738369757012393094143045 := by
  unfold tailWord_3385463
  simp only [CollatzResearch.WordTrace]
  refine ⟨123477979734053216893369043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82318653156035477928912695 123477979734053216893369043)
  ·
    refine ⟨185216969601079825340053565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123477979734053216893369043 185216969601079825340053565)
    ·
      refine ⟨69456363600404934502520087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185216969601079825340053565 69456363600404934502520087)
      ·
        refine ⟨104184545400607401753780131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69456363600404934502520087 104184545400607401753780131)
        ·
          refine ⟨156276818100911102630670197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104184545400607401753780131 156276818100911102630670197)
          ·
            refine ⟨14650951696960415871625331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 156276818100911102630670197 14650951696960415871625331)
            ·
              refine ⟨21976427545440623807437997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14650951696960415871625331 21976427545440623807437997)
              ·
                refine ⟨8241160329540233927789249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21976427545440623807437997 8241160329540233927789249)
                ·
                  refine ⟨6180870247155175445841937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8241160329540233927789249 6180870247155175445841937)
                  ·
                    refine ⟨4635652685366381584381453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6180870247155175445841937 4635652685366381584381453)
                    ·
                      refine ⟨1738369757012393094143045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4635652685366381584381453 1738369757012393094143045)
                      ·
                        rfl

theorem cell23_3385463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 3, 2, 2, 3].length) (baseStart_3385463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3385463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3385463 prefixEnd_3385463 := by exact prefixLift 3385463
  have htrace : WordTrace (prefixWord ++ tailWord_3385463) baseStart_3385463 baseEnd_3385463 := by
    simpa [prefixWord, tailWord_3385463, baseEnd_3385463] using wordTrace_append hprefix tailTrace_3385463
  have hstable : (prefixWord ++ tailWord_3385463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3385463).length < 2 ^ (prefixWord ++ tailWord_3385463).sum := by decide
  have hdescent : baseEnd_3385463 < baseStart_3385463 := by decide
  rcases family_descends (prefixWord ++ tailWord_3385463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3385480 : List Nat := [2, 1, 3, 4, 1, 1, 2, 2, 2, 2, 3]
def baseStart_3385480 : Nat := 118140960795 + 3385480 * 2 ^ 59
def prefixEnd_3385480 : Nat := 4983230072969 + 3 ^ 40 * 3385480 * 2
def baseEnd_3385480 : Nat := 1738378486183519527630467

theorem tailTrace_3385480 : CollatzResearch.WordTrace tailWord_3385480 prefixEnd_3385480 1738378486183519527630467 := by
  unfold tailWord_3385480
  simp only [CollatzResearch.WordTrace]
  refine ⟨61739299887495814398368947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82319066516661085864491929 61739299887495814398368947)
  ·
    refine ⟨92608949831243721597553421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61739299887495814398368947 92608949831243721597553421)
    ·
      refine ⟨34728356186716395599082533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92608949831243721597553421 34728356186716395599082533)
      ·
        refine ⟨6511566785009324174827975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34728356186716395599082533 6511566785009324174827975)
        ·
          refine ⟨9767350177513986262241963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6511566785009324174827975 9767350177513986262241963)
          ·
            refine ⟨14651025266270979393362945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9767350177513986262241963 14651025266270979393362945)
            ·
              refine ⟨10988268949703234545022209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14651025266270979393362945 10988268949703234545022209)
              ·
                refine ⟨8241201712277425908766657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10988268949703234545022209 8241201712277425908766657)
                ·
                  refine ⟨6180901284208069431574993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8241201712277425908766657 6180901284208069431574993)
                  ·
                    refine ⟨4635675963156052073681245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6180901284208069431574993 4635675963156052073681245)
                    ·
                      refine ⟨1738378486183519527630467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4635675963156052073681245 1738378486183519527630467)
                      ·
                        rfl

theorem cell23_3385480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_3385480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3385480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3385480 prefixEnd_3385480 := by exact prefixLift 3385480
  have htrace : WordTrace (prefixWord ++ tailWord_3385480) baseStart_3385480 baseEnd_3385480 := by
    simpa [prefixWord, tailWord_3385480, baseEnd_3385480] using wordTrace_append hprefix tailTrace_3385480
  have hstable : (prefixWord ++ tailWord_3385480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3385480).length < 2 ^ (prefixWord ++ tailWord_3385480).sum := by decide
  have hdescent : baseEnd_3385480 < baseStart_3385480 := by decide
  rcases family_descends (prefixWord ++ tailWord_3385480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3385514 : List Nat := [3, 1, 5, 1, 2, 2, 1, 1, 2, 2, 3]
def baseStart_3385514 : Nat := 118140960795 + 3385514 * 2 ^ 59
def prefixEnd_3385514 : Nat := 4983230072969 + 3 ^ 40 * 3385514 * 2
def baseEnd_3385514 : Nat := 1738395944525772394605311

theorem tailTrace_3385514 : CollatzResearch.WordTrace tailWord_3385514 prefixEnd_3385514 1738395944525772394605311 := by
  unfold tailWord_3385514
  simp only [CollatzResearch.WordTrace]
  refine ⟨30869959964217113150868899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82319893237912301735650397 30869959964217113150868899)
  ·
    refine ⟨46304939946325669726303349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30869959964217113150868899 46304939946325669726303349)
    ·
      refine ⟨4341088119968031536840939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46304939946325669726303349 4341088119968031536840939)
      ·
        refine ⟨6511632179952047305261409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4341088119968031536840939 6511632179952047305261409)
        ·
          refine ⟨4883724134964035478946057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6511632179952047305261409 4883724134964035478946057)
          ·
            refine ⟨3662793101223026609209543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4883724134964035478946057 3662793101223026609209543)
            ·
              refine ⟨5494189651834539913814315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3662793101223026609209543 5494189651834539913814315)
              ·
                refine ⟨8241284477751809870721473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5494189651834539913814315 8241284477751809870721473)
                ·
                  refine ⟨6180963358313857403041105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8241284477751809870721473 6180963358313857403041105)
                  ·
                    refine ⟨4635722518735393052280829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6180963358313857403041105 4635722518735393052280829)
                    ·
                      refine ⟨1738395944525772394605311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4635722518735393052280829 1738395944525772394605311)
                      ·
                        rfl

theorem cell23_3385514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_3385514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3385514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3385514 prefixEnd_3385514 := by exact prefixLift 3385514
  have htrace : WordTrace (prefixWord ++ tailWord_3385514) baseStart_3385514 baseEnd_3385514 := by
    simpa [prefixWord, tailWord_3385514, baseEnd_3385514] using wordTrace_append hprefix tailTrace_3385514
  have hstable : (prefixWord ++ tailWord_3385514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3385514).length < 2 ^ (prefixWord ++ tailWord_3385514).sum := by decide
  have hdescent : baseEnd_3385514 < baseStart_3385514 := by decide
  rcases family_descends (prefixWord ++ tailWord_3385514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3385527 : List Nat := [1, 1, 3, 1, 4, 2, 1, 5, 1, 1, 3]
def baseStart_3385527 : Nat := 118140960795 + 3385527 * 2 ^ 59
def prefixEnd_3385527 : Nat := 4983230072969 + 3 ^ 40 * 3385527 * 2
def baseEnd_3385527 : Nat := 1738402619774280843742751

theorem tailTrace_3385527 : CollatzResearch.WordTrace tailWord_3385527 prefixEnd_3385527 1738402619774280843742751 := by
  unfold tailWord_3385527
  simp only [CollatzResearch.WordTrace]
  refine ⟨123480314005821355823698835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82320209337214237215799223 123480314005821355823698835)
  ·
    refine ⟨185220471008732033735548253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123480314005821355823698835 185220471008732033735548253)
    ·
      refine ⟨69457676628274512650830595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185220471008732033735548253 69457676628274512650830595)
      ·
        refine ⟨104186514942411768976245893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69457676628274512650830595 104186514942411768976245893)
        ·
          refine ⟨19534971551702206683046105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104186514942411768976245893 19534971551702206683046105)
          ·
            refine ⟨14651228663776655012284579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19534971551702206683046105 14651228663776655012284579)
            ·
              refine ⟨21976842995664982518426869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14651228663776655012284579 21976842995664982518426869)
              ·
                refine ⟨2060329030843592111102519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21976842995664982518426869 2060329030843592111102519)
                ·
                  refine ⟨3090493546265388166653779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2060329030843592111102519 3090493546265388166653779)
                  ·
                    refine ⟨4635740319398082249980669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3090493546265388166653779 4635740319398082249980669)
                    ·
                      refine ⟨1738402619774280843742751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4635740319398082249980669 1738402619774280843742751)
                      ·
                        rfl

theorem cell23_3385527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 5, 1, 1, 3].length) (baseStart_3385527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3385527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3385527 prefixEnd_3385527 := by exact prefixLift 3385527
  have htrace : WordTrace (prefixWord ++ tailWord_3385527) baseStart_3385527 baseEnd_3385527 := by
    simpa [prefixWord, tailWord_3385527, baseEnd_3385527] using wordTrace_append hprefix tailTrace_3385527
  have hstable : (prefixWord ++ tailWord_3385527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3385527).length < 2 ^ (prefixWord ++ tailWord_3385527).sum := by decide
  have hdescent : baseEnd_3385527 < baseStart_3385527 := by decide
  rcases family_descends (prefixWord ++ tailWord_3385527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3385530 : List Nat := [3, 1, 1, 1, 2, 2, 6, 1, 1, 5]
def baseStart_3385530 : Nat := 118140960795 + 3385530 * 2 ^ 59
def prefixEnd_3385530 : Nat := 4983230072969 + 3 ^ 40 * 3385530 * 2
def baseEnd_3385530 : Nat := 579468053405414777335079

theorem tailTrace_3385530 : CollatzResearch.WordTrace tailWord_3385530 prefixEnd_3385530 579468053405414777335079 := by
  unfold tailWord_3385530
  simp only [CollatzResearch.WordTrace]
  refine ⟨30870105856202621834014511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82320282283206991557372029 30870105856202621834014511)
  ·
    refine ⟨46305158784303932751021767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30870105856202621834014511 46305158784303932751021767)
    ·
      refine ⟨69457738176455899126532651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46305158784303932751021767 69457738176455899126532651)
      ·
        refine ⟨104186607264683848689798977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69457738176455899126532651 104186607264683848689798977)
        ·
          refine ⟨78139955448512886517349233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104186607264683848689798977 78139955448512886517349233)
          ·
            refine ⟨58604966586384664888011925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78139955448512886517349233 58604966586384664888011925)
            ·
              refine ⟨2747107808736781166625559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 58604966586384664888011925 2747107808736781166625559)
              ·
                refine ⟨4120661713105171749938339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2747107808736781166625559 4120661713105171749938339)
                ·
                  refine ⟨6180992569657757624907509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4120661713105171749938339 6180992569657757624907509)
                  ·
                    refine ⟨579468053405414777335079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6180992569657757624907509 579468053405414777335079)
                    ·
                      rfl

theorem cell23_3385530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 6, 1, 1, 5].length) (baseStart_3385530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3385530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3385530 prefixEnd_3385530 := by exact prefixLift 3385530
  have htrace : WordTrace (prefixWord ++ tailWord_3385530) baseStart_3385530 baseEnd_3385530 := by
    simpa [prefixWord, tailWord_3385530, baseEnd_3385530] using wordTrace_append hprefix tailTrace_3385530
  have hstable : (prefixWord ++ tailWord_3385530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3385530).length < 2 ^ (prefixWord ++ tailWord_3385530).sum := by decide
  have hdescent : baseEnd_3385530 < baseStart_3385530 := by decide
  rcases family_descends (prefixWord ++ tailWord_3385530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3385553 : List Nat := [1, 2, 2, 1, 2, 2, 2, 1, 5, 2, 3]
def baseStart_3385553 : Nat := 118140960795 + 3385553 * 2 ^ 59
def prefixEnd_3385553 : Nat := 4983230072969 + 3 ^ 40 * 3385553 * 2
def baseEnd_3385553 : Nat := 1738415970271297742017631

theorem tailTrace_3385553 : CollatzResearch.WordTrace tailWord_3385553 prefixEnd_3385553 1738415970271297742017631 := by
  unfold tailWord_3385553
  simp only [CollatzResearch.WordTrace]
  refine ⟨123481262303727162264145313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82320841535818108176096875 123481262303727162264145313)
  ·
    refine ⟨92610946727795371698108985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123481262303727162264145313 92610946727795371698108985)
    ·
      refine ⟨69458210045846528773581739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92610946727795371698108985 69458210045846528773581739)
      ·
        refine ⟨104187315068769793160372609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69458210045846528773581739 104187315068769793160372609)
        ·
          refine ⟨78140486301577344870279457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104187315068769793160372609 78140486301577344870279457)
          ·
            refine ⟨58605364726183008652709593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78140486301577344870279457 58605364726183008652709593)
            ·
              refine ⟨43954023544637256489532195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58605364726183008652709593 43954023544637256489532195)
              ·
                refine ⟨65931035316955884734298293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43954023544637256489532195 65931035316955884734298293)
                ·
                  refine ⟨6181034560964614193840465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65931035316955884734298293 6181034560964614193840465)
                  ·
                    refine ⟨4635775920723460645380349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6181034560964614193840465 4635775920723460645380349)
                    ·
                      refine ⟨1738415970271297742017631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4635775920723460645380349 1738415970271297742017631)
                      ·
                        rfl

theorem cell23_3385553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 5, 2, 3].length) (baseStart_3385553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3385553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3385553 prefixEnd_3385553 := by exact prefixLift 3385553
  have htrace : WordTrace (prefixWord ++ tailWord_3385553) baseStart_3385553 baseEnd_3385553 := by
    simpa [prefixWord, tailWord_3385553, baseEnd_3385553] using wordTrace_append hprefix tailTrace_3385553
  have hstable : (prefixWord ++ tailWord_3385553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3385553).length < 2 ^ (prefixWord ++ tailWord_3385553).sum := by decide
  have hdescent : baseEnd_3385553 < baseStart_3385553 := by decide
  rcases family_descends (prefixWord ++ tailWord_3385553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3385560 : List Nat := [2, 1, 2, 2, 4, 3, 1, 1, 1, 6]
def baseStart_3385560 : Nat := 118140960795 + 3385560 * 2 ^ 59
def prefixEnd_3385560 : Nat := 4983230072969 + 3 ^ 40 * 3385560 * 2
def baseEnd_3385560 : Nat := 579473188211959738210033

theorem tailTrace_3385560 : CollatzResearch.WordTrace tailWord_3385560 prefixEnd_3385560 579473188211959738210033 := by
  unfold tailWord_3385560
  simp only [CollatzResearch.WordTrace]
  refine ⟨61740758807350901229825067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82321011743134534973100089 61740758807350901229825067)
  ·
    refine ⟨92611138211026351844737601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61740758807350901229825067 92611138211026351844737601)
    ·
      refine ⟨69458353658269763883553201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92611138211026351844737601 69458353658269763883553201)
      ·
        refine ⟨52093765243702322912664901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69458353658269763883553201 52093765243702322912664901)
        ·
          refine ⟨9767580983194185546124669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52093765243702322912664901 9767580983194185546124669)
          ·
            refine ⟨3662842868697819579796751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9767580983194185546124669 3662842868697819579796751)
            ·
              refine ⟨5494264303046729369695127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3662842868697819579796751 5494264303046729369695127)
              ·
                refine ⟨8241396454570094054542691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5494264303046729369695127 8241396454570094054542691)
                ·
                  refine ⟨12362094681855141081814037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8241396454570094054542691 12362094681855141081814037)
                  ·
                    refine ⟨579473188211959738210033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12362094681855141081814037 579473188211959738210033)
                    ·
                      rfl

theorem cell23_3385560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 1, 1, 1, 6].length) (baseStart_3385560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3385560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3385560 prefixEnd_3385560 := by exact prefixLift 3385560
  have htrace : WordTrace (prefixWord ++ tailWord_3385560) baseStart_3385560 baseEnd_3385560 := by
    simpa [prefixWord, tailWord_3385560, baseEnd_3385560] using wordTrace_append hprefix tailTrace_3385560
  have hstable : (prefixWord ++ tailWord_3385560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3385560).length < 2 ^ (prefixWord ++ tailWord_3385560).sum := by decide
  have hdescent : baseEnd_3385560 < baseStart_3385560 := by decide
  rcases family_descends (prefixWord ++ tailWord_3385560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3385564 : List Nat := [2, 2, 5, 2, 1, 1, 2, 2, 1, 5]
def baseStart_3385564 : Nat := 118140960795 + 3385564 * 2 ^ 59
def prefixEnd_3385564 : Nat := 4983230072969 + 3 ^ 40 * 3385564 * 2
def baseEnd_3385564 : Nat := 579473872852832399660027

theorem tailTrace_3385564 : CollatzResearch.WordTrace tailWord_3385564 prefixEnd_3385564 579473872852832399660027 := by
  unfold tailWord_3385564
  simp only [CollatzResearch.WordTrace]
  refine ⟨61740831753343655571397873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82321109004458207428530497 61740831753343655571397873)
  ·
    refine ⟨46305623815007741678548405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61740831753343655571397873 46305623815007741678548405)
    ·
      refine ⟨4341152232656975782363913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46305623815007741678548405 4341152232656975782363913)
      ·
        refine ⟨3255864174492731836772935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4341152232656975782363913 3255864174492731836772935)
        ·
          refine ⟨4883796261739097755159403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3255864174492731836772935 4883796261739097755159403)
          ·
            refine ⟨7325694392608646632739105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4883796261739097755159403 7325694392608646632739105)
            ·
              refine ⟨5494270794456484974554329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7325694392608646632739105 5494270794456484974554329)
              ·
                refine ⟨4120703095842363730915747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5494270794456484974554329 4120703095842363730915747)
                ·
                  refine ⟨6181054643763545596373621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4120703095842363730915747 6181054643763545596373621)
                  ·
                    refine ⟨579473872852832399660027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6181054643763545596373621 579473872852832399660027)
                    ·
                      rfl

theorem cell23_3385564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_3385564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3385564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3385564 prefixEnd_3385564 := by exact prefixLift 3385564
  have htrace : WordTrace (prefixWord ++ tailWord_3385564) baseStart_3385564 baseEnd_3385564 := by
    simpa [prefixWord, tailWord_3385564, baseEnd_3385564] using wordTrace_append hprefix tailTrace_3385564
  have hstable : (prefixWord ++ tailWord_3385564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3385564).length < 2 ^ (prefixWord ++ tailWord_3385564).sum := by decide
  have hdescent : baseEnd_3385564 < baseStart_3385564 := by decide
  rcases family_descends (prefixWord ++ tailWord_3385564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3385573 : List Nat := [1, 3, 1, 4, 2, 2, 1, 9]
def baseStart_3385573 : Nat := 118140960795 + 3385573 * 2 ^ 59
def prefixEnd_3385573 : Nat := 4983230072969 + 3 ^ 40 * 3385573 * 2
def baseEnd_3385573 : Nat := 64386157032755098658057

theorem tailTrace_3385573 : CollatzResearch.WordTrace tailWord_3385573 prefixEnd_3385573 64386157032755098658057 := by
  unfold tailWord_3385573
  simp only [CollatzResearch.WordTrace]
  refine ⟨123481991763654705679873373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82321327842436470453248915 123481991763654705679873373)
  ·
    refine ⟨46305746911370514629952515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123481991763654705679873373 46305746911370514629952515)
    ·
      refine ⟨69458620367055771944928773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46305746911370514629952515 69458620367055771944928773)
      ·
        refine ⟨13023491318822957239674145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69458620367055771944928773 13023491318822957239674145)
        ·
          refine ⟨9767618489117217929755609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13023491318822957239674145 9767618489117217929755609)
          ·
            refine ⟨7325713866837913447316707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9767618489117217929755609 7325713866837913447316707)
            ·
              refine ⟨10988570800256870170975061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7325713866837913447316707 10988570800256870170975061)
              ·
                refine ⟨64386157032755098658057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10988570800256870170975061 64386157032755098658057)
                ·
                  rfl

theorem cell23_3385573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 9].length) (baseStart_3385573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3385573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3385573 prefixEnd_3385573 := by exact prefixLift 3385573
  have htrace : WordTrace (prefixWord ++ tailWord_3385573) baseStart_3385573 baseEnd_3385573 := by
    simpa [prefixWord, tailWord_3385573, baseEnd_3385573] using wordTrace_append hprefix tailTrace_3385573
  have hstable : (prefixWord ++ tailWord_3385573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3385573).length < 2 ^ (prefixWord ++ tailWord_3385573).sum := by decide
  have hdescent : baseEnd_3385573 < baseStart_3385573 := by decide
  rcases family_descends (prefixWord ++ tailWord_3385573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3385600 : List Nat := [2, 1, 1, 2, 1, 1, 6, 1, 4, 1, 3]
def baseStart_3385600 : Nat := 118140960795 + 3385600 * 2 ^ 59
def prefixEnd_3385600 : Nat := 4983230072969 + 3 ^ 40 * 3385600 * 2
def baseEnd_3385600 : Nat := 1738440103862059058129915

theorem tailTrace_3385600 : CollatzResearch.WordTrace tailWord_3385600 prefixEnd_3385600 1738440103862059058129915 := by
  unfold tailWord_3385600
  simp only [CollatzResearch.WordTrace]
  refine ⟨61741488267278444645553127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82321984356371259527404169 61741488267278444645553127)
  ·
    refine ⟨92612232400917666968329691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61741488267278444645553127 92612232400917666968329691)
    ·
      refine ⟨138918348601376500452494537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92612232400917666968329691 138918348601376500452494537)
      ·
        refine ⟨104188761451032375339370903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138918348601376500452494537 104188761451032375339370903)
        ·
          refine ⟨156283142176548563009056355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104188761451032375339370903 156283142176548563009056355)
          ·
            refine ⟨234424713264822844513584533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156283142176548563009056355 234424713264822844513584533)
            ·
              refine ⟨10988658434288570836574275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 234424713264822844513584533 10988658434288570836574275)
              ·
                refine ⟨16482987651432856254861413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10988658434288570836574275 16482987651432856254861413)
                ·
                  refine ⟨3090560184643660547786515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16482987651432856254861413 3090560184643660547786515)
                  ·
                    refine ⟨4635840276965490821679773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3090560184643660547786515 4635840276965490821679773)
                    ·
                      refine ⟨1738440103862059058129915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4635840276965490821679773 1738440103862059058129915)
                      ·
                        rfl

theorem cell23_3385600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 1, 4, 1, 3].length) (baseStart_3385600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3385600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3385600 prefixEnd_3385600 := by exact prefixLift 3385600
  have htrace : WordTrace (prefixWord ++ tailWord_3385600) baseStart_3385600 baseEnd_3385600 := by
    simpa [prefixWord, tailWord_3385600, baseEnd_3385600] using wordTrace_append hprefix tailTrace_3385600
  have hstable : (prefixWord ++ tailWord_3385600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3385600).length < 2 ^ (prefixWord ++ tailWord_3385600).sum := by decide
  have hdescent : baseEnd_3385600 < baseStart_3385600 := by decide
  rcases family_descends (prefixWord ++ tailWord_3385600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3385601 : List Nat := [1, 2, 4, 1, 1, 2, 5, 2, 1, 2, 2]
def baseStart_3385601 : Nat := 118140960795 + 3385601 * 2 ^ 59
def prefixEnd_3385601 : Nat := 4983230072969 + 3 ^ 40 * 3385601 * 2
def baseEnd_3385601 : Nat := 1738440617342713554217411

theorem tailTrace_3385601 : CollatzResearch.WordTrace tailWord_3385601 prefixEnd_3385601 1738440617342713554217411 := by
  unfold tailWord_3385601
  simp only [CollatzResearch.WordTrace]
  refine ⟨123483013007553266461892657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82322008671702177641261771 123483013007553266461892657)
  ·
    refine ⟨92612259755664949846419493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123483013007553266461892657 92612259755664949846419493)
    ·
      refine ⟨17364798704187178096203655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92612259755664949846419493 17364798704187178096203655)
      ·
        refine ⟨26047198056280767144305483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17364798704187178096203655 26047198056280767144305483)
        ·
          refine ⟨39070797084421150716458225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26047198056280767144305483 39070797084421150716458225)
          ·
            refine ⟨29303097813315863037343669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39070797084421150716458225 29303097813315863037343669)
            ·
              refine ⟨2747165419998362159750969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29303097813315863037343669 2747165419998362159750969)
              ·
                refine ⟨2060374064998771619813227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2747165419998362159750969 2060374064998771619813227)
                ·
                  refine ⟨3090561097498157429719841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2060374064998771619813227 3090561097498157429719841)
                  ·
                    refine ⟨2317920823123618072289881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3090561097498157429719841 2317920823123618072289881)
                    ·
                      refine ⟨1738440617342713554217411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2317920823123618072289881 1738440617342713554217411)
                      ·
                        rfl

theorem cell23_3385601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 5, 2, 1, 2, 2].length) (baseStart_3385601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3385601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3385601 prefixEnd_3385601 := by exact prefixLift 3385601
  have htrace : WordTrace (prefixWord ++ tailWord_3385601) baseStart_3385601 baseEnd_3385601 := by
    simpa [prefixWord, tailWord_3385601, baseEnd_3385601] using wordTrace_append hprefix tailTrace_3385601
  have hstable : (prefixWord ++ tailWord_3385601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3385601).length < 2 ^ (prefixWord ++ tailWord_3385601).sum := by decide
  have hdescent : baseEnd_3385601 < baseStart_3385601 := by decide
  rcases family_descends (prefixWord ++ tailWord_3385601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3385617 : List Nat := [1, 2, 2, 1, 1, 6, 1, 3, 2, 1, 3]
def baseStart_3385617 : Nat := 118140960795 + 3385617 * 2 ^ 59
def prefixEnd_3385617 : Nat := 4983230072969 + 3 ^ 40 * 3385617 * 2
def baseEnd_3385617 : Nat := 1738448833033185491617337

theorem tailTrace_3385617 : CollatzResearch.WordTrace tailWord_3385617 prefixEnd_3385617 1738448833033185491617337 := by
  unfold tailWord_3385617
  simp only [CollatzResearch.WordTrace]
  refine ⟨123483596575495301194475105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82322397716996867462983403 123483596575495301194475105)
  ·
    refine ⟨92612697431621475895856329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123483596575495301194475105 92612697431621475895856329)
    ·
      refine ⟨69459523073716106921892247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92612697431621475895856329 69459523073716106921892247)
      ·
        refine ⟨104189284610574160382838371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69459523073716106921892247 104189284610574160382838371)
        ·
          refine ⟨156283926915861240574257557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104189284610574160382838371 156283926915861240574257557)
          ·
            refine ⟨7325809074180995651918323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 156283926915861240574257557 7325809074180995651918323)
            ·
              refine ⟨10988713611271493477877485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7325809074180995651918323 10988713611271493477877485)
              ·
                refine ⟨4120767604226810054204057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10988713611271493477877485 4120767604226810054204057)
                ·
                  refine ⟨3090575703170107540653043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4120767604226810054204057 3090575703170107540653043)
                  ·
                    refine ⟨4635863554755161310979565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3090575703170107540653043 4635863554755161310979565)
                    ·
                      refine ⟨1738448833033185491617337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4635863554755161310979565 1738448833033185491617337)
                      ·
                        rfl

theorem cell23_3385617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 3, 2, 1, 3].length) (baseStart_3385617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3385617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3385617 prefixEnd_3385617 := by exact prefixLift 3385617
  have htrace : WordTrace (prefixWord ++ tailWord_3385617) baseStart_3385617 baseEnd_3385617 := by
    simpa [prefixWord, tailWord_3385617, baseEnd_3385617] using wordTrace_append hprefix tailTrace_3385617
  have hstable : (prefixWord ++ tailWord_3385617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3385617).length < 2 ^ (prefixWord ++ tailWord_3385617).sum := by decide
  have hdescent : baseEnd_3385617 < baseStart_3385617 := by decide
  rcases family_descends (prefixWord ++ tailWord_3385617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3385627 : List Nat := [1, 1, 1, 1, 1, 1, 9, 2, 1, 3, 2]
def baseStart_3385627 : Nat := 118140960795 + 3385627 * 2 ^ 59
def prefixEnd_3385627 : Nat := 4983230072969 + 3 ^ 40 * 3385627 * 2
def baseEnd_3385627 : Nat := 1738453967839730452492291

theorem tailTrace_3385627 : CollatzResearch.WordTrace tailWord_3385627 prefixEnd_3385627 1738453967839730452492291 := by
  unfold tailWord_3385627
  simp only [CollatzResearch.WordTrace]
  refine ⟨123483961305459072902339135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82322640870306048601559423 123483961305459072902339135)
  ·
    refine ⟨185225941958188609353508703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123483961305459072902339135 185225941958188609353508703)
    ·
      refine ⟨277838912937282914030263055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185225941958188609353508703 277838912937282914030263055)
      ·
        refine ⟨416758369405924371045394583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277838912937282914030263055 416758369405924371045394583)
        ·
          refine ⟨625137554108886556568091875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 416758369405924371045394583 625137554108886556568091875)
          ·
            refine ⟨937706331163329834852137813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 625137554108886556568091875 937706331163329834852137813)
            ·
              refine ⟨5494373034160135751086745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 937706331163329834852137813 5494373034160135751086745)
              ·
                refine ⟨4120779775620101813315059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5494373034160135751086745 4120779775620101813315059)
                ·
                  refine ⟨6181169663430152719972589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4120779775620101813315059 6181169663430152719972589)
                  ·
                    refine ⟨2317938623786307269989721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6181169663430152719972589 2317938623786307269989721)
                    ·
                      refine ⟨1738453967839730452492291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2317938623786307269989721 1738453967839730452492291)
                      ·
                        rfl

theorem cell23_3385627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 9, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 9, 2, 1, 3, 2].length) (baseStart_3385627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3385627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3385627 prefixEnd_3385627 := by exact prefixLift 3385627
  have htrace : WordTrace (prefixWord ++ tailWord_3385627) baseStart_3385627 baseEnd_3385627 := by
    simpa [prefixWord, tailWord_3385627, baseEnd_3385627] using wordTrace_append hprefix tailTrace_3385627
  have hstable : (prefixWord ++ tailWord_3385627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3385627).length < 2 ^ (prefixWord ++ tailWord_3385627).sum := by decide
  have hdescent : baseEnd_3385627 < baseStart_3385627 := by decide
  rcases family_descends (prefixWord ++ tailWord_3385627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3385663 : List Nat := [1, 1, 2, 2, 4, 1, 2, 3, 7]
def baseStart_3385663 : Nat := 118140960795 + 3385663 * 2 ^ 59
def prefixEnd_3385663 : Nat := 4983230072969 + 3 ^ 40 * 3385663 * 2
def baseEnd_3385663 : Nat := 193163605904810256849125

theorem tailTrace_3385663 : CollatzResearch.WordTrace tailWord_3385663 prefixEnd_3385663 193163605904810256849125 := by
  unfold tailWord_3385663
  simp only [CollatzResearch.WordTrace]
  refine ⟨123485274333328651050649643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82323516222219100700433095 123485274333328651050649643)
  ·
    refine ⟨185227911499992976575974465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123485274333328651050649643 185227911499992976575974465)
    ·
      refine ⟨138920933624994732431980849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185227911499992976575974465 138920933624994732431980849)
      ·
        refine ⟨104190700218746049323985637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138920933624994732431980849 104190700218746049323985637)
        ·
          refine ⟨19535756291014884248247307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104190700218746049323985637 19535756291014884248247307)
          ·
            refine ⟨29303634436522326372370961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19535756291014884248247307 29303634436522326372370961)
            ·
              refine ⟨21977725827391744779278221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29303634436522326372370961 21977725827391744779278221)
              ·
                refine ⟨8241647185271904292229333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21977725827391744779278221 8241647185271904292229333)
                ·
                  refine ⟨193163605904810256849125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8241647185271904292229333 193163605904810256849125)
                  ·
                    rfl

theorem cell23_3385663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 3, 7].length) (baseStart_3385663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3385663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3385663 prefixEnd_3385663 := by exact prefixLift 3385663
  have htrace : WordTrace (prefixWord ++ tailWord_3385663) baseStart_3385663 baseEnd_3385663 := by
    simpa [prefixWord, tailWord_3385663, baseEnd_3385663] using wordTrace_append hprefix tailTrace_3385663
  have hstable : (prefixWord ++ tailWord_3385663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3385663).length < 2 ^ (prefixWord ++ tailWord_3385663).sum := by decide
  have hdescent : baseEnd_3385663 < baseStart_3385663 := by decide
  rcases family_descends (prefixWord ++ tailWord_3385663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3385708 : List Nat := [2, 2, 1, 1, 7, 1, 1, 2, 2, 2, 2]
def baseStart_3385708 : Nat := 118140960795 + 3385708 * 2 ^ 59
def prefixEnd_3385708 : Nat := 4983230072969 + 3 ^ 40 * 3385708 * 2
def baseEnd_3385708 : Nat := 1738495559772744635579419

theorem tailTrace_3385708 : CollatzResearch.WordTrace tailWord_3385708 prefixEnd_3385708 1738495559772744635579419 := by
  unfold tailWord_3385708
  simp only [CollatzResearch.WordTrace]
  refine ⟨61743457809082811868018889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82324610412110415824025185 61743457809082811868018889)
  ·
    refine ⟨46307593356812108901014167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61743457809082811868018889 46307593356812108901014167)
    ·
      refine ⟨69461390035218163351521251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46307593356812108901014167 69461390035218163351521251)
      ·
        refine ⟨104192085052827245027281877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69461390035218163351521251 104192085052827245027281877)
        ·
          refine ⟨2442001993425638555326919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 104192085052827245027281877 2442001993425638555326919)
          ·
            refine ⟨3663002990138457832990379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2442001993425638555326919 3663002990138457832990379)
            ·
              refine ⟨5494504485207686749485569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3663002990138457832990379 5494504485207686749485569)
              ·
                refine ⟨4120878363905765062114177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5494504485207686749485569 4120878363905765062114177)
                ·
                  refine ⟨3090658772929323796585633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4120878363905765062114177 3090658772929323796585633)
                  ·
                    refine ⟨2317994079696992847439225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3090658772929323796585633 2317994079696992847439225)
                    ·
                      refine ⟨1738495559772744635579419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2317994079696992847439225 1738495559772744635579419)
                      ·
                        rfl

theorem cell23_3385708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 1, 2, 2, 2, 2].length) (baseStart_3385708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3385708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3385708 prefixEnd_3385708 := by exact prefixLift 3385708
  have htrace : WordTrace (prefixWord ++ tailWord_3385708) baseStart_3385708 baseEnd_3385708 := by
    simpa [prefixWord, tailWord_3385708, baseEnd_3385708] using wordTrace_append hprefix tailTrace_3385708
  have hstable : (prefixWord ++ tailWord_3385708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3385708).length < 2 ^ (prefixWord ++ tailWord_3385708).sum := by decide
  have hdescent : baseEnd_3385708 < baseStart_3385708 := by decide
  rcases family_descends (prefixWord ++ tailWord_3385708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3385753 : List Nat := [1, 2, 1, 2, 1, 4, 1, 1, 10]
def baseStart_3385753 : Nat := 118140960795 + 3385753 * 2 ^ 59
def prefixEnd_3385753 : Nat := 4983230072969 + 3 ^ 40 * 3385753 * 2
def baseEnd_3385753 : Nat := 193168740711355217724079

theorem tailTrace_3385753 : CollatzResearch.WordTrace tailWord_3385753 prefixEnd_3385753 193168740711355217724079 := by
  unfold tailWord_3385753
  simp only [CollatzResearch.WordTrace]
  refine ⟨123488556903002596421425913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82325704602001730947617275 123488556903002596421425913)
  ·
    refine ⟨92616417677251947316069435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123488556903002596421425913 92616417677251947316069435)
    ·
      refine ⟨138924626515877920974104153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92616417677251947316069435 138924626515877920974104153)
      ·
        refine ⟨104193469886908440730578115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138924626515877920974104153 104193469886908440730578115)
        ·
          refine ⟨156290204830362661095867173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104193469886908440730578115 156290204830362661095867173)
          ·
            refine ⟨29304413405692998955475095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 156290204830362661095867173 29304413405692998955475095)
            ·
              refine ⟨43956620108539498433212643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29304413405692998955475095 43956620108539498433212643)
              ·
                refine ⟨65934930162809247649818965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43956620108539498433212643 65934930162809247649818965)
                ·
                  refine ⟨193168740711355217724079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 65934930162809247649818965 193168740711355217724079)
                  ·
                    rfl

theorem cell23_3385753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 10].length) (baseStart_3385753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3385753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3385753 prefixEnd_3385753 := by exact prefixLift 3385753
  have htrace : WordTrace (prefixWord ++ tailWord_3385753) baseStart_3385753 baseEnd_3385753 := by
    simpa [prefixWord, tailWord_3385753, baseEnd_3385753] using wordTrace_append hprefix tailTrace_3385753
  have hstable : (prefixWord ++ tailWord_3385753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3385753).length < 2 ^ (prefixWord ++ tailWord_3385753).sum := by decide
  have hdescent : baseEnd_3385753 < baseStart_3385753 := by decide
  rcases family_descends (prefixWord ++ tailWord_3385753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3385767 : List Nat := [1, 1, 6, 1, 1, 2, 1, 1, 4, 2, 3]
def baseStart_3385767 : Nat := 118140960795 + 3385767 * 2 ^ 59
def prefixEnd_3385767 : Nat := 4983230072969 + 3 ^ 40 * 3385767 * 2
def baseEnd_3385767 : Nat := 1738525855131359904741647

theorem tailTrace_3385767 : CollatzResearch.WordTrace tailWord_3385767 prefixEnd_3385767 1738525855131359904741647 := by
  unfold tailWord_3385767
  simp only [CollatzResearch.WordTrace]
  refine ⟨123489067524951876812435555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82326045016634584541623703 123489067524951876812435555)
  ·
    refine ⟨185233601287427815218653333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123489067524951876812435555 185233601287427815218653333)
    ·
      refine ⟨8682825060348178838374375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 185233601287427815218653333 8682825060348178838374375)
      ·
        refine ⟨13024237590522268257561563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8682825060348178838374375 13024237590522268257561563)
        ·
          refine ⟨19536356385783402386342345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13024237590522268257561563 19536356385783402386342345)
          ·
            refine ⟨14652267289337551789756759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19536356385783402386342345 14652267289337551789756759)
            ·
              refine ⟨21978400934006327684635139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14652267289337551789756759 21978400934006327684635139)
              ·
                refine ⟨32967601401009491526952709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21978400934006327684635139 32967601401009491526952709)
                ·
                  refine ⟨6181425262689279661303633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32967601401009491526952709 6181425262689279661303633)
                  ·
                    refine ⟨4636068947016959745977725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6181425262689279661303633 4636068947016959745977725)
                    ·
                      refine ⟨1738525855131359904741647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4636068947016959745977725 1738525855131359904741647)
                      ·
                        rfl

theorem cell23_3385767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 1, 4, 2, 3].length) (baseStart_3385767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3385767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3385767 prefixEnd_3385767 := by exact prefixLift 3385767
  have htrace : WordTrace (prefixWord ++ tailWord_3385767) baseStart_3385767 baseEnd_3385767 := by
    simpa [prefixWord, tailWord_3385767, baseEnd_3385767] using wordTrace_append hprefix tailTrace_3385767
  have hstable : (prefixWord ++ tailWord_3385767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3385767).length < 2 ^ (prefixWord ++ tailWord_3385767).sum := by decide
  have hdescent : baseEnd_3385767 < baseStart_3385767 := by decide
  rcases family_descends (prefixWord ++ tailWord_3385767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3385790 : List Nat := [4, 2, 1, 1, 1, 1, 2, 2, 1, 2, 6]
def baseStart_3385790 : Nat := 118140960795 + 3385790 * 2 ^ 59
def prefixEnd_3385790 : Nat := 4983230072969 + 3 ^ 40 * 3385790 * 2
def baseEnd_3385790 : Nat := 1738537665186413314754041

theorem tailTrace_3385790 : CollatzResearch.WordTrace tailWord_3385790 prefixEnd_3385790 1738537665186413314754041 := by
  unfold tailWord_3385790
  simp only [CollatzResearch.WordTrace]
  refine ⟨15436238300483568967565353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82326604269245701160348549 15436238300483568967565353)
  ·
    refine ⟨11577178725362676725674015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15436238300483568967565353 11577178725362676725674015)
    ·
      refine ⟨17365768088044015088511023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11577178725362676725674015 17365768088044015088511023)
      ·
        refine ⟨26048652132066022632766535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17365768088044015088511023 26048652132066022632766535)
        ·
          refine ⟨39072978198099033949149803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26048652132066022632766535 39072978198099033949149803)
          ·
            refine ⟨58609467297148550923724705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39072978198099033949149803 58609467297148550923724705)
            ·
              refine ⟨43957100472861413192793529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58609467297148550923724705 43957100472861413192793529)
              ·
                refine ⟨32967825354646059894595147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43957100472861413192793529 32967825354646059894595147)
                ·
                  refine ⟨49451738031969089841892721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32967825354646059894595147 49451738031969089841892721)
                  ·
                    refine ⟨37088803523976817381419541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49451738031969089841892721 37088803523976817381419541)
                    ·
                      refine ⟨1738537665186413314754041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37088803523976817381419541 1738537665186413314754041)
                      ·
                        rfl

theorem cell23_3385790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 2, 1, 2, 6].length) (baseStart_3385790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3385790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3385790 prefixEnd_3385790 := by exact prefixLift 3385790
  have htrace : WordTrace (prefixWord ++ tailWord_3385790) baseStart_3385790 baseEnd_3385790 := by
    simpa [prefixWord, tailWord_3385790, baseEnd_3385790] using wordTrace_append hprefix tailTrace_3385790
  have hstable : (prefixWord ++ tailWord_3385790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3385790).length < 2 ^ (prefixWord ++ tailWord_3385790).sum := by decide
  have hdescent : baseEnd_3385790 < baseStart_3385790 := by decide
  rcases family_descends (prefixWord ++ tailWord_3385790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3385831 : List Nat := [1, 1, 5, 2, 1, 1, 3, 4, 1, 1, 3]
def baseStart_3385831 : Nat := 118140960795 + 3385831 * 2 ^ 59
def prefixEnd_3385831 : Nat := 4983230072969 + 3 ^ 40 * 3385831 * 2
def baseEnd_3385831 : Nat := 1738558717893247654341353

theorem tailTrace_3385831 : CollatzResearch.WordTrace tailWord_3385831 prefixEnd_3385831 1738558717893247654341353 := by
  unfold tailWord_3385831
  simp only [CollatzResearch.WordTrace]
  refine ⟨123491401796720015742765347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82327601197813343828510231 123491401796720015742765347)
  ·
    refine ⟨185237102695080023614148021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123491401796720015742765347 185237102695080023614148021)
    ·
      refine ⟨17365978377663752213826377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 185237102695080023614148021 17365978377663752213826377)
      ·
        refine ⟨13024483783247814160369783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17365978377663752213826377 13024483783247814160369783)
        ·
          refine ⟨19536725674871721240554675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13024483783247814160369783 19536725674871721240554675)
          ·
            refine ⟨29305088512307581860832013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19536725674871721240554675 29305088512307581860832013)
            ·
              refine ⟨10989408192115343197812005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29305088512307581860832013 10989408192115343197812005)
              ·
                refine ⟨2060514036021626849589751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10989408192115343197812005 2060514036021626849589751)
                ·
                  refine ⟨3090771054032440274384627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2060514036021626849589751 3090771054032440274384627)
                  ·
                    refine ⟨4636156581048660411576941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3090771054032440274384627 4636156581048660411576941)
                    ·
                      refine ⟨1738558717893247654341353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4636156581048660411576941 1738558717893247654341353)
                      ·
                        rfl

theorem cell23_3385831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 4, 1, 1, 3].length) (baseStart_3385831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3385831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3385831 prefixEnd_3385831 := by exact prefixLift 3385831
  have htrace : WordTrace (prefixWord ++ tailWord_3385831) baseStart_3385831 baseEnd_3385831 := by
    simpa [prefixWord, tailWord_3385831, baseEnd_3385831] using wordTrace_append hprefix tailTrace_3385831
  have hstable : (prefixWord ++ tailWord_3385831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3385831).length < 2 ^ (prefixWord ++ tailWord_3385831).sum := by decide
  have hdescent : baseEnd_3385831 < baseStart_3385831 := by decide
  rcases family_descends (prefixWord ++ tailWord_3385831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3385840 : List Nat := [2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 5]
def baseStart_3385840 : Nat := 118140960795 + 3385840 * 2 ^ 59
def prefixEnd_3385840 : Nat := 4983230072969 + 3 ^ 40 * 3385840 * 2
def baseEnd_3385840 : Nat := 1738563339219138119128811

theorem tailTrace_3385840 : CollatzResearch.WordTrace tailWord_3385840 prefixEnd_3385840 1738563339219138119128811 := by
  unfold tailWord_3385840
  simp only [CollatzResearch.WordTrace]
  refine ⟨61745865026843705139921487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82327820035791606853228649 61745865026843705139921487)
  ·
    refine ⟨92618797540265557709882231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61745865026843705139921487 92618797540265557709882231)
    ·
      refine ⟨138928196310398336564823347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92618797540265557709882231 138928196310398336564823347)
      ·
        refine ⟨208392294465597504847235021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138928196310398336564823347 208392294465597504847235021)
        ·
          refine ⟨78147110424599064317713133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 208392294465597504847235021 78147110424599064317713133)
          ·
            refine ⟨29305166409224649119142425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78147110424599064317713133 29305166409224649119142425)
            ·
              refine ⟨21978874806918486839356819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29305166409224649119142425 21978874806918486839356819)
              ·
                refine ⟨32968312210377730259035229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21978874806918486839356819 32968312210377730259035229)
                ·
                  refine ⟨12363117078891648847138211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32968312210377730259035229 12363117078891648847138211)
                  ·
                    refine ⟨18544675618337473270707317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12363117078891648847138211 18544675618337473270707317)
                    ·
                      refine ⟨1738563339219138119128811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18544675618337473270707317 1738563339219138119128811)
                      ·
                        rfl

theorem cell23_3385840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 5].length) (baseStart_3385840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3385840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3385840 prefixEnd_3385840 := by exact prefixLift 3385840
  have htrace : WordTrace (prefixWord ++ tailWord_3385840) baseStart_3385840 baseEnd_3385840 := by
    simpa [prefixWord, tailWord_3385840, baseEnd_3385840] using wordTrace_append hprefix tailTrace_3385840
  have hstable : (prefixWord ++ tailWord_3385840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3385840).length < 2 ^ (prefixWord ++ tailWord_3385840).sum := by decide
  have hdescent : baseEnd_3385840 < baseStart_3385840 := by decide
  rcases family_descends (prefixWord ++ tailWord_3385840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3385867 : List Nat := [1, 1, 1, 1, 7, 1, 2, 2, 1, 2, 4]
def baseStart_3385867 : Nat := 118140960795 + 3385867 * 2 ^ 59
def prefixEnd_3385867 : Nat := 4983230072969 + 3 ^ 40 * 3385867 * 2
def baseEnd_3385867 : Nat := 1738577203196809513491187

theorem tailTrace_3385867 : CollatzResearch.WordTrace tailWord_3385867 prefixEnd_3385867 1738577203196809513491187 := by
  unfold tailWord_3385867
  simp only [CollatzResearch.WordTrace]
  refine ⟨123492714824589593891075855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82328476549726395927383903 123492714824589593891075855)
  ·
    refine ⟨185239072236884390836613783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123492714824589593891075855 185239072236884390836613783)
    ·
      refine ⟨277858608355326586254920675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185239072236884390836613783 277858608355326586254920675)
      ·
        refine ⟨416787912532989879382381013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277858608355326586254920675 416787912532989879382381013)
        ·
          refine ⟨9768466699991950298024555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 416787912532989879382381013 9768466699991950298024555)
          ·
            refine ⟨14652700049987925447036833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9768466699991950298024555 14652700049987925447036833)
            ·
              refine ⟨10989525037490944085277625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14652700049987925447036833 10989525037490944085277625)
              ·
                refine ⟨8242143778118208063958219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10989525037490944085277625 8242143778118208063958219)
                ·
                  refine ⟨12363215667177312095937329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8242143778118208063958219 12363215667177312095937329)
                  ·
                    refine ⟨9272411750382984071952997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12363215667177312095937329 9272411750382984071952997)
                    ·
                      refine ⟨1738577203196809513491187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9272411750382984071952997 1738577203196809513491187)
                      ·
                        rfl

theorem cell23_3385867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 2, 1, 2, 4].length) (baseStart_3385867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3385867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3385867 prefixEnd_3385867 := by exact prefixLift 3385867
  have htrace : WordTrace (prefixWord ++ tailWord_3385867) baseStart_3385867 baseEnd_3385867 := by
    simpa [prefixWord, tailWord_3385867, baseEnd_3385867] using wordTrace_append hprefix tailTrace_3385867
  have hstable : (prefixWord ++ tailWord_3385867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3385867).length < 2 ^ (prefixWord ++ tailWord_3385867).sum := by decide
  have hdescent : baseEnd_3385867 < baseStart_3385867 := by decide
  rcases family_descends (prefixWord ++ tailWord_3385867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3385871 : List Nat := [1, 1, 2, 1, 1, 1, 2, 9, 1, 2, 2]
def baseStart_3385871 : Nat := 118140960795 + 3385871 * 2 ^ 59
def prefixEnd_3385871 : Nat := 4983230072969 + 3 ^ 40 * 3385871 * 2
def baseEnd_3385871 : Nat := 1738579257119427497841169

theorem tailTrace_3385871 : CollatzResearch.WordTrace tailWord_3385871 prefixEnd_3385871 1738579257119427497841169 := by
  unfold tailWord_3385871
  simp only [CollatzResearch.WordTrace]
  refine ⟨123492860716575102574221467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82328573811050068382814311 123492860716575102574221467)
  ·
    refine ⟨185239291074862653861332201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123492860716575102574221467 185239291074862653861332201)
    ·
      refine ⟨138929468306146990395999151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185239291074862653861332201 138929468306146990395999151)
      ·
        refine ⟨208394202459220485593998727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138929468306146990395999151 208394202459220485593998727)
        ·
          refine ⟨312591303688830728390998091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208394202459220485593998727 312591303688830728390998091)
          ·
            refine ⟨468886955533246092586497137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 312591303688830728390998091 468886955533246092586497137)
            ·
              refine ⟨351665216649934569439872853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 468886955533246092586497137 351665216649934569439872853)
              ·
                refine ⟨2060538378808210367811755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 351665216649934569439872853 2060538378808210367811755)
                ·
                  refine ⟨3090807568212315551717633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2060538378808210367811755 3090807568212315551717633)
                  ·
                    refine ⟨2318105676159236663788225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3090807568212315551717633 2318105676159236663788225)
                    ·
                      refine ⟨1738579257119427497841169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2318105676159236663788225 1738579257119427497841169)
                      ·
                        rfl

theorem cell23_3385871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 9, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 9, 1, 2, 2].length) (baseStart_3385871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3385871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3385871 prefixEnd_3385871 := by exact prefixLift 3385871
  have htrace : WordTrace (prefixWord ++ tailWord_3385871) baseStart_3385871 baseEnd_3385871 := by
    simpa [prefixWord, tailWord_3385871, baseEnd_3385871] using wordTrace_append hprefix tailTrace_3385871
  have hstable : (prefixWord ++ tailWord_3385871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3385871).length < 2 ^ (prefixWord ++ tailWord_3385871).sum := by decide
  have hdescent : baseEnd_3385871 < baseStart_3385871 := by decide
  rcases family_descends (prefixWord ++ tailWord_3385871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3385888 : List Nat := [2, 1, 1, 6, 2, 1, 2, 1, 3, 2, 2]
def baseStart_3385888 : Nat := 118140960795 + 3385888 * 2 ^ 59
def prefixEnd_3385888 : Nat := 4983230072969 + 3 ^ 40 * 3385888 * 2
def baseEnd_3385888 : Nat := 1738587986290553931328591

theorem tailTrace_3385888 : CollatzResearch.WordTrace tailWord_3385888 prefixEnd_3385888 1738587986290553931328591 := by
  unfold tailWord_3385888
  simp only [CollatzResearch.WordTrace]
  refine ⟨61746740378756757238795159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82328987171675676318393545 61746740378756757238795159)
  ·
    refine ⟨92620110568135135858192739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61746740378756757238795159 92620110568135135858192739)
    ·
      refine ⟨138930165852202703787289109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92620110568135135858192739 138930165852202703787289109)
      ·
        refine ⟨6512351524322001740029177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 138930165852202703787289109 6512351524322001740029177)
        ·
          refine ⟨4884263643241501305021883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6512351524322001740029177 4884263643241501305021883)
          ·
            refine ⟨7326395464862251957532825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4884263643241501305021883 7326395464862251957532825)
            ·
              refine ⟨5494796598646688968149619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7326395464862251957532825 5494796598646688968149619)
              ·
                refine ⟨8242194897970033452224429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5494796598646688968149619 8242194897970033452224429)
                ·
                  refine ⟨3090823086738762544584161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8242194897970033452224429 3090823086738762544584161)
                  ·
                    refine ⟨2318117315054071908438121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3090823086738762544584161 2318117315054071908438121)
                    ·
                      refine ⟨1738587986290553931328591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2318117315054071908438121 1738587986290553931328591)
                      ·
                        rfl

theorem cell23_3385888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 2, 1, 3, 2, 2].length) (baseStart_3385888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3385888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3385888 prefixEnd_3385888 := by exact prefixLift 3385888
  have htrace : WordTrace (prefixWord ++ tailWord_3385888) baseStart_3385888 baseEnd_3385888 := by
    simpa [prefixWord, tailWord_3385888, baseEnd_3385888] using wordTrace_append hprefix tailTrace_3385888
  have hstable : (prefixWord ++ tailWord_3385888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3385888).length < 2 ^ (prefixWord ++ tailWord_3385888).sum := by decide
  have hdescent : baseEnd_3385888 < baseStart_3385888 := by decide
  rcases family_descends (prefixWord ++ tailWord_3385888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3385900 : List Nat := [2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 5]
def baseStart_3385900 : Nat := 118140960795 + 3385900 * 2 ^ 59
def prefixEnd_3385900 : Nat := 4983230072969 + 3 ^ 40 * 3385900 * 2
def baseEnd_3385900 : Nat := 1738594148058407884378535

theorem tailTrace_3385900 : CollatzResearch.WordTrace tailWord_3385900 prefixEnd_3385900 1738594148058407884378535 := by
  unfold tailWord_3385900
  simp only [CollatzResearch.WordTrace]
  refine ⟨61746959216735020263513577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82329278955646693684684769 61746959216735020263513577)
  ·
    refine ⟨46310219412551265197635183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61746959216735020263513577 46310219412551265197635183)
    ·
      refine ⟨69465329118826897796452775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46310219412551265197635183 69465329118826897796452775)
      ·
        refine ⟨104197993678240346694679163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69465329118826897796452775 104197993678240346694679163)
        ·
          refine ⟨156296990517360520042018745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104197993678240346694679163 156296990517360520042018745)
          ·
            refine ⟨117222742888020390031514059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156296990517360520042018745 117222742888020390031514059)
            ·
              refine ⟨175834114332030585047271089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117222742888020390031514059 175834114332030585047271089)
              ·
                refine ⟨131875585749022938785453317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 175834114332030585047271089 131875585749022938785453317)
                ·
                  refine ⟨24726672327941801022272497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 131875585749022938785453317 24726672327941801022272497)
                  ·
                    refine ⟨18545004245956350766704373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24726672327941801022272497 18545004245956350766704373)
                    ·
                      refine ⟨1738594148058407884378535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18545004245956350766704373 1738594148058407884378535)
                      ·
                        rfl

theorem cell23_3385900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 5].length) (baseStart_3385900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3385900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3385900 prefixEnd_3385900 := by exact prefixLift 3385900
  have htrace : WordTrace (prefixWord ++ tailWord_3385900) baseStart_3385900 baseEnd_3385900 := by
    simpa [prefixWord, tailWord_3385900, baseEnd_3385900] using wordTrace_append hprefix tailTrace_3385900
  have hstable : (prefixWord ++ tailWord_3385900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3385900).length < 2 ^ (prefixWord ++ tailWord_3385900).sum := by decide
  have hdescent : baseEnd_3385900 < baseStart_3385900 := by decide
  rcases family_descends (prefixWord ++ tailWord_3385900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3385904 : List Nat := [2, 1, 1, 1, 2, 3, 2, 5, 2, 1, 3]
def baseStart_3385904 : Nat := 118140960795 + 3385904 * 2 ^ 59
def prefixEnd_3385904 : Nat := 4983230072969 + 3 ^ 40 * 3385904 * 2
def baseEnd_3385904 : Nat := 1738596201981025868728517

theorem tailTrace_3385904 : CollatzResearch.WordTrace tailWord_3385904 prefixEnd_3385904 1738596201981025868728517 := by
  unfold tailWord_3385904
  simp only [CollatzResearch.WordTrace]
  refine ⟨61747032162727774605086383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82329376216970366140115177 61747032162727774605086383)
  ·
    refine ⟨92620548244091661907629575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61747032162727774605086383 92620548244091661907629575)
    ·
      refine ⟨138930822366137492861444363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92620548244091661907629575 138930822366137492861444363)
      ·
        refine ⟨208396233549206239292166545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138930822366137492861444363 208396233549206239292166545)
        ·
          refine ⟨156297175161904679469124909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208396233549206239292166545 156297175161904679469124909)
          ·
            refine ⟨58611440685714254800921841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 156297175161904679469124909 58611440685714254800921841)
            ·
              refine ⟨43958580514285691100691381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58611440685714254800921841 43958580514285691100691381)
              ·
                refine ⟨4121116923214283540689817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43958580514285691100691381 4121116923214283540689817)
                ·
                  refine ⟨3090837692410712655517363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4121116923214283540689817 3090837692410712655517363)
                  ·
                    refine ⟨4636256538616068983276045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3090837692410712655517363 4636256538616068983276045)
                    ·
                      refine ⟨1738596201981025868728517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4636256538616068983276045 1738596201981025868728517)
                      ·
                        rfl

theorem cell23_3385904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 5, 2, 1, 3].length) (baseStart_3385904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3385904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3385904 prefixEnd_3385904 := by exact prefixLift 3385904
  have htrace : WordTrace (prefixWord ++ tailWord_3385904) baseStart_3385904 baseEnd_3385904 := by
    simpa [prefixWord, tailWord_3385904, baseEnd_3385904] using wordTrace_append hprefix tailTrace_3385904
  have hstable : (prefixWord ++ tailWord_3385904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3385904).length < 2 ^ (prefixWord ++ tailWord_3385904).sum := by decide
  have hdescent : baseEnd_3385904 < baseStart_3385904 := by decide
  rcases family_descends (prefixWord ++ tailWord_3385904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3385917 : List Nat := [1, 4, 1, 3, 2, 1, 1, 1, 2, 2, 5]
def baseStart_3385917 : Nat := 118140960795 + 3385917 * 2 ^ 59
def prefixEnd_3385917 : Nat := 4983230072969 + 3 ^ 40 * 3385917 * 2
def baseEnd_3385917 : Nat := 1738602877229534317865957

theorem tailTrace_3385917 : CollatzResearch.WordTrace tailWord_3385917 prefixEnd_3385917 1738602877229534317865957 := by
  unfold tailWord_3385917
  simp only [CollatzResearch.WordTrace]
  refine ⟨123494538474408452430396005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82329692316272301620264003 123494538474408452430396005)
  ·
    refine ⟨23155225963951584830699251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123494538474408452430396005 23155225963951584830699251)
    ·
      refine ⟨34732838945927377246048877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23155225963951584830699251 34732838945927377246048877)
      ·
        refine ⟨13024814604722766467268329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34732838945927377246048877 13024814604722766467268329)
        ·
          refine ⟨9768610953542074850451247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13024814604722766467268329 9768610953542074850451247)
          ·
            refine ⟨14652916430313112275676871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9768610953542074850451247 14652916430313112275676871)
            ·
              refine ⟨21979374645469668413515307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14652916430313112275676871 21979374645469668413515307)
              ·
                refine ⟨32969061968204502620272961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21979374645469668413515307 32969061968204502620272961)
                ·
                  refine ⟨24726796476153376965204721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32969061968204502620272961 24726796476153376965204721)
                  ·
                    refine ⟨18545097357115032723903541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24726796476153376965204721 18545097357115032723903541)
                    ·
                      refine ⟨1738602877229534317865957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18545097357115032723903541 1738602877229534317865957)
                      ·
                        rfl

theorem cell23_3385917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_3385917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3385917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3385917 prefixEnd_3385917 := by exact prefixLift 3385917
  have htrace : WordTrace (prefixWord ++ tailWord_3385917) baseStart_3385917 baseEnd_3385917 := by
    simpa [prefixWord, tailWord_3385917, baseEnd_3385917] using wordTrace_append hprefix tailTrace_3385917
  have hstable : (prefixWord ++ tailWord_3385917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3385917).length < 2 ^ (prefixWord ++ tailWord_3385917).sum := by decide
  have hdescent : baseEnd_3385917 < baseStart_3385917 := by decide
  rcases family_descends (prefixWord ++ tailWord_3385917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3385920 : List Nat := [2, 1, 1, 2, 2, 2, 2, 2, 1, 8]
def baseStart_3385920 : Nat := 118140960795 + 3385920 * 2 ^ 59
def prefixEnd_3385920 : Nat := 4983230072969 + 3 ^ 40 * 3385920 * 2
def baseEnd_3385920 : Nat := 579534805890499268709481

theorem tailTrace_3385920 : CollatzResearch.WordTrace tailWord_3385920 prefixEnd_3385920 579534805890499268709481 := by
  unfold tailWord_3385920
  simp only [CollatzResearch.WordTrace]
  refine ⟨61747323946698791971377607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82329765262265055961836809 61747323946698791971377607)
  ·
    refine ⟨92620985920048187957066411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61747323946698791971377607 92620985920048187957066411)
    ·
      refine ⟨138931478880072281935599617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92620985920048187957066411 138931478880072281935599617)
      ·
        refine ⟨104198609160054211451699713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138931478880072281935599617 104198609160054211451699713)
        ·
          refine ⟨78148956870040658588774785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104198609160054211451699713 78148956870040658588774785)
          ·
            refine ⟨58611717652530493941581089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78148956870040658588774785 58611717652530493941581089)
            ·
              refine ⟨43958788239397870456185817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58611717652530493941581089 43958788239397870456185817)
              ·
                refine ⟨32969091179548402842139363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43958788239397870456185817 32969091179548402842139363)
                ·
                  refine ⟨49453636769322604263209045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32969091179548402842139363 49453636769322604263209045)
                  ·
                    refine ⟨579534805890499268709481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 49453636769322604263209045 579534805890499268709481)
                    ·
                      rfl

theorem cell23_3385920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 2, 1, 8].length) (baseStart_3385920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3385920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3385920 prefixEnd_3385920 := by exact prefixLift 3385920
  have htrace : WordTrace (prefixWord ++ tailWord_3385920) baseStart_3385920 baseEnd_3385920 := by
    simpa [prefixWord, tailWord_3385920, baseEnd_3385920] using wordTrace_append hprefix tailTrace_3385920
  have hstable : (prefixWord ++ tailWord_3385920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3385920).length < 2 ^ (prefixWord ++ tailWord_3385920).sum := by decide
  have hdescent : baseEnd_3385920 < baseStart_3385920 := by decide
  rcases family_descends (prefixWord ++ tailWord_3385920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3386007 : List Nat := [1, 1, 3, 3, 2, 1, 1, 3, 1, 2, 5]
def baseStart_3386007 : Nat := 118140960795 + 3386007 * 2 ^ 59
def prefixEnd_3386007 : Nat := 4983230072969 + 3 ^ 40 * 3386007 * 2
def baseEnd_3386007 : Nat := 1738649090488438965740543

theorem tailTrace_3386007 : CollatzResearch.WordTrace tailWord_3386007 prefixEnd_3386007 1738649090488438965740543 := by
  unfold tailWord_3386007
  simp only [CollatzResearch.WordTrace]
  refine ⟨123497821044082397801172275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82331880696054931867448183 123497821044082397801172275)
  ·
    refine ⟨185246731566123596701758413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123497821044082397801172275 185246731566123596701758413)
    ·
      refine ⟨69467524337296348763159405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185246731566123596701758413 69467524337296348763159405)
      ·
        refine ⟨26050321626486130786184777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69467524337296348763159405 26050321626486130786184777)
        ·
          refine ⟨19537741219864598089638583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26050321626486130786184777 19537741219864598089638583)
          ·
            refine ⟨29306611829796897134457875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19537741219864598089638583 29306611829796897134457875)
            ·
              refine ⟨43959917744695345701686813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29306611829796897134457875 43959917744695345701686813)
              ·
                refine ⟨16484969154260754638132555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43959917744695345701686813 16484969154260754638132555)
                ·
                  refine ⟨24727453731391131957198833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16484969154260754638132555 24727453731391131957198833)
                  ·
                    refine ⟨18545590298543348967899125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24727453731391131957198833 18545590298543348967899125)
                    ·
                      refine ⟨1738649090488438965740543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18545590298543348967899125 1738649090488438965740543)
                      ·
                        rfl

theorem cell23_3386007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 3, 1, 2, 5].length) (baseStart_3386007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3386007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3386007 prefixEnd_3386007 := by exact prefixLift 3386007
  have htrace : WordTrace (prefixWord ++ tailWord_3386007) baseStart_3386007 baseEnd_3386007 := by
    simpa [prefixWord, tailWord_3386007, baseEnd_3386007] using wordTrace_append hprefix tailTrace_3386007
  have hstable : (prefixWord ++ tailWord_3386007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3386007).length < 2 ^ (prefixWord ++ tailWord_3386007).sum := by decide
  have hdescent : baseEnd_3386007 < baseStart_3386007 := by decide
  rcases family_descends (prefixWord ++ tailWord_3386007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3386014 : List Nat := [4, 3, 1, 1, 1, 1, 2, 2, 1, 7]
def baseStart_3386014 : Nat := 118140960795 + 3386014 * 2 ^ 59
def prefixEnd_3386014 : Nat := 4983230072969 + 3 ^ 40 * 3386014 * 2
def baseEnd_3386014 : Nat := 579550894951006812784337

theorem tailTrace_3386014 : CollatzResearch.WordTrace tailWord_3386014 prefixEnd_3386014 579550894951006812784337 := by
  unfold tailWord_3386014
  simp only [CollatzResearch.WordTrace]
  refine ⟨15437259544382129749584637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82332050903371358664451397 15437259544382129749584637)
  ·
    refine ⟨5788972329143298656094239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15437259544382129749584637 5788972329143298656094239)
    ·
      refine ⟨8683458493714947984141359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5788972329143298656094239 8683458493714947984141359)
      ·
        refine ⟨13025187740572421976212039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8683458493714947984141359 13025187740572421976212039)
        ·
          refine ⟨19537781610858632964318059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13025187740572421976212039 19537781610858632964318059)
          ·
            refine ⟨29306672416287949446477089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19537781610858632964318059 29306672416287949446477089)
            ·
              refine ⟨21980004312215962084857817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29306672416287949446477089 21980004312215962084857817)
              ·
                refine ⟨16485003234161971563643363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21980004312215962084857817 16485003234161971563643363)
                ·
                  refine ⟨24727504851242957345465045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16485003234161971563643363 24727504851242957345465045)
                  ·
                    refine ⟨579550894951006812784337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24727504851242957345465045 579550894951006812784337)
                    ·
                      rfl

theorem cell23_3386014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 2, 1, 7].length) (baseStart_3386014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3386014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3386014 prefixEnd_3386014 := by exact prefixLift 3386014
  have htrace : WordTrace (prefixWord ++ tailWord_3386014) baseStart_3386014 baseEnd_3386014 := by
    simpa [prefixWord, tailWord_3386014, baseEnd_3386014] using wordTrace_append hprefix tailTrace_3386014
  have hstable : (prefixWord ++ tailWord_3386014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3386014).length < 2 ^ (prefixWord ++ tailWord_3386014).sum := by decide
  have hdescent : baseEnd_3386014 < baseStart_3386014 := by decide
  rcases family_descends (prefixWord ++ tailWord_3386014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3386034 : List Nat := [3, 2, 1, 1, 1, 2, 1, 1, 3, 6, 2]
def baseStart_3386034 : Nat := 118140960795 + 3386034 * 2 ^ 59
def prefixEnd_3386034 : Nat := 4983230072969 + 3 ^ 40 * 3386034 * 2
def baseEnd_3386034 : Nat := 1738662954466110360102919

theorem tailTrace_3386034 : CollatzResearch.WordTrace tailWord_3386034 prefixEnd_3386034 1738662954466110360102919 := by
  unfold tailWord_3386034
  simp only [CollatzResearch.WordTrace]
  refine ⟨30874701453746145353101289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82332537209989720941603437 30874701453746145353101289)
  ·
    refine ⟨23156026090309609014825967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30874701453746145353101289 23156026090309609014825967)
    ·
      refine ⟨34734039135464413522238951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23156026090309609014825967 34734039135464413522238951)
      ·
        refine ⟨52101058703196620283358427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34734039135464413522238951 52101058703196620283358427)
        ·
          refine ⟨78151588054794930425037641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52101058703196620283358427 78151588054794930425037641)
          ·
            refine ⟨58613691041096197818778231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78151588054794930425037641 58613691041096197818778231)
            ·
              refine ⟨87920536561644296728167347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58613691041096197818778231 87920536561644296728167347)
              ·
                refine ⟨131880804842466445092251021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87920536561644296728167347 131880804842466445092251021)
                ·
                  refine ⟨49455301815924916909594133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 131880804842466445092251021 49455301815924916909594133)
                  ·
                    refine ⟨2318217272621480480137225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 49455301815924916909594133 2318217272621480480137225)
                    ·
                      refine ⟨1738662954466110360102919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2318217272621480480137225 1738662954466110360102919)
                      ·
                        rfl

theorem cell23_3386034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 3, 6, 2].length) (baseStart_3386034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3386034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3386034 prefixEnd_3386034 := by exact prefixLift 3386034
  have htrace : WordTrace (prefixWord ++ tailWord_3386034) baseStart_3386034 baseEnd_3386034 := by
    simpa [prefixWord, tailWord_3386034, baseEnd_3386034] using wordTrace_append hprefix tailTrace_3386034
  have hstable : (prefixWord ++ tailWord_3386034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3386034).length < 2 ^ (prefixWord ++ tailWord_3386034).sum := by decide
  have hdescent : baseEnd_3386034 < baseStart_3386034 := by decide
  rcases family_descends (prefixWord ++ tailWord_3386034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3386044 : List Nat := [2, 2, 2, 3, 1, 1, 1, 2, 5, 4]
def baseStart_3386044 : Nat := 118140960795 + 3386044 * 2 ^ 59
def prefixEnd_3386044 : Nat := 4983230072969 + 3 ^ 40 * 3386044 * 2
def baseEnd_3386044 : Nat := 579556029757551773659291

theorem tailTrace_3386044 : CollatzResearch.WordTrace tailWord_3386044 prefixEnd_3386044 579556029757551773659291 := by
  unfold tailWord_3386044
  simp only [CollatzResearch.WordTrace]
  refine ⟨61749585272474176560134593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82332780363298902080179457 61749585272474176560134593)
  ·
    refine ⟨46312188954355632420100945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61749585272474176560134593 46312188954355632420100945)
    ·
      refine ⟨34734141715766724315075709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46312188954355632420100945 34734141715766724315075709)
      ·
        refine ⟨13025303143412521618153391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34734141715766724315075709 13025303143412521618153391)
        ·
          refine ⟨19537954715118782427230087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13025303143412521618153391 19537954715118782427230087)
          ·
            refine ⟨29306932072678173640845131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19537954715118782427230087 29306932072678173640845131)
            ·
              refine ⟨43960398109017260461267697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29306932072678173640845131 43960398109017260461267697)
              ·
                refine ⟨32970298581762945345950773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43960398109017260461267697 32970298581762945345950773)
                ·
                  refine ⟨3090965492040276126182885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32970298581762945345950773 3090965492040276126182885)
                  ·
                    refine ⟨579556029757551773659291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3090965492040276126182885 579556029757551773659291)
                    ·
                      rfl

theorem cell23_3386044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 2, 5, 4].length) (baseStart_3386044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3386044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3386044 prefixEnd_3386044 := by exact prefixLift 3386044
  have htrace : WordTrace (prefixWord ++ tailWord_3386044) baseStart_3386044 baseEnd_3386044 := by
    simpa [prefixWord, tailWord_3386044, baseEnd_3386044] using wordTrace_append hprefix tailTrace_3386044
  have hstable : (prefixWord ++ tailWord_3386044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3386044).length < 2 ^ (prefixWord ++ tailWord_3386044).sum := by decide
  have hdescent : baseEnd_3386044 < baseStart_3386044 := by decide
  rcases family_descends (prefixWord ++ tailWord_3386044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3386047 : List Nat := [1, 1, 2, 2, 2, 4, 1, 1, 2, 1, 6]
def baseStart_3386047 : Nat := 118140960795 + 3386047 * 2 ^ 59
def prefixEnd_3386047 : Nat := 4983230072969 + 3 ^ 40 * 3386047 * 2
def baseEnd_3386047 : Nat := 1738669629714618809240359

theorem tailTrace_3386047 : CollatzResearch.WordTrace tailWord_3386047 prefixEnd_3386047 1738669629714618809240359 := by
  unfold tailWord_3386047
  simp only [CollatzResearch.WordTrace]
  refine ⟨123499279963937484632628395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82332853309291656421752263 123499279963937484632628395)
  ·
    refine ⟨185248919945906226948942593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123499279963937484632628395 185248919945906226948942593)
    ·
      refine ⟨138936689959429670211706945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185248919945906226948942593 138936689959429670211706945)
      ·
        refine ⟨104202517469572252658780209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138936689959429670211706945 104202517469572252658780209)
        ·
          refine ⟨78151888102179189494085157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104202517469572252658780209 78151888102179189494085157)
          ·
            refine ⟨14653479019158598030140967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78151888102179189494085157 14653479019158598030140967)
            ·
              refine ⟨21980218528737897045211451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14653479019158598030140967 21980218528737897045211451)
              ·
                refine ⟨32970327793106845567817177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21980218528737897045211451 32970327793106845567817177)
                ·
                  refine ⟨24727745844830134175862883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32970327793106845567817177 24727745844830134175862883)
                  ·
                    refine ⟨37091618767245201263794325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24727745844830134175862883 37091618767245201263794325)
                    ·
                      refine ⟨1738669629714618809240359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37091618767245201263794325 1738669629714618809240359)
                      ·
                        rfl

theorem cell23_3386047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 1, 2, 1, 6].length) (baseStart_3386047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3386047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3386047 prefixEnd_3386047 := by exact prefixLift 3386047
  have htrace : WordTrace (prefixWord ++ tailWord_3386047) baseStart_3386047 baseEnd_3386047 := by
    simpa [prefixWord, tailWord_3386047, baseEnd_3386047] using wordTrace_append hprefix tailTrace_3386047
  have hstable : (prefixWord ++ tailWord_3386047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3386047).length < 2 ^ (prefixWord ++ tailWord_3386047).sum := by decide
  have hdescent : baseEnd_3386047 < baseStart_3386047 := by decide
  rcases family_descends (prefixWord ++ tailWord_3386047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3386104 : List Nat := [2, 1, 2, 1, 1, 2, 3, 5, 1, 5]
def baseStart_3386104 : Nat := 118140960795 + 3386104 * 2 ^ 59
def prefixEnd_3386104 : Nat := 4983230072969 + 3 ^ 40 * 3386104 * 2
def baseEnd_3386104 : Nat := 579566299370641695409199

theorem tailTrace_3386104 : CollatzResearch.WordTrace tailWord_3386104 prefixEnd_3386104 579566299370641695409199 := by
  unfold tailWord_3386104
  simp only [CollatzResearch.WordTrace]
  refine ⟨61750679462365491683726683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82334239283153988911635577 61750679462365491683726683)
  ·
    refine ⟨92626019193548237525590025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61750679462365491683726683 92626019193548237525590025)
    ·
      refine ⟨69469514395161178144192519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92626019193548237525590025 69469514395161178144192519)
      ·
        refine ⟨104204271592741767216288779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69469514395161178144192519 104204271592741767216288779)
        ·
          refine ⟨156306407389112650824433169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104204271592741767216288779 156306407389112650824433169)
          ·
            refine ⟨117229805541834488118324877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156306407389112650824433169 117229805541834488118324877)
            ·
              refine ⟨43961177078187933044371829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117229805541834488118324877 43961177078187933044371829)
              ·
                refine ⟨4121360351080118722909859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43961177078187933044371829 4121360351080118722909859)
                ·
                  refine ⟨6182040526620178084364789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4121360351080118722909859 6182040526620178084364789)
                  ·
                    refine ⟨579566299370641695409199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6182040526620178084364789 579566299370641695409199)
                    ·
                      rfl

theorem cell23_3386104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 5, 1, 5].length) (baseStart_3386104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3386104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3386104 prefixEnd_3386104 := by exact prefixLift 3386104
  have htrace : WordTrace (prefixWord ++ tailWord_3386104) baseStart_3386104 baseEnd_3386104 := by
    simpa [prefixWord, tailWord_3386104, baseEnd_3386104] using wordTrace_append hprefix tailTrace_3386104
  have hstable : (prefixWord ++ tailWord_3386104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3386104).length < 2 ^ (prefixWord ++ tailWord_3386104).sum := by decide
  have hdescent : baseEnd_3386104 < baseStart_3386104 := by decide
  rcases family_descends (prefixWord ++ tailWord_3386104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3386107 : List Nat := [1, 1, 1, 1, 1, 3, 1, 2, 1, 7, 4]
def baseStart_3386107 : Nat := 118140960795 + 3386107 * 2 ^ 59
def prefixEnd_3386107 : Nat := 4983230072969 + 3 ^ 40 * 3386107 * 2
def baseEnd_3386107 : Nat := 1738700438553888574490083

theorem tailTrace_3386107 : CollatzResearch.WordTrace tailWord_3386107 prefixEnd_3386107 1738700438553888574490083 := by
  unfold tailWord_3386107
  simp only [CollatzResearch.WordTrace]
  refine ⟨123501468343720114879812575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82334312229146743253208383 123501468343720114879812575)
  ·
    refine ⟨185252202515580172319718863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123501468343720114879812575 185252202515580172319718863)
    ·
      refine ⟨277878303773370258479578295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185252202515580172319718863 277878303773370258479578295)
      ·
        refine ⟨416817455660055387719367443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277878303773370258479578295 416817455660055387719367443)
        ·
          refine ⟨625226183490083081579051165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 416817455660055387719367443 625226183490083081579051165)
          ·
            refine ⟨234459818808781155592144187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 625226183490083081579051165 234459818808781155592144187)
            ·
              refine ⟨351689728213171733388216281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 234459818808781155592144187 351689728213171733388216281)
              ·
                refine ⟨263767296159878800041162211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 351689728213171733388216281 263767296159878800041162211)
                ·
                  refine ⟨395650944239818200061743317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 263767296159878800041162211 395650944239818200061743317)
                  ·
                    refine ⟨9273069005620739063947109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 395650944239818200061743317 9273069005620739063947109)
                    ·
                      refine ⟨1738700438553888574490083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9273069005620739063947109 1738700438553888574490083)
                      ·
                        rfl

theorem cell23_3386107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 7, 4].length) (baseStart_3386107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3386107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3386107 prefixEnd_3386107 := by exact prefixLift 3386107
  have htrace : WordTrace (prefixWord ++ tailWord_3386107) baseStart_3386107 baseEnd_3386107 := by
    simpa [prefixWord, tailWord_3386107, baseEnd_3386107] using wordTrace_append hprefix tailTrace_3386107
  have hstable : (prefixWord ++ tailWord_3386107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3386107).length < 2 ^ (prefixWord ++ tailWord_3386107).sum := by decide
  have hdescent : baseEnd_3386107 < baseStart_3386107 := by decide
  rcases family_descends (prefixWord ++ tailWord_3386107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3386124 : List Nat := [2, 2, 1, 2, 2, 1, 1, 4, 3, 1, 4]
def baseStart_3386124 : Nat := 118140960795 + 3386124 * 2 ^ 59
def prefixEnd_3386124 : Nat := 4983230072969 + 3 ^ 40 * 3386124 * 2
def baseEnd_3386124 : Nat := 1738709167725015007977505

theorem tailTrace_3386124 : CollatzResearch.WordTrace tailWord_3386124 prefixEnd_3386124 1738709167725015007977505 := by
  unfold tailWord_3386124
  simp only [CollatzResearch.WordTrace]
  refine ⟨61751044192329263391590713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82334725589772351188787617 61751044192329263391590713)
  ·
    refine ⟨46313283144246947543693035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61751044192329263391590713 46313283144246947543693035)
    ·
      refine ⟨69469924716370421315539553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46313283144246947543693035 69469924716370421315539553)
      ·
        refine ⟨52102443537277815986654665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69469924716370421315539553 52102443537277815986654665)
        ·
          refine ⟨39076832652958361989990999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52102443537277815986654665 39076832652958361989990999)
          ·
            refine ⟨58615248979437542984986499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39076832652958361989990999 58615248979437542984986499)
            ·
              refine ⟨87922873469156314477479749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58615248979437542984986499 87922873469156314477479749)
              ·
                refine ⟨16485538775466808964527453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87922873469156314477479749 16485538775466808964527453)
                ·
                  refine ⟨6182077040800053361697795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16485538775466808964527453 6182077040800053361697795)
                  ·
                    refine ⟨9273115561200080042546693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6182077040800053361697795 9273115561200080042546693)
                    ·
                      refine ⟨1738709167725015007977505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9273115561200080042546693 1738709167725015007977505)
                      ·
                        rfl

theorem cell23_3386124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 4, 3, 1, 4].length) (baseStart_3386124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3386124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3386124 prefixEnd_3386124 := by exact prefixLift 3386124
  have htrace : WordTrace (prefixWord ++ tailWord_3386124) baseStart_3386124 baseEnd_3386124 := by
    simpa [prefixWord, tailWord_3386124, baseEnd_3386124] using wordTrace_append hprefix tailTrace_3386124
  have hstable : (prefixWord ++ tailWord_3386124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3386124).length < 2 ^ (prefixWord ++ tailWord_3386124).sum := by decide
  have hdescent : baseEnd_3386124 < baseStart_3386124 := by decide
  rcases family_descends (prefixWord ++ tailWord_3386124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3386164 : List Nat := [2, 5, 1, 1, 14]
def baseStart_3386164 : Nat := 118140960795 + 3386164 * 2 ^ 59
def prefixEnd_3386164 : Nat := 4983230072969 + 3 ^ 40 * 3386164 * 2
def baseEnd_3386164 : Nat := 2385088761249924350449

theorem tailTrace_3386164 : CollatzResearch.WordTrace tailWord_3386164 prefixEnd_3386164 2385088761249924350449 := by
  unfold tailWord_3386164
  simp only [CollatzResearch.WordTrace]
  refine ⟨61751773652256806807318773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82335698203009075743091697 61751773652256806807318773)
  ·
    refine ⟨5789228779899075638186135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 61751773652256806807318773 5789228779899075638186135)
    ·
      refine ⟨8683843169848613457279203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5789228779899075638186135 8683843169848613457279203)
      ·
        refine ⟨13025764754772920185918805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8683843169848613457279203 13025764754772920185918805)
        ·
          refine ⟨2385088761249924350449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 13025764754772920185918805 2385088761249924350449)
          ·
            rfl

theorem cell23_3386164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 14].length) (baseStart_3386164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3386164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3386164 prefixEnd_3386164 := by exact prefixLift 3386164
  have htrace : WordTrace (prefixWord ++ tailWord_3386164) baseStart_3386164 baseEnd_3386164 := by
    simpa [prefixWord, tailWord_3386164, baseEnd_3386164] using wordTrace_append hprefix tailTrace_3386164
  have hstable : (prefixWord ++ tailWord_3386164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3386164).length < 2 ^ (prefixWord ++ tailWord_3386164).sum := by decide
  have hdescent : baseEnd_3386164 < baseStart_3386164 := by decide
  rcases family_descends (prefixWord ++ tailWord_3386164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3386194 : List Nat := [3, 2, 2, 1, 1, 2, 1, 2, 2, 7]
def baseStart_3386194 : Nat := 118140960795 + 3386194 * 2 ^ 59
def prefixEnd_3386194 : Nat := 4983230072969 + 3 ^ 40 * 3386194 * 2
def baseEnd_3386194 : Nat := 579581703790276578034061

theorem tailTrace_3386194 : CollatzResearch.WordTrace tailWord_3386194 prefixEnd_3386194 579581703790276578034061 := by
  unfold tailWord_3386194
  simp only [CollatzResearch.WordTrace]
  refine ⟨30876160373601232184557409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82336427662936619158819757 30876160373601232184557409)
  ·
    refine ⟨23157120280200924138418057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30876160373601232184557409 23157120280200924138418057)
    ·
      refine ⟨17367840210150693103813543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23157120280200924138418057 17367840210150693103813543)
      ·
        refine ⟨26051760315226039655720315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17367840210150693103813543 26051760315226039655720315)
        ·
          refine ⟨39077640472839059483580473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26051760315226039655720315 39077640472839059483580473)
          ·
            refine ⟨29308230354629294612685355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39077640472839059483580473 29308230354629294612685355)
            ·
              refine ⟨43962345531943941919028033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29308230354629294612685355 43962345531943941919028033)
              ·
                refine ⟨32971759148957956439271025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43962345531943941919028033 32971759148957956439271025)
                ·
                  refine ⟨24728819361718467329453269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32971759148957956439271025 24728819361718467329453269)
                  ·
                    refine ⟨579581703790276578034061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24728819361718467329453269 579581703790276578034061)
                    ·
                      rfl

theorem cell23_3386194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 2, 2, 7].length) (baseStart_3386194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3386194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3386194 prefixEnd_3386194 := by exact prefixLift 3386194
  have htrace : WordTrace (prefixWord ++ tailWord_3386194) baseStart_3386194 baseEnd_3386194 := by
    simpa [prefixWord, tailWord_3386194, baseEnd_3386194] using wordTrace_append hprefix tailTrace_3386194
  have hstable : (prefixWord ++ tailWord_3386194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3386194).length < 2 ^ (prefixWord ++ tailWord_3386194).sum := by decide
  have hdescent : baseEnd_3386194 < baseStart_3386194 := by decide
  rcases family_descends (prefixWord ++ tailWord_3386194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3386224 : List Nat := [2, 1, 1, 1, 4, 1, 3, 2, 2, 6]
def baseStart_3386224 : Nat := 118140960795 + 3386224 * 2 ^ 59
def prefixEnd_3386224 : Nat := 4983230072969 + 3 ^ 40 * 3386224 * 2
def baseEnd_3386224 : Nat := 579586838596821538909015

theorem tailTrace_3386224 : CollatzResearch.WordTrace tailWord_3386224 prefixEnd_3386224 579586838596821538909015 := by
  unfold tailWord_3386224
  simp only [CollatzResearch.WordTrace]
  refine ⟨61752867842148121930910863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82337157122864162574547817 61752867842148121930910863)
  ·
    refine ⟨92629301763222182896366295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61752867842148121930910863 92629301763222182896366295)
    ·
      refine ⟨138943952644833274344549443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92629301763222182896366295 138943952644833274344549443)
      ·
        refine ⟨208415928967249911516824165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138943952644833274344549443 208415928967249911516824165)
        ·
          refine ⟨39077986681359358409404531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 208415928967249911516824165 39077986681359358409404531)
          ·
            refine ⟨58616980022039037614106797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39077986681359358409404531 58616980022039037614106797)
            ·
              refine ⟨21981367508264639105290049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58616980022039037614106797 21981367508264639105290049)
              ·
                refine ⟨16486025631198479328967537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21981367508264639105290049 16486025631198479328967537)
                ·
                  refine ⟨12364519223398859496725653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16486025631198479328967537 12364519223398859496725653)
                  ·
                    refine ⟨579586838596821538909015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12364519223398859496725653 579586838596821538909015)
                    ·
                      rfl

theorem cell23_3386224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 2, 2, 6].length) (baseStart_3386224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3386224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3386224 prefixEnd_3386224 := by exact prefixLift 3386224
  have htrace : WordTrace (prefixWord ++ tailWord_3386224) baseStart_3386224 baseEnd_3386224 := by
    simpa [prefixWord, tailWord_3386224, baseEnd_3386224] using wordTrace_append hprefix tailTrace_3386224
  have hstable : (prefixWord ++ tailWord_3386224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3386224).length < 2 ^ (prefixWord ++ tailWord_3386224).sum := by decide
  have hdescent : baseEnd_3386224 < baseStart_3386224 := by decide
  rcases family_descends (prefixWord ++ tailWord_3386224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3386225 : List Nat := [1, 2, 2, 2, 1, 6, 1, 2, 2, 1, 3]
def baseStart_3386225 : Nat := 118140960795 + 3386225 * 2 ^ 59
def prefixEnd_3386225 : Nat := 4983230072969 + 3 ^ 40 * 3386225 * 2
def baseEnd_3386225 : Nat := 1738761029271119112814541

theorem tailTrace_3386225 : CollatzResearch.WordTrace tailWord_3386225 prefixEnd_3386225 1738761029271119112814541 := by
  unfold tailWord_3386225
  simp only [CollatzResearch.WordTrace]
  refine ⟨123505772157292621032608129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82337181438195080688405419 123505772157292621032608129)
  ·
    refine ⟨92629329117969465774456097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123505772157292621032608129 92629329117969465774456097)
    ·
      refine ⟨69471996838477099330842073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92629329117969465774456097 69471996838477099330842073)
      ·
        refine ⟨52103997628857824498131555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69471996838477099330842073 52103997628857824498131555)
        ·
          refine ⟨78155996443286736747197333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52103997628857824498131555 78155996443286736747197333)
          ·
            refine ⟨3663562333279065785024875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 78155996443286736747197333 3663562333279065785024875)
            ·
              refine ⟨5495343499918598677537313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3663562333279065785024875 5495343499918598677537313)
              ·
                refine ⟨4121507624938949008152985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5495343499918598677537313 4121507624938949008152985)
                ·
                  refine ⟨3091130718704211756114739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4121507624938949008152985 3091130718704211756114739)
                  ·
                    refine ⟨4636696078056317634172109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3091130718704211756114739 4636696078056317634172109)
                    ·
                      refine ⟨1738761029271119112814541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4636696078056317634172109 1738761029271119112814541)
                      ·
                        rfl

theorem cell23_3386225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 1, 2, 2, 1, 3].length) (baseStart_3386225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3386225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3386225 prefixEnd_3386225 := by exact prefixLift 3386225
  have htrace : WordTrace (prefixWord ++ tailWord_3386225) baseStart_3386225 baseEnd_3386225 := by
    simpa [prefixWord, tailWord_3386225, baseEnd_3386225] using wordTrace_append hprefix tailTrace_3386225
  have hstable : (prefixWord ++ tailWord_3386225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3386225).length < 2 ^ (prefixWord ++ tailWord_3386225).sum := by decide
  have hdescent : baseEnd_3386225 < baseStart_3386225 := by decide
  rcases family_descends (prefixWord ++ tailWord_3386225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3386231 : List Nat := [1, 1, 3, 1, 1, 2, 1, 4, 3, 4, 2]
def baseStart_3386231 : Nat := 118140960795 + 3386231 * 2 ^ 59
def prefixEnd_3386231 : Nat := 4983230072969 + 3 ^ 40 * 3386231 * 2
def baseEnd_3386231 : Nat := 1738764110155046089339513

theorem tailTrace_3386231 : CollatzResearch.WordTrace tailWord_3386231 prefixEnd_3386231 1738764110155046089339513 := by
  unfold tailWord_3386231
  simp only [CollatzResearch.WordTrace]
  refine ⟨123505990995270884057326547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82337327330180589371551031 123505990995270884057326547)
  ·
    refine ⟨185258986492906326085989821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123505990995270884057326547 185258986492906326085989821)
    ·
      refine ⟨69472119934839872282246183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185258986492906326085989821 69472119934839872282246183)
      ·
        refine ⟨104208179902259808423369275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69472119934839872282246183 104208179902259808423369275)
        ·
          refine ⟨156312269853389712635053913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104208179902259808423369275 156312269853389712635053913)
          ·
            refine ⟨117234202390042284476290435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156312269853389712635053913 117234202390042284476290435)
            ·
              refine ⟨175851303585063426714435653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117234202390042284476290435 175851303585063426714435653)
              ·
                refine ⟨32972119422199392508956685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 175851303585063426714435653 32972119422199392508956685)
                ·
                  refine ⟨12364544783324772190858757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32972119422199392508956685 12364544783324772190858757)
                  ·
                    refine ⟨2318352146873394785786017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12364544783324772190858757 2318352146873394785786017)
                    ·
                      refine ⟨1738764110155046089339513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2318352146873394785786017 1738764110155046089339513)
                      ·
                        rfl

theorem cell23_3386231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 4, 3, 4, 2].length) (baseStart_3386231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3386231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3386231 prefixEnd_3386231 := by exact prefixLift 3386231
  have htrace : WordTrace (prefixWord ++ tailWord_3386231) baseStart_3386231 baseEnd_3386231 := by
    simpa [prefixWord, tailWord_3386231, baseEnd_3386231] using wordTrace_append hprefix tailTrace_3386231
  have hstable : (prefixWord ++ tailWord_3386231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3386231).length < 2 ^ (prefixWord ++ tailWord_3386231).sum := by decide
  have hdescent : baseEnd_3386231 < baseStart_3386231 := by decide
  rcases family_descends (prefixWord ++ tailWord_3386231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3386234 : List Nat := [3, 1, 1, 1, 1, 1, 3, 2, 4, 1, 5]
def baseStart_3386234 : Nat := 118140960795 + 3386234 * 2 ^ 59
def prefixEnd_3386234 : Nat := 4983230072969 + 3 ^ 40 * 3386234 * 2
def baseEnd_3386234 : Nat := 1738765650597009577601999

theorem tailTrace_3386234 : CollatzResearch.WordTrace tailWord_3386234 prefixEnd_3386234 1738765650597009577601999 := by
  unfold tailWord_3386234
  simp only [CollatzResearch.WordTrace]
  refine ⟨30876525103565003892421439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82337400276173343713123837 30876525103565003892421439)
  ·
    refine ⟨46314787655347505838632159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30876525103565003892421439 46314787655347505838632159)
    ·
      refine ⟨69472181483021258757948239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46314787655347505838632159 69472181483021258757948239)
      ·
        refine ⟨104208272224531888136922359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69472181483021258757948239 104208272224531888136922359)
        ·
          refine ⟨156312408336797832205383539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104208272224531888136922359 156312408336797832205383539)
          ·
            refine ⟨234468612505196748308075309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156312408336797832205383539 234468612505196748308075309)
            ·
              refine ⟨87925729689448780615528241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 234468612505196748308075309 87925729689448780615528241)
              ·
                refine ⟨65944297267086585461646181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87925729689448780615528241 65944297267086585461646181)
                ·
                  refine ⟨12364555737578734774058659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65944297267086585461646181 12364555737578734774058659)
                  ·
                    refine ⟨18546833606368102161087989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12364555737578734774058659 18546833606368102161087989)
                    ·
                      refine ⟨1738765650597009577601999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18546833606368102161087989 1738765650597009577601999)
                      ·
                        rfl

theorem cell23_3386234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 4, 1, 5].length) (baseStart_3386234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3386234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3386234 prefixEnd_3386234 := by exact prefixLift 3386234
  have htrace : WordTrace (prefixWord ++ tailWord_3386234) baseStart_3386234 baseEnd_3386234 := by
    simpa [prefixWord, tailWord_3386234, baseEnd_3386234] using wordTrace_append hprefix tailTrace_3386234
  have hstable : (prefixWord ++ tailWord_3386234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3386234).length < 2 ^ (prefixWord ++ tailWord_3386234).sum := by decide
  have hdescent : baseEnd_3386234 < baseStart_3386234 := by decide
  rcases family_descends (prefixWord ++ tailWord_3386234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3386268 : List Nat := [2, 2, 3, 3, 2, 1, 1, 1, 2, 1, 5]
def baseStart_3386268 : Nat := 118140960795 + 3386268 * 2 ^ 59
def prefixEnd_3386268 : Nat := 4983230072969 + 3 ^ 40 * 3386268 * 2
def baseEnd_3386268 : Nat := 1738783108939262444576843

theorem tailTrace_3386268 : CollatzResearch.WordTrace tailWord_3386268 prefixEnd_3386268 1738783108939262444576843 := by
  unfold tailWord_3386268
  simp only [CollatzResearch.WordTrace]
  refine ⟨61753670248068419688211729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82338226997424559584282305 61753670248068419688211729)
  ·
    refine ⟨46315252686051314766158797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61753670248068419688211729 46315252686051314766158797)
    ·
      refine ⟨17368219757269243037309549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46315252686051314766158797 17368219757269243037309549)
      ·
        refine ⟨6513082408975966138991081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17368219757269243037309549 6513082408975966138991081)
        ·
          refine ⟨4884811806731974604243311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6513082408975966138991081 4884811806731974604243311)
          ·
            refine ⟨7327217710097961906364967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4884811806731974604243311 7327217710097961906364967)
            ·
              refine ⟨10990826565146942859547451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7327217710097961906364967 10990826565146942859547451)
              ·
                refine ⟨16486239847720414289321177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10990826565146942859547451 16486239847720414289321177)
                ·
                  refine ⟨12364679885790310716990883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16486239847720414289321177 12364679885790310716990883)
                  ·
                    refine ⟨18547019828685466075486325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12364679885790310716990883 18547019828685466075486325)
                    ·
                      refine ⟨1738783108939262444576843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18547019828685466075486325 1738783108939262444576843)
                      ·
                        rfl

theorem cell23_3386268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_3386268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3386268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3386268 prefixEnd_3386268 := by exact prefixLift 3386268
  have htrace : WordTrace (prefixWord ++ tailWord_3386268) baseStart_3386268 baseEnd_3386268 := by
    simpa [prefixWord, tailWord_3386268, baseEnd_3386268] using wordTrace_append hprefix tailTrace_3386268
  have hstable : (prefixWord ++ tailWord_3386268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3386268).length < 2 ^ (prefixWord ++ tailWord_3386268).sum := by decide
  have hdescent : baseEnd_3386268 < baseStart_3386268 := by decide
  rcases family_descends (prefixWord ++ tailWord_3386268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3386318 : List Nat := [4, 1, 1, 1, 2, 4, 2, 1, 2, 5]
def baseStart_3386318 : Nat := 118140960795 + 3386318 * 2 ^ 59
def prefixEnd_3386318 : Nat := 4983230072969 + 3 ^ 40 * 3386318 * 2
def baseEnd_3386318 : Nat := 579602927657329082983871

theorem tailTrace_3386318 : CollatzResearch.WordTrace tailWord_3386318 prefixEnd_3386318 579602927657329082983871 := by
  unfold tailWord_3386318
  simp only [CollatzResearch.WordTrace]
  refine ⟨15438645518244462239467951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82339442763970465277162405 15438645518244462239467951)
  ·
    refine ⟨23157968277366693359201927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15438645518244462239467951 23157968277366693359201927)
    ·
      refine ⟨34736952416050040038802891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23157968277366693359201927 34736952416050040038802891)
      ·
        refine ⟨52105428624075060058204337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34736952416050040038802891 52105428624075060058204337)
        ·
          refine ⟨39079071468056295043653253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52105428624075060058204337 39079071468056295043653253)
          ·
            refine ⟨7327325900260555320684985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39079071468056295043653253 7327325900260555320684985)
            ·
              refine ⟨5495494425195416490513739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7327325900260555320684985 5495494425195416490513739)
              ·
                refine ⟨8243241637793124735770609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5495494425195416490513739 8243241637793124735770609)
                ·
                  refine ⟨6182431228344843551827957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8243241637793124735770609 6182431228344843551827957)
                  ·
                    refine ⟨579602927657329082983871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6182431228344843551827957 579602927657329082983871)
                    ·
                      rfl

theorem cell23_3386318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 2, 1, 2, 5].length) (baseStart_3386318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3386318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3386318 prefixEnd_3386318 := by exact prefixLift 3386318
  have htrace : WordTrace (prefixWord ++ tailWord_3386318) baseStart_3386318 baseEnd_3386318 := by
    simpa [prefixWord, tailWord_3386318, baseEnd_3386318] using wordTrace_append hprefix tailTrace_3386318
  have hstable : (prefixWord ++ tailWord_3386318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3386318).length < 2 ^ (prefixWord ++ tailWord_3386318).sum := by decide
  have hdescent : baseEnd_3386318 < baseStart_3386318 := by decide
  rcases family_descends (prefixWord ++ tailWord_3386318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3386361 : List Nat := [1, 2, 1, 3, 1, 3, 1, 5, 6]
def baseStart_3386361 : Nat := 118140960795 + 3386361 * 2 ^ 59
def prefixEnd_3386361 : Nat := 4983230072969 + 3 ^ 40 * 3386361 * 2
def baseEnd_3386361 : Nat := 193203429182236731190435

theorem tailTrace_3386361 : CollatzResearch.WordTrace tailWord_3386361 prefixEnd_3386361 193203429182236731190435 := by
  unfold tailWord_3386361
  simp only [CollatzResearch.WordTrace]
  refine ⟨123510732484799916259558937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82340488323199944173039291 123510732484799916259558937)
  ·
    refine ⟨92633049363599937194669203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123510732484799916259558937 92633049363599937194669203)
    ·
      refine ⟨138949574045399905792003805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92633049363599937194669203 138949574045399905792003805)
      ·
        refine ⟨52106090267024964672001427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138949574045399905792003805 52106090267024964672001427)
        ·
          refine ⟨78159135400537447008002141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52106090267024964672001427 78159135400537447008002141)
          ·
            refine ⟨29309675775201542628000803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78159135400537447008002141 29309675775201542628000803)
            ·
              refine ⟨43964513662802313942001205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29309675775201542628000803 43964513662802313942001205)
              ·
                refine ⟨4121673155887716932062613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43964513662802313942001205 4121673155887716932062613)
                ·
                  refine ⟨193203429182236731190435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4121673155887716932062613 193203429182236731190435)
                  ·
                    rfl

theorem cell23_3386361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 5, 6].length) (baseStart_3386361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3386361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3386361 prefixEnd_3386361 := by exact prefixLift 3386361
  have htrace : WordTrace (prefixWord ++ tailWord_3386361) baseStart_3386361 baseEnd_3386361 := by
    simpa [prefixWord, tailWord_3386361, baseEnd_3386361] using wordTrace_append hprefix tailTrace_3386361
  have hstable : (prefixWord ++ tailWord_3386361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3386361).length < 2 ^ (prefixWord ++ tailWord_3386361).sum := by decide
  have hdescent : baseEnd_3386361 < baseStart_3386361 := by decide
  rcases family_descends (prefixWord ++ tailWord_3386361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3386382 : List Nat := [4, 1, 1, 2, 2, 3, 2, 3, 1, 4]
def baseStart_3386382 : Nat := 118140960795 + 3386382 * 2 ^ 59
def prefixEnd_3386382 : Nat := 4983230072969 + 3 ^ 40 * 3386382 * 2
def baseEnd_3386382 : Nat := 579613881911291666183773

theorem tailTrace_3386382 : CollatzResearch.WordTrace tailWord_3386382 prefixEnd_3386382 579613881911291666183773 := by
  unfold tailWord_3386382
  simp only [CollatzResearch.WordTrace]
  refine ⟨15438937302215479605759175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82340998945149224564048933 15438937302215479605759175)
  ·
    refine ⟨23158405953323219408638763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15438937302215479605759175 23158405953323219408638763)
    ·
      refine ⟨34737608929984829112958145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23158405953323219408638763 34737608929984829112958145)
      ·
        refine ⟨26053206697488621834718609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34737608929984829112958145 26053206697488621834718609)
        ·
          refine ⟨19539905023116466376038957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26053206697488621834718609 19539905023116466376038957)
          ·
            refine ⟨7327464383668674891014609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19539905023116466376038957 7327464383668674891014609)
            ·
              refine ⟨5495598287751506168260957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7327464383668674891014609 5495598287751506168260957)
              ·
                refine ⟨2060849357906814813097859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5495598287751506168260957 2060849357906814813097859)
                ·
                  refine ⟨3091274036860222219646789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2060849357906814813097859 3091274036860222219646789)
                  ·
                    refine ⟨579613881911291666183773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3091274036860222219646789 579613881911291666183773)
                    ·
                      rfl

theorem cell23_3386382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 2, 3, 1, 4].length) (baseStart_3386382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3386382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3386382 prefixEnd_3386382 := by exact prefixLift 3386382
  have htrace : WordTrace (prefixWord ++ tailWord_3386382) baseStart_3386382 baseEnd_3386382 := by
    simpa [prefixWord, tailWord_3386382, baseEnd_3386382] using wordTrace_append hprefix tailTrace_3386382
  have hstable : (prefixWord ++ tailWord_3386382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3386382).length < 2 ^ (prefixWord ++ tailWord_3386382).sum := by decide
  have hdescent : baseEnd_3386382 < baseStart_3386382 := by decide
  rcases family_descends (prefixWord ++ tailWord_3386382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3386405 : List Nat := [1, 3, 1, 2, 2, 2, 4, 1, 3, 1, 3]
def baseStart_3386405 : Nat := 118140960795 + 3386405 * 2 ^ 59
def prefixEnd_3386405 : Nat := 4983230072969 + 3 ^ 40 * 3386405 * 2
def baseEnd_3386405 : Nat := 1738853455788928408563713

theorem tailTrace_3386405 : CollatzResearch.WordTrace tailWord_3386405 prefixEnd_3386405 1738853455788928408563713 := by
  unfold tailWord_3386405
  simp only [CollatzResearch.WordTrace]
  refine ⟨123512337296640511774160669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82341558197760341182773779 123512337296640511774160669)
  ·
    refine ⟨46317126486240191915310251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123512337296640511774160669 46317126486240191915310251)
    ·
      refine ⟨69475689729360287872965377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46317126486240191915310251 69475689729360287872965377)
      ·
        refine ⟨52106767297020215904724033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69475689729360287872965377 52106767297020215904724033)
        ·
          refine ⟨39080075472765161928543025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52106767297020215904724033 39080075472765161928543025)
          ·
            refine ⟨29310056604573871446407269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39080075472765161928543025 29310056604573871446407269)
            ·
              refine ⟨5495635613357600896201363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29310056604573871446407269 5495635613357600896201363)
              ·
                refine ⟨8243453420036401344302045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5495635613357600896201363 8243453420036401344302045)
                ·
                  refine ⟨3091295032513650504113267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8243453420036401344302045 3091295032513650504113267)
                  ·
                    refine ⟨4636942548770475756169901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3091295032513650504113267 4636942548770475756169901)
                    ·
                      refine ⟨1738853455788928408563713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4636942548770475756169901 1738853455788928408563713)
                      ·
                        rfl

theorem cell23_3386405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 4, 1, 3, 1, 3].length) (baseStart_3386405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3386405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3386405 prefixEnd_3386405 := by exact prefixLift 3386405
  have htrace : WordTrace (prefixWord ++ tailWord_3386405) baseStart_3386405 baseEnd_3386405 := by
    simpa [prefixWord, tailWord_3386405, baseEnd_3386405] using wordTrace_append hprefix tailTrace_3386405
  have hstable : (prefixWord ++ tailWord_3386405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3386405).length < 2 ^ (prefixWord ++ tailWord_3386405).sum := by decide
  have hdescent : baseEnd_3386405 < baseStart_3386405 := by decide
  rcases family_descends (prefixWord ++ tailWord_3386405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3386422 : List Nat := [5, 1, 2, 1, 1, 2, 2, 2, 3, 1, 3]
def baseStart_3386422 : Nat := 118140960795 + 3386422 * 2 ^ 59
def prefixEnd_3386422 : Nat := 4983230072969 + 3 ^ 40 * 3386422 * 2
def baseEnd_3386422 : Nat := 1738862184960054842051135

theorem tailTrace_3386422 : CollatzResearch.WordTrace tailWord_3386422 prefixEnd_3386422 1738862184960054842051135 := by
  unfold tailWord_3386422
  simp only [CollatzResearch.WordTrace]
  refine ⟨7719559833598682729845595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 82341971558385949118353013 7719559833598682729845595)
  ·
    refine ⟨11579339750398024094768393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7719559833598682729845595 11579339750398024094768393)
    ·
      refine ⟨8684504812798518071076295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11579339750398024094768393 8684504812798518071076295)
      ·
        refine ⟨13026757219197777106614443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8684504812798518071076295 13026757219197777106614443)
        ·
          refine ⟨19540135828796665659921665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13026757219197777106614443 19540135828796665659921665)
          ·
            refine ⟨14655101871597499244941249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19540135828796665659921665 14655101871597499244941249)
            ·
              refine ⟨10991326403698124433705937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14655101871597499244941249 10991326403698124433705937)
              ·
                refine ⟨8243494802773593325279453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10991326403698124433705937 8243494802773593325279453)
                ·
                  refine ⟨3091310551040097496979795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8243494802773593325279453 3091310551040097496979795)
                  ·
                    refine ⟨4636965826560146245469693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3091310551040097496979795 4636965826560146245469693)
                    ·
                      refine ⟨1738862184960054842051135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4636965826560146245469693 1738862184960054842051135)
                      ·
                        rfl

theorem cell23_3386422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 2, 3, 1, 3].length) (baseStart_3386422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3386422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3386422 prefixEnd_3386422 := by exact prefixLift 3386422
  have htrace : WordTrace (prefixWord ++ tailWord_3386422) baseStart_3386422 baseEnd_3386422 := by
    simpa [prefixWord, tailWord_3386422, baseEnd_3386422] using wordTrace_append hprefix tailTrace_3386422
  have hstable : (prefixWord ++ tailWord_3386422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3386422).length < 2 ^ (prefixWord ++ tailWord_3386422).sum := by decide
  have hdescent : baseEnd_3386422 < baseStart_3386422 := by decide
  rcases family_descends (prefixWord ++ tailWord_3386422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3386425 : List Nat := [1, 2, 1, 5, 2, 2, 2, 2, 1, 5]
def baseStart_3386425 : Nat := 118140960795 + 3386425 * 2 ^ 59
def prefixEnd_3386425 : Nat := 4983230072969 + 3 ^ 40 * 3386425 * 2
def baseEnd_3386425 : Nat := 579621241800672776771207

theorem tailTrace_3386425 : CollatzResearch.WordTrace tailWord_3386425 prefixEnd_3386425 579621241800672776771207 := by
  unfold tailWord_3386425
  simp only [CollatzResearch.WordTrace]
  refine ⟨123513066756568055189888729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82342044504378703459925819 123513066756568055189888729)
  ·
    refine ⟨92634800067426041392416547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123513066756568055189888729 92634800067426041392416547)
    ·
      refine ⟨138952200101139062088624821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92634800067426041392416547 138952200101139062088624821)
      ·
        refine ⟨13026768759481787070808577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 138952200101139062088624821 13026768759481787070808577)
        ·
          refine ⟨9770076569611340303106433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13026768759481787070808577 9770076569611340303106433)
          ·
            refine ⟨7327557427208505227329825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9770076569611340303106433 7327557427208505227329825)
            ·
              refine ⟨5495668070406378920497369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7327557427208505227329825 5495668070406378920497369)
              ·
                refine ⟨4121751052804784190373027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5495668070406378920497369 4121751052804784190373027)
                ·
                  refine ⟨6182626579207176285559541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4121751052804784190373027 6182626579207176285559541)
                  ·
                    refine ⟨579621241800672776771207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6182626579207176285559541 579621241800672776771207)
                    ·
                      rfl

theorem cell23_3386425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 2, 2, 1, 5].length) (baseStart_3386425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3386425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3386425 prefixEnd_3386425 := by exact prefixLift 3386425
  have htrace : WordTrace (prefixWord ++ tailWord_3386425) baseStart_3386425 baseEnd_3386425 := by
    simpa [prefixWord, tailWord_3386425, baseEnd_3386425] using wordTrace_append hprefix tailTrace_3386425
  have hstable : (prefixWord ++ tailWord_3386425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3386425).length < 2 ^ (prefixWord ++ tailWord_3386425).sum := by decide
  have hdescent : baseEnd_3386425 < baseStart_3386425 := by decide
  rcases family_descends (prefixWord ++ tailWord_3386425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3386431 : List Nat := [1, 1, 2, 2, 3, 1, 1, 1, 5, 1, 5]
def baseStart_3386431 : Nat := 118140960795 + 3386431 * 2 ^ 59
def prefixEnd_3386431 : Nat := 4983230072969 + 3 ^ 40 * 3386431 * 2
def baseEnd_3386431 : Nat := 1738866806285945306838593

theorem tailTrace_3386431 : CollatzResearch.WordTrace tailWord_3386431 prefixEnd_3386431 1738866806285945306838593 := by
  unfold tailWord_3386431
  simp only [CollatzResearch.WordTrace]
  refine ⟨123513285594546318214607147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82342190396364212143071431 123513285594546318214607147)
  ·
    refine ⟨185269928391819477321910721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123513285594546318214607147 185269928391819477321910721)
    ·
      refine ⟨138952446293864607991433041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185269928391819477321910721 138952446293864607991433041)
      ·
        refine ⟨104214334720398455993574781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138952446293864607991433041 104214334720398455993574781)
        ·
          refine ⟨39080375520149420997590543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104214334720398455993574781 39080375520149420997590543)
          ·
            refine ⟨58620563280224131496385815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39080375520149420997590543 58620563280224131496385815)
            ·
              refine ⟨87930844920336197244578723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58620563280224131496385815 87930844920336197244578723)
              ·
                refine ⟨131896267380504295866868085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87930844920336197244578723 131896267380504295866868085)
                ·
                  refine ⟨12365275066922277737518883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 131896267380504295866868085 12365275066922277737518883)
                  ·
                    refine ⟨18547912600383416606278325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12365275066922277737518883 18547912600383416606278325)
                    ·
                      refine ⟨1738866806285945306838593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18547912600383416606278325 1738866806285945306838593)
                      ·
                        rfl

theorem cell23_3386431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 5, 1, 5].length) (baseStart_3386431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3386431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3386431 prefixEnd_3386431 := by exact prefixLift 3386431
  have htrace : WordTrace (prefixWord ++ tailWord_3386431) baseStart_3386431 baseEnd_3386431 := by
    simpa [prefixWord, tailWord_3386431, baseEnd_3386431] using wordTrace_append hprefix tailTrace_3386431
  have hstable : (prefixWord ++ tailWord_3386431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3386431).length < 2 ^ (prefixWord ++ tailWord_3386431).sum := by decide
  have hdescent : baseEnd_3386431 < baseStart_3386431 := by decide
  rcases family_descends (prefixWord ++ tailWord_3386431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3386439 : List Nat := [1, 1, 4, 1, 3, 4, 1, 3, 1, 1, 3]
def baseStart_3386439 : Nat := 118140960795 + 3386439 * 2 ^ 59
def prefixEnd_3386439 : Nat := 4983230072969 + 3 ^ 40 * 3386439 * 2
def baseEnd_3386439 : Nat := 1738870914131181275538557

theorem tailTrace_3386439 : CollatzResearch.WordTrace tailWord_3386439 prefixEnd_3386439 1738870914131181275538557 := by
  unfold tailWord_3386439
  simp only [CollatzResearch.WordTrace]
  refine ⟨123513577378517335580898371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82342384919011557053932247 123513577378517335580898371)
  ·
    refine ⟨185270366067776003371347557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123513577378517335580898371 185270366067776003371347557)
    ·
      refine ⟨34738193637708000632127667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 185270366067776003371347557 34738193637708000632127667)
      ·
        refine ⟨52107290456562000948191501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34738193637708000632127667 52107290456562000948191501)
        ·
          refine ⟨19540233921210750355571813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52107290456562000948191501 19540233921210750355571813)
          ·
            refine ⟨3663793860227015691669715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19540233921210750355571813 3663793860227015691669715)
            ·
              refine ⟨5495690790340523537504573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3663793860227015691669715 5495690790340523537504573)
              ·
                refine ⟨2060884046377696326564215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5495690790340523537504573 2060884046377696326564215)
                ·
                  refine ⟨3091326069566544489846323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2060884046377696326564215 3091326069566544489846323)
                  ·
                    refine ⟨4636989104349816734769485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3091326069566544489846323 4636989104349816734769485)
                    ·
                      refine ⟨1738870914131181275538557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4636989104349816734769485 1738870914131181275538557)
                      ·
                        rfl

theorem cell23_3386439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 1, 3, 1, 1, 3].length) (baseStart_3386439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3386439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3386439 prefixEnd_3386439 := by exact prefixLift 3386439
  have htrace : WordTrace (prefixWord ++ tailWord_3386439) baseStart_3386439 baseEnd_3386439 := by
    simpa [prefixWord, tailWord_3386439, baseEnd_3386439] using wordTrace_append hprefix tailTrace_3386439
  have hstable : (prefixWord ++ tailWord_3386439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3386439).length < 2 ^ (prefixWord ++ tailWord_3386439).sum := by decide
  have hdescent : baseEnd_3386439 < baseStart_3386439 := by decide
  rcases family_descends (prefixWord ++ tailWord_3386439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3386481 : List Nat := [1, 2, 2, 2, 1, 1, 2, 1, 4, 7]
def baseStart_3386481 : Nat := 118140960795 + 3386481 * 2 ^ 59
def prefixEnd_3386481 : Nat := 4983230072969 + 3 ^ 40 * 3386481 * 2
def baseEnd_3386481 : Nat := 579630826772890037071121

theorem tailTrace_3386481 : CollatzResearch.WordTrace tailWord_3386481 prefixEnd_3386481 579630826772890037071121 := by
  unfold tailWord_3386481
  simp only [CollatzResearch.WordTrace]
  refine ⟨123515109244365176753927297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82343406162910117835951531 123515109244365176753927297)
  ·
    refine ⟨92636331933273882565445473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123515109244365176753927297 92636331933273882565445473)
    ·
      refine ⟨69477248949955411924084105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92636331933273882565445473 69477248949955411924084105)
      ·
        refine ⟨52107936712466558943063079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69477248949955411924084105 52107936712466558943063079)
        ·
          refine ⟨78161905068699838414594619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52107936712466558943063079 78161905068699838414594619)
          ·
            refine ⟨117242857603049757621891929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78161905068699838414594619 117242857603049757621891929)
            ·
              refine ⟨87932143202287318216418947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117242857603049757621891929 87932143202287318216418947)
              ·
                refine ⟨131898214803430977324628421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87932143202287318216418947 131898214803430977324628421)
                ·
                  refine ⟨24730915275643308248367829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 131898214803430977324628421 24730915275643308248367829)
                  ·
                    refine ⟨579630826772890037071121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24730915275643308248367829 579630826772890037071121)
                    ·
                      rfl

theorem cell23_3386481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 4, 7].length) (baseStart_3386481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3386481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3386481 prefixEnd_3386481 := by exact prefixLift 3386481
  have htrace : WordTrace (prefixWord ++ tailWord_3386481) baseStart_3386481 baseEnd_3386481 := by
    simpa [prefixWord, tailWord_3386481, baseEnd_3386481] using wordTrace_append hprefix tailTrace_3386481
  have hstable : (prefixWord ++ tailWord_3386481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3386481).length < 2 ^ (prefixWord ++ tailWord_3386481).sum := by decide
  have hdescent : baseEnd_3386481 < baseStart_3386481 := by decide
  rcases family_descends (prefixWord ++ tailWord_3386481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3386491 : List Nat := [1, 1, 1, 1, 1, 4, 1, 3, 1, 4, 5]
def baseStart_3386491 : Nat := 118140960795 + 3386491 * 2 ^ 59
def prefixEnd_3386491 : Nat := 4983230072969 + 3 ^ 40 * 3386491 * 2
def baseEnd_3386491 : Nat := 1738897615125215072088317

theorem tailTrace_3386491 : CollatzResearch.WordTrace tailWord_3386491 prefixEnd_3386491 1738897615125215072088317 := by
  unfold tailWord_3386491
  simp only [CollatzResearch.WordTrace]
  refine ⟨123515473974328948461791327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82343649316219298974527551 123515473974328948461791327)
  ·
    refine ⟨185273210961493422692686991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123515473974328948461791327 185273210961493422692686991)
    ·
      refine ⟨277909816442240134039030487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185273210961493422692686991 277909816442240134039030487)
      ·
        refine ⟨416864724663360201058545731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277909816442240134039030487 416864724663360201058545731)
        ·
          refine ⟨625297086995040301587818597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 416864724663360201058545731 625297086995040301587818597)
          ·
            refine ⟨117243203811570056547715987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 625297086995040301587818597 117243203811570056547715987)
            ·
              refine ⟨175864805717355084821573981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117243203811570056547715987 175864805717355084821573981)
              ·
                refine ⟨65949302144008156808090243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 175864805717355084821573981 65949302144008156808090243)
                ·
                  refine ⟨98923953216012235212135365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65949302144008156808090243 98923953216012235212135365)
                  ·
                    refine ⟨18548241228002294102275381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 98923953216012235212135365 18548241228002294102275381)
                    ·
                      refine ⟨1738897615125215072088317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18548241228002294102275381 1738897615125215072088317)
                      ·
                        rfl

theorem cell23_3386491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 4, 5].length) (baseStart_3386491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3386491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3386491 prefixEnd_3386491 := by exact prefixLift 3386491
  have htrace : WordTrace (prefixWord ++ tailWord_3386491) baseStart_3386491 baseEnd_3386491 := by
    simpa [prefixWord, tailWord_3386491, baseEnd_3386491] using wordTrace_append hprefix tailTrace_3386491
  have hstable : (prefixWord ++ tailWord_3386491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3386491).length < 2 ^ (prefixWord ++ tailWord_3386491).sum := by decide
  have hdescent : baseEnd_3386491 < baseStart_3386491 := by decide
  rcases family_descends (prefixWord ++ tailWord_3386491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3386522 : List Nat := [3, 1, 1, 5, 1, 1, 1, 2, 3, 3, 2]
def baseStart_3386522 : Nat := 118140960795 + 3386522 * 2 ^ 59
def prefixEnd_3386522 : Nat := 4983230072969 + 3 ^ 40 * 3386522 * 2
def baseEnd_3386522 : Nat := 1738913533025504450800675

theorem tailTrace_3386522 : CollatzResearch.WordTrace tailWord_3386522 prefixEnd_3386522 1738913533025504450800675 := by
  unfold tailWord_3386522
  simp only [CollatzResearch.WordTrace]
  refine ⟨30879151159304160189042455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82344403091477760504113213 30879151159304160189042455)
  ·
    refine ⟨46318726738956240283563683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30879151159304160189042455 46318726738956240283563683)
    ·
      refine ⟨69478090108434360425345525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46318726738956240283563683 69478090108434360425345525)
      ·
        refine ⟨6513570947665721289876143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 69478090108434360425345525 6513570947665721289876143)
        ·
          refine ⟨9770356421498581934814215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6513570947665721289876143 9770356421498581934814215)
          ·
            refine ⟨14655534632247872902221323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9770356421498581934814215 14655534632247872902221323)
            ·
              refine ⟨21983301948371809353331985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14655534632247872902221323 21983301948371809353331985)
              ·
                refine ⟨16487476461278857014998989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21983301948371809353331985 16487476461278857014998989)
                ·
                  refine ⟨6182803672979571380624621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16487476461278857014998989 6182803672979571380624621)
                  ·
                    refine ⟨2318551377367339267734233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6182803672979571380624621 2318551377367339267734233)
                    ·
                      refine ⟨1738913533025504450800675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2318551377367339267734233 1738913533025504450800675)
                      ·
                        rfl

theorem cell23_3386522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 2, 3, 3, 2].length) (baseStart_3386522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3386522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3386522 prefixEnd_3386522 := by exact prefixLift 3386522
  have htrace : WordTrace (prefixWord ++ tailWord_3386522) baseStart_3386522 baseEnd_3386522 := by
    simpa [prefixWord, tailWord_3386522, baseEnd_3386522] using wordTrace_append hprefix tailTrace_3386522
  have hstable : (prefixWord ++ tailWord_3386522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3386522).length < 2 ^ (prefixWord ++ tailWord_3386522).sum := by decide
  have hdescent : baseEnd_3386522 < baseStart_3386522 := by decide
  rcases family_descends (prefixWord ++ tailWord_3386522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3386528 : List Nat := [2, 1, 1, 4, 2, 1, 3, 1, 2, 6]
def baseStart_3386528 : Nat := 118140960795 + 3386528 * 2 ^ 59
def prefixEnd_3386528 : Nat := 4983230072969 + 3 ^ 40 * 3386528 * 2
def baseEnd_3386528 : Nat := 579638871303143809108549

theorem tailTrace_3386528 : CollatzResearch.WordTrace tailWord_3386528 prefixEnd_3386528 579638871303143809108549 := by
  unfold tailWord_3386528
  simp only [CollatzResearch.WordTrace]
  refine ⟨61758411737597451890444119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82344548983463269187258825 61758411737597451890444119)
  ·
    refine ⟨92637617606396177835666179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61758411737597451890444119 92637617606396177835666179)
    ·
      refine ⟨138956426409594266753499269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92637617606396177835666179 138956426409594266753499269)
      ·
        refine ⟨26054329951798925016281113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 138956426409594266753499269 26054329951798925016281113)
        ·
          refine ⟨19540747463849193762210835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26054329951798925016281113 19540747463849193762210835)
          ·
            refine ⟨29311121195773790643316253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19540747463849193762210835 29311121195773790643316253)
            ·
              refine ⟨10991670448415171491243595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29311121195773790643316253 10991670448415171491243595)
              ·
                refine ⟨16487505672622757236865393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10991670448415171491243595 16487505672622757236865393)
                ·
                  refine ⟨12365629254467067927649045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16487505672622757236865393 12365629254467067927649045)
                  ·
                    refine ⟨579638871303143809108549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12365629254467067927649045 579638871303143809108549)
                    ·
                      rfl

theorem cell23_3386528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 1, 2, 6].length) (baseStart_3386528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3386528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3386528 prefixEnd_3386528 := by exact prefixLift 3386528
  have htrace : WordTrace (prefixWord ++ tailWord_3386528) baseStart_3386528 baseEnd_3386528 := by
    simpa [prefixWord, tailWord_3386528, baseEnd_3386528] using wordTrace_append hprefix tailTrace_3386528
  have hstable : (prefixWord ++ tailWord_3386528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3386528).length < 2 ^ (prefixWord ++ tailWord_3386528).sum := by decide
  have hdescent : baseEnd_3386528 < baseStart_3386528 := by decide
  rcases family_descends (prefixWord ++ tailWord_3386528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3386550 : List Nat := [5, 1, 3, 2, 2, 1, 2, 1, 1, 2, 3]
def baseStart_3386550 : Nat := 118140960795 + 3386550 * 2 ^ 59
def prefixEnd_3386550 : Nat := 4983230072969 + 3 ^ 40 * 3386550 * 2
def baseEnd_3386550 : Nat := 1738927910483830341250547

theorem tailTrace_3386550 : CollatzResearch.WordTrace tailWord_3386550 prefixEnd_3386550 1738927910483830341250547 := by
  unfold tailWord_3386550
  simp only [CollatzResearch.WordTrace]
  refine ⟨7719851617569700096136819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 82345083920743467692126069 7719851617569700096136819)
  ·
    refine ⟨11579777426354550144205229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7719851617569700096136819 11579777426354550144205229)
    ·
      refine ⟨4342416534882956304076961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11579777426354550144205229 4342416534882956304076961)
      ·
        refine ⟨3256812401162217228057721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4342416534882956304076961 3256812401162217228057721)
        ·
          refine ⟨2442609300871662921043291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3256812401162217228057721 2442609300871662921043291)
          ·
            refine ⟨3663913951307494381564937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2442609300871662921043291 3663913951307494381564937)
            ·
              refine ⟨2747935463480620786173703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3663913951307494381564937 2747935463480620786173703)
              ·
                refine ⟨4121903195220931179260555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2747935463480620786173703 4121903195220931179260555)
                ·
                  refine ⟨6182854792831396768890833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4121903195220931179260555 6182854792831396768890833)
                  ·
                    refine ⟨4637141094623547576668125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6182854792831396768890833 4637141094623547576668125)
                    ·
                      refine ⟨1738927910483830341250547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4637141094623547576668125 1738927910483830341250547)
                      ·
                        rfl

theorem cell23_3386550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_3386550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3386550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3386550 prefixEnd_3386550 := by exact prefixLift 3386550
  have htrace : WordTrace (prefixWord ++ tailWord_3386550) baseStart_3386550 baseEnd_3386550 := by
    simpa [prefixWord, tailWord_3386550, baseEnd_3386550] using wordTrace_append hprefix tailTrace_3386550
  have hstable : (prefixWord ++ tailWord_3386550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3386550).length < 2 ^ (prefixWord ++ tailWord_3386550).sum := by decide
  have hdescent : baseEnd_3386550 < baseStart_3386550 := by decide
  rcases family_descends (prefixWord ++ tailWord_3386550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3386556 : List Nat := [2, 2, 2, 3, 2, 3, 2, 1, 1, 3, 2]
def baseStart_3386556 : Nat := 118140960795 + 3386556 * 2 ^ 59
def prefixEnd_3386556 : Nat := 4983230072969 + 3 ^ 40 * 3386556 * 2
def baseEnd_3386556 : Nat := 1738930991367757317775519

theorem tailTrace_3386556 : CollatzResearch.WordTrace tailWord_3386556 prefixEnd_3386556 1738930991367757317775519 := by
  unfold tailWord_3386556
  simp only [CollatzResearch.WordTrace]
  refine ⟨61758922359546732281453761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82345229812728976375271681 61758922359546732281453761)
  ·
    refine ⟨46319191769660049211090321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61758922359546732281453761 46319191769660049211090321)
    ·
      refine ⟨34739393827245036908317741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46319191769660049211090321 34739393827245036908317741)
      ·
        refine ⟨13027272685216888840619153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34739393827245036908317741 13027272685216888840619153)
        ·
          refine ⟨9770454513912666630464365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13027272685216888840619153 9770454513912666630464365)
          ·
            refine ⟨3663920442717249986424137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9770454513912666630464365 3663920442717249986424137)
            ·
              refine ⟨2747940332037937489818103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3663920442717249986424137 2747940332037937489818103)
              ·
                refine ⟨4121910498056906234727155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2747940332037937489818103 4121910498056906234727155)
                ·
                  refine ⟨6182865747085359352090733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4121910498056906234727155 6182865747085359352090733)
                  ·
                    refine ⟨2318574655157009757034025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6182865747085359352090733 2318574655157009757034025)
                    ·
                      refine ⟨1738930991367757317775519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2318574655157009757034025 1738930991367757317775519)
                      ·
                        rfl

theorem cell23_3386556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 2, 1, 1, 3, 2].length) (baseStart_3386556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3386556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3386556 prefixEnd_3386556 := by exact prefixLift 3386556
  have htrace : WordTrace (prefixWord ++ tailWord_3386556) baseStart_3386556 baseEnd_3386556 := by
    simpa [prefixWord, tailWord_3386556, baseEnd_3386556] using wordTrace_append hprefix tailTrace_3386556
  have hstable : (prefixWord ++ tailWord_3386556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3386556).length < 2 ^ (prefixWord ++ tailWord_3386556).sum := by decide
  have hdescent : baseEnd_3386556 < baseStart_3386556 := by decide
  rcases family_descends (prefixWord ++ tailWord_3386556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3386605 : List Nat := [1, 5, 1, 2, 2, 1, 2, 1, 1, 7]
def baseStart_3386605 : Nat := 118140960795 + 3386605 * 2 ^ 59
def prefixEnd_3386605 : Nat := 4983230072969 + 3 ^ 40 * 3386605 * 2
def baseEnd_3386605 : Nat := 579652050639942542020931

theorem tailTrace_3386605 : CollatzResearch.WordTrace tailWord_3386605 prefixEnd_3386605 579652050639942542020931 := by
  unfold tailWord_3386605
  simp only [CollatzResearch.WordTrace]
  refine ⟨123519631895915945931441269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82346421263943963954294179 123519631895915945931441269)
  ·
    refine ⟨11579965490242119931072619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 123519631895915945931441269 11579965490242119931072619)
    ·
      refine ⟨17369948235363179896608929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11579965490242119931072619 17369948235363179896608929)
      ·
        refine ⟨13027461176522384922456697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17369948235363179896608929 13027461176522384922456697)
        ·
          refine ⟨9770595882391788691842523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13027461176522384922456697 9770595882391788691842523)
          ·
            refine ⟨14655893823587683037763785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9770595882391788691842523 14655893823587683037763785)
            ·
              refine ⟨10991920367690762278322839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14655893823587683037763785 10991920367690762278322839)
              ·
                refine ⟨16487880551536143417484259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10991920367690762278322839 16487880551536143417484259)
                ·
                  refine ⟨24731820827304215126226389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16487880551536143417484259 24731820827304215126226389)
                  ·
                    refine ⟨579652050639942542020931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24731820827304215126226389 579652050639942542020931)
                    ·
                      rfl

theorem cell23_3386605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 1, 1, 7].length) (baseStart_3386605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3386605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3386605 prefixEnd_3386605 := by exact prefixLift 3386605
  have htrace : WordTrace (prefixWord ++ tailWord_3386605) baseStart_3386605 baseEnd_3386605 := by
    simpa [prefixWord, tailWord_3386605, baseEnd_3386605] using wordTrace_append hprefix tailTrace_3386605
  have hstable : (prefixWord ++ tailWord_3386605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3386605).length < 2 ^ (prefixWord ++ tailWord_3386605).sum := by decide
  have hdescent : baseEnd_3386605 < baseStart_3386605 := by decide
  rcases family_descends (prefixWord ++ tailWord_3386605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3386622 : List Nat := [4, 2, 2, 1, 1, 3, 1, 2, 2, 5]
def baseStart_3386622 : Nat := 118140960795 + 3386622 * 2 ^ 59
def prefixEnd_3386622 : Nat := 4983230072969 + 3 ^ 40 * 3386622 * 2
def baseEnd_3386622 : Nat := 579654960363651353183405

theorem tailTrace_3386622 : CollatzResearch.WordTrace tailWord_3386622 prefixEnd_3386622 579654960363651353183405 := by
  unfold tailWord_3386622
  simp only [CollatzResearch.WordTrace]
  refine ⟨15440031492106794729351265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82346834624569571889873413 15440031492106794729351265)
  ·
    refine ⟨11580023619080096047013449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15440031492106794729351265 11580023619080096047013449)
    ·
      refine ⟨8685017714310072035260087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11580023619080096047013449 8685017714310072035260087)
      ·
        refine ⟨13027526571465108052890131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8685017714310072035260087 13027526571465108052890131)
        ·
          refine ⟨19541289857197662079335197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13027526571465108052890131 19541289857197662079335197)
          ·
            refine ⟨7327983696449123279750699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19541289857197662079335197 7327983696449123279750699)
            ·
              refine ⟨10991975544673684919626049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7327983696449123279750699 10991975544673684919626049)
              ·
                refine ⟨8243981658505263689719537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10991975544673684919626049 8243981658505263689719537)
                ·
                  refine ⟨6182986243878947767289653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8243981658505263689719537 6182986243878947767289653)
                  ·
                    refine ⟨579654960363651353183405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6182986243878947767289653 579654960363651353183405)
                    ·
                      rfl

theorem cell23_3386622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 2, 2, 5].length) (baseStart_3386622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3386622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3386622 prefixEnd_3386622 := by exact prefixLift 3386622
  have htrace : WordTrace (prefixWord ++ tailWord_3386622) baseStart_3386622 baseEnd_3386622 := by
    simpa [prefixWord, tailWord_3386622, baseEnd_3386622] using wordTrace_append hprefix tailTrace_3386622
  have hstable : (prefixWord ++ tailWord_3386622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3386622).length < 2 ^ (prefixWord ++ tailWord_3386622).sum := by decide
  have hdescent : baseEnd_3386622 < baseStart_3386622 := by decide
  rcases family_descends (prefixWord ++ tailWord_3386622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3386625 : List Nat := [1, 2, 4, 1, 1, 3, 1, 1, 4, 1, 4]
def baseStart_3386625 : Nat := 118140960795 + 3386625 * 2 ^ 59
def prefixEnd_3386625 : Nat := 4983230072969 + 3 ^ 40 * 3386625 * 2
def baseEnd_3386625 : Nat := 1738966421532917547812701

theorem tailTrace_3386625 : CollatzResearch.WordTrace tailWord_3386625 prefixEnd_3386625 1738966421532917547812701 := by
  unfold tailWord_3386625
  simp only [CollatzResearch.WordTrace]
  refine ⟨123520361355843489347169329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82346907570562326231446219 123520361355843489347169329)
  ·
    refine ⟨92640271016882617010376997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123520361355843489347169329 92640271016882617010376997)
    ·
      refine ⟨17370050815665490689445687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92640271016882617010376997 17370050815665490689445687)
      ·
        refine ⟨26055076223498236034168531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17370050815665490689445687 26055076223498236034168531)
        ·
          refine ⟨39082614335247354051252797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26055076223498236034168531 39082614335247354051252797)
          ·
            refine ⟨14655980375717757769219799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39082614335247354051252797 14655980375717757769219799)
            ·
              refine ⟨21983970563576636653829699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14655980375717757769219799 21983970563576636653829699)
              ·
                refine ⟨32975955845364954980744549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21983970563576636653829699 32975955845364954980744549)
                ·
                  refine ⟨6182991721005929058889603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32975955845364954980744549 6182991721005929058889603)
                  ·
                    refine ⟨9274487581508893588334405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6182991721005929058889603 9274487581508893588334405)
                    ·
                      refine ⟨1738966421532917547812701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9274487581508893588334405 1738966421532917547812701)
                      ·
                        rfl

theorem cell23_3386625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 1, 4, 1, 4].length) (baseStart_3386625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3386625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3386625 prefixEnd_3386625 := by exact prefixLift 3386625
  have htrace : WordTrace (prefixWord ++ tailWord_3386625) baseStart_3386625 baseEnd_3386625 := by
    simpa [prefixWord, tailWord_3386625, baseEnd_3386625] using wordTrace_append hprefix tailTrace_3386625
  have hstable : (prefixWord ++ tailWord_3386625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3386625).length < 2 ^ (prefixWord ++ tailWord_3386625).sum := by decide
  have hdescent : baseEnd_3386625 < baseStart_3386625 := by decide
  rcases family_descends (prefixWord ++ tailWord_3386625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3386626 : List Nat := [3, 4, 1, 1, 3, 1, 3, 2, 5]
def baseStart_3386626 : Nat := 118140960795 + 3386626 * 2 ^ 59
def prefixEnd_3386626 : Nat := 4983230072969 + 3 ^ 40 * 3386626 * 2
def baseEnd_3386626 : Nat := 193218548334841338211133

theorem tailTrace_3386626 : CollatzResearch.WordTrace tailWord_3386626 prefixEnd_3386626 193218548334841338211133 := by
  unfold tailWord_3386626
  simp only [CollatzResearch.WordTrace]
  refine ⟨30880099457209966629488933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82346931885893244345303821 30880099457209966629488933)
  ·
    refine ⟨5790018648226868743029175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30880099457209966629488933 5790018648226868743029175)
    ·
      refine ⟨8685027972340303114543763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5790018648226868743029175 8685027972340303114543763)
      ·
        refine ⟨13027541958510454671815645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8685027972340303114543763 13027541958510454671815645)
        ·
          refine ⟨4885328234441420501930867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13027541958510454671815645 4885328234441420501930867)
          ·
            refine ⟨7327992351662130752896301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4885328234441420501930867 7327992351662130752896301)
            ·
              refine ⟨2747997131873299032336113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7327992351662130752896301 2747997131873299032336113)
              ·
                refine ⟨2060997848904974274252085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2747997131873299032336113 2060997848904974274252085)
                ·
                  refine ⟨193218548334841338211133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2060997848904974274252085 193218548334841338211133)
                  ·
                    rfl

theorem cell23_3386626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 3, 2, 5].length) (baseStart_3386626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3386626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3386626 prefixEnd_3386626 := by exact prefixLift 3386626
  have htrace : WordTrace (prefixWord ++ tailWord_3386626) baseStart_3386626 baseEnd_3386626 := by
    simpa [prefixWord, tailWord_3386626, baseEnd_3386626] using wordTrace_append hprefix tailTrace_3386626
  have hstable : (prefixWord ++ tailWord_3386626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3386626).length < 2 ^ (prefixWord ++ tailWord_3386626).sum := by decide
  have hdescent : baseEnd_3386626 < baseStart_3386626 := by decide
  rcases family_descends (prefixWord ++ tailWord_3386626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3386645 : List Nat := [1, 3, 2, 1, 2, 1, 1, 1, 6, 2, 3]
def baseStart_3386645 : Nat := 118140960795 + 3386645 * 2 ^ 59
def prefixEnd_3386645 : Nat := 4983230072969 + 3 ^ 40 * 3386645 * 2
def baseEnd_3386645 : Nat := 1738976691146007469562609

theorem tailTrace_3386645 : CollatzResearch.WordTrace tailWord_3386645 prefixEnd_3386645 1738976691146007469562609 := by
  unfold tailWord_3386645
  simp only [CollatzResearch.WordTrace]
  refine ⟨123521090815771032762897389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82347393877180688508598259 123521090815771032762897389)
  ·
    refine ⟨46320409055914137286086521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123521090815771032762897389 46320409055914137286086521)
    ·
      refine ⟨34740306791935602964564891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46320409055914137286086521 34740306791935602964564891)
      ·
        refine ⟨52110460187903404446847337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34740306791935602964564891 52110460187903404446847337)
        ·
          refine ⟨39082845140927553335135503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52110460187903404446847337 39082845140927553335135503)
          ·
            refine ⟨58624267711391330002703255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39082845140927553335135503 58624267711391330002703255)
            ·
              refine ⟨87936401567086995004054883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58624267711391330002703255 87936401567086995004054883)
              ·
                refine ⟨131904602350630492506082325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87936401567086995004054883 131904602350630492506082325)
                ·
                  refine ⟨6183028235185804336222609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 131904602350630492506082325 6183028235185804336222609)
                  ·
                    refine ⟨4637271176389353252166957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6183028235185804336222609 4637271176389353252166957)
                    ·
                      refine ⟨1738976691146007469562609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4637271176389353252166957 1738976691146007469562609)
                      ·
                        rfl

theorem cell23_3386645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 6, 2, 3].length) (baseStart_3386645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3386645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3386645 prefixEnd_3386645 := by exact prefixLift 3386645
  have htrace : WordTrace (prefixWord ++ tailWord_3386645) baseStart_3386645 baseEnd_3386645 := by
    simpa [prefixWord, tailWord_3386645, baseEnd_3386645] using wordTrace_append hprefix tailTrace_3386645
  have hstable : (prefixWord ++ tailWord_3386645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3386645).length < 2 ^ (prefixWord ++ tailWord_3386645).sum := by decide
  have hdescent : baseEnd_3386645 < baseStart_3386645 := by decide
  rcases family_descends (prefixWord ++ tailWord_3386645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3386668 : List Nat := [2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 8]
def baseStart_3386668 : Nat := 118140960795 + 3386668 * 2 ^ 59
def prefixEnd_3386668 : Nat := 4983230072969 + 3 ^ 40 * 3386668 * 2
def baseEnd_3386668 : Nat := 1738988501201060879575003

theorem tailTrace_3386668 : CollatzResearch.WordTrace tailWord_3386668 prefixEnd_3386668 1738988501201060879575003 := by
  unfold tailWord_3386668
  simp only [CollatzResearch.WordTrace]
  refine ⟨61760964847343853845492329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82347953129791805127323105 61760964847343853845492329)
  ·
    refine ⟨46320723635507890384119247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61760964847343853845492329 46320723635507890384119247)
    ·
      refine ⟨69481085453261835576178871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46320723635507890384119247 69481085453261835576178871)
      ·
        refine ⟨104221628179892753364268307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69481085453261835576178871 104221628179892753364268307)
        ·
          refine ⟨156332442269839130046402461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104221628179892753364268307 156332442269839130046402461)
          ·
            refine ⟨58624665851189673767400923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 156332442269839130046402461 58624665851189673767400923)
            ·
              refine ⟨87936998776784510651101385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58624665851189673767400923 87936998776784510651101385)
              ·
                refine ⟨65952749082588382988326039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87936998776784510651101385 65952749082588382988326039)
                ·
                  refine ⟨98929123623882574482489059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65952749082588382988326039 98929123623882574482489059)
                  ·
                    refine ⟨148393685435823861723733589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 98929123623882574482489059 148393685435823861723733589)
                    ·
                      refine ⟨1738988501201060879575003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 148393685435823861723733589 1738988501201060879575003)
                      ·
                        rfl

theorem cell23_3386668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 8].length) (baseStart_3386668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3386668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3386668 prefixEnd_3386668 := by exact prefixLift 3386668
  have htrace : WordTrace (prefixWord ++ tailWord_3386668) baseStart_3386668 baseEnd_3386668 := by
    simpa [prefixWord, tailWord_3386668, baseEnd_3386668] using wordTrace_append hprefix tailTrace_3386668
  have hstable : (prefixWord ++ tailWord_3386668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3386668).length < 2 ^ (prefixWord ++ tailWord_3386668).sum := by decide
  have hdescent : baseEnd_3386668 < baseStart_3386668 := by decide
  rcases family_descends (prefixWord ++ tailWord_3386668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3386695 : List Nat := [1, 1, 4, 1, 2, 3, 1, 2, 3, 5]
def baseStart_3386695 : Nat := 118140960795 + 3386695 * 2 ^ 59
def prefixEnd_3386695 : Nat := 4983230072969 + 3 ^ 40 * 3386695 * 2
def baseEnd_3386695 : Nat := 579667455059577424645793

theorem tailTrace_3386695 : CollatzResearch.WordTrace tailWord_3386695 prefixEnd_3386695 579667455059577424645793 := by
  unfold tailWord_3386695
  simp only [CollatzResearch.WordTrace]
  refine ⟨123522914465589891302217539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82348609643726594201478359 123522914465589891302217539)
  ·
    refine ⟨185284371698384836953326309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123522914465589891302217539 185284371698384836953326309)
    ·
      refine ⟨34740819693447156928748683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 185284371698384836953326309 34740819693447156928748683)
      ·
        refine ⟨52111229540170735393123025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34740819693447156928748683 52111229540170735393123025)
        ·
          refine ⟨39083422155128051544842269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52111229540170735393123025 39083422155128051544842269)
          ·
            refine ⟨14656283308173019329315851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39083422155128051544842269 14656283308173019329315851)
            ·
              refine ⟨21984424962259528993973777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14656283308173019329315851 21984424962259528993973777)
              ·
                refine ⟨16488318721694646745480333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21984424962259528993973777 16488318721694646745480333)
                ·
                  refine ⟨6183119520635492529555125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16488318721694646745480333 6183119520635492529555125)
                  ·
                    refine ⟨579667455059577424645793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6183119520635492529555125 579667455059577424645793)
                    ·
                      rfl

theorem cell23_3386695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 2, 3, 5].length) (baseStart_3386695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3386695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3386695 prefixEnd_3386695 := by exact prefixLift 3386695
  have htrace : WordTrace (prefixWord ++ tailWord_3386695) baseStart_3386695 baseEnd_3386695 := by
    simpa [prefixWord, tailWord_3386695, baseEnd_3386695] using wordTrace_append hprefix tailTrace_3386695
  have hstable : (prefixWord ++ tailWord_3386695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3386695).length < 2 ^ (prefixWord ++ tailWord_3386695).sum := by decide
  have hdescent : baseEnd_3386695 < baseStart_3386695 := by decide
  rcases family_descends (prefixWord ++ tailWord_3386695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3386702 : List Nat := [4, 1, 1, 1, 1, 1, 4, 2, 1, 5, 2]
def baseStart_3386702 : Nat := 118140960795 + 3386702 * 2 ^ 59
def prefixEnd_3386702 : Nat := 4983230072969 + 3 ^ 40 * 3386702 * 2
def baseEnd_3386702 : Nat := 1739005959543313746549847

theorem tailTrace_3386702 : CollatzResearch.WordTrace tailWord_3386702 prefixEnd_3386702 1739005959543313746549847 := by
  unfold tailWord_3386702
  simp only [CollatzResearch.WordTrace]
  refine ⟨15440396222070566437215295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82348779851043020998481573 15440396222070566437215295)
  ·
    refine ⟨23160594333105849655822943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15440396222070566437215295 23160594333105849655822943)
    ·
      refine ⟨34740891499658774483734415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23160594333105849655822943 34740891499658774483734415)
      ·
        refine ⟨52111337249488161725601623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34740891499658774483734415 52111337249488161725601623)
        ·
          refine ⟨78167005874232242588402435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52111337249488161725601623 78167005874232242588402435)
          ·
            refine ⟨117250508811348363882603653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78167005874232242588402435 117250508811348363882603653)
            ·
              refine ⟨21984470402127818227988185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 117250508811348363882603653 21984470402127818227988185)
              ·
                refine ⟨16488352801595863670991139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21984470402127818227988185 16488352801595863670991139)
                ·
                  refine ⟨24732529202393795506486709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16488352801595863670991139 24732529202393795506486709)
                  ·
                    refine ⟨2318674612724418328733129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24732529202393795506486709 2318674612724418328733129)
                    ·
                      refine ⟨1739005959543313746549847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2318674612724418328733129 1739005959543313746549847)
                      ·
                        rfl

theorem cell23_3386702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 2, 1, 5, 2].length) (baseStart_3386702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3386702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3386702 prefixEnd_3386702 := by exact prefixLift 3386702
  have htrace : WordTrace (prefixWord ++ tailWord_3386702) baseStart_3386702 baseEnd_3386702 := by
    simpa [prefixWord, tailWord_3386702, baseEnd_3386702] using wordTrace_append hprefix tailTrace_3386702
  have hstable : (prefixWord ++ tailWord_3386702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3386702).length < 2 ^ (prefixWord ++ tailWord_3386702).sum := by decide
  have hdescent : baseEnd_3386702 < baseStart_3386702 := by decide
  rcases family_descends (prefixWord ++ tailWord_3386702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3386709 : List Nat := [1, 3, 2, 2, 3, 2, 1, 2, 3, 1, 3]
def baseStart_3386709 : Nat := 118140960795 + 3386709 * 2 ^ 59
def prefixEnd_3386709 : Nat := 4983230072969 + 3 ^ 40 * 3386709 * 2
def baseEnd_3386709 : Nat := 1739009553907895219162315

theorem tailTrace_3386709 : CollatzResearch.WordTrace tailWord_3386709 prefixEnd_3386709 1739009553907895219162315 := by
  unfold tailWord_3386709
  simp only [CollatzResearch.WordTrace]
  refine ⟨123523425087539171693227181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82348950058359447795484787 123523425087539171693227181)
  ·
    refine ⟨46321284407827189384960193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123523425087539171693227181 46321284407827189384960193)
    ·
      refine ⟨34740963305870392038720145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46321284407827189384960193 34740963305870392038720145)
      ·
        refine ⟨26055722479402794029040109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34740963305870392038720145 26055722479402794029040109)
        ·
          refine ⟨9770895929776047760890041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26055722479402794029040109 9770895929776047760890041)
          ·
            refine ⟨7328171947332035820667531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9770895929776047760890041 7328171947332035820667531)
            ·
              refine ⟨10992257920998053731001297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7328171947332035820667531 10992257920998053731001297)
              ·
                refine ⟨8244193440748540298250973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10992257920998053731001297 8244193440748540298250973)
                ·
                  refine ⟨3091572540280702611844115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8244193440748540298250973 3091572540280702611844115)
                  ·
                    refine ⟨4637358810421053917766173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3091572540280702611844115 4637358810421053917766173)
                    ·
                      refine ⟨1739009553907895219162315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4637358810421053917766173 1739009553907895219162315)
                      ·
                        rfl

theorem cell23_3386709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 2, 3, 1, 3].length) (baseStart_3386709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3386709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3386709 prefixEnd_3386709 := by exact prefixLift 3386709
  have htrace : WordTrace (prefixWord ++ tailWord_3386709) baseStart_3386709 baseEnd_3386709 := by
    simpa [prefixWord, tailWord_3386709, baseEnd_3386709] using wordTrace_append hprefix tailTrace_3386709
  have hstable : (prefixWord ++ tailWord_3386709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3386709).length < 2 ^ (prefixWord ++ tailWord_3386709).sum := by decide
  have hdescent : baseEnd_3386709 < baseStart_3386709 := by decide
  rcases family_descends (prefixWord ++ tailWord_3386709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3386710 : List Nat := [5, 2, 3, 1, 1, 2, 1, 1, 2, 1, 4]
def baseStart_3386710 : Nat := 118140960795 + 3386710 * 2 ^ 59
def prefixEnd_3386710 : Nat := 4983230072969 + 3 ^ 40 * 3386710 * 2
def baseEnd_3386710 : Nat := 1739010067388549715249811

theorem tailTrace_3386710 : CollatzResearch.WordTrace tailWord_3386710 prefixEnd_3386710 1739010067388549715249811 := by
  unfold tailWord_3386710
  simp only [CollatzResearch.WordTrace]
  refine ⟨7720216347533471804000849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 82348974373690365909342389 7720216347533471804000849)
  ·
    refine ⟨5790162260650103853000637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7720216347533471804000849 5790162260650103853000637)
    ·
      refine ⟨2171310847743788944875239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5790162260650103853000637 2171310847743788944875239)
      ·
        refine ⟨3256966271615683417312859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2171310847743788944875239 3256966271615683417312859)
        ·
          refine ⟨4885449407423525125969289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3256966271615683417312859 4885449407423525125969289)
          ·
            refine ⟨3664087055567643844476967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4885449407423525125969289 3664087055567643844476967)
            ·
              refine ⟨5496130583351465766715451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3664087055567643844476967 5496130583351465766715451)
              ·
                refine ⟨8244195875027198650073177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5496130583351465766715451 8244195875027198650073177)
                ·
                  refine ⟨6183146906270398987554883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8244195875027198650073177 6183146906270398987554883)
                  ·
                    refine ⟨9274720359405598481332325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6183146906270398987554883 9274720359405598481332325)
                    ·
                      refine ⟨1739010067388549715249811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9274720359405598481332325 1739010067388549715249811)
                      ·
                        rfl

theorem cell23_3386710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_3386710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3386710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3386710 prefixEnd_3386710 := by exact prefixLift 3386710
  have htrace : WordTrace (prefixWord ++ tailWord_3386710) baseStart_3386710 baseEnd_3386710 := by
    simpa [prefixWord, tailWord_3386710, baseEnd_3386710] using wordTrace_append hprefix tailTrace_3386710
  have hstable : (prefixWord ++ tailWord_3386710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3386710).length < 2 ^ (prefixWord ++ tailWord_3386710).sum := by decide
  have hdescent : baseEnd_3386710 < baseStart_3386710 := by decide
  rcases family_descends (prefixWord ++ tailWord_3386710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3386725 : List Nat := [1, 3, 1, 3, 1, 2, 1, 4, 1, 6]
def baseStart_3386725 : Nat := 118140960795 + 3386725 * 2 ^ 59
def prefixEnd_3386725 : Nat := 4983230072969 + 3 ^ 40 * 3386725 * 2
def baseEnd_3386725 : Nat := 579672589866122385520747

theorem tailTrace_3386725 : CollatzResearch.WordTrace tailWord_3386725 prefixEnd_3386725 579672589866122385520747 := by
  unfold tailWord_3386725
  simp only [CollatzResearch.WordTrace]
  refine ⟨123524008655481206425809629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82349339103654137617206419 123524008655481206425809629)
  ·
    refine ⟨46321503245805452409678611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123524008655481206425809629 46321503245805452409678611)
    ·
      refine ⟨69482254868708178614517917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46321503245805452409678611 69482254868708178614517917)
      ·
        refine ⟨26055845575765566980444219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69482254868708178614517917 26055845575765566980444219)
        ·
          refine ⟨39083768363648350470666329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26055845575765566980444219 39083768363648350470666329)
          ·
            refine ⟨29312826272736262852999747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39083768363648350470666329 29312826272736262852999747)
            ·
              refine ⟨43969239409104394279499621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29312826272736262852999747 43969239409104394279499621)
              ·
                refine ⟨8244232389207073927406179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43969239409104394279499621 8244232389207073927406179)
                ·
                  refine ⟨12366348583810610891109269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8244232389207073927406179 12366348583810610891109269)
                  ·
                    refine ⟨579672589866122385520747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12366348583810610891109269 579672589866122385520747)
                    ·
                      rfl

theorem cell23_3386725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 4, 1, 6].length) (baseStart_3386725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3386725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3386725 prefixEnd_3386725 := by exact prefixLift 3386725
  have htrace : WordTrace (prefixWord ++ tailWord_3386725) baseStart_3386725 baseEnd_3386725 := by
    simpa [prefixWord, tailWord_3386725, baseEnd_3386725] using wordTrace_append hprefix tailTrace_3386725
  have hstable : (prefixWord ++ tailWord_3386725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3386725).length < 2 ^ (prefixWord ++ tailWord_3386725).sum := by decide
  have hdescent : baseEnd_3386725 < baseStart_3386725 := by decide
  rcases family_descends (prefixWord ++ tailWord_3386725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3386735 : List Nat := [1, 1, 2, 1, 3, 1, 4, 3, 1, 1, 5]
def baseStart_3386735 : Nat := 118140960795 + 3386735 * 2 ^ 59
def prefixEnd_3386735 : Nat := 4983230072969 + 3 ^ 40 * 3386735 * 2
def baseEnd_3386735 : Nat := 1739022904404912117437195

theorem tailTrace_3386735 : CollatzResearch.WordTrace tailWord_3386735 prefixEnd_3386735 1739022904404912117437195 := by
  unfold tailWord_3386735
  simp only [CollatzResearch.WordTrace]
  refine ⟨123524373385444978133673659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82349582256963318755782439 123524373385444978133673659)
  ·
    refine ⟨185286560078167467200510489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123524373385444978133673659 185286560078167467200510489)
    ·
      refine ⟨138964920058625600400382867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185286560078167467200510489 138964920058625600400382867)
      ·
        refine ⟨208447380087938400600574301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138964920058625600400382867 208447380087938400600574301)
        ·
          refine ⟨78167767532976900225215363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 208447380087938400600574301 78167767532976900225215363)
          ·
            refine ⟨117251651299465350337823045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78167767532976900225215363 117251651299465350337823045)
            ·
              refine ⟨21984684618649753188341821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 117251651299465350337823045 21984684618649753188341821)
              ·
                refine ⟨8244256731993657445628183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21984684618649753188341821 8244256731993657445628183)
                ·
                  refine ⟨12366385097990486168442275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8244256731993657445628183 12366385097990486168442275)
                  ·
                    refine ⟨18549577646985729252663413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12366385097990486168442275 18549577646985729252663413)
                    ·
                      refine ⟨1739022904404912117437195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18549577646985729252663413 1739022904404912117437195)
                      ·
                        rfl

theorem cell23_3386735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 3, 1, 1, 5].length) (baseStart_3386735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3386735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3386735 prefixEnd_3386735 := by exact prefixLift 3386735
  have htrace : WordTrace (prefixWord ++ tailWord_3386735) baseStart_3386735 baseEnd_3386735 := by
    simpa [prefixWord, tailWord_3386735, baseEnd_3386735] using wordTrace_append hprefix tailTrace_3386735
  have hstable : (prefixWord ++ tailWord_3386735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3386735).length < 2 ^ (prefixWord ++ tailWord_3386735).sum := by decide
  have hdescent : baseEnd_3386735 < baseStart_3386735 := by decide
  rcases family_descends (prefixWord ++ tailWord_3386735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3386745 : List Nat := [1, 2, 1, 3, 2, 1, 2, 2, 3, 2, 4]
def baseStart_3386745 : Nat := 118140960795 + 3386745 * 2 ^ 59
def prefixEnd_3386745 : Nat := 4983230072969 + 3 ^ 40 * 3386745 * 2
def baseEnd_3386745 : Nat := 1739028039211457078312149

theorem tailTrace_3386745 : CollatzResearch.WordTrace tailWord_3386745 prefixEnd_3386745 1739028039211457078312149 := by
  unfold tailWord_3386745
  simp only [CollatzResearch.WordTrace]
  refine ⟨123524738115408749841537689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82349825410272499894358459 123524738115408749841537689)
  ·
    refine ⟨92643553586556562381153267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123524738115408749841537689 92643553586556562381153267)
    ·
      refine ⟨138965330379834843571729901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92643553586556562381153267 138965330379834843571729901)
      ·
        refine ⟨52111998892438066339398713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138965330379834843571729901 52111998892438066339398713)
        ·
          refine ⟨39083999169328549754549035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52111998892438066339398713 39083999169328549754549035)
          ·
            refine ⟨58625998753992824631823553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39083999169328549754549035 58625998753992824631823553)
            ·
              refine ⟨43969499065494618473867665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58625998753992824631823553 43969499065494618473867665)
              ·
                refine ⟨32977124299120963855400749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43969499065494618473867665 32977124299120963855400749)
                ·
                  refine ⟨12366421612170361445775281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32977124299120963855400749 12366421612170361445775281)
                  ·
                    refine ⟨9274816209127771084331461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12366421612170361445775281 9274816209127771084331461)
                    ·
                      refine ⟨1739028039211457078312149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9274816209127771084331461 1739028039211457078312149)
                      ·
                        rfl

theorem cell23_3386745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 2, 3, 2, 4].length) (baseStart_3386745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3386745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3386745 prefixEnd_3386745 := by exact prefixLift 3386745
  have htrace : WordTrace (prefixWord ++ tailWord_3386745) baseStart_3386745 baseEnd_3386745 := by
    simpa [prefixWord, tailWord_3386745, baseEnd_3386745] using wordTrace_append hprefix tailTrace_3386745
  have hstable : (prefixWord ++ tailWord_3386745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3386745).length < 2 ^ (prefixWord ++ tailWord_3386745).sum := by decide
  have hdescent : baseEnd_3386745 < baseStart_3386745 := by decide
  rcases family_descends (prefixWord ++ tailWord_3386745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3386766 : List Nat := [4, 1, 1, 4, 2, 1, 2, 2, 1, 1, 4]
def baseStart_3386766 : Nat := 118140960795 + 3386766 * 2 ^ 59
def prefixEnd_3386766 : Nat := 4983230072969 + 3 ^ 40 * 3386766 * 2
def baseEnd_3386766 : Nat := 1739038822305201496149553

theorem tailTrace_3386766 : CollatzResearch.WordTrace tailWord_3386766 prefixEnd_3386766 1739038822305201496149553 := by
  unfold tailWord_3386766
  simp only [CollatzResearch.WordTrace]
  refine ⟨15440688006041583803506519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82350336032221780285368101 15440688006041583803506519)
  ·
    refine ⟨23161032009062375705259779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15440688006041583803506519 23161032009062375705259779)
    ·
      refine ⟨34741548013593563557889669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23161032009062375705259779 34741548013593563557889669)
      ·
        refine ⟨6514040252548793167104313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34741548013593563557889669 6514040252548793167104313)
        ·
          refine ⟨4885530189411594875328235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6514040252548793167104313 4885530189411594875328235)
          ·
            refine ⟨7328295284117392312992353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4885530189411594875328235 7328295284117392312992353)
            ·
              refine ⟨5496221463088044234744265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7328295284117392312992353 5496221463088044234744265)
              ·
                refine ⟨4122166097316033176058199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5496221463088044234744265 4122166097316033176058199)
                ·
                  refine ⟨6183249145974049764087299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4122166097316033176058199 6183249145974049764087299)
                  ·
                    refine ⟨9274873718961074646130949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6183249145974049764087299 9274873718961074646130949)
                    ·
                      refine ⟨1739038822305201496149553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9274873718961074646130949 1739038822305201496149553)
                      ·
                        rfl

theorem cell23_3386766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_3386766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3386766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3386766 prefixEnd_3386766 := by exact prefixLift 3386766
  have htrace : WordTrace (prefixWord ++ tailWord_3386766) baseStart_3386766 baseEnd_3386766 := by
    simpa [prefixWord, tailWord_3386766, baseEnd_3386766] using wordTrace_append hprefix tailTrace_3386766
  have hstable : (prefixWord ++ tailWord_3386766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3386766).length < 2 ^ (prefixWord ++ tailWord_3386766).sum := by decide
  have hdescent : baseEnd_3386766 < baseStart_3386766 := by decide
  rcases family_descends (prefixWord ++ tailWord_3386766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3386772 : List Nat := [2, 4, 2, 1, 2, 2, 1, 9]
def baseStart_3386772 : Nat := 118140960795 + 3386772 * 2 ^ 59
def prefixEnd_3386772 : Nat := 4983230072969 + 3 ^ 40 * 3386772 * 2
def baseEnd_3386772 : Nat := 64408959377375128617575

theorem tailTrace_3386772 : CollatzResearch.WordTrace tailWord_3386772 prefixEnd_3386772 64408959377375128617575 := by
  unfold tailWord_3386772
  simp only [CollatzResearch.WordTrace]
  refine ⟨61762861443155466726385285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82350481924207288968513713 61762861443155466726385285)
  ·
    refine ⟨11580536520591650011197241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61762861443155466726385285 11580536520591650011197241)
    ·
      refine ⟨8685402390443737508397931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11580536520591650011197241 8685402390443737508397931)
      ·
        refine ⟨13028103585665606262596897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8685402390443737508397931 13028103585665606262596897)
        ·
          refine ⟨9771077689249204696947673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13028103585665606262596897 9771077689249204696947673)
          ·
            refine ⟨7328308266936903522710755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9771077689249204696947673 7328308266936903522710755)
            ·
              refine ⟨10992462400405355284066133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7328308266936903522710755 10992462400405355284066133)
              ·
                refine ⟨64408959377375128617575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10992462400405355284066133 64408959377375128617575)
                ·
                  rfl

theorem cell23_3386772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 9].length) (baseStart_3386772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3386772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3386772 prefixEnd_3386772 := by exact prefixLift 3386772
  have htrace : WordTrace (prefixWord ++ tailWord_3386772) baseStart_3386772 baseEnd_3386772 := by
    simpa [prefixWord, tailWord_3386772, baseEnd_3386772] using wordTrace_append hprefix tailTrace_3386772
  have hstable : (prefixWord ++ tailWord_3386772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3386772).length < 2 ^ (prefixWord ++ tailWord_3386772).sum := by decide
  have hdescent : baseEnd_3386772 < baseStart_3386772 := by decide
  rcases family_descends (prefixWord ++ tailWord_3386772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3386783 : List Nat := [1, 1, 2, 5, 1, 2, 3, 3, 1, 2, 2]
def baseStart_3386783 : Nat := 118140960795 + 3386783 * 2 ^ 59
def prefixEnd_3386783 : Nat := 4983230072969 + 3 ^ 40 * 3386783 * 2
def baseEnd_3386783 : Nat := 1739047551476327929636975

theorem tailTrace_3386783 : CollatzResearch.WordTrace tailWord_3386783 prefixEnd_3386783 1739047551476327929636975 := by
  unfold tailWord_3386783
  simp only [CollatzResearch.WordTrace]
  refine ⟨123526124089271082331421003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82350749392847388220947335 123526124089271082331421003)
  ·
    refine ⟨185289186133906623497131505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123526124089271082331421003 185289186133906623497131505)
    ·
      refine ⟨138966889600429967622848629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185289186133906623497131505 138966889600429967622848629)
      ·
        refine ⟨13028145900040309464642059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 138966889600429967622848629 13028145900040309464642059)
        ·
          refine ⟨19542218850060464196963089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13028145900040309464642059 19542218850060464196963089)
          ·
            refine ⟨14656664137545348147722317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19542218850060464196963089 14656664137545348147722317)
            ·
              refine ⟨5496249051579505555395869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14656664137545348147722317 5496249051579505555395869)
              ·
                refine ⟨2061093394342314583273451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5496249051579505555395869 2061093394342314583273451)
                ·
                  refine ⟨3091640091513471874910177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2061093394342314583273451 3091640091513471874910177)
                  ·
                    refine ⟨2318730068635103906182633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3091640091513471874910177 2318730068635103906182633)
                    ·
                      refine ⟨1739047551476327929636975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2318730068635103906182633 1739047551476327929636975)
                      ·
                        rfl

theorem cell23_3386783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 3, 3, 1, 2, 2].length) (baseStart_3386783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3386783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3386783 prefixEnd_3386783 := by exact prefixLift 3386783
  have htrace : WordTrace (prefixWord ++ tailWord_3386783) baseStart_3386783 baseEnd_3386783 := by
    simpa [prefixWord, tailWord_3386783, baseEnd_3386783] using wordTrace_append hprefix tailTrace_3386783
  have hstable : (prefixWord ++ tailWord_3386783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3386783).length < 2 ^ (prefixWord ++ tailWord_3386783).sum := by decide
  have hdescent : baseEnd_3386783 < baseStart_3386783 := by decide
  rcases family_descends (prefixWord ++ tailWord_3386783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3386815 : List Nat := [1, 1, 2, 2, 2, 1, 1, 5, 2, 6]
def baseStart_3386815 : Nat := 118140960795 + 3386815 * 2 ^ 59
def prefixEnd_3386815 : Nat := 4983230072969 + 3 ^ 40 * 3386815 * 2
def baseEnd_3386815 : Nat := 579687994285757268145609

theorem tailTrace_3386815 : CollatzResearch.WordTrace tailWord_3386815 prefixEnd_3386815 579687994285757268145609 := by
  unfold tailWord_3386815
  simp only [CollatzResearch.WordTrace]
  refine ⟨123527291225155151796585899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82351527483436767864390599 123527291225155151796585899)
  ·
    refine ⟨185290936837732727694878849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123527291225155151796585899 185290936837732727694878849)
    ·
      refine ⟨138968202628299545771159137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185290936837732727694878849 138968202628299545771159137)
      ·
        refine ⟨104226151971224659328369353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138968202628299545771159137 104226151971224659328369353)
        ·
          refine ⟨78169613978418494496277015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104226151971224659328369353 78169613978418494496277015)
          ·
            refine ⟨117254420967627741744415523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78169613978418494496277015 117254420967627741744415523)
            ·
              refine ⟨175881631451441612616623285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117254420967627741744415523 175881631451441612616623285)
              ·
                refine ⟨16488902948572651182808433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 175881631451441612616623285 16488902948572651182808433)
                ·
                  refine ⟨12366677211429488387106325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16488902948572651182808433 12366677211429488387106325)
                  ·
                    refine ⟨579687994285757268145609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12366677211429488387106325 579687994285757268145609)
                    ·
                      rfl

theorem cell23_3386815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 5, 2, 6].length) (baseStart_3386815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3386815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3386815 prefixEnd_3386815 := by exact prefixLift 3386815
  have htrace : WordTrace (prefixWord ++ tailWord_3386815) baseStart_3386815 baseEnd_3386815 := by
    simpa [prefixWord, tailWord_3386815, baseEnd_3386815] using wordTrace_append hprefix tailTrace_3386815
  have hstable : (prefixWord ++ tailWord_3386815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3386815).length < 2 ^ (prefixWord ++ tailWord_3386815).sum := by decide
  have hdescent : baseEnd_3386815 < baseStart_3386815 := by decide
  rcases family_descends (prefixWord ++ tailWord_3386815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3386816 : List Nat := [2, 1, 1, 2, 3, 1, 6, 1, 2, 1, 3]
def baseStart_3386816 : Nat := 118140960795 + 3386816 * 2 ^ 59
def prefixEnd_3386816 : Nat := 4983230072969 + 3 ^ 40 * 3386816 * 2
def baseEnd_3386816 : Nat := 1739064496337926300524323

theorem tailTrace_3386816 : CollatzResearch.WordTrace tailWord_3386816 prefixEnd_3386816 1739064496337926300524323 := by
  unfold tailWord_3386816
  simp only [CollatzResearch.WordTrace]
  refine ⟨61763663849075764483686151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82351551798767685978248201 61763663849075764483686151)
  ·
    refine ⟨92645495773613646725529227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61763663849075764483686151 92645495773613646725529227)
    ·
      refine ⟨138968243660420470088293841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92645495773613646725529227 138968243660420470088293841)
      ·
        refine ⟨104226182745315352566220381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138968243660420470088293841 104226182745315352566220381)
        ·
          refine ⟨39084818529493257212332643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104226182745315352566220381 39084818529493257212332643)
          ·
            refine ⟨58627227794239885818498965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39084818529493257212332643 58627227794239885818498965)
            ·
              refine ⟨2748151302854994647742139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 58627227794239885818498965 2748151302854994647742139)
              ·
                refine ⟨4122226954282491971613209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2748151302854994647742139 4122226954282491971613209)
                ·
                  refine ⟨3091670215711868978709907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4122226954282491971613209 3091670215711868978709907)
                  ·
                    refine ⟨4637505323567803468064861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3091670215711868978709907 4637505323567803468064861)
                    ·
                      refine ⟨1739064496337926300524323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4637505323567803468064861 1739064496337926300524323)
                      ·
                        rfl

theorem cell23_3386816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 6, 1, 2, 1, 3].length) (baseStart_3386816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3386816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3386816 prefixEnd_3386816 := by exact prefixLift 3386816
  have htrace : WordTrace (prefixWord ++ tailWord_3386816) baseStart_3386816 baseEnd_3386816 := by
    simpa [prefixWord, tailWord_3386816, baseEnd_3386816] using wordTrace_append hprefix tailTrace_3386816
  have hstable : (prefixWord ++ tailWord_3386816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3386816).length < 2 ^ (prefixWord ++ tailWord_3386816).sum := by decide
  have hdescent : baseEnd_3386816 < baseStart_3386816 := by decide
  rcases family_descends (prefixWord ++ tailWord_3386816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3386826 : List Nat := [3, 1, 2, 1, 2, 3, 3, 2, 1, 3, 2]
def baseStart_3386826 : Nat := 118140960795 + 3386826 * 2 ^ 59
def prefixEnd_3386826 : Nat := 4983230072969 + 3 ^ 40 * 3386826 * 2
def baseEnd_3386826 : Nat := 1739069631144471261399277

theorem tailTrace_3386826 : CollatzResearch.WordTrace tailWord_3386826 prefixEnd_3386826 1739069631144471261399277 := by
  unfold tailWord_3386826
  simp only [CollatzResearch.WordTrace]
  refine ⟨30881923107028825168809083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82351794952076867116824221 30881923107028825168809083)
  ·
    refine ⟨46322884660543237753213625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30881923107028825168809083 46322884660543237753213625)
    ·
      refine ⟨34742163495407428314910219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46322884660543237753213625 34742163495407428314910219)
      ·
        refine ⟨52113245243111142472365329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34742163495407428314910219 52113245243111142472365329)
        ·
          refine ⟨39084933932333356854273997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52113245243111142472365329 39084933932333356854273997)
          ·
            refine ⟨14656850224625008820352749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39084933932333356854273997 14656850224625008820352749)
            ·
              refine ⟨5496318834234378307632281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14656850224625008820352749 5496318834234378307632281)
              ·
                refine ⟨4122239125675783730724211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5496318834234378307632281 4122239125675783730724211)
                ·
                  refine ⟨6183358688513675596086317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4122239125675783730724211 6183358688513675596086317)
                  ·
                    refine ⟨2318759508192628348532369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6183358688513675596086317 2318759508192628348532369)
                    ·
                      refine ⟨1739069631144471261399277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2318759508192628348532369 1739069631144471261399277)
                      ·
                        rfl

theorem cell23_3386826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 3, 2, 1, 3, 2].length) (baseStart_3386826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3386826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3386826 prefixEnd_3386826 := by exact prefixLift 3386826
  have htrace : WordTrace (prefixWord ++ tailWord_3386826) baseStart_3386826 baseEnd_3386826 := by
    simpa [prefixWord, tailWord_3386826, baseEnd_3386826] using wordTrace_append hprefix tailTrace_3386826
  have hstable : (prefixWord ++ tailWord_3386826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3386826).length < 2 ^ (prefixWord ++ tailWord_3386826).sum := by decide
  have hdescent : baseEnd_3386826 < baseStart_3386826 := by decide
  rcases family_descends (prefixWord ++ tailWord_3386826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3386839 : List Nat := [1, 1, 3, 2, 1, 1, 1, 3, 6, 2, 2]
def baseStart_3386839 : Nat := 118140960795 + 3386839 * 2 ^ 59
def prefixEnd_3386839 : Nat := 4983230072969 + 3 ^ 40 * 3386839 * 2
def baseEnd_3386839 : Nat := 1739076306392979710536717

theorem tailTrace_3386839 : CollatzResearch.WordTrace tailWord_3386839 prefixEnd_3386839 1739076306392979710536717 := by
  unfold tailWord_3386839
  simp only [CollatzResearch.WordTrace]
  refine ⟨123528166577068203895459571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82352111051378802596973047 123528166577068203895459571)
  ·
    refine ⟨185292249865602305843189357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123528166577068203895459571 185292249865602305843189357)
    ·
      refine ⟨69484593699600864691196009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185292249865602305843189357 69484593699600864691196009)
      ·
        refine ⟨52113445274700648518397007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69484593699600864691196009 52113445274700648518397007)
        ·
          refine ⟨78170167912050972777595511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52113445274700648518397007 78170167912050972777595511)
          ·
            refine ⟨117255251868076459166393267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78170167912050972777595511 117255251868076459166393267)
            ·
              refine ⟨175882877802114688749589901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117255251868076459166393267 175882877802114688749589901)
              ·
                refine ⟨65956079175793008281096213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 175882877802114688749589901 65956079175793008281096213)
                ·
                  refine ⟨3091691211365297263176385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 65956079175793008281096213 3091691211365297263176385)
                  ·
                    refine ⟨2318768408523972947382289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3091691211365297263176385 2318768408523972947382289)
                    ·
                      refine ⟨1739076306392979710536717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2318768408523972947382289 1739076306392979710536717)
                      ·
                        rfl

theorem cell23_3386839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 6, 2, 2].length) (baseStart_3386839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3386839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3386839 prefixEnd_3386839 := by exact prefixLift 3386839
  have htrace : WordTrace (prefixWord ++ tailWord_3386839) baseStart_3386839 baseEnd_3386839 := by
    simpa [prefixWord, tailWord_3386839, baseEnd_3386839] using wordTrace_append hprefix tailTrace_3386839
  have hstable : (prefixWord ++ tailWord_3386839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3386839).length < 2 ^ (prefixWord ++ tailWord_3386839).sum := by decide
  have hdescent : baseEnd_3386839 < baseStart_3386839 := by decide
  rcases family_descends (prefixWord ++ tailWord_3386839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3386842 : List Nat := [3, 1, 1, 2, 3, 2, 2, 1, 2, 1, 5]
def baseStart_3386842 : Nat := 118140960795 + 3386842 * 2 ^ 59
def prefixEnd_3386842 : Nat := 4983230072969 + 3 ^ 40 * 3386842 * 2
def baseEnd_3386842 : Nat := 1739077846834943198799203

theorem tailTrace_3386842 : CollatzResearch.WordTrace tailWord_3386842 prefixEnd_3386842 1739077846834943198799203 := by
  unfold tailWord_3386842
  simp only [CollatzResearch.WordTrace]
  refine ⟨30882068999014333851954695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82352183997371556938545853 30882068999014333851954695)
  ·
    refine ⟨46323103498521500777932043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30882068999014333851954695 46323103498521500777932043)
    ·
      refine ⟨69484655247782251166898065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46323103498521500777932043 69484655247782251166898065)
      ·
        refine ⟨52113491435836688375173549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69484655247782251166898065 52113491435836688375173549)
        ·
          refine ⟨19542559288438758140690081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52113491435836688375173549 19542559288438758140690081)
          ·
            refine ⟨14656919466329068605517561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19542559288438758140690081 14656919466329068605517561)
            ·
              refine ⟨10992689599746801454138171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14656919466329068605517561 10992689599746801454138171)
              ·
                refine ⟨16489034399620202181207257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10992689599746801454138171 16489034399620202181207257)
                ·
                  refine ⟨12366775799715151635905443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16489034399620202181207257 12366775799715151635905443)
                  ·
                    refine ⟨18550163699572727453858165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12366775799715151635905443 18550163699572727453858165)
                    ·
                      refine ⟨1739077846834943198799203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18550163699572727453858165 1739077846834943198799203)
                      ·
                        rfl

theorem cell23_3386842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 1, 2, 1, 5].length) (baseStart_3386842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3386842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3386842 prefixEnd_3386842 := by exact prefixLift 3386842
  have htrace : WordTrace (prefixWord ++ tailWord_3386842) baseStart_3386842 baseEnd_3386842 := by
    simpa [prefixWord, tailWord_3386842, baseEnd_3386842] using wordTrace_append hprefix tailTrace_3386842
  have hstable : (prefixWord ++ tailWord_3386842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3386842).length < 2 ^ (prefixWord ++ tailWord_3386842).sum := by decide
  have hdescent : baseEnd_3386842 < baseStart_3386842 := by decide
  rcases family_descends (prefixWord ++ tailWord_3386842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3386862 : List Nat := [4, 1, 2, 1, 2, 1, 2, 3, 7]
def baseStart_3386862 : Nat := 118140960795 + 3386862 * 2 ^ 59
def prefixEnd_3386862 : Nat := 4983230072969 + 3 ^ 40 * 3386862 * 2
def baseEnd_3386862 : Nat := 193232012938670346727679

theorem tailTrace_3386862 : CollatzResearch.WordTrace tailWord_3386862 prefixEnd_3386862 193232012938670346727679 := by
  unfold tailWord_3386862
  simp only [CollatzResearch.WordTrace]
  refine ⟨15441125681998109852943355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82352670303989919215697893 15441125681998109852943355)
  ·
    refine ⟨23161688522997164779415033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15441125681998109852943355 23161688522997164779415033)
    ·
      refine ⟨17371266392247873584561275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23161688522997164779415033 17371266392247873584561275)
      ·
        refine ⟨26056899588371810376841913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17371266392247873584561275 26056899588371810376841913)
        ·
          refine ⟨19542674691278857782631435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26056899588371810376841913 19542674691278857782631435)
          ·
            refine ⟨29314012036918286673947153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19542674691278857782631435 29314012036918286673947153)
            ·
              refine ⟨21985509027688715005460365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29314012036918286673947153 21985509027688715005460365)
              ·
                refine ⟨8244565885383268127047637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21985509027688715005460365 8244565885383268127047637)
                ·
                  refine ⟨193232012938670346727679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8244565885383268127047637 193232012938670346727679)
                  ·
                    rfl

theorem cell23_3386862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 3, 7].length) (baseStart_3386862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3386862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3386862 prefixEnd_3386862 := by exact prefixLift 3386862
  have htrace : WordTrace (prefixWord ++ tailWord_3386862) baseStart_3386862 baseEnd_3386862 := by
    simpa [prefixWord, tailWord_3386862, baseEnd_3386862] using wordTrace_append hprefix tailTrace_3386862
  have hstable : (prefixWord ++ tailWord_3386862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3386862).length < 2 ^ (prefixWord ++ tailWord_3386862).sum := by decide
  have hdescent : baseEnd_3386862 < baseStart_3386862 := by decide
  rcases family_descends (prefixWord ++ tailWord_3386862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3386869 : List Nat := [1, 3, 5, 1, 1, 1, 1, 1, 1, 4, 4]
def baseStart_3386869 : Nat := 118140960795 + 3386869 * 2 ^ 59
def prefixEnd_3386869 : Nat := 4983230072969 + 3 ^ 40 * 3386869 * 2
def baseEnd_3386869 : Nat := 1739091710812614593161579

theorem tailTrace_3386869 : CollatzResearch.WordTrace tailWord_3386869 prefixEnd_3386869 1739091710812614593161579 := by
  unfold tailWord_3386869
  simp only [CollatzResearch.WordTrace]
  refine ⟨123529260766959519019051661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82352840511306346012701107 123529260766959519019051661)
  ·
    refine ⟨46323472787609819632144373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123529260766959519019051661 46323472787609819632144373)
    ·
      refine ⟨4342825573838420590513535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46323472787609819632144373 4342825573838420590513535)
      ·
        refine ⟨6514238360757630885770303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4342825573838420590513535 6514238360757630885770303)
        ·
          refine ⟨9771357541136446328655455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6514238360757630885770303 9771357541136446328655455)
          ·
            refine ⟨14657036311704669492983183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9771357541136446328655455 14657036311704669492983183)
            ·
              refine ⟨21985554467557004239474775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14657036311704669492983183 21985554467557004239474775)
              ·
                refine ⟨32978331701335506359212163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21985554467557004239474775 32978331701335506359212163)
                ·
                  refine ⟨49467497552003259538818245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32978331701335506359212163 49467497552003259538818245)
                  ·
                    refine ⟨9275155791000611163528421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49467497552003259538818245 9275155791000611163528421)
                    ·
                      refine ⟨1739091710812614593161579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9275155791000611163528421 1739091710812614593161579)
                      ·
                        rfl

theorem cell23_3386869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_3386869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3386869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3386869 prefixEnd_3386869 := by exact prefixLift 3386869
  have htrace : WordTrace (prefixWord ++ tailWord_3386869) baseStart_3386869 baseEnd_3386869 := by
    simpa [prefixWord, tailWord_3386869, baseEnd_3386869] using wordTrace_append hprefix tailTrace_3386869
  have hstable : (prefixWord ++ tailWord_3386869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3386869).length < 2 ^ (prefixWord ++ tailWord_3386869).sum := by decide
  have hdescent : baseEnd_3386869 < baseStart_3386869 := by decide
  rcases family_descends (prefixWord ++ tailWord_3386869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3386872 : List Nat := [2, 1, 2, 1, 1, 5, 1, 1, 1, 5, 3]
def baseStart_3386872 : Nat := 118140960795 + 3386872 * 2 ^ 59
def prefixEnd_3386872 : Nat := 4983230072969 + 3 ^ 40 * 3386872 * 2
def baseEnd_3386872 : Nat := 1739093251254578081424065

theorem tailTrace_3386872 : CollatzResearch.WordTrace tailWord_3386872 prefixEnd_3386872 1739093251254578081424065 := by
  unfold tailWord_3386872
  simp only [CollatzResearch.WordTrace]
  refine ⟨61764685092974325265705435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82352913457299100354273913 61764685092974325265705435)
  ·
    refine ⟨92647027639461487898558153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61764685092974325265705435 92647027639461487898558153)
    ·
      refine ⟨69485270729596115923918615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92647027639461487898558153 69485270729596115923918615)
      ·
        refine ⟨104227906094394173885877923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69485270729596115923918615 104227906094394173885877923)
        ·
          refine ⟨156341859141591260828816885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104227906094394173885877923 156341859141591260828816885)
          ·
            refine ⟨14657049294524180702701583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 156341859141591260828816885 14657049294524180702701583)
            ·
              refine ⟨21985573941786271054052375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14657049294524180702701583 21985573941786271054052375)
              ·
                refine ⟨32978360912679406581078563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21985573941786271054052375 32978360912679406581078563)
                ·
                  refine ⟨49467541369019109871617845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32978360912679406581078563 49467541369019109871617845)
                  ·
                    refine ⟨4637582003345541550464173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49467541369019109871617845 4637582003345541550464173)
                    ·
                      refine ⟨1739093251254578081424065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4637582003345541550464173 1739093251254578081424065)
                      ·
                        rfl

theorem cell23_3386872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 1, 1, 5, 3].length) (baseStart_3386872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3386872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3386872 prefixEnd_3386872 := by exact prefixLift 3386872
  have htrace : WordTrace (prefixWord ++ tailWord_3386872) baseStart_3386872 baseEnd_3386872 := by
    simpa [prefixWord, tailWord_3386872, baseEnd_3386872] using wordTrace_append hprefix tailTrace_3386872
  have hstable : (prefixWord ++ tailWord_3386872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3386872).length < 2 ^ (prefixWord ++ tailWord_3386872).sum := by decide
  have hdescent : baseEnd_3386872 < baseStart_3386872 := by decide
  rcases family_descends (prefixWord ++ tailWord_3386872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3386875 : List Nat := [1, 1, 1, 1, 1, 3, 2, 3, 3, 7]
def baseStart_3386875 : Nat := 118140960795 + 3386875 * 2 ^ 59
def prefixEnd_3386875 : Nat := 4983230072969 + 3 ^ 40 * 3386875 * 2
def baseEnd_3386875 : Nat := 579698263898847189895517

theorem tailTrace_3386875 : CollatzResearch.WordTrace tailWord_3386875 prefixEnd_3386875 579698263898847189895517 := by
  unfold tailWord_3386875
  simp only [CollatzResearch.WordTrace]
  refine ⟨123529479604937782043770079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82352986403291854695846719 123529479604937782043770079)
  ·
    refine ⟨185294219407406673065655119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123529479604937782043770079 185294219407406673065655119)
    ·
      refine ⟨277941329111110009598482679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185294219407406673065655119 277941329111110009598482679)
      ·
        refine ⟨416911993666665014397724019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277941329111110009598482679 416911993666665014397724019)
        ·
          refine ⟨625367990499997521596586029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 416911993666665014397724019 625367990499997521596586029)
          ·
            refine ⟨234512996437499070598719761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 625367990499997521596586029 234512996437499070598719761)
            ·
              refine ⟨175884747328124302949039821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 234512996437499070598719761 175884747328124302949039821)
              ·
                refine ⟨65956780248046613605889933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 175884747328124302949039821 65956780248046613605889933)
                ·
                  refine ⟨24733792593017480102208725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65956780248046613605889933 24733792593017480102208725)
                  ·
                    refine ⟨579698263898847189895517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24733792593017480102208725 579698263898847189895517)
                    ·
                      rfl

theorem cell23_3386875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 3, 7].length) (baseStart_3386875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3386875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3386875 prefixEnd_3386875 := by exact prefixLift 3386875
  have htrace : WordTrace (prefixWord ++ tailWord_3386875) baseStart_3386875 baseEnd_3386875 := by
    simpa [prefixWord, tailWord_3386875, baseEnd_3386875] using wordTrace_append hprefix tailTrace_3386875
  have hstable : (prefixWord ++ tailWord_3386875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3386875).length < 2 ^ (prefixWord ++ tailWord_3386875).sum := by decide
  have hdescent : baseEnd_3386875 < baseStart_3386875 := by decide
  rcases family_descends (prefixWord ++ tailWord_3386875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3386895 : List Nat := [1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 8]
def baseStart_3386895 : Nat := 118140960795 + 3386895 * 2 ^ 59
def prefixEnd_3386895 : Nat := 4983230072969 + 3 ^ 40 * 3386895 * 2
def baseEnd_3386895 : Nat := 1739105061309631491436459

theorem tailTrace_3386895 : CollatzResearch.WordTrace tailWord_3386895 prefixEnd_3386895 1739105061309631491436459 := by
  unfold tailWord_3386895
  simp only [CollatzResearch.WordTrace]
  refine ⟨123530209064865325459498139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82353472709910216972998759 123530209064865325459498139)
  ·
    refine ⟨185295313597297988189247209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123530209064865325459498139 185295313597297988189247209)
    ·
      refine ⟨138971485197973491141935407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185295313597297988189247209 138971485197973491141935407)
      ·
        refine ⟨208457227796960236712903111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138971485197973491141935407 208457227796960236712903111)
        ·
          refine ⟨312685841695440355069354667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208457227796960236712903111 312685841695440355069354667)
          ·
            refine ⟨469028762543160532604032001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 312685841695440355069354667 469028762543160532604032001)
            ·
              refine ⟨351771571907370399453024001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 469028762543160532604032001 351771571907370399453024001)
              ·
                refine ⟨263828678930527799589768001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 351771571907370399453024001 263828678930527799589768001)
                ·
                  refine ⟨197871509197895849692326001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 263828678930527799589768001 197871509197895849692326001)
                  ·
                    refine ⟨148403631898421887269244501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 197871509197895849692326001 148403631898421887269244501)
                    ·
                      refine ⟨1739105061309631491436459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 148403631898421887269244501 1739105061309631491436459)
                      ·
                        rfl

theorem cell23_3386895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 8].length) (baseStart_3386895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3386895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3386895 prefixEnd_3386895 := by exact prefixLift 3386895
  have htrace : WordTrace (prefixWord ++ tailWord_3386895) baseStart_3386895 baseEnd_3386895 := by
    simpa [prefixWord, tailWord_3386895, baseEnd_3386895] using wordTrace_append hprefix tailTrace_3386895
  have hstable : (prefixWord ++ tailWord_3386895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3386895).length < 2 ^ (prefixWord ++ tailWord_3386895).sum := by decide
  have hdescent : baseEnd_3386895 < baseStart_3386895 := by decide
  rcases family_descends (prefixWord ++ tailWord_3386895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3386949 : List Nat := [1, 3, 1, 1, 1, 4, 2, 3, 2, 2, 3]
def baseStart_3386949 : Nat := 118140960795 + 3386949 * 2 ^ 59
def prefixEnd_3386949 : Nat := 4983230072969 + 3 ^ 40 * 3386949 * 2
def baseEnd_3386949 : Nat := 1739132789264974280161211

theorem tailTrace_3386949 : CollatzResearch.WordTrace tailWord_3386949 prefixEnd_3386949 1739132789264974280161211 := by
  unfold tailWord_3386949
  simp only [CollatzResearch.WordTrace]
  refine ⟨123532178606669692681963901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82354785737779795121309267 123532178606669692681963901)
  ·
    refine ⟨46324566977501134755736463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123532178606669692681963901 46324566977501134755736463)
    ·
      refine ⟨69486850466251702133604695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46324566977501134755736463 69486850466251702133604695)
      ·
        refine ⟨104230275699377553200407043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69486850466251702133604695 104230275699377553200407043)
        ·
          refine ⟨156345413549066329800610565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104230275699377553200407043 156345413549066329800610565)
          ·
            refine ⟨29314765040449936837614481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 156345413549066329800610565 29314765040449936837614481)
            ·
              refine ⟨21986073780337452628210861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29314765040449936837614481 21986073780337452628210861)
              ·
                refine ⟨8244777667626544735579073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21986073780337452628210861 8244777667626544735579073)
                ·
                  refine ⟨6183583250719908551684305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8244777667626544735579073 6183583250719908551684305)
                  ·
                    refine ⟨4637687438039931413763229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6183583250719908551684305 4637687438039931413763229)
                    ·
                      refine ⟨1739132789264974280161211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4637687438039931413763229 1739132789264974280161211)
                      ·
                        rfl

theorem cell23_3386949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 3, 2, 2, 3].length) (baseStart_3386949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3386949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3386949 prefixEnd_3386949 := by exact prefixLift 3386949
  have htrace : WordTrace (prefixWord ++ tailWord_3386949) baseStart_3386949 baseEnd_3386949 := by
    simpa [prefixWord, tailWord_3386949, baseEnd_3386949] using wordTrace_append hprefix tailTrace_3386949
  have hstable : (prefixWord ++ tailWord_3386949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3386949).length < 2 ^ (prefixWord ++ tailWord_3386949).sum := by decide
  have hdescent : baseEnd_3386949 < baseStart_3386949 := by decide
  rcases family_descends (prefixWord ++ tailWord_3386949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3386986 : List Nat := [3, 1, 3, 2, 1, 2, 4, 1, 6]
def baseStart_3386986 : Nat := 118140960795 + 3386986 * 2 ^ 59
def prefixEnd_3386986 : Nat := 4983230072969 + 3 ^ 40 * 3386986 * 2
def baseEnd_3386986 : Nat := 193239087561021181710949

theorem tailTrace_3386986 : CollatzResearch.WordTrace tailWord_3386986 prefixEnd_3386986 193239087561021181710949 := by
  unfold tailWord_3386986
  simp only [CollatzResearch.WordTrace]
  refine ⟨30883382026883912000265203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82355685405023765334040541 30883382026883912000265203)
  ·
    refine ⟨46325073040325868000397805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30883382026883912000265203 46325073040325868000397805)
    ·
      refine ⟨17371902390122200500149177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46325073040325868000397805 17371902390122200500149177)
      ·
        refine ⟨13028926792591650375111883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17371902390122200500149177 13028926792591650375111883)
        ·
          refine ⟨19543390188887475562667825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13028926792591650375111883 19543390188887475562667825)
          ·
            refine ⟨14657542641665606672000869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19543390188887475562667825 14657542641665606672000869)
            ·
              refine ⟨2748289245312301251000163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14657542641665606672000869 2748289245312301251000163)
              ·
                refine ⟨4122433867968451876500245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2748289245312301251000163 4122433867968451876500245)
                ·
                  refine ⟨193239087561021181710949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4122433867968451876500245 193239087561021181710949)
                  ·
                    rfl

theorem cell23_3386986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 4, 1, 6].length) (baseStart_3386986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3386986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3386986 prefixEnd_3386986 := by exact prefixLift 3386986
  have htrace : WordTrace (prefixWord ++ tailWord_3386986) baseStart_3386986 baseEnd_3386986 := by
    simpa [prefixWord, tailWord_3386986, baseEnd_3386986] using wordTrace_append hprefix tailTrace_3386986
  have hstable : (prefixWord ++ tailWord_3386986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3386986).length < 2 ^ (prefixWord ++ tailWord_3386986).sum := by decide
  have hdescent : baseEnd_3386986 < baseStart_3386986 := by decide
  rcases family_descends (prefixWord ++ tailWord_3386986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3387013 : List Nat := [1, 3, 1, 1, 4, 1, 2, 5, 1, 1, 3]
def baseStart_3387013 : Nat := 118140960795 + 3387013 * 2 ^ 59
def prefixEnd_3387013 : Nat := 4983230072969 + 3 ^ 40 * 3387013 * 2
def baseEnd_3387013 : Nat := 1739165652026862029760917

theorem tailTrace_3387013 : CollatzResearch.WordTrace tailWord_3387013 prefixEnd_3387013 1739165652026862029760917 := by
  unfold tailWord_3387013
  simp only [CollatzResearch.WordTrace]
  refine ⟨123534512878437831612293693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82356341918958554408195795 123534512878437831612293693)
  ·
    refine ⟨46325442329414186854610135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123534512878437831612293693 46325442329414186854610135)
    ·
      refine ⟨69488163494121280281915203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46325442329414186854610135 69488163494121280281915203)
      ·
        refine ⟨104232245241181920422872805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69488163494121280281915203 104232245241181920422872805)
        ·
          refine ⟨19543545982721610079288651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104232245241181920422872805 19543545982721610079288651)
          ·
            refine ⟨29315318974082415118932977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19543545982721610079288651 29315318974082415118932977)
            ·
              refine ⟨21986489230561811339199733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29315318974082415118932977 21986489230561811339199733)
              ·
                refine ⟨2061233365365169813049975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21986489230561811339199733 2061233365365169813049975)
                ·
                  refine ⟨3091850048047754719574963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2061233365365169813049975 3091850048047754719574963)
                  ·
                    refine ⟨4637775072071632079362445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3091850048047754719574963 4637775072071632079362445)
                    ·
                      refine ⟨1739165652026862029760917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4637775072071632079362445 1739165652026862029760917)
                      ·
                        rfl

theorem cell23_3387013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 5, 1, 1, 3].length) (baseStart_3387013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3387013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3387013 prefixEnd_3387013 := by exact prefixLift 3387013
  have htrace : WordTrace (prefixWord ++ tailWord_3387013) baseStart_3387013 baseEnd_3387013 := by
    simpa [prefixWord, tailWord_3387013, baseEnd_3387013] using wordTrace_append hprefix tailTrace_3387013
  have hstable : (prefixWord ++ tailWord_3387013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3387013).length < 2 ^ (prefixWord ++ tailWord_3387013).sum := by decide
  have hdescent : baseEnd_3387013 < baseStart_3387013 := by decide
  rcases family_descends (prefixWord ++ tailWord_3387013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3387029 : List Nat := [1, 3, 2, 1, 1, 1, 1, 5, 4, 4]
def baseStart_3387029 : Nat := 118140960795 + 3387029 * 2 ^ 59
def prefixEnd_3387029 : Nat := 4983230072969 + 3 ^ 40 * 3387029 * 2
def baseEnd_3387029 : Nat := 579724622572444655720281

theorem tailTrace_3387029 : CollatzResearch.WordTrace tailWord_3387029 prefixEnd_3387029 579724622572444655720281 := by
  unfold tailWord_3387029
  simp only [CollatzResearch.WordTrace]
  refine ⟨123535096446379866344876141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82356730964253244229917427 123535096446379866344876141)
  ·
    refine ⟨46325661167392449879328553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123535096446379866344876141 46325661167392449879328553)
    ·
      refine ⟨34744245875544337409496415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46325661167392449879328553 34744245875544337409496415)
      ·
        refine ⟨52116368813316506114244623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34744245875544337409496415 52116368813316506114244623)
        ·
          refine ⟨78174553219974759171366935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52116368813316506114244623 78174553219974759171366935)
          ·
            refine ⟨117261829829962138757050403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78174553219974759171366935 117261829829962138757050403)
            ·
              refine ⟨175892744744943208135575605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117261829829962138757050403 175892744744943208135575605)
              ·
                refine ⟨16489944819838425762710213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 175892744744943208135575605 16489944819838425762710213)
                ·
                  refine ⟨3091864653719704830508165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16489944819838425762710213 3091864653719704830508165)
                  ·
                    refine ⟨579724622572444655720281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3091864653719704830508165 579724622572444655720281)
                    ·
                      rfl

theorem cell23_3387029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 5, 4, 4].length) (baseStart_3387029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3387029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3387029 prefixEnd_3387029 := by exact prefixLift 3387029
  have htrace : WordTrace (prefixWord ++ tailWord_3387029) baseStart_3387029 baseEnd_3387029 := by
    simpa [prefixWord, tailWord_3387029, baseEnd_3387029] using wordTrace_append hprefix tailTrace_3387029
  have hstable : (prefixWord ++ tailWord_3387029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3387029).length < 2 ^ (prefixWord ++ tailWord_3387029).sum := by decide
  have hdescent : baseEnd_3387029 < baseStart_3387029 := by decide
  rcases family_descends (prefixWord ++ tailWord_3387029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3387052 : List Nat := [2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 7]
def baseStart_3387052 : Nat := 118140960795 + 3387052 * 2 ^ 59
def prefixEnd_3387052 : Nat := 4983230072969 + 3 ^ 40 * 3387052 * 2
def baseEnd_3387052 : Nat := 1739185677772387377173237

theorem tailTrace_3387052 : CollatzResearch.WordTrace tailWord_3387052 prefixEnd_3387052 1739185677772387377173237 := by
  unfold tailWord_3387052
  simp only [CollatzResearch.WordTrace]
  refine ⟨61767967662648270636481705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82357290216864360848642273 61767967662648270636481705)
  ·
    refine ⟨46325975746986202977361279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61767967662648270636481705 46325975746986202977361279)
    ·
      refine ⟨69488963620479304466041919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46325975746986202977361279 69488963620479304466041919)
      ·
        refine ⟨104233445430718956699062879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69488963620479304466041919 104233445430718956699062879)
        ·
          refine ⟨156350168146078435048594319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104233445430718956699062879 156350168146078435048594319)
          ·
            refine ⟨234525252219117652572891479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156350168146078435048594319 234525252219117652572891479)
            ·
              refine ⟨351787878328676478859337219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 234525252219117652572891479 351787878328676478859337219)
              ·
                refine ⟨527681817493014718289005829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 351787878328676478859337219 527681817493014718289005829)
                ·
                  refine ⟨98940340779940259679188593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 527681817493014718289005829 98940340779940259679188593)
                  ·
                    refine ⟨74205255584955194759391445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 98940340779940259679188593 74205255584955194759391445)
                    ·
                      refine ⟨1739185677772387377173237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 74205255584955194759391445 1739185677772387377173237)
                      ·
                        rfl

theorem cell23_3387052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 7].length) (baseStart_3387052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3387052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3387052 prefixEnd_3387052 := by exact prefixLift 3387052
  have htrace : WordTrace (prefixWord ++ tailWord_3387052) baseStart_3387052 baseEnd_3387052 := by
    simpa [prefixWord, tailWord_3387052, baseEnd_3387052] using wordTrace_append hprefix tailTrace_3387052
  have hstable : (prefixWord ++ tailWord_3387052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3387052).length < 2 ^ (prefixWord ++ tailWord_3387052).sum := by decide
  have hdescent : baseEnd_3387052 < baseStart_3387052 := by decide
  rcases family_descends (prefixWord ++ tailWord_3387052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3387059 : List Nat := [1, 1, 1, 2, 3, 3, 5, 7]
def baseStart_3387059 : Nat := 118140960795 + 3387059 * 2 ^ 59
def prefixEnd_3387059 : Nat := 4983230072969 + 3 ^ 40 * 3387059 * 2
def baseEnd_3387059 : Nat := 64414417486554401843915

theorem tailTrace_3387059 : CollatzResearch.WordTrace tailWord_3387059 prefixEnd_3387059 64414417486554401843915 := by
  unfold tailWord_3387059
  simp only [CollatzResearch.WordTrace]
  refine ⟨123536190636271181468468231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82357460424180787645645487 123536190636271181468468231)
  ·
    refine ⟨185304285954406772202702347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123536190636271181468468231 185304285954406772202702347)
    ·
      refine ⟨277956428931610158304053521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185304285954406772202702347 277956428931610158304053521)
      ·
        refine ⟨208467321698707618728040141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 277956428931610158304053521 208467321698707618728040141)
        ·
          refine ⟨78175245637015357023015053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 208467321698707618728040141 78175245637015357023015053)
          ·
            refine ⟨29315717113880758883630645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78175245637015357023015053 29315717113880758883630645)
            ·
              refine ⟨2748348479426321145340373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29315717113880758883630645 2748348479426321145340373)
              ·
                refine ⟨64414417486554401843915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2748348479426321145340373 64414417486554401843915)
                ·
                  rfl

theorem cell23_3387059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 5, 7].length) (baseStart_3387059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3387059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3387059 prefixEnd_3387059 := by exact prefixLift 3387059
  have htrace : WordTrace (prefixWord ++ tailWord_3387059) baseStart_3387059 baseEnd_3387059 := by
    simpa [prefixWord, tailWord_3387059, baseEnd_3387059] using wordTrace_append hprefix tailTrace_3387059
  have hstable : (prefixWord ++ tailWord_3387059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3387059).length < 2 ^ (prefixWord ++ tailWord_3387059).sum := by decide
  have hdescent : baseEnd_3387059 < baseStart_3387059 := by decide
  rcases family_descends (prefixWord ++ tailWord_3387059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3387070 : List Nat := [4, 2, 1, 1, 2, 4, 2, 1, 1, 1, 4]
def baseStart_3387070 : Nat := 118140960795 + 3387070 * 2 ^ 59
def prefixEnd_3387070 : Nat := 4983230072969 + 3 ^ 40 * 3387070 * 2
def baseEnd_3387070 : Nat := 1739194920424168306748155

theorem tailTrace_3387070 : CollatzResearch.WordTrace tailWord_3387070 prefixEnd_3387070 1739194920424168306748155 := by
  unfold tailWord_3387070
  simp only [CollatzResearch.WordTrace]
  refine ⟨15442073979903916293389833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82357727892820886898079109 15442073979903916293389833)
  ·
    refine ⟨11581555484927937220042375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15442073979903916293389833 11581555484927937220042375)
    ·
      refine ⟨17372333227391905830063563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11581555484927937220042375 17372333227391905830063563)
      ·
        refine ⟨26058499841087858745095345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17372333227391905830063563 26058499841087858745095345)
        ·
          refine ⟨19543874880815894058821509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26058499841087858745095345 19543874880815894058821509)
          ·
            refine ⟨3664476540152980136029033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19543874880815894058821509 3664476540152980136029033)
            ·
              refine ⟨2748357405114735102021775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3664476540152980136029033 2748357405114735102021775)
              ·
                refine ⟨4122536107672102653032663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2748357405114735102021775 4122536107672102653032663)
                ·
                  refine ⟨6183804161508153979548995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4122536107672102653032663 6183804161508153979548995)
                  ·
                    refine ⟨9275706242262230969323493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6183804161508153979548995 9275706242262230969323493)
                    ·
                      refine ⟨1739194920424168306748155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9275706242262230969323493 1739194920424168306748155)
                      ·
                        rfl

theorem cell23_3387070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 2, 1, 1, 1, 4].length) (baseStart_3387070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3387070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3387070 prefixEnd_3387070 := by exact prefixLift 3387070
  have htrace : WordTrace (prefixWord ++ tailWord_3387070) baseStart_3387070 baseEnd_3387070 := by
    simpa [prefixWord, tailWord_3387070, baseEnd_3387070] using wordTrace_append hprefix tailTrace_3387070
  have hstable : (prefixWord ++ tailWord_3387070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3387070).length < 2 ^ (prefixWord ++ tailWord_3387070).sum := by decide
  have hdescent : baseEnd_3387070 < baseStart_3387070 := by decide
  rcases family_descends (prefixWord ++ tailWord_3387070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3387100 : List Nat := [2, 2, 5, 1, 2, 2, 1, 1, 1, 2, 4]
def baseStart_3387100 : Nat := 118140960795 + 3387100 * 2 ^ 59
def prefixEnd_3387100 : Nat := 4983230072969 + 3 ^ 40 * 3387100 * 2
def baseEnd_3387100 : Nat := 1739210324843803189373017

theorem tailTrace_3387100 : CollatzResearch.WordTrace tailWord_3387100 prefixEnd_3387100 1739210324843803189373017 := by
  unfold tailWord_3387100
  simp only [CollatzResearch.WordTrace]
  refine ⟨61768843014561322735355377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82358457352748430313807169 61768843014561322735355377)
  ·
    refine ⟨46326632260920992051516533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61768843014561322735355377 46326632260920992051516533)
    ·
      refine ⟨4343121774461343004829675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46326632260920992051516533 4343121774461343004829675)
      ·
        refine ⟨6514682661692014507244513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4343121774461343004829675 6514682661692014507244513)
        ·
          refine ⟨4886011996269010880433385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6514682661692014507244513 4886011996269010880433385)
          ·
            refine ⟨3664508997201758160325039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4886011996269010880433385 3664508997201758160325039)
            ·
              refine ⟨5496763495802637240487559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3664508997201758160325039 5496763495802637240487559)
              ·
                refine ⟨8245145243703955860731339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5496763495802637240487559 8245145243703955860731339)
                ·
                  refine ⟨12367717865555933791097009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8245145243703955860731339 12367717865555933791097009)
                  ·
                    refine ⟨9275788399166950343322757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12367717865555933791097009 9275788399166950343322757)
                    ·
                      refine ⟨1739210324843803189373017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9275788399166950343322757 1739210324843803189373017)
                      ·
                        rfl

theorem cell23_3387100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_3387100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3387100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3387100 prefixEnd_3387100 := by exact prefixLift 3387100
  have htrace : WordTrace (prefixWord ++ tailWord_3387100) baseStart_3387100 baseEnd_3387100 := by
    simpa [prefixWord, tailWord_3387100, baseEnd_3387100] using wordTrace_append hprefix tailTrace_3387100
  have hstable : (prefixWord ++ tailWord_3387100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3387100).length < 2 ^ (prefixWord ++ tailWord_3387100).sum := by decide
  have hdescent : baseEnd_3387100 < baseStart_3387100 := by decide
  rcases family_descends (prefixWord ++ tailWord_3387100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3387129 : List Nat := [1, 2, 1, 3, 1, 1, 1, 1, 3, 6, 3]
def baseStart_3387129 : Nat := 118140960795 + 3387129 * 2 ^ 59
def prefixEnd_3387129 : Nat := 4983230072969 + 3 ^ 40 * 3387129 * 2
def baseEnd_3387129 : Nat := 1739225215782783575910383

theorem tailTrace_3387129 : CollatzResearch.WordTrace tailWord_3387129 prefixEnd_3387129 1739225215782783575910383 := by
  unfold tailWord_3387129
  simp only [CollatzResearch.WordTrace]
  refine ⟨123538743746017583423516441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82359162497345055615677627 123538743746017583423516441)
  ·
    refine ⟨92654057809513187567637331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123538743746017583423516441 92654057809513187567637331)
    ·
      refine ⟨138981086714269781351455997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92654057809513187567637331 138981086714269781351455997)
      ·
        refine ⟨52117907517851168006795999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138981086714269781351455997 52117907517851168006795999)
        ·
          refine ⟨78176861276776752010193999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52117907517851168006795999 78176861276776752010193999)
          ·
            refine ⟨117265291915165128015290999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78176861276776752010193999 117265291915165128015290999)
            ·
              refine ⟨175897937872747692022936499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117265291915165128015290999 175897937872747692022936499)
              ·
                refine ⟨263846906809121538034404749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 175897937872747692022936499 263846906809121538034404749)
                ·
                  refine ⟨98942590053420576762901781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 263846906809121538034404749 98942590053420576762901781)
                  ·
                    refine ⟨4637933908754089535761021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 98942590053420576762901781 4637933908754089535761021)
                    ·
                      refine ⟨1739225215782783575910383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4637933908754089535761021 1739225215782783575910383)
                      ·
                        rfl

theorem cell23_3387129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 6, 3].length) (baseStart_3387129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3387129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3387129 prefixEnd_3387129 := by exact prefixLift 3387129
  have htrace : WordTrace (prefixWord ++ tailWord_3387129) baseStart_3387129 baseEnd_3387129 := by
    simpa [prefixWord, tailWord_3387129, baseEnd_3387129] using wordTrace_append hprefix tailTrace_3387129
  have hstable : (prefixWord ++ tailWord_3387129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3387129).length < 2 ^ (prefixWord ++ tailWord_3387129).sum := by decide
  have hdescent : baseEnd_3387129 < baseStart_3387129 := by decide
  rcases family_descends (prefixWord ++ tailWord_3387129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3387139 : List Nat := [1, 1, 1, 3, 2, 2, 2, 1, 4, 2, 4]
def baseStart_3387139 : Nat := 118140960795 + 3387139 * 2 ^ 59
def prefixEnd_3387139 : Nat := 4983230072969 + 3 ^ 40 * 3387139 * 2
def baseEnd_3387139 : Nat := 1739230350589328536785337

theorem tailTrace_3387139 : CollatzResearch.WordTrace tailWord_3387139 prefixEnd_3387139 1739230350589328536785337 := by
  unfold tailWord_3387139
  simp only [CollatzResearch.WordTrace]
  refine ⟨123539108475981355131380471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82359405650654236754253647 123539108475981355131380471)
  ·
    refine ⟨185308662713972032697070707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123539108475981355131380471 185308662713972032697070707)
    ·
      refine ⟨277962994070958049045606061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185308662713972032697070707 277962994070958049045606061)
      ·
        refine ⟨104236122776609268392102273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 277962994070958049045606061 104236122776609268392102273)
        ·
          refine ⟨78177092082456951294076705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104236122776609268392102273 78177092082456951294076705)
          ·
            refine ⟨58632819061842713470557529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78177092082456951294076705 58632819061842713470557529)
            ·
              refine ⟨43974614296382035102918147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58632819061842713470557529 43974614296382035102918147)
              ·
                refine ⟨65961921444573052654377221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43974614296382035102918147 65961921444573052654377221)
                ·
                  refine ⟨12367860270857447372695729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65961921444573052654377221 12367860270857447372695729)
                  ·
                    refine ⟨9275895203143085529521797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12367860270857447372695729 9275895203143085529521797)
                    ·
                      refine ⟨1739230350589328536785337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9275895203143085529521797 1739230350589328536785337)
                      ·
                        rfl

theorem cell23_3387139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 4, 2, 4].length) (baseStart_3387139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3387139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3387139 prefixEnd_3387139 := by exact prefixLift 3387139
  have htrace : WordTrace (prefixWord ++ tailWord_3387139) baseStart_3387139 baseEnd_3387139 := by
    simpa [prefixWord, tailWord_3387139, baseEnd_3387139] using wordTrace_append hprefix tailTrace_3387139
  have hstable : (prefixWord ++ tailWord_3387139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3387139).length < 2 ^ (prefixWord ++ tailWord_3387139).sum := by decide
  have hdescent : baseEnd_3387139 < baseStart_3387139 := by decide
  rcases family_descends (prefixWord ++ tailWord_3387139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3387154 : List Nat := [3, 2, 4, 1, 1, 3, 2, 1, 2, 1, 3]
def baseStart_3387154 : Nat := 118140960795 + 3387154 * 2 ^ 59
def prefixEnd_3387154 : Nat := 4983230072969 + 3 ^ 40 * 3387154 * 2
def baseEnd_3387154 : Nat := 1739238052799145978097769

theorem tailTrace_3387154 : CollatzResearch.WordTrace tailWord_3387154 prefixEnd_3387154 1739238052799145978097769 := by
  unfold tailWord_3387154
  simp only [CollatzResearch.WordTrace]
  refine ⟨30884913892731753173294129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82359770380618008462117677 30884913892731753173294129)
  ·
    refine ⟨23163685419548814879970597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30884913892731753173294129 23163685419548814879970597)
    ·
      refine ⟨4343191016165402789994487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23163685419548814879970597 4343191016165402789994487)
      ·
        refine ⟨6514786524248104184991731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4343191016165402789994487 6514786524248104184991731)
        ·
          refine ⟨9772179786372156277487597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6514786524248104184991731 9772179786372156277487597)
          ·
            refine ⟨3664567419889558604057849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9772179786372156277487597 3664567419889558604057849)
            ·
              refine ⟨2748425564917168953043387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3664567419889558604057849 2748425564917168953043387)
              ·
                refine ⟨4122638347375753429565081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2748425564917168953043387 4122638347375753429565081)
                ·
                  refine ⟨3091978760531815072173811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4122638347375753429565081 3091978760531815072173811)
                  ·
                    refine ⟨4637968140797722608260717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3091978760531815072173811 4637968140797722608260717)
                    ·
                      refine ⟨1739238052799145978097769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4637968140797722608260717 1739238052799145978097769)
                      ·
                        rfl

theorem cell23_3387154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 2, 1, 2, 1, 3].length) (baseStart_3387154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3387154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3387154 prefixEnd_3387154 := by exact prefixLift 3387154
  have htrace : WordTrace (prefixWord ++ tailWord_3387154) baseStart_3387154 baseEnd_3387154 := by
    simpa [prefixWord, tailWord_3387154, baseEnd_3387154] using wordTrace_append hprefix tailTrace_3387154
  have hstable : (prefixWord ++ tailWord_3387154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3387154).length < 2 ^ (prefixWord ++ tailWord_3387154).sum := by decide
  have hdescent : baseEnd_3387154 < baseStart_3387154 := by decide
  rcases family_descends (prefixWord ++ tailWord_3387154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3387196 : List Nat := [2, 2, 2, 2, 1, 1, 4, 2, 2, 5]
def baseStart_3387196 : Nat := 118140960795 + 3387196 * 2 ^ 59
def prefixEnd_3387196 : Nat := 4983230072969 + 3 ^ 40 * 3387196 * 2
def baseEnd_3387196 : Nat := 579753206328878271257525

theorem tailTrace_3387196 : CollatzResearch.WordTrace tailWord_3387196 prefixEnd_3387196 579753206328878271257525 := by
  unfold tailWord_3387196
  simp only [CollatzResearch.WordTrace]
  refine ⟨61770593718387426933102721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82360791624516569244136961 61770593718387426933102721)
  ·
    refine ⟨46327945288790570199827041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61770593718387426933102721 46327945288790570199827041)
    ·
      refine ⟨34745958966592927649870281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46327945288790570199827041 34745958966592927649870281)
      ·
        refine ⟨26059469224944695737402711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34745958966592927649870281 26059469224944695737402711)
        ·
          refine ⟨39089203837417043606104067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26059469224944695737402711 39089203837417043606104067)
          ·
            refine ⟨58633805756125565409156101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39089203837417043606104067 58633805756125565409156101)
            ·
              refine ⟨10993838579273543514216769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58633805756125565409156101 10993838579273543514216769)
              ·
                refine ⟨8245378934455157635662577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10993838579273543514216769 8245378934455157635662577)
                ·
                  refine ⟨6184034200841368226746933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8245378934455157635662577 6184034200841368226746933)
                  ·
                    refine ⟨579753206328878271257525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6184034200841368226746933 579753206328878271257525)
                    ·
                      rfl

theorem cell23_3387196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 2, 2, 5].length) (baseStart_3387196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3387196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3387196 prefixEnd_3387196 := by exact prefixLift 3387196
  have htrace : WordTrace (prefixWord ++ tailWord_3387196) baseStart_3387196 baseEnd_3387196 := by
    simpa [prefixWord, tailWord_3387196, baseEnd_3387196] using wordTrace_append hprefix tailTrace_3387196
  have hstable : (prefixWord ++ tailWord_3387196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3387196).length < 2 ^ (prefixWord ++ tailWord_3387196).sum := by decide
  have hdescent : baseEnd_3387196 < baseStart_3387196 := by decide
  rcases family_descends (prefixWord ++ tailWord_3387196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3387253 : List Nat := [1, 3, 4, 1, 1, 1, 2, 1, 4, 2, 3]
def baseStart_3387253 : Nat := 118140960795 + 3387253 * 2 ^ 59
def prefixEnd_3387253 : Nat := 4983230072969 + 3 ^ 40 * 3387253 * 2
def baseEnd_3387253 : Nat := 1739288887383941090759813

theorem tailTrace_3387253 : CollatzResearch.WordTrace tailWord_3387253 prefixEnd_3387253 1739288887383941090759813 := by
  unfold tailWord_3387253
  simp only [CollatzResearch.WordTrace]
  refine ⟨123543266397568352601030413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82362177598378901734020275 123543266397568352601030413)
  ·
    refine ⟨46328724899088132225386405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123543266397568352601030413 46328724899088132225386405)
    ·
      refine ⟨8686635918579024792259951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46328724899088132225386405 8686635918579024792259951)
      ·
        refine ⟨13029953877868537188389927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8686635918579024792259951 13029953877868537188389927)
        ·
          refine ⟨19544930816802805782584891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13029953877868537188389927 19544930816802805782584891)
          ·
            refine ⟨29317396225204208673877337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19544930816802805782584891 29317396225204208673877337)
            ·
              refine ⟨21988047168903156505408003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29317396225204208673877337 21988047168903156505408003)
              ·
                refine ⟨32982070753354734758112005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21988047168903156505408003 32982070753354734758112005)
                ·
                  refine ⟨6184138266254012767146001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32982070753354734758112005 6184138266254012767146001)
                  ·
                    refine ⟨4638103699690509575359501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6184138266254012767146001 4638103699690509575359501)
                    ·
                      refine ⟨1739288887383941090759813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4638103699690509575359501 1739288887383941090759813)
                      ·
                        rfl

theorem cell23_3387253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 1, 4, 2, 3].length) (baseStart_3387253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3387253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3387253 prefixEnd_3387253 := by exact prefixLift 3387253
  have htrace : WordTrace (prefixWord ++ tailWord_3387253) baseStart_3387253 baseEnd_3387253 := by
    simpa [prefixWord, tailWord_3387253, baseEnd_3387253] using wordTrace_append hprefix tailTrace_3387253
  have hstable : (prefixWord ++ tailWord_3387253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3387253).length < 2 ^ (prefixWord ++ tailWord_3387253).sum := by decide
  have hdescent : baseEnd_3387253 < baseStart_3387253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3387253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3387273 : List Nat := [1, 2, 1, 1, 5, 1, 5, 1, 6]
def baseStart_3387273 : Nat := 118140960795 + 3387273 * 2 ^ 59
def prefixEnd_3387273 : Nat := 4983230072969 + 3 ^ 40 * 3387273 * 2
def baseEnd_3387273 : Nat := 193255461888559001389969

theorem tailTrace_3387273 : CollatzResearch.WordTrace tailWord_3387273 prefixEnd_3387273 193255461888559001389969 := by
  unfold tailWord_3387273
  simp only [CollatzResearch.WordTrace]
  refine ⟨123543995857495896016758473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82362663904997264011172315 123543995857495896016758473)
  ·
    refine ⟨92657996893121922012568855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123543995857495896016758473 92657996893121922012568855)
    ·
      refine ⟨138986995339682883018853283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92657996893121922012568855 138986995339682883018853283)
      ·
        refine ⟨208480493009524324528279925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138986995339682883018853283 208480493009524324528279925)
        ·
          refine ⟨19545046219642905424526243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 208480493009524324528279925 19545046219642905424526243)
          ·
            refine ⟨29317569329464358136789365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19545046219642905424526243 29317569329464358136789365)
            ·
              refine ⟨2748522124637283575324003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29317569329464358136789365 2748522124637283575324003)
              ·
                refine ⟨4122783186955925362986005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2748522124637283575324003 4122783186955925362986005)
                ·
                  refine ⟨193255461888559001389969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4122783186955925362986005 193255461888559001389969)
                  ·
                    rfl

theorem cell23_3387273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 5, 1, 6].length) (baseStart_3387273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3387273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3387273 prefixEnd_3387273 := by exact prefixLift 3387273
  have htrace : WordTrace (prefixWord ++ tailWord_3387273) baseStart_3387273 baseEnd_3387273 := by
    simpa [prefixWord, tailWord_3387273, baseEnd_3387273] using wordTrace_append hprefix tailTrace_3387273
  have hstable : (prefixWord ++ tailWord_3387273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3387273).length < 2 ^ (prefixWord ++ tailWord_3387273).sum := by decide
  have hdescent : baseEnd_3387273 < baseStart_3387273 := by decide
  rcases family_descends (prefixWord ++ tailWord_3387273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3387317 : List Nat := [1, 3, 3, 2, 1, 4, 1, 1, 3, 1, 3]
def baseStart_3387317 : Nat := 118140960795 + 3387317 * 2 ^ 59
def prefixEnd_3387317 : Nat := 4983230072969 + 3 ^ 40 * 3387317 * 2
def baseEnd_3387317 : Nat := 1739321750145828840359519

theorem tailTrace_3387317 : CollatzResearch.WordTrace tailWord_3387317 prefixEnd_3387317 1739321750145828840359519 := by
  unfold tailWord_3387317
  simp only [CollatzResearch.WordTrace]
  refine ⟨123545600669336491531360205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82363733779557661020906803 123545600669336491531360205)
  ·
    refine ⟨46329600251001184324260077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123545600669336491531360205 46329600251001184324260077)
    ·
      refine ⟨17373600094125444121597529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46329600251001184324260077 17373600094125444121597529)
      ·
        refine ⟨13030200070594083091198147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17373600094125444121597529 13030200070594083091198147)
        ·
          refine ⟨19545300105891124636797221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13030200070594083091198147 19545300105891124636797221)
          ·
            refine ⟨3664743769854585869399479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19545300105891124636797221 3664743769854585869399479)
            ·
              refine ⟨5497115654781878804099219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3664743769854585869399479 5497115654781878804099219)
              ·
                refine ⟨8245673482172818206148829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5497115654781878804099219 8245673482172818206148829)
                ·
                  refine ⟨3092127555814806827305811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8245673482172818206148829 3092127555814806827305811)
                  ·
                    refine ⟨4638191333722210240958717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3092127555814806827305811 4638191333722210240958717)
                    ·
                      refine ⟨1739321750145828840359519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4638191333722210240958717 1739321750145828840359519)
                      ·
                        rfl

theorem cell23_3387317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 1, 1, 3, 1, 3].length) (baseStart_3387317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3387317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3387317 prefixEnd_3387317 := by exact prefixLift 3387317
  have htrace : WordTrace (prefixWord ++ tailWord_3387317) baseStart_3387317 baseEnd_3387317 := by
    simpa [prefixWord, tailWord_3387317, baseEnd_3387317] using wordTrace_append hprefix tailTrace_3387317
  have hstable : (prefixWord ++ tailWord_3387317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3387317).length < 2 ^ (prefixWord ++ tailWord_3387317).sum := by decide
  have hdescent : baseEnd_3387317 < baseStart_3387317 := by decide
  rcases family_descends (prefixWord ++ tailWord_3387317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3387324 : List Nat := [2, 2, 2, 5, 2, 1, 2, 1, 6]
def baseStart_3387324 : Nat := 118140960795 + 3387324 * 2 ^ 59
def prefixEnd_3387324 : Nat := 4983230072969 + 3 ^ 40 * 3387324 * 2
def baseEnd_3387324 : Nat := 193258371612267812552443

theorem tailTrace_3387324 : CollatzResearch.WordTrace tailWord_3387324 prefixEnd_3387324 193258371612267812552443 := by
  unfold tailWord_3387324
  simp only [CollatzResearch.WordTrace]
  refine ⟨61772927990155565863432513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82363903986874087817910017 61772927990155565863432513)
  ·
    refine ⟨46329695992616674397574385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61772927990155565863432513 46329695992616674397574385)
    ·
      refine ⟨34747271994462505798180789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46329695992616674397574385 34747271994462505798180789)
      ·
        refine ⟨3257556749480859918579449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34747271994462505798180789 3257556749480859918579449)
        ·
          refine ⟨2443167562110644938934587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3257556749480859918579449 2443167562110644938934587)
          ·
            refine ⟨3664751343165967408401881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2443167562110644938934587 3664751343165967408401881)
            ·
              refine ⟨2748563507374475556301411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3664751343165967408401881 2748563507374475556301411)
              ·
                refine ⟨4122845261061713334452117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2748563507374475556301411 4122845261061713334452117)
                ·
                  refine ⟨193258371612267812552443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4122845261061713334452117 193258371612267812552443)
                  ·
                    rfl

theorem cell23_3387324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 2, 1, 6].length) (baseStart_3387324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3387324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3387324 prefixEnd_3387324 := by exact prefixLift 3387324
  have htrace : WordTrace (prefixWord ++ tailWord_3387324) baseStart_3387324 baseEnd_3387324 := by
    simpa [prefixWord, tailWord_3387324, baseEnd_3387324] using wordTrace_append hprefix tailTrace_3387324
  have hstable : (prefixWord ++ tailWord_3387324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3387324).length < 2 ^ (prefixWord ++ tailWord_3387324).sum := by decide
  have hdescent : baseEnd_3387324 < baseStart_3387324 := by decide
  rcases family_descends (prefixWord ++ tailWord_3387324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3387340 : List Nat := [2, 2, 1, 4, 1, 2, 3, 2, 1, 1, 4]
def baseStart_3387340 : Nat := 118140960795 + 3387340 * 2 ^ 59
def prefixEnd_3387340 : Nat := 4983230072969 + 3 ^ 40 * 3387340 * 2
def baseEnd_3387340 : Nat := 1739333560200882250371913

theorem tailTrace_3387340 : CollatzResearch.WordTrace tailWord_3387340 prefixEnd_3387340 1739333560200882250371913 := by
  unfold tailWord_3387340
  simp only [CollatzResearch.WordTrace]
  refine ⟨61773219774126583229723737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82364293032168777639631649 61773219774126583229723737)
  ·
    refine ⟨46329914830594937422292803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61773219774126583229723737 46329914830594937422292803)
    ·
      refine ⟨69494872245892406133439205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46329914830594937422292803 69494872245892406133439205)
      ·
        refine ⟨13030288546104826150019851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69494872245892406133439205 13030288546104826150019851)
        ·
          refine ⟨19545432819157239225029777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13030288546104826150019851 19545432819157239225029777)
          ·
            refine ⟨14659074614367929418772333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19545432819157239225029777 14659074614367929418772333)
            ·
              refine ⟨5497152980387973532039625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14659074614367929418772333 5497152980387973532039625)
              ·
                refine ⟨4122864735290980149029719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5497152980387973532039625 4122864735290980149029719)
                ·
                  refine ⟨6184297102936470223544579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4122864735290980149029719 6184297102936470223544579)
                  ·
                    refine ⟨9276445654404705335316869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6184297102936470223544579 9276445654404705335316869)
                    ·
                      refine ⟨1739333560200882250371913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9276445654404705335316869 1739333560200882250371913)
                      ·
                        rfl

theorem cell23_3387340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 3, 2, 1, 1, 4].length) (baseStart_3387340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3387340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3387340 prefixEnd_3387340 := by exact prefixLift 3387340
  have htrace : WordTrace (prefixWord ++ tailWord_3387340) baseStart_3387340 baseEnd_3387340 := by
    simpa [prefixWord, tailWord_3387340, baseEnd_3387340] using wordTrace_append hprefix tailTrace_3387340
  have hstable : (prefixWord ++ tailWord_3387340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3387340).length < 2 ^ (prefixWord ++ tailWord_3387340).sum := by decide
  have hdescent : baseEnd_3387340 < baseStart_3387340 := by decide
  rcases family_descends (prefixWord ++ tailWord_3387340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3387343 : List Nat := [1, 1, 2, 1, 1, 5, 3, 1, 3, 2, 3]
def baseStart_3387343 : Nat := 118140960795 + 3387343 * 2 ^ 59
def prefixEnd_3387343 : Nat := 4983230072969 + 3 ^ 40 * 3387343 * 2
def baseEnd_3387343 : Nat := 1739335100642845738634399

theorem tailTrace_3387343 : CollatzResearch.WordTrace tailWord_3387343 prefixEnd_3387343 1739335100642845738634399 := by
  unfold tailWord_3387343
  simp only [CollatzResearch.WordTrace]
  refine ⟨123546548967242297971806683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82364365978161531981204455 123546548967242297971806683)
  ·
    refine ⟨185319823450863446957710025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123546548967242297971806683 185319823450863446957710025)
    ·
      refine ⟨138989867588147585218282519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185319823450863446957710025 138989867588147585218282519)
      ·
        refine ⟨208484801382221377827423779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138989867588147585218282519 208484801382221377827423779)
        ·
          refine ⟨312727202073332066741135669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208484801382221377827423779 312727202073332066741135669)
          ·
            refine ⟨29318175194374881256981469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 312727202073332066741135669 29318175194374881256981469)
            ·
              refine ⟨10994315697890580471368051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29318175194374881256981469 10994315697890580471368051)
              ·
                refine ⟨16491473546835870707052077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10994315697890580471368051 16491473546835870707052077)
                ·
                  refine ⟨6184302580063451515144529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16491473546835870707052077 6184302580063451515144529)
                  ·
                    refine ⟨4638226935047588636358397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6184302580063451515144529 4638226935047588636358397)
                    ·
                      refine ⟨1739335100642845738634399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4638226935047588636358397 1739335100642845738634399)
                      ·
                        rfl

theorem cell23_3387343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 1, 3, 2, 3].length) (baseStart_3387343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3387343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3387343 prefixEnd_3387343 := by exact prefixLift 3387343
  have htrace : WordTrace (prefixWord ++ tailWord_3387343) baseStart_3387343 baseEnd_3387343 := by
    simpa [prefixWord, tailWord_3387343, baseEnd_3387343] using wordTrace_append hprefix tailTrace_3387343
  have hstable : (prefixWord ++ tailWord_3387343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3387343).length < 2 ^ (prefixWord ++ tailWord_3387343).sum := by decide
  have hdescent : baseEnd_3387343 < baseStart_3387343 := by decide
  rcases family_descends (prefixWord ++ tailWord_3387343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3387367 : List Nat := [1, 1, 5, 2, 3, 1, 2, 2, 2, 4]
def baseStart_3387367 : Nat := 118140960795 + 3387367 * 2 ^ 59
def prefixEnd_3387367 : Nat := 4983230072969 + 3 ^ 40 * 3387367 * 2
def baseEnd_3387367 : Nat := 579782474726184548244763

theorem tailTrace_3387367 : CollatzResearch.WordTrace tailWord_3387367 prefixEnd_3387367 579782474726184548244763 := by
  unfold tailWord_3387367
  simp only [CollatzResearch.WordTrace]
  refine ⟨123547424319155350070680355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82364949546103566713786903 123547424319155350070680355)
  ·
    refine ⟨185321136478733025106020533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123547424319155350070680355 185321136478733025106020533)
    ·
      refine ⟨17373856544881221103689425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 185321136478733025106020533 17373856544881221103689425)
      ·
        refine ⟨13030392408660915827767069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17373856544881221103689425 13030392408660915827767069)
        ·
          refine ⟨4886397153247843435412651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13030392408660915827767069 4886397153247843435412651)
          ·
            refine ⟨7329595729871765153118977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4886397153247843435412651 7329595729871765153118977)
            ·
              refine ⟨5497196797403823864839233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7329595729871765153118977 5497196797403823864839233)
              ·
                refine ⟨4122897598052867898629425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5497196797403823864839233 4122897598052867898629425)
                ·
                  refine ⟨3092173198539650923972069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4122897598052867898629425 3092173198539650923972069)
                  ·
                    refine ⟨579782474726184548244763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3092173198539650923972069 579782474726184548244763)
                    ·
                      rfl

theorem cell23_3387367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 2, 2, 2, 4].length) (baseStart_3387367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3387367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3387367 prefixEnd_3387367 := by exact prefixLift 3387367
  have htrace : WordTrace (prefixWord ++ tailWord_3387367) baseStart_3387367 baseEnd_3387367 := by
    simpa [prefixWord, tailWord_3387367, baseEnd_3387367] using wordTrace_append hprefix tailTrace_3387367
  have hstable : (prefixWord ++ tailWord_3387367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3387367).length < 2 ^ (prefixWord ++ tailWord_3387367).sum := by decide
  have hdescent : baseEnd_3387367 < baseStart_3387367 := by decide
  rcases family_descends (prefixWord ++ tailWord_3387367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3387376 : List Nat := [2, 1, 1, 1, 3, 2, 3, 1, 2, 7]
def baseStart_3387376 : Nat := 118140960795 + 3387376 * 2 ^ 59
def prefixEnd_3387376 : Nat := 4983230072969 + 3 ^ 40 * 3387376 * 2
def baseEnd_3387376 : Nat := 579784015168148036507249

theorem tailTrace_3387376 : CollatzResearch.WordTrace tailWord_3387376 prefixEnd_3387376 579784015168148036507249 := by
  unfold tailWord_3387376
  simp only [CollatzResearch.WordTrace]
  refine ⟨61773876288061372303878991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82365168384081829738505321 61773876288061372303878991)
  ·
    refine ⟨92660814432092058455818487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61773876288061372303878991 92660814432092058455818487)
    ·
      refine ⟨138991221648138087683727731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92660814432092058455818487 138991221648138087683727731)
      ·
        refine ⟨208486832472207131525591597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138991221648138087683727731 208486832472207131525591597)
        ·
          refine ⟨78182562177077674322096849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 208486832472207131525591597 78182562177077674322096849)
          ·
            refine ⟨58636921632808255741572637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78182562177077674322096849 58636921632808255741572637)
            ·
              refine ⟨21988845612303095903089739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58636921632808255741572637 21988845612303095903089739)
              ·
                refine ⟨32983268418454643854634609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21988845612303095903089739 32983268418454643854634609)
                ·
                  refine ⟨24737451313840982890975957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32983268418454643854634609 24737451313840982890975957)
                  ·
                    refine ⟨579784015168148036507249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24737451313840982890975957 579784015168148036507249)
                    ·
                      rfl

theorem cell23_3387376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 1, 2, 7].length) (baseStart_3387376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3387376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3387376 prefixEnd_3387376 := by exact prefixLift 3387376
  have htrace : WordTrace (prefixWord ++ tailWord_3387376) baseStart_3387376 baseEnd_3387376 := by
    simpa [prefixWord, tailWord_3387376, baseEnd_3387376] using wordTrace_append hprefix tailTrace_3387376
  have hstable : (prefixWord ++ tailWord_3387376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3387376).length < 2 ^ (prefixWord ++ tailWord_3387376).sum := by decide
  have hdescent : baseEnd_3387376 < baseStart_3387376 := by decide
  rcases family_descends (prefixWord ++ tailWord_3387376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3387386 : List Nat := [3, 1, 1, 1, 1, 2, 1, 1, 3, 4, 5]
def baseStart_3387386 : Nat := 118140960795 + 3387386 * 2 ^ 59
def prefixEnd_3387386 : Nat := 4983230072969 + 3 ^ 40 * 3387386 * 2
def baseEnd_3387386 : Nat := 1739357180310989070396701

theorem tailTrace_3387386 : CollatzResearch.WordTrace tailWord_3387386 prefixEnd_3387386 1739357180310989070396701 := by
  unfold tailWord_3387386
  simp only [CollatzResearch.WordTrace]
  refine ⟨30887029326521629078905503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82365411537391010877081341 30887029326521629078905503)
  ·
    refine ⟨46330543989782443618358255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30887029326521629078905503 46330543989782443618358255)
    ·
      refine ⟨69495815984673665427537383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46330543989782443618358255 69495815984673665427537383)
      ·
        refine ⟨104243723977010498141306075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69495815984673665427537383 104243723977010498141306075)
        ·
          refine ⟨156365585965515747211959113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104243723977010498141306075 156365585965515747211959113)
          ·
            refine ⟨117274189474136810408969335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156365585965515747211959113 117274189474136810408969335)
            ·
              refine ⟨175911284211205215613454003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117274189474136810408969335 175911284211205215613454003)
              ·
                refine ⟨263866926316807823420181005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 175911284211205215613454003 263866926316807823420181005)
                ·
                  refine ⟨98950097368802933782567877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 263866926316807823420181005 98950097368802933782567877)
                  ·
                    refine ⟨18553143256650550084231477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 98950097368802933782567877 18553143256650550084231477)
                    ·
                      refine ⟨1739357180310989070396701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18553143256650550084231477 1739357180310989070396701)
                      ·
                        rfl

theorem cell23_3387386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 3, 4, 5].length) (baseStart_3387386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3387386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3387386 prefixEnd_3387386 := by exact prefixLift 3387386
  have htrace : WordTrace (prefixWord ++ tailWord_3387386) baseStart_3387386 baseEnd_3387386 := by
    simpa [prefixWord, tailWord_3387386, baseEnd_3387386] using wordTrace_append hprefix tailTrace_3387386
  have hstable : (prefixWord ++ tailWord_3387386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3387386).length < 2 ^ (prefixWord ++ tailWord_3387386).sum := by decide
  have hdescent : baseEnd_3387386 < baseStart_3387386 := by decide
  rcases family_descends (prefixWord ++ tailWord_3387386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3387400 : List Nat := [2, 1, 3, 2, 1, 2, 1, 3, 3, 3, 2]
def baseStart_3387400 : Nat := 118140960795 + 3387400 * 2 ^ 59
def prefixEnd_3387400 : Nat := 4983230072969 + 3 ^ 40 * 3387400 * 2
def baseEnd_3387400 : Nat := 1739364369040152015621637

theorem tailTrace_3387400 : CollatzResearch.WordTrace tailWord_3387400 prefixEnd_3387400 1739364369040152015621637 := by
  unfold tailWord_3387400
  simp only [CollatzResearch.WordTrace]
  refine ⟨61774313964017898353315827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82365751952023864471087769 61774313964017898353315827)
  ·
    refine ⟨92661470946026847529973741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61774313964017898353315827 92661470946026847529973741)
    ·
      refine ⟨34748051604760067823740153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92661470946026847529973741 34748051604760067823740153)
      ·
        refine ⟨26061038703570050867805115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34748051604760067823740153 26061038703570050867805115)
        ·
          refine ⟨39091558055355076301707673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26061038703570050867805115 39091558055355076301707673)
          ·
            refine ⟨29318668541516307226280755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39091558055355076301707673 29318668541516307226280755)
            ·
              refine ⟨43978002812274460839421133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29318668541516307226280755 43978002812274460839421133)
              ·
                refine ⟨16491751054602922814782925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43978002812274460839421133 16491751054602922814782925)
                ·
                  refine ⟨6184406645476096055543597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16491751054602922814782925 6184406645476096055543597)
                  ·
                    refine ⟨2319152492053536020828849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6184406645476096055543597 2319152492053536020828849)
                    ·
                      refine ⟨1739364369040152015621637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2319152492053536020828849 1739364369040152015621637)
                      ·
                        rfl

theorem cell23_3387400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 3, 3, 3, 2].length) (baseStart_3387400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3387400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3387400 prefixEnd_3387400 := by exact prefixLift 3387400
  have htrace : WordTrace (prefixWord ++ tailWord_3387400) baseStart_3387400 baseEnd_3387400 := by
    simpa [prefixWord, tailWord_3387400, baseEnd_3387400] using wordTrace_append hprefix tailTrace_3387400
  have hstable : (prefixWord ++ tailWord_3387400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3387400).length < 2 ^ (prefixWord ++ tailWord_3387400).sum := by decide
  have hdescent : baseEnd_3387400 < baseStart_3387400 := by decide
  rcases family_descends (prefixWord ++ tailWord_3387400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3387443 : List Nat := [1, 1, 1, 2, 4, 1, 4, 1, 2, 2, 4]
def baseStart_3387443 : Nat := 118140960795 + 3387443 * 2 ^ 59
def prefixEnd_3387443 : Nat := 4983230072969 + 3 ^ 40 * 3387443 * 2
def baseEnd_3387443 : Nat := 1739386448708295347383939

theorem tailTrace_3387443 : CollatzResearch.WordTrace tailWord_3387443 prefixEnd_3387443 1739386448708295347383939 := by
  unfold tailWord_3387443
  simp only [CollatzResearch.WordTrace]
  refine ⟨123550196266880015050446983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82366797511253343366964655 123550196266880015050446983)
  ·
    refine ⟨185325294400320022575670475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123550196266880015050446983 185325294400320022575670475)
    ·
      refine ⟨277987941600480033863505713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185325294400320022575670475 277987941600480033863505713)
      ·
        refine ⟨208490956200360025397629285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 277987941600480033863505713 208490956200360025397629285)
        ·
          refine ⟨39092054287567504762055491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 208490956200360025397629285 39092054287567504762055491)
          ·
            refine ⟨58638081431351257143083237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39092054287567504762055491 58638081431351257143083237)
            ·
              refine ⟨10994640268378360714328107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58638081431351257143083237 10994640268378360714328107)
              ·
                refine ⟨16491960402567541071492161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10994640268378360714328107 16491960402567541071492161)
                ·
                  refine ⟨12368970301925655803619121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16491960402567541071492161 12368970301925655803619121)
                  ·
                    refine ⟨9276727726444241852714341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12368970301925655803619121 9276727726444241852714341)
                    ·
                      refine ⟨1739386448708295347383939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9276727726444241852714341 1739386448708295347383939)
                      ·
                        rfl

theorem cell23_3387443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 1, 2, 2, 4].length) (baseStart_3387443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3387443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3387443 prefixEnd_3387443 := by exact prefixLift 3387443
  have htrace : WordTrace (prefixWord ++ tailWord_3387443) baseStart_3387443 baseEnd_3387443 := by
    simpa [prefixWord, tailWord_3387443, baseEnd_3387443] using wordTrace_append hprefix tailTrace_3387443
  have hstable : (prefixWord ++ tailWord_3387443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3387443).length < 2 ^ (prefixWord ++ tailWord_3387443).sum := by decide
  have hdescent : baseEnd_3387443 < baseStart_3387443 := by decide
  rcases family_descends (prefixWord ++ tailWord_3387443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3387447 : List Nat := [1, 1, 3, 1, 2, 2, 2, 5, 2, 2, 2]
def baseStart_3387447 : Nat := 118140960795 + 3387447 * 2 ^ 59
def prefixEnd_3387447 : Nat := 4983230072969 + 3 ^ 40 * 3387447 * 2
def baseEnd_3387447 : Nat := 1739388502630913331733921

theorem tailTrace_3387447 : CollatzResearch.WordTrace tailWord_3387447 prefixEnd_3387447 1739388502630913331733921 := by
  unfold tailWord_3387447
  simp only [CollatzResearch.WordTrace]
  refine ⟨123550342158865523733592595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82366894772577015822395063 123550342158865523733592595)
  ·
    refine ⟨185325513238298285600388893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123550342158865523733592595 185325513238298285600388893)
    ·
      refine ⟨69497067464361857100145835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185325513238298285600388893 69497067464361857100145835)
      ·
        refine ⟨104245601196542785650218753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69497067464361857100145835 104245601196542785650218753)
        ·
          refine ⟨78184200897407089237664065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104245601196542785650218753 78184200897407089237664065)
          ·
            refine ⟨58638150673055316928248049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78184200897407089237664065 58638150673055316928248049)
            ·
              refine ⟨43978613004791487696186037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58638150673055316928248049 43978613004791487696186037)
              ·
                refine ⟨4122994969199201971517441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43978613004791487696186037 4122994969199201971517441)
                ·
                  refine ⟨3092246226899401478638081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4122994969199201971517441 3092246226899401478638081)
                  ·
                    refine ⟨2319184670174551108978561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3092246226899401478638081 2319184670174551108978561)
                    ·
                      refine ⟨1739388502630913331733921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2319184670174551108978561 1739388502630913331733921)
                      ·
                        rfl

theorem cell23_3387447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 5, 2, 2, 2].length) (baseStart_3387447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3387447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3387447 prefixEnd_3387447 := by exact prefixLift 3387447
  have htrace : WordTrace (prefixWord ++ tailWord_3387447) baseStart_3387447 baseEnd_3387447 := by
    simpa [prefixWord, tailWord_3387447, baseEnd_3387447] using wordTrace_append hprefix tailTrace_3387447
  have hstable : (prefixWord ++ tailWord_3387447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3387447).length < 2 ^ (prefixWord ++ tailWord_3387447).sum := by decide
  have hdescent : baseEnd_3387447 < baseStart_3387447 := by decide
  rcases family_descends (prefixWord ++ tailWord_3387447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3387453 : List Nat := [1, 4, 1, 3, 1, 1, 1, 4, 7]
def baseStart_3387453 : Nat := 118140960795 + 3387453 * 2 ^ 59
def prefixEnd_3387453 : Nat := 4983230072969 + 3 ^ 40 * 3387453 * 2
def baseEnd_3387453 : Nat := 193265731501648923139877

theorem tailTrace_3387453 : CollatzResearch.WordTrace tailWord_3387453 prefixEnd_3387453 193265731501648923139877 := by
  unfold tailWord_3387453
  simp only [CollatzResearch.WordTrace]
  refine ⟨123550560996843786758311013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82367040664562524505540675 123550560996843786758311013)
  ·
    refine ⟨23165730186908210017183315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123550560996843786758311013 23165730186908210017183315)
    ·
      refine ⟨34748595280362315025774973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23165730186908210017183315 34748595280362315025774973)
      ·
        refine ⟨13030723230135868134665615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34748595280362315025774973 13030723230135868134665615)
        ·
          refine ⟨19546084845203802201998423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13030723230135868134665615 19546084845203802201998423)
          ·
            refine ⟨29319127267805703302997635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19546084845203802201998423 29319127267805703302997635)
            ·
              refine ⟨43978690901708554954496453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29319127267805703302997635 43978690901708554954496453)
              ·
                refine ⟨8246004544070354053968085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43978690901708554954496453 8246004544070354053968085)
                ·
                  refine ⟨193265731501648923139877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8246004544070354053968085 193265731501648923139877)
                  ·
                    rfl

theorem cell23_3387453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 4, 7].length) (baseStart_3387453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3387453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3387453 prefixEnd_3387453 := by exact prefixLift 3387453
  have htrace : WordTrace (prefixWord ++ tailWord_3387453) baseStart_3387453 baseEnd_3387453 := by
    simpa [prefixWord, tailWord_3387453, baseEnd_3387453] using wordTrace_append hprefix tailTrace_3387453
  have hstable : (prefixWord ++ tailWord_3387453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3387453).length < 2 ^ (prefixWord ++ tailWord_3387453).sum := by decide
  have hdescent : baseEnd_3387453 < baseStart_3387453 := by decide
  rcases family_descends (prefixWord ++ tailWord_3387453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3387493 : List Nat := [1, 3, 1, 3, 2, 2, 1, 1, 1, 1, 7]
def baseStart_3387493 : Nat := 118140960795 + 3387493 * 2 ^ 59
def prefixEnd_3387493 : Nat := 4983230072969 + 3 ^ 40 * 3387493 * 2
def baseEnd_3387493 : Nat := 1739412122741020151758709

theorem tailTrace_3387493 : CollatzResearch.WordTrace tailWord_3387493 prefixEnd_3387493 1739412122741020151758709 := by
  unfold tailWord_3387493
  simp only [CollatzResearch.WordTrace]
  refine ⟨123552019916698873589767133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82368013277799249059844755 123552019916698873589767133)
  ·
    refine ⟨46332007468762077596162675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123552019916698873589767133 46332007468762077596162675)
    ·
      refine ⟨69498011203143116394244013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46332007468762077596162675 69498011203143116394244013)
      ·
        refine ⟨26061754201178668647841505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69498011203143116394244013 26061754201178668647841505)
        ·
          refine ⟨19546315650884001485881129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26061754201178668647841505 19546315650884001485881129)
          ·
            refine ⟨14659736738163001114410847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19546315650884001485881129 14659736738163001114410847)
            ·
              refine ⟨21989605107244501671616271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14659736738163001114410847 21989605107244501671616271)
              ·
                refine ⟨32984407660866752507424407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21989605107244501671616271 32984407660866752507424407)
                ·
                  refine ⟨49476611491300128761136611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32984407660866752507424407 49476611491300128761136611)
                  ·
                    refine ⟨74214917236950193141704917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49476611491300128761136611 74214917236950193141704917)
                    ·
                      refine ⟨1739412122741020151758709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 74214917236950193141704917 1739412122741020151758709)
                      ·
                        rfl

theorem cell23_3387493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 1, 1, 1, 7].length) (baseStart_3387493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3387493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3387493 prefixEnd_3387493 := by exact prefixLift 3387493
  have htrace : WordTrace (prefixWord ++ tailWord_3387493) baseStart_3387493 baseEnd_3387493 := by
    simpa [prefixWord, tailWord_3387493, baseEnd_3387493] using wordTrace_append hprefix tailTrace_3387493
  have hstable : (prefixWord ++ tailWord_3387493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3387493).length < 2 ^ (prefixWord ++ tailWord_3387493).sum := by decide
  have hdescent : baseEnd_3387493 < baseStart_3387493 := by decide
  rcases family_descends (prefixWord ++ tailWord_3387493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3387498 : List Nat := [3, 1, 3, 2, 3, 2, 2, 1, 2, 2, 2]
def baseStart_3387498 : Nat := 118140960795 + 3387498 * 2 ^ 59
def prefixEnd_3387498 : Nat := 4983230072969 + 3 ^ 40 * 3387498 * 2
def baseEnd_3387498 : Nat := 1739414690144292632196187

theorem tailTrace_3387498 : CollatzResearch.WordTrace tailWord_3387498 prefixEnd_3387498 1739414690144292632196187 := by
  unfold tailWord_3387498
  simp only [CollatzResearch.WordTrace]
  refine ⟨30888050570420189860924787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82368134854453839629132765 30888050570420189860924787)
  ·
    refine ⟨46332075855630284791387181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30888050570420189860924787 46332075855630284791387181)
    ·
      refine ⟨17374528445861356796770193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46332075855630284791387181 17374528445861356796770193)
      ·
        refine ⟨13030896334396017597577645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17374528445861356796770193 13030896334396017597577645)
        ·
          refine ⟨4886586125398506599091617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13030896334396017597577645 4886586125398506599091617)
          ·
            refine ⟨3664939594048879949318713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4886586125398506599091617 3664939594048879949318713)
            ·
              refine ⟨2748704695536659961989035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3664939594048879949318713 2748704695536659961989035)
              ·
                refine ⟨4123057043304989942983553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2748704695536659961989035 4123057043304989942983553)
                ·
                  refine ⟨3092292782478742457237665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4123057043304989942983553 3092292782478742457237665)
                  ·
                    refine ⟨2319219586859056842928249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3092292782478742457237665 2319219586859056842928249)
                    ·
                      refine ⟨1739414690144292632196187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2319219586859056842928249 1739414690144292632196187)
                      ·
                        rfl

theorem cell23_3387498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 2, 1, 2, 2, 2].length) (baseStart_3387498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3387498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3387498 prefixEnd_3387498 := by exact prefixLift 3387498
  have htrace : WordTrace (prefixWord ++ tailWord_3387498) baseStart_3387498 baseEnd_3387498 := by
    simpa [prefixWord, tailWord_3387498, baseEnd_3387498] using wordTrace_append hprefix tailTrace_3387498
  have hstable : (prefixWord ++ tailWord_3387498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3387498).length < 2 ^ (prefixWord ++ tailWord_3387498).sum := by decide
  have hdescent : baseEnd_3387498 < baseStart_3387498 := by decide
  rcases family_descends (prefixWord ++ tailWord_3387498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3387520 : List Nat := [2, 1, 1, 2, 1, 3, 1, 2, 4, 4, 2]
def baseStart_3387520 : Nat := 118140960795 + 3387520 * 2 ^ 59
def prefixEnd_3387520 : Nat := 4983230072969 + 3 ^ 40 * 3387520 * 2
def baseEnd_3387520 : Nat := 1739425986718691546121085

theorem tailTrace_3387520 : CollatzResearch.WordTrace tailWord_3387520 prefixEnd_3387520 1739425986718691546121085 := by
  unfold tailWord_3387520
  simp only [CollatzResearch.WordTrace]
  refine ⟨61776502343800528600500007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82368669791734038134000009 61776502343800528600500007)
  ·
    refine ⟨92664753515700792900750011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61776502343800528600500007 92664753515700792900750011)
    ·
      refine ⟨138997130273551189351125017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92664753515700792900750011 138997130273551189351125017)
      ·
        refine ⟨104247847705163392013343763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138997130273551189351125017 104247847705163392013343763)
        ·
          refine ⟨156371771557745088020015645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104247847705163392013343763 156371771557745088020015645)
          ·
            refine ⟨58639414334154408007505867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 156371771557745088020015645 58639414334154408007505867)
            ·
              refine ⟨87959121501231612011258801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58639414334154408007505867 87959121501231612011258801)
              ·
                refine ⟨65969341125923709008444101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87959121501231612011258801 65969341125923709008444101)
                ·
                  refine ⟨12369251461110695439083269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65969341125923709008444101 12369251461110695439083269)
                  ·
                    refine ⟨2319234648958255394828113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12369251461110695439083269 2319234648958255394828113)
                    ·
                      refine ⟨1739425986718691546121085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2319234648958255394828113 1739425986718691546121085)
                      ·
                        rfl

theorem cell23_3387520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 4, 4, 2].length) (baseStart_3387520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3387520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3387520 prefixEnd_3387520 := by exact prefixLift 3387520
  have htrace : WordTrace (prefixWord ++ tailWord_3387520) baseStart_3387520 baseEnd_3387520 := by
    simpa [prefixWord, tailWord_3387520, baseEnd_3387520] using wordTrace_append hprefix tailTrace_3387520
  have hstable : (prefixWord ++ tailWord_3387520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3387520).length < 2 ^ (prefixWord ++ tailWord_3387520).sum := by decide
  have hdescent : baseEnd_3387520 < baseStart_3387520 := by decide
  rcases family_descends (prefixWord ++ tailWord_3387520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3387554 : List Nat := [3, 3, 1, 3, 1, 2, 1, 1, 2, 4, 2]
def baseStart_3387554 : Nat := 118140960795 + 3387554 * 2 ^ 59
def prefixEnd_3387554 : Nat := 4983230072969 + 3 ^ 40 * 3387554 * 2
def baseEnd_3387554 : Nat := 1739443445060944413095929

theorem tailTrace_3387554 : CollatzResearch.WordTrace tailWord_3387554 prefixEnd_3387554 1739443445060944413095929 := by
  unfold tailWord_3387554
  simp only [CollatzResearch.WordTrace]
  refine ⟨30888561192369470251934429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82369496512985254005158477 30888561192369470251934429)
  ·
    refine ⟨11583210447138551344475411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30888561192369470251934429 11583210447138551344475411)
    ·
      refine ⟨17374815670707827016713117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11583210447138551344475411 17374815670707827016713117)
      ·
        refine ⟨6515555876515435131267419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17374815670707827016713117 6515555876515435131267419)
        ·
          refine ⟨9773333814773152696901129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6515555876515435131267419 9773333814773152696901129)
          ·
            refine ⟨7330000361079864522675847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9773333814773152696901129 7330000361079864522675847)
            ·
              refine ⟨10995000541619796784013771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7330000361079864522675847 10995000541619796784013771)
              ·
                refine ⟨16492500812429695176020657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10995000541619796784013771 16492500812429695176020657)
                ·
                  refine ⟨12369375609322271382015493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16492500812429695176020657 12369375609322271382015493)
                  ·
                    refine ⟨2319257926747925884127905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12369375609322271382015493 2319257926747925884127905)
                    ·
                      refine ⟨1739443445060944413095929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2319257926747925884127905 1739443445060944413095929)
                      ·
                        rfl

theorem cell23_3387554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 1, 2, 4, 2].length) (baseStart_3387554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3387554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3387554 prefixEnd_3387554 := by exact prefixLift 3387554
  have htrace : WordTrace (prefixWord ++ tailWord_3387554) baseStart_3387554 baseEnd_3387554 := by
    simpa [prefixWord, tailWord_3387554, baseEnd_3387554] using wordTrace_append hprefix tailTrace_3387554
  have hstable : (prefixWord ++ tailWord_3387554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3387554).length < 2 ^ (prefixWord ++ tailWord_3387554).sum := by decide
  have hdescent : baseEnd_3387554 < baseStart_3387554 := by decide
  rcases family_descends (prefixWord ++ tailWord_3387554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3387583 : List Nat := [1, 1, 2, 2, 2, 2, 1, 1, 2, 4, 5]
def baseStart_3387583 : Nat := 118140960795 + 3387583 * 2 ^ 59
def prefixEnd_3387583 : Nat := 4983230072969 + 3 ^ 40 * 3387583 * 2
def baseEnd_3387583 : Nat := 1739458335999924799633295

theorem tailTrace_3387583 : CollatzResearch.WordTrace tailWord_3387583 prefixEnd_3387583 1739458335999924799633295 := by
  unfold tailWord_3387583
  simp only [CollatzResearch.WordTrace]
  refine ⟨123555302486372818960543403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82370201657581879307028935 123555302486372818960543403)
  ·
    refine ⟨185332953729559228440815105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123555302486372818960543403 185332953729559228440815105)
    ·
      refine ⟨138999715297169421330611329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185332953729559228440815105 138999715297169421330611329)
      ·
        refine ⟨104249786472877065997958497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138999715297169421330611329 104249786472877065997958497)
        ·
          refine ⟨78187339854657799498468873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104249786472877065997958497 78187339854657799498468873)
          ·
            refine ⟨58640504890993349623851655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78187339854657799498468873 58640504890993349623851655)
            ·
              refine ⟨87960757336490024435777483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58640504890993349623851655 87960757336490024435777483)
              ·
                refine ⟨131941136004735036653666225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87960757336490024435777483 131941136004735036653666225)
                ·
                  refine ⟨98955852003551277490249669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 131941136004735036653666225 98955852003551277490249669)
                  ·
                    refine ⟨18554222250665864529421813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 98955852003551277490249669 18554222250665864529421813)
                    ·
                      refine ⟨1739458335999924799633295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18554222250665864529421813 1739458335999924799633295)
                      ·
                        rfl

theorem cell23_3387583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 4, 5].length) (baseStart_3387583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3387583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3387583 prefixEnd_3387583 := by exact prefixLift 3387583
  have htrace : WordTrace (prefixWord ++ tailWord_3387583) baseStart_3387583 baseEnd_3387583 := by
    simpa [prefixWord, tailWord_3387583, baseEnd_3387583] using wordTrace_append hprefix tailTrace_3387583
  have hstable : (prefixWord ++ tailWord_3387583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3387583).length < 2 ^ (prefixWord ++ tailWord_3387583).sum := by decide
  have hdescent : baseEnd_3387583 < baseStart_3387583 := by decide
  rcases family_descends (prefixWord ++ tailWord_3387583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3387610 : List Nat := [3, 1, 1, 2, 2, 1, 2, 1, 5, 1, 4]
def baseStart_3387610 : Nat := 118140960795 + 3387610 * 2 ^ 59
def prefixEnd_3387610 : Nat := 4983230072969 + 3 ^ 40 * 3387610 * 2
def baseEnd_3387610 : Nat := 1739472199977596193995671

theorem tailTrace_3387610 : CollatzResearch.WordTrace tailWord_3387610 prefixEnd_3387610 1739472199977596193995671 := by
  unfold tailWord_3387610
  simp only [CollatzResearch.WordTrace]
  refine ⟨30889071814318750642944071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82370858171516668381184189 30889071814318750642944071)
  ·
    refine ⟨46333607721478125964416107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30889071814318750642944071 46333607721478125964416107)
    ·
      refine ⟨69500411582217188946624161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46333607721478125964416107 69500411582217188946624161)
      ·
        refine ⟨52125308686662891709968121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69500411582217188946624161 52125308686662891709968121)
        ·
          refine ⟨39093981514997168782476091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52125308686662891709968121 39093981514997168782476091)
          ·
            refine ⟨58640972272495753173714137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39093981514997168782476091 58640972272495753173714137)
            ·
              refine ⟨43980729204371814880285603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58640972272495753173714137 43980729204371814880285603)
              ·
                refine ⟨65971093806557722320428405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43980729204371814880285603 65971093806557722320428405)
                ·
                  refine ⟨6184790044364786467540163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65971093806557722320428405 6184790044364786467540163)
                  ·
                    refine ⟨9277185066547179701310245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6184790044364786467540163 9277185066547179701310245)
                    ·
                      refine ⟨1739472199977596193995671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9277185066547179701310245 1739472199977596193995671)
                      ·
                        rfl

theorem cell23_3387610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 5, 1, 4].length) (baseStart_3387610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3387610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3387610 prefixEnd_3387610 := by exact prefixLift 3387610
  have htrace : WordTrace (prefixWord ++ tailWord_3387610) baseStart_3387610 baseEnd_3387610 := by
    simpa [prefixWord, tailWord_3387610, baseEnd_3387610] using wordTrace_append hprefix tailTrace_3387610
  have hstable : (prefixWord ++ tailWord_3387610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3387610).length < 2 ^ (prefixWord ++ tailWord_3387610).sum := by decide
  have hdescent : baseEnd_3387610 < baseStart_3387610 := by decide
  rcases family_descends (prefixWord ++ tailWord_3387610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3387627 : List Nat := [1, 1, 1, 1, 2, 5, 4, 2, 1, 1, 4]
def baseStart_3387627 : Nat := 118140960795 + 3387627 * 2 ^ 59
def prefixEnd_3387627 : Nat := 4983230072969 + 3 ^ 40 * 3387627 * 2
def baseEnd_3387627 : Nat := 1739480929148722627483093

theorem tailTrace_3387627 : CollatzResearch.WordTrace tailWord_3387627 prefixEnd_3387627 1739480929148722627483093 := by
  unfold tailWord_3387627
  simp only [CollatzResearch.WordTrace]
  refine ⟨123556907298213414475145135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82371271532142276316763423 123556907298213414475145135)
  ·
    refine ⟨185335360947320121712717703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123556907298213414475145135 185335360947320121712717703)
    ·
      refine ⟨278003041420980182569076555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185335360947320121712717703 278003041420980182569076555)
      ·
        refine ⟨417004562131470273853614833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278003041420980182569076555 417004562131470273853614833)
        ·
          refine ⟨312753421598602705390211125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 417004562131470273853614833 312753421598602705390211125)
          ·
            refine ⟨29320633274869003630332293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 312753421598602705390211125 29320633274869003630332293)
            ·
              refine ⟨5497618739037938180687305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29320633274869003630332293 5497618739037938180687305)
              ·
                refine ⟨4123214054278453635515479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5497618739037938180687305 4123214054278453635515479)
                ·
                  refine ⟨6184821081417680453273219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4123214054278453635515479 6184821081417680453273219)
                  ·
                    refine ⟨9277231622126520679909829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6184821081417680453273219 9277231622126520679909829)
                    ·
                      refine ⟨1739480929148722627483093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9277231622126520679909829 1739480929148722627483093)
                      ·
                        rfl

theorem cell23_3387627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 4, 2, 1, 1, 4].length) (baseStart_3387627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3387627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3387627 prefixEnd_3387627 := by exact prefixLift 3387627
  have htrace : WordTrace (prefixWord ++ tailWord_3387627) baseStart_3387627 baseEnd_3387627 := by
    simpa [prefixWord, tailWord_3387627, baseEnd_3387627] using wordTrace_append hprefix tailTrace_3387627
  have hstable : (prefixWord ++ tailWord_3387627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3387627).length < 2 ^ (prefixWord ++ tailWord_3387627).sum := by decide
  have hdescent : baseEnd_3387627 < baseStart_3387627 := by decide
  rcases family_descends (prefixWord ++ tailWord_3387627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3387630 : List Nat := [4, 1, 2, 1, 1, 1, 1, 1, 5, 1, 5]
def baseStart_3387630 : Nat := 118140960795 + 3387630 * 2 ^ 59
def prefixEnd_3387630 : Nat := 4983230072969 + 3 ^ 40 * 3387630 * 2
def baseEnd_3387630 : Nat := 1739482469590686115745579

theorem tailTrace_3387630 : CollatzResearch.WordTrace tailWord_3387630 prefixEnd_3387630 1739482469590686115745579 := by
  unfold tailWord_3387630
  simp only [CollatzResearch.WordTrace]
  refine ⟨15444627089650318248438043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82371344478135030658336229 15444627089650318248438043)
  ·
    refine ⟨23166940634475477372657065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15444627089650318248438043 23166940634475477372657065)
    ·
      refine ⟨17375205475856608029492799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23166940634475477372657065 17375205475856608029492799)
      ·
        refine ⟨26062808213784912044239199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17375205475856608029492799 26062808213784912044239199)
        ·
          refine ⟨39094212320677368066358799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26062808213784912044239199 39094212320677368066358799)
          ·
            refine ⟨58641318481016052099538199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39094212320677368066358799 58641318481016052099538199)
            ·
              refine ⟨87961977721524078149307299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58641318481016052099538199 87961977721524078149307299)
              ·
                refine ⟨131942966582286117223960949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87961977721524078149307299 131942966582286117223960949)
                ·
                  refine ⟨12369653117089323489746339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 131942966582286117223960949 12369653117089323489746339)
                  ·
                    refine ⟨18554479675633985234619509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12369653117089323489746339 18554479675633985234619509)
                    ·
                      refine ⟨1739482469590686115745579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18554479675633985234619509 1739482469590686115745579)
                      ·
                        rfl

theorem cell23_3387630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 5, 1, 5].length) (baseStart_3387630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3387630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3387630 prefixEnd_3387630 := by exact prefixLift 3387630
  have htrace : WordTrace (prefixWord ++ tailWord_3387630) baseStart_3387630 baseEnd_3387630 := by
    simpa [prefixWord, tailWord_3387630, baseEnd_3387630] using wordTrace_append hprefix tailTrace_3387630
  have hstable : (prefixWord ++ tailWord_3387630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3387630).length < 2 ^ (prefixWord ++ tailWord_3387630).sum := by decide
  have hdescent : baseEnd_3387630 < baseStart_3387630 := by decide
  rcases family_descends (prefixWord ++ tailWord_3387630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3387640 : List Nat := [2, 1, 2, 1, 1, 2, 1, 6, 1, 2, 4]
def baseStart_3387640 : Nat := 118140960795 + 3387640 * 2 ^ 59
def prefixEnd_3387640 : Nat := 4983230072969 + 3 ^ 40 * 3387640 * 2
def baseEnd_3387640 : Nat := 1739487604397231076620533

theorem tailTrace_3387640 : CollatzResearch.WordTrace tailWord_3387640 prefixEnd_3387640 1739487604397231076620533 := by
  unfold tailWord_3387640
  simp only [CollatzResearch.WordTrace]
  refine ⟨61778690723583158847684187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82371587631444211796912249 61778690723583158847684187)
  ·
    refine ⟨92668036085374738271526281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61778690723583158847684187 92668036085374738271526281)
    ·
      refine ⟨69501027064031053703644711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92668036085374738271526281 69501027064031053703644711)
      ·
        refine ⟨104251540596046580555467067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69501027064031053703644711 104251540596046580555467067)
        ·
          refine ⟨156377310894069870833200601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104251540596046580555467067 156377310894069870833200601)
          ·
            refine ⟨117282983170552403124900451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156377310894069870833200601 117282983170552403124900451)
            ·
              refine ⟨175924474755828604687350677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117282983170552403124900451 175924474755828604687350677)
              ·
                refine ⟨8246459754179465844719563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 175924474755828604687350677 8246459754179465844719563)
                ·
                  refine ⟨12369689631269198767079345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8246459754179465844719563 12369689631269198767079345)
                  ·
                    refine ⟨9277267223451899075309509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12369689631269198767079345 9277267223451899075309509)
                    ·
                      refine ⟨1739487604397231076620533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9277267223451899075309509 1739487604397231076620533)
                      ·
                        rfl

theorem cell23_3387640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 6, 1, 2, 4].length) (baseStart_3387640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3387640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3387640 prefixEnd_3387640 := by exact prefixLift 3387640
  have htrace : WordTrace (prefixWord ++ tailWord_3387640) baseStart_3387640 baseEnd_3387640 := by
    simpa [prefixWord, tailWord_3387640, baseEnd_3387640] using wordTrace_append hprefix tailTrace_3387640
  have hstable : (prefixWord ++ tailWord_3387640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3387640).length < 2 ^ (prefixWord ++ tailWord_3387640).sum := by decide
  have hdescent : baseEnd_3387640 < baseStart_3387640 := by decide
  rcases family_descends (prefixWord ++ tailWord_3387640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
