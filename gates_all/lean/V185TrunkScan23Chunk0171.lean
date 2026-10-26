import V185TrunkScan23Chunk0170

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1011726 : List Nat := [4, 1, 1, 2, 2, 1, 3, 2, 2, 3, 2]
def baseStart_1011726 : Nat := 118140960795 + 1011726 * 2 ^ 59
def prefixEnd_1011726 : Nat := 4983230072969 + 3 ^ 40 * 1011726 * 2
def baseEnd_1011726 : Nat := 519501728650813851072163

theorem tailTrace_1011726 : CollatzResearch.WordTrace tailWord_1011726 prefixEnd_1011726 519501728650813851072163 := by
  unfold tailWord_1011726
  simp only [CollatzResearch.WordTrace]
  refine ⟨4612584841587120736183879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24600452488464643926314021 4612584841587120736183879)
  ·
    refine ⟨6918877262380681104275819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4612584841587120736183879 6918877262380681104275819)
    ·
      refine ⟨10378315893571021656413729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6918877262380681104275819 10378315893571021656413729)
      ·
        refine ⟨7783736920178266242310297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10378315893571021656413729 7783736920178266242310297)
        ·
          refine ⟨5837802690133699681732723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7783736920178266242310297 5837802690133699681732723)
          ·
            refine ⟨8756704035200549522599085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5837802690133699681732723 8756704035200549522599085)
            ·
              refine ⟨3283764013200206070974657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8756704035200549522599085 3283764013200206070974657)
              ·
                refine ⟨2462823009900154553230993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3283764013200206070974657 2462823009900154553230993)
                ·
                  refine ⟨1847117257425115914923245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2462823009900154553230993 1847117257425115914923245)
                  ·
                    refine ⟨692668971534418468096217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1847117257425115914923245 692668971534418468096217)
                    ·
                      refine ⟨519501728650813851072163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 692668971534418468096217 519501728650813851072163)
                      ·
                        rfl

theorem cell23_1011726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 2, 2, 3, 2].length) (baseStart_1011726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1011726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1011726 prefixEnd_1011726 := by exact prefixLift 1011726
  have htrace : WordTrace (prefixWord ++ tailWord_1011726) baseStart_1011726 baseEnd_1011726 := by
    simpa [prefixWord, tailWord_1011726, baseEnd_1011726] using wordTrace_append hprefix tailTrace_1011726
  have hstable : (prefixWord ++ tailWord_1011726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011726).length < 2 ^ (prefixWord ++ tailWord_1011726).sum := by decide
  have hdescent : baseEnd_1011726 < baseStart_1011726 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011733 : List Nat := [1, 3, 2, 1, 5, 2, 1, 1, 3, 1, 3]
def baseStart_1011733 : Nat := 118140960795 + 1011733 * 2 ^ 59
def prefixEnd_1011733 : Nat := 4983230072969 + 3 ^ 40 * 1011733 * 2
def baseEnd_1011733 : Nat := 519505323015395323684631

theorem tailTrace_1011733 : CollatzResearch.WordTrace tailWord_1011733 prefixEnd_1011733 519505323015395323684631 := by
  unfold tailWord_1011733
  simp only [CollatzResearch.WordTrace]
  refine ⟨36900934043671606084975853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24600622695781070723317235 36900934043671606084975853)
  ·
    refine ⟨13837850266376852281865945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36900934043671606084975853 13837850266376852281865945)
    ·
      refine ⟨10378387699782639211399459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13837850266376852281865945 10378387699782639211399459)
      ·
        refine ⟨15567581549673958817099189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10378387699782639211399459 15567581549673958817099189)
        ·
          refine ⟨1459460770281933639103049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15567581549673958817099189 1459460770281933639103049)
          ·
            refine ⟨1094595577711450229327287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1459460770281933639103049 1094595577711450229327287)
            ·
              refine ⟨1641893366567175343990931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1094595577711450229327287 1641893366567175343990931)
              ·
                refine ⟨2462840049850763015986397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1641893366567175343990931 2462840049850763015986397)
                ·
                  refine ⟨923565018694036130994899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2462840049850763015986397 923565018694036130994899)
                  ·
                    refine ⟨1385347528041054196492349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 923565018694036130994899 1385347528041054196492349)
                    ·
                      refine ⟨519505323015395323684631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1385347528041054196492349 519505323015395323684631)
                      ·
                        rfl

theorem cell23_1011733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 1, 1, 3, 1, 3].length) (baseStart_1011733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1011733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1011733 prefixEnd_1011733 := by exact prefixLift 1011733
  have htrace : WordTrace (prefixWord ++ tailWord_1011733) baseStart_1011733 baseEnd_1011733 := by
    simpa [prefixWord, tailWord_1011733, baseEnd_1011733] using wordTrace_append hprefix tailTrace_1011733
  have hstable : (prefixWord ++ tailWord_1011733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011733).length < 2 ^ (prefixWord ++ tailWord_1011733).sum := by decide
  have hdescent : baseEnd_1011733 < baseStart_1011733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011759 : List Nat := [1, 1, 2, 1, 2, 1, 1, 8, 1, 2, 3]
def baseStart_1011759 : Nat := 118140960795 + 1011759 * 2 ^ 59
def prefixEnd_1011759 : Nat := 4983230072969 + 3 ^ 40 * 1011759 * 2
def baseEnd_1011759 : Nat := 519518673512412221959511

theorem tailTrace_1011759 : CollatzResearch.WordTrace tailWord_1011759 prefixEnd_1011759 519518673512412221959511 := by
  unfold tailWord_1011759
  simp only [CollatzResearch.WordTrace]
  refine ⟨36901882341577412525422331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24601254894384941683614887 36901882341577412525422331)
  ·
    refine ⟨55352823512366118788133497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36901882341577412525422331 55352823512366118788133497)
    ·
      refine ⟨41514617634274589091100123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55352823512366118788133497 41514617634274589091100123)
      ·
        refine ⟨62271926451411883636650185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41514617634274589091100123 62271926451411883636650185)
        ·
          refine ⟨46703944838558912727487639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62271926451411883636650185 46703944838558912727487639)
          ·
            refine ⟨70055917257838369091231459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46703944838558912727487639 70055917257838369091231459)
            ·
              refine ⟨105083875886757553636847189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70055917257838369091231459 105083875886757553636847189)
              ·
                refine ⟨1231451670547940081681803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 105083875886757553636847189 1231451670547940081681803)
                ·
                  refine ⟨1847177505821910122522705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1231451670547940081681803 1847177505821910122522705)
                  ·
                    refine ⟨1385383129366432591892029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1847177505821910122522705 1385383129366432591892029)
                    ·
                      refine ⟨519518673512412221959511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1385383129366432591892029 519518673512412221959511)
                      ·
                        rfl

theorem cell23_1011759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 8, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 8, 1, 2, 3].length) (baseStart_1011759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1011759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1011759 prefixEnd_1011759 := by exact prefixLift 1011759
  have htrace : WordTrace (prefixWord ++ tailWord_1011759) baseStart_1011759 baseEnd_1011759 := by
    simpa [prefixWord, tailWord_1011759, baseEnd_1011759] using wordTrace_append hprefix tailTrace_1011759
  have hstable : (prefixWord ++ tailWord_1011759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011759).length < 2 ^ (prefixWord ++ tailWord_1011759).sum := by decide
  have hdescent : baseEnd_1011759 < baseStart_1011759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011762 : List Nat := [3, 2, 1, 1, 2, 3, 2, 9]
def baseStart_1011762 : Nat := 118140960795 + 1011762 * 2 ^ 59
def prefixEnd_1011762 : Nat := 4983230072969 + 3 ^ 40 * 1011762 * 2
def baseEnd_1011762 : Nat := 19241489405717618897111

theorem tailTrace_1011762 : CollatzResearch.WordTrace tailWord_1011762 prefixEnd_1011762 19241489405717618897111 := by
  unfold tailWord_1011762
  simp only [CollatzResearch.WordTrace]
  refine ⟨9225497940141636009445385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24601327840377696025187693 9225497940141636009445385)
  ·
    refine ⟨6919123455106227007084039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9225497940141636009445385 6919123455106227007084039)
    ·
      refine ⟨10378685182659340510626059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6919123455106227007084039 10378685182659340510626059)
      ·
        refine ⟨15568027773989010765939089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10378685182659340510626059 15568027773989010765939089)
        ·
          refine ⟨11676020830491758074454317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15568027773989010765939089 11676020830491758074454317)
          ·
            refine ⟨4378507811434409277920369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11676020830491758074454317 4378507811434409277920369)
            ·
              refine ⟨3283880858575806958440277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4378507811434409277920369 3283880858575806958440277)
              ·
                refine ⟨19241489405717618897111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3283880858575806958440277 19241489405717618897111)
                ·
                  rfl

theorem cell23_1011762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 9].length) (baseStart_1011762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1011762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1011762 prefixEnd_1011762 := by exact prefixLift 1011762
  have htrace : WordTrace (prefixWord ++ tailWord_1011762) baseStart_1011762 baseEnd_1011762 := by
    simpa [prefixWord, tailWord_1011762, baseEnd_1011762] using wordTrace_append hprefix tailTrace_1011762
  have hstable : (prefixWord ++ tailWord_1011762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011762).length < 2 ^ (prefixWord ++ tailWord_1011762).sum := by decide
  have hdescent : baseEnd_1011762 < baseStart_1011762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011790 : List Nat := [4, 1, 1, 1, 1, 5, 1, 4, 1, 2, 2]
def baseStart_1011790 : Nat := 118140960795 + 1011790 * 2 ^ 59
def prefixEnd_1011790 : Nat := 4983230072969 + 3 ^ 40 * 1011790 * 2
def baseEnd_1011790 : Nat := 519534591412701600671869

theorem tailTrace_1011790 : CollatzResearch.WordTrace tailWord_1011790 prefixEnd_1011790 519534591412701600671869 := by
  unfold tailWord_1011790
  simp only [CollatzResearch.WordTrace]
  refine ⟨4612876625558138102475103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24602008669643403213200549 4612876625558138102475103)
  ·
    refine ⟨6919314938337207153712655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4612876625558138102475103 6919314938337207153712655)
    ·
      refine ⟨10378972407505810730568983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6919314938337207153712655 10378972407505810730568983)
      ·
        refine ⟨15568458611258716095853475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10378972407505810730568983 15568458611258716095853475)
        ·
          refine ⟨23352687916888074143780213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15568458611258716095853475 23352687916888074143780213)
          ·
            refine ⟨2189314492208256950979395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23352687916888074143780213 2189314492208256950979395)
            ·
              refine ⟨3283971738312385426469093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2189314492208256950979395 3283971738312385426469093)
              ·
                refine ⟨615744700933572267462955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3283971738312385426469093 615744700933572267462955)
                ·
                  refine ⟨923617051400358401194433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 615744700933572267462955 923617051400358401194433)
                  ·
                    refine ⟨692712788550268800895825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 923617051400358401194433 692712788550268800895825)
                    ·
                      refine ⟨519534591412701600671869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 692712788550268800895825 519534591412701600671869)
                      ·
                        rfl

theorem cell23_1011790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 4, 1, 2, 2].length) (baseStart_1011790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1011790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1011790 prefixEnd_1011790 := by exact prefixLift 1011790
  have htrace : WordTrace (prefixWord ++ tailWord_1011790) baseStart_1011790 baseEnd_1011790 := by
    simpa [prefixWord, tailWord_1011790, baseEnd_1011790] using wordTrace_append hprefix tailTrace_1011790
  have hstable : (prefixWord ++ tailWord_1011790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011790).length < 2 ^ (prefixWord ++ tailWord_1011790).sum := by decide
  have hdescent : baseEnd_1011790 < baseStart_1011790 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011832 : List Nat := [2, 1, 2, 1, 1, 1, 3, 3, 1, 3, 5]
def baseStart_1011832 : Nat := 118140960795 + 1011832 * 2 ^ 59
def prefixEnd_1011832 : Nat := 4983230072969 + 3 ^ 40 * 1011832 * 2
def baseEnd_1011832 : Nat := 519556157600190436346675

theorem tailTrace_1011832 : CollatzResearch.WordTrace tailWord_1011832 prefixEnd_1011832 519556157600190436346675 := by
  unfold tailWord_1011832
  simp only [CollatzResearch.WordTrace]
  refine ⟨18452272435156472996414875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24603029913541963995219833 18452272435156472996414875)
  ·
    refine ⟨27678408652734709494622313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18452272435156472996414875 27678408652734709494622313)
    ·
      refine ⟨20758806489551032120966735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27678408652734709494622313 20758806489551032120966735)
      ·
        refine ⟨31138209734326548181450103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20758806489551032120966735 31138209734326548181450103)
        ·
          refine ⟨46707314601489822272175155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31138209734326548181450103 46707314601489822272175155)
          ·
            refine ⟨70060971902234733408262733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46707314601489822272175155 70060971902234733408262733)
            ·
              refine ⟨26272864463338025028098525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70060971902234733408262733 26272864463338025028098525)
              ·
                refine ⟨9852324173751759385536947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26272864463338025028098525 9852324173751759385536947)
                ·
                  refine ⟨14778486260627639078305421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9852324173751759385536947 14778486260627639078305421)
                  ·
                    refine ⟨5541932347735364654364533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14778486260627639078305421 5541932347735364654364533)
                    ·
                      refine ⟨519556157600190436346675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5541932347735364654364533 519556157600190436346675)
                      ·
                        rfl

theorem cell23_1011832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 3, 1, 3, 5].length) (baseStart_1011832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1011832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1011832 prefixEnd_1011832 := by exact prefixLift 1011832
  have htrace : WordTrace (prefixWord ++ tailWord_1011832) baseStart_1011832 baseEnd_1011832 := by
    simpa [prefixWord, tailWord_1011832, baseEnd_1011832] using wordTrace_append hprefix tailTrace_1011832
  have hstable : (prefixWord ++ tailWord_1011832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011832).length < 2 ^ (prefixWord ++ tailWord_1011832).sum := by decide
  have hdescent : baseEnd_1011832 < baseStart_1011832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011833 : List Nat := [1, 2, 1, 3, 4, 2, 1, 3, 1, 3, 2]
def baseStart_1011833 : Nat := 118140960795 + 1011833 * 2 ^ 59
def prefixEnd_1011833 : Nat := 4983230072969 + 3 ^ 40 * 1011833 * 2
def baseEnd_1011833 : Nat := 519556671080844932434171

theorem tailTrace_1011833 : CollatzResearch.WordTrace tailWord_1011833 prefixEnd_1011833 519556671080844932434171 := by
  unfold tailWord_1011833
  simp only [CollatzResearch.WordTrace]
  refine ⟨36904581343309323163616153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24603054228872882109077435 36904581343309323163616153)
  ·
    refine ⟨27678436007481992372712115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36904581343309323163616153 27678436007481992372712115)
    ·
      refine ⟨41517654011222988559068173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27678436007481992372712115 41517654011222988559068173)
      ·
        refine ⟨15569120254208620709650565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41517654011222988559068173 15569120254208620709650565)
        ·
          refine ⟨2919210047664116383059481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15569120254208620709650565 2919210047664116383059481)
          ·
            refine ⟨2189407535748087287294611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2919210047664116383059481 2189407535748087287294611)
            ·
              refine ⟨3284111303622130930941917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2189407535748087287294611 3284111303622130930941917)
              ·
                refine ⟨1231541738858299099103219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3284111303622130930941917 1231541738858299099103219)
                ·
                  refine ⟨1847312608287448648654829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1231541738858299099103219 1847312608287448648654829)
                  ·
                    refine ⟨692742228107793243245561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1847312608287448648654829 692742228107793243245561)
                    ·
                      refine ⟨519556671080844932434171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 692742228107793243245561 519556671080844932434171)
                      ·
                        rfl

theorem cell23_1011833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 3, 1, 3, 2].length) (baseStart_1011833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1011833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1011833 prefixEnd_1011833 := by exact prefixLift 1011833
  have htrace : WordTrace (prefixWord ++ tailWord_1011833) baseStart_1011833 baseEnd_1011833 := by
    simpa [prefixWord, tailWord_1011833, baseEnd_1011833] using wordTrace_append hprefix tailTrace_1011833
  have hstable : (prefixWord ++ tailWord_1011833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011833).length < 2 ^ (prefixWord ++ tailWord_1011833).sum := by decide
  have hdescent : baseEnd_1011833 < baseStart_1011833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011869 : List Nat := [1, 4, 2, 1, 1, 3, 2, 2, 7]
def baseStart_1011869 : Nat := 118140960795 + 1011869 * 2 ^ 59
def prefixEnd_1011869 : Nat := 4983230072969 + 3 ^ 40 * 1011869 * 2
def baseEnd_1011869 : Nat := 57730572931600754620445

theorem tailTrace_1011869 : CollatzResearch.WordTrace tailWord_1011869 prefixEnd_1011869 57730572931600754620445 := by
  unfold tailWord_1011869
  simp only [CollatzResearch.WordTrace]
  refine ⟨36905894371178901311926661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24603929580785934207951107 36905894371178901311926661)
  ·
    refine ⟨6919855194596043995986249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36905894371178901311926661 6919855194596043995986249)
    ·
      refine ⟨5189891395947032996989687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6919855194596043995986249 5189891395947032996989687)
      ·
        refine ⟨7784837093920549495484531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5189891395947032996989687 7784837093920549495484531)
        ·
          refine ⟨11677255640880824243226797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7784837093920549495484531 11677255640880824243226797)
          ·
            refine ⟨4378970865330309091210049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11677255640880824243226797 4378970865330309091210049)
            ·
              refine ⟨3284228148997731818407537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4378970865330309091210049 3284228148997731818407537)
              ·
                refine ⟨2463171111748298863805653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3284228148997731818407537 2463171111748298863805653)
                ·
                  refine ⟨57730572931600754620445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2463171111748298863805653 57730572931600754620445)
                  ·
                    rfl

theorem cell23_1011869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 2, 7].length) (baseStart_1011869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1011869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1011869 prefixEnd_1011869 := by exact prefixLift 1011869
  have htrace : WordTrace (prefixWord ++ tailWord_1011869) baseStart_1011869 baseEnd_1011869 := by
    simpa [prefixWord, tailWord_1011869, baseEnd_1011869] using wordTrace_append hprefix tailTrace_1011869
  have hstable : (prefixWord ++ tailWord_1011869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011869).length < 2 ^ (prefixWord ++ tailWord_1011869).sum := by decide
  have hdescent : baseEnd_1011869 < baseStart_1011869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011899 : List Nat := [1, 1, 1, 1, 1, 2, 7, 2, 2, 5]
def baseStart_1011899 : Nat := 118140960795 + 1011899 * 2 ^ 59
def prefixEnd_1011899 : Nat := 4983230072969 + 3 ^ 40 * 1011899 * 2
def baseEnd_1011899 : Nat := 173196853601347224736289

theorem tailTrace_1011899 : CollatzResearch.WordTrace tailWord_1011899 prefixEnd_1011899 173196853601347224736289 := by
  unfold tailWord_1011899
  simp only [CollatzResearch.WordTrace]
  refine ⟨36906988561070216435518751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24604659040713477623679167 36906988561070216435518751)
  ·
    refine ⟨55360482841605324653278127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36906988561070216435518751 55360482841605324653278127)
    ·
      refine ⟨83040724262407986979917191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55360482841605324653278127 83040724262407986979917191)
      ·
        refine ⟨124561086393611980469875787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83040724262407986979917191 124561086393611980469875787)
        ·
          refine ⟨186841629590417970704813681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124561086393611980469875787 186841629590417970704813681)
          ·
            refine ⟨140131222192813478028610261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186841629590417970704813681 140131222192813478028610261)
            ·
              refine ⟨3284325520144065891295553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 140131222192813478028610261 3284325520144065891295553)
              ·
                refine ⟨2463244140108049418471665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3284325520144065891295553 2463244140108049418471665)
                ·
                  refine ⟨1847433105081037063853749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2463244140108049418471665 1847433105081037063853749)
                  ·
                    refine ⟨173196853601347224736289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1847433105081037063853749 173196853601347224736289)
                    ·
                      rfl

theorem cell23_1011899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 2, 2, 5].length) (baseStart_1011899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1011899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1011899 prefixEnd_1011899 := by exact prefixLift 1011899
  have htrace : WordTrace (prefixWord ++ tailWord_1011899) baseStart_1011899 baseEnd_1011899 := by
    simpa [prefixWord, tailWord_1011899, baseEnd_1011899] using wordTrace_append hprefix tailTrace_1011899
  have hstable : (prefixWord ++ tailWord_1011899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011899).length < 2 ^ (prefixWord ++ tailWord_1011899).sum := by decide
  have hdescent : baseEnd_1011899 < baseStart_1011899 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011919 : List Nat := [1, 1, 2, 1, 1, 3, 3, 2, 4, 1, 4]
def baseStart_1011919 : Nat := 118140960795 + 1011919 * 2 ^ 59
def prefixEnd_1011919 : Nat := 4983230072969 + 3 ^ 40 * 1011919 * 2
def baseEnd_1011919 : Nat := 519600830417131595958775

theorem tailTrace_1011919 : CollatzResearch.WordTrace tailWord_1011919 prefixEnd_1011919 519600830417131595958775 := by
  unfold tailWord_1011919
  simp only [CollatzResearch.WordTrace]
  refine ⟨36907718020997759851246811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24605145347331839900831207 36907718020997759851246811)
  ·
    refine ⟨55361577031496639776870217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36907718020997759851246811 55361577031496639776870217)
    ·
      refine ⟨41521182773622479832652663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55361577031496639776870217 41521182773622479832652663)
      ·
        refine ⟨62281774160433719748978995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41521182773622479832652663 62281774160433719748978995)
        ·
          refine ⟨93422661240650579623468493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62281774160433719748978995 93422661240650579623468493)
          ·
            refine ⟨35033497965243967358800685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93422661240650579623468493 35033497965243967358800685)
            ·
              refine ⟨13137561736966487759550257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35033497965243967358800685 13137561736966487759550257)
              ·
                refine ⟨9853171302724865819662693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13137561736966487759550257 9853171302724865819662693)
                ·
                  refine ⟨1847469619260912341186755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9853171302724865819662693 1847469619260912341186755)
                  ·
                    refine ⟨2771204428891368511780133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1847469619260912341186755 2771204428891368511780133)
                    ·
                      refine ⟨519600830417131595958775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2771204428891368511780133 519600830417131595958775)
                      ·
                        rfl

theorem cell23_1011919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 2, 4, 1, 4].length) (baseStart_1011919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1011919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1011919 prefixEnd_1011919 := by exact prefixLift 1011919
  have htrace : WordTrace (prefixWord ++ tailWord_1011919) baseStart_1011919 baseEnd_1011919 := by
    simpa [prefixWord, tailWord_1011919, baseEnd_1011919] using wordTrace_append hprefix tailTrace_1011919
  have hstable : (prefixWord ++ tailWord_1011919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011919).length < 2 ^ (prefixWord ++ tailWord_1011919).sum := by decide
  have hdescent : baseEnd_1011919 < baseStart_1011919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011933 : List Nat := [1, 4, 3, 2, 1, 2, 2, 1, 2, 5]
def baseStart_1011933 : Nat := 118140960795 + 1011933 * 2 ^ 59
def prefixEnd_1011933 : Nat := 4983230072969 + 3 ^ 40 * 1011933 * 2
def baseEnd_1011933 : Nat := 173202673048764847061237

theorem tailTrace_1011933 : CollatzResearch.WordTrace tailWord_1011933 prefixEnd_1011933 173202673048764847061237 := by
  unfold tailWord_1011933
  simp only [CollatzResearch.WordTrace]
  refine ⟨36908228642947040242256453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24605485761964693494837635 36908228642947040242256453)
  ·
    refine ⟨6920292870552570045423085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36908228642947040242256453 6920292870552570045423085)
    ·
      refine ⟨2595109826457213767033657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6920292870552570045423085 2595109826457213767033657)
      ·
        refine ⟨1946332369842910325275243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2595109826457213767033657 1946332369842910325275243)
        ·
          refine ⟨2919498554764365487912865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1946332369842910325275243 2919498554764365487912865)
          ·
            refine ⟨2189623916073274115934649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2919498554764365487912865 2189623916073274115934649)
            ·
              refine ⟨1642217937054955586950987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2189623916073274115934649 1642217937054955586950987)
              ·
                refine ⟨2463326905582433380426481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1642217937054955586950987 2463326905582433380426481)
                ·
                  refine ⟨1847495179186825035319861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2463326905582433380426481 1847495179186825035319861)
                  ·
                    refine ⟨173202673048764847061237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1847495179186825035319861 173202673048764847061237)
                    ·
                      rfl

theorem cell23_1011933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 2, 1, 2, 5].length) (baseStart_1011933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1011933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1011933 prefixEnd_1011933 := by exact prefixLift 1011933
  have htrace : WordTrace (prefixWord ++ tailWord_1011933) baseStart_1011933 baseEnd_1011933 := by
    simpa [prefixWord, tailWord_1011933, baseEnd_1011933] using wordTrace_append hprefix tailTrace_1011933
  have hstable : (prefixWord ++ tailWord_1011933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011933).length < 2 ^ (prefixWord ++ tailWord_1011933).sum := by decide
  have hdescent : baseEnd_1011933 < baseStart_1011933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011936 : List Nat := [2, 1, 1, 3, 1, 3, 4, 1, 2, 1, 4]
def baseStart_1011936 : Nat := 118140960795 + 1011936 * 2 ^ 59
def prefixEnd_1011936 : Nat := 4983230072969 + 3 ^ 40 * 1011936 * 2
def baseEnd_1011936 : Nat := 519609559588258029446197

theorem tailTrace_1011936 : CollatzResearch.WordTrace tailWord_1011936 prefixEnd_1011936 519609559588258029446197 := by
  unfold tailWord_1011936
  simp only [CollatzResearch.WordTrace]
  refine ⟨18454169030968085877307831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24605558707957447836410441 18454169030968085877307831)
  ·
    refine ⟨27681253546452128815961747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18454169030968085877307831 27681253546452128815961747)
    ·
      refine ⟨41521880319678193223942621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27681253546452128815961747 41521880319678193223942621)
      ·
        refine ⟨15570705119879322458978483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41521880319678193223942621 15570705119879322458978483)
        ·
          refine ⟨23356057679818983688467725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15570705119879322458978483 23356057679818983688467725)
          ·
            refine ⟨8758521629932118883175397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23356057679818983688467725 8758521629932118883175397)
            ·
              refine ⟨1642222805612272290595387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8758521629932118883175397 1642222805612272290595387)
              ·
                refine ⟨2463334208418408435893081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1642222805612272290595387 2463334208418408435893081)
                ·
                  refine ⟨1847500656313806326919811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2463334208418408435893081 1847500656313806326919811)
                  ·
                    refine ⟨2771250984470709490379717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1847500656313806326919811 2771250984470709490379717)
                    ·
                      refine ⟨519609559588258029446197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2771250984470709490379717 519609559588258029446197)
                      ·
                        rfl

theorem cell23_1011936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4, 1, 2, 1, 4].length) (baseStart_1011936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1011936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1011936 prefixEnd_1011936 := by exact prefixLift 1011936
  have htrace : WordTrace (prefixWord ++ tailWord_1011936) baseStart_1011936 baseEnd_1011936 := by
    simpa [prefixWord, tailWord_1011936, baseEnd_1011936] using wordTrace_append hprefix tailTrace_1011936
  have hstable : (prefixWord ++ tailWord_1011936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011936).length < 2 ^ (prefixWord ++ tailWord_1011936).sum := by decide
  have hdescent : baseEnd_1011936 < baseStart_1011936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011970 : List Nat := [3, 4, 1, 1, 2, 2, 1, 1, 2, 4, 2]
def baseStart_1011970 : Nat := 118140960795 + 1011970 * 2 ^ 59
def prefixEnd_1011970 : Nat := 4983230072969 + 3 ^ 40 * 1011970 * 2
def baseEnd_1011970 : Nat := 519627017930510896421041

theorem tailTrace_1011970 : CollatzResearch.WordTrace tailWord_1011970 prefixEnd_1011970 519627017930510896421041 := by
  unfold tailWord_1011970
  simp only [CollatzResearch.WordTrace]
  refine ⟨9227394535953248890338341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24606385429208663707568909 9227394535953248890338341)
  ·
    refine ⟨1730136475491234166938439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9227394535953248890338341 1730136475491234166938439)
    ·
      refine ⟨2595204713236851250407659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1730136475491234166938439 2595204713236851250407659)
      ·
        refine ⟨3892807069855276875611489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2595204713236851250407659 3892807069855276875611489)
        ·
          refine ⟨2919605302391457656708617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3892807069855276875611489 2919605302391457656708617)
          ·
            refine ⟨2189703976793593242531463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2919605302391457656708617 2189703976793593242531463)
            ·
              refine ⟨3284555965190389863797195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2189703976793593242531463 3284555965190389863797195)
              ·
                refine ⟨4926833947785584795695793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3284555965190389863797195 4926833947785584795695793)
                ·
                  refine ⟨3695125460839188596771845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4926833947785584795695793 3695125460839188596771845)
                  ·
                    refine ⟨692836023907347861894721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3695125460839188596771845 692836023907347861894721)
                    ·
                      refine ⟨519627017930510896421041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 692836023907347861894721 519627017930510896421041)
                      ·
                        rfl

theorem cell23_1011970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 1, 2, 4, 2].length) (baseStart_1011970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1011970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1011970 prefixEnd_1011970 := by exact prefixLift 1011970
  have htrace : WordTrace (prefixWord ++ tailWord_1011970) baseStart_1011970 baseEnd_1011970 := by
    simpa [prefixWord, tailWord_1011970, baseEnd_1011970] using wordTrace_append hprefix tailTrace_1011970
  have hstable : (prefixWord ++ tailWord_1011970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011970).length < 2 ^ (prefixWord ++ tailWord_1011970).sum := by decide
  have hdescent : baseEnd_1011970 < baseStart_1011970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011976 : List Nat := [2, 1, 3, 2, 3, 1, 2, 3, 6]
def baseStart_1011976 : Nat := 118140960795 + 1011976 * 2 ^ 59
def prefixEnd_1011976 : Nat := 4983230072969 + 3 ^ 40 * 1011976 * 2
def baseEnd_1011976 : Nat := 57736677646048652549557

theorem tailTrace_1011976 : CollatzResearch.WordTrace tailWord_1011976 prefixEnd_1011976 57736677646048652549557 := by
  unfold tailWord_1011976
  simp only [CollatzResearch.WordTrace]
  refine ⟨18454898490895629293035891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24606531321194172390714521 18454898490895629293035891)
  ·
    refine ⟨27682347736343443939553837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18454898490895629293035891 27682347736343443939553837)
    ·
      refine ⟨10380880401128791477332689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27682347736343443939553837 10380880401128791477332689)
      ·
        refine ⟨7785660300846593607999517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10380880401128791477332689 7785660300846593607999517)
        ·
          refine ⟨2919622612817472602999819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7785660300846593607999517 2919622612817472602999819)
          ·
            refine ⟨4379433919226208904499729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2919622612817472602999819 4379433919226208904499729)
            ·
              refine ⟨3284575439419656678374797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4379433919226208904499729 3284575439419656678374797)
              ·
                refine ⟨1231715789782371254390549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3284575439419656678374797 1231715789782371254390549)
                ·
                  refine ⟨57736677646048652549557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1231715789782371254390549 57736677646048652549557)
                  ·
                    rfl

theorem cell23_1011976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 3, 6].length) (baseStart_1011976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1011976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1011976 prefixEnd_1011976 := by exact prefixLift 1011976
  have htrace : WordTrace (prefixWord ++ tailWord_1011976) baseStart_1011976 baseEnd_1011976 := by
    simpa [prefixWord, tailWord_1011976, baseEnd_1011976] using wordTrace_append hprefix tailTrace_1011976
  have hstable : (prefixWord ++ tailWord_1011976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011976).length < 2 ^ (prefixWord ++ tailWord_1011976).sum := by decide
  have hdescent : baseEnd_1011976 < baseStart_1011976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011997 : List Nat := [1, 4, 2, 3, 2, 1, 2, 3, 1, 4]
def baseStart_1011997 : Nat := 118140960795 + 1011997 * 2 ^ 59
def prefixEnd_1011997 : Nat := 4983230072969 + 3 ^ 40 * 1011997 * 2
def baseEnd_1011997 : Nat := 173213627302727430261139

theorem tailTrace_1011997 : CollatzResearch.WordTrace tailWord_1011997 prefixEnd_1011997 173213627302727430261139 := by
  unfold tailWord_1011997
  simp only [CollatzResearch.WordTrace]
  refine ⟨36910562914715179172586245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24607041943143452781724163 36910562914715179172586245)
  ·
    refine ⟨6920730546509096094859921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36910562914715179172586245 6920730546509096094859921)
    ·
      refine ⟨5190547909881822071144941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6920730546509096094859921 5190547909881822071144941)
      ·
        refine ⟨1946455466205683276679353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5190547909881822071144941 1946455466205683276679353)
        ·
          refine ⟨1459841599654262457509515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1946455466205683276679353 1459841599654262457509515)
          ·
            refine ⟨2189762399481393686264273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1459841599654262457509515 2189762399481393686264273)
            ·
              refine ⟨1642321799611045264698205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2189762399481393686264273 1642321799611045264698205)
              ·
                refine ⟨615870674854141974261827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1642321799611045264698205 615870674854141974261827)
                ·
                  refine ⟨923806012281212961392741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 615870674854141974261827 923806012281212961392741)
                  ·
                    refine ⟨173213627302727430261139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 923806012281212961392741 173213627302727430261139)
                    ·
                      rfl

theorem cell23_1011997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 2, 3, 1, 4].length) (baseStart_1011997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1011997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1011997 prefixEnd_1011997 := by exact prefixLift 1011997
  have htrace : WordTrace (prefixWord ++ tailWord_1011997) baseStart_1011997 baseEnd_1011997 := by
    simpa [prefixWord, tailWord_1011997, baseEnd_1011997] using wordTrace_append hprefix tailTrace_1011997
  have hstable : (prefixWord ++ tailWord_1011997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011997).length < 2 ^ (prefixWord ++ tailWord_1011997).sum := by decide
  have hdescent : baseEnd_1011997 < baseStart_1011997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012010 : List Nat := [3, 1, 4, 2, 2, 2, 1, 2, 6]
def baseStart_1012010 : Nat := 118140960795 + 1012010 * 2 ^ 59
def prefixEnd_1012010 : Nat := 4983230072969 + 3 ^ 40 * 1012010 * 2
def baseEnd_1012010 : Nat := 57738617461854526657873

theorem tailTrace_1012010 : CollatzResearch.WordTrace tailWord_1012010 prefixEnd_1012010 57738617461854526657873 := by
  unfold tailWord_1012010
  simp only [CollatzResearch.WordTrace]
  refine ⟨9227759265917020598202371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24607358042445388261872989 9227759265917020598202371)
  ·
    refine ⟨13841638898875530897303557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9227759265917020598202371 13841638898875530897303557)
    ·
      refine ⟨2595307293539162043244417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13841638898875530897303557 2595307293539162043244417)
      ·
        refine ⟨1946480470154371532433313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2595307293539162043244417 1946480470154371532433313)
        ·
          refine ⟨1459860352615778649324985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1946480470154371532433313 1459860352615778649324985)
          ·
            refine ⟨1094895264461833986993739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1459860352615778649324985 1094895264461833986993739)
            ·
              refine ⟨1642342896692750980490609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1094895264461833986993739 1642342896692750980490609)
              ·
                refine ⟨1231757172519563235367957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1642342896692750980490609 1231757172519563235367957)
                ·
                  refine ⟨57738617461854526657873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1231757172519563235367957 57738617461854526657873)
                  ·
                    rfl

theorem cell23_1012010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 1, 2, 6].length) (baseStart_1012010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1012010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1012010 prefixEnd_1012010 := by exact prefixLift 1012010
  have htrace : WordTrace (prefixWord ++ tailWord_1012010) baseStart_1012010 baseEnd_1012010 := by
    simpa [prefixWord, tailWord_1012010, baseEnd_1012010] using wordTrace_append hprefix tailTrace_1012010
  have hstable : (prefixWord ++ tailWord_1012010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012010).length < 2 ^ (prefixWord ++ tailWord_1012010).sum := by decide
  have hdescent : baseEnd_1012010 < baseStart_1012010 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012020 : List Nat := [2, 5, 1, 1, 1, 2, 1, 3, 3, 1, 3]
def baseStart_1012020 : Nat := 118140960795 + 1012020 * 2 ^ 59
def prefixEnd_1012020 : Nat := 4983230072969 + 3 ^ 40 * 1012020 * 2
def baseEnd_1012020 : Nat := 519652691963235700795811

theorem tailTrace_1012020 : CollatzResearch.WordTrace tailWord_1012020 prefixEnd_1012020 519652691963235700795811 := by
  unfold tailWord_1012020
  simp only [CollatzResearch.WordTrace]
  refine ⟨18455700896815927050336757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24607601195754569400449009 18455700896815927050336757)
  ·
    refine ⟨1730221959076493160969071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18455700896815927050336757 1730221959076493160969071)
    ·
      refine ⟨2595332938614739741453607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1730221959076493160969071 2595332938614739741453607)
      ·
        refine ⟨3892999407922109612180411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2595332938614739741453607 3892999407922109612180411)
        ·
          refine ⟨5839499111883164418270617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3892999407922109612180411 5839499111883164418270617)
          ·
            refine ⟨4379624333912373313702963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5839499111883164418270617 4379624333912373313702963)
            ·
              refine ⟨6569436500868559970554445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4379624333912373313702963 6569436500868559970554445)
              ·
                refine ⟨2463538687825709988957917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6569436500868559970554445 2463538687825709988957917)
                ·
                  refine ⟨923827007934641245859219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2463538687825709988957917 923827007934641245859219)
                  ·
                    refine ⟨1385740511901961868788829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 923827007934641245859219 1385740511901961868788829)
                    ·
                      refine ⟨519652691963235700795811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1385740511901961868788829 519652691963235700795811)
                      ·
                        rfl

theorem cell23_1012020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 3, 3, 1, 3].length) (baseStart_1012020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1012020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1012020 prefixEnd_1012020 := by exact prefixLift 1012020
  have htrace : WordTrace (prefixWord ++ tailWord_1012020) baseStart_1012020 baseEnd_1012020 := by
    simpa [prefixWord, tailWord_1012020, baseEnd_1012020] using wordTrace_append hprefix tailTrace_1012020
  have hstable : (prefixWord ++ tailWord_1012020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012020).length < 2 ^ (prefixWord ++ tailWord_1012020).sum := by decide
  have hdescent : baseEnd_1012020 < baseStart_1012020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012043 : List Nat := [1, 1, 1, 1, 3, 1, 1, 5, 5, 2, 2]
def baseStart_1012043 : Nat := 118140960795 + 1012043 * 2 ^ 59
def prefixEnd_1012043 : Nat := 4983230072969 + 3 ^ 40 * 1012043 * 2
def baseEnd_1012043 : Nat := 519664502018289110808205

theorem tailTrace_1012043 : CollatzResearch.WordTrace tailWord_1012043 prefixEnd_1012043 519664502018289110808205 := by
  unfold tailWord_1012043
  simp only [CollatzResearch.WordTrace]
  refine ⟨36912240672548529028760783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24608160448365686019173855 36912240672548529028760783)
  ·
    refine ⟨55368361008822793543141175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36912240672548529028760783 55368361008822793543141175)
    ·
      refine ⟨83052541513234190314711763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55368361008822793543141175 83052541513234190314711763)
      ·
        refine ⟨124578812269851285472067645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83052541513234190314711763 124578812269851285472067645)
        ·
          refine ⟨46717054601194232052025367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124578812269851285472067645 46717054601194232052025367)
          ·
            refine ⟨70075581901791348078038051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46717054601194232052025367 70075581901791348078038051)
            ·
              refine ⟨105113372852687022117057077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70075581901791348078038051 105113372852687022117057077)
              ·
                refine ⟨9854378704939408323474101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 105113372852687022117057077 9854378704939408323474101)
                ·
                  refine ⟨923848003588069530325697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9854378704939408323474101 923848003588069530325697)
                  ·
                    refine ⟨692886002691052147744273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 923848003588069530325697 692886002691052147744273)
                    ·
                      refine ⟨519664502018289110808205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 692886002691052147744273 519664502018289110808205)
                      ·
                        rfl

theorem cell23_1012043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 5, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 5, 5, 2, 2].length) (baseStart_1012043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1012043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1012043 prefixEnd_1012043 := by exact prefixLift 1012043
  have htrace : WordTrace (prefixWord ++ tailWord_1012043) baseStart_1012043 baseEnd_1012043 := by
    simpa [prefixWord, tailWord_1012043, baseEnd_1012043] using wordTrace_append hprefix tailTrace_1012043
  have hstable : (prefixWord ++ tailWord_1012043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012043).length < 2 ^ (prefixWord ++ tailWord_1012043).sum := by decide
  have hdescent : baseEnd_1012043 < baseStart_1012043 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012063 : List Nat := [1, 1, 2, 3, 1, 2, 4, 3, 1, 2, 3]
def baseStart_1012063 : Nat := 118140960795 + 1012063 * 2 ^ 59
def prefixEnd_1012063 : Nat := 4983230072969 + 3 ^ 40 * 1012063 * 2
def baseEnd_1012063 : Nat := 519674771631379032558113

theorem tailTrace_1012063 : CollatzResearch.WordTrace tailWord_1012063 prefixEnd_1012063 519674771631379032558113 := by
  unfold tailWord_1012063
  simp only [CollatzResearch.WordTrace]
  refine ⟨36912970132476072444488843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24608646754984048296325895 36912970132476072444488843)
  ·
    refine ⟨55369455198714108666733265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36912970132476072444488843 55369455198714108666733265)
    ·
      refine ⟨41527091399035581500049949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55369455198714108666733265 41527091399035581500049949)
      ·
        refine ⟨15572659274638343062518731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41527091399035581500049949 15572659274638343062518731)
        ·
          refine ⟨23358988911957514593778097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15572659274638343062518731 23358988911957514593778097)
          ·
            refine ⟨17519241683968135945333573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23358988911957514593778097 17519241683968135945333573)
            ·
              refine ⟨3284857815744025489750045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17519241683968135945333573 3284857815744025489750045)
              ·
                refine ⟨1231821680904009558656267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3284857815744025489750045 1231821680904009558656267)
                ·
                  refine ⟨1847732521356014337984401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1231821680904009558656267 1847732521356014337984401)
                  ·
                    refine ⟨1385799391017010753488301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1847732521356014337984401 1385799391017010753488301)
                    ·
                      refine ⟨519674771631379032558113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1385799391017010753488301 519674771631379032558113)
                      ·
                        rfl

theorem cell23_1012063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 3, 1, 2, 3].length) (baseStart_1012063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1012063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1012063 prefixEnd_1012063 := by exact prefixLift 1012063
  have htrace : WordTrace (prefixWord ++ tailWord_1012063) baseStart_1012063 baseEnd_1012063 := by
    simpa [prefixWord, tailWord_1012063, baseEnd_1012063] using wordTrace_append hprefix tailTrace_1012063
  have hstable : (prefixWord ++ tailWord_1012063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012063).length < 2 ^ (prefixWord ++ tailWord_1012063).sum := by decide
  have hdescent : baseEnd_1012063 < baseStart_1012063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012066 : List Nat := [3, 3, 2, 1, 1, 2, 11]
def baseStart_1012066 : Nat := 118140960795 + 1012066 * 2 ^ 59
def prefixEnd_1012066 : Nat := 4983230072969 + 3 ^ 40 * 1012066 * 2
def baseEnd_1012066 : Nat := 6415756939177068158279

theorem tailTrace_1012066 : CollatzResearch.WordTrace tailWord_1012066 prefixEnd_1012066 6415756939177068158279 := by
  unfold tailWord_1012066
  simp only [CollatzResearch.WordTrace]
  refine ⟨9228269887866300989212013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24608719700976802637898701 9228269887866300989212013)
  ·
    refine ⟨3460601207949862870954505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9228269887866300989212013 3460601207949862870954505)
    ·
      refine ⟨2595450905962397153215879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3460601207949862870954505 2595450905962397153215879)
      ·
        refine ⟨3893176358943595729823819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2595450905962397153215879 3893176358943595729823819)
        ·
          refine ⟨5839764538415393594735729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3893176358943595729823819 5839764538415393594735729)
          ·
            refine ⟨4379823403811545196051797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5839764538415393594735729 4379823403811545196051797)
            ·
              refine ⟨6415756939177068158279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 4379823403811545196051797 6415756939177068158279)
              ·
                rfl

theorem cell23_1012066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 11].length) (baseStart_1012066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1012066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1012066 prefixEnd_1012066 := by exact prefixLift 1012066
  have htrace : WordTrace (prefixWord ++ tailWord_1012066) baseStart_1012066 baseEnd_1012066 := by
    simpa [prefixWord, tailWord_1012066, baseEnd_1012066] using wordTrace_append hprefix tailTrace_1012066
  have hstable : (prefixWord ++ tailWord_1012066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012066).length < 2 ^ (prefixWord ++ tailWord_1012066).sum := by decide
  have hdescent : baseEnd_1012066 < baseStart_1012066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012097 : List Nat := [1, 2, 4, 3, 1, 3, 1, 2, 1, 2, 3]
def baseStart_1012097 : Nat := 118140960795 + 1012097 * 2 ^ 59
def prefixEnd_1012097 : Nat := 4983230072969 + 3 ^ 40 * 1012097 * 2
def baseEnd_1012097 : Nat := 519692229973631899532957

theorem tailTrace_1012097 : CollatzResearch.WordTrace tailWord_1012097 prefixEnd_1012097 519692229973631899532957 := by
  unfold tailWord_1012097
  simp only [CollatzResearch.WordTrace]
  refine ⟨36914210214352896251226545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24609473476235264167484363 36914210214352896251226545)
  ·
    refine ⟨27685657660764672188419909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36914210214352896251226545 27685657660764672188419909)
    ·
      refine ⟨5191060811393376035328733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27685657660764672188419909 5191060811393376035328733)
      ·
        refine ⟨1946647804272516013248275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5191060811393376035328733 1946647804272516013248275)
        ·
          refine ⟨2919971706408774019872413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1946647804272516013248275 2919971706408774019872413)
          ·
            refine ⟨1094989389903290257452155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2919971706408774019872413 1094989389903290257452155)
            ·
              refine ⟨1642484084854935386178233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1094989389903290257452155 1642484084854935386178233)
              ·
                refine ⟨1231863063641201539633675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1642484084854935386178233 1231863063641201539633675)
                ·
                  refine ⟨1847794595461802309450513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1231863063641201539633675 1847794595461802309450513)
                  ·
                    refine ⟨1385845946596351732087885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1847794595461802309450513 1385845946596351732087885)
                    ·
                      refine ⟨519692229973631899532957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1385845946596351732087885 519692229973631899532957)
                      ·
                        rfl

theorem cell23_1012097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_1012097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1012097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1012097 prefixEnd_1012097 := by exact prefixLift 1012097
  have htrace : WordTrace (prefixWord ++ tailWord_1012097) baseStart_1012097 baseEnd_1012097 := by
    simpa [prefixWord, tailWord_1012097, baseEnd_1012097] using wordTrace_append hprefix tailTrace_1012097
  have hstable : (prefixWord ++ tailWord_1012097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012097).length < 2 ^ (prefixWord ++ tailWord_1012097).sum := by decide
  have hdescent : baseEnd_1012097 < baseStart_1012097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012110 : List Nat := [4, 1, 1, 4, 1, 2, 1, 2, 1, 3, 3]
def baseStart_1012110 : Nat := 118140960795 + 1012110 * 2 ^ 59
def prefixEnd_1012110 : Nat := 4983230072969 + 3 ^ 40 * 1012110 * 2
def baseEnd_1012110 : Nat := 519698905222140348670397

theorem tailTrace_1012110 : CollatzResearch.WordTrace tailWord_1012110 prefixEnd_1012110 519698905222140348670397 := by
  unfold tailWord_1012110
  simp only [CollatzResearch.WordTrace]
  refine ⟨4614335545413224933931223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24609789575537199647633189 4614335545413224933931223)
  ·
    refine ⟨6921503318119837400896835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4614335545413224933931223 6921503318119837400896835)
    ·
      refine ⟨10382254977179756101345253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6921503318119837400896835 10382254977179756101345253)
      ·
        refine ⟨1946672808221204269002235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10382254977179756101345253 1946672808221204269002235)
        ·
          refine ⟨2920009212331806403503353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1946672808221204269002235 2920009212331806403503353)
          ·
            refine ⟨2190006909248854802627515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2920009212331806403503353 2190006909248854802627515)
            ·
              refine ⟨3285010363873282203941273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2190006909248854802627515 3285010363873282203941273)
              ·
                refine ⟨2463757772904961652955955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3285010363873282203941273 2463757772904961652955955)
                ·
                  refine ⟨3695636659357442479433933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2463757772904961652955955 3695636659357442479433933)
                  ·
                    refine ⟨1385863747259040929787725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3695636659357442479433933 1385863747259040929787725)
                    ·
                      refine ⟨519698905222140348670397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1385863747259040929787725 519698905222140348670397)
                      ·
                        rfl

theorem cell23_1012110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_1012110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1012110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1012110 prefixEnd_1012110 := by exact prefixLift 1012110
  have htrace : WordTrace (prefixWord ++ tailWord_1012110) baseStart_1012110 baseEnd_1012110 := by
    simpa [prefixWord, tailWord_1012110, baseEnd_1012110] using wordTrace_append hprefix tailTrace_1012110
  have hstable : (prefixWord ++ tailWord_1012110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012110).length < 2 ^ (prefixWord ++ tailWord_1012110).sum := by decide
  have hdescent : baseEnd_1012110 < baseStart_1012110 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012133 : List Nat := [1, 3, 1, 2, 1, 1, 3, 2, 3, 4, 2]
def baseStart_1012133 : Nat := 118140960795 + 1012133 * 2 ^ 59
def prefixEnd_1012133 : Nat := 4983230072969 + 3 ^ 40 * 1012133 * 2
def baseEnd_1012133 : Nat := 519710715277193758682791

theorem tailTrace_1012133 : CollatzResearch.WordTrace tailWord_1012133 prefixEnd_1012133 519710715277193758682791 := by
  unfold tailWord_1012133
  simp only [CollatzResearch.WordTrace]
  refine ⟨36915523242222474399537053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24610348828148316266358035 36915523242222474399537053)
  ·
    refine ⟨13843321215833427899826395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36915523242222474399537053 13843321215833427899826395)
    ·
      refine ⟨20764981823750141849739593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13843321215833427899826395 20764981823750141849739593)
      ·
        refine ⟨15573736367812606387304695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20764981823750141849739593 15573736367812606387304695)
        ·
          refine ⟨23360604551718909580957043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15573736367812606387304695 23360604551718909580957043)
          ·
            refine ⟨35040906827578364371435565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23360604551718909580957043 35040906827578364371435565)
            ·
              refine ⟨13140340060341886639288337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35040906827578364371435565 13140340060341886639288337)
              ·
                refine ⟨9855255045256414979466253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13140340060341886639288337 9855255045256414979466253)
                ·
                  refine ⟨3695720641971155617299845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9855255045256414979466253 3695720641971155617299845)
                  ·
                    refine ⟨692947620369591678243721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3695720641971155617299845 692947620369591678243721)
                    ·
                      refine ⟨519710715277193758682791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 692947620369591678243721 519710715277193758682791)
                      ·
                        rfl

theorem cell23_1012133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 2, 3, 4, 2].length) (baseStart_1012133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1012133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1012133 prefixEnd_1012133 := by exact prefixLift 1012133
  have htrace : WordTrace (prefixWord ++ tailWord_1012133) baseStart_1012133 baseEnd_1012133 := by
    simpa [prefixWord, tailWord_1012133, baseEnd_1012133] using wordTrace_append hprefix tailTrace_1012133
  have hstable : (prefixWord ++ tailWord_1012133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012133).length < 2 ^ (prefixWord ++ tailWord_1012133).sum := by decide
  have hdescent : baseEnd_1012133 < baseStart_1012133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012216 : List Nat := [2, 1, 2, 1, 1, 4, 1, 1, 2, 8]
def baseStart_1012216 : Nat := 118140960795 + 1012216 * 2 ^ 59
def prefixEnd_1012216 : Nat := 4983230072969 + 3 ^ 40 * 1012216 * 2
def baseEnd_1012216 : Nat := 173251111390505644648303

theorem tailTrace_1012216 : CollatzResearch.WordTrace tailWord_1012216 prefixEnd_1012216 173251111390505644648303 := by
  unfold tailWord_1012216
  simp only [CollatzResearch.WordTrace]
  refine ⟨18459275250460889787404251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24612367000614519716539001 18459275250460889787404251)
  ·
    refine ⟨27688912875691334681106377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18459275250460889787404251 27688912875691334681106377)
    ·
      refine ⟨20766684656768501010829783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27688912875691334681106377 20766684656768501010829783)
      ·
        refine ⟨31150026985152751516244675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20766684656768501010829783 31150026985152751516244675)
        ·
          refine ⟨46725040477729127274367013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31150026985152751516244675 46725040477729127274367013)
          ·
            refine ⟨8760945089574211363943815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46725040477729127274367013 8760945089574211363943815)
            ·
              refine ⟨13141417634361317045915723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8760945089574211363943815 13141417634361317045915723)
              ·
                refine ⟨19712126451541975568873585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13141417634361317045915723 19712126451541975568873585)
                ·
                  refine ⟨14784094838656481676655189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19712126451541975568873585 14784094838656481676655189)
                  ·
                    refine ⟨173251111390505644648303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 14784094838656481676655189 173251111390505644648303)
                    ·
                      rfl

theorem cell23_1012216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 2, 8].length) (baseStart_1012216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1012216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1012216 prefixEnd_1012216 := by exact prefixLift 1012216
  have htrace : WordTrace (prefixWord ++ tailWord_1012216) baseStart_1012216 baseEnd_1012216 := by
    simpa [prefixWord, tailWord_1012216, baseEnd_1012216] using wordTrace_append hprefix tailTrace_1012216
  have hstable : (prefixWord ++ tailWord_1012216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012216).length < 2 ^ (prefixWord ++ tailWord_1012216).sum := by decide
  have hdescent : baseEnd_1012216 < baseStart_1012216 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012223 : List Nat := [1, 1, 2, 2, 1, 2, 4, 3, 2, 1, 4]
def baseStart_1012223 : Nat := 118140960795 + 1012223 * 2 ^ 59
def prefixEnd_1012223 : Nat := 4983230072969 + 3 ^ 40 * 1012223 * 2
def baseEnd_1012223 : Nat := 519756928536098406557377

theorem tailTrace_1012223 : CollatzResearch.WordTrace tailWord_1012223 prefixEnd_1012223 519756928536098406557377 := by
  unfold tailWord_1012223
  simp only [CollatzResearch.WordTrace]
  refine ⟨36918805811896419770313323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24612537207930946513542215 36918805811896419770313323)
  ·
    refine ⟨55378208717844629655469985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36918805811896419770313323 55378208717844629655469985)
    ·
      refine ⟨41533656538383472241602489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55378208717844629655469985 41533656538383472241602489)
      ·
        refine ⟨31150242403787604181201867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41533656538383472241602489 31150242403787604181201867)
        ·
          refine ⟨46725363605681406271802801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31150242403787604181201867 46725363605681406271802801)
          ·
            refine ⟨35044022704261054703852101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46725363605681406271802801 35044022704261054703852101)
            ·
              refine ⟨6570754257048947756972269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35044022704261054703852101 6570754257048947756972269)
              ·
                refine ⟨2464032846393355408864601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6570754257048947756972269 2464032846393355408864601)
                ·
                  refine ⟨1848024634795016556648451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2464032846393355408864601 1848024634795016556648451)
                  ·
                    refine ⟨2772036952192524834972677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1848024634795016556648451 2772036952192524834972677)
                    ·
                      refine ⟨519756928536098406557377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2772036952192524834972677 519756928536098406557377)
                      ·
                        rfl

theorem cell23_1012223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 3, 2, 1, 4].length) (baseStart_1012223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1012223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1012223 prefixEnd_1012223 := by exact prefixLift 1012223
  have htrace : WordTrace (prefixWord ++ tailWord_1012223) baseStart_1012223 baseEnd_1012223 := by
    simpa [prefixWord, tailWord_1012223, baseEnd_1012223] using wordTrace_append hprefix tailTrace_1012223
  have hstable : (prefixWord ++ tailWord_1012223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012223).length < 2 ^ (prefixWord ++ tailWord_1012223).sum := by decide
  have hdescent : baseEnd_1012223 < baseStart_1012223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012237 : List Nat := [1, 7, 1, 1, 1, 1, 1, 1, 4, 5]
def baseStart_1012237 : Nat := 118140960795 + 1012237 * 2 ^ 59
def prefixEnd_1012237 : Nat := 4983230072969 + 3 ^ 40 * 1012237 * 2
def baseEnd_1012237 : Nat := 173254705755087117260771

theorem tailTrace_1012237 : CollatzResearch.WordTrace tailWord_1012237 prefixEnd_1012237 173254705755087117260771 := by
  unfold tailWord_1012237
  simp only [CollatzResearch.WordTrace]
  refine ⟨36919316433845700161322965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24612877622563800107548643 36919316433845700161322965)
  ·
    refine ⟨865296478918258597531007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 36919316433845700161322965 865296478918258597531007)
    ·
      refine ⟨1297944718377387896296511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 865296478918258597531007 1297944718377387896296511)
      ·
        refine ⟨1946917077566081844444767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1297944718377387896296511 1946917077566081844444767)
        ·
          refine ⟨2920375616349122766667151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1946917077566081844444767 2920375616349122766667151)
          ·
            refine ⟨4380563424523684150000727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2920375616349122766667151 4380563424523684150000727)
            ·
              refine ⟨6570845136785526225001091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4380563424523684150000727 6570845136785526225001091)
              ·
                refine ⟨9856267705178289337501637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6570845136785526225001091 9856267705178289337501637)
                ·
                  refine ⟨1848050194720929250781557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9856267705178289337501637 1848050194720929250781557)
                  ·
                    refine ⟨173254705755087117260771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1848050194720929250781557 173254705755087117260771)
                    ·
                      rfl

theorem cell23_1012237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_1012237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1012237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1012237 prefixEnd_1012237 := by exact prefixLift 1012237
  have htrace : WordTrace (prefixWord ++ tailWord_1012237) baseStart_1012237 baseEnd_1012237 := by
    simpa [prefixWord, tailWord_1012237, baseEnd_1012237] using wordTrace_append hprefix tailTrace_1012237
  have hstable : (prefixWord ++ tailWord_1012237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012237).length < 2 ^ (prefixWord ++ tailWord_1012237).sum := by decide
  have hdescent : baseEnd_1012237 < baseStart_1012237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012250 : List Nat := [3, 1, 1, 3, 1, 1, 5, 1, 3, 4]
def baseStart_1012250 : Nat := 118140960795 + 1012250 * 2 ^ 59
def prefixEnd_1012250 : Nat := 4983230072969 + 3 ^ 40 * 1012250 * 2
def baseEnd_1012250 : Nat := 173256930837923266973251

theorem tailTrace_1012250 : CollatzResearch.WordTrace tailWord_1012250 prefixEnd_1012250 173256930837923266973251 := by
  unfold tailWord_1012250
  simp only [CollatzResearch.WordTrace]
  refine ⟨9229947645699650845386551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24613193721865735587697469 9229947645699650845386551)
  ·
    refine ⟨13844921468549476268079827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9229947645699650845386551 13844921468549476268079827)
    ·
      refine ⟨20767382202824214402119741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13844921468549476268079827 20767382202824214402119741)
      ·
        refine ⟨7787768326059080400794903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20767382202824214402119741 7787768326059080400794903)
        ·
          refine ⟨11681652489088620601192355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7787768326059080400794903 11681652489088620601192355)
          ·
            refine ⟨17522478733632930901788533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11681652489088620601192355 17522478733632930901788533)
            ·
              refine ⟨1642732381278087272042675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17522478733632930901788533 1642732381278087272042675)
              ·
                refine ⟨2464098571917130908064013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1642732381278087272042675 2464098571917130908064013)
                ·
                  refine ⟨924036964468924090524005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2464098571917130908064013 924036964468924090524005)
                  ·
                    refine ⟨173256930837923266973251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 924036964468924090524005 173256930837923266973251)
                    ·
                      rfl

theorem cell23_1012250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5, 1, 3, 4].length) (baseStart_1012250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1012250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1012250 prefixEnd_1012250 := by exact prefixLift 1012250
  have htrace : WordTrace (prefixWord ++ tailWord_1012250) baseStart_1012250 baseEnd_1012250 := by
    simpa [prefixWord, tailWord_1012250, baseEnd_1012250] using wordTrace_append hprefix tailTrace_1012250
  have hstable : (prefixWord ++ tailWord_1012250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012250).length < 2 ^ (prefixWord ++ tailWord_1012250).sum := by decide
  have hdescent : baseEnd_1012250 < baseStart_1012250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012273 : List Nat := [1, 2, 2, 3, 1, 1, 2, 1, 2, 5, 3]
def baseStart_1012273 : Nat := 118140960795 + 1012273 * 2 ^ 59
def prefixEnd_1012273 : Nat := 4983230072969 + 3 ^ 40 * 1012273 * 2
def baseEnd_1012273 : Nat := 519782602568823210932147

theorem tailTrace_1012273 : CollatzResearch.WordTrace tailWord_1012273 prefixEnd_1012273 519782602568823210932147 := by
  unfold tailWord_1012273
  simp only [CollatzResearch.WordTrace]
  refine ⟨36920629461715278309633473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24613752974476852206422315 36920629461715278309633473)
  ·
    refine ⟨27690472096286458732225105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36920629461715278309633473 27690472096286458732225105)
    ·
      refine ⟨20767854072214844049168829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27690472096286458732225105 20767854072214844049168829)
      ·
        refine ⟨7787945277080566518438311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20767854072214844049168829 7787945277080566518438311)
        ·
          refine ⟨11681917915620849777657467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7787945277080566518438311 11681917915620849777657467)
          ·
            refine ⟨17522876873431274666486201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11681917915620849777657467 17522876873431274666486201)
            ·
              refine ⟨13142157655073455999864651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17522876873431274666486201 13142157655073455999864651)
              ·
                refine ⟨19713236482610183999796977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13142157655073455999864651 19713236482610183999796977)
                ·
                  refine ⟨14784927361957637999847733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19713236482610183999796977 14784927361957637999847733)
                  ·
                    refine ⟨1386086940183528562485725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14784927361957637999847733 1386086940183528562485725)
                    ·
                      refine ⟨519782602568823210932147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1386086940183528562485725 519782602568823210932147)
                      ·
                        rfl

theorem cell23_1012273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 2, 5, 3].length) (baseStart_1012273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1012273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1012273 prefixEnd_1012273 := by exact prefixLift 1012273
  have htrace : WordTrace (prefixWord ++ tailWord_1012273) baseStart_1012273 baseEnd_1012273 := by
    simpa [prefixWord, tailWord_1012273, baseEnd_1012273] using wordTrace_append hprefix tailTrace_1012273
  have hstable : (prefixWord ++ tailWord_1012273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012273).length < 2 ^ (prefixWord ++ tailWord_1012273).sum := by decide
  have hdescent : baseEnd_1012273 < baseStart_1012273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012294 : List Nat := [6, 1, 1, 1, 2, 1, 2, 2, 2, 2, 3]
def baseStart_1012294 : Nat := 118140960795 + 1012294 * 2 ^ 59
def prefixEnd_1012294 : Nat := 4983230072969 + 3 ^ 40 * 1012294 * 2
def baseEnd_1012294 : Nat := 519793385662567628769551

theorem tailTrace_1012294 : CollatzResearch.WordTrace tailWord_1012294 prefixEnd_1012294 519793385662567628769551 := by
  unfold tailWord_1012294
  simp only [CollatzResearch.WordTrace]
  refine ⟨1153793606082474965504623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 24614263596426132597431957 1153793606082474965504623)
  ·
    refine ⟨1730690409123712448256935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1153793606082474965504623 1730690409123712448256935)
    ·
      refine ⟨2596035613685568672385403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1730690409123712448256935 2596035613685568672385403)
      ·
        refine ⟨3894053420528353008578105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2596035613685568672385403 3894053420528353008578105)
        ·
          refine ⟨2920540065396264756433579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3894053420528353008578105 2920540065396264756433579)
          ·
            refine ⟨4380810098094397134650369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2920540065396264756433579 4380810098094397134650369)
            ·
              refine ⟨3285607573570797850987777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4380810098094397134650369 3285607573570797850987777)
              ·
                refine ⟨2464205680178098388240833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3285607573570797850987777 2464205680178098388240833)
                ·
                  refine ⟨1848154260133573791180625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2464205680178098388240833 1848154260133573791180625)
                  ·
                    refine ⟨1386115695100180343385469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1848154260133573791180625 1386115695100180343385469)
                    ·
                      refine ⟨519793385662567628769551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1386115695100180343385469 519793385662567628769551)
                      ·
                        rfl

theorem cell23_1012294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 2, 2, 2, 3].length) (baseStart_1012294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1012294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1012294 prefixEnd_1012294 := by exact prefixLift 1012294
  have htrace : WordTrace (prefixWord ++ tailWord_1012294) baseStart_1012294 baseEnd_1012294 := by
    simpa [prefixWord, tailWord_1012294, baseEnd_1012294] using wordTrace_append hprefix tailTrace_1012294
  have hstable : (prefixWord ++ tailWord_1012294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012294).length < 2 ^ (prefixWord ++ tailWord_1012294).sum := by decide
  have hdescent : baseEnd_1012294 < baseStart_1012294 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012301 : List Nat := [1, 6, 1, 1, 2, 1, 4, 2, 1, 4]
def baseStart_1012301 : Nat := 118140960795 + 1012301 * 2 ^ 59
def prefixEnd_1012301 : Nat := 4983230072969 + 3 ^ 40 * 1012301 * 2
def baseEnd_1012301 : Nat := 173265660009049700460673

theorem tailTrace_1012301 : CollatzResearch.WordTrace tailWord_1012301 prefixEnd_1012301 173265660009049700460673 := by
  unfold tailWord_1012301
  simp only [CollatzResearch.WordTrace]
  refine ⟨36921650705613839091652757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24614433803742559394435171 36921650705613839091652757)
  ·
    refine ⟨1730702376825648707421223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 36921650705613839091652757 1730702376825648707421223)
    ·
      refine ⟨2596053565238473061131835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1730702376825648707421223 2596053565238473061131835)
      ·
        refine ⟨3894080347857709591697753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2596053565238473061131835 3894080347857709591697753)
        ·
          refine ⟨2920560260893282193773315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3894080347857709591697753 2920560260893282193773315)
          ·
            refine ⟨4380840391339923290659973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2920560260893282193773315 4380840391339923290659973)
            ·
              refine ⟨821407573376235616998745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4380840391339923290659973 821407573376235616998745)
              ·
                refine ⟨616055680032176712749059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 821407573376235616998745 616055680032176712749059)
                ·
                  refine ⟨924083520048265069123589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 616055680032176712749059 924083520048265069123589)
                  ·
                    refine ⟨173265660009049700460673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 924083520048265069123589 173265660009049700460673)
                    ·
                      rfl

theorem cell23_1012301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 4, 2, 1, 4].length) (baseStart_1012301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1012301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1012301 prefixEnd_1012301 := by exact prefixLift 1012301
  have htrace : WordTrace (prefixWord ++ tailWord_1012301) baseStart_1012301 baseEnd_1012301 := by
    simpa [prefixWord, tailWord_1012301, baseEnd_1012301] using wordTrace_append hprefix tailTrace_1012301
  have hstable : (prefixWord ++ tailWord_1012301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012301).length < 2 ^ (prefixWord ++ tailWord_1012301).sum := by decide
  have hdescent : baseEnd_1012301 < baseStart_1012301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012330 : List Nat := [3, 1, 3, 2, 1, 1, 1, 3, 3, 1, 4]
def baseStart_1012330 : Nat := 118140960795 + 1012330 * 2 ^ 59
def prefixEnd_1012330 : Nat := 4983230072969 + 3 ^ 40 * 1012330 * 2
def baseEnd_1012330 : Nat := 519811870966129487919385

theorem tailTrace_1012330 : CollatzResearch.WordTrace tailWord_1012330 prefixEnd_1012330 519811870966129487919385 := by
  unfold tailWord_1012330
  simp only [CollatzResearch.WordTrace]
  refine ⟨9230677105627194261114611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24615138948339184696305629 9230677105627194261114611)
  ·
    refine ⟨13846015658440791391671917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9230677105627194261114611 13846015658440791391671917)
    ·
      refine ⟨5192255871915296771876969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13846015658440791391671917 5192255871915296771876969)
      ·
        refine ⟨3894191903936472578907727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5192255871915296771876969 3894191903936472578907727)
        ·
          refine ⟨5841287855904708868361591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3894191903936472578907727 5841287855904708868361591)
          ·
            refine ⟨8761931783857063302542387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5841287855904708868361591 8761931783857063302542387)
            ·
              refine ⟨13142897675785594953813581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8761931783857063302542387 13142897675785594953813581)
              ·
                refine ⟨4928586628419598107680093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13142897675785594953813581 4928586628419598107680093)
                ·
                  refine ⟨1848219985657349290380035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4928586628419598107680093 1848219985657349290380035)
                  ·
                    refine ⟨2772329978486023935570053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1848219985657349290380035 2772329978486023935570053)
                    ·
                      refine ⟨519811870966129487919385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2772329978486023935570053 519811870966129487919385)
                      ·
                        rfl

theorem cell23_1012330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_1012330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1012330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1012330 prefixEnd_1012330 := by exact prefixLift 1012330
  have htrace : WordTrace (prefixWord ++ tailWord_1012330) baseStart_1012330 baseEnd_1012330 := by
    simpa [prefixWord, tailWord_1012330, baseEnd_1012330] using wordTrace_append hprefix tailTrace_1012330
  have hstable : (prefixWord ++ tailWord_1012330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012330).length < 2 ^ (prefixWord ++ tailWord_1012330).sum := by decide
  have hdescent : baseEnd_1012330 < baseStart_1012330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012334 : List Nat := [4, 1, 2, 2, 2, 1, 3, 1, 2, 3, 2]
def baseStart_1012334 : Nat := 118140960795 + 1012334 * 2 ^ 59
def prefixEnd_1012334 : Nat := 4983230072969 + 3 ^ 40 * 1012334 * 2
def baseEnd_1012334 : Nat := 519813924888747472269367

theorem tailTrace_1012334 : CollatzResearch.WordTrace tailWord_1012334 prefixEnd_1012334 519813924888747472269367 := by
  unfold tailWord_1012334
  simp only [CollatzResearch.WordTrace]
  refine ⟨4615356789311785715950507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24615236209662857151736037 4615356789311785715950507)
  ·
    refine ⟨6923035183967678573925761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4615356789311785715950507 6923035183967678573925761)
    ·
      refine ⟨5192276387975758930444321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6923035183967678573925761 5192276387975758930444321)
      ·
        refine ⟨3894207290981819197833241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5192276387975758930444321 3894207290981819197833241)
        ·
          refine ⟨2920655468236364398374931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3894207290981819197833241 2920655468236364398374931)
          ·
            refine ⟨4380983202354546597562397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2920655468236364398374931 4380983202354546597562397)
            ·
              refine ⟨1642868700882954974085899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4380983202354546597562397 1642868700882954974085899)
              ·
                refine ⟨2464303051324432461128849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1642868700882954974085899 2464303051324432461128849)
                ·
                  refine ⟨1848227288493324345846637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2464303051324432461128849 1848227288493324345846637)
                  ·
                    refine ⟨693085233184996629692489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1848227288493324345846637 693085233184996629692489)
                    ·
                      refine ⟨519813924888747472269367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 693085233184996629692489 519813924888747472269367)
                      ·
                        rfl

theorem cell23_1012334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 3, 1, 2, 3, 2].length) (baseStart_1012334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1012334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1012334 prefixEnd_1012334 := by exact prefixLift 1012334
  have htrace : WordTrace (prefixWord ++ tailWord_1012334) baseStart_1012334 baseEnd_1012334 := by
    simpa [prefixWord, tailWord_1012334, baseEnd_1012334] using wordTrace_append hprefix tailTrace_1012334
  have hstable : (prefixWord ++ tailWord_1012334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012334).length < 2 ^ (prefixWord ++ tailWord_1012334).sum := by decide
  have hdescent : baseEnd_1012334 < baseStart_1012334 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012353 : List Nat := [1, 2, 4, 2, 1, 1, 12]
def baseStart_1012353 : Nat := 118140960795 + 1012353 * 2 ^ 59
def prefixEnd_1012353 : Nat := 4983230072969 + 3 ^ 40 * 1012353 * 2
def baseEnd_1012353 : Nat := 6417576308903492567059

theorem tailTrace_1012353 : CollatzResearch.WordTrace tailWord_1012353 prefixEnd_1012353 6417576308903492567059 := by
  unfold tailWord_1012353
  simp only [CollatzResearch.WordTrace]
  refine ⟨36923547301425451972545713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24615698200950301315030475 36923547301425451972545713)
  ·
    refine ⟨27692660476069088979409285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36923547301425451972545713 27692660476069088979409285)
    ·
      refine ⟨5192373839262954183639241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27692660476069088979409285 5192373839262954183639241)
      ·
        refine ⟨3894280379447215637729431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5192373839262954183639241 3894280379447215637729431)
        ·
          refine ⟨5841420569170823456594147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3894280379447215637729431 5841420569170823456594147)
          ·
            refine ⟨8762130853756235184891221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5841420569170823456594147 8762130853756235184891221)
            ·
              refine ⟨6417576308903492567059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 8762130853756235184891221 6417576308903492567059)
              ·
                rfl

theorem cell23_1012353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 12].length) (baseStart_1012353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1012353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1012353 prefixEnd_1012353 := by exact prefixLift 1012353
  have htrace : WordTrace (prefixWord ++ tailWord_1012353) baseStart_1012353 baseEnd_1012353 := by
    simpa [prefixWord, tailWord_1012353, baseEnd_1012353] using wordTrace_append hprefix tailTrace_1012353
  have hstable : (prefixWord ++ tailWord_1012353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012353).length < 2 ^ (prefixWord ++ tailWord_1012353).sum := by decide
  have hdescent : baseEnd_1012353 < baseStart_1012353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012357 : List Nat := [1, 3, 1, 1, 4, 2, 3, 2, 2, 4]
def baseStart_1012357 : Nat := 118140960795 + 1012357 * 2 ^ 59
def prefixEnd_1012357 : Nat := 4983230072969 + 3 ^ 40 * 1012357 * 2
def baseEnd_1012357 : Nat := 173275244981266960760587

theorem tailTrace_1012357 : CollatzResearch.WordTrace tailWord_1012357 prefixEnd_1012357 173275244981266960760587 := by
  unfold tailWord_1012357
  simp only [CollatzResearch.WordTrace]
  refine ⟨36923693193410960655691325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24615795462273973770460883 36923693193410960655691325)
  ·
    refine ⟨13846384947529110245884247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36923693193410960655691325 13846384947529110245884247)
    ·
      refine ⟨20769577421293665368826371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13846384947529110245884247 20769577421293665368826371)
      ·
        refine ⟨31154366131940498053239557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20769577421293665368826371 31154366131940498053239557)
        ·
          refine ⟨5841443649738843384982417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31154366131940498053239557 5841443649738843384982417)
          ·
            refine ⟨4381082737304132538736813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5841443649738843384982417 4381082737304132538736813)
            ·
              refine ⟨1642906026489049702026305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4381082737304132538736813 1642906026489049702026305)
              ·
                refine ⟨1232179519866787276519729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1642906026489049702026305 1232179519866787276519729)
                ·
                  refine ⟨924134639900090457389797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1232179519866787276519729 924134639900090457389797)
                  ·
                    refine ⟨173275244981266960760587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 924134639900090457389797 173275244981266960760587)
                    ·
                      rfl

theorem cell23_1012357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 3, 2, 2, 4].length) (baseStart_1012357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1012357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1012357 prefixEnd_1012357 := by exact prefixLift 1012357
  have htrace : WordTrace (prefixWord ++ tailWord_1012357) baseStart_1012357 baseEnd_1012357 := by
    simpa [prefixWord, tailWord_1012357, baseEnd_1012357] using wordTrace_append hprefix tailTrace_1012357
  have hstable : (prefixWord ++ tailWord_1012357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012357).length < 2 ^ (prefixWord ++ tailWord_1012357).sum := by decide
  have hdescent : baseEnd_1012357 < baseStart_1012357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012384 : List Nat := [2, 1, 1, 4, 4, 1, 2, 2, 1, 2, 3]
def baseStart_1012384 : Nat := 118140960795 + 1012384 * 2 ^ 59
def prefixEnd_1012384 : Nat := 4983230072969 + 3 ^ 40 * 1012384 * 2
def baseEnd_1012384 : Nat := 519839598921472276644137

theorem tailTrace_1012384 : CollatzResearch.WordTrace tailWord_1012384 prefixEnd_1012384 519839598921472276644137 := by
  unfold tailWord_1012384
  simp only [CollatzResearch.WordTrace]
  refine ⟨18462338982156572133462103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24616451976208762844616137 18462338982156572133462103)
  ·
    refine ⟨27693508473234858200193155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18462338982156572133462103 27693508473234858200193155)
    ·
      refine ⟨41540262709852287300289733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27693508473234858200193155 41540262709852287300289733)
      ·
        refine ⟨7788799258097303868804325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41540262709852287300289733 7788799258097303868804325)
        ·
          refine ⟨1460399860893244475400811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7788799258097303868804325 1460399860893244475400811)
          ·
            refine ⟨2190599791339866713101217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1460399860893244475400811 2190599791339866713101217)
            ·
              refine ⟨1642949843504900034825913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2190599791339866713101217 1642949843504900034825913)
              ·
                refine ⟨1232212382628675026119435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1642949843504900034825913 1232212382628675026119435)
                ·
                  refine ⟨1848318573943012539179153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1232212382628675026119435 1848318573943012539179153)
                  ·
                    refine ⟨1386238930457259404384365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1848318573943012539179153 1386238930457259404384365)
                    ·
                      refine ⟨519839598921472276644137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1386238930457259404384365 519839598921472276644137)
                      ·
                        rfl

theorem cell23_1012384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 2, 2, 1, 2, 3].length) (baseStart_1012384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1012384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1012384 prefixEnd_1012384 := by exact prefixLift 1012384
  have htrace : WordTrace (prefixWord ++ tailWord_1012384) baseStart_1012384 baseEnd_1012384 := by
    simpa [prefixWord, tailWord_1012384, baseEnd_1012384] using wordTrace_append hprefix tailTrace_1012384
  have hstable : (prefixWord ++ tailWord_1012384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012384).length < 2 ^ (prefixWord ++ tailWord_1012384).sum := by decide
  have hdescent : baseEnd_1012384 < baseStart_1012384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012393 : List Nat := [1, 2, 1, 1, 1, 1, 2, 5, 2, 2, 5]
def baseStart_1012393 : Nat := 118140960795 + 1012393 * 2 ^ 59
def prefixEnd_1012393 : Nat := 4983230072969 + 3 ^ 40 * 1012393 * 2
def baseEnd_1012393 : Nat := 519844220247362741431595

theorem tailTrace_1012393 : CollatzResearch.WordTrace tailWord_1012393 prefixEnd_1012393 519844220247362741431595 := by
  unfold tailWord_1012393
  simp only [CollatzResearch.WordTrace]
  refine ⟨36925006221280538804001833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24616670814187025869334555 36925006221280538804001833)
  ·
    refine ⟨27693754665960404103001375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36925006221280538804001833 27693754665960404103001375)
    ·
      refine ⟨41540631998940606154502063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27693754665960404103001375 41540631998940606154502063)
      ·
        refine ⟨62310947998410909231753095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41540631998940606154502063 62310947998410909231753095)
        ·
          refine ⟨93466421997616363847629643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62310947998410909231753095 93466421997616363847629643)
          ·
            refine ⟨140199632996424545771444465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93466421997616363847629643 140199632996424545771444465)
            ·
              refine ⟨105149724747318409328583349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140199632996424545771444465 105149724747318409328583349)
              ·
                refine ⟨9857786695061100874554689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 105149724747318409328583349 9857786695061100874554689)
                ·
                  refine ⟨7393340021295825655916017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9857786695061100874554689 7393340021295825655916017)
                  ·
                    refine ⟨5545005015971869241937013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7393340021295825655916017 5545005015971869241937013)
                    ·
                      refine ⟨519844220247362741431595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5545005015971869241937013 519844220247362741431595)
                      ·
                        rfl

theorem cell23_1012393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 5, 2, 2, 5].length) (baseStart_1012393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1012393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1012393 prefixEnd_1012393 := by exact prefixLift 1012393
  have htrace : WordTrace (prefixWord ++ tailWord_1012393) baseStart_1012393 baseEnd_1012393 := by
    simpa [prefixWord, tailWord_1012393, baseEnd_1012393] using wordTrace_append hprefix tailTrace_1012393
  have hstable : (prefixWord ++ tailWord_1012393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012393).length < 2 ^ (prefixWord ++ tailWord_1012393).sum := by decide
  have hdescent : baseEnd_1012393 < baseStart_1012393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012414 : List Nat := [4, 2, 1, 1, 2, 1, 2, 4, 2, 1, 3]
def baseStart_1012414 : Nat := 118140960795 + 1012414 * 2 ^ 59
def prefixEnd_1012414 : Nat := 4983230072969 + 3 ^ 40 * 1012414 * 2
def baseEnd_1012414 : Nat := 519855003341107159268999

theorem tailTrace_1012414 : CollatzResearch.WordTrace tailWord_1012414 prefixEnd_1012414 519855003341107159268999 := by
  unfold tailWord_1012414
  simp only [CollatzResearch.WordTrace]
  refine ⟨4615721519275557423814537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24617181436136306260344197 4615721519275557423814537)
  ·
    refine ⟨3461791139456668067860903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4615721519275557423814537 3461791139456668067860903)
    ·
      refine ⟨5192686709185002101791355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3461791139456668067860903 5192686709185002101791355)
      ·
        refine ⟨7789030063777503152687033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5192686709185002101791355 7789030063777503152687033)
        ·
          refine ⟨5841772547833127364515275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7789030063777503152687033 5841772547833127364515275)
          ·
            refine ⟨8762658821749691046772913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5841772547833127364515275 8762658821749691046772913)
            ·
              refine ⟨6571994116312268285079685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8762658821749691046772913 6571994116312268285079685)
              ·
                refine ⟨1232248896808550303452441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6571994116312268285079685 1232248896808550303452441)
                ·
                  refine ⟨924186672606412727589331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1232248896808550303452441 924186672606412727589331)
                  ·
                    refine ⟨1386280008909619091383997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 924186672606412727589331 1386280008909619091383997)
                    ·
                      refine ⟨519855003341107159268999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1386280008909619091383997 519855003341107159268999)
                      ·
                        rfl

theorem cell23_1012414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 4, 2, 1, 3].length) (baseStart_1012414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1012414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1012414 prefixEnd_1012414 := by exact prefixLift 1012414
  have htrace : WordTrace (prefixWord ++ tailWord_1012414) baseStart_1012414 baseEnd_1012414 := by
    simpa [prefixWord, tailWord_1012414, baseEnd_1012414] using wordTrace_append hprefix tailTrace_1012414
  have hstable : (prefixWord ++ tailWord_1012414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012414).length < 2 ^ (prefixWord ++ tailWord_1012414).sum := by decide
  have hdescent : baseEnd_1012414 < baseStart_1012414 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012440 : List Nat := [2, 1, 2, 2, 3, 2, 1, 2, 2, 1, 5]
def baseStart_1012440 : Nat := 118140960795 + 1012440 * 2 ^ 59
def prefixEnd_1012440 : Nat := 4983230072969 + 3 ^ 40 * 1012440 * 2
def baseEnd_1012440 : Nat := 519868353838124057543879

theorem tailTrace_1012440 : CollatzResearch.WordTrace tailWord_1012440 prefixEnd_1012440 519868353838124057543879 := by
  unfold tailWord_1012440
  simp only [CollatzResearch.WordTrace]
  refine ⟨18463360226055132915481387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24617813634740177220641849 18463360226055132915481387)
  ·
    refine ⟨27695040339082699373222081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18463360226055132915481387 27695040339082699373222081)
    ·
      refine ⟨20771280254312024529916561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27695040339082699373222081 20771280254312024529916561)
      ·
        refine ⟨15578460190734018397437421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20771280254312024529916561 15578460190734018397437421)
        ·
          refine ⟨5841922571525256899039033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15578460190734018397437421 5841922571525256899039033)
          ·
            refine ⟨4381441928643942674279275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5841922571525256899039033 4381441928643942674279275)
            ·
              refine ⟨6572162892965914011418913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4381441928643942674279275 6572162892965914011418913)
              ·
                refine ⟨4929122169724435508564185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6572162892965914011418913 4929122169724435508564185)
                ·
                  refine ⟨3696841627293326631423139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4929122169724435508564185 3696841627293326631423139)
                  ·
                    refine ⟨5545262440939989947134709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3696841627293326631423139 5545262440939989947134709)
                    ·
                      refine ⟨519868353838124057543879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5545262440939989947134709 519868353838124057543879)
                      ·
                        rfl

theorem cell23_1012440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 2, 2, 1, 5].length) (baseStart_1012440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1012440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1012440 prefixEnd_1012440 := by exact prefixLift 1012440
  have htrace : WordTrace (prefixWord ++ tailWord_1012440) baseStart_1012440 baseEnd_1012440 := by
    simpa [prefixWord, tailWord_1012440, baseEnd_1012440] using wordTrace_append hprefix tailTrace_1012440
  have hstable : (prefixWord ++ tailWord_1012440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012440).length < 2 ^ (prefixWord ++ tailWord_1012440).sum := by decide
  have hdescent : baseEnd_1012440 < baseStart_1012440 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012477 : List Nat := [1, 4, 1, 1, 1, 1, 5, 4, 5]
def baseStart_1012477 : Nat := 118140960795 + 1012477 * 2 ^ 59
def prefixEnd_1012477 : Nat := 4983230072969 + 3 ^ 40 * 1012477 * 2
def baseEnd_1012477 : Nat := 57765261402482268086801

theorem tailTrace_1012477 : CollatzResearch.WordTrace tailWord_1012477 prefixEnd_1012477 57765261402482268086801 := by
  unfold tailWord_1012477
  simp only [CollatzResearch.WordTrace]
  refine ⟨36928069952976221150059685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24618713301984147433373123 36928069952976221150059685)
  ·
    refine ⟨6924013116183041465636191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36928069952976221150059685 6924013116183041465636191)
    ·
      refine ⟨10386019674274562198454287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6924013116183041465636191 10386019674274562198454287)
      ·
        refine ⟨15579029511411843297681431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10386019674274562198454287 15579029511411843297681431)
        ·
          refine ⟨23368544267117764946522147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15579029511411843297681431 23368544267117764946522147)
          ·
            refine ⟨35052816400676647419783221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23368544267117764946522147 35052816400676647419783221)
            ·
              refine ⟨3286201537563435695604677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35052816400676647419783221 3286201537563435695604677)
              ·
                refine ⟨616162788293144192925877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3286201537563435695604677 616162788293144192925877)
                ·
                  refine ⟨57765261402482268086801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 616162788293144192925877 57765261402482268086801)
                  ·
                    rfl

theorem cell23_1012477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 4, 5].length) (baseStart_1012477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1012477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1012477 prefixEnd_1012477 := by exact prefixLift 1012477
  have htrace : WordTrace (prefixWord ++ tailWord_1012477) baseStart_1012477 baseEnd_1012477 := by
    simpa [prefixWord, tailWord_1012477, baseEnd_1012477] using wordTrace_append hprefix tailTrace_1012477
  have hstable : (prefixWord ++ tailWord_1012477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012477).length < 2 ^ (prefixWord ++ tailWord_1012477).sum := by decide
  have hdescent : baseEnd_1012477 < baseStart_1012477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012487 : List Nat := [1, 1, 4, 4, 1, 1, 1, 1, 1, 5, 3]
def baseStart_1012487 : Nat := 118140960795 + 1012487 * 2 ^ 59
def prefixEnd_1012487 : Nat := 4983230072969 + 3 ^ 40 * 1012487 * 2
def baseEnd_1012487 : Nat := 519892487428885373656163

theorem tailTrace_1012487 : CollatzResearch.WordTrace tailWord_1012487 prefixEnd_1012487 519892487428885373656163 := by
  unfold tailWord_1012487
  simp only [CollatzResearch.WordTrace]
  refine ⟨36928434682939992857923715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24618956455293328571949143 36928434682939992857923715)
  ·
    refine ⟨55392652024409989286885573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36928434682939992857923715 55392652024409989286885573)
    ·
      refine ⟨10386122254576872991291045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55392652024409989286885573 10386122254576872991291045)
      ·
        refine ⟨1947397922733163685867071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10386122254576872991291045 1947397922733163685867071)
        ·
          refine ⟨2921096884099745528800607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1947397922733163685867071 2921096884099745528800607)
          ·
            refine ⟨4381645326149618293200911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2921096884099745528800607 4381645326149618293200911)
            ·
              refine ⟨6572467989224427439801367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4381645326149618293200911 6572467989224427439801367)
              ·
                refine ⟨9858701983836641159702051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6572467989224427439801367 9858701983836641159702051)
                ·
                  refine ⟨14788052975754961739553077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9858701983836641159702051 14788052975754961739553077)
                  ·
                    refine ⟨1386379966477027663083101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14788052975754961739553077 1386379966477027663083101)
                    ·
                      refine ⟨519892487428885373656163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1386379966477027663083101 519892487428885373656163)
                      ·
                        rfl

theorem cell23_1012487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_1012487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1012487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1012487 prefixEnd_1012487 := by exact prefixLift 1012487
  have htrace : WordTrace (prefixWord ++ tailWord_1012487) baseStart_1012487 baseEnd_1012487 := by
    simpa [prefixWord, tailWord_1012487, baseEnd_1012487] using wordTrace_append hprefix tailTrace_1012487
  have hstable : (prefixWord ++ tailWord_1012487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012487).length < 2 ^ (prefixWord ++ tailWord_1012487).sum := by decide
  have hdescent : baseEnd_1012487 < baseStart_1012487 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012490 : List Nat := [3, 1, 2, 2, 1, 2, 2, 2, 1, 7]
def baseStart_1012490 : Nat := 118140960795 + 1012490 * 2 ^ 59
def prefixEnd_1012490 : Nat := 4983230072969 + 3 ^ 40 * 1012490 * 2
def baseEnd_1012490 : Nat := 173298009290282953972883

theorem tailTrace_1012490 : CollatzResearch.WordTrace tailWord_1012490 prefixEnd_1012490 173298009290282953972883 := by
  unfold tailWord_1012490
  simp only [CollatzResearch.WordTrace]
  refine ⟨9232136025482281092570731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24619029401286082913521949 9232136025482281092570731)
  ·
    refine ⟨13848204038223421638856097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9232136025482281092570731 13848204038223421638856097)
    ·
      refine ⟨10386153028667566229142073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13848204038223421638856097 10386153028667566229142073)
      ·
        refine ⟨7789614771500674671856555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10386153028667566229142073 7789614771500674671856555)
        ·
          refine ⟨11684422157251012007784833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7789614771500674671856555 11684422157251012007784833)
          ·
            refine ⟨8763316617938259005838625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11684422157251012007784833 8763316617938259005838625)
            ·
              refine ⟨6572487463453694254378969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8763316617938259005838625 6572487463453694254378969)
              ·
                refine ⟨4929365597590270690784227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6572487463453694254378969 4929365597590270690784227)
                ·
                  refine ⟨7394048396385406036176341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4929365597590270690784227 7394048396385406036176341)
                  ·
                    refine ⟨173298009290282953972883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7394048396385406036176341 173298009290282953972883)
                    ·
                      rfl

theorem cell23_1012490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 2, 1, 7].length) (baseStart_1012490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1012490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1012490 prefixEnd_1012490 := by exact prefixLift 1012490
  have htrace : WordTrace (prefixWord ++ tailWord_1012490) baseStart_1012490 baseEnd_1012490 := by
    simpa [prefixWord, tailWord_1012490, baseEnd_1012490] using wordTrace_append hprefix tailTrace_1012490
  have hstable : (prefixWord ++ tailWord_1012490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012490).length < 2 ^ (prefixWord ++ tailWord_1012490).sum := by decide
  have hdescent : baseEnd_1012490 < baseStart_1012490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012522 : List Nat := [3, 1, 4, 3, 2, 1, 1, 2, 2, 2, 2]
def baseStart_1012522 : Nat := 118140960795 + 1012522 * 2 ^ 59
def prefixEnd_1012522 : Nat := 4983230072969 + 3 ^ 40 * 1012522 * 2
def baseEnd_1012522 : Nat := 519910459251792736718503

theorem tailTrace_1012522 : CollatzResearch.WordTrace tailWord_1012522 prefixEnd_1012522 519910459251792736718503 := by
  unfold tailWord_1012522
  simp only [CollatzResearch.WordTrace]
  refine ⟨9232427809453298458861955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24619807491875462556965213 9232427809453298458861955)
  ·
    refine ⟨13848641714179947688292933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9232427809453298458861955 13848641714179947688292933)
    ·
      refine ⟨2596620321408740191554925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13848641714179947688292933 2596620321408740191554925)
      ·
        refine ⟨973732620528277571833097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2596620321408740191554925 973732620528277571833097)
        ·
          refine ⟨730299465396208178874823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 973732620528277571833097 730299465396208178874823)
          ·
            refine ⟨1095449198094312268312235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 730299465396208178874823 1095449198094312268312235)
            ·
              refine ⟨1643173797141468402468353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1095449198094312268312235 1643173797141468402468353)
              ·
                refine ⟨1232380347856101301851265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1643173797141468402468353 1232380347856101301851265)
                ·
                  refine ⟨924285260892075976388449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1232380347856101301851265 924285260892075976388449)
                  ·
                    refine ⟨693213945669056982291337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 924285260892075976388449 693213945669056982291337)
                    ·
                      refine ⟨519910459251792736718503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 693213945669056982291337 519910459251792736718503)
                      ·
                        rfl

theorem cell23_1012522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_1012522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1012522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1012522 prefixEnd_1012522 := by exact prefixLift 1012522
  have htrace : WordTrace (prefixWord ++ tailWord_1012522) baseStart_1012522 baseEnd_1012522 := by
    simpa [prefixWord, tailWord_1012522, baseEnd_1012522] using wordTrace_append hprefix tailTrace_1012522
  have hstable : (prefixWord ++ tailWord_1012522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012522).length < 2 ^ (prefixWord ++ tailWord_1012522).sum := by decide
  have hdescent : baseEnd_1012522 < baseStart_1012522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012540 : List Nat := [2, 2, 2, 2, 1, 1, 1, 1, 4, 1, 6]
def baseStart_1012540 : Nat := 118140960795 + 1012540 * 2 ^ 59
def prefixEnd_1012540 : Nat := 4983230072969 + 3 ^ 40 * 1012540 * 2
def baseEnd_1012540 : Nat := 519919701903573666293419

theorem tailTrace_1012540 : CollatzResearch.WordTrace tailWord_1012540 prefixEnd_1012540 519919701903573666293419 := by
  unfold tailWord_1012540
  simp only [CollatzResearch.WordTrace]
  refine ⟨18465183875873991454801537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24620245167831988606402049 18465183875873991454801537)
  ·
    refine ⟨13848887906905493591101153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18465183875873991454801537 13848887906905493591101153)
    ·
      refine ⟨10386665930179120193325865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13848887906905493591101153 10386665930179120193325865)
      ·
        refine ⟨7789999447634340144994399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10386665930179120193325865 7789999447634340144994399)
        ·
          refine ⟨11684999171451510217491599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7789999447634340144994399 11684999171451510217491599)
          ·
            refine ⟨17527498757177265326237399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11684999171451510217491599 17527498757177265326237399)
            ·
              refine ⟨26291248135765897989356099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17527498757177265326237399 26291248135765897989356099)
              ·
                refine ⟨39436872203648846984034149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26291248135765897989356099 39436872203648846984034149)
                ·
                  refine ⟨7394413538184158809506403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39436872203648846984034149 7394413538184158809506403)
                  ·
                    refine ⟨11091620307276238214259605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7394413538184158809506403 11091620307276238214259605)
                    ·
                      refine ⟨519919701903573666293419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11091620307276238214259605 519919701903573666293419)
                      ·
                        rfl

theorem cell23_1012540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 4, 1, 6].length) (baseStart_1012540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1012540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1012540 prefixEnd_1012540 := by exact prefixLift 1012540
  have htrace : WordTrace (prefixWord ++ tailWord_1012540) baseStart_1012540 baseEnd_1012540 := by
    simpa [prefixWord, tailWord_1012540, baseEnd_1012540] using wordTrace_append hprefix tailTrace_1012540
  have hstable : (prefixWord ++ tailWord_1012540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012540).length < 2 ^ (prefixWord ++ tailWord_1012540).sum := by decide
  have hdescent : baseEnd_1012540 < baseStart_1012540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012627 : List Nat := [1, 1, 1, 2, 1, 2, 1, 6, 4, 4]
def baseStart_1012627 : Nat := 118140960795 + 1012627 * 2 ^ 59
def prefixEnd_1012627 : Nat := 4983230072969 + 3 ^ 40 * 1012627 * 2
def baseEnd_1012627 : Nat := 173321458240171608635173

theorem tailTrace_1012627 : CollatzResearch.WordTrace tailWord_1012627 prefixEnd_1012627 173321458240171608635173 := by
  unfold tailWord_1012627
  simp only [CollatzResearch.WordTrace]
  refine ⟨36933540902432796768020135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24622360601621864512013423 36933540902432796768020135)
  ·
    refine ⟨55400311353649195152030203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36933540902432796768020135 55400311353649195152030203)
    ·
      refine ⟨83100467030473792728045305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55400311353649195152030203 83100467030473792728045305)
      ·
        refine ⟨62325350272855344546033979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83100467030473792728045305 62325350272855344546033979)
        ·
          refine ⟨93488025409283016819050969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62325350272855344546033979 93488025409283016819050969)
          ·
            refine ⟨70116019056962262614288227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93488025409283016819050969 70116019056962262614288227)
            ·
              refine ⟨105174028585443393921432341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70116019056962262614288227 105174028585443393921432341)
              ·
                refine ⟨4930032589942659090067141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 105174028585443393921432341 4930032589942659090067141)
                ·
                  refine ⟨924381110614248579387589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4930032589942659090067141 924381110614248579387589)
                  ·
                    refine ⟨173321458240171608635173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 924381110614248579387589 173321458240171608635173)
                    ·
                      rfl

theorem cell23_1012627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 6, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 6, 4, 4].length) (baseStart_1012627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1012627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1012627 prefixEnd_1012627 := by exact prefixLift 1012627
  have htrace : WordTrace (prefixWord ++ tailWord_1012627) baseStart_1012627 baseEnd_1012627 := by
    simpa [prefixWord, tailWord_1012627, baseEnd_1012627] using wordTrace_append hprefix tailTrace_1012627
  have hstable : (prefixWord ++ tailWord_1012627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012627).length < 2 ^ (prefixWord ++ tailWord_1012627).sum := by decide
  have hdescent : baseEnd_1012627 < baseStart_1012627 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012628 : List Nat := [2, 4, 2, 1, 1, 1, 2, 5, 1, 1, 3]
def baseStart_1012628 : Nat := 118140960795 + 1012628 * 2 ^ 59
def prefixEnd_1012628 : Nat := 4983230072969 + 3 ^ 40 * 1012628 * 2
def baseEnd_1012628 : Nat := 519964888201169321993015

theorem tailTrace_1012628 : CollatzResearch.WordTrace tailWord_1012628 prefixEnd_1012628 519964888201169321993015 := by
  unfold tailWord_1012628
  simp only [CollatzResearch.WordTrace]
  refine ⟨18466788687714586969403269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24622384916952782625871025 18466788687714586969403269)
  ·
    refine ⟨3462522878946485056763113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18466788687714586969403269 3462522878946485056763113)
    ·
      refine ⟨2596892159209863792572335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3462522878946485056763113 2596892159209863792572335)
      ·
        refine ⟨3895338238814795688858503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2596892159209863792572335 3895338238814795688858503)
        ·
          refine ⟨5843007358222193533287755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3895338238814795688858503 5843007358222193533287755)
          ·
            refine ⟨8764511037333290299931633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5843007358222193533287755 8764511037333290299931633)
            ·
              refine ⟨6573383277999967724948725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8764511037333290299931633 6573383277999967724948725)
              ·
                refine ⟨616254682312496974213943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6573383277999967724948725 616254682312496974213943)
                ·
                  refine ⟨924382023468745461320915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 616254682312496974213943 924382023468745461320915)
                  ·
                    refine ⟨1386573035203118191981373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 924382023468745461320915 1386573035203118191981373)
                    ·
                      refine ⟨519964888201169321993015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1386573035203118191981373 519964888201169321993015)
                      ·
                        rfl

theorem cell23_1012628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 5, 1, 1, 3].length) (baseStart_1012628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1012628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1012628 prefixEnd_1012628 := by exact prefixLift 1012628
  have htrace : WordTrace (prefixWord ++ tailWord_1012628) baseStart_1012628 baseEnd_1012628 := by
    simpa [prefixWord, tailWord_1012628, baseEnd_1012628] using wordTrace_append hprefix tailTrace_1012628
  have hstable : (prefixWord ++ tailWord_1012628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012628).length < 2 ^ (prefixWord ++ tailWord_1012628).sum := by decide
  have hdescent : baseEnd_1012628 < baseStart_1012628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012662 : List Nat := [5, 1, 4, 1, 1, 1, 1, 2, 3, 1, 3]
def baseStart_1012662 : Nat := 118140960795 + 1012662 * 2 ^ 59
def prefixEnd_1012662 : Nat := 4983230072969 + 3 ^ 40 * 1012662 * 2
def baseEnd_1012662 : Nat := 519982346543422188967859

theorem tailTrace_1012662 : CollatzResearch.WordTrace tailWord_1012662 prefixEnd_1012662 519982346543422188967859 := by
  unfold tailWord_1012662
  simp only [CollatzResearch.WordTrace]
  refine ⟨2308426091081624859096515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24623211638203998497029493 2308426091081624859096515)
  ·
    refine ⟨3462639136622437288644773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2308426091081624859096515 3462639136622437288644773)
    ·
      refine ⟨649244838116706991620895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3462639136622437288644773 649244838116706991620895)
      ·
        refine ⟨973867257175060487431343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 649244838116706991620895 973867257175060487431343)
        ·
          refine ⟨1460800885762590731147015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 973867257175060487431343 1460800885762590731147015)
          ·
            refine ⟨2191201328643886096720523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1460800885762590731147015 2191201328643886096720523)
            ·
              refine ⟨3286801992965829145080785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2191201328643886096720523 3286801992965829145080785)
              ·
                refine ⟨2465101494724371858810589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3286801992965829145080785 2465101494724371858810589)
                ·
                  refine ⟨924413060521639447053971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2465101494724371858810589 924413060521639447053971)
                  ·
                    refine ⟨1386619590782459170580957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 924413060521639447053971 1386619590782459170580957)
                    ·
                      refine ⟨519982346543422188967859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1386619590782459170580957 519982346543422188967859)
                      ·
                        rfl

theorem cell23_1012662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_1012662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1012662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1012662 prefixEnd_1012662 := by exact prefixLift 1012662
  have htrace : WordTrace (prefixWord ++ tailWord_1012662) baseStart_1012662 baseEnd_1012662 := by
    simpa [prefixWord, tailWord_1012662, baseEnd_1012662] using wordTrace_append hprefix tailTrace_1012662
  have hstable : (prefixWord ++ tailWord_1012662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012662).length < 2 ^ (prefixWord ++ tailWord_1012662).sum := by decide
  have hdescent : baseEnd_1012662 < baseStart_1012662 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012664 : List Nat := [2, 1, 2, 1, 2, 5, 2, 1, 1, 2, 4]
def baseStart_1012664 : Nat := 118140960795 + 1012664 * 2 ^ 59
def prefixEnd_1012664 : Nat := 4983230072969 + 3 ^ 40 * 1012664 * 2
def baseEnd_1012664 : Nat := 519983373504731181142849

theorem tailTrace_1012664 : CollatzResearch.WordTrace tailWord_1012664 prefixEnd_1012664 519983373504731181142849 := by
  unfold tailWord_1012664
  simp only [CollatzResearch.WordTrace]
  refine ⟨18467445201649376043558523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24623260268865834724744697 18467445201649376043558523)
  ·
    refine ⟨27701167802474064065337785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18467445201649376043558523 27701167802474064065337785)
    ·
      refine ⟨20775875851855548049003339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27701167802474064065337785 20775875851855548049003339)
      ·
        refine ⟨31163813777783322073505009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20775875851855548049003339 31163813777783322073505009)
        ·
          refine ⟨23372860333337491555128757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31163813777783322073505009 23372860333337491555128757)
          ·
            refine ⟨2191205656250389833293321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23372860333337491555128757 2191205656250389833293321)
            ·
              refine ⟨1643404242187792374969991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2191205656250389833293321 1643404242187792374969991)
              ·
                refine ⟨2465106363281688562454987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1643404242187792374969991 2465106363281688562454987)
                ·
                  refine ⟨3697659544922532843682481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2465106363281688562454987 3697659544922532843682481)
                  ·
                    refine ⟨2773244658691899632761861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3697659544922532843682481 2773244658691899632761861)
                    ·
                      refine ⟨519983373504731181142849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2773244658691899632761861 519983373504731181142849)
                      ·
                        rfl

theorem cell23_1012664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 2, 1, 1, 2, 4].length) (baseStart_1012664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1012664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1012664 prefixEnd_1012664 := by exact prefixLift 1012664
  have htrace : WordTrace (prefixWord ++ tailWord_1012664) baseStart_1012664 baseEnd_1012664 := by
    simpa [prefixWord, tailWord_1012664, baseEnd_1012664] using wordTrace_append hprefix tailTrace_1012664
  have hstable : (prefixWord ++ tailWord_1012664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012664).length < 2 ^ (prefixWord ++ tailWord_1012664).sum := by decide
  have hdescent : baseEnd_1012664 < baseStart_1012664 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012684 : List Nat := [2, 2, 1, 4, 1, 1, 1, 4, 1, 3, 3]
def baseStart_1012684 : Nat := 118140960795 + 1012684 * 2 ^ 59
def prefixEnd_1012684 : Nat := 4983230072969 + 3 ^ 40 * 1012684 * 2
def baseEnd_1012684 : Nat := 519993643117821102892757

theorem tailTrace_1012684 : CollatzResearch.WordTrace tailWord_1012684 prefixEnd_1012684 519993643117821102892757 := by
  unfold tailWord_1012684
  simp only [CollatzResearch.WordTrace]
  refine ⟨18467809931613147751422553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24623746575484197001896737 18467809931613147751422553)
  ·
    refine ⟨13850857448709860813566915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18467809931613147751422553 13850857448709860813566915)
    ·
      refine ⟨20776286173064791220350373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13850857448709860813566915 20776286173064791220350373)
      ·
        refine ⟨3895553657449648353815695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20776286173064791220350373 3895553657449648353815695)
        ·
          refine ⟨5843330486174472530723543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3895553657449648353815695 5843330486174472530723543)
          ·
            refine ⟨8764995729261708796085315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5843330486174472530723543 8764995729261708796085315)
            ·
              refine ⟨13147493593892563194127973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8764995729261708796085315 13147493593892563194127973)
              ·
                refine ⟨2465155048854855598898995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13147493593892563194127973 2465155048854855598898995)
                ·
                  refine ⟨3697732573282283398348493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2465155048854855598898995 3697732573282283398348493)
                  ·
                    refine ⟨1386649714980856274380685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3697732573282283398348493 1386649714980856274380685)
                    ·
                      refine ⟨519993643117821102892757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1386649714980856274380685 519993643117821102892757)
                      ·
                        rfl

theorem cell23_1012684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 4, 1, 3, 3].length) (baseStart_1012684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1012684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1012684 prefixEnd_1012684 := by exact prefixLift 1012684
  have htrace : WordTrace (prefixWord ++ tailWord_1012684) baseStart_1012684 baseEnd_1012684 := by
    simpa [prefixWord, tailWord_1012684, baseEnd_1012684] using wordTrace_append hprefix tailTrace_1012684
  have hstable : (prefixWord ++ tailWord_1012684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012684).length < 2 ^ (prefixWord ++ tailWord_1012684).sum := by decide
  have hdescent : baseEnd_1012684 < baseStart_1012684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012718 : List Nat := [4, 1, 2, 1, 4, 2, 1, 1, 1, 3, 3]
def baseStart_1012718 : Nat := 118140960795 + 1012718 * 2 ^ 59
def prefixEnd_1012718 : Nat := 4983230072969 + 3 ^ 40 * 1012718 * 2
def baseEnd_1012718 : Nat := 520011101460073969867601

theorem tailTrace_1012718 : CollatzResearch.WordTrace tailWord_1012718 prefixEnd_1012718 520011101460073969867601 := by
  unfold tailWord_1012718
  simp only [CollatzResearch.WordTrace]
  refine ⟨4617107493137889913697851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24624573296735412873055205 4617107493137889913697851)
  ·
    refine ⟨6925661239706834870546777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4617107493137889913697851 6925661239706834870546777)
    ·
      refine ⟨5194245929780126152910083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6925661239706834870546777 5194245929780126152910083)
      ·
        refine ⟨7791368894670189229365125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5194245929780126152910083 7791368894670189229365125)
        ·
          refine ⟨1460881667750660480505961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7791368894670189229365125 1460881667750660480505961)
          ·
            refine ⟨1095661250812995360379471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1460881667750660480505961 1095661250812995360379471)
            ·
              refine ⟨1643491876219493040569207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1095661250812995360379471 1643491876219493040569207)
              ·
                refine ⟨2465237814329239560853811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1643491876219493040569207 2465237814329239560853811)
                ·
                  refine ⟨3697856721493859341280717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2465237814329239560853811 3697856721493859341280717)
                  ·
                    refine ⟨1386696270560197252980269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3697856721493859341280717 1386696270560197252980269)
                    ·
                      refine ⟨520011101460073969867601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1386696270560197252980269 520011101460073969867601)
                      ·
                        rfl

theorem cell23_1012718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 1, 1, 1, 3, 3].length) (baseStart_1012718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1012718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1012718 prefixEnd_1012718 := by exact prefixLift 1012718
  have htrace : WordTrace (prefixWord ++ tailWord_1012718) baseStart_1012718 baseEnd_1012718 := by
    simpa [prefixWord, tailWord_1012718, baseEnd_1012718] using wordTrace_append hprefix tailTrace_1012718
  have hstable : (prefixWord ++ tailWord_1012718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012718).length < 2 ^ (prefixWord ++ tailWord_1012718).sum := by decide
  have hdescent : baseEnd_1012718 < baseStart_1012718 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012725 : List Nat := [1, 3, 5, 2, 2, 1, 2, 7]
def baseStart_1012725 : Nat := 118140960795 + 1012725 * 2 ^ 59
def prefixEnd_1012725 : Nat := 4983230072969 + 3 ^ 40 * 1012725 * 2
def baseEnd_1012725 : Nat := 19259803549061312684447

theorem tailTrace_1012725 : CollatzResearch.WordTrace tailWord_1012725 prefixEnd_1012725 19259803549061312684447 := by
  unfold tailWord_1012725
  simp only [CollatzResearch.WordTrace]
  refine ⟨36937115256077759505087629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24624743504051839670058419 36937115256077759505087629)
  ·
    refine ⟨13851418221029159814407861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36937115256077759505087629 13851418221029159814407861)
    ·
      refine ⟨1298570458221483732600737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13851418221029159814407861 1298570458221483732600737)
      ·
        refine ⟨973927843666112799450553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1298570458221483732600737 973927843666112799450553)
        ·
          refine ⟨730445882749584599587915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 973927843666112799450553 730445882749584599587915)
          ·
            refine ⟨1095668824124376899381873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 730445882749584599587915 1095668824124376899381873)
            ·
              refine ⟨821751618093282674536405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1095668824124376899381873 821751618093282674536405)
              ·
                refine ⟨19259803549061312684447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 821751618093282674536405 19259803549061312684447)
                ·
                  rfl

theorem cell23_1012725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 2, 7].length) (baseStart_1012725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1012725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1012725 prefixEnd_1012725 := by exact prefixLift 1012725
  have htrace : WordTrace (prefixWord ++ tailWord_1012725) baseStart_1012725 baseEnd_1012725 := by
    simpa [prefixWord, tailWord_1012725, baseEnd_1012725] using wordTrace_append hprefix tailTrace_1012725
  have hstable : (prefixWord ++ tailWord_1012725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012725).length < 2 ^ (prefixWord ++ tailWord_1012725).sum := by decide
  have hdescent : baseEnd_1012725 < baseStart_1012725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012741 : List Nat := [1, 3, 1, 1, 2, 3, 1, 1, 6, 2, 2]
def baseStart_1012741 : Nat := 118140960795 + 1012741 * 2 ^ 59
def prefixEnd_1012741 : Nat := 4983230072969 + 3 ^ 40 * 1012741 * 2
def baseEnd_1012741 : Nat := 520022911515127379879995

theorem tailTrace_1012741 : CollatzResearch.WordTrace tailWord_1012741 prefixEnd_1012741 520022911515127379879995 := by
  unfold tailWord_1012741
  simp only [CollatzResearch.WordTrace]
  refine ⟨36937698824019794237670077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24625132549346529491780051 36937698824019794237670077)
  ·
    refine ⟨13851637059007422839126279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36937698824019794237670077 13851637059007422839126279)
    ·
      refine ⟨20777455588511134258689419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13851637059007422839126279 20777455588511134258689419)
      ·
        refine ⟨31166183382766701388034129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20777455588511134258689419 31166183382766701388034129)
        ·
          refine ⟨23374637537075026041025597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31166183382766701388034129 23374637537075026041025597)
          ·
            refine ⟨8765489076403134765384599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23374637537075026041025597 8765489076403134765384599)
            ·
              refine ⟨13148233614604702148076899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8765489076403134765384599 13148233614604702148076899)
              ·
                refine ⟨19722350421907053222115349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13148233614604702148076899 19722350421907053222115349)
                ·
                  refine ⟨924485176026893119786657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 19722350421907053222115349 924485176026893119786657)
                  ·
                    refine ⟨693363882020169839839993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 924485176026893119786657 693363882020169839839993)
                    ·
                      refine ⟨520022911515127379879995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 693363882020169839839993 520022911515127379879995)
                      ·
                        rfl

theorem cell23_1012741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 6, 2, 2].length) (baseStart_1012741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1012741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1012741 prefixEnd_1012741 := by exact prefixLift 1012741
  have htrace : WordTrace (prefixWord ++ tailWord_1012741) baseStart_1012741 baseEnd_1012741 := by
    simpa [prefixWord, tailWord_1012741, baseEnd_1012741] using wordTrace_append hprefix tailTrace_1012741
  have hstable : (prefixWord ++ tailWord_1012741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012741).length < 2 ^ (prefixWord ++ tailWord_1012741).sum := by decide
  have hdescent : baseEnd_1012741 < baseStart_1012741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012744 : List Nat := [2, 1, 3, 2, 1, 4, 1, 1, 2, 1, 5]
def baseStart_1012744 : Nat := 118140960795 + 1012744 * 2 ^ 59
def prefixEnd_1012744 : Nat := 4983230072969 + 3 ^ 40 * 1012744 * 2
def baseEnd_1012744 : Nat := 520024451957090868142481

theorem tailTrace_1012744 : CollatzResearch.WordTrace tailWord_1012744 prefixEnd_1012744 520024451957090868142481 := by
  unfold tailWord_1012744
  simp only [CollatzResearch.WordTrace]
  refine ⟨18468904121504462875014643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24625205495339283833352857 18468904121504462875014643)
  ·
    refine ⟨27703356182256694312521965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18468904121504462875014643 27703356182256694312521965)
    ·
      refine ⟨10388758568346260367195737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27703356182256694312521965 10388758568346260367195737)
      ·
        refine ⟨7791568926259695275396803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10388758568346260367195737 7791568926259695275396803)
        ·
          refine ⟨11687353389389542913095205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7791568926259695275396803 11687353389389542913095205)
          ·
            refine ⟨2191378760510539296205351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11687353389389542913095205 2191378760510539296205351)
            ·
              refine ⟨3287068140765808944308027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2191378760510539296205351 3287068140765808944308027)
              ·
                refine ⟨4930602211148713416462041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3287068140765808944308027 4930602211148713416462041)
                ·
                  refine ⟨3697951658361535062346531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4930602211148713416462041 3697951658361535062346531)
                  ·
                    refine ⟨5546927487542302593519797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3697951658361535062346531 5546927487542302593519797)
                    ·
                      refine ⟨520024451957090868142481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5546927487542302593519797 520024451957090868142481)
                      ·
                        rfl

theorem cell23_1012744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 1, 2, 1, 5].length) (baseStart_1012744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1012744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1012744 prefixEnd_1012744 := by exact prefixLift 1012744
  have htrace : WordTrace (prefixWord ++ tailWord_1012744) baseStart_1012744 baseEnd_1012744 := by
    simpa [prefixWord, tailWord_1012744, baseEnd_1012744] using wordTrace_append hprefix tailTrace_1012744
  have hstable : (prefixWord ++ tailWord_1012744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012744).length < 2 ^ (prefixWord ++ tailWord_1012744).sum := by decide
  have hdescent : baseEnd_1012744 < baseStart_1012744 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012787 : List Nat := [1, 1, 1, 2, 4, 1, 1, 1, 3, 1, 7]
def baseStart_1012787 : Nat := 118140960795 + 1012787 * 2 ^ 59
def prefixEnd_1012787 : Nat := 4983230072969 + 3 ^ 40 * 1012787 * 2
def baseEnd_1012787 : Nat := 520046531625234199904783

theorem tailTrace_1012787 : CollatzResearch.WordTrace tailWord_1012787 prefixEnd_1012787 520046531625234199904783 := by
  unfold tailWord_1012787
  simp only [CollatzResearch.WordTrace]
  refine ⟨36939376581853144093844615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24626251054568762729229743 36939376581853144093844615)
  ·
    refine ⟨55409064872779716140766923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36939376581853144093844615 55409064872779716140766923)
    ·
      refine ⟨83113597309169574211150385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55409064872779716140766923 83113597309169574211150385)
      ·
        refine ⟨62335197981877180658362789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83113597309169574211150385 62335197981877180658362789)
        ·
          refine ⟨11687849621601971373443023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62335197981877180658362789 11687849621601971373443023)
          ·
            refine ⟨17531774432402957060164535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11687849621601971373443023 17531774432402957060164535)
            ·
              refine ⟨26297661648604435590246803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17531774432402957060164535 26297661648604435590246803)
              ·
                refine ⟨39446492472906653385370205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26297661648604435590246803 39446492472906653385370205)
                ·
                  refine ⟨14792434677339995019513827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39446492472906653385370205 14792434677339995019513827)
                  ·
                    refine ⟨22188652016009992529270741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14792434677339995019513827 22188652016009992529270741)
                    ·
                      refine ⟨520046531625234199904783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 22188652016009992529270741 520046531625234199904783)
                      ·
                        rfl

theorem cell23_1012787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 3, 1, 7].length) (baseStart_1012787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1012787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1012787 prefixEnd_1012787 := by exact prefixLift 1012787
  have htrace : WordTrace (prefixWord ++ tailWord_1012787) baseStart_1012787 baseEnd_1012787 := by
    simpa [prefixWord, tailWord_1012787, baseEnd_1012787] using wordTrace_append hprefix tailTrace_1012787
  have hstable : (prefixWord ++ tailWord_1012787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012787).length < 2 ^ (prefixWord ++ tailWord_1012787).sum := by decide
  have hdescent : baseEnd_1012787 < baseStart_1012787 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012794 : List Nat := [3, 1, 1, 1, 3, 1, 3, 3, 2, 5]
def baseStart_1012794 : Nat := 118140960795 + 1012794 * 2 ^ 59
def prefixEnd_1012794 : Nat := 4983230072969 + 3 ^ 40 * 1012794 * 2
def baseEnd_1012794 : Nat := 173350041996605224172417

theorem tailTrace_1012794 : CollatzResearch.WordTrace tailWord_1012794 prefixEnd_1012794 173350041996605224172417 := by
  unfold tailWord_1012794
  simp only [CollatzResearch.WordTrace]
  refine ⟨9234907973206946072337359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24626421261885189526232957 9234907973206946072337359)
  ·
    refine ⟨13852361959810419108506039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9234907973206946072337359 13852361959810419108506039)
    ·
      refine ⟨20778542939715628662759059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13852361959810419108506039 20778542939715628662759059)
      ·
        refine ⟨31167814409573442994138589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20778542939715628662759059 31167814409573442994138589)
        ·
          refine ⟨11687930403590041122801971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31167814409573442994138589 11687930403590041122801971)
          ·
            refine ⟨17531895605385061684202957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11687930403590041122801971 17531895605385061684202957)
            ·
              refine ⟨6574460852019398131576109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17531895605385061684202957 6574460852019398131576109)
              ·
                refine ⟨2465422819507274299341041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6574460852019398131576109 2465422819507274299341041)
                ·
                  refine ⟨1849067114630455724505781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2465422819507274299341041 1849067114630455724505781)
                  ·
                    refine ⟨173350041996605224172417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1849067114630455724505781 173350041996605224172417)
                    ·
                      rfl

theorem cell23_1012794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 3, 2, 5].length) (baseStart_1012794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1012794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1012794 prefixEnd_1012794 := by exact prefixLift 1012794
  have htrace : WordTrace (prefixWord ++ tailWord_1012794) baseStart_1012794 baseEnd_1012794 := by
    simpa [prefixWord, tailWord_1012794, baseEnd_1012794] using wordTrace_append hprefix tailTrace_1012794
  have hstable : (prefixWord ++ tailWord_1012794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012794).length < 2 ^ (prefixWord ++ tailWord_1012794).sum := by decide
  have hdescent : baseEnd_1012794 < baseStart_1012794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012831 : List Nat := [1, 1, 2, 3, 1, 1, 5, 1, 2, 4, 2]
def baseStart_1012831 : Nat := 118140960795 + 1012831 * 2 ^ 59
def prefixEnd_1012831 : Nat := 4983230072969 + 3 ^ 40 * 1012831 * 2
def baseEnd_1012831 : Nat := 520069124774032027754581

theorem tailTrace_1012831 : CollatzResearch.WordTrace tailWord_1012831 prefixEnd_1012831 520069124774032027754581 := by
  unfold tailWord_1012831
  simp only [CollatzResearch.WordTrace]
  refine ⟨36940981393693739608446347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24627320929129159738964231 36940981393693739608446347)
  ·
    refine ⟨55411472090540609412669521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36940981393693739608446347 55411472090540609412669521)
    ·
      refine ⟨41558604067905457059502141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55411472090540609412669521 41558604067905457059502141)
      ·
        refine ⟨15584476525464546397313303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41558604067905457059502141 15584476525464546397313303)
        ·
          refine ⟨23376714788196819595969955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15584476525464546397313303 23376714788196819595969955)
          ·
            refine ⟨35065072182295229393954933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23376714788196819595969955 35065072182295229393954933)
            ·
              refine ⟨3287350517090177755683275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35065072182295229393954933 3287350517090177755683275)
              ·
                refine ⟨4931025775635266633524913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3287350517090177755683275 4931025775635266633524913)
                ·
                  refine ⟨3698269331726449975143685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4931025775635266633524913 3698269331726449975143685)
                  ·
                    refine ⟨693425499698709370339441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3698269331726449975143685 693425499698709370339441)
                    ·
                      refine ⟨520069124774032027754581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 693425499698709370339441 520069124774032027754581)
                      ·
                        rfl

theorem cell23_1012831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 1, 2, 4, 2].length) (baseStart_1012831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1012831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1012831 prefixEnd_1012831 := by exact prefixLift 1012831
  have htrace : WordTrace (prefixWord ++ tailWord_1012831) baseStart_1012831 baseEnd_1012831 := by
    simpa [prefixWord, tailWord_1012831, baseEnd_1012831] using wordTrace_append hprefix tailTrace_1012831
  have hstable : (prefixWord ++ tailWord_1012831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012831).length < 2 ^ (prefixWord ++ tailWord_1012831).sum := by decide
  have hdescent : baseEnd_1012831 < baseStart_1012831 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012841 : List Nat := [1, 2, 1, 1, 1, 7, 1, 2, 3, 4]
def baseStart_1012841 : Nat := 118140960795 + 1012841 * 2 ^ 59
def prefixEnd_1012841 : Nat := 4983230072969 + 3 ^ 40 * 1012841 * 2
def baseEnd_1012841 : Nat := 173358086526858996209845

theorem tailTrace_1012841 : CollatzResearch.WordTrace tailWord_1012841 prefixEnd_1012841 173358086526858996209845 := by
  unfold tailWord_1012841
  simp only [CollatzResearch.WordTrace]
  refine ⟨36941346123657511316310377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24627564082438340877540251 36941346123657511316310377)
  ·
    refine ⟨27706009592743133487232783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36941346123657511316310377 27706009592743133487232783)
    ·
      refine ⟨41559014389114700230849175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27706009592743133487232783 41559014389114700230849175)
      ·
        refine ⟨62338521583672050346273763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41559014389114700230849175 62338521583672050346273763)
        ·
          refine ⟨93507782375508075519410645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62338521583672050346273763 93507782375508075519410645)
          ·
            refine ⟨2191588649425970519986187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 93507782375508075519410645 2191588649425970519986187)
            ·
              refine ⟨3287382974138955779979281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2191588649425970519986187 3287382974138955779979281)
              ·
                refine ⟨2465537230604216834984461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3287382974138955779979281 2465537230604216834984461)
                ·
                  refine ⟨924576461476581313119173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2465537230604216834984461 924576461476581313119173)
                  ·
                    refine ⟨173358086526858996209845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 924576461476581313119173 173358086526858996209845)
                    ·
                      rfl

theorem cell23_1012841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 2, 3, 4].length) (baseStart_1012841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1012841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1012841 prefixEnd_1012841 := by exact prefixLift 1012841
  have htrace : WordTrace (prefixWord ++ tailWord_1012841) baseStart_1012841 baseEnd_1012841 := by
    simpa [prefixWord, tailWord_1012841, baseEnd_1012841] using wordTrace_append hprefix tailTrace_1012841
  have hstable : (prefixWord ++ tailWord_1012841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012841).length < 2 ^ (prefixWord ++ tailWord_1012841).sum := by decide
  have hdescent : baseEnd_1012841 < baseStart_1012841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012874 : List Nat := [3, 1, 2, 3, 1, 1, 1, 1, 1, 1, 8]
def baseStart_1012874 : Nat := 118140960795 + 1012874 * 2 ^ 59
def prefixEnd_1012874 : Nat := 4983230072969 + 3 ^ 40 * 1012874 * 2
def baseEnd_1012874 : Nat := 520091204442175359516883

theorem tailTrace_1012874 : CollatzResearch.WordTrace tailWord_1012874 prefixEnd_1012874 520091204442175359516883 := by
  unfold tailWord_1012874
  simp only [CollatzResearch.WordTrace]
  refine ⟨9235637433134489488065419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24628366488358638634841117 9235637433134489488065419)
  ·
    refine ⟨13853456149701734232098129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9235637433134489488065419 13853456149701734232098129)
    ·
      refine ⟨10390092112276300674073597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13853456149701734232098129 10390092112276300674073597)
      ·
        refine ⟨3896284542103612752777599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10390092112276300674073597 3896284542103612752777599)
        ·
          refine ⟨5844426813155419129166399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3896284542103612752777599 5844426813155419129166399)
          ·
            refine ⟨8766640219733128693749599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5844426813155419129166399 8766640219733128693749599)
            ·
              refine ⟨13149960329599693040624399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8766640219733128693749599 13149960329599693040624399)
              ·
                refine ⟨19724940494399539560936599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13149960329599693040624399 19724940494399539560936599)
                ·
                  refine ⟨29587410741599309341404899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19724940494399539560936599 29587410741599309341404899)
                  ·
                    refine ⟨44381116112398964012107349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29587410741599309341404899 44381116112398964012107349)
                    ·
                      refine ⟨520091204442175359516883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 44381116112398964012107349 520091204442175359516883)
                      ·
                        rfl

theorem cell23_1012874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_1012874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1012874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1012874 prefixEnd_1012874 := by exact prefixLift 1012874
  have htrace : WordTrace (prefixWord ++ tailWord_1012874) baseStart_1012874 baseEnd_1012874 := by
    simpa [prefixWord, tailWord_1012874, baseEnd_1012874] using wordTrace_append hprefix tailTrace_1012874
  have hstable : (prefixWord ++ tailWord_1012874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012874).length < 2 ^ (prefixWord ++ tailWord_1012874).sum := by decide
  have hdescent : baseEnd_1012874 < baseStart_1012874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012888 : List Nat := [2, 1, 2, 4, 2, 2, 3, 1, 6]
def baseStart_1012888 : Nat := 118140960795 + 1012888 * 2 ^ 59
def prefixEnd_1012888 : Nat := 4983230072969 + 3 ^ 40 * 1012888 * 2
def baseEnd_1012888 : Nat := 57788710352370922749091

theorem tailTrace_1012888 : CollatzResearch.WordTrace tailWord_1012888 prefixEnd_1012888 57788710352370922749091 := by
  unfold tailWord_1012888
  simp only [CollatzResearch.WordTrace]
  refine ⟨18471530177243619171635659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24628706902991492228847545 18471530177243619171635659)
  ·
    refine ⟨27707295265865428757453489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18471530177243619171635659 27707295265865428757453489)
    ·
      refine ⟨20780471449399071568090117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27707295265865428757453489 20780471449399071568090117)
      ·
        refine ⟨3896338396762325919016897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20780471449399071568090117 3896338396762325919016897)
        ·
          refine ⟨2922253797571744439262673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3896338396762325919016897 2922253797571744439262673)
          ·
            refine ⟨2191690348178808329447005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2922253797571744439262673 2191690348178808329447005)
            ·
              refine ⟨821883880567053123542627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2191690348178808329447005 821883880567053123542627)
              ·
                refine ⟨1232825820850579685313941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 821883880567053123542627 1232825820850579685313941)
                ·
                  refine ⟨57788710352370922749091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1232825820850579685313941 57788710352370922749091)
                  ·
                    rfl

theorem cell23_1012888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 3, 1, 6].length) (baseStart_1012888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1012888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1012888 prefixEnd_1012888 := by exact prefixLift 1012888
  have htrace : WordTrace (prefixWord ++ tailWord_1012888) baseStart_1012888 baseEnd_1012888 := by
    simpa [prefixWord, tailWord_1012888, baseEnd_1012888] using wordTrace_append hprefix tailTrace_1012888
  have hstable : (prefixWord ++ tailWord_1012888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012888).length < 2 ^ (prefixWord ++ tailWord_1012888).sum := by decide
  have hdescent : baseEnd_1012888 < baseStart_1012888 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012901 : List Nat := [1, 3, 1, 2, 1, 4, 1, 4, 1, 5]
def baseStart_1012901 : Nat := 118140960795 + 1012901 * 2 ^ 59
def prefixEnd_1012901 : Nat := 4983230072969 + 3 ^ 40 * 1012901 * 2
def baseEnd_1012901 : Nat := 173368356139948917959753

theorem tailTrace_1012901 : CollatzResearch.WordTrace tailWord_1012901 prefixEnd_1012901 173368356139948917959753 := by
  unfold tailWord_1012901
  simp only [CollatzResearch.WordTrace]
  refine ⟨36943534503440141563494557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24629023002293427708996371 36943534503440141563494557)
  ·
    refine ⟨13853825438790053086310459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36943534503440141563494557 13853825438790053086310459)
    ·
      refine ⟨20780738158185079629465689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13853825438790053086310459 20780738158185079629465689)
      ·
        refine ⟨15585553618638809722099267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20780738158185079629465689 15585553618638809722099267)
        ·
          refine ⟨23378330427958214583148901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15585553618638809722099267 23378330427958214583148901)
          ·
            refine ⟨4383436955242165234340419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23378330427958214583148901 4383436955242165234340419)
            ·
              refine ⟨6575155432863247851510629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4383436955242165234340419 6575155432863247851510629)
              ·
                refine ⟨1232841643661858972158243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6575155432863247851510629 1232841643661858972158243)
                ·
                  refine ⟨1849262465492788458237365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1232841643661858972158243 1849262465492788458237365)
                  ·
                    refine ⟨173368356139948917959753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1849262465492788458237365 173368356139948917959753)
                    ·
                      rfl

theorem cell23_1012901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 4, 1, 5].length) (baseStart_1012901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1012901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1012901 prefixEnd_1012901 := by exact prefixLift 1012901
  have htrace : WordTrace (prefixWord ++ tailWord_1012901) baseStart_1012901 baseEnd_1012901 := by
    simpa [prefixWord, tailWord_1012901, baseEnd_1012901] using wordTrace_append hprefix tailTrace_1012901
  have hstable : (prefixWord ++ tailWord_1012901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012901).length < 2 ^ (prefixWord ++ tailWord_1012901).sum := by decide
  have hdescent : baseEnd_1012901 < baseStart_1012901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012909 : List Nat := [1, 5, 2, 1, 4, 1, 1, 3, 1, 4]
def baseStart_1012909 : Nat := 118140960795 + 1012909 * 2 ^ 59
def prefixEnd_1012909 : Nat := 4983230072969 + 3 ^ 40 * 1012909 * 2
def baseEnd_1012909 : Nat := 173369725421694240859741

theorem tailTrace_1012909 : CollatzResearch.WordTrace tailWord_1012909 prefixEnd_1012909 173369725421694240859741 := by
  unfold tailWord_1012909
  simp only [CollatzResearch.WordTrace]
  refine ⟨36943826287411158929785781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24629217524940772619857187 36943826287411158929785781)
  ·
    refine ⟨3463483714444796149667417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36943826287411158929785781 3463483714444796149667417)
    ·
      refine ⟨2597612785833597112250563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3463483714444796149667417 2597612785833597112250563)
      ·
        refine ⟨3896419178750395668375845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2597612785833597112250563 3896419178750395668375845)
        ·
          refine ⟨730578596015699187820471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3896419178750395668375845 730578596015699187820471)
          ·
            refine ⟨1095867894023548781730707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 730578596015699187820471 1095867894023548781730707)
            ·
              refine ⟨1643801841035323172596061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1095867894023548781730707 1643801841035323172596061)
              ·
                refine ⟨616425690388246189723523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1643801841035323172596061 616425690388246189723523)
                ·
                  refine ⟨924638535582369284585285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 616425690388246189723523 924638535582369284585285)
                  ·
                    refine ⟨173369725421694240859741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 924638535582369284585285 173369725421694240859741)
                    ·
                      rfl

theorem cell23_1012909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 1, 3, 1, 4].length) (baseStart_1012909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1012909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1012909 prefixEnd_1012909 := by exact prefixLift 1012909
  have htrace : WordTrace (prefixWord ++ tailWord_1012909) baseStart_1012909 baseEnd_1012909 := by
    simpa [prefixWord, tailWord_1012909, baseEnd_1012909] using wordTrace_append hprefix tailTrace_1012909
  have hstable : (prefixWord ++ tailWord_1012909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012909).length < 2 ^ (prefixWord ++ tailWord_1012909).sum := by decide
  have hdescent : baseEnd_1012909 < baseStart_1012909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012915 : List Nat := [1, 1, 1, 2, 3, 2, 5, 3, 1, 1, 3]
def baseStart_1012915 : Nat := 118140960795 + 1012915 * 2 ^ 59
def prefixEnd_1012915 : Nat := 4983230072969 + 3 ^ 40 * 1012915 * 2
def baseEnd_1012915 : Nat := 520112257149009699104195

theorem tailTrace_1012915 : CollatzResearch.WordTrace tailWord_1012915 prefixEnd_1012915 520112257149009699104195 := by
  unfold tailWord_1012915
  simp only [CollatzResearch.WordTrace]
  refine ⟨36944045125389421954504199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24629363416926281303002799 36944045125389421954504199)
  ·
    refine ⟨55416067688084132931756299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36944045125389421954504199 55416067688084132931756299)
    ·
      refine ⟨83124101532126199397634449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55416067688084132931756299 83124101532126199397634449)
      ·
        refine ⟨62343076149094649548225837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83124101532126199397634449 62343076149094649548225837)
        ·
          refine ⟨23378653555910493580584689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62343076149094649548225837 23378653555910493580584689)
          ·
            refine ⟨17533990166932870185438517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23378653555910493580584689 17533990166932870185438517)
            ·
              refine ⟨1643811578149956579884861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17533990166932870185438517 1643811578149956579884861)
              ·
                refine ⟨616429341806233717456823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1643811578149956579884861 616429341806233717456823)
                ·
                  refine ⟨924644012709350576185235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 616429341806233717456823 924644012709350576185235)
                  ·
                    refine ⟨1386966019064025864277853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 924644012709350576185235 1386966019064025864277853)
                    ·
                      refine ⟨520112257149009699104195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1386966019064025864277853 520112257149009699104195)
                      ·
                        rfl

theorem cell23_1012915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 5, 3, 1, 1, 3].length) (baseStart_1012915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1012915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1012915 prefixEnd_1012915 := by exact prefixLift 1012915
  have htrace : WordTrace (prefixWord ++ tailWord_1012915) baseStart_1012915 baseEnd_1012915 := by
    simpa [prefixWord, tailWord_1012915, baseEnd_1012915] using wordTrace_append hprefix tailTrace_1012915
  have hstable : (prefixWord ++ tailWord_1012915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012915).length < 2 ^ (prefixWord ++ tailWord_1012915).sum := by decide
  have hdescent : baseEnd_1012915 < baseStart_1012915 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012932 : List Nat := [2, 3, 3, 1, 3, 2, 1, 1, 3, 1, 3]
def baseStart_1012932 : Nat := 118140960795 + 1012932 * 2 ^ 59
def prefixEnd_1012932 : Nat := 4983230072969 + 3 ^ 40 * 1012932 * 2
def baseEnd_1012932 : Nat := 520120986320136132591617

theorem tailTrace_1012932 : CollatzResearch.WordTrace tailWord_1012932 prefixEnd_1012932 520120986320136132591617 := by
  unfold tailWord_1012932
  simp only [CollatzResearch.WordTrace]
  refine ⟨18472332583163916928936525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24629776777551889238582033 18472332583163916928936525)
  ·
    refine ⟨6927124718686468848351197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18472332583163916928936525 6927124718686468848351197)
    ·
      refine ⟨2597671769507425818131699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6927124718686468848351197 2597671769507425818131699)
      ·
        refine ⟨3896507654261138727197549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2597671769507425818131699 3896507654261138727197549)
        ·
          refine ⟨1461190370347927022699081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3896507654261138727197549 1461190370347927022699081)
          ·
            refine ⟨1095892777760945267024311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1461190370347927022699081 1095892777760945267024311)
            ·
              refine ⟨1643839166641417900536467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1095892777760945267024311 1643839166641417900536467)
              ·
                refine ⟨2465758749962126850804701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1643839166641417900536467 2465758749962126850804701)
                ·
                  refine ⟨924659531235797569051763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2465758749962126850804701 924659531235797569051763)
                  ·
                    refine ⟨1386989296853696353577645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 924659531235797569051763 1386989296853696353577645)
                    ·
                      refine ⟨520120986320136132591617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1386989296853696353577645 520120986320136132591617)
                      ·
                        rfl

theorem cell23_1012932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 1, 1, 3, 1, 3].length) (baseStart_1012932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1012932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1012932 prefixEnd_1012932 := by exact prefixLift 1012932
  have htrace : WordTrace (prefixWord ++ tailWord_1012932) baseStart_1012932 baseEnd_1012932 := by
    simpa [prefixWord, tailWord_1012932, baseEnd_1012932] using wordTrace_append hprefix tailTrace_1012932
  have hstable : (prefixWord ++ tailWord_1012932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012932).length < 2 ^ (prefixWord ++ tailWord_1012932).sum := by decide
  have hdescent : baseEnd_1012932 < baseStart_1012932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012971 : List Nat := [1, 1, 1, 1, 2, 6, 1, 1, 3, 3, 3]
def baseStart_1012971 : Nat := 118140960795 + 1012971 * 2 ^ 59
def prefixEnd_1012971 : Nat := 4983230072969 + 3 ^ 40 * 1012971 * 2
def baseEnd_1012971 : Nat := 520141012065661480003937

theorem tailTrace_1012971 : CollatzResearch.WordTrace tailWord_1012971 prefixEnd_1012971 520141012065661480003937 := by
  unfold tailWord_1012971
  simp only [CollatzResearch.WordTrace]
  refine ⟨36946087613186543518542767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24630725075457695679028511 36946087613186543518542767)
  ·
    refine ⟨55419131419779815277814151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36946087613186543518542767 55419131419779815277814151)
    ·
      refine ⟨83128697129669722916721227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55419131419779815277814151 83128697129669722916721227)
      ·
        refine ⟨124693045694504584375081841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83128697129669722916721227 124693045694504584375081841)
        ·
          refine ⟨93519784270878438281311381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124693045694504584375081841 93519784270878438281311381)
          ·
            refine ⟨4383739887697426794436471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 93519784270878438281311381 4383739887697426794436471)
            ·
              refine ⟨6575609831546140191654707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4383739887697426794436471 6575609831546140191654707)
              ·
                refine ⟨9863414747319210287482061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6575609831546140191654707 9863414747319210287482061)
                ·
                  refine ⟨3698780530244703857805773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9863414747319210287482061 3698780530244703857805773)
                  ·
                    refine ⟨1387042698841763946677165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3698780530244703857805773 1387042698841763946677165)
                    ·
                      refine ⟨520141012065661480003937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1387042698841763946677165 520141012065661480003937)
                      ·
                        rfl

theorem cell23_1012971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 1, 3, 3, 3].length) (baseStart_1012971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1012971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1012971 prefixEnd_1012971 := by exact prefixLift 1012971
  have htrace : WordTrace (prefixWord ++ tailWord_1012971) baseStart_1012971 baseEnd_1012971 := by
    simpa [prefixWord, tailWord_1012971, baseEnd_1012971] using wordTrace_append hprefix tailTrace_1012971
  have hstable : (prefixWord ++ tailWord_1012971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012971).length < 2 ^ (prefixWord ++ tailWord_1012971).sum := by decide
  have hdescent : baseEnd_1012971 < baseStart_1012971 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012975 : List Nat := [1, 1, 2, 1, 8, 1, 1, 1, 1, 1, 5]
def baseStart_1012975 : Nat := 118140960795 + 1012975 * 2 ^ 59
def prefixEnd_1012975 : Nat := 4983230072969 + 3 ^ 40 * 1012975 * 2
def baseEnd_1012975 : Nat := 520143065988279464353919

theorem tailTrace_1012975 : CollatzResearch.WordTrace tailWord_1012975 prefixEnd_1012975 520143065988279464353919 := by
  unfold tailWord_1012975
  simp only [CollatzResearch.WordTrace]
  refine ⟨36946233505172052201688379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24630822336781368134458919 36946233505172052201688379)
  ·
    refine ⟨55419350257758078302532569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36946233505172052201688379 55419350257758078302532569)
    ·
      refine ⟨41564512693318558726899427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55419350257758078302532569 41564512693318558726899427)
      ·
        refine ⟨62346769039977838090349141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41564512693318558726899427 62346769039977838090349141)
        ·
          refine ⟨730626199687240290121279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 62346769039977838090349141 730626199687240290121279)
          ·
            refine ⟨1095939299530860435181919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 730626199687240290121279 1095939299530860435181919)
            ·
              refine ⟨1643908949296290652772879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1095939299530860435181919 1643908949296290652772879)
              ·
                refine ⟨2465863423944435979159319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1643908949296290652772879 2465863423944435979159319)
                ·
                  refine ⟨3698795135916653968738979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2465863423944435979159319 3698795135916653968738979)
                  ·
                    refine ⟨5548192703874980953108469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3698795135916653968738979 5548192703874980953108469)
                    ·
                      refine ⟨520143065988279464353919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5548192703874980953108469 520143065988279464353919)
                      ·
                        rfl

theorem cell23_1012975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 1, 1, 1, 1, 5].length) (baseStart_1012975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1012975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1012975 prefixEnd_1012975 := by exact prefixLift 1012975
  have htrace : WordTrace (prefixWord ++ tailWord_1012975) baseStart_1012975 baseEnd_1012975 := by
    simpa [prefixWord, tailWord_1012975, baseEnd_1012975] using wordTrace_append hprefix tailTrace_1012975
  have hstable : (prefixWord ++ tailWord_1012975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012975).length < 2 ^ (prefixWord ++ tailWord_1012975).sum := by decide
  have hdescent : baseEnd_1012975 < baseStart_1012975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012984 : List Nat := [2, 1, 2, 1, 1, 2, 1, 1, 2, 3, 7]
def baseStart_1012984 : Nat := 118140960795 + 1012984 * 2 ^ 59
def prefixEnd_1012984 : Nat := 4983230072969 + 3 ^ 40 * 1012984 * 2
def baseEnd_1012984 : Nat := 520147687314169929141377

theorem tailTrace_1012984 : CollatzResearch.WordTrace tailWord_1012984 prefixEnd_1012984 520147687314169929141377 := by
  unfold tailWord_1012984
  simp only [CollatzResearch.WordTrace]
  refine ⟨18473280881069723369383003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24631041174759631159177337 18473280881069723369383003)
  ·
    refine ⟨27709921321604585054074505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18473280881069723369383003 27709921321604585054074505)
    ·
      refine ⟨20782440991203438790555879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27709921321604585054074505 20782440991203438790555879)
      ·
        refine ⟨31173661486805158185833819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20782440991203438790555879 31173661486805158185833819)
        ·
          refine ⟨46760492230207737278750729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31173661486805158185833819 46760492230207737278750729)
          ·
            refine ⟨35070369172655802959063047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46760492230207737278750729 35070369172655802959063047)
            ·
              refine ⟨52605553758983704438594571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35070369172655802959063047 52605553758983704438594571)
              ·
                refine ⟨78908330638475556657891857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52605553758983704438594571 78908330638475556657891857)
                ·
                  refine ⟨59181247978856667493418893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78908330638475556657891857 59181247978856667493418893)
                  ·
                    refine ⟨22192967992071250310032085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59181247978856667493418893 22192967992071250310032085)
                    ·
                      refine ⟨520147687314169929141377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 22192967992071250310032085 520147687314169929141377)
                      ·
                        rfl

theorem cell23_1012984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 2, 3, 7].length) (baseStart_1012984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1012984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1012984 prefixEnd_1012984 := by exact prefixLift 1012984
  have htrace : WordTrace (prefixWord ++ tailWord_1012984) baseStart_1012984 baseEnd_1012984 := by
    simpa [prefixWord, tailWord_1012984, baseEnd_1012984] using wordTrace_append hprefix tailTrace_1012984
  have hstable : (prefixWord ++ tailWord_1012984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012984).length < 2 ^ (prefixWord ++ tailWord_1012984).sum := by decide
  have hdescent : baseEnd_1012984 < baseStart_1012984 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013015 : List Nat := [1, 1, 3, 4, 1, 1, 2, 4, 1, 3, 2]
def baseStart_1013015 : Nat := 118140960795 + 1013015 * 2 ^ 59
def prefixEnd_1013015 : Nat := 4983230072969 + 3 ^ 40 * 1013015 * 2
def baseEnd_1013015 : Nat := 520163605214459307853735

theorem tailTrace_1013015 : CollatzResearch.WordTrace tailWord_1013015 prefixEnd_1013015 520163605214459307853735 := by
  unfold tailWord_1013015
  simp only [CollatzResearch.WordTrace]
  refine ⟨36947692425027139033144499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24631794950018092688762999 36947692425027139033144499)
  ·
    refine ⟨55421538637540708549716749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36947692425027139033144499 55421538637540708549716749)
    ·
      refine ⟨20783076989077765706143781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55421538637540708549716749 20783076989077765706143781)
      ·
        refine ⟨3896826935452081069901959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20783076989077765706143781 3896826935452081069901959)
        ·
          refine ⟨5845240403178121604852939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3896826935452081069901959 5845240403178121604852939)
          ·
            refine ⟨8767860604767182407279409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5845240403178121604852939 8767860604767182407279409)
            ·
              refine ⟨6575895453575386805459557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8767860604767182407279409 6575895453575386805459557)
              ·
                refine ⟨1232980397545385026023667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6575895453575386805459557 1232980397545385026023667)
                ·
                  refine ⟨1849470596318077539035501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1232980397545385026023667 1849470596318077539035501)
                  ·
                    refine ⟨693551473619279077138313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1849470596318077539035501 693551473619279077138313)
                    ·
                      refine ⟨520163605214459307853735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 693551473619279077138313 520163605214459307853735)
                      ·
                        rfl

theorem cell23_1013015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 4, 1, 3, 2].length) (baseStart_1013015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1013015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1013015 prefixEnd_1013015 := by exact prefixLift 1013015
  have htrace : WordTrace (prefixWord ++ tailWord_1013015) baseStart_1013015 baseEnd_1013015 := by
    simpa [prefixWord, tailWord_1013015, baseEnd_1013015] using wordTrace_append hprefix tailTrace_1013015
  have hstable : (prefixWord ++ tailWord_1013015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013015).length < 2 ^ (prefixWord ++ tailWord_1013015).sum := by decide
  have hdescent : baseEnd_1013015 < baseStart_1013015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013032 : List Nat := [2, 1, 5, 1, 2, 2, 1, 3, 1, 3, 2]
def baseStart_1013032 : Nat := 118140960795 + 1013032 * 2 ^ 59
def prefixEnd_1013032 : Nat := 4983230072969 + 3 ^ 40 * 1013032 * 2
def baseEnd_1013032 : Nat := 520172334385585741341157

theorem tailTrace_1013032 : CollatzResearch.WordTrace tailWord_1013032 prefixEnd_1013032 520172334385585741341157 := by
  unfold tailWord_1013032
  simp only [CollatzResearch.WordTrace]
  refine ⟨18474156232982775468256675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24632208310643700624342233 18474156232982775468256675)
  ·
    refine ⟨27711234349474163202385013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18474156232982775468256675 27711234349474163202385013)
    ·
      refine ⟨2597928220263202800223595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27711234349474163202385013 2597928220263202800223595)
      ·
        refine ⟨3896892330394804200335393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2597928220263202800223595 3896892330394804200335393)
        ·
          refine ⟨2922669247796103150251545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3896892330394804200335393 2922669247796103150251545)
          ·
            refine ⟨2192001935847077362688659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2922669247796103150251545 2192001935847077362688659)
            ·
              refine ⟨3288002903770616044032989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2192001935847077362688659 3288002903770616044032989)
              ·
                refine ⟨1233001088913981016512371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3288002903770616044032989 1233001088913981016512371)
                ·
                  refine ⟨1849501633370971524768557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1233001088913981016512371 1849501633370971524768557)
                  ·
                    refine ⟨693563112514114321788209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1849501633370971524768557 693563112514114321788209)
                    ·
                      refine ⟨520172334385585741341157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 693563112514114321788209 520172334385585741341157)
                      ·
                        rfl

theorem cell23_1013032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 3, 1, 3, 2].length) (baseStart_1013032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1013032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1013032 prefixEnd_1013032 := by exact prefixLift 1013032
  have htrace : WordTrace (prefixWord ++ tailWord_1013032) baseStart_1013032 baseEnd_1013032 := by
    simpa [prefixWord, tailWord_1013032, baseEnd_1013032] using wordTrace_append hprefix tailTrace_1013032
  have hstable : (prefixWord ++ tailWord_1013032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013032).length < 2 ^ (prefixWord ++ tailWord_1013032).sum := by decide
  have hdescent : baseEnd_1013032 < baseStart_1013032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013081 : List Nat := [1, 2, 1, 2, 2, 2, 4, 1, 1, 7]
def baseStart_1013081 : Nat := 118140960795 + 1013081 * 2 ^ 59
def prefixEnd_1013081 : Nat := 4983230072969 + 3 ^ 40 * 1013081 * 2
def baseEnd_1013081 : Nat := 173399164979218683209477

theorem tailTrace_1013081 : CollatzResearch.WordTrace tailWord_1013081 prefixEnd_1013081 173399164979218683209477 := by
  unfold tailWord_1013081
  simp only [CollatzResearch.WordTrace]
  refine ⟨36950099642788032305047097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24633399761858688203364731 36950099642788032305047097)
  ·
    refine ⟨27712574732091024228785323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36950099642788032305047097 27712574732091024228785323)
    ·
      refine ⟨41568862098136536343177985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27712574732091024228785323 41568862098136536343177985)
      ·
        refine ⟨31176646573602402257383489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41568862098136536343177985 31176646573602402257383489)
        ·
          refine ⟨23382484930201801693037617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31176646573602402257383489 23382484930201801693037617)
          ·
            refine ⟨17536863697651351269778213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23382484930201801693037617 17536863697651351269778213)
            ·
              refine ⟨3288161943309628363083415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17536863697651351269778213 3288161943309628363083415)
              ·
                refine ⟨4932242914964442544625123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3288161943309628363083415 4932242914964442544625123)
                ·
                  refine ⟨7398364372446663816937685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4932242914964442544625123 7398364372446663816937685)
                  ·
                    refine ⟨173399164979218683209477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7398364372446663816937685 173399164979218683209477)
                    ·
                      rfl

theorem cell23_1013081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 1, 1, 7].length) (baseStart_1013081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1013081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1013081 prefixEnd_1013081 := by exact prefixLift 1013081
  have htrace : WordTrace (prefixWord ++ tailWord_1013081) baseStart_1013081 baseEnd_1013081 := by
    simpa [prefixWord, tailWord_1013081, baseEnd_1013081] using wordTrace_append hprefix tailTrace_1013081
  have hstable : (prefixWord ++ tailWord_1013081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013081).length < 2 ^ (prefixWord ++ tailWord_1013081).sum := by decide
  have hdescent : baseEnd_1013081 < baseStart_1013081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013102 : List Nat := [4, 1, 2, 4, 1, 2, 1, 1, 7]
def baseStart_1013102 : Nat := 118140960795 + 1013102 * 2 ^ 59
def prefixEnd_1013102 : Nat := 4983230072969 + 3 ^ 40 * 1013102 * 2
def baseEnd_1013102 : Nat := 57800919781266718607315

theorem tailTrace_1013102 : CollatzResearch.WordTrace tailWord_1013102 prefixEnd_1013102 57800919781266718607315 := by
  unfold tailWord_1013102
  simp only [CollatzResearch.WordTrace]
  refine ⟨4618858196963994111445195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24633910383807968594374373 4618858196963994111445195)
  ·
    refine ⟨6928287295445991167167793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4618858196963994111445195 6928287295445991167167793)
    ·
      refine ⟨5196215471584493375375845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6928287295445991167167793 5196215471584493375375845)
      ·
        refine ⟨974290400922092507882971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5196215471584493375375845 974290400922092507882971)
        ·
          refine ⟨1461435601383138761824457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 974290400922092507882971 1461435601383138761824457)
          ·
            refine ⟨1096076701037354071368343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1461435601383138761824457 1096076701037354071368343)
            ·
              refine ⟨1644115051556031107052515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1096076701037354071368343 1644115051556031107052515)
              ·
                refine ⟨2466172577334046660578773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1644115051556031107052515 2466172577334046660578773)
                ·
                  refine ⟨57800919781266718607315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2466172577334046660578773 57800919781266718607315)
                  ·
                    rfl

theorem cell23_1013102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 1, 1, 7].length) (baseStart_1013102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1013102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1013102 prefixEnd_1013102 := by exact prefixLift 1013102
  have htrace : WordTrace (prefixWord ++ tailWord_1013102) baseStart_1013102 baseEnd_1013102 := by
    simpa [prefixWord, tailWord_1013102, baseEnd_1013102] using wordTrace_append hprefix tailTrace_1013102
  have hstable : (prefixWord ++ tailWord_1013102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013102).length < 2 ^ (prefixWord ++ tailWord_1013102).sum := by decide
  have hdescent : baseEnd_1013102 < baseStart_1013102 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013141 : List Nat := [1, 3, 2, 1, 1, 2, 2, 1, 10]
def baseStart_1013141 : Nat := 118140960795 + 1013141 * 2 ^ 59
def prefixEnd_1013141 : Nat := 4983230072969 + 3 ^ 40 * 1013141 * 2
def baseEnd_1013141 : Nat := 57803144864102868319795

theorem tailTrace_1013141 : CollatzResearch.WordTrace tailWord_1013141 prefixEnd_1013141 57803144864102868319795 := by
  unfold tailWord_1013141
  simp only [CollatzResearch.WordTrace]
  refine ⟨36952288022570662552231277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24634858681713775034820851 36952288022570662552231277)
  ·
    refine ⟨13857108008463998457086729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36952288022570662552231277 13857108008463998457086729)
    ·
      refine ⟨10392831006347998842815047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13857108008463998457086729 10392831006347998842815047)
      ·
        refine ⟨15589246509521998264222571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10392831006347998842815047 15589246509521998264222571)
        ·
          refine ⟨23383869764282997396333857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15589246509521998264222571 23383869764282997396333857)
          ·
            refine ⟨17537902323212248047250393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23383869764282997396333857 17537902323212248047250393)
            ·
              refine ⟨13153426742409186035437795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17537902323212248047250393 13153426742409186035437795)
              ·
                refine ⟨19730140113613779053156693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13153426742409186035437795 19730140113613779053156693)
                ·
                  refine ⟨57803144864102868319795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 19730140113613779053156693 57803144864102868319795)
                  ·
                    rfl

theorem cell23_1013141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 10].length) (baseStart_1013141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1013141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1013141 prefixEnd_1013141 := by exact prefixLift 1013141
  have htrace : WordTrace (prefixWord ++ tailWord_1013141) baseStart_1013141 baseEnd_1013141 := by
    simpa [prefixWord, tailWord_1013141, baseEnd_1013141] using wordTrace_append hprefix tailTrace_1013141
  have hstable : (prefixWord ++ tailWord_1013141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013141).length < 2 ^ (prefixWord ++ tailWord_1013141).sum := by decide
  have hdescent : baseEnd_1013141 < baseStart_1013141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013186 : List Nat := [3, 5, 2, 1, 1, 1, 1, 1, 1, 3, 4]
def baseStart_1013186 : Nat := 118140960795 + 1013186 * 2 ^ 59
def prefixEnd_1013186 : Nat := 4983230072969 + 3 ^ 40 * 1013186 * 2
def baseEnd_1013186 : Nat := 520251410406378138815449

theorem tailTrace_1013186 : CollatzResearch.WordTrace tailWord_1013186 prefixEnd_1013186 520251410406378138815449 := by
  unfold tailWord_1013186
  simp only [CollatzResearch.WordTrace]
  refine ⟨9238482326851908809404853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24635952871605090158412941 9238482326851908809404853)
  ·
    refine ⟨866107718142366450881705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9238482326851908809404853 866107718142366450881705)
    ·
      refine ⟨649580788606774838161279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 866107718142366450881705 649580788606774838161279)
      ·
        refine ⟨974371182910162257241919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 649580788606774838161279 974371182910162257241919)
        ·
          refine ⟨1461556774365243385862879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 974371182910162257241919 1461556774365243385862879)
          ·
            refine ⟨2192335161547865078794319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1461556774365243385862879 2192335161547865078794319)
            ·
              refine ⟨3288502742321797618191479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2192335161547865078794319 3288502742321797618191479)
              ·
                refine ⟨4932754113482696427287219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3288502742321797618191479 4932754113482696427287219)
                ·
                  refine ⟨7399131170224044640930829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4932754113482696427287219 7399131170224044640930829)
                  ·
                    refine ⟨2774674188834016740349061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7399131170224044640930829 2774674188834016740349061)
                    ·
                      refine ⟨520251410406378138815449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2774674188834016740349061 520251410406378138815449)
                      ·
                        rfl

theorem cell23_1013186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_1013186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1013186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1013186 prefixEnd_1013186 := by exact prefixLift 1013186
  have htrace : WordTrace (prefixWord ++ tailWord_1013186) baseStart_1013186 baseEnd_1013186 := by
    simpa [prefixWord, tailWord_1013186, baseEnd_1013186] using wordTrace_append hprefix tailTrace_1013186
  have hstable : (prefixWord ++ tailWord_1013186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013186).length < 2 ^ (prefixWord ++ tailWord_1013186).sum := by decide
  have hdescent : baseEnd_1013186 < baseStart_1013186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013205 : List Nat := [1, 3, 2, 3, 1, 1, 3, 3, 1, 5]
def baseStart_1013205 : Nat := 118140960795 + 1013205 * 2 ^ 59
def prefixEnd_1013205 : Nat := 4983230072969 + 3 ^ 40 * 1013205 * 2
def baseEnd_1013205 : Nat := 173420388846271188159287

theorem tailTrace_1013205 : CollatzResearch.WordTrace tailWord_1013205 prefixEnd_1013205 173420388846271188159287 := by
  unfold tailWord_1013205
  simp only [CollatzResearch.WordTrace]
  refine ⟨36954622294338801482561069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24636414862892534321707379 36954622294338801482561069)
  ·
    refine ⟨13857983360377050555960401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36954622294338801482561069 13857983360377050555960401)
    ·
      refine ⟨10393487520282787916970301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13857983360377050555960401 10393487520282787916970301)
      ·
        refine ⟨3897557820106045468863863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10393487520282787916970301 3897557820106045468863863)
        ·
          refine ⟨5846336730159068203295795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3897557820106045468863863 5846336730159068203295795)
          ·
            refine ⟨8769505095238602304943693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5846336730159068203295795 8769505095238602304943693)
            ·
              refine ⟨3288564410714475864353885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8769505095238602304943693 3288564410714475864353885)
              ·
                refine ⟨1233211654017928449132707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3288564410714475864353885 1233211654017928449132707)
                ·
                  refine ⟨1849817481026892673699061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1233211654017928449132707 1849817481026892673699061)
                  ·
                    refine ⟨173420388846271188159287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1849817481026892673699061 173420388846271188159287)
                    ·
                      rfl

theorem cell23_1013205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 3, 1, 5].length) (baseStart_1013205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1013205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1013205 prefixEnd_1013205 := by exact prefixLift 1013205
  have htrace : WordTrace (prefixWord ++ tailWord_1013205) baseStart_1013205 baseEnd_1013205 := by
    simpa [prefixWord, tailWord_1013205, baseEnd_1013205] using wordTrace_append hprefix tailTrace_1013205
  have hstable : (prefixWord ++ tailWord_1013205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013205).length < 2 ^ (prefixWord ++ tailWord_1013205).sum := by decide
  have hdescent : baseEnd_1013205 < baseStart_1013205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013219 : List Nat := [1, 1, 1, 6, 2, 1, 2, 4, 1, 1, 3]
def baseStart_1013219 : Nat := 118140960795 + 1013219 * 2 ^ 59
def prefixEnd_1013219 : Nat := 4983230072969 + 3 ^ 40 * 1013219 * 2
def baseEnd_1013219 : Nat := 520268355267976509702797

theorem tailTrace_1013219 : CollatzResearch.WordTrace tailWord_1013219 prefixEnd_1013219 520268355267976509702797 := by
  unfold tailWord_1013219
  simp only [CollatzResearch.WordTrace]
  refine ⟨36955132916288081873570711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24636755277525387915713807 36955132916288081873570711)
  ·
    refine ⟨55432699374432122810356067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36955132916288081873570711 55432699374432122810356067)
    ·
      refine ⟨83149049061648184215534101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55432699374432122810356067 83149049061648184215534101)
      ·
        refine ⟨3897611674764758635103161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 83149049061648184215534101 3897611674764758635103161)
        ·
          refine ⟨2923208756073568976327371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3897611674764758635103161 2923208756073568976327371)
          ·
            refine ⟨4384813134110353464491057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2923208756073568976327371 4384813134110353464491057)
            ·
              refine ⟨3288609850582765098368293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4384813134110353464491057 3288609850582765098368293)
              ·
                refine ⟨616614346984268455944055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3288609850582765098368293 616614346984268455944055)
                ·
                  refine ⟨924921520476402683916083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 616614346984268455944055 924921520476402683916083)
                  ·
                    refine ⟨1387382280714604025874125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 924921520476402683916083 1387382280714604025874125)
                    ·
                      refine ⟨520268355267976509702797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1387382280714604025874125 520268355267976509702797)
                      ·
                        rfl

theorem cell23_1013219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 4, 1, 1, 3].length) (baseStart_1013219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1013219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1013219 prefixEnd_1013219 := by exact prefixLift 1013219
  have htrace : WordTrace (prefixWord ++ tailWord_1013219) baseStart_1013219 baseEnd_1013219 := by
    simpa [prefixWord, tailWord_1013219, baseEnd_1013219] using wordTrace_append hprefix tailTrace_1013219
  have hstable : (prefixWord ++ tailWord_1013219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013219).length < 2 ^ (prefixWord ++ tailWord_1013219).sum := by decide
  have hdescent : baseEnd_1013219 < baseStart_1013219 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013228 : List Nat := [2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 3]
def baseStart_1013228 : Nat := 118140960795 + 1013228 * 2 ^ 59
def prefixEnd_1013228 : Nat := 4983230072969 + 3 ^ 40 * 1013228 * 2
def baseEnd_1013228 : Nat := 520272976593866974490255

theorem tailTrace_1013228 : CollatzResearch.WordTrace tailWord_1013228 prefixEnd_1013228 520272976593866974490255 := by
  unfold tailWord_1013228
  simp only [CollatzResearch.WordTrace]
  refine ⟨18477730586627738205324169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24636974115503650940432225 18477730586627738205324169)
  ·
    refine ⟨13858297939970803653993127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18477730586627738205324169 13858297939970803653993127)
    ·
      refine ⟨20787446909956205480989691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13858297939970803653993127 20787446909956205480989691)
      ·
        refine ⟨31181170364934308221484537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20787446909956205480989691 31181170364934308221484537)
        ·
          refine ⟨23385877773700731166113403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31181170364934308221484537 23385877773700731166113403)
          ·
            refine ⟨35078816660551096749170105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23385877773700731166113403 35078816660551096749170105)
            ·
              refine ⟨26309112495413322561877579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35078816660551096749170105 26309112495413322561877579)
              ·
                refine ⟨39463668743119983842816369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26309112495413322561877579 39463668743119983842816369)
                ·
                  refine ⟨29597751557339987882112277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39463668743119983842816369 29597751557339987882112277)
                  ·
                    refine ⟨1387394604250311931974013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29597751557339987882112277 1387394604250311931974013)
                    ·
                      refine ⟨520272976593866974490255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1387394604250311931974013 520272976593866974490255)
                      ·
                        rfl

theorem cell23_1013228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 3].length) (baseStart_1013228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1013228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1013228 prefixEnd_1013228 := by exact prefixLift 1013228
  have htrace : WordTrace (prefixWord ++ tailWord_1013228) baseStart_1013228 baseEnd_1013228 := by
    simpa [prefixWord, tailWord_1013228, baseEnd_1013228] using wordTrace_append hprefix tailTrace_1013228
  have hstable : (prefixWord ++ tailWord_1013228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013228).length < 2 ^ (prefixWord ++ tailWord_1013228).sum := by decide
  have hdescent : baseEnd_1013228 < baseStart_1013228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013242 : List Nat := [3, 1, 1, 1, 1, 2, 3, 4, 3, 2, 2]
def baseStart_1013242 : Nat := 118140960795 + 1013242 * 2 ^ 59
def prefixEnd_1013242 : Nat := 4983230072969 + 3 ^ 40 * 1013242 * 2
def baseEnd_1013242 : Nat := 520280165323029919715191

theorem tailTrace_1013242 : CollatzResearch.WordTrace tailWord_1013242 prefixEnd_1013242 520280165323029919715191 := by
  unfold tailWord_1013242
  simp only [CollatzResearch.WordTrace]
  refine ⟨9238992948801189200414495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24637314530136504534438653 9238992948801189200414495)
  ·
    refine ⟨13858489423201783800621743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9238992948801189200414495 13858489423201783800621743)
    ·
      refine ⟨20787734134802675700932615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13858489423201783800621743 20787734134802675700932615)
      ·
        refine ⟨31181601202204013551398923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20787734134802675700932615 31181601202204013551398923)
        ·
          refine ⟨46772401803306020327098385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31181601202204013551398923 46772401803306020327098385)
          ·
            refine ⟨35079301352479515245323789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46772401803306020327098385 35079301352479515245323789)
            ·
              refine ⟨13154738007179818216996421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35079301352479515245323789 13154738007179818216996421)
              ·
                refine ⟨2466513376346215915686829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13154738007179818216996421 2466513376346215915686829)
                ·
                  refine ⟨924942516129830968382561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2466513376346215915686829 924942516129830968382561)
                  ·
                    refine ⟨693706887097373226286921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 924942516129830968382561 693706887097373226286921)
                    ·
                      refine ⟨520280165323029919715191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 693706887097373226286921 520280165323029919715191)
                      ·
                        rfl

theorem cell23_1013242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 4, 3, 2, 2].length) (baseStart_1013242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1013242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1013242 prefixEnd_1013242 := by exact prefixLift 1013242
  have htrace : WordTrace (prefixWord ++ tailWord_1013242) baseStart_1013242 baseEnd_1013242 := by
    simpa [prefixWord, tailWord_1013242, baseEnd_1013242] using wordTrace_append hprefix tailTrace_1013242
  have hstable : (prefixWord ++ tailWord_1013242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013242).length < 2 ^ (prefixWord ++ tailWord_1013242).sum := by decide
  have hdescent : baseEnd_1013242 < baseStart_1013242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013262 : List Nat := [4, 1, 1, 2, 4, 1, 2, 1, 1, 1, 5]
def baseStart_1013262 : Nat := 118140960795 + 1013262 * 2 ^ 59
def prefixEnd_1013262 : Nat := 4983230072969 + 3 ^ 40 * 1013262 * 2
def baseEnd_1013262 : Nat := 520290434936119841465099

theorem tailTrace_1013262 : CollatzResearch.WordTrace tailWord_1013262 prefixEnd_1013262 520290434936119841465099 := by
  unfold tailWord_1013262
  simp only [CollatzResearch.WordTrace]
  refine ⟨4619587656891537527173255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24637800836754866811590693 4619587656891537527173255)
  ·
    refine ⟨6929381485337306290759883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4619587656891537527173255 6929381485337306290759883)
    ·
      refine ⟨10394072228005959436139825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6929381485337306290759883 10394072228005959436139825)
      ·
        refine ⟨7795554171004469577104869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10394072228005959436139825 7795554171004469577104869)
        ·
          refine ⟨1461666407063338045707163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7795554171004469577104869 1461666407063338045707163)
          ·
            refine ⟨2192499610595007068560745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1461666407063338045707163 2192499610595007068560745)
            ·
              refine ⟨1644374707946255301420559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2192499610595007068560745 1644374707946255301420559)
              ·
                refine ⟨2466562061919382952130839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1644374707946255301420559 2466562061919382952130839)
                ·
                  refine ⟨3699843092879074428196259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2466562061919382952130839 3699843092879074428196259)
                  ·
                    refine ⟨5549764639318611642294389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3699843092879074428196259 5549764639318611642294389)
                    ·
                      refine ⟨520290434936119841465099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5549764639318611642294389 520290434936119841465099)
                      ·
                        rfl

theorem cell23_1013262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 2, 1, 1, 1, 5].length) (baseStart_1013262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1013262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1013262 prefixEnd_1013262 := by exact prefixLift 1013262
  have htrace : WordTrace (prefixWord ++ tailWord_1013262) baseStart_1013262 baseEnd_1013262 := by
    simpa [prefixWord, tailWord_1013262, baseEnd_1013262] using wordTrace_append hprefix tailTrace_1013262
  have hstable : (prefixWord ++ tailWord_1013262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013262).length < 2 ^ (prefixWord ++ tailWord_1013262).sum := by decide
  have hdescent : baseEnd_1013262 < baseStart_1013262 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013285 : List Nat := [1, 3, 1, 2, 2, 1, 1, 1, 2, 7, 2]
def baseStart_1013285 : Nat := 118140960795 + 1013285 * 2 ^ 59
def prefixEnd_1013285 : Nat := 4983230072969 + 3 ^ 40 * 1013285 * 2
def baseEnd_1013285 : Nat := 520302244991173251477493

theorem tailTrace_1013285 : CollatzResearch.WordTrace tailWord_1013285 prefixEnd_1013285 520302244991173251477493 := by
  unfold tailWord_1013285
  simp only [CollatzResearch.WordTrace]
  refine ⟨36957540134048975145473309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24638360089365983430315539 36957540134048975145473309)
  ·
    refine ⟨13859077550268365679552491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36957540134048975145473309 13859077550268365679552491)
    ·
      refine ⟨20788616325402548519328737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13859077550268365679552491 20788616325402548519328737)
      ·
        refine ⟨15591462244051911389496553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20788616325402548519328737 15591462244051911389496553)
        ·
          refine ⟨11693596683038933542122415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15591462244051911389496553 11693596683038933542122415)
          ·
            refine ⟨17540395024558400313183623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11693596683038933542122415 17540395024558400313183623)
            ·
              refine ⟨26310592536837600469775435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17540395024558400313183623 26310592536837600469775435)
              ·
                refine ⟨39465888805256400704663153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26310592536837600469775435 39465888805256400704663153)
                ·
                  refine ⟨29599416603942300528497365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39465888805256400704663153 29599416603942300528497365)
                  ·
                    refine ⟨693736326654897668636657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29599416603942300528497365 693736326654897668636657)
                    ·
                      refine ⟨520302244991173251477493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 693736326654897668636657 520302244991173251477493)
                      ·
                        rfl

theorem cell23_1013285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 7, 2].length) (baseStart_1013285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1013285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1013285 prefixEnd_1013285 := by exact prefixLift 1013285
  have htrace : WordTrace (prefixWord ++ tailWord_1013285) baseStart_1013285 baseEnd_1013285 := by
    simpa [prefixWord, tailWord_1013285, baseEnd_1013285] using wordTrace_append hprefix tailTrace_1013285
  have hstable : (prefixWord ++ tailWord_1013285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013285).length < 2 ^ (prefixWord ++ tailWord_1013285).sum := by decide
  have hdescent : baseEnd_1013285 < baseStart_1013285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013298 : List Nat := [3, 2, 1, 1, 2, 1, 1, 1, 1, 2, 8]
def baseStart_1013298 : Nat := 118140960795 + 1013298 * 2 ^ 59
def prefixEnd_1013298 : Nat := 4983230072969 + 3 ^ 40 * 1013298 * 2
def baseEnd_1013298 : Nat := 520308920239681700614933

theorem tailTrace_1013298 : CollatzResearch.WordTrace tailWord_1013298 prefixEnd_1013298 520308920239681700614933 := by
  unfold tailWord_1013298
  simp only [CollatzResearch.WordTrace]
  refine ⟨9239503570750469591424137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24638676188667918910464365 9239503570750469591424137)
  ·
    refine ⟨6929627678062852193568103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9239503570750469591424137 6929627678062852193568103)
    ·
      refine ⟨10394441517094278290352155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6929627678062852193568103 10394441517094278290352155)
      ·
        refine ⟨15591662275641417435528233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10394441517094278290352155 15591662275641417435528233)
        ·
          refine ⟨11693746706731063076646175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15591662275641417435528233 11693746706731063076646175)
          ·
            refine ⟨17540620060096594614969263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11693746706731063076646175 17540620060096594614969263)
            ·
              refine ⟨26310930090144891922453895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17540620060096594614969263 26310930090144891922453895)
              ·
                refine ⟨39466395135217337883680843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26310930090144891922453895 39466395135217337883680843)
                ·
                  refine ⟨59199592702826006825521265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39466395135217337883680843 59199592702826006825521265)
                  ·
                    refine ⟨44399694527119505119140949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59199592702826006825521265 44399694527119505119140949)
                    ·
                      refine ⟨520308920239681700614933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 44399694527119505119140949 520308920239681700614933)
                      ·
                        rfl

theorem cell23_1013298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 1, 2, 8].length) (baseStart_1013298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1013298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1013298 prefixEnd_1013298 := by exact prefixLift 1013298
  have htrace : WordTrace (prefixWord ++ tailWord_1013298) baseStart_1013298 baseEnd_1013298 := by
    simpa [prefixWord, tailWord_1013298, baseEnd_1013298] using wordTrace_append hprefix tailTrace_1013298
  have hstable : (prefixWord ++ tailWord_1013298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013298).length < 2 ^ (prefixWord ++ tailWord_1013298).sum := by decide
  have hdescent : baseEnd_1013298 < baseStart_1013298 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013332 : List Nat := [2, 4, 1, 1, 1, 2, 1, 2, 3, 4, 2]
def baseStart_1013332 : Nat := 118140960795 + 1013332 * 2 ^ 59
def prefixEnd_1013332 : Nat := 4983230072969 + 3 ^ 40 * 1013332 * 2
def baseEnd_1013332 : Nat := 520326378581934567589777

theorem tailTrace_1013332 : CollatzResearch.WordTrace tailWord_1013332 prefixEnd_1013332 520326378581934567589777 := by
  unfold tailWord_1013332
  simp only [CollatzResearch.WordTrace]
  refine ⟨18479627182439351086217125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24639502909919134781622833 18479627182439351086217125)
  ·
    refine ⟨3464930096707378328665711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18479627182439351086217125 3464930096707378328665711)
    ·
      refine ⟨5197395145061067492998567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3464930096707378328665711 5197395145061067492998567)
      ·
        refine ⟨7796092717591601239497851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5197395145061067492998567 7796092717591601239497851)
        ·
          refine ⟨11694139076387401859246777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7796092717591601239497851 11694139076387401859246777)
          ·
            refine ⟨8770604307290551394435083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11694139076387401859246777 8770604307290551394435083)
            ·
              refine ⟨13155906460935827091652625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8770604307290551394435083 13155906460935827091652625)
              ·
                refine ⟨9866929845701870318739469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13155906460935827091652625 9866929845701870318739469)
                ·
                  refine ⟨3700098692138201369527301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9866929845701870318739469 3700098692138201369527301)
                  ·
                    refine ⟨693768504775912756786369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3700098692138201369527301 693768504775912756786369)
                    ·
                      refine ⟨520326378581934567589777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 693768504775912756786369 520326378581934567589777)
                      ·
                        rfl

theorem cell23_1013332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 2, 3, 4, 2].length) (baseStart_1013332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1013332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1013332 prefixEnd_1013332 := by exact prefixLift 1013332
  have htrace : WordTrace (prefixWord ++ tailWord_1013332) baseStart_1013332 baseEnd_1013332 := by
    simpa [prefixWord, tailWord_1013332, baseEnd_1013332] using wordTrace_append hprefix tailTrace_1013332
  have hstable : (prefixWord ++ tailWord_1013332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013332).length < 2 ^ (prefixWord ++ tailWord_1013332).sum := by decide
  have hdescent : baseEnd_1013332 < baseStart_1013332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013335 : List Nat := [1, 1, 3, 2, 2, 3, 1, 1, 2, 4, 3]
def baseStart_1013335 : Nat := 118140960795 + 1013335 * 2 ^ 59
def prefixEnd_1013335 : Nat := 4983230072969 + 3 ^ 40 * 1013335 * 2
def baseEnd_1013335 : Nat := 520327919023898055852263

theorem tailTrace_1013335 : CollatzResearch.WordTrace tailWord_1013335 prefixEnd_1013335 520327919023898055852263 := by
  unfold tailWord_1013335
  simp only [CollatzResearch.WordTrace]
  refine ⟨36959363783867833684793459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24639575855911889123195639 36959363783867833684793459)
  ·
    refine ⟨55439045675801750527190189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36959363783867833684793459 55439045675801750527190189)
    ·
      refine ⟨20789642128425656447696321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55439045675801750527190189 20789642128425656447696321)
      ·
        refine ⟨15592231596319242335772241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20789642128425656447696321 15592231596319242335772241)
        ·
          refine ⟨11694173697239431751829181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15592231596319242335772241 11694173697239431751829181)
          ·
            refine ⟨4385315136464786906935943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11694173697239431751829181 4385315136464786906935943)
            ·
              refine ⟨6577972704697180360403915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4385315136464786906935943 6577972704697180360403915)
              ·
                refine ⟨9866959057045770540605873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6577972704697180360403915 9866959057045770540605873)
                ·
                  refine ⟨7400219292784327905454405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9866959057045770540605873 7400219292784327905454405)
                  ·
                    refine ⟨1387541117397061482272701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7400219292784327905454405 1387541117397061482272701)
                    ·
                      refine ⟨520327919023898055852263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1387541117397061482272701 520327919023898055852263)
                      ·
                        rfl

theorem cell23_1013335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 1, 2, 4, 3].length) (baseStart_1013335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1013335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1013335 prefixEnd_1013335 := by exact prefixLift 1013335
  have htrace : WordTrace (prefixWord ++ tailWord_1013335) baseStart_1013335 baseEnd_1013335 := by
    simpa [prefixWord, tailWord_1013335, baseEnd_1013335] using wordTrace_append hprefix tailTrace_1013335
  have hstable : (prefixWord ++ tailWord_1013335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013335).length < 2 ^ (prefixWord ++ tailWord_1013335).sum := by decide
  have hdescent : baseEnd_1013335 < baseStart_1013335 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013338 : List Nat := [3, 1, 1, 2, 1, 1, 1, 2, 11]
def baseStart_1013338 : Nat := 118140960795 + 1013338 * 2 ^ 59
def prefixEnd_1013338 : Nat := 4983230072969 + 3 ^ 40 * 1013338 * 2
def baseEnd_1013338 : Nat := 57814384385095727123861

theorem tailTrace_1013338 : CollatzResearch.WordTrace tailWord_1013338 prefixEnd_1013338 57814384385095727123861 := by
  unfold tailWord_1013338
  simp only [CollatzResearch.WordTrace]
  refine ⟨9239868300714241299288167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24639648801904643464768445 9239868300714241299288167)
  ·
    refine ⟨13859802451071361948932251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9239868300714241299288167 13859802451071361948932251)
    ·
      refine ⟨20789703676607042923398377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13859802451071361948932251 20789703676607042923398377)
      ·
        refine ⟨15592277757455282192548783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20789703676607042923398377 15592277757455282192548783)
        ·
          refine ⟨23388416636182923288823175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15592277757455282192548783 23388416636182923288823175)
          ·
            refine ⟨35082624954274384933234763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23388416636182923288823175 35082624954274384933234763)
            ·
              refine ⟨52623937431411577399852145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35082624954274384933234763 52623937431411577399852145)
              ·
                refine ⟨39467953073558683049889109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52623937431411577399852145 39467953073558683049889109)
                ·
                  refine ⟨57814384385095727123861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 39467953073558683049889109 57814384385095727123861)
                  ·
                    rfl

theorem cell23_1013338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 11].length) (baseStart_1013338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1013338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1013338 prefixEnd_1013338 := by exact prefixLift 1013338
  have htrace : WordTrace (prefixWord ++ tailWord_1013338) baseStart_1013338 baseEnd_1013338 := by
    simpa [prefixWord, tailWord_1013338, baseEnd_1013338] using wordTrace_append hprefix tailTrace_1013338
  have hstable : (prefixWord ++ tailWord_1013338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013338).length < 2 ^ (prefixWord ++ tailWord_1013338).sum := by decide
  have hdescent : baseEnd_1013338 < baseStart_1013338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013345 : List Nat := [1, 2, 3, 1, 1, 3, 3, 1, 2, 2, 4]
def baseStart_1013345 : Nat := 118140960795 + 1013345 * 2 ^ 59
def prefixEnd_1013345 : Nat := 4983230072969 + 3 ^ 40 * 1013345 * 2
def baseEnd_1013345 : Nat := 520333053830443016727217

theorem tailTrace_1013345 : CollatzResearch.WordTrace tailWord_1013345 prefixEnd_1013345 520333053830443016727217 := by
  unfold tailWord_1013345
  simp only [CollatzResearch.WordTrace]
  refine ⟨36959728513831605392657489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24639819009221070261771659 36959728513831605392657489)
  ·
    refine ⟨27719796385373704044493117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36959728513831605392657489 27719796385373704044493117)
    ·
      refine ⟨10394923644515139016684919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27719796385373704044493117 10394923644515139016684919)
      ·
        refine ⟨15592385466772708525027379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10394923644515139016684919 15592385466772708525027379)
        ·
          refine ⟨23388578200159062787541069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15592385466772708525027379 23388578200159062787541069)
          ·
            refine ⟨8770716825059648545327901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23388578200159062787541069 8770716825059648545327901)
            ·
              refine ⟨3289018809397368204497963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8770716825059648545327901 3289018809397368204497963)
              ·
                refine ⟨4933528214096052306746945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3289018809397368204497963 4933528214096052306746945)
                ·
                  refine ⟨3700146160572039230060209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4933528214096052306746945 3700146160572039230060209)
                  ·
                    refine ⟨2775109620429029422545157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3700146160572039230060209 2775109620429029422545157)
                    ·
                      refine ⟨520333053830443016727217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2775109620429029422545157 520333053830443016727217)
                      ·
                        rfl

theorem cell23_1013345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 1, 2, 2, 4].length) (baseStart_1013345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1013345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1013345 prefixEnd_1013345 := by exact prefixLift 1013345
  have htrace : WordTrace (prefixWord ++ tailWord_1013345) baseStart_1013345 baseEnd_1013345 := by
    simpa [prefixWord, tailWord_1013345, baseEnd_1013345] using wordTrace_append hprefix tailTrace_1013345
  have hstable : (prefixWord ++ tailWord_1013345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013345).length < 2 ^ (prefixWord ++ tailWord_1013345).sum := by decide
  have hdescent : baseEnd_1013345 < baseStart_1013345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013349 : List Nat := [1, 3, 1, 3, 3, 2, 2, 1, 1, 4, 2]
def baseStart_1013349 : Nat := 118140960795 + 1013349 * 2 ^ 59
def prefixEnd_1013349 : Nat := 4983230072969 + 3 ^ 40 * 1013349 * 2
def baseEnd_1013349 : Nat := 520335107753061001077199

theorem tailTrace_1013349 : CollatzResearch.WordTrace tailWord_1013349 prefixEnd_1013349 520335107753061001077199 := by
  unfold tailWord_1013349
  simp only [CollatzResearch.WordTrace]
  refine ⟨36959874405817114075803101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24639916270544742717202067 36959874405817114075803101)
  ·
    refine ⟨13859952902181417778426163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36959874405817114075803101 13859952902181417778426163)
    ·
      refine ⟨20789929353272126667639245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13859952902181417778426163 20789929353272126667639245)
      ·
        refine ⟨7796223507477047500364717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20789929353272126667639245 7796223507477047500364717)
        ·
          refine ⟨2923583815303892812636769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7796223507477047500364717 2923583815303892812636769)
          ·
            refine ⟨2192687861477919609477577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2923583815303892812636769 2192687861477919609477577)
            ·
              refine ⟨1644515896108439707108183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2192687861477919609477577 1644515896108439707108183)
              ·
                refine ⟨2466773844162659560662275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1644515896108439707108183 2466773844162659560662275)
                ·
                  refine ⟨3700160766243989340993413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2466773844162659560662275 3700160766243989340993413)
                  ·
                    refine ⟨693780143670748001436265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3700160766243989340993413 693780143670748001436265)
                    ·
                      refine ⟨520335107753061001077199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 693780143670748001436265 520335107753061001077199)
                      ·
                        rfl

theorem cell23_1013349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 2, 1, 1, 4, 2].length) (baseStart_1013349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1013349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1013349 prefixEnd_1013349 := by exact prefixLift 1013349
  have htrace : WordTrace (prefixWord ++ tailWord_1013349) baseStart_1013349 baseEnd_1013349 := by
    simpa [prefixWord, tailWord_1013349, baseEnd_1013349] using wordTrace_append hprefix tailTrace_1013349
  have hstable : (prefixWord ++ tailWord_1013349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013349).length < 2 ^ (prefixWord ++ tailWord_1013349).sum := by decide
  have hdescent : baseEnd_1013349 < baseStart_1013349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013385 : List Nat := [1, 2, 1, 1, 4, 1, 2, 4, 2, 5]
def baseStart_1013385 : Nat := 118140960795 + 1013385 * 2 ^ 59
def prefixEnd_1013385 : Nat := 4983230072969 + 3 ^ 40 * 1013385 * 2
def baseEnd_1013385 : Nat := 173451197685540953409011

theorem tailTrace_1013385 : CollatzResearch.WordTrace tailWord_1013385 prefixEnd_1013385 173451197685540953409011 := by
  unfold tailWord_1013385
  simp only [CollatzResearch.WordTrace]
  refine ⟨36961187433686692224113609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24640791622457794816075739 36961187433686692224113609)
  ·
    refine ⟨27720890575265019168085207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36961187433686692224113609 27720890575265019168085207)
    ·
      refine ⟨41581335862897528752127811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27720890575265019168085207 41581335862897528752127811)
      ·
        refine ⟨62372003794346293128191717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41581335862897528752127811 62372003794346293128191717)
        ·
          refine ⟨11694750711439929961535947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62372003794346293128191717 11694750711439929961535947)
          ·
            refine ⟨17542126067159894942303921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11694750711439929961535947 17542126067159894942303921)
            ·
              refine ⟨13156594550369921206727941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17542126067159894942303921 13156594550369921206727941)
              ·
                refine ⟨2466861478194360226261489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13156594550369921206727941 2466861478194360226261489)
                ·
                  refine ⟨1850146108645770169696117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2466861478194360226261489 1850146108645770169696117)
                  ·
                    refine ⟨173451197685540953409011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1850146108645770169696117 173451197685540953409011)
                    ·
                      rfl

theorem cell23_1013385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 4, 2, 5].length) (baseStart_1013385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1013385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1013385 prefixEnd_1013385 := by exact prefixLift 1013385
  have htrace : WordTrace (prefixWord ++ tailWord_1013385) baseStart_1013385 baseEnd_1013385 := by
    simpa [prefixWord, tailWord_1013385, baseEnd_1013385] using wordTrace_append hprefix tailTrace_1013385
  have hstable : (prefixWord ++ tailWord_1013385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013385).length < 2 ^ (prefixWord ++ tailWord_1013385).sum := by decide
  have hdescent : baseEnd_1013385 < baseStart_1013385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013446 : List Nat := [6, 1, 2, 1, 1, 2, 1, 1, 1, 2, 5]
def baseStart_1013446 : Nat := 118140960795 + 1013446 * 2 ^ 59
def prefixEnd_1013446 : Nat := 4983230072969 + 3 ^ 40 * 1013446 * 2
def baseEnd_1013446 : Nat := 520384915376547121564253

theorem tailTrace_1013446 : CollatzResearch.WordTrace tailWord_1013446 prefixEnd_1013446 520384915376547121564253 := by
  unfold tailWord_1013446
  simp only [CollatzResearch.WordTrace]
  refine ⟨1155106633952053113815131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 24642274857643799761389461 1155106633952053113815131)
  ·
    refine ⟨1732659950928079670722697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1155106633952053113815131 1732659950928079670722697)
    ·
      refine ⟨1299494963196059753042023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1732659950928079670722697 1299494963196059753042023)
      ·
        refine ⟨1949242444794089629563035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1299494963196059753042023 1949242444794089629563035)
        ·
          refine ⟨2923863667191134444344553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1949242444794089629563035 2923863667191134444344553)
          ·
            refine ⟨2192897750393350833258415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2923863667191134444344553 2192897750393350833258415)
            ·
              refine ⟨3289346625590026249887623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2192897750393350833258415 3289346625590026249887623)
              ·
                refine ⟨4934019938385039374831435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3289346625590026249887623 4934019938385039374831435)
                ·
                  refine ⟨7401029907577559062247153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4934019938385039374831435 7401029907577559062247153)
                  ·
                    refine ⟨5550772430683169296685365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7401029907577559062247153 5550772430683169296685365)
                    ·
                      refine ⟨520384915376547121564253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5550772430683169296685365 520384915376547121564253)
                      ·
                        rfl

theorem cell23_1013446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_1013446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1013446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1013446 prefixEnd_1013446 := by exact prefixLift 1013446
  have htrace : WordTrace (prefixWord ++ tailWord_1013446) baseStart_1013446 baseEnd_1013446 := by
    simpa [prefixWord, tailWord_1013446, baseEnd_1013446] using wordTrace_append hprefix tailTrace_1013446
  have hstable : (prefixWord ++ tailWord_1013446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013446).length < 2 ^ (prefixWord ++ tailWord_1013446).sum := by decide
  have hdescent : baseEnd_1013446 < baseStart_1013446 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013506 : List Nat := [3, 4, 1, 1, 1, 1, 2, 3, 3, 1, 3]
def baseStart_1013506 : Nat := 118140960795 + 1013506 * 2 ^ 59
def prefixEnd_1013506 : Nat := 4983230072969 + 3 ^ 40 * 1013506 * 2
def baseEnd_1013506 : Nat := 520415724215816886813977

theorem tailTrace_1013506 : CollatzResearch.WordTrace tailWord_1013506 prefixEnd_1013506 520415724215816886813977 := by
  unfold tailWord_1013506
  simp only [CollatzResearch.WordTrace]
  refine ⟨9241400166562082472317093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24643733777498886592845581 9241400166562082472317093)
  ·
    refine ⟨1732762531230390463559455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9241400166562082472317093 1732762531230390463559455)
    ·
      refine ⟨2599143796845585695339183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1732762531230390463559455 2599143796845585695339183)
      ·
        refine ⟨3898715695268378543008775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2599143796845585695339183 3898715695268378543008775)
        ·
          refine ⟨5848073542902567814513163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3898715695268378543008775 5848073542902567814513163)
          ·
            refine ⟨8772110314353851721769745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5848073542902567814513163 8772110314353851721769745)
            ·
              refine ⟨6579082735765388791327309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8772110314353851721769745 6579082735765388791327309)
              ·
                refine ⟨2467156025912020796747741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6579082735765388791327309 2467156025912020796747741)
                ·
                  refine ⟨925183509717007798780403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2467156025912020796747741 925183509717007798780403)
                  ·
                    refine ⟨1387775264575511698170605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 925183509717007798780403 1387775264575511698170605)
                    ·
                      refine ⟨520415724215816886813977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1387775264575511698170605 520415724215816886813977)
                      ·
                        rfl

theorem cell23_1013506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 3, 3, 1, 3].length) (baseStart_1013506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1013506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1013506 prefixEnd_1013506 := by exact prefixLift 1013506
  have htrace : WordTrace (prefixWord ++ tailWord_1013506) baseStart_1013506 baseEnd_1013506 := by
    simpa [prefixWord, tailWord_1013506, baseEnd_1013506] using wordTrace_append hprefix tailTrace_1013506
  have hstable : (prefixWord ++ tailWord_1013506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013506).length < 2 ^ (prefixWord ++ tailWord_1013506).sum := by decide
  have hdescent : baseEnd_1013506 < baseStart_1013506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013512 : List Nat := [2, 1, 3, 2, 2, 1, 1, 1, 5, 1, 4]
def baseStart_1013512 : Nat := 118140960795 + 1013512 * 2 ^ 59
def prefixEnd_1013512 : Nat := 4983230072969 + 3 ^ 40 * 1013512 * 2
def baseEnd_1013512 : Nat := 520418805099743863338949

theorem tailTrace_1013512 : CollatzResearch.WordTrace tailWord_1013512 prefixEnd_1013512 520418805099743863338949 := by
  unfold tailWord_1013512
  simp only [CollatzResearch.WordTrace]
  refine ⟨18482909752113296456993395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24643879669484395275991193 18482909752113296456993395)
  ·
    refine ⟨27724364628169944685490093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18482909752113296456993395 27724364628169944685490093)
    ·
      refine ⟨10396636735563729257058785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27724364628169944685490093 10396636735563729257058785)
      ·
        refine ⟨7797477551672796942794089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10396636735563729257058785 7797477551672796942794089)
        ·
          refine ⟨5848108163754597707095567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7797477551672796942794089 5848108163754597707095567)
          ·
            refine ⟨8772162245631896560643351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5848108163754597707095567 8772162245631896560643351)
            ·
              refine ⟨13158243368447844840965027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8772162245631896560643351 13158243368447844840965027)
              ·
                refine ⟨19737365052671767261447541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13158243368447844840965027 19737365052671767261447541)
                ·
                  refine ⟨1850377973687978180760707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19737365052671767261447541 1850377973687978180760707)
                  ·
                    refine ⟨2775566960531967271141061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1850377973687978180760707 2775566960531967271141061)
                    ·
                      refine ⟨520418805099743863338949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2775566960531967271141061 520418805099743863338949)
                      ·
                        rfl

theorem cell23_1013512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 5, 1, 4].length) (baseStart_1013512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1013512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1013512 prefixEnd_1013512 := by exact prefixLift 1013512
  have htrace : WordTrace (prefixWord ++ tailWord_1013512) baseStart_1013512 baseEnd_1013512 := by
    simpa [prefixWord, tailWord_1013512, baseEnd_1013512] using wordTrace_append hprefix tailTrace_1013512
  have hstable : (prefixWord ++ tailWord_1013512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013512).length < 2 ^ (prefixWord ++ tailWord_1013512).sum := by decide
  have hdescent : baseEnd_1013512 < baseStart_1013512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013556 : List Nat := [2, 5, 1, 1, 2, 2, 1, 1, 4, 4]
def baseStart_1013556 : Nat := 118140960795 + 1013556 * 2 ^ 59
def prefixEnd_1013556 : Nat := 4983230072969 + 3 ^ 40 * 1013556 * 2
def baseEnd_1013556 : Nat := 173480466082847230396249

theorem tailTrace_1013556 : CollatzResearch.WordTrace tailWord_1013556 prefixEnd_1013556 173480466082847230396249 := by
  unfold tailWord_1013556
  simp only [CollatzResearch.WordTrace]
  refine ⟨18483712158033594214294261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24644949544044792285725681 18483712158033594214294261)
  ·
    refine ⟨1732848014815649457590087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18483712158033594214294261 1732848014815649457590087)
    ·
      refine ⟨2599272022223474186385131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1732848014815649457590087 2599272022223474186385131)
      ·
        refine ⟨3898908033335211279577697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2599272022223474186385131 3898908033335211279577697)
        ·
          refine ⟨2924181025001408459683273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3898908033335211279577697 2924181025001408459683273)
          ·
            refine ⟨2193135768751056344762455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2924181025001408459683273 2193135768751056344762455)
            ·
              refine ⟨3289703653126584517143683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2193135768751056344762455 3289703653126584517143683)
              ·
                refine ⟨4934555479689876775715525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3289703653126584517143683 4934555479689876775715525)
                ·
                  refine ⟨925229152441851895446661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4934555479689876775715525 925229152441851895446661)
                  ·
                    refine ⟨173480466082847230396249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 925229152441851895446661 173480466082847230396249)
                    ·
                      rfl

theorem cell23_1013556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 1, 4, 4].length) (baseStart_1013556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1013556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1013556 prefixEnd_1013556 := by exact prefixLift 1013556
  have htrace : WordTrace (prefixWord ++ tailWord_1013556) baseStart_1013556 baseEnd_1013556 := by
    simpa [prefixWord, tailWord_1013556, baseEnd_1013556] using wordTrace_append hprefix tailTrace_1013556
  have hstable : (prefixWord ++ tailWord_1013556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013556).length < 2 ^ (prefixWord ++ tailWord_1013556).sum := by decide
  have hdescent : baseEnd_1013556 < baseStart_1013556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013630 : List Nat := [4, 2, 3, 1, 1, 2, 1, 3, 2, 1, 3]
def baseStart_1013630 : Nat := 118140960795 + 1013630 * 2 ^ 59
def prefixEnd_1013630 : Nat := 4983230072969 + 3 ^ 40 * 1013630 * 2
def baseEnd_1013630 : Nat := 520479395816974401663407

theorem tailTrace_1013630 : CollatzResearch.WordTrace tailWord_1013630 prefixEnd_1013630 520479395816974401663407 := by
  unfold tailWord_1013630
  simp only [CollatzResearch.WordTrace]
  refine ⟨4621265414724887383347793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24646748878532732711188229 4621265414724887383347793)
  ·
    refine ⟨3465949061043665537510845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4621265414724887383347793 3465949061043665537510845)
    ·
      refine ⟨1299730897891374576566567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3465949061043665537510845 1299730897891374576566567)
      ·
        refine ⟨1949596346837061864849851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1299730897891374576566567 1949596346837061864849851)
        ·
          refine ⟨2924394520255592797274777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1949596346837061864849851 2924394520255592797274777)
          ·
            refine ⟨2193295890191694597956083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2924394520255592797274777 2193295890191694597956083)
            ·
              refine ⟨3289943835287541896934125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2193295890191694597956083 3289943835287541896934125)
              ·
                refine ⟨1233728938232828211350297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3289943835287541896934125 1233728938232828211350297)
                ·
                  refine ⟨925296703674621158512723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1233728938232828211350297 925296703674621158512723)
                  ·
                    refine ⟨1387945055511931737769085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 925296703674621158512723 1387945055511931737769085)
                    ·
                      refine ⟨520479395816974401663407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1387945055511931737769085 520479395816974401663407)
                      ·
                        rfl

theorem cell23_1013630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_1013630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1013630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1013630 prefixEnd_1013630 := by exact prefixLift 1013630
  have htrace : WordTrace (prefixWord ++ tailWord_1013630) baseStart_1013630 baseEnd_1013630 := by
    simpa [prefixWord, tailWord_1013630, baseEnd_1013630] using wordTrace_append hprefix tailTrace_1013630
  have hstable : (prefixWord ++ tailWord_1013630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013630).length < 2 ^ (prefixWord ++ tailWord_1013630).sum := by decide
  have hdescent : baseEnd_1013630 < baseStart_1013630 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013632 : List Nat := [2, 1, 1, 2, 1, 2, 4, 1, 1, 4, 4]
def baseStart_1013632 : Nat := 118140960795 + 1013632 * 2 ^ 59
def prefixEnd_1013632 : Nat := 4983230072969 + 3 ^ 40 * 1013632 * 2
def baseEnd_1013632 : Nat := 520480422778283393838397

theorem tailTrace_1013632 : CollatzResearch.WordTrace tailWord_1013632 prefixEnd_1013632 520480422778283393838397 := by
  unfold tailWord_1013632
  simp only [CollatzResearch.WordTrace]
  refine ⟨18485098131895926704177575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24646797509194568938903433 18485098131895926704177575)
  ·
    refine ⟨27727647197843890056266363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18485098131895926704177575 27727647197843890056266363)
    ·
      refine ⟨41591470796765835084399545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27727647197843890056266363 41591470796765835084399545)
      ·
        refine ⟨31193603097574376313299659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41591470796765835084399545 31193603097574376313299659)
        ·
          refine ⟨46790404646361564469949489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31193603097574376313299659 46790404646361564469949489)
          ·
            refine ⟨35092803484771173352462117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46790404646361564469949489 35092803484771173352462117)
            ·
              refine ⟨6579900653394595003586647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35092803484771173352462117 6579900653394595003586647)
              ·
                refine ⟨9869850980091892505379971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6579900653394595003586647 9869850980091892505379971)
                ·
                  refine ⟨14804776470137838758069957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9869850980091892505379971 14804776470137838758069957)
                  ·
                    refine ⟨2775895588150844767138117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14804776470137838758069957 2775895588150844767138117)
                    ·
                      refine ⟨520480422778283393838397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2775895588150844767138117 520480422778283393838397)
                      ·
                        rfl

theorem cell23_1013632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 1, 1, 4, 4].length) (baseStart_1013632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1013632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1013632 prefixEnd_1013632 := by exact prefixLift 1013632
  have htrace : WordTrace (prefixWord ++ tailWord_1013632) baseStart_1013632 baseEnd_1013632 := by
    simpa [prefixWord, tailWord_1013632, baseEnd_1013632] using wordTrace_append hprefix tailTrace_1013632
  have hstable : (prefixWord ++ tailWord_1013632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013632).length < 2 ^ (prefixWord ++ tailWord_1013632).sum := by decide
  have hdescent : baseEnd_1013632 < baseStart_1013632 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013640 : List Nat := [2, 1, 3, 3, 3, 2, 1, 2, 1, 3, 2]
def baseStart_1013640 : Nat := 118140960795 + 1013640 * 2 ^ 59
def prefixEnd_1013640 : Nat := 4983230072969 + 3 ^ 40 * 1013640 * 2
def baseEnd_1013640 : Nat := 520484530623519362538361

theorem tailTrace_1013640 : CollatzResearch.WordTrace tailWord_1013640 prefixEnd_1013640 520484530623519362538361 := by
  unfold tailWord_1013640
  simp only [CollatzResearch.WordTrace]
  refine ⟨18485244023881435387323187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24646992031841913849764249 18485244023881435387323187)
  ·
    refine ⟨27727866035822153080984781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18485244023881435387323187 27727866035822153080984781)
    ·
      refine ⟨10397949763433307405369293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27727866035822153080984781 10397949763433307405369293)
      ·
        refine ⟨3899231161287490277013485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10397949763433307405369293 3899231161287490277013485)
        ·
          refine ⟨1462211685482808853880057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3899231161287490277013485 1462211685482808853880057)
          ·
            refine ⟨1096658764112106640410043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1462211685482808853880057 1096658764112106640410043)
            ·
              refine ⟨1644988146168159960615065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1096658764112106640410043 1644988146168159960615065)
              ·
                refine ⟨1233741109626119970461299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1644988146168159960615065 1233741109626119970461299)
                ·
                  refine ⟨1850611664439179955691949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1233741109626119970461299 1850611664439179955691949)
                  ·
                    refine ⟨693979374164692483384481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1850611664439179955691949 693979374164692483384481)
                    ·
                      refine ⟨520484530623519362538361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 693979374164692483384481 520484530623519362538361)
                      ·
                        rfl

theorem cell23_1013640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 1, 2, 1, 3, 2].length) (baseStart_1013640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1013640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1013640 prefixEnd_1013640 := by exact prefixLift 1013640
  have htrace : WordTrace (prefixWord ++ tailWord_1013640) baseStart_1013640 baseEnd_1013640 := by
    simpa [prefixWord, tailWord_1013640, baseEnd_1013640] using wordTrace_append hprefix tailTrace_1013640
  have hstable : (prefixWord ++ tailWord_1013640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013640).length < 2 ^ (prefixWord ++ tailWord_1013640).sum := by decide
  have hdescent : baseEnd_1013640 < baseStart_1013640 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013679 : List Nat := [1, 1, 2, 1, 2, 2, 3, 1, 1, 7, 2]
def baseStart_1013679 : Nat := 118140960795 + 1013679 * 2 ^ 59
def prefixEnd_1013679 : Nat := 4983230072969 + 3 ^ 40 * 1013679 * 2
def baseEnd_1013679 : Nat := 520504556369044709950681

theorem tailTrace_1013679 : CollatzResearch.WordTrace tailWord_1013679 prefixEnd_1013679 520504556369044709950681 := by
  unfold tailWord_1013679
  simp only [CollatzResearch.WordTrace]
  refine ⟨36971910494621580435316091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24647940329747720290210727 36971910494621580435316091)
  ·
    refine ⟨55457865741932370652974137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36971910494621580435316091 55457865741932370652974137)
    ·
      refine ⟨41593399306449277989730603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55457865741932370652974137 41593399306449277989730603)
      ·
        refine ⟨62390098959673916984595905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41593399306449277989730603 62390098959673916984595905)
        ·
          refine ⟨46792574219755437738446929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62390098959673916984595905 46792574219755437738446929)
          ·
            refine ⟨35094430664816578303835197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46792574219755437738446929 35094430664816578303835197)
            ·
              refine ⟨13160411499306216863938199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35094430664816578303835197 13160411499306216863938199)
              ·
                refine ⟨19740617248959325295907299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13160411499306216863938199 19740617248959325295907299)
                ·
                  refine ⟨29610925873438987943860949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19740617248959325295907299 29610925873438987943860949)
                  ·
                    refine ⟨694006075158726279934241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29610925873438987943860949 694006075158726279934241)
                    ·
                      refine ⟨520504556369044709950681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 694006075158726279934241 520504556369044709950681)
                      ·
                        rfl

theorem cell23_1013679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 7, 2].length) (baseStart_1013679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1013679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1013679 prefixEnd_1013679 := by exact prefixLift 1013679
  have htrace : WordTrace (prefixWord ++ tailWord_1013679) baseStart_1013679 baseEnd_1013679 := by
    simpa [prefixWord, tailWord_1013679, baseEnd_1013679] using wordTrace_append hprefix tailTrace_1013679
  have hstable : (prefixWord ++ tailWord_1013679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013679).length < 2 ^ (prefixWord ++ tailWord_1013679).sum := by decide
  have hdescent : baseEnd_1013679 < baseStart_1013679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013719 : List Nat := [1, 1, 3, 2, 1, 1, 3, 2, 5, 4]
def baseStart_1013719 : Nat := 118140960795 + 1013719 * 2 ^ 59
def prefixEnd_1013719 : Nat := 4983230072969 + 3 ^ 40 * 1013719 * 2
def baseEnd_1013719 : Nat := 173508365198408184483499

theorem tailTrace_1013719 : CollatzResearch.WordTrace tailWord_1013719 prefixEnd_1013719 173508365198408184483499 := by
  unfold tailWord_1013719
  simp only [CollatzResearch.WordTrace]
  refine ⟨36973369414476667266772211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24648912942984444844514807 36973369414476667266772211)
  ·
    refine ⟨55460054121715000900158317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36973369414476667266772211 55460054121715000900158317)
    ·
      refine ⟨20797520295643125337559369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55460054121715000900158317 20797520295643125337559369)
      ·
        refine ⟨15598140221732344003169527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20797520295643125337559369 15598140221732344003169527)
        ·
          refine ⟨23397210332598516004754291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15598140221732344003169527 23397210332598516004754291)
          ·
            refine ⟨35095815498897774007131437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23397210332598516004754291 35095815498897774007131437)
            ·
              refine ⟨13160930812086665252674289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35095815498897774007131437 13160930812086665252674289)
              ·
                refine ⟨9870698109064998939505717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13160930812086665252674289 9870698109064998939505717)
                ·
                  refine ⟨925377947724843650578661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9870698109064998939505717 925377947724843650578661)
                  ·
                    refine ⟨173508365198408184483499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 925377947724843650578661 173508365198408184483499)
                    ·
                      rfl

theorem cell23_1013719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 2, 5, 4].length) (baseStart_1013719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1013719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1013719 prefixEnd_1013719 := by exact prefixLift 1013719
  have htrace : WordTrace (prefixWord ++ tailWord_1013719) baseStart_1013719 baseEnd_1013719 := by
    simpa [prefixWord, tailWord_1013719, baseEnd_1013719] using wordTrace_append hprefix tailTrace_1013719
  have hstable : (prefixWord ++ tailWord_1013719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013719).length < 2 ^ (prefixWord ++ tailWord_1013719).sum := by decide
  have hdescent : baseEnd_1013719 < baseStart_1013719 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013819 : List Nat := [1, 1, 1, 1, 1, 2, 1, 4, 2, 6, 3]
def baseStart_1013819 : Nat := 118140960795 + 1013819 * 2 ^ 59
def prefixEnd_1013819 : Nat := 4983230072969 + 3 ^ 40 * 1013819 * 2
def baseEnd_1013819 : Nat := 520576443660674162200037

theorem tailTrace_1013819 : CollatzResearch.WordTrace tailWord_1013819 prefixEnd_1013819 520576443660674162200037 := by
  unfold tailWord_1013819
  simp only [CollatzResearch.WordTrace]
  refine ⟨36977016714114384345412511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24651344476076256230275007 36977016714114384345412511)
  ·
    refine ⟨55465525071171576518118767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36977016714114384345412511 55465525071171576518118767)
    ·
      refine ⟨83198287606757364777178151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55465525071171576518118767 83198287606757364777178151)
      ·
        refine ⟨124797431410136047165767227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83198287606757364777178151 124797431410136047165767227)
        ·
          refine ⟨187196147115204070748650841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124797431410136047165767227 187196147115204070748650841)
          ·
            refine ⟨140397110336403053061488131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187196147115204070748650841 140397110336403053061488131)
            ·
              refine ⟨210595665504604579592232197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140397110336403053061488131 210595665504604579592232197)
              ·
                refine ⟨39486687282113358673543537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 210595665504604579592232197 39486687282113358673543537)
                ·
                  refine ⟨29615015461585019005157653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39486687282113358673543537 29615015461585019005157653)
                  ·
                    refine ⟨1388203849761797765866765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29615015461585019005157653 1388203849761797765866765)
                    ·
                      refine ⟨520576443660674162200037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1388203849761797765866765 520576443660674162200037)
                      ·
                        rfl

theorem cell23_1013819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 6, 3].length) (baseStart_1013819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1013819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1013819 prefixEnd_1013819 := by exact prefixLift 1013819
  have htrace : WordTrace (prefixWord ++ tailWord_1013819) baseStart_1013819 baseEnd_1013819 := by
    simpa [prefixWord, tailWord_1013819, baseEnd_1013819] using wordTrace_append hprefix tailTrace_1013819
  have hstable : (prefixWord ++ tailWord_1013819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013819).length < 2 ^ (prefixWord ++ tailWord_1013819).sum := by decide
  have hdescent : baseEnd_1013819 < baseStart_1013819 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013833 : List Nat := [1, 2, 1, 1, 2, 2, 7, 1, 1, 1, 4]
def baseStart_1013833 : Nat := 118140960795 + 1013833 * 2 ^ 59
def prefixEnd_1013833 : Nat := 4983230072969 + 3 ^ 40 * 1013833 * 2
def baseEnd_1013833 : Nat := 520583632389837107424973

theorem tailTrace_1013833 : CollatzResearch.WordTrace tailWord_1013833 prefixEnd_1013833 520583632389837107424973 := by
  unfold tailWord_1013833
  simp only [CollatzResearch.WordTrace]
  refine ⟨36977527336063664736422153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24651684890709109824281435 36977527336063664736422153)
  ·
    refine ⟨27733145502047748552316615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36977527336063664736422153 27733145502047748552316615)
    ·
      refine ⟨41599718253071622828474923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27733145502047748552316615 41599718253071622828474923)
      ·
        refine ⟨62399577379607434242712385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41599718253071622828474923 62399577379607434242712385)
        ·
          refine ⟨46799683034705575682034289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62399577379607434242712385 46799683034705575682034289)
          ·
            refine ⟨35099762276029181761525717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46799683034705575682034289 35099762276029181761525717)
            ·
              refine ⟨822650678344433947535759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 35099762276029181761525717 822650678344433947535759)
              ·
                refine ⟨1233976017516650921303639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 822650678344433947535759 1233976017516650921303639)
                ·
                  refine ⟨1850964026274976381955459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1233976017516650921303639 1850964026274976381955459)
                  ·
                    refine ⟨2776446039412464572933189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1850964026274976381955459 2776446039412464572933189)
                    ·
                      refine ⟨520583632389837107424973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2776446039412464572933189 520583632389837107424973)
                      ·
                        rfl

theorem cell23_1013833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 7, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 7, 1, 1, 1, 4].length) (baseStart_1013833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1013833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1013833 prefixEnd_1013833 := by exact prefixLift 1013833
  have htrace : WordTrace (prefixWord ++ tailWord_1013833) baseStart_1013833 baseEnd_1013833 := by
    simpa [prefixWord, tailWord_1013833, baseEnd_1013833] using wordTrace_append hprefix tailTrace_1013833
  have hstable : (prefixWord ++ tailWord_1013833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013833).length < 2 ^ (prefixWord ++ tailWord_1013833).sum := by decide
  have hdescent : baseEnd_1013833 < baseStart_1013833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013836 : List Nat := [2, 2, 1, 3, 1, 1, 5, 1, 1, 1, 5]
def baseStart_1013836 : Nat := 118140960795 + 1013836 * 2 ^ 59
def prefixEnd_1013836 : Nat := 4983230072969 + 3 ^ 40 * 1013836 * 2
def baseEnd_1013836 : Nat := 520585172831800595687459

theorem tailTrace_1013836 : CollatzResearch.WordTrace tailWord_1013836 prefixEnd_1013836 520585172831800595687459 := by
  unfold tailWord_1013836
  simp only [CollatzResearch.WordTrace]
  refine ⟨18488818377526398124390681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24651757836701864165854241 18488818377526398124390681)
  ·
    refine ⟨13866613783144798593293011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18488818377526398124390681 13866613783144798593293011)
    ·
      refine ⟨20799920674717197889939517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13866613783144798593293011 20799920674717197889939517)
      ·
        refine ⟨7799970253018949208727319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20799920674717197889939517 7799970253018949208727319)
        ·
          refine ⟨11699955379528423813090979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7799970253018949208727319 11699955379528423813090979)
          ·
            refine ⟨17549933069292635719636469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11699955379528423813090979 17549933069292635719636469)
            ·
              refine ⟨1645306225246184598715919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17549933069292635719636469 1645306225246184598715919)
              ·
                refine ⟨2467959337869276898073879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1645306225246184598715919 2467959337869276898073879)
                ·
                  refine ⟨3701939006803915347110819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2467959337869276898073879 3701939006803915347110819)
                  ·
                    refine ⟨5552908510205873020666229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3701939006803915347110819 5552908510205873020666229)
                    ·
                      refine ⟨520585172831800595687459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5552908510205873020666229 520585172831800595687459)
                      ·
                        rfl

theorem cell23_1013836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5, 1, 1, 1, 5].length) (baseStart_1013836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1013836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1013836 prefixEnd_1013836 := by exact prefixLift 1013836
  have htrace : WordTrace (prefixWord ++ tailWord_1013836) baseStart_1013836 baseEnd_1013836 := by
    simpa [prefixWord, tailWord_1013836, baseEnd_1013836] using wordTrace_append hprefix tailTrace_1013836
  have hstable : (prefixWord ++ tailWord_1013836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013836).length < 2 ^ (prefixWord ++ tailWord_1013836).sum := by decide
  have hdescent : baseEnd_1013836 < baseStart_1013836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013856 : List Nat := [2, 1, 1, 3, 2, 5, 1, 8]
def baseStart_1013856 : Nat := 118140960795 + 1013856 * 2 ^ 59
def prefixEnd_1013856 : Nat := 4983230072969 + 3 ^ 40 * 1013856 * 2
def baseEnd_1013856 : Nat := 19281312683144093238421

theorem tailTrace_1013856 : CollatzResearch.WordTrace tailWord_1013856 prefixEnd_1013856 19281312683144093238421 := by
  unfold tailWord_1013856
  simp only [CollatzResearch.WordTrace]
  refine ⟨18489183107490169832254711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24652244143320226443006281 18489183107490169832254711)
  ·
    refine ⟨27733774661235254748382067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18489183107490169832254711 27733774661235254748382067)
    ·
      refine ⟨41600661991852882122573101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27733774661235254748382067 41600661991852882122573101)
      ·
        refine ⟨15600248246944830795964913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41600661991852882122573101 15600248246944830795964913)
        ·
          refine ⟨11700186185208623096973685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15600248246944830795964913 11700186185208623096973685)
          ·
            refine ⟨1096892454863308415341283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11700186185208623096973685 1096892454863308415341283)
            ·
              refine ⟨1645338682294962623011925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1096892454863308415341283 1645338682294962623011925)
              ·
                refine ⟨19281312683144093238421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1645338682294962623011925 19281312683144093238421)
                ·
                  rfl

theorem cell23_1013856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 1, 8].length) (baseStart_1013856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1013856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1013856 prefixEnd_1013856 := by exact prefixLift 1013856
  have htrace : WordTrace (prefixWord ++ tailWord_1013856) baseStart_1013856 baseEnd_1013856 := by
    simpa [prefixWord, tailWord_1013856, baseEnd_1013856] using wordTrace_append hprefix tailTrace_1013856
  have hstable : (prefixWord ++ tailWord_1013856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013856).length < 2 ^ (prefixWord ++ tailWord_1013856).sum := by decide
  have hdescent : baseEnd_1013856 < baseStart_1013856 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013859 : List Nat := [1, 1, 1, 5, 1, 1, 2, 1, 2, 2, 6]
def baseStart_1013859 : Nat := 118140960795 + 1013859 * 2 ^ 59
def prefixEnd_1013859 : Nat := 4983230072969 + 3 ^ 40 * 1013859 * 2
def baseEnd_1013859 : Nat := 520596982886854005699853

theorem tailTrace_1013859 : CollatzResearch.WordTrace tailWord_1013859 prefixEnd_1013859 520596982886854005699853 := by
  unfold tailWord_1013859
  simp only [CollatzResearch.WordTrace]
  refine ⟨36978475633969471176868631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24652317089312980784579087 36978475633969471176868631)
  ·
    refine ⟨55467713450954206765302947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36978475633969471176868631 55467713450954206765302947)
    ·
      refine ⟨83201570176431310147954421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55467713450954206765302947 83201570176431310147954421)
      ·
        refine ⟨7800147204040435326370727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 83201570176431310147954421 7800147204040435326370727)
        ·
          refine ⟨11700220806060652989556091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7800147204040435326370727 11700220806060652989556091)
          ·
            refine ⟨17550331209090979484334137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11700220806060652989556091 17550331209090979484334137)
            ·
              refine ⟨13162748406818234613250603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17550331209090979484334137 13162748406818234613250603)
              ·
                refine ⟨19744122610227351919875905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13162748406818234613250603 19744122610227351919875905)
                ·
                  refine ⟨14808091957670513939906929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19744122610227351919875905 14808091957670513939906929)
                  ·
                    refine ⟨11106068968252885454930197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14808091957670513939906929 11106068968252885454930197)
                    ·
                      refine ⟨520596982886854005699853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11106068968252885454930197 520596982886854005699853)
                      ·
                        rfl

theorem cell23_1013859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 2, 2, 6].length) (baseStart_1013859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1013859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1013859 prefixEnd_1013859 := by exact prefixLift 1013859
  have htrace : WordTrace (prefixWord ++ tailWord_1013859) baseStart_1013859 baseEnd_1013859 := by
    simpa [prefixWord, tailWord_1013859, baseEnd_1013859] using wordTrace_append hprefix tailTrace_1013859
  have hstable : (prefixWord ++ tailWord_1013859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013859).length < 2 ^ (prefixWord ++ tailWord_1013859).sum := by decide
  have hdescent : baseEnd_1013859 < baseStart_1013859 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013916 : List Nat := [2, 2, 3, 2, 1, 1, 1, 3, 2, 6]
def baseStart_1013916 : Nat := 118140960795 + 1013916 * 2 ^ 59
def prefixEnd_1013916 : Nat := 4983230072969 + 3 ^ 40 * 1013916 * 2
def baseEnd_1013916 : Nat := 173542083761386760895697

theorem tailTrace_1013916 : CollatzResearch.WordTrace tailWord_1013916 prefixEnd_1013916 173542083761386760895697 := by
  unfold tailWord_1013916
  simp only [CollatzResearch.WordTrace]
  refine ⟨18490277297381484955846801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24653703063175313274462401 18490277297381484955846801)
  ·
    refine ⟨13867707973036113716885101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18490277297381484955846801 13867707973036113716885101)
    ·
      refine ⟨5200390489888542643831913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13867707973036113716885101 5200390489888542643831913)
      ·
        refine ⟨3900292867416406982873935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5200390489888542643831913 3900292867416406982873935)
        ·
          refine ⟨5850439301124610474310903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3900292867416406982873935 5850439301124610474310903)
          ·
            refine ⟨8775658951686915711466355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5850439301124610474310903 8775658951686915711466355)
            ·
              refine ⟨13163488427530373567199533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8775658951686915711466355 13163488427530373567199533)
              ·
                refine ⟨4936308160323890087699825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13163488427530373567199533 4936308160323890087699825)
                ·
                  refine ⟨3702231120242917565774869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4936308160323890087699825 3702231120242917565774869)
                  ·
                    refine ⟨173542083761386760895697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3702231120242917565774869 173542083761386760895697)
                    ·
                      rfl

theorem cell23_1013916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 3, 2, 6].length) (baseStart_1013916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1013916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1013916 prefixEnd_1013916 := by exact prefixLift 1013916
  have htrace : WordTrace (prefixWord ++ tailWord_1013916) baseStart_1013916 baseEnd_1013916 := by
    simpa [prefixWord, tailWord_1013916, baseEnd_1013916] using wordTrace_append hprefix tailTrace_1013916
  have hstable : (prefixWord ++ tailWord_1013916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013916).length < 2 ^ (prefixWord ++ tailWord_1013916).sum := by decide
  have hdescent : baseEnd_1013916 < baseStart_1013916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013917 : List Nat := [1, 4, 2, 1, 1, 4, 3, 1, 2, 1, 3]
def baseStart_1013917 : Nat := 118140960795 + 1013917 * 2 ^ 59
def prefixEnd_1013917 : Nat := 4983230072969 + 3 ^ 40 * 1013917 * 2
def baseEnd_1013917 : Nat := 520626764764814778774587

theorem tailTrace_1013917 : CollatzResearch.WordTrace tailWord_1013917 prefixEnd_1013917 520626764764814778774587 := by
  unfold tailWord_1013917
  simp only [CollatzResearch.WordTrace]
  refine ⟨36980591067759347082480005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24653727378506231388320003 36980591067759347082480005)
  ·
    refine ⟨6933860825204877577965001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36980591067759347082480005 6933860825204877577965001)
    ·
      refine ⟨5200395618903658183473751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6933860825204877577965001 5200395618903658183473751)
      ·
        refine ⟨7800593428355487275210627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5200395618903658183473751 7800593428355487275210627)
        ·
          refine ⟨11700890142533230912815941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7800593428355487275210627 11700890142533230912815941)
          ·
            refine ⟨2193916901724980796152989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11700890142533230912815941 2193916901724980796152989)
            ·
              refine ⟨822718838146867798557371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2193916901724980796152989 822718838146867798557371)
              ·
                refine ⟨1234078257220301697836057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 822718838146867798557371 1234078257220301697836057)
                ·
                  refine ⟨925558692915226273377043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1234078257220301697836057 925558692915226273377043)
                  ·
                    refine ⟨1388338039372839410065565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 925558692915226273377043 1388338039372839410065565)
                    ·
                      refine ⟨520626764764814778774587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1388338039372839410065565 520626764764814778774587)
                      ·
                        rfl

theorem cell23_1013917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 3, 1, 2, 1, 3].length) (baseStart_1013917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1013917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1013917 prefixEnd_1013917 := by exact prefixLift 1013917
  have htrace : WordTrace (prefixWord ++ tailWord_1013917) baseStart_1013917 baseEnd_1013917 := by
    simpa [prefixWord, tailWord_1013917, baseEnd_1013917] using wordTrace_append hprefix tailTrace_1013917
  have hstable : (prefixWord ++ tailWord_1013917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013917).length < 2 ^ (prefixWord ++ tailWord_1013917).sum := by decide
  have hdescent : baseEnd_1013917 < baseStart_1013917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014013 : List Nat := [1, 4, 1, 1, 1, 1, 1, 2, 3, 6, 2]
def baseStart_1014013 : Nat := 118140960795 + 1014013 * 2 ^ 59
def prefixEnd_1014013 : Nat := 4983230072969 + 3 ^ 40 * 1014013 * 2
def baseEnd_1014013 : Nat := 520676058907646403174145

theorem tailTrace_1014013 : CollatzResearch.WordTrace tailWord_1014013 prefixEnd_1014013 520676058907646403174145 := by
  unfold tailWord_1014013
  simp only [CollatzResearch.WordTrace]
  refine ⟨36984092475411555477974693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24656061650274370318649795 36984092475411555477974693)
  ·
    refine ⟨6934517339139666652120255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36984092475411555477974693 6934517339139666652120255)
    ·
      refine ⟨10401776008709499978180383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6934517339139666652120255 10401776008709499978180383)
      ·
        refine ⟨15602664013064249967270575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10401776008709499978180383 15602664013064249967270575)
        ·
          refine ⟨23403996019596374950905863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15602664013064249967270575 23403996019596374950905863)
          ·
            refine ⟨35105994029394562426358795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23403996019596374950905863 35105994029394562426358795)
            ·
              refine ⟨52658991044091843639538193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35105994029394562426358795 52658991044091843639538193)
              ·
                refine ⟨39494243283068882729653645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52658991044091843639538193 39494243283068882729653645)
                ·
                  refine ⟨14810341231150831023620117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39494243283068882729653645 14810341231150831023620117)
                  ·
                    refine ⟨694234745210195204232193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14810341231150831023620117 694234745210195204232193)
                    ·
                      refine ⟨520676058907646403174145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 694234745210195204232193 520676058907646403174145)
                      ·
                        rfl

theorem cell23_1014013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 3, 6, 2].length) (baseStart_1014013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1014013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1014013 prefixEnd_1014013 := by exact prefixLift 1014013
  have htrace : WordTrace (prefixWord ++ tailWord_1014013) baseStart_1014013 baseEnd_1014013 := by
    simpa [prefixWord, tailWord_1014013, baseEnd_1014013] using wordTrace_append hprefix tailTrace_1014013
  have hstable : (prefixWord ++ tailWord_1014013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014013).length < 2 ^ (prefixWord ++ tailWord_1014013).sum := by decide
  have hdescent : baseEnd_1014013 < baseStart_1014013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014030 : List Nat := [4, 1, 1, 2, 1, 2, 3, 1, 2, 4, 2]
def baseStart_1014030 : Nat := 118140960795 + 1014030 * 2 ^ 59
def prefixEnd_1014030 : Nat := 4983230072969 + 3 ^ 40 * 1014030 * 2
def baseEnd_1014030 : Nat := 520684788078772836661567

theorem tailTrace_1014030 : CollatzResearch.WordTrace tailWord_1014030 prefixEnd_1014030 520684788078772836661567 := by
  unfold tailWord_1014030
  simp only [CollatzResearch.WordTrace]
  refine ⟨4623089064543745922667943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24656475010899978254229029 4623089064543745922667943)
  ·
    refine ⟨6934633596815618884001915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4623089064543745922667943 6934633596815618884001915)
    ·
      refine ⟨10401950395223428326002873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6934633596815618884001915 10401950395223428326002873)
      ·
        refine ⟨7801462796417571244502155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10401950395223428326002873 7801462796417571244502155)
        ·
          refine ⟨11702194194626356866753233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7801462796417571244502155 11702194194626356866753233)
          ·
            refine ⟨8776645645969767650064925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11702194194626356866753233 8776645645969767650064925)
            ·
              refine ⟨3291242117238662868774347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8776645645969767650064925 3291242117238662868774347)
              ·
                refine ⟨4936863175857994303161521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3291242117238662868774347 4936863175857994303161521)
                ·
                  refine ⟨3702647381893495727371141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4936863175857994303161521 3702647381893495727371141)
                  ·
                    refine ⟨694246384105030448882089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3702647381893495727371141 694246384105030448882089)
                    ·
                      refine ⟨520684788078772836661567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 694246384105030448882089 520684788078772836661567)
                      ·
                        rfl

theorem cell23_1014030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 1, 2, 4, 2].length) (baseStart_1014030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1014030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1014030 prefixEnd_1014030 := by exact prefixLift 1014030
  have htrace : WordTrace (prefixWord ++ tailWord_1014030) baseStart_1014030 baseEnd_1014030 := by
    simpa [prefixWord, tailWord_1014030, baseEnd_1014030] using wordTrace_append hprefix tailTrace_1014030
  have hstable : (prefixWord ++ tailWord_1014030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014030).length < 2 ^ (prefixWord ++ tailWord_1014030).sum := by decide
  have hdescent : baseEnd_1014030 < baseStart_1014030 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014050 : List Nat := [3, 3, 1, 1, 3, 2, 1, 1, 1, 4, 3]
def baseStart_1014050 : Nat := 118140960795 + 1014050 * 2 ^ 59
def prefixEnd_1014050 : Nat := 4983230072969 + 3 ^ 40 * 1014050 * 2
def baseEnd_1014050 : Nat := 520695057691862758411475

theorem tailTrace_1014050 : CollatzResearch.WordTrace tailWord_1014050 prefixEnd_1014050 520695057691862758411475 := by
  unfold tailWord_1014050
  simp only [CollatzResearch.WordTrace]
  refine ⟨9246360494069377699267901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24656961317518340531381069 9246360494069377699267901)
  ·
    refine ⟨3467385185276016637225463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9246360494069377699267901 3467385185276016637225463)
    ·
      refine ⟨5201077777914024955838195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3467385185276016637225463 5201077777914024955838195)
      ·
        refine ⟨7801616666871037433757293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5201077777914024955838195 7801616666871037433757293)
        ·
          refine ⟨2925606250076639037658985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7801616666871037433757293 2925606250076639037658985)
          ·
            refine ⟨2194204687557479278244239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2925606250076639037658985 2194204687557479278244239)
            ·
              refine ⟨3291307031336218917366359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2194204687557479278244239 3291307031336218917366359)
              ·
                refine ⟨4936960547004328376049539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3291307031336218917366359 4936960547004328376049539)
                ·
                  refine ⟨7405440820506492564074309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4936960547004328376049539 7405440820506492564074309)
                  ·
                    refine ⟨1388520153844967355763933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7405440820506492564074309 1388520153844967355763933)
                    ·
                      refine ⟨520695057691862758411475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1388520153844967355763933 520695057691862758411475)
                      ·
                        rfl

theorem cell23_1014050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 1, 1, 4, 3].length) (baseStart_1014050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1014050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1014050 prefixEnd_1014050 := by exact prefixLift 1014050
  have htrace : WordTrace (prefixWord ++ tailWord_1014050) baseStart_1014050 baseEnd_1014050 := by
    simpa [prefixWord, tailWord_1014050, baseEnd_1014050] using wordTrace_append hprefix tailTrace_1014050
  have hstable : (prefixWord ++ tailWord_1014050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014050).length < 2 ^ (prefixWord ++ tailWord_1014050).sum := by decide
  have hdescent : baseEnd_1014050 < baseStart_1014050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014073 : List Nat := [1, 2, 1, 6, 1, 1, 1, 1, 1, 2, 6]
def baseStart_1014073 : Nat := 118140960795 + 1014073 * 2 ^ 59
def prefixEnd_1014073 : Nat := 4983230072969 + 3 ^ 40 * 1014073 * 2
def baseEnd_1014073 : Nat := 520706867746916168423869

theorem tailTrace_1014073 : CollatzResearch.WordTrace tailWord_1014073 prefixEnd_1014073 520706867746916168423869 := by
  unfold tailWord_1014073
  simp only [CollatzResearch.WordTrace]
  refine ⟨36986280855194185725158873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24657520570129457150105915 36986280855194185725158873)
  ·
    refine ⟨27739710641395639293869155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36986280855194185725158873 27739710641395639293869155)
    ·
      refine ⟨41609565962093458940803733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27739710641395639293869155 41609565962093458940803733)
      ·
        refine ⟨1950448404473130887850175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 41609565962093458940803733 1950448404473130887850175)
        ·
          refine ⟨2925672606709696331775263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1950448404473130887850175 2925672606709696331775263)
          ·
            refine ⟨4388508910064544497662895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2925672606709696331775263 4388508910064544497662895)
            ·
              refine ⟨6582763365096816746494343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4388508910064544497662895 6582763365096816746494343)
              ·
                refine ⟨9874145047645225119741515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6582763365096816746494343 9874145047645225119741515)
                ·
                  refine ⟨14811217571467837679612273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9874145047645225119741515 14811217571467837679612273)
                  ·
                    refine ⟨11108413178600878259709205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14811217571467837679612273 11108413178600878259709205)
                    ·
                      refine ⟨520706867746916168423869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11108413178600878259709205 520706867746916168423869)
                      ·
                        rfl

theorem cell23_1014073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_1014073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1014073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1014073 prefixEnd_1014073 := by exact prefixLift 1014073
  have htrace : WordTrace (prefixWord ++ tailWord_1014073) baseStart_1014073 baseEnd_1014073 := by
    simpa [prefixWord, tailWord_1014073, baseEnd_1014073] using wordTrace_append hprefix tailTrace_1014073
  have hstable : (prefixWord ++ tailWord_1014073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014073).length < 2 ^ (prefixWord ++ tailWord_1014073).sum := by decide
  have hdescent : baseEnd_1014073 < baseStart_1014073 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014100 : List Nat := [2, 4, 1, 1, 2, 2, 1, 4, 1, 5]
def baseStart_1014100 : Nat := 118140960795 + 1014100 * 2 ^ 59
def prefixEnd_1014100 : Nat := 4983230072969 + 3 ^ 40 * 1014100 * 2
def baseEnd_1014100 : Nat := 173573577241529187595415

theorem tailTrace_1014100 : CollatzResearch.WordTrace tailWord_1014100 prefixEnd_1014100 173573577241529187595415 := by
  unfold tailWord_1014100
  simp only [CollatzResearch.WordTrace]
  refine ⟨18493632813048184668195877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24658177084064246224261169 18493632813048184668195877)
  ·
    refine ⟨3467556152446534625286727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18493632813048184668195877 3467556152446534625286727)
    ·
      refine ⟨5201334228669801937930091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3467556152446534625286727 5201334228669801937930091)
      ·
        refine ⟨7802001343004702906895137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5201334228669801937930091 7802001343004702906895137)
        ·
          refine ⟨5851501007253527180171353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7802001343004702906895137 5851501007253527180171353)
          ·
            refine ⟨4388625755440145385128515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5851501007253527180171353 4388625755440145385128515)
            ·
              refine ⟨6582938633160218077692773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4388625755440145385128515 6582938633160218077692773)
              ·
                refine ⟨1234300993717540889567395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6582938633160218077692773 1234300993717540889567395)
                ·
                  refine ⟨1851451490576311334351093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1234300993717540889567395 1851451490576311334351093)
                  ·
                    refine ⟨173573577241529187595415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1851451490576311334351093 173573577241529187595415)
                    ·
                      rfl

theorem cell23_1014100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 4, 1, 5].length) (baseStart_1014100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1014100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1014100 prefixEnd_1014100 := by exact prefixLift 1014100
  have htrace : WordTrace (prefixWord ++ tailWord_1014100) baseStart_1014100 baseEnd_1014100 := by
    simpa [prefixWord, tailWord_1014100, baseEnd_1014100] using wordTrace_append hprefix tailTrace_1014100
  have hstable : (prefixWord ++ tailWord_1014100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014100).length < 2 ^ (prefixWord ++ tailWord_1014100).sum := by decide
  have hdescent : baseEnd_1014100 < baseStart_1014100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014108 : List Nat := [2, 2, 4, 3, 2, 1, 1, 3, 1, 4]
def baseStart_1014108 : Nat := 118140960795 + 1014108 * 2 ^ 59
def prefixEnd_1014108 : Nat := 4983230072969 + 3 ^ 40 * 1014108 * 2
def baseEnd_1014108 : Nat := 173574946523274510495403

theorem tailTrace_1014108 : CollatzResearch.WordTrace tailWord_1014108 prefixEnd_1014108 173574946523274510495403 := by
  unfold tailWord_1014108
  simp only [CollatzResearch.WordTrace]
  refine ⟨18493778705033693351341489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24658371606711591135121985 18493778705033693351341489)
  ·
    refine ⟨13870334028775270013506117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18493778705033693351341489 13870334028775270013506117)
    ·
      refine ⟨2600687630395363127532397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13870334028775270013506117 2600687630395363127532397)
      ·
        refine ⟨975257861398261172824649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2600687630395363127532397 975257861398261172824649)
        ·
          refine ⟨731443396048695879618487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 975257861398261172824649 731443396048695879618487)
          ·
            refine ⟨1097165094073043819427731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 731443396048695879618487 1097165094073043819427731)
            ·
              refine ⟨1645747641109565729141597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1097165094073043819427731 1645747641109565729141597)
              ·
                refine ⟨617155365416087148428099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1645747641109565729141597 617155365416087148428099)
                ·
                  refine ⟨925733048124130722642149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 617155365416087148428099 925733048124130722642149)
                  ·
                    refine ⟨173574946523274510495403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 925733048124130722642149 173574946523274510495403)
                    ·
                      rfl

theorem cell23_1014108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 1, 3, 1, 4].length) (baseStart_1014108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1014108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1014108 prefixEnd_1014108 := by exact prefixLift 1014108
  have htrace : WordTrace (prefixWord ++ tailWord_1014108) baseStart_1014108 baseEnd_1014108 := by
    simpa [prefixWord, tailWord_1014108, baseEnd_1014108] using wordTrace_append hprefix tailTrace_1014108
  have hstable : (prefixWord ++ tailWord_1014108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014108).length < 2 ^ (prefixWord ++ tailWord_1014108).sum := by decide
  have hdescent : baseEnd_1014108 < baseStart_1014108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014130 : List Nat := [3, 2, 1, 2, 1, 3, 2, 1, 4, 4]
def baseStart_1014130 : Nat := 118140960795 + 1014130 * 2 ^ 59
def prefixEnd_1014130 : Nat := 4983230072969 + 3 ^ 40 * 1014130 * 2
def baseEnd_1014130 : Nat := 173578712048074148470369

theorem tailTrace_1014130 : CollatzResearch.WordTrace tailWord_1014130 prefixEnd_1014130 173578712048074148470369 := by
  unfold tailWord_1014130
  simp only [CollatzResearch.WordTrace]
  refine ⟨9247089953996921114995961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24658906543991789639989229 9247089953996921114995961)
  ·
    refine ⟨6935317465497690836246971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9247089953996921114995961 6935317465497690836246971)
    ·
      refine ⟨10402976198246536254370457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6935317465497690836246971 10402976198246536254370457)
      ·
        refine ⟨7802232148684902190777843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10402976198246536254370457 7802232148684902190777843)
        ·
          refine ⟨11703348223027353286166765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7802232148684902190777843 11703348223027353286166765)
          ·
            refine ⟨4388755583635257482312537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11703348223027353286166765 4388755583635257482312537)
            ·
              refine ⟨3291566687726443111734403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4388755583635257482312537 3291566687726443111734403)
              ·
                refine ⟨4937350031589664667601605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3291566687726443111734403 4937350031589664667601605)
                ·
                  refine ⟨925753130923062125175301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4937350031589664667601605 925753130923062125175301)
                  ·
                    refine ⟨173578712048074148470369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 925753130923062125175301 173578712048074148470369)
                    ·
                      rfl

theorem cell23_1014130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 1, 4, 4].length) (baseStart_1014130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1014130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1014130 prefixEnd_1014130 := by exact prefixLift 1014130
  have htrace : WordTrace (prefixWord ++ tailWord_1014130) baseStart_1014130 baseEnd_1014130 := by
    simpa [prefixWord, tailWord_1014130, baseEnd_1014130] using wordTrace_append hprefix tailTrace_1014130
  have hstable : (prefixWord ++ tailWord_1014130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014130).length < 2 ^ (prefixWord ++ tailWord_1014130).sum := by decide
  have hdescent : baseEnd_1014130 < baseStart_1014130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014147 : List Nat := [1, 1, 1, 3, 6, 1, 1, 3, 2, 4]
def baseStart_1014147 : Nat := 118140960795 + 1014147 * 2 ^ 59
def prefixEnd_1014147 : Nat := 4983230072969 + 3 ^ 40 * 1014147 * 2
def baseEnd_1014147 : Nat := 173581621771782959632843

theorem tailTrace_1014147 : CollatzResearch.WordTrace tailWord_1014147 prefixEnd_1014147 173581621771782959632843 := by
  unfold tailWord_1014147
  simp only [CollatzResearch.WordTrace]
  refine ⟨36988979856926096363352695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24659319904617397575568463 36988979856926096363352695)
  ·
    refine ⟨55483469785389144545029043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36988979856926096363352695 55483469785389144545029043)
    ·
      refine ⟨83225204678083716817543565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55483469785389144545029043 83225204678083716817543565)
      ·
        refine ⟨31209451754281393806578837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83225204678083716817543565 31209451754281393806578837)
        ·
          refine ⟨1462943050981940334683383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 31209451754281393806578837 1462943050981940334683383)
          ·
            refine ⟨2194414576472910502025075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1462943050981940334683383 2194414576472910502025075)
            ·
              refine ⟨3291621864709365753037613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2194414576472910502025075 3291621864709365753037613)
              ·
                refine ⟨1234358199266012157389105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3291621864709365753037613 1234358199266012157389105)
                ·
                  refine ⟨925768649449509118041829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1234358199266012157389105 925768649449509118041829)
                  ·
                    refine ⟨173581621771782959632843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 925768649449509118041829 173581621771782959632843)
                    ·
                      rfl

theorem cell23_1014147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 3, 2, 4].length) (baseStart_1014147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1014147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1014147 prefixEnd_1014147 := by exact prefixLift 1014147
  have htrace : WordTrace (prefixWord ++ tailWord_1014147) baseStart_1014147 baseEnd_1014147 := by
    simpa [prefixWord, tailWord_1014147, baseEnd_1014147] using wordTrace_append hprefix tailTrace_1014147
  have hstable : (prefixWord ++ tailWord_1014147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014147).length < 2 ^ (prefixWord ++ tailWord_1014147).sum := by decide
  have hdescent : baseEnd_1014147 < baseStart_1014147 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014170 : List Nat := [3, 1, 1, 4, 1, 2, 1, 1, 3, 3, 3]
def baseStart_1014170 : Nat := 118140960795 + 1014170 * 2 ^ 59
def prefixEnd_1014170 : Nat := 4983230072969 + 3 ^ 40 * 1014170 * 2
def baseEnd_1014170 : Nat := 520756675370402288910923

theorem tailTrace_1014170 : CollatzResearch.WordTrace tailWord_1014170 prefixEnd_1014170 520756675370402288910923 := by
  unfold tailWord_1014170
  simp only [CollatzResearch.WordTrace]
  refine ⟨9247454683960692822859991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24659879157228514194293309 9247454683960692822859991)
  ·
    refine ⟨13871182025941039234289987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9247454683960692822859991 13871182025941039234289987)
    ·
      refine ⟨20806773038911558851434981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13871182025941039234289987 20806773038911558851434981)
      ·
        refine ⟨3901269944795917284644059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20806773038911558851434981 3901269944795917284644059)
        ·
          refine ⟨5851904917193875926966089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3901269944795917284644059 5851904917193875926966089)
          ·
            refine ⟨4388928687895406945224567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5851904917193875926966089 4388928687895406945224567)
            ·
              refine ⟨6583393031843110417836851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4388928687895406945224567 6583393031843110417836851)
              ·
                refine ⟨9875089547764665626755277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6583393031843110417836851 9875089547764665626755277)
                ·
                  refine ⟨3703158580411749610033229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9875089547764665626755277 3703158580411749610033229)
                  ·
                    refine ⟨1388684467654406103762461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3703158580411749610033229 1388684467654406103762461)
                    ·
                      refine ⟨520756675370402288910923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1388684467654406103762461 520756675370402288910923)
                      ·
                        rfl

theorem cell23_1014170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 1, 3, 3, 3].length) (baseStart_1014170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1014170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1014170 prefixEnd_1014170 := by exact prefixLift 1014170
  have htrace : WordTrace (prefixWord ++ tailWord_1014170) baseStart_1014170 baseEnd_1014170 := by
    simpa [prefixWord, tailWord_1014170, baseEnd_1014170] using wordTrace_append hprefix tailTrace_1014170
  have hstable : (prefixWord ++ tailWord_1014170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014170).length < 2 ^ (prefixWord ++ tailWord_1014170).sum := by decide
  have hdescent : baseEnd_1014170 < baseStart_1014170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014174 : List Nat := [4, 3, 1, 2, 1, 3, 1, 1, 1, 1, 5]
def baseStart_1014174 : Nat := 118140960795 + 1014174 * 2 ^ 59
def prefixEnd_1014174 : Nat := 4983230072969 + 3 ^ 40 * 1014174 * 2
def baseEnd_1014174 : Nat := 520758729293020273260905

theorem tailTrace_1014174 : CollatzResearch.WordTrace tailWord_1014174 prefixEnd_1014174 520758729293020273260905 := by
  unfold tailWord_1014174
  simp only [CollatzResearch.WordTrace]
  refine ⟨4623745578478534996823197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24659976418552186649723717 4623745578478534996823197)
  ·
    refine ⟨1733904591929450623808699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4623745578478534996823197 1733904591929450623808699)
    ·
      refine ⟨2600856887894175935713049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1733904591929450623808699 2600856887894175935713049)
      ·
        refine ⟨1950642665920631951784787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2600856887894175935713049 1950642665920631951784787)
        ·
          refine ⟨2925963998880947927677181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1950642665920631951784787 2925963998880947927677181)
          ·
            refine ⟨1097236499580355472878943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2925963998880947927677181 1097236499580355472878943)
            ·
              refine ⟨1645854749370533209318415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1097236499580355472878943 1645854749370533209318415)
              ·
                refine ⟨2468782124055799813977623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1645854749370533209318415 2468782124055799813977623)
                ·
                  refine ⟨3703173186083699720966435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2468782124055799813977623 3703173186083699720966435)
                  ·
                    refine ⟨5554759779125549581449653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3703173186083699720966435 5554759779125549581449653)
                    ·
                      refine ⟨520758729293020273260905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5554759779125549581449653 520758729293020273260905)
                      ·
                        rfl

theorem cell23_1014174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_1014174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1014174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1014174 prefixEnd_1014174 := by exact prefixLift 1014174
  have htrace : WordTrace (prefixWord ++ tailWord_1014174) baseStart_1014174 baseEnd_1014174 := by
    simpa [prefixWord, tailWord_1014174, baseEnd_1014174] using wordTrace_append hprefix tailTrace_1014174
  have hstable : (prefixWord ++ tailWord_1014174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014174).length < 2 ^ (prefixWord ++ tailWord_1014174).sum := by decide
  have hdescent : baseEnd_1014174 < baseStart_1014174 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014204 : List Nat := [2, 2, 2, 4, 1, 1, 2, 3, 2, 1, 3]
def baseStart_1014204 : Nat := 118140960795 + 1014204 * 2 ^ 59
def prefixEnd_1014204 : Nat := 4983230072969 + 3 ^ 40 * 1014204 * 2
def baseEnd_1014204 : Nat := 520774133712655155885767

theorem tailTrace_1014204 : CollatzResearch.WordTrace tailWord_1014204 prefixEnd_1014204 520774133712655155885767 := by
  unfold tailWord_1014204
  simp only [CollatzResearch.WordTrace]
  refine ⟨18495529408859797549088833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24660705878479730065451777 18495529408859797549088833)
  ·
    refine ⟨13871647056644848161816625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18495529408859797549088833 13871647056644848161816625)
    ·
      refine ⟨10403735292483636121362469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13871647056644848161816625 10403735292483636121362469)
      ·
        refine ⟨1950700367340681772755463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10403735292483636121362469 1950700367340681772755463)
        ·
          refine ⟨2926050551011022659133195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1950700367340681772755463 2926050551011022659133195)
          ·
            refine ⟨4389075826516533988699793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2926050551011022659133195 4389075826516533988699793)
            ·
              refine ⟨3291806869887400491524845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4389075826516533988699793 3291806869887400491524845)
              ·
                refine ⟨1234427576207775184321817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3291806869887400491524845 1234427576207775184321817)
                ·
                  refine ⟨925820682155831388241363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1234427576207775184321817 925820682155831388241363)
                  ·
                    refine ⟨1388731023233747082362045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 925820682155831388241363 1388731023233747082362045)
                    ·
                      refine ⟨520774133712655155885767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1388731023233747082362045 520774133712655155885767)
                      ·
                        rfl

theorem cell23_1014204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_1014204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1014204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1014204 prefixEnd_1014204 := by exact prefixLift 1014204
  have htrace : WordTrace (prefixWord ++ tailWord_1014204) baseStart_1014204 baseEnd_1014204 := by
    simpa [prefixWord, tailWord_1014204, baseEnd_1014204] using wordTrace_append hprefix tailTrace_1014204
  have hstable : (prefixWord ++ tailWord_1014204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014204).length < 2 ^ (prefixWord ++ tailWord_1014204).sum := by decide
  have hdescent : baseEnd_1014204 < baseStart_1014204 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014223 : List Nat := [1, 1, 2, 1, 1, 4, 1, 1, 3, 4, 4]
def baseStart_1014223 : Nat := 118140960795 + 1014223 * 2 ^ 59
def prefixEnd_1014223 : Nat := 4983230072969 + 3 ^ 40 * 1014223 * 2
def baseEnd_1014223 : Nat := 520783889845090581548179

theorem tailTrace_1014223 : CollatzResearch.WordTrace tailWord_1014223 prefixEnd_1014223 520783889845090581548179 := by
  unfold tailWord_1014223
  simp only [CollatzResearch.WordTrace]
  refine ⟨36991751804650761343119323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24661167869767174228746215 36991751804650761343119323)
  ·
    refine ⟨55487627706976142014678985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36991751804650761343119323 55487627706976142014678985)
    ·
      refine ⟨41615720780232106511009239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55487627706976142014678985 41615720780232106511009239)
      ·
        refine ⟨62423581170348159766513859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41615720780232106511009239 62423581170348159766513859)
        ·
          refine ⟨93635371755522239649770789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62423581170348159766513859 93635371755522239649770789)
          ·
            refine ⟨17556632204160419934332023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93635371755522239649770789 17556632204160419934332023)
            ·
              refine ⟨26334948306240629901498035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17556632204160419934332023 26334948306240629901498035)
              ·
                refine ⟨39502422459360944852247053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26334948306240629901498035 39502422459360944852247053)
                ·
                  refine ⟨14813408422260354319592645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39502422459360944852247053 14813408422260354319592645)
                  ·
                    refine ⟨2777514079173816434923621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14813408422260354319592645 2777514079173816434923621)
                    ·
                      refine ⟨520783889845090581548179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2777514079173816434923621 520783889845090581548179)
                      ·
                        rfl

theorem cell23_1014223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 3, 4, 4].length) (baseStart_1014223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1014223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1014223 prefixEnd_1014223 := by exact prefixLift 1014223
  have htrace : WordTrace (prefixWord ++ tailWord_1014223) baseStart_1014223 baseEnd_1014223 := by
    simpa [prefixWord, tailWord_1014223, baseEnd_1014223] using wordTrace_append hprefix tailTrace_1014223
  have hstable : (prefixWord ++ tailWord_1014223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014223).length < 2 ^ (prefixWord ++ tailWord_1014223).sum := by decide
  have hdescent : baseEnd_1014223 < baseStart_1014223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014233 : List Nat := [1, 2, 1, 2, 4, 1, 1, 2, 9]
def baseStart_1014233 : Nat := 118140960795 + 1014233 * 2 ^ 59
def prefixEnd_1014233 : Nat := 4983230072969 + 3 ^ 40 * 1014233 * 2
def baseEnd_1014233 : Nat := 57865447183515060269237

theorem tailTrace_1014233 : CollatzResearch.WordTrace tailWord_1014233 prefixEnd_1014233 57865447183515060269237 := by
  unfold tailWord_1014233
  simp only [CollatzResearch.WordTrace]
  refine ⟨36992116534614533050983353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24661411023076355367322235 36992116534614533050983353)
  ·
    refine ⟨27744087400960899788237515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36992116534614533050983353 27744087400960899788237515)
    ·
      refine ⟨41616131101441349682356273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27744087400960899788237515 41616131101441349682356273)
      ·
        refine ⟨31212098326081012261767205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41616131101441349682356273 31212098326081012261767205)
        ·
          refine ⟨5852268436140189799081351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31212098326081012261767205 5852268436140189799081351)
          ·
            refine ⟨8778402654210284698622027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5852268436140189799081351 8778402654210284698622027)
            ·
              refine ⟨13167603981315427047933041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8778402654210284698622027 13167603981315427047933041)
              ·
                refine ⟨9875702985986570285949781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13167603981315427047933041 9875702985986570285949781)
                ·
                  refine ⟨57865447183515060269237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 9875702985986570285949781 57865447183515060269237)
                  ·
                    rfl

theorem cell23_1014233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 2, 9].length) (baseStart_1014233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1014233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1014233 prefixEnd_1014233 := by exact prefixLift 1014233
  have htrace : WordTrace (prefixWord ++ tailWord_1014233) baseStart_1014233 baseEnd_1014233 := by
    simpa [prefixWord, tailWord_1014233, baseEnd_1014233] using wordTrace_append hprefix tailTrace_1014233
  have hstable : (prefixWord ++ tailWord_1014233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014233).length < 2 ^ (prefixWord ++ tailWord_1014233).sum := by decide
  have hdescent : baseEnd_1014233 < baseStart_1014233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014250 : List Nat := [3, 1, 3, 1, 3, 1, 1, 3, 7]
def baseStart_1014250 : Nat := 118140960795 + 1014250 * 2 ^ 59
def prefixEnd_1014250 : Nat := 4983230072969 + 3 ^ 40 * 1014250 * 2
def baseEnd_1014250 : Nat := 57866417091417997323395

theorem tailTrace_1014250 : CollatzResearch.WordTrace tailWord_1014250 prefixEnd_1014250 57866417091417997323395 := by
  unfold tailWord_1014250
  simp only [CollatzResearch.WordTrace]
  refine ⟨9248184143888236238588051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24661824383701963302901469 9248184143888236238588051)
  ·
    refine ⟨13872276215832354357882077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9248184143888236238588051 13872276215832354357882077)
    ·
      refine ⟨5202103580937132884205779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13872276215832354357882077 5202103580937132884205779)
      ·
        refine ⟨7803155371405699326308669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5202103580937132884205779 7803155371405699326308669)
        ·
          refine ⟨2926183264277137247365751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7803155371405699326308669 2926183264277137247365751)
          ·
            refine ⟨4389274896415705871048627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2926183264277137247365751 4389274896415705871048627)
            ·
              refine ⟨6583912344623558806572941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4389274896415705871048627 6583912344623558806572941)
              ·
                refine ⟨2468967129233834552464853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6583912344623558806572941 2468967129233834552464853)
                ·
                  refine ⟨57866417091417997323395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2468967129233834552464853 57866417091417997323395)
                  ·
                    rfl

theorem cell23_1014250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 3, 7].length) (baseStart_1014250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1014250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1014250 prefixEnd_1014250 := by exact prefixLift 1014250
  have htrace : WordTrace (prefixWord ++ tailWord_1014250) baseStart_1014250 baseEnd_1014250 := by
    simpa [prefixWord, tailWord_1014250, baseEnd_1014250] using wordTrace_append hprefix tailTrace_1014250
  have hstable : (prefixWord ++ tailWord_1014250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014250).length < 2 ^ (prefixWord ++ tailWord_1014250).sum := by decide
  have hdescent : baseEnd_1014250 < baseStart_1014250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014280 : List Nat := [2, 1, 3, 2, 1, 1, 1, 5, 2, 5]
def baseStart_1014280 : Nat := 118140960795 + 1014280 * 2 ^ 59
def prefixEnd_1014280 : Nat := 4983230072969 + 3 ^ 40 * 1014280 * 2
def baseEnd_1014280 : Nat := 173604386080798952845139

theorem tailTrace_1014280 : CollatzResearch.WordTrace tailWord_1014280 prefixEnd_1014280 173604386080798952845139 := by
  unfold tailWord_1014280
  simp only [CollatzResearch.WordTrace]
  refine ⟨18496915382722130038972147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24662553843629506718629529 18496915382722130038972147)
  ·
    refine ⟨27745373074083195058458221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18496915382722130038972147 27745373074083195058458221)
    ·
      refine ⟨10404514902781198146921833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27745373074083195058458221 10404514902781198146921833)
      ·
        refine ⟨7803386177085898610191375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10404514902781198146921833 7803386177085898610191375)
        ·
          refine ⟨11705079265628847915287063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7803386177085898610191375 11705079265628847915287063)
          ·
            refine ⟨17557618898443271872930595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11705079265628847915287063 17557618898443271872930595)
            ·
              refine ⟨26336428347664907809395893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17557618898443271872930595 26336428347664907809395893)
              ·
                refine ⟨2469040157593585107130865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26336428347664907809395893 2469040157593585107130865)
                ·
                  refine ⟨1851780118195188830348149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2469040157593585107130865 1851780118195188830348149)
                  ·
                    refine ⟨173604386080798952845139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1851780118195188830348149 173604386080798952845139)
                    ·
                      rfl

theorem cell23_1014280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 5, 2, 5].length) (baseStart_1014280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1014280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1014280 prefixEnd_1014280 := by exact prefixLift 1014280
  have htrace : WordTrace (prefixWord ++ tailWord_1014280) baseStart_1014280 baseEnd_1014280 := by
    simpa [prefixWord, tailWord_1014280, baseEnd_1014280] using wordTrace_append hprefix tailTrace_1014280
  have hstable : (prefixWord ++ tailWord_1014280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014280).length < 2 ^ (prefixWord ++ tailWord_1014280).sum := by decide
  have hdescent : baseEnd_1014280 < baseStart_1014280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014284 : List Nat := [2, 2, 1, 2, 4, 3, 1, 3, 5]
def baseStart_1014284 : Nat := 118140960795 + 1014284 * 2 ^ 59
def prefixEnd_1014284 : Nat := 4983230072969 + 3 ^ 40 * 1014284 * 2
def baseEnd_1014284 : Nat := 57868356907223871431711

theorem tailTrace_1014284 : CollatzResearch.WordTrace tailWord_1014284 prefixEnd_1014284 57868356907223871431711 := by
  unfold tailWord_1014284
  simp only [CollatzResearch.WordTrace]
  refine ⟨18496988328714884380544953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24662651104953179174059937 18496988328714884380544953)
  ·
    refine ⟨13872741246536163285408715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18496988328714884380544953 13872741246536163285408715)
    ·
      refine ⟨20809111869804244928113073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13872741246536163285408715 20809111869804244928113073)
      ·
        refine ⟨15606833902353183696084805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20809111869804244928113073 15606833902353183696084805)
        ·
          refine ⟨2926281356691221943015901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15606833902353183696084805 2926281356691221943015901)
          ·
            refine ⟨1097355508759208228630963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2926281356691221943015901 1097355508759208228630963)
            ·
              refine ⟨1646033263138812342946445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1097355508759208228630963 1646033263138812342946445)
              ·
                refine ⟨617262473677054628604917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1646033263138812342946445 617262473677054628604917)
                ·
                  refine ⟨57868356907223871431711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 617262473677054628604917 57868356907223871431711)
                  ·
                    rfl

theorem cell23_1014284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 1, 3, 5].length) (baseStart_1014284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1014284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1014284 prefixEnd_1014284 := by exact prefixLift 1014284
  have htrace : WordTrace (prefixWord ++ tailWord_1014284) baseStart_1014284 baseEnd_1014284 := by
    simpa [prefixWord, tailWord_1014284, baseEnd_1014284] using wordTrace_append hprefix tailTrace_1014284
  have hstable : (prefixWord ++ tailWord_1014284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014284).length < 2 ^ (prefixWord ++ tailWord_1014284).sum := by decide
  have hdescent : baseEnd_1014284 < baseStart_1014284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014320 : List Nat := [2, 1, 1, 1, 2, 3, 2, 1, 3, 4, 3]
def baseStart_1014320 : Nat := 118140960795 + 1014320 * 2 ^ 59
def prefixEnd_1014320 : Nat := 4983230072969 + 3 ^ 40 * 1014320 * 2
def baseEnd_1014320 : Nat := 520833697468576702035233

theorem tailTrace_1014320 : CollatzResearch.WordTrace tailWord_1014320 prefixEnd_1014320 520833697468576702035233 := by
  unfold tailWord_1014320
  simp only [CollatzResearch.WordTrace]
  refine ⟨18497644842649673454700207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24663526456866231272933609 18497644842649673454700207)
  ·
    refine ⟨27746467263974510182050311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18497644842649673454700207 27746467263974510182050311)
    ·
      refine ⟨41619700895961765273075467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27746467263974510182050311 41619700895961765273075467)
      ·
        refine ⟨62429551343942647909613201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41619700895961765273075467 62429551343942647909613201)
        ·
          refine ⟨46822163507956985932209901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62429551343942647909613201 46822163507956985932209901)
          ·
            refine ⟨17558311315483869724578713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46822163507956985932209901 17558311315483869724578713)
            ·
              refine ⟨13168733486612902293434035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17558311315483869724578713 13168733486612902293434035)
              ·
                refine ⟨19753100229919353440151053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13168733486612902293434035 19753100229919353440151053)
                ·
                  refine ⟨7407412586219757540056645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19753100229919353440151053 7407412586219757540056645)
                  ·
                    refine ⟨1388889859916204538760621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7407412586219757540056645 1388889859916204538760621)
                    ·
                      refine ⟨520833697468576702035233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1388889859916204538760621 520833697468576702035233)
                      ·
                        rfl

theorem cell23_1014320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 3, 4, 3].length) (baseStart_1014320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1014320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1014320 prefixEnd_1014320 := by exact prefixLift 1014320
  have htrace : WordTrace (prefixWord ++ tailWord_1014320) baseStart_1014320 baseEnd_1014320 := by
    simpa [prefixWord, tailWord_1014320, baseEnd_1014320] using wordTrace_append hprefix tailTrace_1014320
  have hstable : (prefixWord ++ tailWord_1014320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014320).length < 2 ^ (prefixWord ++ tailWord_1014320).sum := by decide
  have hdescent : baseEnd_1014320 < baseStart_1014320 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014367 : List Nat := [1, 1, 2, 3, 1, 1, 1, 2, 7, 1, 3]
def baseStart_1014367 : Nat := 118140960795 + 1014367 * 2 ^ 59
def prefixEnd_1014367 : Nat := 4983230072969 + 3 ^ 40 * 1014367 * 2
def baseEnd_1014367 : Nat := 520857831059338018147517

theorem tailTrace_1014367 : CollatzResearch.WordTrace tailWord_1014367 prefixEnd_1014367 520857831059338018147517 := by
  unfold tailWord_1014367
  simp only [CollatzResearch.WordTrace]
  refine ⟨36997003916129073936361355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24664669277419382624240903 36997003916129073936361355)
  ·
    refine ⟨55495505874193610904542033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36997003916129073936361355 55495505874193610904542033)
    ·
      refine ⟨41621629405645208178406525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55495505874193610904542033 41621629405645208178406525)
      ·
        refine ⟨15608111027116953066902447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41621629405645208178406525 15608111027116953066902447)
        ·
          refine ⟨23412166540675429600353671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15608111027116953066902447 23412166540675429600353671)
          ·
            refine ⟨35118249811013144400530507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23412166540675429600353671 35118249811013144400530507)
            ·
              refine ⟨52677374716519716600795761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35118249811013144400530507 52677374716519716600795761)
              ·
                refine ⟨39508031037389787450596821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52677374716519716600795761 39508031037389787450596821)
                ·
                  refine ⟨925969477438823143373363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 39508031037389787450596821 925969477438823143373363)
                  ·
                    refine ⟨1388954216158234715060045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 925969477438823143373363 1388954216158234715060045)
                    ·
                      refine ⟨520857831059338018147517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1388954216158234715060045 520857831059338018147517)
                      ·
                        rfl

theorem cell23_1014367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 7, 1, 3].length) (baseStart_1014367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1014367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1014367 prefixEnd_1014367 := by exact prefixLift 1014367
  have htrace : WordTrace (prefixWord ++ tailWord_1014367) baseStart_1014367 baseEnd_1014367 := by
    simpa [prefixWord, tailWord_1014367, baseEnd_1014367] using wordTrace_append hprefix tailTrace_1014367
  have hstable : (prefixWord ++ tailWord_1014367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014367).length < 2 ^ (prefixWord ++ tailWord_1014367).sum := by decide
  have hdescent : baseEnd_1014367 < baseStart_1014367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014377 : List Nat := [1, 2, 1, 1, 1, 4, 1, 4, 1, 5, 2]
def baseStart_1014377 : Nat := 118140960795 + 1014377 * 2 ^ 59
def prefixEnd_1014377 : Nat := 4983230072969 + 3 ^ 40 * 1014377 * 2
def baseEnd_1014377 : Nat := 520862965865882979022471

theorem tailTrace_1014377 : CollatzResearch.WordTrace tailWord_1014377 prefixEnd_1014377 520862965865882979022471 := by
  unfold tailWord_1014377
  simp only [CollatzResearch.WordTrace]
  refine ⟨36997368646092845644225385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24664912430728563762816923 36997368646092845644225385)
  ·
    refine ⟨27748026484569634233169039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36997368646092845644225385 27748026484569634233169039)
    ·
      refine ⟨41622039726854451349753559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27748026484569634233169039 41622039726854451349753559)
      ·
        refine ⟨62433059590281677024630339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41622039726854451349753559 62433059590281677024630339)
        ·
          refine ⟨93649589385422515536945509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62433059590281677024630339 93649589385422515536945509)
          ·
            refine ⟨17559298009766721663177283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93649589385422515536945509 17559298009766721663177283)
            ·
              refine ⟨26338947014650082494765925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17559298009766721663177283 26338947014650082494765925)
              ·
                refine ⟨4938552565246890467768611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26338947014650082494765925 4938552565246890467768611)
                ·
                  refine ⟨7407828847870335701652917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4938552565246890467768611 7407828847870335701652917)
                  ·
                    refine ⟨694483954487843972029961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7407828847870335701652917 694483954487843972029961)
                    ·
                      refine ⟨520862965865882979022471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 694483954487843972029961 520862965865882979022471)
                      ·
                        rfl

theorem cell23_1014377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 4, 1, 5, 2].length) (baseStart_1014377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1014377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1014377 prefixEnd_1014377 := by exact prefixLift 1014377
  have htrace : WordTrace (prefixWord ++ tailWord_1014377) baseStart_1014377 baseEnd_1014377 := by
    simpa [prefixWord, tailWord_1014377, baseEnd_1014377] using wordTrace_append hprefix tailTrace_1014377
  have hstable : (prefixWord ++ tailWord_1014377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014377).length < 2 ^ (prefixWord ++ tailWord_1014377).sum := by decide
  have hdescent : baseEnd_1014377 < baseStart_1014377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014404 : List Nat := [2, 3, 2, 1, 3, 2, 1, 3, 1, 5]
def baseStart_1014404 : Nat := 118140960795 + 1014404 * 2 ^ 59
def prefixEnd_1014404 : Nat := 4983230072969 + 3 ^ 40 * 1014404 * 2
def baseEnd_1014404 : Nat := 173625609947851457794949

theorem tailTrace_1014404 : CollatzResearch.WordTrace tailWord_1014404 prefixEnd_1014404 173625609947851457794949 := by
  unfold tailWord_1014404
  simp only [CollatzResearch.WordTrace]
  refine ⟨18499176708497514627729133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24665568944663352836972177 18499176708497514627729133)
  ·
    refine ⟨6937191265686567985398425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18499176708497514627729133 6937191265686567985398425)
    ·
      refine ⟨5202893449264925989048819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6937191265686567985398425 5202893449264925989048819)
      ·
        refine ⟨7804340173897388983573229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5202893449264925989048819 7804340173897388983573229)
        ·
          refine ⟨2926627565211520868839961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7804340173897388983573229 2926627565211520868839961)
          ·
            refine ⟨2194970673908640651629971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2926627565211520868839961 2194970673908640651629971)
            ·
              refine ⟨3292456010862960977444957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2194970673908640651629971 3292456010862960977444957)
              ·
                refine ⟨1234671004073610366541859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3292456010862960977444957 1234671004073610366541859)
                ·
                  refine ⟨1852006506110415549812789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1234671004073610366541859 1852006506110415549812789)
                  ·
                    refine ⟨173625609947851457794949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1852006506110415549812789 173625609947851457794949)
                    ·
                      rfl

theorem cell23_1014404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 3, 1, 5].length) (baseStart_1014404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1014404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1014404 prefixEnd_1014404 := by exact prefixLift 1014404
  have htrace : WordTrace (prefixWord ++ tailWord_1014404) baseStart_1014404 baseEnd_1014404 := by
    simpa [prefixWord, tailWord_1014404, baseEnd_1014404] using wordTrace_append hprefix tailTrace_1014404
  have hstable : (prefixWord ++ tailWord_1014404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014404).length < 2 ^ (prefixWord ++ tailWord_1014404).sum := by decide
  have hdescent : baseEnd_1014404 < baseStart_1014404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014418 : List Nat := [3, 2, 3, 1, 2, 1, 2, 4, 1, 1, 3]
def baseStart_1014418 : Nat := 118140960795 + 1014418 * 2 ^ 59
def prefixEnd_1014418 : Nat := 4983230072969 + 3 ^ 40 * 1014418 * 2
def baseEnd_1014418 : Nat := 520884018572717318609783

theorem tailTrace_1014418 : CollatzResearch.WordTrace tailWord_1014418 prefixEnd_1014418 520884018572717318609783 := by
  unfold tailWord_1014418
  simp only [CollatzResearch.WordTrace]
  refine ⟨9249716009736077411616977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24665909359296206430978605 9249716009736077411616977)
  ·
    refine ⟨6937287007302058058712733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9249716009736077411616977 6937287007302058058712733)
    ·
      refine ⟨2601482627738271772017275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6937287007302058058712733 2601482627738271772017275)
      ·
        refine ⟨3902223941607407658025913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2601482627738271772017275 3902223941607407658025913)
        ·
          refine ⟨2926667956205555743519435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3902223941607407658025913 2926667956205555743519435)
          ·
            refine ⟨4390001934308333615279153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2926667956205555743519435 4390001934308333615279153)
            ·
              refine ⟨3292501450731250211459365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4390001934308333615279153 3292501450731250211459365)
              ·
                refine ⟨617344022012109414648631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3292501450731250211459365 617344022012109414648631)
                ·
                  refine ⟨926016033018164121972947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 617344022012109414648631 926016033018164121972947)
                  ·
                    refine ⟨1389024049527246182959421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 926016033018164121972947 1389024049527246182959421)
                    ·
                      refine ⟨520884018572717318609783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1389024049527246182959421 520884018572717318609783)
                      ·
                        rfl

theorem cell23_1014418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 4, 1, 1, 3].length) (baseStart_1014418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1014418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1014418 prefixEnd_1014418 := by exact prefixLift 1014418
  have htrace : WordTrace (prefixWord ++ tailWord_1014418) baseStart_1014418 baseEnd_1014418 := by
    simpa [prefixWord, tailWord_1014418, baseEnd_1014418] using wordTrace_append hprefix tailTrace_1014418
  have hstable : (prefixWord ++ tailWord_1014418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014418).length < 2 ^ (prefixWord ++ tailWord_1014418).sum := by decide
  have hdescent : baseEnd_1014418 < baseStart_1014418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014447 : List Nat := [1, 1, 2, 1, 2, 5, 4, 7]
def baseStart_1014447 : Nat := 118140960795 + 1014447 * 2 ^ 59
def prefixEnd_1014447 : Nat := 4983230072969 + 3 ^ 40 * 1014447 * 2
def baseEnd_1014447 : Nat := 19292552204136952042487

theorem tailTrace_1014447 : CollatzResearch.WordTrace tailWord_1014447 prefixEnd_1014447 19292552204136952042487 := by
  unfold tailWord_1014447
  simp only [CollatzResearch.WordTrace]
  refine ⟨36999921755839247599273595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24666614503892831732849063 36999921755839247599273595)
  ·
    refine ⟨55499882633758871398910393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36999921755839247599273595 55499882633758871398910393)
    ·
      refine ⟨41624911975319153549182795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55499882633758871398910393 41624911975319153549182795)
      ·
        refine ⟨62437367962978730323774193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41624911975319153549182795 62437367962978730323774193)
        ·
          refine ⟨46828025972234047742830645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62437367962978730323774193 46828025972234047742830645)
          ·
            refine ⟨4390127434896941975890373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46828025972234047742830645 4390127434896941975890373)
            ·
              refine ⟨823148894043176620479445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4390127434896941975890373 823148894043176620479445)
              ·
                refine ⟨19292552204136952042487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 823148894043176620479445 19292552204136952042487)
                ·
                  rfl

theorem cell23_1014447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 4, 7].length) (baseStart_1014447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1014447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1014447 prefixEnd_1014447 := by exact prefixLift 1014447
  have htrace : WordTrace (prefixWord ++ tailWord_1014447) baseStart_1014447 baseEnd_1014447 := by
    simpa [prefixWord, tailWord_1014447, baseEnd_1014447] using wordTrace_append hprefix tailTrace_1014447
  have hstable : (prefixWord ++ tailWord_1014447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014447).length < 2 ^ (prefixWord ++ tailWord_1014447).sum := by decide
  have hdescent : baseEnd_1014447 < baseStart_1014447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014457 : List Nat := [1, 2, 1, 4, 1, 1, 1, 3, 3, 3, 3]
def baseStart_1014457 : Nat := 118140960795 + 1014457 * 2 ^ 59
def prefixEnd_1014457 : Nat := 4983230072969 + 3 ^ 40 * 1014457 * 2
def baseEnd_1014457 : Nat := 520904044318242666022103

theorem tailTrace_1014457 : CollatzResearch.WordTrace tailWord_1014457 prefixEnd_1014457 520904044318242666022103 := by
  unfold tailWord_1014457
  simp only [CollatzResearch.WordTrace]
  refine ⟨37000286485803019307137625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24666857657202012871425083 37000286485803019307137625)
  ·
    refine ⟨27750214864352264480353219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37000286485803019307137625 27750214864352264480353219)
    ·
      refine ⟨41625322296528396720529829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27750214864352264480353219 41625322296528396720529829)
      ·
        refine ⟨7804747930599074385099343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41625322296528396720529829 7804747930599074385099343)
        ·
          refine ⟨11707121895898611577649015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7804747930599074385099343 11707121895898611577649015)
          ·
            refine ⟨17560682843847917366473523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11707121895898611577649015 17560682843847917366473523)
            ·
              refine ⟨26341024265771876049710285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17560682843847917366473523 26341024265771876049710285)
              ·
                refine ⟨9877884099664453518641357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26341024265771876049710285 9877884099664453518641357)
                ·
                  refine ⟨3704206537374170069490509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9877884099664453518641357 3704206537374170069490509)
                  ·
                    refine ⟨1389077451515313776058941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3704206537374170069490509 1389077451515313776058941)
                    ·
                      refine ⟨520904044318242666022103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1389077451515313776058941 520904044318242666022103)
                      ·
                        rfl

theorem cell23_1014457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 3, 3, 3, 3].length) (baseStart_1014457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1014457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1014457 prefixEnd_1014457 := by exact prefixLift 1014457
  have htrace : WordTrace (prefixWord ++ tailWord_1014457) baseStart_1014457 baseEnd_1014457 := by
    simpa [prefixWord, tailWord_1014457, baseEnd_1014457] using wordTrace_append hprefix tailTrace_1014457
  have hstable : (prefixWord ++ tailWord_1014457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014457).length < 2 ^ (prefixWord ++ tailWord_1014457).sum := by decide
  have hdescent : baseEnd_1014457 < baseStart_1014457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014480 : List Nat := [2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 10]
def baseStart_1014480 : Nat := 118140960795 + 1014480 * 2 ^ 59
def prefixEnd_1014480 : Nat := 4983230072969 + 3 ^ 40 * 1014480 * 2
def baseEnd_1014480 : Nat := 520915854373296076034497

theorem tailTrace_1014480 : CollatzResearch.WordTrace tailWord_1014480 prefixEnd_1014480 520915854373296076034497 := by
  unfold tailWord_1014480
  simp only [CollatzResearch.WordTrace]
  refine ⟨18500562682359847117612447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24667416909813129490149929 18500562682359847117612447)
  ·
    refine ⟨27750844023539770676418671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18500562682359847117612447 27750844023539770676418671)
    ·
      refine ⟨41626266035309656014628007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27750844023539770676418671 41626266035309656014628007)
      ·
        refine ⟨62439399052964484021942011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41626266035309656014628007 62439399052964484021942011)
        ·
          refine ⟨93659098579446726032913017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62439399052964484021942011 93659098579446726032913017)
          ·
            refine ⟨70244323934585044524684763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93659098579446726032913017 70244323934585044524684763)
            ·
              refine ⟨105366485901877566787027145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70244323934585044524684763 105366485901877566787027145)
              ·
                refine ⟨79024864426408175090270359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105366485901877566787027145 79024864426408175090270359)
                ·
                  refine ⟨118537296639612262635405539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79024864426408175090270359 118537296639612262635405539)
                  ·
                    refine ⟨177805944959418393953108309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 118537296639612262635405539 177805944959418393953108309)
                    ·
                      refine ⟨520915854373296076034497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 177805944959418393953108309 520915854373296076034497)
                      ·
                        rfl

theorem cell23_1014480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 10].length) (baseStart_1014480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1014480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1014480 prefixEnd_1014480 := by exact prefixLift 1014480
  have htrace : WordTrace (prefixWord ++ tailWord_1014480) baseStart_1014480 baseEnd_1014480 := by
    simpa [prefixWord, tailWord_1014480, baseEnd_1014480] using wordTrace_append hprefix tailTrace_1014480
  have hstable : (prefixWord ++ tailWord_1014480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014480).length < 2 ^ (prefixWord ++ tailWord_1014480).sum := by decide
  have hdescent : baseEnd_1014480 < baseStart_1014480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014485 : List Nat := [1, 3, 2, 5, 1, 2, 2, 1, 2, 4]
def baseStart_1014485 : Nat := 118140960795 + 1014485 * 2 ^ 59
def prefixEnd_1014485 : Nat := 4983230072969 + 3 ^ 40 * 1014485 * 2
def baseEnd_1014485 : Nat := 173639473925522852157325

theorem tailTrace_1014485 : CollatzResearch.WordTrace tailWord_1014485 prefixEnd_1014485 173639473925522852157325 := by
  unfold tailWord_1014485
  simp only [CollatzResearch.WordTrace]
  refine ⟨37001307729701580089156909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24667538486467720059437939 37001307729701580089156909)
  ·
    refine ⟨13875490398638092533433841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37001307729701580089156909 13875490398638092533433841)
    ·
      refine ⟨10406617798978569400075381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13875490398638092533433841 10406617798978569400075381)
      ·
        refine ⟨975620418654240881257067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10406617798978569400075381 975620418654240881257067)
        ·
          refine ⟨1463430627981361321885601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 975620418654240881257067 1463430627981361321885601)
          ·
            refine ⟨1097572970986020991414201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1463430627981361321885601 1097572970986020991414201)
            ·
              refine ⟨823179728239515743560651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1097572970986020991414201 823179728239515743560651)
              ·
                refine ⟨1234769592359273615340977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 823179728239515743560651 1234769592359273615340977)
                ·
                  refine ⟨926077194269455211505733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1234769592359273615340977 926077194269455211505733)
                  ·
                    refine ⟨173639473925522852157325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 926077194269455211505733 173639473925522852157325)
                    ·
                      rfl

theorem cell23_1014485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 2, 1, 2, 4].length) (baseStart_1014485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1014485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1014485 prefixEnd_1014485 := by exact prefixLift 1014485
  have htrace : WordTrace (prefixWord ++ tailWord_1014485) baseStart_1014485 baseEnd_1014485 := by
    simpa [prefixWord, tailWord_1014485, baseEnd_1014485] using wordTrace_append hprefix tailTrace_1014485
  have hstable : (prefixWord ++ tailWord_1014485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014485).length < 2 ^ (prefixWord ++ tailWord_1014485).sum := by decide
  have hdescent : baseEnd_1014485 < baseStart_1014485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014501 : List Nat := [1, 3, 1, 4, 1, 3, 1, 1, 3, 3, 2]
def baseStart_1014501 : Nat := 118140960795 + 1014501 * 2 ^ 59
def prefixEnd_1014501 : Nat := 4983230072969 + 3 ^ 40 * 1014501 * 2
def baseEnd_1014501 : Nat := 520926637467040493871901

theorem tailTrace_1014501 : CollatzResearch.WordTrace tailWord_1014501 prefixEnd_1014501 520926637467040493871901 := by
  unfold tailWord_1014501
  simp only [CollatzResearch.WordTrace]
  refine ⟨37001891297643614821739357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24667927531762409881159571 37001891297643614821739357)
  ·
    refine ⟨13875709236616355558152259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37001891297643614821739357 13875709236616355558152259)
    ·
      refine ⟨20813563854924533337228389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13875709236616355558152259 20813563854924533337228389)
      ·
        refine ⟨3902543222798350000730323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20813563854924533337228389 3902543222798350000730323)
        ·
          refine ⟨5853814834197525001095485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3902543222798350000730323 5853814834197525001095485)
          ·
            refine ⟨2195180562824071875410807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5853814834197525001095485 2195180562824071875410807)
            ·
              refine ⟨3292770844236107813116211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2195180562824071875410807 3292770844236107813116211)
              ·
                refine ⟨4939156266354161719674317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3292770844236107813116211 4939156266354161719674317)
                ·
                  refine ⟨1852183599882810644877869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4939156266354161719674317 1852183599882810644877869)
                  ·
                    refine ⟨694568849956053991829201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1852183599882810644877869 694568849956053991829201)
                    ·
                      refine ⟨520926637467040493871901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 694568849956053991829201 520926637467040493871901)
                      ·
                        rfl

theorem cell23_1014501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 1, 3, 3, 2].length) (baseStart_1014501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1014501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1014501 prefixEnd_1014501 := by exact prefixLift 1014501
  have htrace : WordTrace (prefixWord ++ tailWord_1014501) baseStart_1014501 baseEnd_1014501 := by
    simpa [prefixWord, tailWord_1014501, baseEnd_1014501] using wordTrace_append hprefix tailTrace_1014501
  have hstable : (prefixWord ++ tailWord_1014501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014501).length < 2 ^ (prefixWord ++ tailWord_1014501).sum := by decide
  have hdescent : baseEnd_1014501 < baseStart_1014501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014527 : List Nat := [1, 1, 2, 2, 1, 3, 1, 4, 2, 2, 4]
def baseStart_1014527 : Nat := 118140960795 + 1014527 * 2 ^ 59
def prefixEnd_1014527 : Nat := 4983230072969 + 3 ^ 40 * 1014527 * 2
def baseEnd_1014527 : Nat := 520939987964057392146781

theorem tailTrace_1014527 : CollatzResearch.WordTrace tailWord_1014527 prefixEnd_1014527 520939987964057392146781 := by
  unfold tailWord_1014527
  simp only [CollatzResearch.WordTrace]
  refine ⟨37002839595549421262185835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24668559730366280841457223 37002839595549421262185835)
  ·
    refine ⟨55504259393324131893278753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37002839595549421262185835 55504259393324131893278753)
    ·
      refine ⟨41628194544993098919959065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55504259393324131893278753 41628194544993098919959065)
      ·
        refine ⟨31221145908744824189969299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41628194544993098919959065 31221145908744824189969299)
        ·
          refine ⟨46831718863117236284953949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31221145908744824189969299 46831718863117236284953949)
          ·
            refine ⟨17561894573668963606857731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46831718863117236284953949 17561894573668963606857731)
            ·
              refine ⟨26342841860503445410286597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17561894573668963606857731 26342841860503445410286597)
              ·
                refine ⟨4939282848844396014428737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26342841860503445410286597 4939282848844396014428737)
                ·
                  refine ⟨3704462136633297010821553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4939282848844396014428737 3704462136633297010821553)
                  ·
                    refine ⟨2778346602474972758116165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3704462136633297010821553 2778346602474972758116165)
                    ·
                      refine ⟨520939987964057392146781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2778346602474972758116165 520939987964057392146781)
                      ·
                        rfl

theorem cell23_1014527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 4, 2, 2, 4].length) (baseStart_1014527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1014527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1014527 prefixEnd_1014527 := by exact prefixLift 1014527
  have htrace : WordTrace (prefixWord ++ tailWord_1014527) baseStart_1014527 baseEnd_1014527 := by
    simpa [prefixWord, tailWord_1014527, baseEnd_1014527] using wordTrace_append hprefix tailTrace_1014527
  have hstable : (prefixWord ++ tailWord_1014527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014527).length < 2 ^ (prefixWord ++ tailWord_1014527).sum := by decide
  have hdescent : baseEnd_1014527 < baseStart_1014527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014604 : List Nat := [2, 2, 1, 3, 3, 1, 1, 2, 1, 3, 4]
def baseStart_1014604 : Nat := 118140960795 + 1014604 * 2 ^ 59
def prefixEnd_1014604 : Nat := 4983230072969 + 3 ^ 40 * 1014604 * 2
def baseEnd_1014604 : Nat := 520979525974453590883927

theorem tailTrace_1014604 : CollatzResearch.WordTrace tailWord_1014604 prefixEnd_1014604 520979525974453590883927 := by
  unfold tailWord_1014604
  simp only [CollatzResearch.WordTrace]
  refine ⟨18502824008135231706369433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24670432010846975608492577 18502824008135231706369433)
  ·
    refine ⟨13877118006101423779777075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18502824008135231706369433 13877118006101423779777075)
    ·
      refine ⟨20815677009152135669665613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13877118006101423779777075 20815677009152135669665613)
      ·
        refine ⟨7805878878432050876124605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20815677009152135669665613 7805878878432050876124605)
        ·
          refine ⟨2927204579412019078546727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7805878878432050876124605 2927204579412019078546727)
          ·
            refine ⟨4390806869118028617820091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2927204579412019078546727 4390806869118028617820091)
            ·
              refine ⟨6586210303677042926730137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4390806869118028617820091 6586210303677042926730137)
              ·
                refine ⟨4939657727757782195047603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6586210303677042926730137 4939657727757782195047603)
                ·
                  refine ⟨7409486591636673292571405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4939657727757782195047603 7409486591636673292571405)
                  ·
                    refine ⟨2778557471863752484714277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7409486591636673292571405 2778557471863752484714277)
                    ·
                      refine ⟨520979525974453590883927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2778557471863752484714277 520979525974453590883927)
                      ·
                        rfl

theorem cell23_1014604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 2, 1, 3, 4].length) (baseStart_1014604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1014604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1014604 prefixEnd_1014604 := by exact prefixLift 1014604
  have htrace : WordTrace (prefixWord ++ tailWord_1014604) baseStart_1014604 baseEnd_1014604 := by
    simpa [prefixWord, tailWord_1014604, baseEnd_1014604] using wordTrace_append hprefix tailTrace_1014604
  have hstable : (prefixWord ++ tailWord_1014604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014604).length < 2 ^ (prefixWord ++ tailWord_1014604).sum := by decide
  have hdescent : baseEnd_1014604 < baseStart_1014604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014624 : List Nat := [2, 1, 1, 3, 3, 1, 1, 3, 1, 4, 3]
def baseStart_1014624 : Nat := 118140960795 + 1014624 * 2 ^ 59
def prefixEnd_1014624 : Nat := 4983230072969 + 3 ^ 40 * 1014624 * 2
def baseEnd_1014624 : Nat := 520989795587543512633835

theorem tailTrace_1014624 : CollatzResearch.WordTrace tailWord_1014624 prefixEnd_1014624 520989795587543512633835 := by
  unfold tailWord_1014624
  simp only [CollatzResearch.WordTrace]
  refine ⟨18503188738099003414233463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24670918317465337885644617 18503188738099003414233463)
  ·
    refine ⟨27754783107148505121350195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18503188738099003414233463 27754783107148505121350195)
    ·
      refine ⟨41632174660722757682025293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27754783107148505121350195 41632174660722757682025293)
      ·
        refine ⟨15612065497771034130759485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41632174660722757682025293 15612065497771034130759485)
        ·
          refine ⟨5854524561664137799034807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15612065497771034130759485 5854524561664137799034807)
          ·
            refine ⟨8781786842496206698552211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5854524561664137799034807 8781786842496206698552211)
            ·
              refine ⟨13172680263744310047828317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8781786842496206698552211 13172680263744310047828317)
              ·
                refine ⟨4939755098904116267935619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13172680263744310047828317 4939755098904116267935619)
                ·
                  refine ⟨7409632648356174401903429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4939755098904116267935619 7409632648356174401903429)
                  ·
                    refine ⟨1389306121566782700356893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7409632648356174401903429 1389306121566782700356893)
                    ·
                      refine ⟨520989795587543512633835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1389306121566782700356893 520989795587543512633835)
                      ·
                        rfl

theorem cell23_1014624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 3, 1, 4, 3].length) (baseStart_1014624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1014624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1014624 prefixEnd_1014624 := by exact prefixLift 1014624
  have htrace : WordTrace (prefixWord ++ tailWord_1014624) baseStart_1014624 baseEnd_1014624 := by
    simpa [prefixWord, tailWord_1014624, baseEnd_1014624] using wordTrace_append hprefix tailTrace_1014624
  have hstable : (prefixWord ++ tailWord_1014624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014624).length < 2 ^ (prefixWord ++ tailWord_1014624).sum := by decide
  have hdescent : baseEnd_1014624 < baseStart_1014624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014638 : List Nat := [4, 1, 2, 3, 2, 1, 1, 2, 2, 1, 4]
def baseStart_1014638 : Nat := 118140960795 + 1014638 * 2 ^ 59
def prefixEnd_1014638 : Nat := 4983230072969 + 3 ^ 40 * 1014638 * 2
def baseEnd_1014638 : Nat := 520996984316706457858771

theorem tailTrace_1014638 : CollatzResearch.WordTrace tailWord_1014638 prefixEnd_1014638 520996984316706457858771 := by
  unfold tailWord_1014638
  simp only [CollatzResearch.WordTrace]
  refine ⟨4625861012268410902434571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24671258732098191479651045 4625861012268410902434571)
  ·
    refine ⟨6938791518402616353651857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4625861012268410902434571 6938791518402616353651857)
    ·
      refine ⟨5204093638801962265238893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6938791518402616353651857 5204093638801962265238893)
      ·
        refine ⟨1951535114550735849464585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5204093638801962265238893 1951535114550735849464585)
        ·
          refine ⟨1463651335913051887098439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1951535114550735849464585 1463651335913051887098439)
          ·
            refine ⟨2195477003869577830647659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1463651335913051887098439 2195477003869577830647659)
            ·
              refine ⟨3293215505804366745971489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2195477003869577830647659 3293215505804366745971489)
              ·
                refine ⟨2469911629353275059478617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3293215505804366745971489 2469911629353275059478617)
                ·
                  refine ⟨1852433722014956294608963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2469911629353275059478617 1852433722014956294608963)
                  ·
                    refine ⟨2778650583022434441913445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1852433722014956294608963 2778650583022434441913445)
                    ·
                      refine ⟨520996984316706457858771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2778650583022434441913445 520996984316706457858771)
                      ·
                        rfl

theorem cell23_1014638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_1014638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1014638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1014638 prefixEnd_1014638 := by exact prefixLift 1014638
  have htrace : WordTrace (prefixWord ++ tailWord_1014638) baseStart_1014638 baseEnd_1014638 := by
    simpa [prefixWord, tailWord_1014638, baseEnd_1014638] using wordTrace_append hprefix tailTrace_1014638
  have hstable : (prefixWord ++ tailWord_1014638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014638).length < 2 ^ (prefixWord ++ tailWord_1014638).sum := by decide
  have hdescent : baseEnd_1014638 < baseStart_1014638 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014641 : List Nat := [1, 2, 2, 2, 1, 5, 1, 2, 2, 2, 3]
def baseStart_1014641 : Nat := 118140960795 + 1014641 * 2 ^ 59
def prefixEnd_1014641 : Nat := 4983230072969 + 3 ^ 40 * 1014641 * 2
def baseEnd_1014641 : Nat := 520998524758669946121257

theorem tailTrace_1014641 : CollatzResearch.WordTrace tailWord_1014641 prefixEnd_1014641 520998524758669946121257 := by
  unfold tailWord_1014641
  simp only [CollatzResearch.WordTrace]
  refine ⟨37006997517136418731835777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24671331678090945821223851 37006997517136418731835777)
  ·
    refine ⟨27755248137852314048876833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37006997517136418731835777 27755248137852314048876833)
    ·
      refine ⟨20816436103389235536657625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27755248137852314048876833 20816436103389235536657625)
      ·
        refine ⟨15612327077541926652493219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20816436103389235536657625 15612327077541926652493219)
        ·
          refine ⟨23418490616312889978739829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15612327077541926652493219 23418490616312889978739829)
          ·
            refine ⟨2195483495279333435506859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23418490616312889978739829 2195483495279333435506859)
            ·
              refine ⟨3293225242919000153260289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2195483495279333435506859 3293225242919000153260289)
              ·
                refine ⟨2469918932189250114945217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3293225242919000153260289 2469918932189250114945217)
                ·
                  refine ⟨1852439199141937586208913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2469918932189250114945217 1852439199141937586208913)
                  ·
                    refine ⟨1389329399356453189656685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1852439199141937586208913 1389329399356453189656685)
                    ·
                      refine ⟨520998524758669946121257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1389329399356453189656685 520998524758669946121257)
                      ·
                        rfl

theorem cell23_1014641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 2, 2, 2, 3].length) (baseStart_1014641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1014641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1014641 prefixEnd_1014641 := by exact prefixLift 1014641
  have htrace : WordTrace (prefixWord ++ tailWord_1014641) baseStart_1014641 baseEnd_1014641 := by
    simpa [prefixWord, tailWord_1014641, baseEnd_1014641] using wordTrace_append hprefix tailTrace_1014641
  have hstable : (prefixWord ++ tailWord_1014641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014641).length < 2 ^ (prefixWord ++ tailWord_1014641).sum := by decide
  have hdescent : baseEnd_1014641 < baseStart_1014641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014647 : List Nat := [1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 8]
def baseStart_1014647 : Nat := 118140960795 + 1014647 * 2 ^ 59
def prefixEnd_1014647 : Nat := 4983230072969 + 3 ^ 40 * 1014647 * 2
def baseEnd_1014647 : Nat := 521001605642596922646229

theorem tailTrace_1014647 : CollatzResearch.WordTrace tailWord_1014647 prefixEnd_1014647 521001605642596922646229 := by
  unfold tailWord_1014647
  simp only [CollatzResearch.WordTrace]
  refine ⟨37007216355114681756554195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24671477570076454504369463 37007216355114681756554195)
  ·
    refine ⟨55510824532672022634831293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37007216355114681756554195 55510824532672022634831293)
    ·
      refine ⟨20816559199752008488061735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55510824532672022634831293 20816559199752008488061735)
      ·
        refine ⟨31224838799628012732092603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20816559199752008488061735 31224838799628012732092603)
        ·
          refine ⟨46837258199442019098138905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31224838799628012732092603 46837258199442019098138905)
          ·
            refine ⟨35127943649581514323604179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46837258199442019098138905 35127943649581514323604179)
            ·
              refine ⟨52691915474372271485406269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35127943649581514323604179 52691915474372271485406269)
              ·
                refine ⟨19759468302889601807027351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52691915474372271485406269 19759468302889601807027351)
                ·
                  refine ⟨29639202454334402710541027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19759468302889601807027351 29639202454334402710541027)
                  ·
                    refine ⟨44458803681501604065811541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29639202454334402710541027 44458803681501604065811541)
                    ·
                      refine ⟨521001605642596922646229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 44458803681501604065811541 521001605642596922646229)
                      ·
                        rfl

theorem cell23_1014647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 8].length) (baseStart_1014647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1014647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1014647 prefixEnd_1014647 := by exact prefixLift 1014647
  have htrace : WordTrace (prefixWord ++ tailWord_1014647) baseStart_1014647 baseEnd_1014647 := by
    simpa [prefixWord, tailWord_1014647, baseEnd_1014647] using wordTrace_append hprefix tailTrace_1014647
  have hstable : (prefixWord ++ tailWord_1014647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014647).length < 2 ^ (prefixWord ++ tailWord_1014647).sum := by decide
  have hdescent : baseEnd_1014647 < baseStart_1014647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014661 : List Nat := [1, 3, 1, 1, 3, 3, 4, 1, 6]
def baseStart_1014661 : Nat := 118140960795 + 1014661 * 2 ^ 59
def prefixEnd_1014661 : Nat := 4983230072969 + 3 ^ 40 * 1014661 * 2
def baseEnd_1014661 : Nat := 57889866041306651985685

theorem tailTrace_1014661 : CollatzResearch.WordTrace tailWord_1014661 prefixEnd_1014661 57889866041306651985685 := by
  unfold tailWord_1014661
  simp only [CollatzResearch.WordTrace]
  refine ⟨37007726977063962147563837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24671817984709308098375891 37007726977063962147563837)
  ·
    refine ⟨13877897616398985805336439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37007726977063962147563837 13877897616398985805336439)
    ·
      refine ⟨20816846424598478708004659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13877897616398985805336439 20816846424598478708004659)
      ·
        refine ⟨31225269636897718062006989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20816846424598478708004659 31225269636897718062006989)
        ·
          refine ⟨11709476113836644273252621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31225269636897718062006989 11709476113836644273252621)
          ·
            refine ⟨4391053542688741602469733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11709476113836644273252621 4391053542688741602469733)
            ·
              refine ⟨823322539254139050463075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4391053542688741602469733 823322539254139050463075)
              ·
                refine ⟨1234983808881208575694613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 823322539254139050463075 1234983808881208575694613)
                ·
                  refine ⟨57889866041306651985685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1234983808881208575694613 57889866041306651985685)
                  ·
                    rfl

theorem cell23_1014661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 4, 1, 6].length) (baseStart_1014661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1014661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1014661 prefixEnd_1014661 := by exact prefixLift 1014661
  have htrace : WordTrace (prefixWord ++ tailWord_1014661) baseStart_1014661 baseEnd_1014661 := by
    simpa [prefixWord, tailWord_1014661, baseEnd_1014661] using wordTrace_append hprefix tailTrace_1014661
  have hstable : (prefixWord ++ tailWord_1014661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014661).length < 2 ^ (prefixWord ++ tailWord_1014661).sum := by decide
  have hdescent : baseEnd_1014661 < baseStart_1014661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014708 : List Nat := [2, 5, 2, 1, 1, 1, 1, 2, 3, 5]
def baseStart_1014708 : Nat := 118140960795 + 1014708 * 2 ^ 59
def prefixEnd_1014708 : Nat := 4983230072969 + 3 ^ 40 * 1014708 * 2
def baseEnd_1014708 : Nat := 173677642654173727994483

theorem tailTrace_1014708 : CollatzResearch.WordTrace tailWord_1014708 prefixEnd_1014708 173677642654173727994483 := by
  unfold tailWord_1014708
  simp only [CollatzResearch.WordTrace]
  refine ⟨18504720603946844587262389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24672960805262459449683185 18504720603946844587262389)
  ·
    refine ⟨1734817556620016680055849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18504720603946844587262389 1734817556620016680055849)
    ·
      refine ⟨1301113167465012510041887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1734817556620016680055849 1301113167465012510041887)
      ·
        refine ⟨1951669751197518765062831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1301113167465012510041887 1951669751197518765062831)
        ·
          refine ⟨2927504626796278147594247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1951669751197518765062831 2927504626796278147594247)
          ·
            refine ⟨4391256940194417221391371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2927504626796278147594247 4391256940194417221391371)
            ·
              refine ⟨6586885410291625832087057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4391256940194417221391371 6586885410291625832087057)
              ·
                refine ⟨4940164057718719374065293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6586885410291625832087057 4940164057718719374065293)
                ·
                  refine ⟨1852561521644519765274485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4940164057718719374065293 1852561521644519765274485)
                  ·
                    refine ⟨173677642654173727994483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1852561521644519765274485 173677642654173727994483)
                    ·
                      rfl

theorem cell23_1014708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_1014708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1014708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1014708 prefixEnd_1014708 := by exact prefixLift 1014708
  have htrace : WordTrace (prefixWord ++ tailWord_1014708) baseStart_1014708 baseEnd_1014708 := by
    simpa [prefixWord, tailWord_1014708, baseEnd_1014708] using wordTrace_append hprefix tailTrace_1014708
  have hstable : (prefixWord ++ tailWord_1014708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014708).length < 2 ^ (prefixWord ++ tailWord_1014708).sum := by decide
  have hdescent : baseEnd_1014708 < baseStart_1014708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014714 : List Nat := [3, 1, 1, 1, 2, 1, 4, 1, 3, 1, 5]
def baseStart_1014714 : Nat := 118140960795 + 1014714 * 2 ^ 59
def prefixEnd_1014714 : Nat := 4983230072969 + 3 ^ 40 * 1014714 * 2
def baseEnd_1014714 : Nat := 521036008846448160508421

theorem tailTrace_1014714 : CollatzResearch.WordTrace tailWord_1014714 prefixEnd_1014714 521036008846448160508421 := by
  unfold tailWord_1014714
  simp only [CollatzResearch.WordTrace]
  refine ⟨9252415011467988049810799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24673106697247968132828797 9252415011467988049810799)
  ·
    refine ⟨13878622517201982074716199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9252415011467988049810799 13878622517201982074716199)
    ·
      refine ⟨20817933775802973112074299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13878622517201982074716199 20817933775802973112074299)
      ·
        refine ⟨31226900663704459668111449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20817933775802973112074299 31226900663704459668111449)
        ·
          refine ⟨23420175497778344751083587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31226900663704459668111449 23420175497778344751083587)
          ·
            refine ⟨35130263246667517126625381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23420175497778344751083587 35130263246667517126625381)
            ·
              refine ⟨6586924358750159461242259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35130263246667517126625381 6586924358750159461242259)
              ·
                refine ⟨9880386538125239191863389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6586924358750159461242259 9880386538125239191863389)
                ·
                  refine ⟨3705144951796964696948771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9880386538125239191863389 3705144951796964696948771)
                  ·
                    refine ⟨5557717427695447045423157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3705144951796964696948771 5557717427695447045423157)
                    ·
                      refine ⟨521036008846448160508421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5557717427695447045423157 521036008846448160508421)
                      ·
                        rfl

theorem cell23_1014714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 1, 3, 1, 5].length) (baseStart_1014714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1014714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1014714 prefixEnd_1014714 := by exact prefixLift 1014714
  have htrace : WordTrace (prefixWord ++ tailWord_1014714) baseStart_1014714 baseEnd_1014714 := by
    simpa [prefixWord, tailWord_1014714, baseEnd_1014714] using wordTrace_append hprefix tailTrace_1014714
  have hstable : (prefixWord ++ tailWord_1014714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014714).length < 2 ^ (prefixWord ++ tailWord_1014714).sum := by decide
  have hdescent : baseEnd_1014714 < baseStart_1014714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014726 : List Nat := [6, 1, 3, 1, 1, 2, 1, 1, 2, 2, 3]
def baseStart_1014726 : Nat := 118140960795 + 1014726 * 2 ^ 59
def prefixEnd_1014726 : Nat := 4983230072969 + 3 ^ 40 * 1014726 * 2
def baseEnd_1014726 : Nat := 521042170614302113558367

theorem tailTrace_1014726 : CollatzResearch.WordTrace tailWord_1014726 prefixEnd_1014726 521042170614302113558367 := by
  unfold tailWord_1014726
  simp only [CollatzResearch.WordTrace]
  refine ⟨1156565553807139945271251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 24673398481218985499120021 1156565553807139945271251)
  ·
    refine ⟨1734848330710709917906877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1156565553807139945271251 1734848330710709917906877)
    ·
      refine ⟨650568124016516219215079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1734848330710709917906877 650568124016516219215079)
      ·
        refine ⟨975852186024774328822619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 650568124016516219215079 975852186024774328822619)
        ·
          refine ⟨1463778279037161493233929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 975852186024774328822619 1463778279037161493233929)
          ·
            refine ⟨1097833709277871119925447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1463778279037161493233929 1097833709277871119925447)
            ·
              refine ⟨1646750563916806679888171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1097833709277871119925447 1646750563916806679888171)
              ·
                refine ⟨2470125845875210019832257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1646750563916806679888171 2470125845875210019832257)
                ·
                  refine ⟨1852594384406407514874193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2470125845875210019832257 1852594384406407514874193)
                  ·
                    refine ⟨1389445788304805636155645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1852594384406407514874193 1389445788304805636155645)
                    ·
                      refine ⟨521042170614302113558367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1389445788304805636155645 521042170614302113558367)
                      ·
                        rfl

theorem cell23_1014726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_1014726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1014726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1014726 prefixEnd_1014726 := by exact prefixLift 1014726
  have htrace : WordTrace (prefixWord ++ tailWord_1014726) baseStart_1014726 baseEnd_1014726 := by
    simpa [prefixWord, tailWord_1014726, baseEnd_1014726] using wordTrace_append hprefix tailTrace_1014726
  have hstable : (prefixWord ++ tailWord_1014726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014726).length < 2 ^ (prefixWord ++ tailWord_1014726).sum := by decide
  have hdescent : baseEnd_1014726 < baseStart_1014726 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014731 : List Nat := [1, 1, 1, 1, 3, 5, 2, 1, 3, 2, 3]
def baseStart_1014731 : Nat := 118140960795 + 1014731 * 2 ^ 59
def prefixEnd_1014731 : Nat := 4983230072969 + 3 ^ 40 * 1014731 * 2
def baseEnd_1014731 : Nat := 521044738017574593995843

theorem tailTrace_1014731 : CollatzResearch.WordTrace tailWord_1014731 prefixEnd_1014731 521044738017574593995843 := by
  unfold tailWord_1014731
  simp only [CollatzResearch.WordTrace]
  refine ⟨37010280086810364102612047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24673520057873576068408031 37010280086810364102612047)
  ·
    refine ⟨55515420130215546153918071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37010280086810364102612047 55515420130215546153918071)
    ·
      refine ⟨83273130195323319230877107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55515420130215546153918071 83273130195323319230877107)
      ·
        refine ⟨124909695292984978846315661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83273130195323319230877107 124909695292984978846315661)
        ·
          refine ⟨46841135734869367067368373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124909695292984978846315661 46841135734869367067368373)
          ·
            refine ⟨4391356475144003162565785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46841135734869367067368373 4391356475144003162565785)
            ·
              refine ⟨3293517356358002371924339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4391356475144003162565785 3293517356358002371924339)
              ·
                refine ⟨4940276034537003557886509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3293517356358002371924339 4940276034537003557886509)
                ·
                  refine ⟨1852603512951376334207441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4940276034537003557886509 1852603512951376334207441)
                  ·
                    refine ⟨1389452634713532250655581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1852603512951376334207441 1389452634713532250655581)
                    ·
                      refine ⟨521044738017574593995843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1389452634713532250655581 521044738017574593995843)
                      ·
                        rfl

theorem cell23_1014731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 1, 3, 2, 3].length) (baseStart_1014731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1014731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1014731 prefixEnd_1014731 := by exact prefixLift 1014731
  have htrace : WordTrace (prefixWord ++ tailWord_1014731) baseStart_1014731 baseEnd_1014731 := by
    simpa [prefixWord, tailWord_1014731, baseEnd_1014731] using wordTrace_append hprefix tailTrace_1014731
  have hstable : (prefixWord ++ tailWord_1014731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014731).length < 2 ^ (prefixWord ++ tailWord_1014731).sum := by decide
  have hdescent : baseEnd_1014731 < baseStart_1014731 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014742 : List Nat := [5, 2, 1, 1, 2, 3, 2, 1, 1, 5]
def baseStart_1014742 : Nat := 118140960795 + 1014742 * 2 ^ 59
def prefixEnd_1014742 : Nat := 4983230072969 + 3 ^ 40 * 1014742 * 2
def baseEnd_1014742 : Nat := 173683462101591350319431

theorem tailTrace_1014742 : CollatzResearch.WordTrace tailWord_1014742 prefixEnd_1014742 173683462101591350319431 := by
  unfold tailWord_1014742
  simp only [CollatzResearch.WordTrace]
  refine ⟨2313167580610657061328905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24673787526513675320841653 2313167580610657061328905)
  ·
    refine ⟨1734875685457992795996679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2313167580610657061328905 1734875685457992795996679)
    ·
      refine ⟨2602313528186989193995019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1734875685457992795996679 2602313528186989193995019)
      ·
        refine ⟨3903470292280483790992529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2602313528186989193995019 3903470292280483790992529)
        ·
          refine ⟨2927602719210362843244397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3903470292280483790992529 2927602719210362843244397)
          ·
            refine ⟨1097851019703886066216649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2927602719210362843244397 1097851019703886066216649)
            ·
              refine ⟨823388264777914549662487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1097851019703886066216649 823388264777914549662487)
              ·
                refine ⟨1235082397166871824493731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 823388264777914549662487 1235082397166871824493731)
                ·
                  refine ⟨1852623595750307736740597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1235082397166871824493731 1852623595750307736740597)
                  ·
                    refine ⟨173683462101591350319431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1852623595750307736740597 173683462101591350319431)
                    ·
                      rfl

theorem cell23_1014742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 2, 1, 1, 5].length) (baseStart_1014742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1014742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1014742 prefixEnd_1014742 := by exact prefixLift 1014742
  have htrace : WordTrace (prefixWord ++ tailWord_1014742) baseStart_1014742 baseEnd_1014742 := by
    simpa [prefixWord, tailWord_1014742, baseEnd_1014742] using wordTrace_append hprefix tailTrace_1014742
  have hstable : (prefixWord ++ tailWord_1014742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014742).length < 2 ^ (prefixWord ++ tailWord_1014742).sum := by decide
  have hdescent : baseEnd_1014742 < baseStart_1014742 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014745 : List Nat := [1, 2, 1, 2, 5, 3, 2, 1, 1, 1, 4]
def baseStart_1014745 : Nat := 118140960795 + 1014745 * 2 ^ 59
def prefixEnd_1014745 : Nat := 4983230072969 + 3 ^ 40 * 1014745 * 2
def baseEnd_1014745 : Nat := 521051926746737539220779

theorem tailTrace_1014745 : CollatzResearch.WordTrace tailWord_1014745 prefixEnd_1014745 521051926746737539220779 := by
  unfold tailWord_1014745
  simp only [CollatzResearch.WordTrace]
  refine ⟨37010790708759644493621689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24673860472506429662414459 37010790708759644493621689)
  ·
    refine ⟨27758093031569733370216267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37010790708759644493621689 27758093031569733370216267)
    ·
      refine ⟨41637139547354600055324401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27758093031569733370216267 41637139547354600055324401)
      ·
        refine ⟨31227854660515950041493301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41637139547354600055324401 31227854660515950041493301)
        ·
          refine ⟨2927611374423370316389997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31227854660515950041493301 2927611374423370316389997)
          ·
            refine ⟨1097854265408763868646249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2927611374423370316389997 1097854265408763868646249)
            ·
              refine ⟨823390699056572901484687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1097854265408763868646249 823390699056572901484687)
              ·
                refine ⟨1235086048584859352227031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 823390699056572901484687 1235086048584859352227031)
                ·
                  refine ⟨1852629072877289028340547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1235086048584859352227031 1852629072877289028340547)
                  ·
                    refine ⟨2778943609315933542510821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1852629072877289028340547 2778943609315933542510821)
                    ·
                      refine ⟨521051926746737539220779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2778943609315933542510821 521051926746737539220779)
                      ·
                        rfl

theorem cell23_1014745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 2, 1, 1, 1, 4].length) (baseStart_1014745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1014745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1014745 prefixEnd_1014745 := by exact prefixLift 1014745
  have htrace : WordTrace (prefixWord ++ tailWord_1014745) baseStart_1014745 baseEnd_1014745 := by
    simpa [prefixWord, tailWord_1014745, baseEnd_1014745] using wordTrace_append hprefix tailTrace_1014745
  have hstable : (prefixWord ++ tailWord_1014745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014745).length < 2 ^ (prefixWord ++ tailWord_1014745).sum := by decide
  have hdescent : baseEnd_1014745 < baseStart_1014745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014762 : List Nat := [3, 1, 3, 1, 2, 2, 2, 4, 1, 2, 2]
def baseStart_1014762 : Nat := 118140960795 + 1014762 * 2 ^ 59
def prefixEnd_1014762 : Nat := 4983230072969 + 3 ^ 40 * 1014762 * 2
def baseEnd_1014762 : Nat := 521060655917863972708201

theorem tailTrace_1014762 : CollatzResearch.WordTrace tailWord_1014762 prefixEnd_1014762 521060655917863972708201 := by
  unfold tailWord_1014762
  simp only [CollatzResearch.WordTrace]
  refine ⟨9252852687424514099247635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24674273833132037597993693 9252852687424514099247635)
  ·
    refine ⟨13879279031136771148871453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9252852687424514099247635 13879279031136771148871453)
    ·
      refine ⟨5204729636676289180826795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13879279031136771148871453 5204729636676289180826795)
      ·
        refine ⟨7807094455014433771240193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5204729636676289180826795 7807094455014433771240193)
        ·
          refine ⟨5855320841260825328430145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7807094455014433771240193 5855320841260825328430145)
          ·
            refine ⟨4391490630945618996322609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5855320841260825328430145 4391490630945618996322609)
            ·
              refine ⟨3293617973209214247241957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4391490630945618996322609 3293617973209214247241957)
              ·
                refine ⟨617553369976727671357867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3293617973209214247241957 617553369976727671357867)
                ·
                  refine ⟨926330054965091507036801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 617553369976727671357867 926330054965091507036801)
                  ·
                    refine ⟨694747541223818630277601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 926330054965091507036801 694747541223818630277601)
                    ·
                      refine ⟨521060655917863972708201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 694747541223818630277601 521060655917863972708201)
                      ·
                        rfl

theorem cell23_1014762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 4, 1, 2, 2].length) (baseStart_1014762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1014762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1014762 prefixEnd_1014762 := by exact prefixLift 1014762
  have htrace : WordTrace (prefixWord ++ tailWord_1014762) baseStart_1014762 baseEnd_1014762 := by
    simpa [prefixWord, tailWord_1014762, baseEnd_1014762] using wordTrace_append hprefix tailTrace_1014762
  have hstable : (prefixWord ++ tailWord_1014762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014762).length < 2 ^ (prefixWord ++ tailWord_1014762).sum := by decide
  have hdescent : baseEnd_1014762 < baseStart_1014762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014778 : List Nat := [3, 1, 1, 1, 1, 2, 1, 7, 2, 1, 3]
def baseStart_1014778 : Nat := 118140960795 + 1014778 * 2 ^ 59
def prefixEnd_1014778 : Nat := 4983230072969 + 3 ^ 40 * 1014778 * 2
def baseEnd_1014778 : Nat := 521068871608335910108127

theorem tailTrace_1014778 : CollatzResearch.WordTrace tailWord_1014778 prefixEnd_1014778 521068871608335910108127 := by
  unfold tailWord_1014778
  simp only [CollatzResearch.WordTrace]
  refine ⟨9252998579410022782393247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24674662878426727419715325 9252998579410022782393247)
  ·
    refine ⟨13879497869115034173589871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9252998579410022782393247 13879497869115034173589871)
    ·
      refine ⟨20819246803672551260384807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13879497869115034173589871 20819246803672551260384807)
      ·
        refine ⟨31228870205508826890577211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20819246803672551260384807 31228870205508826890577211)
        ·
          refine ⟨46843305308263240335865817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31228870205508826890577211 46843305308263240335865817)
          ·
            refine ⟨35132478981197430251899363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46843305308263240335865817 35132478981197430251899363)
            ·
              refine ⟨52698718471796145377849045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35132478981197430251899363 52698718471796145377849045)
              ·
                refine ⟨1235126214182722157293337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 52698718471796145377849045 1235126214182722157293337)
                ·
                  refine ⟨926344660637041617970003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1235126214182722157293337 926344660637041617970003)
                  ·
                    refine ⟨1389516990955562426955005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 926344660637041617970003 1389516990955562426955005)
                    ·
                      refine ⟨521068871608335910108127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1389516990955562426955005 521068871608335910108127)
                      ·
                        rfl

theorem cell23_1014778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 7, 2, 1, 3].length) (baseStart_1014778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1014778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1014778 prefixEnd_1014778 := by exact prefixLift 1014778
  have htrace : WordTrace (prefixWord ++ tailWord_1014778) baseStart_1014778 baseEnd_1014778 := by
    simpa [prefixWord, tailWord_1014778, baseEnd_1014778] using wordTrace_append hprefix tailTrace_1014778
  have hstable : (prefixWord ++ tailWord_1014778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014778).length < 2 ^ (prefixWord ++ tailWord_1014778).sum := by decide
  have hdescent : baseEnd_1014778 < baseStart_1014778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014782 : List Nat := [4, 2, 2, 2, 2, 1, 2, 2, 1, 2, 3]
def baseStart_1014782 : Nat := 118140960795 + 1014782 * 2 ^ 59
def prefixEnd_1014782 : Nat := 4983230072969 + 3 ^ 40 * 1014782 * 2
def baseEnd_1014782 : Nat := 521070925530953894458109

theorem tailTrace_1014782 : CollatzResearch.WordTrace tailWord_1014782 prefixEnd_1014782 521070925530953894458109 := by
  unfold tailWord_1014782
  simp only [CollatzResearch.WordTrace]
  refine ⟨4626517526203199976589825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24674760139750399875145733 4626517526203199976589825)
  ·
    refine ⟨3469888144652399982442369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4626517526203199976589825 3469888144652399982442369)
    ·
      refine ⟨2602416108489299986831777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3469888144652399982442369 2602416108489299986831777)
      ·
        refine ⟨1951812081366974990123833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2602416108489299986831777 1951812081366974990123833)
        ·
          refine ⟨1463859061025231242592875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1951812081366974990123833 1463859061025231242592875)
          ·
            refine ⟨2195788591537846863889313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1463859061025231242592875 2195788591537846863889313)
            ·
              refine ⟨1646841443653385147916985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2195788591537846863889313 1646841443653385147916985)
              ·
                refine ⟨1235131082740038860937739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1646841443653385147916985 1235131082740038860937739)
                ·
                  refine ⟨1852696624110058291406609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1235131082740038860937739 1852696624110058291406609)
                  ·
                    refine ⟨1389522468082543718554957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1852696624110058291406609 1389522468082543718554957)
                    ·
                      refine ⟨521070925530953894458109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1389522468082543718554957 521070925530953894458109)
                      ·
                        rfl

theorem cell23_1014782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_1014782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1014782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1014782 prefixEnd_1014782 := by exact prefixLift 1014782
  have htrace : WordTrace (prefixWord ++ tailWord_1014782) baseStart_1014782 baseEnd_1014782 := by
    simpa [prefixWord, tailWord_1014782, baseEnd_1014782] using wordTrace_append hprefix tailTrace_1014782
  have hstable : (prefixWord ++ tailWord_1014782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014782).length < 2 ^ (prefixWord ++ tailWord_1014782).sum := by decide
  have hdescent : baseEnd_1014782 < baseStart_1014782 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014784 : List Nat := [2, 1, 1, 2, 1, 1, 1, 2, 3, 5, 4]
def baseStart_1014784 : Nat := 118140960795 + 1014784 * 2 ^ 59
def prefixEnd_1014784 : Nat := 4983230072969 + 3 ^ 40 * 1014784 * 2
def baseEnd_1014784 : Nat := 521071952492262886633099

theorem tailTrace_1014784 : CollatzResearch.WordTrace tailWord_1014784 prefixEnd_1014784 521071952492262886633099 := by
  unfold tailWord_1014784
  simp only [CollatzResearch.WordTrace]
  refine ⟨18506106577809177077145703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24674808770412236102860937 18506106577809177077145703)
  ·
    refine ⟨27759159866713765615718555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18506106577809177077145703 27759159866713765615718555)
    ·
      refine ⟨41638739800070648423577833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27759159866713765615718555 41638739800070648423577833)
      ·
        refine ⟨31229054850052986317683375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41638739800070648423577833 31229054850052986317683375)
        ·
          refine ⟨46843582275079479476525063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31229054850052986317683375 46843582275079479476525063)
          ·
            refine ⟨70265373412619219214787595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46843582275079479476525063 70265373412619219214787595)
            ·
              refine ⟨105398060118928828822181393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70265373412619219214787595 105398060118928828822181393)
              ·
                refine ⟨79048545089196621616636045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105398060118928828822181393 79048545089196621616636045)
                ·
                  refine ⟨29643204408448733106238517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79048545089196621616636045 29643204408448733106238517)
                  ·
                    refine ⟨2779050413292068728709861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29643204408448733106238517 2779050413292068728709861)
                    ·
                      refine ⟨521071952492262886633099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2779050413292068728709861 521071952492262886633099)
                      ·
                        rfl

theorem cell23_1014784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 3, 5, 4].length) (baseStart_1014784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1014784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1014784 prefixEnd_1014784 := by exact prefixLift 1014784
  have htrace : WordTrace (prefixWord ++ tailWord_1014784) baseStart_1014784 baseEnd_1014784 := by
    simpa [prefixWord, tailWord_1014784, baseEnd_1014784] using wordTrace_append hprefix tailTrace_1014784
  have hstable : (prefixWord ++ tailWord_1014784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014784).length < 2 ^ (prefixWord ++ tailWord_1014784).sum := by decide
  have hdescent : baseEnd_1014784 < baseStart_1014784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014802 : List Nat := [3, 2, 5, 1, 2, 1, 9]
def baseStart_1014802 : Nat := 118140960795 + 1014802 * 2 ^ 59
def prefixEnd_1014802 : Nat := 4983230072969 + 3 ^ 40 * 1014802 * 2
def baseEnd_1014802 : Nat := 6433101174617824891457

theorem tailTrace_1014802 : CollatzResearch.WordTrace tailWord_1014802 prefixEnd_1014802 6433101174617824891457 := by
  unfold tailWord_1014802
  simp only [CollatzResearch.WordTrace]
  refine ⟨9253217417388285807111665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24675246446368762152297773 9253217417388285807111665)
  ·
    refine ⟨6939913063041214355333749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9253217417388285807111665 6939913063041214355333749)
    ·
      refine ⟨650616849660113845812539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6939913063041214355333749 650616849660113845812539)
      ·
        refine ⟨975925274490170768718809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 650616849660113845812539 975925274490170768718809)
        ·
          refine ⟨731943955867628076539107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 975925274490170768718809 731943955867628076539107)
          ·
            refine ⟨1097915933801442114808661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 731943955867628076539107 1097915933801442114808661)
            ·
              refine ⟨6433101174617824891457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1097915933801442114808661 6433101174617824891457)
              ·
                rfl

theorem cell23_1014802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 9].length) (baseStart_1014802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1014802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1014802 prefixEnd_1014802 := by exact prefixLift 1014802
  have htrace : WordTrace (prefixWord ++ tailWord_1014802) baseStart_1014802 baseEnd_1014802 := by
    simpa [prefixWord, tailWord_1014802, baseEnd_1014802] using wordTrace_append hprefix tailTrace_1014802
  have hstable : (prefixWord ++ tailWord_1014802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014802).length < 2 ^ (prefixWord ++ tailWord_1014802).sum := by decide
  have hdescent : baseEnd_1014802 < baseStart_1014802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014805 : List Nat := [1, 3, 2, 1, 4, 1, 2, 3, 1, 3, 2]
def baseStart_1014805 : Nat := 118140960795 + 1014805 * 2 ^ 59
def prefixEnd_1014805 : Nat := 4983230072969 + 3 ^ 40 * 1014805 * 2
def baseEnd_1014805 : Nat := 521082735586007304470503

theorem tailTrace_1014805 : CollatzResearch.WordTrace tailWord_1014805 prefixEnd_1014805 521082735586007304470503 := by
  unfold tailWord_1014805
  simp only [CollatzResearch.WordTrace]
  refine ⟨37012979088542274740805869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24675319392361516493870579 37012979088542274740805869)
  ·
    refine ⟨13879867158203353027802201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37012979088542274740805869 13879867158203353027802201)
    ·
      refine ⟨10409900368652514770851651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13879867158203353027802201 10409900368652514770851651)
      ·
        refine ⟨15614850552978772156277477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10409900368652514770851651 15614850552978772156277477)
        ·
          refine ⟨2927784478683519779302027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15614850552978772156277477 2927784478683519779302027)
          ·
            refine ⟨4391676718025279668953041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2927784478683519779302027 4391676718025279668953041)
            ·
              refine ⟨3293757538518959751714781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4391676718025279668953041 3293757538518959751714781)
              ·
                refine ⟨1235159076944609906893043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3293757538518959751714781 1235159076944609906893043)
                ·
                  refine ⟨1852738615416914860339565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1235159076944609906893043 1852738615416914860339565)
                  ·
                    refine ⟨694776980781343072627337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1852738615416914860339565 694776980781343072627337)
                    ·
                      refine ⟨521082735586007304470503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 694776980781343072627337 521082735586007304470503)
                      ·
                        rfl

theorem cell23_1014805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 3, 1, 3, 2].length) (baseStart_1014805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1014805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1014805 prefixEnd_1014805 := by exact prefixLift 1014805
  have htrace : WordTrace (prefixWord ++ tailWord_1014805) baseStart_1014805 baseEnd_1014805 := by
    simpa [prefixWord, tailWord_1014805, baseEnd_1014805] using wordTrace_append hprefix tailTrace_1014805
  have hstable : (prefixWord ++ tailWord_1014805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014805).length < 2 ^ (prefixWord ++ tailWord_1014805).sum := by decide
  have hdescent : baseEnd_1014805 < baseStart_1014805 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014821 : List Nat := [1, 3, 1, 2, 2, 2, 2, 1, 2, 4, 3]
def baseStart_1014821 : Nat := 118140960795 + 1014821 * 2 ^ 59
def prefixEnd_1014821 : Nat := 4983230072969 + 3 ^ 40 * 1014821 * 2
def baseEnd_1014821 : Nat := 521090951276479241870429

theorem tailTrace_1014821 : CollatzResearch.WordTrace tailWord_1014821 prefixEnd_1014821 521090951276479241870429 := by
  unfold tailWord_1014821
  simp only [CollatzResearch.WordTrace]
  refine ⟨37013562656484309473388317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24675708437656206315592211 37013562656484309473388317)
  ·
    refine ⟨13880085996181616052520619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37013562656484309473388317 13880085996181616052520619)
    ·
      refine ⟨20820128994272424078780929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13880085996181616052520619 20820128994272424078780929)
      ·
        refine ⟨15615096745704318059085697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20820128994272424078780929 15615096745704318059085697)
        ·
          refine ⟨11711322559278238544314273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15615096745704318059085697 11711322559278238544314273)
          ·
            refine ⟨8783491919458678908235705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11711322559278238544314273 8783491919458678908235705)
            ·
              refine ⟨6587618939594009181176779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8783491919458678908235705 6587618939594009181176779)
              ·
                refine ⟨9881428409391013771765169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6587618939594009181176779 9881428409391013771765169)
                ·
                  refine ⟨7411071307043260328823877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9881428409391013771765169 7411071307043260328823877)
                  ·
                    refine ⟨1389575870070611311654477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7411071307043260328823877 1389575870070611311654477)
                    ·
                      refine ⟨521090951276479241870429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1389575870070611311654477 521090951276479241870429)
                      ·
                        rfl

theorem cell23_1014821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 1, 2, 4, 3].length) (baseStart_1014821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1014821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1014821 prefixEnd_1014821 := by exact prefixLift 1014821
  have htrace : WordTrace (prefixWord ++ tailWord_1014821) baseStart_1014821 baseEnd_1014821 := by
    simpa [prefixWord, tailWord_1014821, baseEnd_1014821] using wordTrace_append hprefix tailTrace_1014821
  have hstable : (prefixWord ++ tailWord_1014821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014821).length < 2 ^ (prefixWord ++ tailWord_1014821).sum := by decide
  have hdescent : baseEnd_1014821 < baseStart_1014821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014838 : List Nat := [5, 1, 2, 1, 1, 2, 1, 2, 2, 1, 5]
def baseStart_1014838 : Nat := 118140960795 + 1014838 * 2 ^ 59
def prefixEnd_1014838 : Nat := 4983230072969 + 3 ^ 40 * 1014838 * 2
def baseEnd_1014838 : Nat := 521099680447605675357851

theorem tailTrace_1014838 : CollatzResearch.WordTrace tailWord_1014838 prefixEnd_1014838 521099680447605675357851 := by
  unfold tailWord_1014838
  simp only [CollatzResearch.WordTrace]
  refine ⟨2313386418588920086047323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24676121798281814251171445 2313386418588920086047323)
  ·
    refine ⟨3470079627883380129070985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2313386418588920086047323 3470079627883380129070985)
    ·
      refine ⟨2602559720912535096803239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3470079627883380129070985 2602559720912535096803239)
      ·
        refine ⟨3903839581368802645204859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2602559720912535096803239 3903839581368802645204859)
        ·
          refine ⟨5855759372053203967807289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3903839581368802645204859 5855759372053203967807289)
          ·
            refine ⟨4391819529039902975855467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5855759372053203967807289 4391819529039902975855467)
            ·
              refine ⟨6587729293559854463783201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4391819529039902975855467 6587729293559854463783201)
              ·
                refine ⟨4940796970169890847837401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6587729293559854463783201 4940796970169890847837401)
                ·
                  refine ⟨3705597727627418135878051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4940796970169890847837401 3705597727627418135878051)
                  ·
                    refine ⟨5558396591441127203817077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3705597727627418135878051 5558396591441127203817077)
                    ·
                      refine ⟨521099680447605675357851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5558396591441127203817077 521099680447605675357851)
                      ·
                        rfl

theorem cell23_1014838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_1014838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1014838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1014838 prefixEnd_1014838 := by exact prefixLift 1014838
  have htrace : WordTrace (prefixWord ++ tailWord_1014838) baseStart_1014838 baseEnd_1014838 := by
    simpa [prefixWord, tailWord_1014838, baseEnd_1014838] using wordTrace_append hprefix tailTrace_1014838
  have hstable : (prefixWord ++ tailWord_1014838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014838).length < 2 ^ (prefixWord ++ tailWord_1014838).sum := by decide
  have hdescent : baseEnd_1014838 < baseStart_1014838 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014881 : List Nat := [1, 2, 3, 1, 1, 2, 4, 1, 1, 2, 5]
def baseStart_1014881 : Nat := 118140960795 + 1014881 * 2 ^ 59
def prefixEnd_1014881 : Nat := 4983230072969 + 3 ^ 40 * 1014881 * 2
def baseEnd_1014881 : Nat := 521121760115749007120153

theorem tailTrace_1014881 : CollatzResearch.WordTrace tailWord_1014881 prefixEnd_1014881 521121760115749007120153 := by
  unfold tailWord_1014881
  simp only [CollatzResearch.WordTrace]
  refine ⟨37015751036266939720572497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24677167357511293147048331 37015751036266939720572497)
  ·
    refine ⟨27761813277200204790429373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37015751036266939720572497 27761813277200204790429373)
    ·
      refine ⟨10410679978950076796411015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27761813277200204790429373 10410679978950076796411015)
      ·
        refine ⟨15616019968425115194616523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10410679978950076796411015 15616019968425115194616523)
        ·
          refine ⟨23424029952637672791924785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15616019968425115194616523 23424029952637672791924785)
          ·
            refine ⟨17568022464478254593943589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23424029952637672791924785 17568022464478254593943589)
            ·
              refine ⟨3294004212089672736364423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17568022464478254593943589 3294004212089672736364423)
              ·
                refine ⟨4941006318134509104546635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3294004212089672736364423 4941006318134509104546635)
                ·
                  refine ⟨7411509477201763656819953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4941006318134509104546635 7411509477201763656819953)
                  ·
                    refine ⟨5558632107901322742614965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7411509477201763656819953 5558632107901322742614965)
                    ·
                      refine ⟨521121760115749007120153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5558632107901322742614965 521121760115749007120153)
                      ·
                        rfl

theorem cell23_1014881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 1, 1, 2, 5].length) (baseStart_1014881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1014881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1014881 prefixEnd_1014881 := by exact prefixLift 1014881
  have htrace : WordTrace (prefixWord ++ tailWord_1014881) baseStart_1014881 baseEnd_1014881 := by
    simpa [prefixWord, tailWord_1014881, baseEnd_1014881] using wordTrace_append hprefix tailTrace_1014881
  have hstable : (prefixWord ++ tailWord_1014881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014881).length < 2 ^ (prefixWord ++ tailWord_1014881).sum := by decide
  have hdescent : baseEnd_1014881 < baseStart_1014881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014905 : List Nat := [1, 2, 1, 3, 5, 2, 1, 1, 2, 5]
def baseStart_1014905 : Nat := 118140960795 + 1014905 * 2 ^ 59
def prefixEnd_1014905 : Nat := 4983230072969 + 3 ^ 40 * 1014905 * 2
def baseEnd_1014905 : Nat := 173711361217152304406681

theorem tailTrace_1014905 : CollatzResearch.WordTrace tailWord_1014905 prefixEnd_1014905 173711361217152304406681 := by
  unfold tailWord_1014905
  simp only [CollatzResearch.WordTrace]
  refine ⟨37016626388179991819446169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24677750925453327879630779 37016626388179991819446169)
  ·
    refine ⟨27762469791134993864584627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37016626388179991819446169 27762469791134993864584627)
    ·
      refine ⟨41643704686702490796876941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27762469791134993864584627 41643704686702490796876941)
      ·
        refine ⟨15616389257513434048828853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41643704686702490796876941 15616389257513434048828853)
        ·
          refine ⟨1464036492891884442077705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15616389257513434048828853 1464036492891884442077705)
          ·
            refine ⟨1098027369668913331558279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1464036492891884442077705 1098027369668913331558279)
            ·
              refine ⟨1647041054503369997337419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1098027369668913331558279 1647041054503369997337419)
              ·
                refine ⟨2470561581755054996006129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1647041054503369997337419 2470561581755054996006129)
                ·
                  refine ⟨1852921186316291247004597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2470561581755054996006129 1852921186316291247004597)
                  ·
                    refine ⟨173711361217152304406681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1852921186316291247004597 173711361217152304406681)
                    ·
                      rfl

theorem cell23_1014905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 1, 1, 2, 5].length) (baseStart_1014905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1014905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1014905 prefixEnd_1014905 := by exact prefixLift 1014905
  have htrace : WordTrace (prefixWord ++ tailWord_1014905) baseStart_1014905 baseEnd_1014905 := by
    simpa [prefixWord, tailWord_1014905, baseEnd_1014905] using wordTrace_append hprefix tailTrace_1014905
  have hstable : (prefixWord ++ tailWord_1014905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014905).length < 2 ^ (prefixWord ++ tailWord_1014905).sum := by decide
  have hdescent : baseEnd_1014905 < baseStart_1014905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014908 : List Nat := [2, 2, 2, 1, 1, 3, 1, 2, 1, 6, 2]
def baseStart_1014908 : Nat := 118140960795 + 1014908 * 2 ^ 59
def prefixEnd_1014908 : Nat := 4983230072969 + 3 ^ 40 * 1014908 * 2
def baseEnd_1014908 : Nat := 521135624093420401482529

theorem tailTrace_1014908 : CollatzResearch.WordTrace tailWord_1014908 prefixEnd_1014908 521135624093420401482529 := by
  unfold tailWord_1014908
  simp only [CollatzResearch.WordTrace]
  refine ⟨18508367903584561665902689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24677823871446082221203585 18508367903584561665902689)
  ·
    refine ⟨13881275927688421249427017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18508367903584561665902689 13881275927688421249427017)
    ·
      refine ⟨10410956945766315937070263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13881275927688421249427017 10410956945766315937070263)
      ·
        refine ⟨15616435418649473905605395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10410956945766315937070263 15616435418649473905605395)
        ·
          refine ⟨23424653127974210858408093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15616435418649473905605395 23424653127974210858408093)
          ·
            refine ⟨8784244922990329071903035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23424653127974210858408093 8784244922990329071903035)
            ·
              refine ⟨13176367384485493607854553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8784244922990329071903035 13176367384485493607854553)
              ·
                refine ⟨9882275538364120205890915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13176367384485493607854553 9882275538364120205890915)
                ·
                  refine ⟨14823413307546180308836373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9882275538364120205890915 14823413307546180308836373)
                  ·
                    refine ⟨694847498791227201976705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14823413307546180308836373 694847498791227201976705)
                    ·
                      refine ⟨521135624093420401482529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 694847498791227201976705 521135624093420401482529)
                      ·
                        rfl

theorem cell23_1014908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 2, 1, 6, 2].length) (baseStart_1014908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1014908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1014908 prefixEnd_1014908 := by exact prefixLift 1014908
  have htrace : WordTrace (prefixWord ++ tailWord_1014908) baseStart_1014908 baseEnd_1014908 := by
    simpa [prefixWord, tailWord_1014908, baseEnd_1014908] using wordTrace_append hprefix tailTrace_1014908
  have hstable : (prefixWord ++ tailWord_1014908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014908).length < 2 ^ (prefixWord ++ tailWord_1014908).sum := by decide
  have hdescent : baseEnd_1014908 < baseStart_1014908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014921 : List Nat := [1, 2, 1, 1, 4, 3, 1, 1, 2, 1, 6]
def baseStart_1014921 : Nat := 118140960795 + 1014921 * 2 ^ 59
def prefixEnd_1014921 : Nat := 4983230072969 + 3 ^ 40 * 1014921 * 2
def baseEnd_1014921 : Nat := 521142299341928850619969

theorem tailTrace_1014921 : CollatzResearch.WordTrace tailWord_1014921 prefixEnd_1014921 521142299341928850619969 := by
  unfold tailWord_1014921
  simp only [CollatzResearch.WordTrace]
  refine ⟨37017209956122026552028617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24678139970748017701352411 37017209956122026552028617)
  ·
    refine ⟨27762907467091519914021463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37017209956122026552028617 27762907467091519914021463)
    ·
      refine ⟨41644361200637279871032195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27762907467091519914021463 41644361200637279871032195)
      ·
        refine ⟨62466541800955919806548293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41644361200637279871032195 62466541800955919806548293)
        ·
          refine ⟨11712476587679234963727805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62466541800955919806548293 11712476587679234963727805)
          ·
            refine ⟨4392178720379713111397927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11712476587679234963727805 4392178720379713111397927)
            ·
              refine ⟨6588268080569569667096891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4392178720379713111397927 6588268080569569667096891)
              ·
                refine ⟨9882402120854354500645337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6588268080569569667096891 9882402120854354500645337)
                ·
                  refine ⟨7411801590640765875484003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9882402120854354500645337 7411801590640765875484003)
                  ·
                    refine ⟨11117702385961148813226005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7411801590640765875484003 11117702385961148813226005)
                    ·
                      refine ⟨521142299341928850619969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11117702385961148813226005 521142299341928850619969)
                      ·
                        rfl

theorem cell23_1014921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 1, 2, 1, 6].length) (baseStart_1014921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1014921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1014921 prefixEnd_1014921 := by exact prefixLift 1014921
  have htrace : WordTrace (prefixWord ++ tailWord_1014921) baseStart_1014921 baseEnd_1014921 := by
    simpa [prefixWord, tailWord_1014921, baseEnd_1014921] using wordTrace_append hprefix tailTrace_1014921
  have hstable : (prefixWord ++ tailWord_1014921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014921).length < 2 ^ (prefixWord ++ tailWord_1014921).sum := by decide
  have hdescent : baseEnd_1014921 < baseStart_1014921 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014935 : List Nat := [1, 1, 3, 3, 3, 2, 2, 1, 3, 4]
def baseStart_1014935 : Nat := 118140960795 + 1014935 * 2 ^ 59
def prefixEnd_1014935 : Nat := 4983230072969 + 3 ^ 40 * 1014935 * 2
def baseEnd_1014935 : Nat := 173716496023697265281635

theorem tailTrace_1014935 : CollatzResearch.WordTrace tailWord_1014935 prefixEnd_1014935 173716496023697265281635 := by
  unfold tailWord_1014935
  simp only [CollatzResearch.WordTrace]
  refine ⟨37017720578071306943038259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24678480385380871295358839 37017720578071306943038259)
  ·
    refine ⟨55526580867106960414557389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37017720578071306943038259 55526580867106960414557389)
    ·
      refine ⟨20822467825165110155459021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55526580867106960414557389 20822467825165110155459021)
      ·
        refine ⟨7808425434436916308297133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20822467825165110155459021 7808425434436916308297133)
        ·
          refine ⟨2928159537913843615611425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7808425434436916308297133 2928159537913843615611425)
          ·
            refine ⟨2196119653435382711708569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2928159537913843615611425 2196119653435382711708569)
            ·
              refine ⟨1647089740076537033781427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2196119653435382711708569 1647089740076537033781427)
              ·
                refine ⟨2470634610114805550672141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1647089740076537033781427 2470634610114805550672141)
                ·
                  refine ⟨926487978793052081502053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2470634610114805550672141 926487978793052081502053)
                  ·
                    refine ⟨173716496023697265281635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 926487978793052081502053 173716496023697265281635)
                    ·
                      rfl

theorem cell23_1014935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 1, 3, 4].length) (baseStart_1014935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1014935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1014935 prefixEnd_1014935 := by exact prefixLift 1014935
  have htrace : WordTrace (prefixWord ++ tailWord_1014935) baseStart_1014935 baseEnd_1014935 := by
    simpa [prefixWord, tailWord_1014935, baseEnd_1014935] using wordTrace_append hprefix tailTrace_1014935
  have hstable : (prefixWord ++ tailWord_1014935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014935).length < 2 ^ (prefixWord ++ tailWord_1014935).sum := by decide
  have hdescent : baseEnd_1014935 < baseStart_1014935 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014942 : List Nat := [4, 3, 1, 1, 2, 1, 2, 1, 2, 4, 2]
def baseStart_1014942 : Nat := 118140960795 + 1014942 * 2 ^ 59
def prefixEnd_1014942 : Nat := 4983230072969 + 3 ^ 40 * 1014942 * 2
def baseEnd_1014942 : Nat := 521153082435673268457373

theorem tailTrace_1014942 : CollatzResearch.WordTrace tailWord_1014942 prefixEnd_1014942 521153082435673268457373 := by
  unfold tailWord_1014942
  simp only [CollatzResearch.WordTrace]
  refine ⟨4627246986130743392317885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24678650592697298092362053 4627246986130743392317885)
  ·
    refine ⟨1735217619799028772119207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4627246986130743392317885 1735217619799028772119207)
    ·
      refine ⟨2602826429698543158178811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1735217619799028772119207 2602826429698543158178811)
      ·
        refine ⟨3904239644547814737268217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2602826429698543158178811 3904239644547814737268217)
        ·
          refine ⟨2928179733410861052951163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3904239644547814737268217 2928179733410861052951163)
          ·
            refine ⟨4392269600116291579426745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2928179733410861052951163 4392269600116291579426745)
            ·
              refine ⟨3294202200087218684570059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4392269600116291579426745 3294202200087218684570059)
              ·
                refine ⟨4941303300130828026855089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3294202200087218684570059 4941303300130828026855089)
                ·
                  refine ⟨3705977475098121020141317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4941303300130828026855089 3705977475098121020141317)
                  ·
                    refine ⟨694870776580897691276497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3705977475098121020141317 694870776580897691276497)
                    ·
                      refine ⟨521153082435673268457373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 694870776580897691276497 521153082435673268457373)
                      ·
                        rfl

theorem cell23_1014942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 1, 2, 4, 2].length) (baseStart_1014942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1014942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1014942 prefixEnd_1014942 := by exact prefixLift 1014942
  have htrace : WordTrace (prefixWord ++ tailWord_1014942) baseStart_1014942 baseEnd_1014942 := by
    simpa [prefixWord, tailWord_1014942, baseEnd_1014942] using wordTrace_append hprefix tailTrace_1014942
  have hstable : (prefixWord ++ tailWord_1014942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014942).length < 2 ^ (prefixWord ++ tailWord_1014942).sum := by decide
  have hdescent : baseEnd_1014942 < baseStart_1014942 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014991 : List Nat := [1, 1, 2, 1, 1, 3, 2, 1, 5, 6]
def baseStart_1014991 : Nat := 118140960795 + 1014991 * 2 ^ 59
def prefixEnd_1014991 : Nat := 4983230072969 + 3 ^ 40 * 1014991 * 2
def baseEnd_1014991 : Nat := 173726080995914525581549

theorem tailTrace_1014991 : CollatzResearch.WordTrace tailWord_1014991 prefixEnd_1014991 173726080995914525581549 := by
  unfold tailWord_1014991
  simp only [CollatzResearch.WordTrace]
  refine ⟨37019763065868428507076827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24679842043912285671384551 37019763065868428507076827)
  ·
    refine ⟨55529644598802642760615241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37019763065868428507076827 55529644598802642760615241)
    ·
      refine ⟨41647233449101982070461431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55529644598802642760615241 41647233449101982070461431)
      ·
        refine ⟨62470850173652973105692147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41647233449101982070461431 62470850173652973105692147)
        ·
          refine ⟨93706275260479459658538221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62470850173652973105692147 93706275260479459658538221)
          ·
            refine ⟨35139853222679797371951833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93706275260479459658538221 35139853222679797371951833)
            ·
              refine ⟨26354889917009848028963875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35139853222679797371951833 26354889917009848028963875)
              ·
                refine ⟨39532334875514772043445813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26354889917009848028963875 39532334875514772043445813)
                ·
                  refine ⟨3706156394579509879073045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39532334875514772043445813 3706156394579509879073045)
                  ·
                    refine ⟨173726080995914525581549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3706156394579509879073045 173726080995914525581549)
                    ·
                      rfl

theorem cell23_1014991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 5, 6].length) (baseStart_1014991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1014991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1014991 prefixEnd_1014991 := by exact prefixLift 1014991
  have htrace : WordTrace (prefixWord ++ tailWord_1014991) baseStart_1014991 baseEnd_1014991 := by
    simpa [prefixWord, tailWord_1014991, baseEnd_1014991] using wordTrace_append hprefix tailTrace_1014991
  have hstable : (prefixWord ++ tailWord_1014991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014991).length < 2 ^ (prefixWord ++ tailWord_1014991).sum := by decide
  have hdescent : baseEnd_1014991 < baseStart_1014991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015038 : List Nat := [4, 2, 2, 1, 1, 13]
def baseStart_1015038 : Nat := 118140960795 + 1015038 * 2 ^ 59
def prefixEnd_1015038 : Nat := 4983230072969 + 3 ^ 40 * 1015038 * 2
def baseEnd_1015038 : Nat := 2144865747236645649617

theorem tailTrace_1015038 : CollatzResearch.WordTrace tailWord_1015038 prefixEnd_1015038 2144865747236645649617 := by
  unfold tailWord_1015038
  simp only [CollatzResearch.WordTrace]
  refine ⟨4627684662087269441754721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24680984864465437022691845 4627684662087269441754721)
  ·
    refine ⟨3470763496565452081316041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4627684662087269441754721 3470763496565452081316041)
    ·
      refine ⟨2603072622424089060987031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3470763496565452081316041 2603072622424089060987031)
      ·
        refine ⟨3904608933636133591480547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2603072622424089060987031 3904608933636133591480547)
        ·
          refine ⟨5856913400454200387220821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3904608933636133591480547 5856913400454200387220821)
          ·
            refine ⟨2144865747236645649617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 5856913400454200387220821 2144865747236645649617)
            ·
              rfl

theorem cell23_1015038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 13].length) (baseStart_1015038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1015038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1015038 prefixEnd_1015038 := by exact prefixLift 1015038
  have htrace : WordTrace (prefixWord ++ tailWord_1015038) baseStart_1015038 baseEnd_1015038 := by
    simpa [prefixWord, tailWord_1015038, baseEnd_1015038] using wordTrace_append hprefix tailTrace_1015038
  have hstable : (prefixWord ++ tailWord_1015038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015038).length < 2 ^ (prefixWord ++ tailWord_1015038).sum := by decide
  have hdescent : baseEnd_1015038 < baseStart_1015038 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015049 : List Nat := [1, 2, 1, 1, 3, 3, 3, 4, 1, 2, 2]
def baseStart_1015049 : Nat := 118140960795 + 1015049 * 2 ^ 59
def prefixEnd_1015049 : Nat := 4983230072969 + 3 ^ 40 * 1015049 * 2
def baseEnd_1015049 : Nat := 521208024865704349819381

theorem tailTrace_1015049 : CollatzResearch.WordTrace tailWord_1015049 prefixEnd_1015049 521208024865704349819381 := by
  unfold tailWord_1015049
  simp only [CollatzResearch.WordTrace]
  refine ⟨37021878499658304412688201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24681252333105536275125467 37021878499658304412688201)
  ·
    refine ⟨27766408874743728309516151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37021878499658304412688201 27766408874743728309516151)
    ·
      refine ⟨41649613312115592464274227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27766408874743728309516151 41649613312115592464274227)
      ·
        refine ⟨62474419968173388696411341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41649613312115592464274227 62474419968173388696411341)
        ·
          refine ⟨23427907488065020761154253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62474419968173388696411341 23427907488065020761154253)
          ·
            refine ⟨8785465308024382785432845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23427907488065020761154253 8785465308024382785432845)
            ·
              refine ⟨3294549490509143544537317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8785465308024382785432845 3294549490509143544537317)
              ·
                refine ⟨617728029470464414600747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3294549490509143544537317 617728029470464414600747)
                ·
                  refine ⟨926592044205696621901121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 617728029470464414600747 926592044205696621901121)
                  ·
                    refine ⟨694944033154272466425841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 926592044205696621901121 694944033154272466425841)
                    ·
                      refine ⟨521208024865704349819381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 694944033154272466425841 521208024865704349819381)
                      ·
                        rfl

theorem cell23_1015049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 4, 1, 2, 2].length) (baseStart_1015049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1015049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1015049 prefixEnd_1015049 := by exact prefixLift 1015049
  have htrace : WordTrace (prefixWord ++ tailWord_1015049) baseStart_1015049 baseEnd_1015049 := by
    simpa [prefixWord, tailWord_1015049, baseEnd_1015049] using wordTrace_append hprefix tailTrace_1015049
  have hstable : (prefixWord ++ tailWord_1015049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015049).length < 2 ^ (prefixWord ++ tailWord_1015049).sum := by decide
  have hdescent : baseEnd_1015049 < baseStart_1015049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015082 : List Nat := [3, 1, 4, 2, 1, 1, 2, 2, 1, 3, 3]
def baseStart_1015082 : Nat := 118140960795 + 1015082 * 2 ^ 59
def prefixEnd_1015082 : Nat := 4983230072969 + 3 ^ 40 * 1015082 * 2
def baseEnd_1015082 : Nat := 521224969727302720706729

theorem tailTrace_1015082 : CollatzResearch.WordTrace tailWord_1015082 prefixEnd_1015082 521224969727302720706729 := by
  unfold tailWord_1015082
  simp only [CollatzResearch.WordTrace]
  refine ⟨9255770527134687762159875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24682054739025834032426333 9255770527134687762159875)
  ·
    refine ⟨13883655790702031643239813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9255770527134687762159875 13883655790702031643239813)
    ·
      refine ⟨2603185460756630933107465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13883655790702031643239813 2603185460756630933107465)
      ·
        refine ⟨1952389095567473199830599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2603185460756630933107465 1952389095567473199830599)
        ·
          refine ⟨2928583643351209799745899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1952389095567473199830599 2928583643351209799745899)
          ·
            refine ⟨4392875465026814699618849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2928583643351209799745899 4392875465026814699618849)
            ·
              refine ⟨3294656598770111024714137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4392875465026814699618849 3294656598770111024714137)
              ·
                refine ⟨2470992449077583268535603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3294656598770111024714137 2470992449077583268535603)
                ·
                  refine ⟨3706488673616374902803405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2470992449077583268535603 3706488673616374902803405)
                  ·
                    refine ⟨1389933252606140588551277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3706488673616374902803405 1389933252606140588551277)
                    ·
                      refine ⟨521224969727302720706729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1389933252606140588551277 521224969727302720706729)
                      ·
                        rfl

theorem cell23_1015082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_1015082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1015082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1015082 prefixEnd_1015082 := by exact prefixLift 1015082
  have htrace : WordTrace (prefixWord ++ tailWord_1015082) baseStart_1015082 baseEnd_1015082 := by
    simpa [prefixWord, tailWord_1015082, baseEnd_1015082] using wordTrace_append hprefix tailTrace_1015082
  have hstable : (prefixWord ++ tailWord_1015082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015082).length < 2 ^ (prefixWord ++ tailWord_1015082).sum := by decide
  have hdescent : baseEnd_1015082 < baseStart_1015082 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015098 : List Nat := [3, 1, 1, 1, 4, 1, 1, 1, 4, 6]
def baseStart_1015098 : Nat := 118140960795 + 1015098 * 2 ^ 59
def prefixEnd_1015098 : Nat := 4983230072969 + 3 ^ 40 * 1015098 * 2
def baseEnd_1015098 : Nat := 173744395139258219368885

theorem tailTrace_1015098 : CollatzResearch.WordTrace tailWord_1015098 prefixEnd_1015098 173744395139258219368885 := by
  unfold tailWord_1015098
  simp only [CollatzResearch.WordTrace]
  refine ⟨9255916419120196445305487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24682443784320523854147965 9255916419120196445305487)
  ·
    refine ⟨13883874628680294667958231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9255916419120196445305487 13883874628680294667958231)
    ·
      refine ⟨20825811943020442001937347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13883874628680294667958231 20825811943020442001937347)
      ·
        refine ⟨31238717914530663002906021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20825811943020442001937347 31238717914530663002906021)
        ·
          refine ⟨5857259608974499313044879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31238717914530663002906021 5857259608974499313044879)
          ·
            refine ⟨8785889413461748969567319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5857259608974499313044879 8785889413461748969567319)
            ·
              refine ⟨13178834120192623454350979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8785889413461748969567319 13178834120192623454350979)
              ·
                refine ⟨19768251180288935181526469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13178834120192623454350979 19768251180288935181526469)
                ·
                  refine ⟨3706547096304175346536213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19768251180288935181526469 3706547096304175346536213)
                  ·
                    refine ⟨173744395139258219368885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3706547096304175346536213 173744395139258219368885)
                    ·
                      rfl

theorem cell23_1015098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 4, 6].length) (baseStart_1015098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1015098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1015098 prefixEnd_1015098 := by exact prefixLift 1015098
  have htrace : WordTrace (prefixWord ++ tailWord_1015098) baseStart_1015098 baseEnd_1015098 := by
    simpa [prefixWord, tailWord_1015098, baseEnd_1015098] using wordTrace_append hprefix tailTrace_1015098
  have hstable : (prefixWord ++ tailWord_1015098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015098).length < 2 ^ (prefixWord ++ tailWord_1015098).sum := by decide
  have hdescent : baseEnd_1015098 < baseStart_1015098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015128 : List Nat := [2, 1, 2, 2, 1, 1, 3, 4, 7]
def baseStart_1015128 : Nat := 118140960795 + 1015128 * 2 ^ 59
def prefixEnd_1015128 : Nat := 4983230072969 + 3 ^ 40 * 1015128 * 2
def baseEnd_1015128 : Nat := 57916509981934393414613

theorem tailTrace_1015128 : CollatzResearch.WordTrace tailWord_1015128 prefixEnd_1015128 57916509981934393414613 := by
  unfold tailWord_1015128
  simp only [CollatzResearch.WordTrace]
  refine ⟨18512379933186050452407019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24683173244248067269876025 18512379933186050452407019)
  ·
    refine ⟨27768569899779075678610529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18512379933186050452407019 27768569899779075678610529)
    ·
      refine ⟨20826427424834306758957897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27768569899779075678610529 20826427424834306758957897)
      ·
        refine ⟨15619820568625730069218423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20826427424834306758957897 15619820568625730069218423)
        ·
          refine ⟨23429730852938595103827635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15619820568625730069218423 23429730852938595103827635)
          ·
            refine ⟨35144596279407892655741453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23429730852938595103827635 35144596279407892655741453)
            ·
              refine ⟨13179223604777959745903045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35144596279407892655741453 13179223604777959745903045)
              ·
                refine ⟨2471104425895867452356821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13179223604777959745903045 2471104425895867452356821)
                ·
                  refine ⟨57916509981934393414613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2471104425895867452356821 57916509981934393414613)
                  ·
                    rfl

theorem cell23_1015128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 4, 7].length) (baseStart_1015128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1015128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1015128 prefixEnd_1015128 := by exact prefixLift 1015128
  have htrace : WordTrace (prefixWord ++ tailWord_1015128) baseStart_1015128 baseEnd_1015128 := by
    simpa [prefixWord, tailWord_1015128, baseEnd_1015128] using wordTrace_append hprefix tailTrace_1015128
  have hstable : (prefixWord ++ tailWord_1015128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015128).length < 2 ^ (prefixWord ++ tailWord_1015128).sum := by decide
  have hdescent : baseEnd_1015128 < baseStart_1015128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015145 : List Nat := [1, 2, 1, 1, 1, 3, 2, 7, 5]
def baseStart_1015145 : Nat := 118140960795 + 1015145 * 2 ^ 59
def prefixEnd_1015145 : Nat := 4983230072969 + 3 ^ 40 * 1015145 * 2
def baseEnd_1015145 : Nat := 57917479889837330468771

theorem tailTrace_1015145 : CollatzResearch.WordTrace tailWord_1015145 prefixEnd_1015145 57917479889837330468771 := by
  unfold tailWord_1015145
  simp only [CollatzResearch.WordTrace]
  refine ⟨37025379907310512808182889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24683586604873675205455259 37025379907310512808182889)
  ·
    refine ⟨27769034930482884606137167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37025379907310512808182889 27769034930482884606137167)
    ·
      refine ⟨41653552395724326909205751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27769034930482884606137167 41653552395724326909205751)
      ·
        refine ⟨62480328593586490363808627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41653552395724326909205751 62480328593586490363808627)
        ·
          refine ⟨93720492890379735545712941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62480328593586490363808627 93720492890379735545712941)
          ·
            refine ⟨35145184833892400829642353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93720492890379735545712941 35145184833892400829642353)
            ·
              refine ⟨26358888625419300622231765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35145184833892400829642353 26358888625419300622231765)
              ·
                refine ⟨617786452158264858333557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 26358888625419300622231765 617786452158264858333557)
                ·
                  refine ⟨57917479889837330468771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 617786452158264858333557 57917479889837330468771)
                  ·
                    rfl

theorem cell23_1015145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 7, 5].length) (baseStart_1015145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1015145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1015145 prefixEnd_1015145 := by exact prefixLift 1015145
  have htrace : WordTrace (prefixWord ++ tailWord_1015145) baseStart_1015145 baseEnd_1015145 := by
    simpa [prefixWord, tailWord_1015145, baseEnd_1015145] using wordTrace_append hprefix tailTrace_1015145
  have hstable : (prefixWord ++ tailWord_1015145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015145).length < 2 ^ (prefixWord ++ tailWord_1015145).sum := by decide
  have hdescent : baseEnd_1015145 < baseStart_1015145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015205 : List Nat := [1, 3, 1, 2, 1, 1, 2, 1, 7, 4]
def baseStart_1015205 : Nat := 118140960795 + 1015205 * 2 ^ 59
def prefixEnd_1015205 : Nat := 4983230072969 + 3 ^ 40 * 1015205 * 2
def baseEnd_1015205 : Nat := 173762709282601913156221

theorem tailTrace_1015205 : CollatzResearch.WordTrace tailWord_1015205 prefixEnd_1015205 173762709282601913156221 := by
  unfold tailWord_1015205
  simp only [CollatzResearch.WordTrace]
  refine ⟨37027568287093143055367069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24685045524728762036911379 37027568287093143055367069)
  ·
    refine ⟨13885338107659928645762651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37027568287093143055367069 13885338107659928645762651)
    ·
      refine ⟨20828007161489892968643977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13885338107659928645762651 20828007161489892968643977)
      ·
        refine ⟨15621005371117419726482983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20828007161489892968643977 15621005371117419726482983)
        ·
          refine ⟨23431508056676129589724475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15621005371117419726482983 23431508056676129589724475)
          ·
            refine ⟨35147262085014194384586713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23431508056676129589724475 35147262085014194384586713)
            ·
              refine ⟨26360446563760645788440035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35147262085014194384586713 26360446563760645788440035)
              ·
                refine ⟨39540669845640968682660053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26360446563760645788440035 39540669845640968682660053)
                ·
                  refine ⟨926734449507210203499845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 39540669845640968682660053 926734449507210203499845)
                  ·
                    refine ⟨173762709282601913156221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 926734449507210203499845 173762709282601913156221)
                    ·
                      rfl

theorem cell23_1015205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 7, 4].length) (baseStart_1015205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1015205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1015205 prefixEnd_1015205 := by exact prefixLift 1015205
  have htrace : WordTrace (prefixWord ++ tailWord_1015205) baseStart_1015205 baseEnd_1015205 := by
    simpa [prefixWord, tailWord_1015205, baseEnd_1015205] using wordTrace_append hprefix tailTrace_1015205
  have hstable : (prefixWord ++ tailWord_1015205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015205).length < 2 ^ (prefixWord ++ tailWord_1015205).sum := by decide
  have hdescent : baseEnd_1015205 < baseStart_1015205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015235 : List Nat := [1, 1, 1, 3, 1, 1, 6, 3, 6]
def baseStart_1015235 : Nat := 118140960795 + 1015235 * 2 ^ 59
def prefixEnd_1015235 : Nat := 4983230072969 + 3 ^ 40 * 1015235 * 2
def baseEnd_1015235 : Nat := 57922614696382291343725

theorem tailTrace_1015235 : CollatzResearch.WordTrace tailWord_1015235 prefixEnd_1015235 57922614696382291343725 := by
  unfold tailWord_1015235
  simp only [CollatzResearch.WordTrace]
  refine ⟨37028662476984458178959159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24685774984656305452639439 37028662476984458178959159)
  ·
    refine ⟨55542993715476687268438739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37028662476984458178959159 55542993715476687268438739)
    ·
      refine ⟨83314490573215030902658109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55542993715476687268438739 83314490573215030902658109)
      ·
        refine ⟨31242933964955636588496791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83314490573215030902658109 31242933964955636588496791)
        ·
          refine ⟨46864400947433454882745187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31242933964955636588496791 46864400947433454882745187)
          ·
            refine ⟨70296601421150182324117781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46864400947433454882745187 70296601421150182324117781)
            ·
              refine ⟨3295153191616414796443021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 70296601421150182324117781 3295153191616414796443021)
              ·
                refine ⟨1235682446856155548666133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3295153191616414796443021 1235682446856155548666133)
                ·
                  refine ⟨57922614696382291343725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1235682446856155548666133 57922614696382291343725)
                  ·
                    rfl

theorem cell23_1015235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 3, 6].length) (baseStart_1015235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1015235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1015235 prefixEnd_1015235 := by exact prefixLift 1015235
  have htrace : WordTrace (prefixWord ++ tailWord_1015235) baseStart_1015235 baseEnd_1015235 := by
    simpa [prefixWord, tailWord_1015235, baseEnd_1015235] using wordTrace_append hprefix tailTrace_1015235
  have hstable : (prefixWord ++ tailWord_1015235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015235).length < 2 ^ (prefixWord ++ tailWord_1015235).sum := by decide
  have hdescent : baseEnd_1015235 < baseStart_1015235 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015269 : List Nat := [1, 3, 1, 5, 1, 3, 1, 2, 6]
def baseStart_1015269 : Nat := 118140960795 + 1015269 * 2 ^ 59
def prefixEnd_1015269 : Nat := 4983230072969 + 3 ^ 40 * 1015269 * 2
def baseEnd_1015269 : Nat := 57924554512188165452041

theorem tailTrace_1015269 : CollatzResearch.WordTrace tailWord_1015269 prefixEnd_1015269 57924554512188165452041 := by
  unfold tailWord_1015269
  simp only [CollatzResearch.WordTrace]
  refine ⟨37029902558861281985696861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24686601705907521323797907 37029902558861281985696861)
  ·
    refine ⟨13886213459572980744636323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37029902558861281985696861 13886213459572980744636323)
    ·
      refine ⟨20829320189359471116954485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13886213459572980744636323 20829320189359471116954485)
      ·
        refine ⟨1952748767752450417214483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20829320189359471116954485 1952748767752450417214483)
        ·
          refine ⟨2929123151628675625821725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1952748767752450417214483 2929123151628675625821725)
          ·
            refine ⟨1098421181860753359683147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2929123151628675625821725 1098421181860753359683147)
            ·
              refine ⟨1647631772791130039524721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1098421181860753359683147 1647631772791130039524721)
              ·
                refine ⟨1235723829593347529643541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1647631772791130039524721 1235723829593347529643541)
                ·
                  refine ⟨57924554512188165452041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1235723829593347529643541 57924554512188165452041)
                  ·
                    rfl

theorem cell23_1015269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 1, 2, 6].length) (baseStart_1015269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1015269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1015269 prefixEnd_1015269 := by exact prefixLift 1015269
  have htrace : WordTrace (prefixWord ++ tailWord_1015269) baseStart_1015269 baseEnd_1015269 := by
    simpa [prefixWord, tailWord_1015269, baseEnd_1015269] using wordTrace_append hprefix tailTrace_1015269
  have hstable : (prefixWord ++ tailWord_1015269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015269).length < 2 ^ (prefixWord ++ tailWord_1015269).sum := by decide
  have hdescent : baseEnd_1015269 < baseStart_1015269 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015295 : List Nat := [1, 1, 2, 2, 1, 2, 2, 5, 1, 6]
def baseStart_1015295 : Nat := 118140960795 + 1015295 * 2 ^ 59
def prefixEnd_1015295 : Nat := 4983230072969 + 3 ^ 40 * 1015295 * 2
def baseEnd_1015295 : Nat := 173778113702236795781083

theorem tailTrace_1015295 : CollatzResearch.WordTrace tailWord_1015295 prefixEnd_1015295 173778113702236795781083 := by
  unfold tailWord_1015295
  simp only [CollatzResearch.WordTrace]
  refine ⟨37030850856767088426143339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24687233904511392284095559 37030850856767088426143339)
  ·
    refine ⟨55546276285150632639215009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37030850856767088426143339 55546276285150632639215009)
    ·
      refine ⟨41659707213862974479411257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55546276285150632639215009 41659707213862974479411257)
      ·
        refine ⟨31244780410397230859558443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41659707213862974479411257 31244780410397230859558443)
        ·
          refine ⟨46867170615595846289337665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31244780410397230859558443 46867170615595846289337665)
          ·
            refine ⟨35150377961696884717003249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46867170615595846289337665 35150377961696884717003249)
            ·
              refine ⟨26362783471272663537752437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35150377961696884717003249 26362783471272663537752437)
              ·
                refine ⟨2471510950431812206664291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26362783471272663537752437 2471510950431812206664291)
                ·
                  refine ⟨3707266425647718309996437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2471510950431812206664291 3707266425647718309996437)
                  ·
                    refine ⟨173778113702236795781083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3707266425647718309996437 173778113702236795781083)
                    ·
                      rfl

theorem cell23_1015295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 5, 1, 6].length) (baseStart_1015295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1015295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1015295 prefixEnd_1015295 := by exact prefixLift 1015295
  have htrace : WordTrace (prefixWord ++ tailWord_1015295) baseStart_1015295 baseEnd_1015295 := by
    simpa [prefixWord, tailWord_1015295, baseEnd_1015295] using wordTrace_append hprefix tailTrace_1015295
  have hstable : (prefixWord ++ tailWord_1015295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015295).length < 2 ^ (prefixWord ++ tailWord_1015295).sum := by decide
  have hdescent : baseEnd_1015295 < baseStart_1015295 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015305 : List Nat := [1, 2, 1, 1, 3, 1, 3, 2, 3, 1, 5]
def baseStart_1015305 : Nat := 118140960795 + 1015305 * 2 ^ 59
def prefixEnd_1015305 : Nat := 4983230072969 + 3 ^ 40 * 1015305 * 2
def baseEnd_1015305 : Nat := 521339475913255348218203

theorem tailTrace_1015305 : CollatzResearch.WordTrace tailWord_1015305 prefixEnd_1015305 521339475913255348218203 := by
  unfold tailWord_1015305
  simp only [CollatzResearch.WordTrace]
  refine ⟨37031215586730860134007369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24687477057820573422671579 37031215586730860134007369)
  ·
    refine ⟨27773411690048145100505527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37031215586730860134007369 27773411690048145100505527)
    ·
      refine ⟨41660117535072217650758291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27773411690048145100505527 41660117535072217650758291)
      ·
        refine ⟨62490176302608326476137437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41660117535072217650758291 62490176302608326476137437)
        ·
          refine ⟨23433816113478122428551539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62490176302608326476137437 23433816113478122428551539)
          ·
            refine ⟨35150724170217183642827309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23433816113478122428551539 35150724170217183642827309)
            ·
              refine ⟨13181521563831443866060241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35150724170217183642827309 13181521563831443866060241)
              ·
                refine ⟨9886141172873582899545181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13181521563831443866060241 9886141172873582899545181)
                ·
                  refine ⟨3707302939827593587329443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9886141172873582899545181 3707302939827593587329443)
                  ·
                    refine ⟨5560954409741390380994165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3707302939827593587329443 5560954409741390380994165)
                    ·
                      refine ⟨521339475913255348218203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5560954409741390380994165 521339475913255348218203)
                      ·
                        rfl

theorem cell23_1015305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 2, 3, 1, 5].length) (baseStart_1015305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1015305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1015305 prefixEnd_1015305 := by exact prefixLift 1015305
  have htrace : WordTrace (prefixWord ++ tailWord_1015305) baseStart_1015305 baseEnd_1015305 := by
    simpa [prefixWord, tailWord_1015305, baseEnd_1015305] using wordTrace_append hprefix tailTrace_1015305
  have hstable : (prefixWord ++ tailWord_1015305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015305).length < 2 ^ (prefixWord ++ tailWord_1015305).sum := by decide
  have hdescent : baseEnd_1015305 < baseStart_1015305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015322 : List Nat := [3, 1, 1, 3, 1, 1, 1, 2, 5, 2, 3]
def baseStart_1015322 : Nat := 118140960795 + 1015322 * 2 ^ 59
def prefixEnd_1015322 : Nat := 4983230072969 + 3 ^ 40 * 1015322 * 2
def baseEnd_1015322 : Nat := 521348205084381781705625

theorem tailTrace_1015322 : CollatzResearch.WordTrace tailWord_1015322 prefixEnd_1015322 521348205084381781705625 := by
  unfold tailWord_1015322
  simp only [CollatzResearch.WordTrace]
  refine ⟨9257958906917318009344055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24687890418446181358250813 9257958906917318009344055)
  ·
    refine ⟨13886938360375977014016083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9257958906917318009344055 13886938360375977014016083)
    ·
      refine ⟨20830407540563965521024125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13886938360375977014016083 20830407540563965521024125)
      ·
        refine ⟨7811402827711487070384047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20830407540563965521024125 7811402827711487070384047)
        ·
          refine ⟨11717104241567230605576071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7811402827711487070384047 11717104241567230605576071)
          ·
            refine ⟨17575656362350845908364107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11717104241567230605576071 17575656362350845908364107)
            ·
              refine ⟨26363484543526268862546161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17575656362350845908364107 26363484543526268862546161)
              ·
                refine ⟨19772613407644701646909621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26363484543526268862546161 19772613407644701646909621)
                ·
                  refine ⟨1853682506966690779397777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19772613407644701646909621 1853682506966690779397777)
                  ·
                    refine ⟨1390261880225018084548333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1853682506966690779397777 1390261880225018084548333)
                    ·
                      refine ⟨521348205084381781705625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1390261880225018084548333 521348205084381781705625)
                      ·
                        rfl

theorem cell23_1015322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 5, 2, 3].length) (baseStart_1015322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1015322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1015322 prefixEnd_1015322 := by exact prefixLift 1015322
  have htrace : WordTrace (prefixWord ++ tailWord_1015322) baseStart_1015322 baseEnd_1015322 := by
    simpa [prefixWord, tailWord_1015322, baseEnd_1015322] using wordTrace_append hprefix tailTrace_1015322
  have hstable : (prefixWord ++ tailWord_1015322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015322).length < 2 ^ (prefixWord ++ tailWord_1015322).sum := by decide
  have hdescent : baseEnd_1015322 < baseStart_1015322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015342 : List Nat := [4, 1, 3, 1, 2, 1, 1, 10]
def baseStart_1015342 : Nat := 118140960795 + 1015342 * 2 ^ 59
def prefixEnd_1015342 : Nat := 4983230072969 + 3 ^ 40 * 1015342 * 2
def baseEnd_1015342 : Nat := 19309573136943396424279

theorem tailTrace_1015342 : CollatzResearch.WordTrace tailWord_1015342 prefixEnd_1015342 19309573136943396424279 := by
  unfold tailWord_1015342
  simp only [CollatzResearch.WordTrace]
  refine ⟨4629070635949601931638035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24688376725064543635402853 4629070635949601931638035)
  ·
    refine ⟨6943605953924402897457053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4629070635949601931638035 6943605953924402897457053)
    ·
      refine ⟨2603852232721651086546395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6943605953924402897457053 2603852232721651086546395)
      ·
        refine ⟨3905778349082476629819593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2603852232721651086546395 3905778349082476629819593)
        ·
          refine ⟨2929333761811857472364695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3905778349082476629819593 2929333761811857472364695)
          ·
            refine ⟨4394000642717786208547043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2929333761811857472364695 4394000642717786208547043)
            ·
              refine ⟨6591000964076679312820565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4394000642717786208547043 6591000964076679312820565)
              ·
                refine ⟨19309573136943396424279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 6591000964076679312820565 19309573136943396424279)
                ·
                  rfl

theorem cell23_1015342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 10].length) (baseStart_1015342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1015342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1015342 prefixEnd_1015342 := by exact prefixLift 1015342
  have htrace : WordTrace (prefixWord ++ tailWord_1015342) baseStart_1015342 baseEnd_1015342 := by
    simpa [prefixWord, tailWord_1015342, baseEnd_1015342] using wordTrace_append hprefix tailTrace_1015342
  have hstable : (prefixWord ++ tailWord_1015342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015342).length < 2 ^ (prefixWord ++ tailWord_1015342).sum := by decide
  have hdescent : baseEnd_1015342 < baseStart_1015342 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015345 : List Nat := [1, 2, 2, 3, 1, 1, 1, 1, 1, 4, 6]
def baseStart_1015345 : Nat := 118140960795 + 1015345 * 2 ^ 59
def prefixEnd_1015345 : Nat := 4983230072969 + 3 ^ 40 * 1015345 * 2
def baseEnd_1015345 : Nat := 521360015139435191718019

theorem tailTrace_1015345 : CollatzResearch.WordTrace tailWord_1015345 prefixEnd_1015345 521360015139435191718019 := by
  unfold tailWord_1015345
  simp only [CollatzResearch.WordTrace]
  refine ⟨37032674506585946965463489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24688449671057297976975659 37032674506585946965463489)
  ·
    refine ⟨27774505879939460224097617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37032674506585946965463489 27774505879939460224097617)
    ·
      refine ⟨20830879409954595168073213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27774505879939460224097617 20830879409954595168073213)
      ·
        refine ⟨7811579778732973188027455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20830879409954595168073213 7811579778732973188027455)
        ·
          refine ⟨11717369668099459782041183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7811579778732973188027455 11717369668099459782041183)
          ·
            refine ⟨17576054502149189673061775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11717369668099459782041183 17576054502149189673061775)
            ·
              refine ⟨26364081753223784509592663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17576054502149189673061775 26364081753223784509592663)
              ·
                refine ⟨39546122629835676764388995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26364081753223784509592663 39546122629835676764388995)
                ·
                  refine ⟨59319183944753515146583493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39546122629835676764388995 59319183944753515146583493)
                  ·
                    refine ⟨11122346989641284089984405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59319183944753515146583493 11122346989641284089984405)
                    ·
                      refine ⟨521360015139435191718019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11122346989641284089984405 521360015139435191718019)
                      ·
                        rfl

theorem cell23_1015345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 4, 6].length) (baseStart_1015345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1015345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1015345 prefixEnd_1015345 := by exact prefixLift 1015345
  have htrace : WordTrace (prefixWord ++ tailWord_1015345) baseStart_1015345 baseEnd_1015345 := by
    simpa [prefixWord, tailWord_1015345, baseEnd_1015345] using wordTrace_append hprefix tailTrace_1015345
  have hstable : (prefixWord ++ tailWord_1015345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015345).length < 2 ^ (prefixWord ++ tailWord_1015345).sum := by decide
  have hdescent : baseEnd_1015345 < baseStart_1015345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015373 : List Nat := [1, 6, 1, 1, 4, 1, 1, 1, 1, 1, 5]
def baseStart_1015373 : Nat := 118140960795 + 1015373 * 2 ^ 59
def prefixEnd_1015373 : Nat := 4983230072969 + 3 ^ 40 * 1015373 * 2
def baseEnd_1015373 : Nat := 521374392597761082167891

theorem tailTrace_1015373 : CollatzResearch.WordTrace tailWord_1015373 prefixEnd_1015373 521374392597761082167891 := by
  unfold tailWord_1015373
  simp only [CollatzResearch.WordTrace]
  refine ⟨37033695750484507747482773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24689130500323005164988515 37033695750484507747482773)
  ·
    refine ⟨1735954488303961300663255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 37033695750484507747482773 1735954488303961300663255)
    ·
      refine ⟨2603931732455941950994883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1735954488303961300663255 2603931732455941950994883)
      ·
        refine ⟨3905897598683912926492325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2603931732455941950994883 3905897598683912926492325)
        ·
          refine ⟨732355799753233673717311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3905897598683912926492325 732355799753233673717311)
          ·
            refine ⟨1098533699629850510575967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 732355799753233673717311 1098533699629850510575967)
            ·
              refine ⟨1647800549444775765863951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1098533699629850510575967 1647800549444775765863951)
              ·
                refine ⟨2471700824167163648795927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1647800549444775765863951 2471700824167163648795927)
                ·
                  refine ⟨3707551236250745473193891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2471700824167163648795927 3707551236250745473193891)
                  ·
                    refine ⟨5561326854376118209790837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3707551236250745473193891 5561326854376118209790837)
                    ·
                      refine ⟨521374392597761082167891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5561326854376118209790837 521374392597761082167891)
                      ·
                        rfl

theorem cell23_1015373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 1, 1, 1, 1, 5].length) (baseStart_1015373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1015373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1015373 prefixEnd_1015373 := by exact prefixLift 1015373
  have htrace : WordTrace (prefixWord ++ tailWord_1015373) baseStart_1015373 baseEnd_1015373 := by
    simpa [prefixWord, tailWord_1015373, baseEnd_1015373] using wordTrace_append hprefix tailTrace_1015373
  have hstable : (prefixWord ++ tailWord_1015373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015373).length < 2 ^ (prefixWord ++ tailWord_1015373).sum := by decide
  have hdescent : baseEnd_1015373 < baseStart_1015373 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015385 : List Nat := [1, 2, 1, 2, 2, 1, 1, 2, 3, 8]
def baseStart_1015385 : Nat := 118140960795 + 1015385 * 2 ^ 59
def prefixEnd_1015385 : Nat := 4983230072969 + 3 ^ 40 * 1015385 * 2
def baseEnd_1015385 : Nat := 173793518121871678405945

theorem tailTrace_1015385 : CollatzResearch.WordTrace tailWord_1015385 prefixEnd_1015385 173793518121871678405945 := by
  unfold tailWord_1015385
  simp only [CollatzResearch.WordTrace]
  refine ⟨37034133426441033796919609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24689422284294022531279739 37034133426441033796919609)
  ·
    refine ⟨27775600069830775347689707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37034133426441033796919609 27775600069830775347689707)
    ·
      refine ⟨41663400104746163021534561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27775600069830775347689707 41663400104746163021534561)
      ·
        refine ⟨31247550078559622266150921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41663400104746163021534561 31247550078559622266150921)
        ·
          refine ⟨23435662558919716699613191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31247550078559622266150921 23435662558919716699613191)
          ·
            refine ⟨35153493838379575049419787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23435662558919716699613191 35153493838379575049419787)
            ·
              refine ⟨52730240757569362574129681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35153493838379575049419787 52730240757569362574129681)
              ·
                refine ⟨39547680568177021930597261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52730240757569362574129681 39547680568177021930597261)
                ·
                  refine ⟨14830380213066383223973973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39547680568177021930597261 14830380213066383223973973)
                  ·
                    refine ⟨173793518121871678405945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 14830380213066383223973973 173793518121871678405945)
                    ·
                      rfl

theorem cell23_1015385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 3, 8].length) (baseStart_1015385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1015385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1015385 prefixEnd_1015385 := by exact prefixLift 1015385
  have htrace : WordTrace (prefixWord ++ tailWord_1015385) baseStart_1015385 baseEnd_1015385 := by
    simpa [prefixWord, tailWord_1015385, baseEnd_1015385] using wordTrace_append hprefix tailTrace_1015385
  have hstable : (prefixWord ++ tailWord_1015385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015385).length < 2 ^ (prefixWord ++ tailWord_1015385).sum := by decide
  have hdescent : baseEnd_1015385 < baseStart_1015385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015402 : List Nat := [3, 1, 3, 2, 1, 2, 1, 1, 1, 8]
def baseStart_1015402 : Nat := 118140960795 + 1015402 * 2 ^ 59
def prefixEnd_1015402 : Nat := 4983230072969 + 3 ^ 40 * 1015402 * 2
def baseEnd_1015402 : Nat := 173796427845580489568419

theorem tailTrace_1015402 : CollatzResearch.WordTrace tailWord_1015402 prefixEnd_1015402 173796427845580489568419 := by
  unfold tailWord_1015402
  simp only [CollatzResearch.WordTrace]
  refine ⟨9258688366844861425072115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24689835644919630466858973 9258688366844861425072115)
  ·
    refine ⟨13888032550267292137608173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9258688366844861425072115 13888032550267292137608173)
    ·
      refine ⟨5208012206350234551603065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13888032550267292137608173 5208012206350234551603065)
      ·
        refine ⟨3906009154762675913702299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5208012206350234551603065 3906009154762675913702299)
        ·
          refine ⟨5859013732144013870553449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3906009154762675913702299 5859013732144013870553449)
          ·
            refine ⟨4394260299108010402915087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5859013732144013870553449 4394260299108010402915087)
            ·
              refine ⟨6591390448662015604372631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4394260299108010402915087 6591390448662015604372631)
              ·
                refine ⟨9887085672993023406558947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6591390448662015604372631 9887085672993023406558947)
                ·
                  refine ⟨14830628509489535109838421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9887085672993023406558947 14830628509489535109838421)
                  ·
                    refine ⟨173796427845580489568419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 14830628509489535109838421 173796427845580489568419)
                    ·
                      rfl

theorem cell23_1015402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 1, 1, 8].length) (baseStart_1015402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1015402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1015402 prefixEnd_1015402 := by exact prefixLift 1015402
  have htrace : WordTrace (prefixWord ++ tailWord_1015402) baseStart_1015402 baseEnd_1015402 := by
    simpa [prefixWord, tailWord_1015402, baseEnd_1015402] using wordTrace_append hprefix tailTrace_1015402
  have hstable : (prefixWord ++ tailWord_1015402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015402).length < 2 ^ (prefixWord ++ tailWord_1015402).sum := by decide
  have hdescent : baseEnd_1015402 < baseStart_1015402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015460 : List Nat := [2, 3, 1, 2, 2, 3, 3, 1, 2, 2, 2]
def baseStart_1015460 : Nat := 118140960795 + 1015460 * 2 ^ 59
def prefixEnd_1015460 : Nat := 4983230072969 + 3 ^ 40 * 1015460 * 2
def baseEnd_1015460 : Nat := 521419065414702241779991

theorem tailTrace_1015460 : CollatzResearch.WordTrace tailWord_1015460 prefixEnd_1015460 521419065414702241779991 := by
  unfold tailWord_1015460
  simp only [CollatzResearch.WordTrace]
  refine ⟨18518434450584660802949917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24691245934112881070599889 18518434450584660802949917)
  ·
    refine ⟨6944412918969247801106219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18518434450584660802949917 6944412918969247801106219)
    ·
      refine ⟨10416619378453871701659329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6944412918969247801106219 10416619378453871701659329)
      ·
        refine ⟨7812464533840403776244497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10416619378453871701659329 7812464533840403776244497)
        ·
          refine ⟨5859348400380302832183373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7812464533840403776244497 5859348400380302832183373)
          ·
            refine ⟨2197255650142613562068765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5859348400380302832183373 2197255650142613562068765)
            ·
              refine ⟨823970868803480085775787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2197255650142613562068765 823970868803480085775787)
              ·
                refine ⟨1235956303205220128663681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 823970868803480085775787 1235956303205220128663681)
                ·
                  refine ⟨926967227403915096497761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1235956303205220128663681 926967227403915096497761)
                  ·
                    refine ⟨695225420552936322373321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 926967227403915096497761 695225420552936322373321)
                    ·
                      refine ⟨521419065414702241779991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 695225420552936322373321 521419065414702241779991)
                      ·
                        rfl

theorem cell23_1015460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 3, 1, 2, 2, 2].length) (baseStart_1015460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1015460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1015460 prefixEnd_1015460 := by exact prefixLift 1015460
  have htrace : WordTrace (prefixWord ++ tailWord_1015460) baseStart_1015460 baseEnd_1015460 := by
    simpa [prefixWord, tailWord_1015460, baseEnd_1015460] using wordTrace_append hprefix tailTrace_1015460
  have hstable : (prefixWord ++ tailWord_1015460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015460).length < 2 ^ (prefixWord ++ tailWord_1015460).sum := by decide
  have hdescent : baseEnd_1015460 < baseStart_1015460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015499 : List Nat := [1, 1, 1, 1, 3, 2, 1, 3, 4, 4, 2]
def baseStart_1015499 : Nat := 118140960795 + 1015499 * 2 ^ 59
def prefixEnd_1015499 : Nat := 4983230072969 + 3 ^ 40 * 1015499 * 2
def baseEnd_1015499 : Nat := 521439091160227589192311

theorem tailTrace_1015499 : CollatzResearch.WordTrace tailWord_1015499 prefixEnd_1015499 521439091160227589192311 := by
  unfold tailWord_1015499
  simp only [CollatzResearch.WordTrace]
  refine ⟨37038291348028031266569551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24692194232018687511046367 37038291348028031266569551)
  ·
    refine ⟨55557437022042046899854327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37038291348028031266569551 55557437022042046899854327)
    ·
      refine ⟨83336155533063070349781491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55557437022042046899854327 83336155533063070349781491)
      ·
        refine ⟨125004233299594605524672237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83336155533063070349781491 125004233299594605524672237)
        ·
          refine ⟨46876587487347977071752089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125004233299594605524672237 46876587487347977071752089)
          ·
            refine ⟨35157440615510982803814067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46876587487347977071752089 35157440615510982803814067)
            ·
              refine ⟨52736160923266474205721101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35157440615510982803814067 52736160923266474205721101)
              ·
                refine ⟨19776060346224927827145413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52736160923266474205721101 19776060346224927827145413)
                ·
                  refine ⟨3708011314917173967589765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19776060346224927827145413 3708011314917173967589765)
                  ·
                    refine ⟨695252121546970118923081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3708011314917173967589765 695252121546970118923081)
                    ·
                      refine ⟨521439091160227589192311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 695252121546970118923081 521439091160227589192311)
                      ·
                        rfl

theorem cell23_1015499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 4, 4, 2].length) (baseStart_1015499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1015499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1015499 prefixEnd_1015499 := by exact prefixLift 1015499
  have htrace : WordTrace (prefixWord ++ tailWord_1015499) baseStart_1015499 baseEnd_1015499 := by
    simpa [prefixWord, tailWord_1015499, baseEnd_1015499] using wordTrace_append hprefix tailTrace_1015499
  have hstable : (prefixWord ++ tailWord_1015499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015499).length < 2 ^ (prefixWord ++ tailWord_1015499).sum := by decide
  have hdescent : baseEnd_1015499 < baseStart_1015499 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015519 : List Nat := [1, 1, 2, 3, 2, 2, 1, 2, 4, 2, 3]
def baseStart_1015519 : Nat := 118140960795 + 1015519 * 2 ^ 59
def prefixEnd_1015519 : Nat := 4983230072969 + 3 ^ 40 * 1015519 * 2
def baseEnd_1015519 : Nat := 521449360773317510942219

theorem tailTrace_1015519 : CollatzResearch.WordTrace tailWord_1015519 prefixEnd_1015519 521449360773317510942219 := by
  unfold tailWord_1015519
  simp only [CollatzResearch.WordTrace]
  refine ⟨37039020807955574682297611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24692680538637049788198407 37039020807955574682297611)
  ·
    refine ⟨55558531211933362023446417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37039020807955574682297611 55558531211933362023446417)
    ·
      refine ⟨41668898408950021517584813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55558531211933362023446417 41668898408950021517584813)
      ·
        refine ⟨15625836903356258069094305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41668898408950021517584813 15625836903356258069094305)
        ·
          refine ⟨11719377677517193551820729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15625836903356258069094305 11719377677517193551820729)
          ·
            refine ⟨8789533258137895163865547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11719377677517193551820729 8789533258137895163865547)
            ·
              refine ⟨13184299887206842745798321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8789533258137895163865547 13184299887206842745798321)
              ·
                refine ⟨9888224915405132059348741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13184299887206842745798321 9888224915405132059348741)
                ·
                  refine ⟨1854042171638462261127889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9888224915405132059348741 1854042171638462261127889)
                  ·
                    refine ⟨1390531628728846695845917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1854042171638462261127889 1390531628728846695845917)
                    ·
                      refine ⟨521449360773317510942219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1390531628728846695845917 521449360773317510942219)
                      ·
                        rfl

theorem cell23_1015519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 2, 4, 2, 3].length) (baseStart_1015519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1015519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1015519 prefixEnd_1015519 := by exact prefixLift 1015519
  have htrace : WordTrace (prefixWord ++ tailWord_1015519) baseStart_1015519 baseEnd_1015519 := by
    simpa [prefixWord, tailWord_1015519, baseEnd_1015519] using wordTrace_append hprefix tailTrace_1015519
  have hstable : (prefixWord ++ tailWord_1015519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015519).length < 2 ^ (prefixWord ++ tailWord_1015519).sum := by decide
  have hdescent : baseEnd_1015519 < baseStart_1015519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015556 : List Nat := [2, 3, 2, 2, 1, 3, 2, 2, 6]
def baseStart_1015556 : Nat := 118140960795 + 1015556 * 2 ^ 59
def prefixEnd_1015556 : Nat := 4983230072969 + 3 ^ 40 * 1015556 * 2
def baseEnd_1015556 : Nat := 57940928839725985131061

theorem tailTrace_1015556 : CollatzResearch.WordTrace tailWord_1015556 prefixEnd_1015556 57940928839725985131061 := by
  unfold tailWord_1015556
  simp only [CollatzResearch.WordTrace]
  refine ⟨18520185154410765000697261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24693580205881020000929681 18520185154410765000697261)
  ·
    refine ⟨6945069432904036875261473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18520185154410765000697261 6945069432904036875261473)
    ·
      refine ⟨5208802074678027656446105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6945069432904036875261473 5208802074678027656446105)
      ·
        refine ⟨3906601556008520742334579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5208802074678027656446105 3906601556008520742334579)
        ·
          refine ⟨5859902334012781113501869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3906601556008520742334579 5859902334012781113501869)
          ·
            refine ⟨2197463375254792917563201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5859902334012781113501869 2197463375254792917563201)
            ·
              refine ⟨1648097531441094688172401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2197463375254792917563201 1648097531441094688172401)
              ·
                refine ⟨1236073148580821016129301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1648097531441094688172401 1236073148580821016129301)
                ·
                  refine ⟨57940928839725985131061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1236073148580821016129301 57940928839725985131061)
                  ·
                    rfl

theorem cell23_1015556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 2, 2, 6].length) (baseStart_1015556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1015556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1015556 prefixEnd_1015556 := by exact prefixLift 1015556
  have htrace : WordTrace (prefixWord ++ tailWord_1015556) baseStart_1015556 baseEnd_1015556 := by
    simpa [prefixWord, tailWord_1015556, baseEnd_1015556] using wordTrace_append hprefix tailTrace_1015556
  have hstable : (prefixWord ++ tailWord_1015556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015556).length < 2 ^ (prefixWord ++ tailWord_1015556).sum := by decide
  have hdescent : baseEnd_1015556 < baseStart_1015556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015576 : List Nat := [2, 1, 2, 3, 1, 1, 2, 2, 4, 3, 2]
def baseStart_1015576 : Nat := 118140960795 + 1015576 * 2 ^ 59
def prefixEnd_1015576 : Nat := 4983230072969 + 3 ^ 40 * 1015576 * 2
def baseEnd_1015576 : Nat := 521478629170623787929457

theorem tailTrace_1015576 : CollatzResearch.WordTrace tailWord_1015576 prefixEnd_1015576 521478629170623787929457 := by
  unfold tailWord_1015576
  simp only [CollatzResearch.WordTrace]
  refine ⟨18520549884374536708561291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24694066512499382278081721 18520549884374536708561291)
  ·
    refine ⟨27780824826561805062841937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18520549884374536708561291 27780824826561805062841937)
    ·
      refine ⟨20835618619921353797131453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27780824826561805062841937 20835618619921353797131453)
      ·
        refine ⟨7813356982470507673924295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20835618619921353797131453 7813356982470507673924295)
        ·
          refine ⟨11720035473705761510886443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7813356982470507673924295 11720035473705761510886443)
          ·
            refine ⟨17580053210558642266329665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11720035473705761510886443 17580053210558642266329665)
            ·
              refine ⟨13185039907918981699747249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17580053210558642266329665 13185039907918981699747249)
              ·
                refine ⟨9888779930939236274810437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13185039907918981699747249 9888779930939236274810437)
                ·
                  refine ⟨1854146237051106801526957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9888779930939236274810437 1854146237051106801526957)
                  ·
                    refine ⟨695304838894165050572609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1854146237051106801526957 695304838894165050572609)
                    ·
                      refine ⟨521478629170623787929457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 695304838894165050572609 521478629170623787929457)
                      ·
                        rfl

theorem cell23_1015576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 2, 4, 3, 2].length) (baseStart_1015576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1015576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1015576 prefixEnd_1015576 := by exact prefixLift 1015576
  have htrace : WordTrace (prefixWord ++ tailWord_1015576) baseStart_1015576 baseEnd_1015576 := by
    simpa [prefixWord, tailWord_1015576, baseEnd_1015576] using wordTrace_append hprefix tailTrace_1015576
  have hstable : (prefixWord ++ tailWord_1015576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015576).length < 2 ^ (prefixWord ++ tailWord_1015576).sum := by decide
  have hdescent : baseEnd_1015576 < baseStart_1015576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015586 : List Nat := [3, 3, 1, 1, 2, 1, 2, 4, 1, 5]
def baseStart_1015586 : Nat := 118140960795 + 1015586 * 2 ^ 59
def prefixEnd_1015586 : Nat := 4983230072969 + 3 ^ 40 * 1015586 * 2
def baseEnd_1015586 : Nat := 173827921325722916268137

theorem tailTrace_1015586 : CollatzResearch.WordTrace tailWord_1015586 prefixEnd_1015586 173827921325722916268137 := by
  unfold tailWord_1015586
  simp only [CollatzResearch.WordTrace]
  refine ⟨9260366124678211281246653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24694309665808563416657741 9260366124678211281246653)
  ·
    refine ⟨3472637296754329230467495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9260366124678211281246653 3472637296754329230467495)
    ·
      refine ⟨5208955945131493845701243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3472637296754329230467495 5208955945131493845701243)
      ·
        refine ⟨7813433917697240768551865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5208955945131493845701243 7813433917697240768551865)
        ·
          refine ⟨5860075438272930576413899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7813433917697240768551865 5860075438272930576413899)
          ·
            refine ⟨8790113157409395864620849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5860075438272930576413899 8790113157409395864620849)
            ·
              refine ⟨6592584868057046898465637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8790113157409395864620849 6592584868057046898465637)
              ·
                refine ⟨1236109662760696293462307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6592584868057046898465637 1236109662760696293462307)
                ·
                  refine ⟨1854164494141044440193461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1236109662760696293462307 1854164494141044440193461)
                  ·
                    refine ⟨173827921325722916268137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1854164494141044440193461 173827921325722916268137)
                    ·
                      rfl

theorem cell23_1015586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 4, 1, 5].length) (baseStart_1015586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1015586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1015586 prefixEnd_1015586 := by exact prefixLift 1015586
  have htrace : WordTrace (prefixWord ++ tailWord_1015586) baseStart_1015586 baseEnd_1015586 := by
    simpa [prefixWord, tailWord_1015586, baseEnd_1015586] using wordTrace_append hprefix tailTrace_1015586
  have hstable : (prefixWord ++ tailWord_1015586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015586).length < 2 ^ (prefixWord ++ tailWord_1015586).sum := by decide
  have hdescent : baseEnd_1015586 < baseStart_1015586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015599 : List Nat := [1, 1, 2, 1, 2, 1, 2, 3, 6, 4]
def baseStart_1015599 : Nat := 118140960795 + 1015599 * 2 ^ 59
def prefixEnd_1015599 : Nat := 4983230072969 + 3 ^ 40 * 1015599 * 2
def baseEnd_1015599 : Nat := 173830146408559065980617

theorem tailTrace_1015599 : CollatzResearch.WordTrace tailWord_1015599 prefixEnd_1015599 173830146408559065980617 := by
  unfold tailWord_1015599
  simp only [CollatzResearch.WordTrace]
  refine ⟨37041938647665748345209851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24694625765110498896806567 37041938647665748345209851)
  ·
    refine ⟨55562907971498622517814777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37041938647665748345209851 55562907971498622517814777)
    ·
      refine ⟨41672180978623966888361083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55562907971498622517814777 41672180978623966888361083)
      ·
        refine ⟨62508271467935950332541625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41672180978623966888361083 62508271467935950332541625)
        ·
          refine ⟨46881203600951962749406219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62508271467935950332541625 46881203600951962749406219)
          ·
            refine ⟨70321805401427944124109329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46881203600951962749406219 70321805401427944124109329)
            ·
              refine ⟨52741354051070958093081997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70321805401427944124109329 52741354051070958093081997)
              ·
                refine ⟨19778007769151609284905749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52741354051070958093081997 19778007769151609284905749)
                ·
                  refine ⟨927094114178981685229957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 19778007769151609284905749 927094114178981685229957)
                  ·
                    refine ⟨173830146408559065980617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 927094114178981685229957 173830146408559065980617)
                    ·
                      rfl

theorem cell23_1015599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 6, 4].length) (baseStart_1015599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1015599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1015599 prefixEnd_1015599 := by exact prefixLift 1015599
  have htrace : WordTrace (prefixWord ++ tailWord_1015599) baseStart_1015599 baseEnd_1015599 := by
    simpa [prefixWord, tailWord_1015599, baseEnd_1015599] using wordTrace_append hprefix tailTrace_1015599
  have hstable : (prefixWord ++ tailWord_1015599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015599).length < 2 ^ (prefixWord ++ tailWord_1015599).sum := by decide
  have hdescent : baseEnd_1015599 < baseStart_1015599 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015623 : List Nat := [1, 1, 4, 1, 2, 1, 3, 3, 3, 2, 2]
def baseStart_1015623 : Nat := 118140960795 + 1015623 * 2 ^ 59
def prefixEnd_1015623 : Nat := 4983230072969 + 3 ^ 40 * 1015623 * 2
def baseEnd_1015623 : Nat := 521502762761385104041741

theorem tailTrace_1015623 : CollatzResearch.WordTrace tailWord_1015623 prefixEnd_1015623 521502762761385104041741 := by
  unfold tailWord_1015623
  simp only [CollatzResearch.WordTrace]
  refine ⟨37042813999578800444083523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24695209333052533629389015 37042813999578800444083523)
  ·
    refine ⟨55564220999368200666125285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37042813999578800444083523 55564220999368200666125285)
    ·
      refine ⟨10418291437381537624898491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55564220999368200666125285 10418291437381537624898491)
      ·
        refine ⟨15627437156072306437347737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10418291437381537624898491 15627437156072306437347737)
        ·
          refine ⟨11720577867054229828010803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15627437156072306437347737 11720577867054229828010803)
          ·
            refine ⟨17580866800581344742016205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11720577867054229828010803 17580866800581344742016205)
            ·
              refine ⟨6592825050218004278256077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17580866800581344742016205 6592825050218004278256077)
              ·
                refine ⟨2472309393831751604346029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6592825050218004278256077 2472309393831751604346029)
                ·
                  refine ⟨927116022686906851629761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2472309393831751604346029 927116022686906851629761)
                  ·
                    refine ⟨695337017015180138722321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 927116022686906851629761 695337017015180138722321)
                    ·
                      refine ⟨521502762761385104041741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 695337017015180138722321 521502762761385104041741)
                      ·
                        rfl

theorem cell23_1015623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 3, 3, 2, 2].length) (baseStart_1015623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1015623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1015623 prefixEnd_1015623 := by exact prefixLift 1015623
  have htrace : WordTrace (prefixWord ++ tailWord_1015623) baseStart_1015623 baseEnd_1015623 := by
    simpa [prefixWord, tailWord_1015623, baseEnd_1015623] using wordTrace_append hprefix tailTrace_1015623
  have hstable : (prefixWord ++ tailWord_1015623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015623).length < 2 ^ (prefixWord ++ tailWord_1015623).sum := by decide
  have hdescent : baseEnd_1015623 < baseStart_1015623 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015636 : List Nat := [2, 4, 1, 1, 3, 2, 1, 1, 1, 1, 6]
def baseStart_1015636 : Nat := 118140960795 + 1015636 * 2 ^ 59
def prefixEnd_1015636 : Nat := 4983230072969 + 3 ^ 40 * 1015636 * 2
def baseEnd_1015636 : Nat := 521509438009893553179181

theorem tailTrace_1015636 : CollatzResearch.WordTrace tailWord_1015636 prefixEnd_1015636 521509438009893553179181 := by
  unfold tailWord_1015636
  simp only [CollatzResearch.WordTrace]
  refine ⟨18521644074265851832153381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24695525432354469109537841 18521644074265851832153381)
  ·
    refine ⟨3472808263924847218528759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18521644074265851832153381 3472808263924847218528759)
    ·
      refine ⟨5209212395887270827793139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3472808263924847218528759 5209212395887270827793139)
      ·
        refine ⟨7813818593830906241689709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5209212395887270827793139 7813818593830906241689709)
        ·
          refine ⟨2930181972686589840633641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7813818593830906241689709 2930181972686589840633641)
          ·
            refine ⟨2197636479514942380475231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2930181972686589840633641 2197636479514942380475231)
            ·
              refine ⟨3296454719272413570712847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2197636479514942380475231 3296454719272413570712847)
              ·
                refine ⟨4944682078908620356069271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3296454719272413570712847 4944682078908620356069271)
                ·
                  refine ⟨7417023118362930534103907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4944682078908620356069271 7417023118362930534103907)
                  ·
                    refine ⟨11125534677544395801155861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7417023118362930534103907 11125534677544395801155861)
                    ·
                      refine ⟨521509438009893553179181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11125534677544395801155861 521509438009893553179181)
                      ·
                        rfl

theorem cell23_1015636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 1, 1, 1, 6].length) (baseStart_1015636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1015636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1015636 prefixEnd_1015636 := by exact prefixLift 1015636
  have htrace : WordTrace (prefixWord ++ tailWord_1015636) baseStart_1015636 baseEnd_1015636 := by
    simpa [prefixWord, tailWord_1015636, baseEnd_1015636] using wordTrace_append hprefix tailTrace_1015636
  have hstable : (prefixWord ++ tailWord_1015636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015636).length < 2 ^ (prefixWord ++ tailWord_1015636).sum := by decide
  have hdescent : baseEnd_1015636 < baseStart_1015636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015656 : List Nat := [2, 1, 4, 2, 1, 1, 2, 1, 3, 3, 3]
def baseStart_1015656 : Nat := 118140960795 + 1015656 * 2 ^ 59
def prefixEnd_1015656 : Nat := 4983230072969 + 3 ^ 40 * 1015656 * 2
def baseEnd_1015656 : Nat := 521519707622983474929089

theorem tailTrace_1015656 : CollatzResearch.WordTrace tailWord_1015656 prefixEnd_1015656 521519707622983474929089 := by
  unfold tailWord_1015656
  simp only [CollatzResearch.WordTrace]
  refine ⟨18522008804229623540017411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24696011738972831386689881 18522008804229623540017411)
  ·
    refine ⟨27783013206344435310026117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18522008804229623540017411 27783013206344435310026117)
    ·
      refine ⟨5209314976189581620629897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27783013206344435310026117 5209314976189581620629897)
      ·
        refine ⟨3906986232142186215472423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5209314976189581620629897 3906986232142186215472423)
        ·
          refine ⟨5860479348213279323208635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3906986232142186215472423 5860479348213279323208635)
          ·
            refine ⟨8790719022319918984812953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5860479348213279323208635 8790719022319918984812953)
            ·
              refine ⟨6593039266739939238609715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8790719022319918984812953 6593039266739939238609715)
              ·
                refine ⟨9889558900109908857914573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6593039266739939238609715 9889558900109908857914573)
                ·
                  refine ⟨3708584587541215821717965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9889558900109908857914573 3708584587541215821717965)
                  ·
                    refine ⟨1390719220327955933144237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3708584587541215821717965 1390719220327955933144237)
                    ·
                      refine ⟨521519707622983474929089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1390719220327955933144237 521519707622983474929089)
                      ·
                        rfl

theorem cell23_1015656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 1, 3, 3, 3].length) (baseStart_1015656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1015656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1015656 prefixEnd_1015656 := by exact prefixLift 1015656
  have htrace : WordTrace (prefixWord ++ tailWord_1015656) baseStart_1015656 baseEnd_1015656 := by
    simpa [prefixWord, tailWord_1015656, baseEnd_1015656] using wordTrace_append hprefix tailTrace_1015656
  have hstable : (prefixWord ++ tailWord_1015656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015656).length < 2 ^ (prefixWord ++ tailWord_1015656).sum := by decide
  have hdescent : baseEnd_1015656 < baseStart_1015656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015673 : List Nat := [1, 2, 1, 3, 2, 2, 2, 4, 2, 1, 3]
def baseStart_1015673 : Nat := 118140960795 + 1015673 * 2 ^ 59
def prefixEnd_1015673 : Nat := 4983230072969 + 3 ^ 40 * 1015673 * 2
def baseEnd_1015673 : Nat := 521528436794109908416511

theorem tailTrace_1015673 : CollatzResearch.WordTrace tailWord_1015673 prefixEnd_1015673 521528436794109908416511 := by
  unfold tailWord_1015673
  simp only [CollatzResearch.WordTrace]
  refine ⟨37044637649397658983403673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24696425099598439322269115 37044637649397658983403673)
  ·
    refine ⟨27783478237048244237552755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37044637649397658983403673 27783478237048244237552755)
    ·
      refine ⟨41675217355572366356329133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27783478237048244237552755 41675217355572366356329133)
      ·
        refine ⟨15628206508339637383623425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41675217355572366356329133 15628206508339637383623425)
        ·
          refine ⟨11721154881254728037717569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15628206508339637383623425 11721154881254728037717569)
          ·
            refine ⟨8790866160941046028288177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11721154881254728037717569 8790866160941046028288177)
            ·
              refine ⟨6593149620705784521216133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8790866160941046028288177 6593149620705784521216133)
              ·
                refine ⟨1236215553882334597728025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6593149620705784521216133 1236215553882334597728025)
                ·
                  refine ⟨927161665411750948296019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1236215553882334597728025 927161665411750948296019)
                  ·
                    refine ⟨1390742498117626422444029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 927161665411750948296019 1390742498117626422444029)
                    ·
                      refine ⟨521528436794109908416511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1390742498117626422444029 521528436794109908416511)
                      ·
                        rfl

theorem cell23_1015673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 4, 2, 1, 3].length) (baseStart_1015673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1015673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1015673 prefixEnd_1015673 := by exact prefixLift 1015673
  have htrace : WordTrace (prefixWord ++ tailWord_1015673) baseStart_1015673 baseEnd_1015673 := by
    simpa [prefixWord, tailWord_1015673, baseEnd_1015673] using wordTrace_append hprefix tailTrace_1015673
  have hstable : (prefixWord ++ tailWord_1015673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015673).length < 2 ^ (prefixWord ++ tailWord_1015673).sum := by decide
  have hdescent : baseEnd_1015673 < baseStart_1015673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015679 : List Nat := [1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 4]
def baseStart_1015679 : Nat := 118140960795 + 1015679 * 2 ^ 59
def prefixEnd_1015679 : Nat := 4983230072969 + 3 ^ 40 * 1015679 * 2
def baseEnd_1015679 : Nat := 521531517678036884941483

theorem tailTrace_1015679 : CollatzResearch.WordTrace tailWord_1015679 prefixEnd_1015679 521531517678036884941483 := by
  unfold tailWord_1015679
  simp only [CollatzResearch.WordTrace]
  refine ⟨37044856487375922008122091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24696570991583948005414727 37044856487375922008122091)
  ·
    refine ⟨55567284731063883012183137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37044856487375922008122091 55567284731063883012183137)
    ·
      refine ⟨41675463548297912259137353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55567284731063883012183137 41675463548297912259137353)
      ·
        refine ⟨31256597661223434194353015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41675463548297912259137353 31256597661223434194353015)
        ·
          refine ⟨46884896491835151291529523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31256597661223434194353015 46884896491835151291529523)
          ·
            refine ⟨70327344737752726937294285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46884896491835151291529523 70327344737752726937294285)
            ·
              refine ⟨26372754276657272601485357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70327344737752726937294285 26372754276657272601485357)
              ·
                refine ⟨9889782853746477225557009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26372754276657272601485357 9889782853746477225557009)
                ·
                  refine ⟨7417337140309857919167757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9889782853746477225557009 7417337140309857919167757)
                  ·
                    refine ⟨2781501427616196719687909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7417337140309857919167757 2781501427616196719687909)
                    ·
                      refine ⟨521531517678036884941483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2781501427616196719687909 521531517678036884941483)
                      ·
                        rfl

theorem cell23_1015679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 4].length) (baseStart_1015679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1015679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1015679 prefixEnd_1015679 := by exact prefixLift 1015679
  have htrace : WordTrace (prefixWord ++ tailWord_1015679) baseStart_1015679 baseEnd_1015679 := by
    simpa [prefixWord, tailWord_1015679, baseEnd_1015679] using wordTrace_append hprefix tailTrace_1015679
  have hstable : (prefixWord ++ tailWord_1015679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015679).length < 2 ^ (prefixWord ++ tailWord_1015679).sum := by decide
  have hdescent : baseEnd_1015679 < baseStart_1015679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015689 : List Nat := [1, 2, 1, 1, 5, 1, 2, 1, 1, 8]
def baseStart_1015689 : Nat := 118140960795 + 1015689 * 2 ^ 59
def prefixEnd_1015689 : Nat := 4983230072969 + 3 ^ 40 * 1015689 * 2
def baseEnd_1015689 : Nat := 173845550828193948605479

theorem tailTrace_1015689 : CollatzResearch.WordTrace tailWord_1015689 prefixEnd_1015689 173845550828193948605479 := by
  unfold tailWord_1015689
  simp only [CollatzResearch.WordTrace]
  refine ⟨37045221217339693715986121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24696814144893129143990747 37045221217339693715986121)
  ·
    refine ⟨27783915913004770286989591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37045221217339693715986121 27783915913004770286989591)
    ·
      refine ⟨41675873869507155430484387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27783915913004770286989591 41675873869507155430484387)
      ·
        refine ⟨62513810804260733145726581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41675873869507155430484387 62513810804260733145726581)
        ·
          refine ⟨5860669762899443732411867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62513810804260733145726581 5860669762899443732411867)
          ·
            refine ⟨8791004644349165598617801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5860669762899443732411867 8791004644349165598617801)
            ·
              refine ⟨6593253483261874198963351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8791004644349165598617801 6593253483261874198963351)
              ·
                refine ⟨9889880224892811298445027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6593253483261874198963351 9889880224892811298445027)
                ·
                  refine ⟨14834820337339216947667541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9889880224892811298445027 14834820337339216947667541)
                  ·
                    refine ⟨173845550828193948605479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 14834820337339216947667541 173845550828193948605479)
                    ·
                      rfl

theorem cell23_1015689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 1, 1, 8].length) (baseStart_1015689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1015689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1015689 prefixEnd_1015689 := by exact prefixLift 1015689
  have htrace : WordTrace (prefixWord ++ tailWord_1015689) baseStart_1015689 baseEnd_1015689 := by
    simpa [prefixWord, tailWord_1015689, baseEnd_1015689] using wordTrace_append hprefix tailTrace_1015689
  have hstable : (prefixWord ++ tailWord_1015689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015689).length < 2 ^ (prefixWord ++ tailWord_1015689).sum := by decide
  have hdescent : baseEnd_1015689 < baseStart_1015689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015694 : List Nat := [4, 1, 1, 5, 2, 1, 1, 2, 1, 2, 3]
def baseStart_1015694 : Nat := 118140960795 + 1015694 * 2 ^ 59
def prefixEnd_1015694 : Nat := 4983230072969 + 3 ^ 40 * 1015694 * 2
def baseEnd_1015694 : Nat := 521539219887854326253915

theorem tailTrace_1015694 : CollatzResearch.WordTrace tailWord_1015694 prefixEnd_1015694 521539219887854326253915 := by
  unfold tailWord_1015694
  simp only [CollatzResearch.WordTrace]
  refine ⟨4630675447790197446239767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24696935721547719713278757 4630675447790197446239767)
  ·
    refine ⟨6946013171685296169359651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4630675447790197446239767 6946013171685296169359651)
    ·
      refine ⟨10419019757527944254039477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6946013171685296169359651 10419019757527944254039477)
      ·
        refine ⟨976783102268244773816201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10419019757527944254039477 976783102268244773816201)
        ·
          refine ⟨732587326701183580362151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 976783102268244773816201 732587326701183580362151)
          ·
            refine ⟨1098880990051775370543227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 732587326701183580362151 1098880990051775370543227)
            ·
              refine ⟨1648321485077663055814841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1098880990051775370543227 1648321485077663055814841)
              ·
                refine ⟨1236241113808247291861131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1648321485077663055814841 1236241113808247291861131)
                ·
                  refine ⟨1854361670712370937791697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1236241113808247291861131 1854361670712370937791697)
                  ·
                    refine ⟨1390771253034278203343773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1854361670712370937791697 1390771253034278203343773)
                    ·
                      refine ⟨521539219887854326253915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1390771253034278203343773 521539219887854326253915)
                      ·
                        rfl

theorem cell23_1015694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_1015694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1015694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1015694 prefixEnd_1015694 := by exact prefixLift 1015694
  have htrace : WordTrace (prefixWord ++ tailWord_1015694) baseStart_1015694 baseEnd_1015694 := by
    simpa [prefixWord, tailWord_1015694, baseEnd_1015694] using wordTrace_append hprefix tailTrace_1015694
  have hstable : (prefixWord ++ tailWord_1015694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015694).length < 2 ^ (prefixWord ++ tailWord_1015694).sum := by decide
  have hdescent : baseEnd_1015694 < baseStart_1015694 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015700 : List Nat := [2, 4, 2, 1, 1, 3, 1, 1, 3, 3, 2]
def baseStart_1015700 : Nat := 118140960795 + 1015700 * 2 ^ 59
def prefixEnd_1015700 : Nat := 4983230072969 + 3 ^ 40 * 1015700 * 2
def baseEnd_1015700 : Nat := 521542300771781302778887

theorem tailTrace_1015700 : CollatzResearch.WordTrace tailWord_1015700 prefixEnd_1015700 521542300771781302778887 := by
  unfold tailWord_1015700
  simp only [CollatzResearch.WordTrace]
  refine ⟨18522811210149921297318277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24697081613533228396424369 18522811210149921297318277)
  ·
    refine ⟨3473027101903110243247177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18522811210149921297318277 3473027101903110243247177)
    ·
      refine ⟨2604770326427332682435383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3473027101903110243247177 2604770326427332682435383)
      ·
        refine ⟨3907155489640999023653075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2604770326427332682435383 3907155489640999023653075)
        ·
          refine ⟨5860733234461498535479613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3907155489640999023653075 5860733234461498535479613)
          ·
            refine ⟨2197774962923061950804855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5860733234461498535479613 2197774962923061950804855)
            ·
              refine ⟨3296662444384592926207283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2197774962923061950804855 3296662444384592926207283)
              ·
                refine ⟨4944993666576889389310925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3296662444384592926207283 4944993666576889389310925)
                ·
                  refine ⟨1854372624966333520991597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4944993666576889389310925 1854372624966333520991597)
                  ·
                    refine ⟨695389734362375070371849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1854372624966333520991597 695389734362375070371849)
                    ·
                      refine ⟨521542300771781302778887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 695389734362375070371849 521542300771781302778887)
                      ·
                        rfl

theorem cell23_1015700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 1, 3, 3, 2].length) (baseStart_1015700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1015700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1015700 prefixEnd_1015700 := by exact prefixLift 1015700
  have htrace : WordTrace (prefixWord ++ tailWord_1015700) baseStart_1015700 baseEnd_1015700 := by
    simpa [prefixWord, tailWord_1015700, baseEnd_1015700] using wordTrace_append hprefix tailTrace_1015700
  have hstable : (prefixWord ++ tailWord_1015700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015700).length < 2 ^ (prefixWord ++ tailWord_1015700).sum := by decide
  have hdescent : baseEnd_1015700 < baseStart_1015700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015716 : List Nat := [2, 3, 1, 2, 1, 3, 2, 1, 2, 1, 5]
def baseStart_1015716 : Nat := 118140960795 + 1015716 * 2 ^ 59
def prefixEnd_1015716 : Nat := 4983230072969 + 3 ^ 40 * 1015716 * 2
def baseEnd_1015716 : Nat := 521550516462253240178813

theorem tailTrace_1015716 : CollatzResearch.WordTrace tailWord_1015716 prefixEnd_1015716 521550516462253240178813 := by
  unfold tailWord_1015716
  simp only [CollatzResearch.WordTrace]
  refine ⟨18523102994120938663609501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24697470658827918218146001 18523102994120938663609501)
  ·
    refine ⟨6946163622795351998853563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18523102994120938663609501 6946163622795351998853563)
    ·
      refine ⟨10419245434193027998280345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6946163622795351998853563 10419245434193027998280345)
      ·
        refine ⟨7814434075644770998710259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10419245434193027998280345 7814434075644770998710259)
        ·
          refine ⟨11721651113467156498065389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7814434075644770998710259 11721651113467156498065389)
          ·
            refine ⟨4395619167550183686774521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11721651113467156498065389 4395619167550183686774521)
            ·
              refine ⟨3296714375662637765080891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4395619167550183686774521 3296714375662637765080891)
              ·
                refine ⟨4945071563493956647621337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3296714375662637765080891 4945071563493956647621337)
                ·
                  refine ⟨3708803672620467485716003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4945071563493956647621337 3708803672620467485716003)
                  ·
                    refine ⟨5563205508930701228574005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3708803672620467485716003 5563205508930701228574005)
                    ·
                      refine ⟨521550516462253240178813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5563205508930701228574005 521550516462253240178813)
                      ·
                        rfl

theorem cell23_1015716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 1, 2, 1, 5].length) (baseStart_1015716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1015716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1015716 prefixEnd_1015716 := by exact prefixLift 1015716
  have htrace : WordTrace (prefixWord ++ tailWord_1015716) baseStart_1015716 baseEnd_1015716 := by
    simpa [prefixWord, tailWord_1015716, baseEnd_1015716] using wordTrace_append hprefix tailTrace_1015716
  have hstable : (prefixWord ++ tailWord_1015716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015716).length < 2 ^ (prefixWord ++ tailWord_1015716).sum := by decide
  have hdescent : baseEnd_1015716 < baseStart_1015716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015770 : List Nat := [3, 1, 1, 2, 5, 1, 2, 3, 5]
def baseStart_1015770 : Nat := 118140960795 + 1015770 * 2 ^ 59
def prefixEnd_1015770 : Nat := 4983230072969 + 3 ^ 40 * 1015770 * 2
def baseEnd_1015770 : Nat := 57953138268621780989285

theorem tailTrace_1015770 : CollatzResearch.WordTrace tailWord_1015770 prefixEnd_1015770 57953138268621780989285 := by
  unfold tailWord_1015770
  simp only [CollatzResearch.WordTrace]
  refine ⟨9262043882511561137421191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24698783686697496366456509 9262043882511561137421191)
  ·
    refine ⟨13893065823767341706131787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9262043882511561137421191 13893065823767341706131787)
    ·
      refine ⟨20839598735651012559197681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13893065823767341706131787 20839598735651012559197681)
      ·
        refine ⟨15629699051738259419398261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20839598735651012559197681 15629699051738259419398261)
        ·
          refine ⟨1465284286100461820568587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15629699051738259419398261 1465284286100461820568587)
          ·
            refine ⟨2197926429150692730852881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1465284286100461820568587 2197926429150692730852881)
            ·
              refine ⟨1648444821863019548139661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2197926429150692730852881 1648444821863019548139661)
              ·
                refine ⟨618166808198632330552373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1648444821863019548139661 618166808198632330552373)
                ·
                  refine ⟨57953138268621780989285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 618166808198632330552373 57953138268621780989285)
                  ·
                    rfl

theorem cell23_1015770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 2, 3, 5].length) (baseStart_1015770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1015770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1015770 prefixEnd_1015770 := by exact prefixLift 1015770
  have htrace : WordTrace (prefixWord ++ tailWord_1015770) baseStart_1015770 baseEnd_1015770 := by
    simpa [prefixWord, tailWord_1015770, baseEnd_1015770] using wordTrace_append hprefix tailTrace_1015770
  have hstable : (prefixWord ++ tailWord_1015770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015770).length < 2 ^ (prefixWord ++ tailWord_1015770).sum := by decide
  have hdescent : baseEnd_1015770 < baseStart_1015770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015803 : List Nat := [1, 1, 1, 1, 1, 3, 6, 1, 2, 4, 2]
def baseStart_1015803 : Nat := 118140960795 + 1015803 * 2 ^ 59
def prefixEnd_1015803 : Nat := 4983230072969 + 3 ^ 40 * 1015803 * 2
def baseEnd_1015803 : Nat := 521595189279194399790913

theorem tailTrace_1015803 : CollatzResearch.WordTrace tailWord_1015803 prefixEnd_1015803 521595189279194399790913 := by
  unfold tailWord_1015803
  simp only [CollatzResearch.WordTrace]
  refine ⟨37049379138926691185636063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24699586092617794123757375 37049379138926691185636063)
  ·
    refine ⟨55574068708390036778454095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37049379138926691185636063 55574068708390036778454095)
    ·
      refine ⟨83361103062585055167681143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55574068708390036778454095 83361103062585055167681143)
      ·
        refine ⟨125041654593877582751521715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83361103062585055167681143 125041654593877582751521715)
        ·
          refine ⟨187562481890816374127282573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125041654593877582751521715 187562481890816374127282573)
          ·
            refine ⟨70335930709056140297730965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 187562481890816374127282573 70335930709056140297730965)
            ·
              refine ⟨3296996751987006576456139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 70335930709056140297730965 3296996751987006576456139)
              ·
                refine ⟨4945495127980509864684209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3296996751987006576456139 4945495127980509864684209)
                ·
                  refine ⟨3709121345985382398513157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4945495127980509864684209 3709121345985382398513157)
                  ·
                    refine ⟨695460252372259199721217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3709121345985382398513157 695460252372259199721217)
                    ·
                      refine ⟨521595189279194399790913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 695460252372259199721217 521595189279194399790913)
                      ·
                        rfl

theorem cell23_1015803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 1, 2, 4, 2].length) (baseStart_1015803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1015803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1015803 prefixEnd_1015803 := by exact prefixLift 1015803
  have htrace : WordTrace (prefixWord ++ tailWord_1015803) baseStart_1015803 baseEnd_1015803 := by
    simpa [prefixWord, tailWord_1015803, baseEnd_1015803] using wordTrace_append hprefix tailTrace_1015803
  have hstable : (prefixWord ++ tailWord_1015803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015803).length < 2 ^ (prefixWord ++ tailWord_1015803).sum := by decide
  have hdescent : baseEnd_1015803 < baseStart_1015803 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015813 : List Nat := [1, 3, 1, 1, 2, 4, 2, 2, 3, 4]
def baseStart_1015813 : Nat := 118140960795 + 1015813 * 2 ^ 59
def prefixEnd_1015813 : Nat := 4983230072969 + 3 ^ 40 * 1015813 * 2
def baseEnd_1015813 : Nat := 173866774695246453555289

theorem tailTrace_1015813 : CollatzResearch.WordTrace tailWord_1015813 prefixEnd_1015813 173866774695246453555289 := by
  unfold tailWord_1015813
  simp only [CollatzResearch.WordTrace]
  refine ⟨37049743868890462893500093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24699829245926975262333395 37049743868890462893500093)
  ·
    refine ⟨13893653950833923585062535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37049743868890462893500093 13893653950833923585062535)
    ·
      refine ⟨20840480926250885377593803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13893653950833923585062535 20840480926250885377593803)
      ·
        refine ⟨31260721389376328066390705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20840480926250885377593803 31260721389376328066390705)
        ·
          refine ⟨23445541042032246049793029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31260721389376328066390705 23445541042032246049793029)
          ·
            refine ⟨4396038945381046134336193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23445541042032246049793029 4396038945381046134336193)
            ·
              refine ⟨3297029209035784600752145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4396038945381046134336193 3297029209035784600752145)
              ·
                refine ⟨2472771906776838450564109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3297029209035784600752145 2472771906776838450564109)
                ·
                  refine ⟨927289465041314418961541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2472771906776838450564109 927289465041314418961541)
                  ·
                    refine ⟨173866774695246453555289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 927289465041314418961541 173866774695246453555289)
                    ·
                      rfl

theorem cell23_1015813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 2, 3, 4].length) (baseStart_1015813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1015813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1015813 prefixEnd_1015813 := by exact prefixLift 1015813
  have htrace : WordTrace (prefixWord ++ tailWord_1015813) baseStart_1015813 baseEnd_1015813 := by
    simpa [prefixWord, tailWord_1015813, baseEnd_1015813] using wordTrace_append hprefix tailTrace_1015813
  have hstable : (prefixWord ++ tailWord_1015813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015813).length < 2 ^ (prefixWord ++ tailWord_1015813).sum := by decide
  have hdescent : baseEnd_1015813 < baseStart_1015813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015816 : List Nat := [2, 1, 3, 2, 1, 2, 1, 1, 2, 4, 4]
def baseStart_1015816 : Nat := 118140960795 + 1015816 * 2 ^ 59
def prefixEnd_1015816 : Nat := 4983230072969 + 3 ^ 40 * 1015816 * 2
def baseEnd_1015816 : Nat := 521601864527702848928353

theorem tailTrace_1015816 : CollatzResearch.WordTrace tailWord_1015816 prefixEnd_1015816 521601864527702848928353 := by
  unfold tailWord_1015816
  simp only [CollatzResearch.WordTrace]
  refine ⟨18524926643939797202929651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24699902191919729603906201 18524926643939797202929651)
  ·
    refine ⟨27787389965909695804394477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18524926643939797202929651 27787389965909695804394477)
    ·
      refine ⟨10420271237216135926647929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27787389965909695804394477 10420271237216135926647929)
      ·
        refine ⟨7815203427912101944985947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10420271237216135926647929 7815203427912101944985947)
        ·
          refine ⟨11722805141868152917478921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7815203427912101944985947 11722805141868152917478921)
          ·
            refine ⟨8792103856401114688109191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11722805141868152917478921 8792103856401114688109191)
            ·
              refine ⟨13188155784601672032163787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8792103856401114688109191 13188155784601672032163787)
              ·
                refine ⟨19782233676902508048245681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13188155784601672032163787 19782233676902508048245681)
                ·
                  refine ⟨14836675257676881036184261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19782233676902508048245681 14836675257676881036184261)
                  ·
                    refine ⟨2781876610814415194284549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14836675257676881036184261 2781876610814415194284549)
                    ·
                      refine ⟨521601864527702848928353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2781876610814415194284549 521601864527702848928353)
                      ·
                        rfl

theorem cell23_1015816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 2, 4, 4].length) (baseStart_1015816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1015816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1015816 prefixEnd_1015816 := by exact prefixLift 1015816
  have htrace : WordTrace (prefixWord ++ tailWord_1015816) baseStart_1015816 baseEnd_1015816 := by
    simpa [prefixWord, tailWord_1015816, baseEnd_1015816] using wordTrace_append hprefix tailTrace_1015816
  have hstable : (prefixWord ++ tailWord_1015816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015816).length < 2 ^ (prefixWord ++ tailWord_1015816).sum := by decide
  have hdescent : baseEnd_1015816 < baseStart_1015816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015821 : List Nat := [1, 7, 1, 2, 1, 2, 1, 3, 5]
def baseStart_1015821 : Nat := 118140960795 + 1015821 * 2 ^ 59
def prefixEnd_1015821 : Nat := 4983230072969 + 3 ^ 40 * 1015821 * 2
def baseEnd_1015821 : Nat := 57956047992330592151759

theorem tailTrace_1015821 : CollatzResearch.WordTrace tailWord_1015821 prefixEnd_1015821 57956047992330592151759 := by
  unfold tailWord_1015821
  simp only [CollatzResearch.WordTrace]
  refine ⟨37050035652861480259791317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24700023768574320173194211 37050035652861480259791317)
  ·
    refine ⟨868360210613940943588859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 37050035652861480259791317 868360210613940943588859)
    ·
      refine ⟨1302540315920911415383289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 868360210613940943588859 1302540315920911415383289)
      ·
        refine ⟨976905236940683561537467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1302540315920911415383289 976905236940683561537467)
        ·
          refine ⟨1465357855411025342306201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 976905236940683561537467 1465357855411025342306201)
          ·
            refine ⟨1099018391558269006729651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1465357855411025342306201 1099018391558269006729651)
            ·
              refine ⟨1648527587337403510094477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1099018391558269006729651 1648527587337403510094477)
              ·
                refine ⟨618197845251526316285429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1648527587337403510094477 618197845251526316285429)
                ·
                  refine ⟨57956047992330592151759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 618197845251526316285429 57956047992330592151759)
                  ·
                    rfl

theorem cell23_1015821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 1, 3, 5].length) (baseStart_1015821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1015821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1015821 prefixEnd_1015821 := by exact prefixLift 1015821
  have htrace : WordTrace (prefixWord ++ tailWord_1015821) baseStart_1015821 baseEnd_1015821 := by
    simpa [prefixWord, tailWord_1015821, baseEnd_1015821] using wordTrace_append hprefix tailTrace_1015821
  have hstable : (prefixWord ++ tailWord_1015821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015821).length < 2 ^ (prefixWord ++ tailWord_1015821).sum := by decide
  have hdescent : baseEnd_1015821 < baseStart_1015821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015863 : List Nat := [1, 1, 3, 1, 2, 2, 2, 1, 3, 5, 2]
def baseStart_1015863 : Nat := 118140960795 + 1015863 * 2 ^ 59
def prefixEnd_1015863 : Nat := 4983230072969 + 3 ^ 40 * 1015863 * 2
def baseEnd_1015863 : Nat := 521625998118464165040637

theorem tailTrace_1015863 : CollatzResearch.WordTrace tailWord_1015863 prefixEnd_1015863 521625998118464165040637 := by
  unfold tailWord_1015863
  simp only [CollatzResearch.WordTrace]
  refine ⟨37051567518709321432820243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24701045012472880955213495 37051567518709321432820243)
  ·
    refine ⟨55577351278063982149230365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37051567518709321432820243 55577351278063982149230365)
    ·
      refine ⟨20841506729273993305961387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55577351278063982149230365 20841506729273993305961387)
      ·
        refine ⟨31262260093910989958942081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20841506729273993305961387 31262260093910989958942081)
        ·
          refine ⟨23446695070433242469206561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31262260093910989958942081 23446695070433242469206561)
          ·
            refine ⟨17585021302824931851904921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23446695070433242469206561 17585021302824931851904921)
            ·
              refine ⟨13188765977118698888928691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17585021302824931851904921 13188765977118698888928691)
              ·
                refine ⟨19783148965678048333393037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13188765977118698888928691 19783148965678048333393037)
                ·
                  refine ⟨7418680862129268125022389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19783148965678048333393037 7418680862129268125022389)
                  ·
                    refine ⟨695501330824618886720849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7418680862129268125022389 695501330824618886720849)
                    ·
                      refine ⟨521625998118464165040637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 695501330824618886720849 521625998118464165040637)
                      ·
                        rfl

theorem cell23_1015863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 3, 5, 2].length) (baseStart_1015863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1015863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1015863 prefixEnd_1015863 := by exact prefixLift 1015863
  have htrace : WordTrace (prefixWord ++ tailWord_1015863) baseStart_1015863 baseEnd_1015863 := by
    simpa [prefixWord, tailWord_1015863, baseEnd_1015863] using wordTrace_append hprefix tailTrace_1015863
  have hstable : (prefixWord ++ tailWord_1015863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015863).length < 2 ^ (prefixWord ++ tailWord_1015863).sum := by decide
  have hdescent : baseEnd_1015863 < baseStart_1015863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015904 : List Nat := [2, 1, 1, 3, 2, 3, 4, 2, 1, 1, 3]
def baseStart_1015904 : Nat := 118140960795 + 1015904 * 2 ^ 59
def prefixEnd_1015904 : Nat := 4983230072969 + 3 ^ 40 * 1015904 * 2
def baseEnd_1015904 : Nat := 521647050825298504627949

theorem tailTrace_1015904 : CollatzResearch.WordTrace tailWord_1015904 prefixEnd_1015904 521647050825298504627949 := by
  unfold tailWord_1015904
  simp only [CollatzResearch.WordTrace]
  refine ⟨18526531455780392717531383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24702041941040523623375177 18526531455780392717531383)
  ·
    refine ⟨27789797183670589076297075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18526531455780392717531383 27789797183670589076297075)
    ·
      refine ⟨41684695775505883614445613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27789797183670589076297075 41684695775505883614445613)
      ·
        refine ⟨15631760915814706355417105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41684695775505883614445613 15631760915814706355417105)
        ·
          refine ⟨11723820686861029766562829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15631760915814706355417105 11723820686861029766562829)
          ·
            refine ⟨4396432757572886162461061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11723820686861029766562829 4396432757572886162461061)
            ·
              refine ⟨824331142044916155461449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4396432757572886162461061 824331142044916155461449)
              ·
                refine ⟨618248356533687116596087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 824331142044916155461449 618248356533687116596087)
                ·
                  refine ⟨927372534800530674894131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 618248356533687116596087 927372534800530674894131)
                  ·
                    refine ⟨1391058802200796012341197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 927372534800530674894131 1391058802200796012341197)
                    ·
                      refine ⟨521647050825298504627949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1391058802200796012341197 521647050825298504627949)
                      ·
                        rfl

theorem cell23_1015904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 4, 2, 1, 1, 3].length) (baseStart_1015904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1015904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1015904 prefixEnd_1015904 := by exact prefixLift 1015904
  have htrace : WordTrace (prefixWord ++ tailWord_1015904) baseStart_1015904 baseEnd_1015904 := by
    simpa [prefixWord, tailWord_1015904, baseEnd_1015904] using wordTrace_append hprefix tailTrace_1015904
  have hstable : (prefixWord ++ tailWord_1015904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015904).length < 2 ^ (prefixWord ++ tailWord_1015904).sum := by decide
  have hdescent : baseEnd_1015904 < baseStart_1015904 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015913 : List Nat := [1, 2, 1, 1, 1, 5, 1, 1, 5, 2, 3]
def baseStart_1015913 : Nat := 118140960795 + 1015913 * 2 ^ 59
def prefixEnd_1015913 : Nat := 4983230072969 + 3 ^ 40 * 1015913 * 2
def baseEnd_1015913 : Nat := 521651672151188969415407

theorem tailTrace_1015913 : CollatzResearch.WordTrace tailWord_1015913 prefixEnd_1015913 521651672151188969415407 := by
  unfold tailWord_1015913
  simp only [CollatzResearch.WordTrace]
  refine ⟨37053391168528179972140393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24702260779018786648093595 37053391168528179972140393)
  ·
    refine ⟨27790043376396134979105295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37053391168528179972140393 27790043376396134979105295)
    ·
      refine ⟨41685065064594202468657943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27790043376396134979105295 41685065064594202468657943)
      ·
        refine ⟨62527597596891303702986915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41685065064594202468657943 62527597596891303702986915)
        ·
          refine ⟨93791396395336955554480373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62527597596891303702986915 93791396395336955554480373)
          ·
            refine ⟨8792943412062839583232535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 93791396395336955554480373 8792943412062839583232535)
            ·
              refine ⟨13189415118094259374848803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8792943412062839583232535 13189415118094259374848803)
              ·
                refine ⟨19784122677141389062273205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13189415118094259374848803 19784122677141389062273205)
                ·
                  refine ⟨1854761500982005224588113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19784122677141389062273205 1854761500982005224588113)
                  ·
                    refine ⟨1391071125736503918441085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1854761500982005224588113 1391071125736503918441085)
                    ·
                      refine ⟨521651672151188969415407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1391071125736503918441085 521651672151188969415407)
                      ·
                        rfl

theorem cell23_1015913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 5, 2, 3].length) (baseStart_1015913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1015913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1015913 prefixEnd_1015913 := by exact prefixLift 1015913
  have htrace : WordTrace (prefixWord ++ tailWord_1015913) baseStart_1015913 baseEnd_1015913 := by
    simpa [prefixWord, tailWord_1015913, baseEnd_1015913] using wordTrace_append hprefix tailTrace_1015913
  have hstable : (prefixWord ++ tailWord_1015913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015913).length < 2 ^ (prefixWord ++ tailWord_1015913).sum := by decide
  have hdescent : baseEnd_1015913 < baseStart_1015913 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015920 : List Nat := [2, 1, 1, 1, 5, 2, 2, 3, 2, 4]
def baseStart_1015920 : Nat := 118140960795 + 1015920 * 2 ^ 59
def prefixEnd_1015920 : Nat := 4983230072969 + 3 ^ 40 * 1015920 * 2
def baseEnd_1015920 : Nat := 173885088838590147342625

theorem tailTrace_1015920 : CollatzResearch.WordTrace tailWord_1015920 prefixEnd_1015920 173885088838590147342625 := by
  unfold tailWord_1015920
  simp only [CollatzResearch.WordTrace]
  refine ⟨18526823239751410083822607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24702430986335213445096809 18526823239751410083822607)
  ·
    refine ⟨27790234859627115125733911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18526823239751410083822607 27790234859627115125733911)
    ·
      refine ⟨41685352289440672688600867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27790234859627115125733911 41685352289440672688600867)
      ·
        refine ⟨62528028434161009032901301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41685352289440672688600867 62528028434161009032901301)
        ·
          refine ⟨5862002665702594596834497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62528028434161009032901301 5862002665702594596834497)
          ·
            refine ⟨4396501999276945947625873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5862002665702594596834497 4396501999276945947625873)
            ·
              refine ⟨3297376499457709460719405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4396501999276945947625873 3297376499457709460719405)
              ·
                refine ⟨1236516187296641047769777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3297376499457709460719405 1236516187296641047769777)
                ·
                  refine ⟨927387140472480785827333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1236516187296641047769777 927387140472480785827333)
                  ·
                    refine ⟨173885088838590147342625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 927387140472480785827333 173885088838590147342625)
                    ·
                      rfl

theorem cell23_1015920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 3, 2, 4].length) (baseStart_1015920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1015920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1015920 prefixEnd_1015920 := by exact prefixLift 1015920
  have htrace : WordTrace (prefixWord ++ tailWord_1015920) baseStart_1015920 baseEnd_1015920 := by
    simpa [prefixWord, tailWord_1015920, baseEnd_1015920] using wordTrace_append hprefix tailTrace_1015920
  have hstable : (prefixWord ++ tailWord_1015920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015920).length < 2 ^ (prefixWord ++ tailWord_1015920).sum := by decide
  have hdescent : baseEnd_1015920 < baseStart_1015920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015927 : List Nat := [1, 1, 3, 1, 1, 6, 1, 2, 3, 2, 2]
def baseStart_1015927 : Nat := 118140960795 + 1015927 * 2 ^ 59
def prefixEnd_1015927 : Nat := 4983230072969 + 3 ^ 40 * 1015927 * 2
def baseEnd_1015927 : Nat := 521658860880351914640343

theorem tailTrace_1015927 : CollatzResearch.WordTrace tailWord_1015927 prefixEnd_1015927 521658860880351914640343 := by
  unfold tailWord_1015927
  simp only [CollatzResearch.WordTrace]
  refine ⟨37053901790477460363150035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24702601193651640242100023 37053901790477460363150035)
  ·
    refine ⟨55580852685716190544725053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37053901790477460363150035 55580852685716190544725053)
    ·
      refine ⟨20842819757143571454271895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55580852685716190544725053 20842819757143571454271895)
      ·
        refine ⟨31264229635715357181407843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20842819757143571454271895 31264229635715357181407843)
        ·
          refine ⟨46896344453573035772111765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31264229635715357181407843 46896344453573035772111765)
          ·
            refine ⟨2198266146261236051817739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 46896344453573035772111765 2198266146261236051817739)
            ·
              refine ⟨3297399219391854077726609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2198266146261236051817739 3297399219391854077726609)
              ·
                refine ⟨2473049414543890558294957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3297399219391854077726609 2473049414543890558294957)
                ·
                  refine ⟨927393530453958959360609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2473049414543890558294957 927393530453958959360609)
                  ·
                    refine ⟨695545147840469219520457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 927393530453958959360609 695545147840469219520457)
                    ·
                      refine ⟨521658860880351914640343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 695545147840469219520457 521658860880351914640343)
                      ·
                        rfl

theorem cell23_1015927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 2, 3, 2, 2].length) (baseStart_1015927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1015927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1015927 prefixEnd_1015927 := by exact prefixLift 1015927
  have htrace : WordTrace (prefixWord ++ tailWord_1015927) baseStart_1015927 baseEnd_1015927 := by
    simpa [prefixWord, tailWord_1015927, baseEnd_1015927] using wordTrace_append hprefix tailTrace_1015927
  have hstable : (prefixWord ++ tailWord_1015927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015927).length < 2 ^ (prefixWord ++ tailWord_1015927).sum := by decide
  have hdescent : baseEnd_1015927 < baseStart_1015927 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015944 : List Nat := [2, 1, 3, 4, 1, 3, 2, 1, 1, 1, 4]
def baseStart_1015944 : Nat := 118140960795 + 1015944 * 2 ^ 59
def prefixEnd_1015944 : Nat := 4983230072969 + 3 ^ 40 * 1015944 * 2
def baseEnd_1015944 : Nat := 521667590051478348127765

theorem tailTrace_1015944 : CollatzResearch.WordTrace tailWord_1015944 prefixEnd_1015944 521667590051478348127765 := by
  unfold tailWord_1015944
  simp only [CollatzResearch.WordTrace]
  refine ⟨18527260915707936133259443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24703014554277248177679257 18527260915707936133259443)
  ·
    refine ⟨27790891373561904199889165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18527260915707936133259443 27790891373561904199889165)
    ·
      refine ⟨10421584265085714074958437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27790891373561904199889165 10421584265085714074958437)
      ·
        refine ⟨1954047049703571389054707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10421584265085714074958437 1954047049703571389054707)
        ·
          refine ⟨2931070574555357083582061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1954047049703571389054707 2931070574555357083582061)
          ·
            refine ⟨1099151465458258906343273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2931070574555357083582061 1099151465458258906343273)
            ·
              refine ⟨824363599093694179757455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1099151465458258906343273 824363599093694179757455)
              ·
                refine ⟨1236545398640541269636183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 824363599093694179757455 1236545398640541269636183)
                ·
                  refine ⟨1854818097960811904454275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1236545398640541269636183 1854818097960811904454275)
                  ·
                    refine ⟨2782227146941217856681413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1854818097960811904454275 2782227146941217856681413)
                    ·
                      refine ⟨521667590051478348127765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2782227146941217856681413 521667590051478348127765)
                      ·
                        rfl

theorem cell23_1015944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 2, 1, 1, 1, 4].length) (baseStart_1015944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1015944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1015944 prefixEnd_1015944 := by exact prefixLift 1015944
  have htrace : WordTrace (prefixWord ++ tailWord_1015944) baseStart_1015944 baseEnd_1015944 := by
    simpa [prefixWord, tailWord_1015944, baseEnd_1015944] using wordTrace_append hprefix tailTrace_1015944
  have hstable : (prefixWord ++ tailWord_1015944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015944).length < 2 ^ (prefixWord ++ tailWord_1015944).sum := by decide
  have hdescent : baseEnd_1015944 < baseStart_1015944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016004 : List Nat := [2, 3, 3, 1, 2, 1, 2, 3, 1, 3, 2]
def baseStart_1016004 : Nat := 118140960795 + 1016004 * 2 ^ 59
def prefixEnd_1016004 : Nat := 4983230072969 + 3 ^ 40 * 1016004 * 2
def baseEnd_1016004 : Nat := 521698398890748113377489

theorem tailTrace_1016004 : CollatzResearch.WordTrace tailWord_1016004 prefixEnd_1016004 521698398890748113377489 := by
  unfold tailWord_1016004
  simp only [CollatzResearch.WordTrace]
  refine ⟨18528355105599251256851533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24704473474132335009135377 18528355105599251256851533)
  ·
    refine ⟨6948133164599719221319325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18528355105599251256851533 6948133164599719221319325)
    ·
      refine ⟨2605549936724894707994747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6948133164599719221319325 2605549936724894707994747)
      ·
        refine ⟨3908324905087342061992121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2605549936724894707994747 3908324905087342061992121)
        ·
          refine ⟨2931243678815506546494091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3908324905087342061992121 2931243678815506546494091)
          ·
            refine ⟨4396865518223259819741137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2931243678815506546494091 4396865518223259819741137)
            ·
              refine ⟨3297649138667444864805853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4396865518223259819741137 3297649138667444864805853)
              ·
                refine ⟨1236618427000291824302195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3297649138667444864805853 1236618427000291824302195)
                ·
                  refine ⟨1854927640500437736453293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1236618427000291824302195 1854927640500437736453293)
                  ·
                    refine ⟨695597865187664151169985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1854927640500437736453293 695597865187664151169985)
                    ·
                      refine ⟨521698398890748113377489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 695597865187664151169985 521698398890748113377489)
                      ·
                        rfl

theorem cell23_1016004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 3, 1, 3, 2].length) (baseStart_1016004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1016004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1016004 prefixEnd_1016004 := by exact prefixLift 1016004
  have htrace : WordTrace (prefixWord ++ tailWord_1016004) baseStart_1016004 baseEnd_1016004 := by
    simpa [prefixWord, tailWord_1016004, baseEnd_1016004] using wordTrace_append hprefix tailTrace_1016004
  have hstable : (prefixWord ++ tailWord_1016004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016004).length < 2 ^ (prefixWord ++ tailWord_1016004).sum := by decide
  have hdescent : baseEnd_1016004 < baseStart_1016004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016017 : List Nat := [1, 2, 2, 1, 2, 2, 4, 1, 4, 2, 2]
def baseStart_1016017 : Nat := 118140960795 + 1016017 * 2 ^ 59
def prefixEnd_1016017 : Nat := 4983230072969 + 3 ^ 40 * 1016017 * 2
def baseEnd_1016017 : Nat := 521705074139256562514929

theorem tailTrace_1016017 : CollatzResearch.WordTrace tailWord_1016017 prefixEnd_1016017 521705074139256562514929 := by
  unfold tailWord_1016017
  simp only [CollatzResearch.WordTrace]
  refine ⟨37057184360151405733926305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24704789573434270489284203 37057184360151405733926305)
  ·
    refine ⟨27792888270113554300444729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37057184360151405733926305 27792888270113554300444729)
    ·
      refine ⟨20844666202585165725333547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27792888270113554300444729 20844666202585165725333547)
      ·
        refine ⟨31266999303877748588000321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20844666202585165725333547 31266999303877748588000321)
        ·
          refine ⟨23450249477908311441000241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31266999303877748588000321 23450249477908311441000241)
          ·
            refine ⟨17587687108431233580750181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23450249477908311441000241 17587687108431233580750181)
            ·
              refine ⟨3297691332830856296390659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17587687108431233580750181 3297691332830856296390659)
              ·
                refine ⟨4946536999246284444585989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3297691332830856296390659 4946536999246284444585989)
                ·
                  refine ⟨927475687358678333359873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4946536999246284444585989 927475687358678333359873)
                  ·
                    refine ⟨695606765519008750019905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 927475687358678333359873 695606765519008750019905)
                    ·
                      refine ⟨521705074139256562514929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 695606765519008750019905 521705074139256562514929)
                      ·
                        rfl

theorem cell23_1016017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 1, 4, 2, 2].length) (baseStart_1016017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1016017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1016017 prefixEnd_1016017 := by exact prefixLift 1016017
  have htrace : WordTrace (prefixWord ++ tailWord_1016017) baseStart_1016017 baseEnd_1016017 := by
    simpa [prefixWord, tailWord_1016017, baseEnd_1016017] using wordTrace_append hprefix tailTrace_1016017
  have hstable : (prefixWord ++ tailWord_1016017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016017).length < 2 ^ (prefixWord ++ tailWord_1016017).sum := by decide
  have hdescent : baseEnd_1016017 < baseStart_1016017 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016063 : List Nat := [1, 1, 2, 2, 1, 4, 1, 1, 3, 2, 5]
def baseStart_1016063 : Nat := 118140960795 + 1016063 * 2 ^ 59
def prefixEnd_1016063 : Nat := 4983230072969 + 3 ^ 40 * 1016063 * 2
def baseEnd_1016063 : Nat := 521728694249363382539717

theorem tailTrace_1016063 : CollatzResearch.WordTrace tailWord_1016063 prefixEnd_1016063 521728694249363382539717 := by
  unfold tailWord_1016063
  simp only [CollatzResearch.WordTrace]
  refine ⟨37058862117984755590100843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24705908078656503726733895 37058862117984755590100843)
  ·
    refine ⟨55588293176977133385151265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37058862117984755590100843 55588293176977133385151265)
    ·
      refine ⟨41691219882732850038863449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55588293176977133385151265 41691219882732850038863449)
      ·
        refine ⟨31268414912049637529147587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41691219882732850038863449 31268414912049637529147587)
        ·
          refine ⟨46902622368074456293721381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31268414912049637529147587 46902622368074456293721381)
          ·
            refine ⟨8794241694013960555072759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46902622368074456293721381 8794241694013960555072759)
            ·
              refine ⟨13191362541020940832609139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8794241694013960555072759 13191362541020940832609139)
              ·
                refine ⟨19787043811531411248913709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13191362541020940832609139 19787043811531411248913709)
                ·
                  refine ⟨7420141429324279218342641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19787043811531411248913709 7420141429324279218342641)
                  ·
                    refine ⟨5565106071993209413756981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7420141429324279218342641 5565106071993209413756981)
                    ·
                      refine ⟨521728694249363382539717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5565106071993209413756981 521728694249363382539717)
                      ·
                        rfl

theorem cell23_1016063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 3, 2, 5].length) (baseStart_1016063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1016063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1016063 prefixEnd_1016063 := by exact prefixLift 1016063
  have htrace : WordTrace (prefixWord ++ tailWord_1016063) baseStart_1016063 baseEnd_1016063 := by
    simpa [prefixWord, tailWord_1016063, baseEnd_1016063] using wordTrace_append hprefix tailTrace_1016063
  have hstable : (prefixWord ++ tailWord_1016063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016063).length < 2 ^ (prefixWord ++ tailWord_1016063).sum := by decide
  have hdescent : baseEnd_1016063 < baseStart_1016063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016104 : List Nat := [2, 1, 5, 1, 3, 2, 1, 1, 2, 5]
def baseStart_1016104 : Nat := 118140960795 + 1016104 * 2 ^ 59
def prefixEnd_1016104 : Nat := 4983230072969 + 3 ^ 40 * 1016104 * 2
def baseEnd_1016104 : Nat := 173916582318732574042343

theorem tailTrace_1016104 : CollatzResearch.WordTrace tailWord_1016104 prefixEnd_1016104 173916582318732574042343 := by
  unfold tailWord_1016104
  simp only [CollatzResearch.WordTrace]
  refine ⟨18530178755418109796171683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24706905007224146394895577 18530178755418109796171683)
  ·
    refine ⟨27795268133127164694257525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18530178755418109796171683 27795268133127164694257525)
    ·
      refine ⟨2605806387480671690086643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27795268133127164694257525 2605806387480671690086643)
      ·
        refine ⟨3908709581221007535129965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2605806387480671690086643 3908709581221007535129965)
        ·
          refine ⟨1465766092957877825673737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3908709581221007535129965 1465766092957877825673737)
          ·
            refine ⟨1099324569718408369255303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1465766092957877825673737 1099324569718408369255303)
            ·
              refine ⟨1648986854577612553882955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1099324569718408369255303 1648986854577612553882955)
              ·
                refine ⟨2473480281866418830824433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1648986854577612553882955 2473480281866418830824433)
                ·
                  refine ⟨1855110211399814123118325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2473480281866418830824433 1855110211399814123118325)
                  ·
                    refine ⟨173916582318732574042343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1855110211399814123118325 173916582318732574042343)
                    ·
                      rfl

theorem cell23_1016104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 1, 1, 2, 5].length) (baseStart_1016104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1016104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1016104 prefixEnd_1016104 := by exact prefixLift 1016104
  have htrace : WordTrace (prefixWord ++ tailWord_1016104) baseStart_1016104 baseEnd_1016104 := by
    simpa [prefixWord, tailWord_1016104, baseEnd_1016104] using wordTrace_append hprefix tailTrace_1016104
  have hstable : (prefixWord ++ tailWord_1016104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016104).length < 2 ^ (prefixWord ++ tailWord_1016104).sum := by decide
  have hdescent : baseEnd_1016104 < baseStart_1016104 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016143 : List Nat := [1, 1, 2, 1, 1, 2, 1, 3, 2, 9]
def baseStart_1016143 : Nat := 118140960795 + 1016143 * 2 ^ 59
def prefixEnd_1016143 : Nat := 4983230072969 + 3 ^ 40 * 1016143 * 2
def baseEnd_1016143 : Nat := 173923257567241023179783

theorem tailTrace_1016143 : CollatzResearch.WordTrace tailWord_1016143 prefixEnd_1016143 173923257567241023179783 := by
  unfold tailWord_1016143
  simp only [CollatzResearch.WordTrace]
  refine ⟨37061779957694929253013083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24707853305129952835342055 37061779957694929253013083)
  ·
    refine ⟨55592669936542393879519625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37061779957694929253013083 55592669936542393879519625)
    ·
      refine ⟨41694502452406795409639719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55592669936542393879519625 41694502452406795409639719)
      ·
        refine ⟨62541753678610193114459579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41694502452406795409639719 62541753678610193114459579)
        ·
          refine ⟨93812630517915289671689369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62541753678610193114459579 93812630517915289671689369)
          ·
            refine ⟨70359472888436467253767027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93812630517915289671689369 70359472888436467253767027)
            ·
              refine ⟨105539209332654700880650541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70359472888436467253767027 105539209332654700880650541)
              ·
                refine ⟨39577203499745512830243953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105539209332654700880650541 39577203499745512830243953)
                ·
                  refine ⟨29682902624809134622682965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39577203499745512830243953 29682902624809134622682965)
                  ·
                    refine ⟨173923257567241023179783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 29682902624809134622682965 173923257567241023179783)
                    ·
                      rfl

theorem cell23_1016143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 9].length) (baseStart_1016143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1016143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1016143 prefixEnd_1016143 := by exact prefixLift 1016143
  have htrace : WordTrace (prefixWord ++ tailWord_1016143) baseStart_1016143 baseEnd_1016143 := by
    simpa [prefixWord, tailWord_1016143, baseEnd_1016143] using wordTrace_append hprefix tailTrace_1016143
  have hstable : (prefixWord ++ tailWord_1016143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016143).length < 2 ^ (prefixWord ++ tailWord_1016143).sum := by decide
  have hdescent : baseEnd_1016143 < baseStart_1016143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016217 : List Nat := [1, 2, 1, 2, 1, 4, 3, 1, 3, 2, 3]
def baseStart_1016217 : Nat := 118140960795 + 1016217 * 2 ^ 59
def prefixEnd_1016217 : Nat := 4983230072969 + 3 ^ 40 * 1016217 * 2
def baseEnd_1016217 : Nat := 521807770270155780014009

theorem tailTrace_1016217 : CollatzResearch.WordTrace tailWord_1016217 prefixEnd_1016217 521807770270155780014009 := by
  unfold tailWord_1016217
  simp only [CollatzResearch.WordTrace]
  refine ⟨37064478959426839891206905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24709652639617893260804603 37064478959426839891206905)
  ·
    refine ⟨27798359219570129918405179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37064478959426839891206905 27798359219570129918405179)
    ·
      refine ⟨41697538829355194877607769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27798359219570129918405179 41697538829355194877607769)
      ·
        refine ⟨31273154122016396158205827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41697538829355194877607769 31273154122016396158205827)
        ·
          refine ⟨46909731183024594237308741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31273154122016396158205827 46909731183024594237308741)
          ·
            refine ⟨8795574596817111419495389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46909731183024594237308741 8795574596817111419495389)
            ·
              refine ⟨3298340473806416782310771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8795574596817111419495389 3298340473806416782310771)
              ·
                refine ⟨4947510710709625173466157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3298340473806416782310771 4947510710709625173466157)
                ·
                  refine ⟨1855316516516109440049809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4947510710709625173466157 1855316516516109440049809)
                  ·
                    refine ⟨1391487387387082080037357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1855316516516109440049809 1391487387387082080037357)
                    ·
                      refine ⟨521807770270155780014009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1391487387387082080037357 521807770270155780014009)
                      ·
                        rfl

theorem cell23_1016217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 1, 3, 2, 3].length) (baseStart_1016217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1016217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1016217 prefixEnd_1016217 := by exact prefixLift 1016217
  have htrace : WordTrace (prefixWord ++ tailWord_1016217) baseStart_1016217 baseEnd_1016217 := by
    simpa [prefixWord, tailWord_1016217, baseEnd_1016217] using wordTrace_append hprefix tailTrace_1016217
  have hstable : (prefixWord ++ tailWord_1016217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016217).length < 2 ^ (prefixWord ++ tailWord_1016217).sum := by decide
  have hdescent : baseEnd_1016217 < baseStart_1016217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016227 : List Nat := [1, 1, 1, 4, 1, 5, 1, 2, 1, 2, 4]
def baseStart_1016227 : Nat := 118140960795 + 1016227 * 2 ^ 59
def prefixEnd_1016227 : Nat := 4983230072969 + 3 ^ 40 * 1016227 * 2
def baseEnd_1016227 : Nat := 521812905076700740888963

theorem tailTrace_1016227 : CollatzResearch.WordTrace tailWord_1016227 prefixEnd_1016227 521812905076700740888963 := by
  unfold tailWord_1016227
  simp only [CollatzResearch.WordTrace]
  refine ⟨37064843689390611599070935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24709895792927074399380623 37064843689390611599070935)
  ·
    refine ⟨55597265534085917398606403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37064843689390611599070935 55597265534085917398606403)
    ·
      refine ⟨83395898301128876097909605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55597265534085917398606403 83395898301128876097909605)
      ·
        refine ⟨15636730931461664268358051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83395898301128876097909605 15636730931461664268358051)
        ·
          refine ⟨23455096397192496402537077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15636730931461664268358051 23455096397192496402537077)
          ·
            refine ⟨2198915287236796537737851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23455096397192496402537077 2198915287236796537737851)
            ·
              refine ⟨3298372930855194806606777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2198915287236796537737851 3298372930855194806606777)
              ·
                refine ⟨2473779698141396104955083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3298372930855194806606777 2473779698141396104955083)
                ·
                  refine ⟨3710669547212094157432625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2473779698141396104955083 3710669547212094157432625)
                  ·
                    refine ⟨2783002160409070618074469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3710669547212094157432625 2783002160409070618074469)
                    ·
                      refine ⟨521812905076700740888963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2783002160409070618074469 521812905076700740888963)
                      ·
                        rfl

theorem cell23_1016227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 2, 1, 2, 4].length) (baseStart_1016227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1016227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1016227 prefixEnd_1016227 := by exact prefixLift 1016227
  have htrace : WordTrace (prefixWord ++ tailWord_1016227) baseStart_1016227 baseEnd_1016227 := by
    simpa [prefixWord, tailWord_1016227, baseEnd_1016227] using wordTrace_append hprefix tailTrace_1016227
  have hstable : (prefixWord ++ tailWord_1016227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016227).length < 2 ^ (prefixWord ++ tailWord_1016227).sum := by decide
  have hdescent : baseEnd_1016227 < baseStart_1016227 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016231 : List Nat := [1, 1, 6, 1, 1, 3, 3, 1, 1, 1, 4]
def baseStart_1016231 : Nat := 118140960795 + 1016231 * 2 ^ 59
def prefixEnd_1016231 : Nat := 4983230072969 + 3 ^ 40 * 1016231 * 2
def baseEnd_1016231 : Nat := 521814958999318725238945

theorem tailTrace_1016231 : CollatzResearch.WordTrace tailWord_1016231 prefixEnd_1016231 521814958999318725238945 := by
  unfold tailWord_1016231
  simp only [CollatzResearch.WordTrace]
  refine ⟨37064989581376120282216547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24709993054250746854811031 37064989581376120282216547)
  ·
    refine ⟨55597484372064180423324821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37064989581376120282216547 55597484372064180423324821)
    ·
      refine ⟨2606132079940508457343351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 55597484372064180423324821 2606132079940508457343351)
      ·
        refine ⟨3909198119910762686015027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2606132079940508457343351 3909198119910762686015027)
        ·
          refine ⟨5863797179866144029022541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3909198119910762686015027 5863797179866144029022541)
          ·
            refine ⟨2198923942449804010883453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5863797179866144029022541 2198923942449804010883453)
            ·
              refine ⟨824596478418676504081295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2198923942449804010883453 824596478418676504081295)
              ·
                refine ⟨1236894717628014756121943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 824596478418676504081295 1236894717628014756121943)
                ·
                  refine ⟨1855342076442022134182915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1236894717628014756121943 1855342076442022134182915)
                  ·
                    refine ⟨2783013114663033201274373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1855342076442022134182915 2783013114663033201274373)
                    ·
                      refine ⟨521814958999318725238945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2783013114663033201274373 521814958999318725238945)
                      ·
                        rfl

theorem cell23_1016231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 3, 1, 1, 1, 4].length) (baseStart_1016231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1016231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1016231 prefixEnd_1016231 := by exact prefixLift 1016231
  have htrace : WordTrace (prefixWord ++ tailWord_1016231) baseStart_1016231 baseEnd_1016231 := by
    simpa [prefixWord, tailWord_1016231, baseEnd_1016231] using wordTrace_append hprefix tailTrace_1016231
  have hstable : (prefixWord ++ tailWord_1016231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016231).length < 2 ^ (prefixWord ++ tailWord_1016231).sum := by decide
  have hdescent : baseEnd_1016231 < baseStart_1016231 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016237 : List Nat := [1, 5, 2, 2, 2, 11]
def baseStart_1016237 : Nat := 118140960795 + 1016237 * 2 ^ 59
def prefixEnd_1016237 : Nat := 4983230072969 + 3 ^ 40 * 1016237 * 2
def baseEnd_1016237 : Nat := 2147399341083315645119

theorem tailTrace_1016237 : CollatzResearch.WordTrace tailWord_1016237 prefixEnd_1016237 2147399341083315645119 := by
  unfold tailWord_1016237
  simp only [CollatzResearch.WordTrace]
  refine ⟨37065208419354383306934965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24710138946236255537956643 37065208419354383306934965)
  ·
    refine ⟨3474863289314473435025153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37065208419354383306934965 3474863289314473435025153)
    ·
      refine ⟨2606147466985855076268865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3474863289314473435025153 2606147466985855076268865)
      ·
        refine ⟨1954610600239391307201649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2606147466985855076268865 1954610600239391307201649)
        ·
          refine ⟨1465957950179543480401237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1954610600239391307201649 1465957950179543480401237)
          ·
            refine ⟨2147399341083315645119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 1465957950179543480401237 2147399341083315645119)
            ·
              rfl

theorem cell23_1016237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 11].length) (baseStart_1016237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1016237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1016237 prefixEnd_1016237 := by exact prefixLift 1016237
  have htrace : WordTrace (prefixWord ++ tailWord_1016237) baseStart_1016237 baseEnd_1016237 := by
    simpa [prefixWord, tailWord_1016237, baseEnd_1016237] using wordTrace_append hprefix tailTrace_1016237
  have hstable : (prefixWord ++ tailWord_1016237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016237).length < 2 ^ (prefixWord ++ tailWord_1016237).sum := by decide
  have hdescent : baseEnd_1016237 < baseStart_1016237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016264 : List Nat := [2, 1, 3, 1, 3, 3, 2, 1, 1, 3, 3]
def baseStart_1016264 : Nat := 118140960795 + 1016264 * 2 ^ 59
def prefixEnd_1016264 : Nat := 4983230072969 + 3 ^ 40 * 1016264 * 2
def baseEnd_1016264 : Nat := 521831903860917096126293

theorem tailTrace_1016264 : CollatzResearch.WordTrace tailWord_1016264 prefixEnd_1016264 521831903860917096126293 := by
  unfold tailWord_1016264
  simp only [CollatzResearch.WordTrace]
  refine ⟨18533096595128283459083923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24710795460171044612111897 18533096595128283459083923)
  ·
    refine ⟨27799644892692425188625885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18533096595128283459083923 27799644892692425188625885)
    ·
      refine ⟨10424866834759659445734707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27799644892692425188625885 10424866834759659445734707)
      ·
        refine ⟨15637300252139489168602061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10424866834759659445734707 15637300252139489168602061)
        ·
          refine ⟨5863987594552308438225773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15637300252139489168602061 5863987594552308438225773)
          ·
            refine ⟨2198995347957115664334665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5863987594552308438225773 2198995347957115664334665)
            ·
              refine ⟨1649246510967836748250999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2198995347957115664334665 1649246510967836748250999)
              ·
                refine ⟨2473869766451755122376499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1649246510967836748250999 2473869766451755122376499)
                ·
                  refine ⟨3710804649677632683564749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2473869766451755122376499 3710804649677632683564749)
                  ·
                    refine ⟨1391551743629112256336781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3710804649677632683564749 1391551743629112256336781)
                    ·
                      refine ⟨521831903860917096126293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1391551743629112256336781 521831903860917096126293)
                      ·
                        rfl

theorem cell23_1016264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 2, 1, 1, 3, 3].length) (baseStart_1016264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1016264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1016264 prefixEnd_1016264 := by exact prefixLift 1016264
  have htrace : WordTrace (prefixWord ++ tailWord_1016264) baseStart_1016264 baseEnd_1016264 := by
    simpa [prefixWord, tailWord_1016264, baseEnd_1016264] using wordTrace_append hprefix tailTrace_1016264
  have hstable : (prefixWord ++ tailWord_1016264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016264).length < 2 ^ (prefixWord ++ tailWord_1016264).sum := by decide
  have hdescent : baseEnd_1016264 < baseStart_1016264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016280 : List Nat := [2, 1, 2, 2, 2, 1, 1, 1, 3, 8]
def baseStart_1016280 : Nat := 118140960795 + 1016280 * 2 ^ 59
def prefixEnd_1016280 : Nat := 4983230072969 + 3 ^ 40 * 1016280 * 2
def baseEnd_1016280 : Nat := 173946706517129677842073

theorem tailTrace_1016280 : CollatzResearch.WordTrace tailWord_1016280 prefixEnd_1016280 173946706517129677842073 := by
  unfold tailWord_1016280
  simp only [CollatzResearch.WordTrace]
  refine ⟨18533388379099300825375147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24711184505465734433833529 18533388379099300825375147)
  ·
    refine ⟨27800082568648951238062721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18533388379099300825375147 27800082568648951238062721)
    ·
      refine ⟨20850061926486713428547041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27800082568648951238062721 20850061926486713428547041)
      ·
        refine ⟨15637546444865035071410281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20850061926486713428547041 15637546444865035071410281)
        ·
          refine ⟨11728159833648776303557711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15637546444865035071410281 11728159833648776303557711)
          ·
            refine ⟨17592239750473164455336567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11728159833648776303557711 17592239750473164455336567)
            ·
              refine ⟨26388359625709746683004851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17592239750473164455336567 26388359625709746683004851)
              ·
                refine ⟨39582539438564620024507277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26388359625709746683004851 39582539438564620024507277)
                ·
                  refine ⟨14843452289461732509190229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39582539438564620024507277 14843452289461732509190229)
                  ·
                    refine ⟨173946706517129677842073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 14843452289461732509190229 173946706517129677842073)
                    ·
                      rfl

theorem cell23_1016280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 3, 8].length) (baseStart_1016280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1016280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1016280 prefixEnd_1016280 := by exact prefixLift 1016280
  have htrace : WordTrace (prefixWord ++ tailWord_1016280) baseStart_1016280 baseEnd_1016280 := by
    simpa [prefixWord, tailWord_1016280, baseEnd_1016280] using wordTrace_append hprefix tailTrace_1016280
  have hstable : (prefixWord ++ tailWord_1016280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016280).length < 2 ^ (prefixWord ++ tailWord_1016280).sum := by decide
  have hdescent : baseEnd_1016280 < baseStart_1016280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016298 : List Nat := [3, 1, 3, 1, 3, 3, 1, 2, 2, 1, 3]
def baseStart_1016298 : Nat := 118140960795 + 1016298 * 2 ^ 59
def prefixEnd_1016298 : Nat := 4983230072969 + 3 ^ 40 * 1016298 * 2
def baseEnd_1016298 : Nat := 521849362203169963101137

theorem tailTrace_1016298 : CollatzResearch.WordTrace tailWord_1016298 prefixEnd_1016298 521849362203169963101137 := by
  unfold tailWord_1016298
  simp only [CollatzResearch.WordTrace]
  refine ⟨9266858318033347681226387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24711622181422260483270365 9266858318033347681226387)
  ·
    refine ⟨13900287477050021521839581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9266858318033347681226387 13900287477050021521839581)
    ·
      refine ⟨5212607803893758070689843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13900287477050021521839581 5212607803893758070689843)
      ·
        refine ⟨7818911705840637106034765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5212607803893758070689843 7818911705840637106034765)
        ·
          refine ⟨2932091889690238914763037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7818911705840637106034765 2932091889690238914763037)
          ·
            refine ⟨1099534458633839593036139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2932091889690238914763037 1099534458633839593036139)
            ·
              refine ⟨1649301687950759389554209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1099534458633839593036139 1649301687950759389554209)
              ·
                refine ⟨1236976265963069542165657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1649301687950759389554209 1236976265963069542165657)
                ·
                  refine ⟨927732199472302156624243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1236976265963069542165657 927732199472302156624243)
                  ·
                    refine ⟨1391598299208453234936365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 927732199472302156624243 1391598299208453234936365)
                    ·
                      refine ⟨521849362203169963101137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1391598299208453234936365 521849362203169963101137)
                      ·
                        rfl

theorem cell23_1016298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 1, 2, 2, 1, 3].length) (baseStart_1016298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1016298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1016298 prefixEnd_1016298 := by exact prefixLift 1016298
  have htrace : WordTrace (prefixWord ++ tailWord_1016298) baseStart_1016298 baseEnd_1016298 := by
    simpa [prefixWord, tailWord_1016298, baseEnd_1016298] using wordTrace_append hprefix tailTrace_1016298
  have hstable : (prefixWord ++ tailWord_1016298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016298).length < 2 ^ (prefixWord ++ tailWord_1016298).sum := by decide
  have hdescent : baseEnd_1016298 < baseStart_1016298 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016317 : List Nat := [1, 4, 1, 1, 1, 3, 1, 3, 2, 2, 4]
def baseStart_1016317 : Nat := 118140960795 + 1016317 * 2 ^ 59
def prefixEnd_1016317 : Nat := 4983230072969 + 3 ^ 40 * 1016317 * 2
def baseEnd_1016317 : Nat := 521859118335605388763549

theorem tailTrace_1016317 : CollatzResearch.WordTrace tailWord_1016317 prefixEnd_1016317 521859118335605388763549 := by
  unfold tailWord_1016317
  simp only [CollatzResearch.WordTrace]
  refine ⟨37068126259064556969847205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24712084172709704646564803 37068126259064556969847205)
  ·
    refine ⟨6950273673574604431846351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37068126259064556969847205 6950273673574604431846351)
    ·
      refine ⟨10425410510361906647769527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6950273673574604431846351 10425410510361906647769527)
      ·
        refine ⟨15638115765542859971654291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10425410510361906647769527 15638115765542859971654291)
        ·
          refine ⟨23457173648314289957481437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15638115765542859971654291 23457173648314289957481437)
          ·
            refine ⟨8796440118117858734055539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23457173648314289957481437 8796440118117858734055539)
            ·
              refine ⟨13194660177176788101083309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8796440118117858734055539 13194660177176788101083309)
              ·
                refine ⟨4947997566441295537906241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13194660177176788101083309 4947997566441295537906241)
                ·
                  refine ⟨3710998174830971653429681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4947997566441295537906241 3710998174830971653429681)
                  ·
                    refine ⟨2783248631123228740072261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3710998174830971653429681 2783248631123228740072261)
                    ·
                      refine ⟨521859118335605388763549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2783248631123228740072261 521859118335605388763549)
                      ·
                        rfl

theorem cell23_1016317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 3, 2, 2, 4].length) (baseStart_1016317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1016317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1016317 prefixEnd_1016317 := by exact prefixLift 1016317
  have htrace : WordTrace (prefixWord ++ tailWord_1016317) baseStart_1016317 baseEnd_1016317 := by
    simpa [prefixWord, tailWord_1016317, baseEnd_1016317] using wordTrace_append hprefix tailTrace_1016317
  have hstable : (prefixWord ++ tailWord_1016317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016317).length < 2 ^ (prefixWord ++ tailWord_1016317).sum := by decide
  have hdescent : baseEnd_1016317 < baseStart_1016317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016320 : List Nat := [2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 9]
def baseStart_1016320 : Nat := 118140960795 + 1016320 * 2 ^ 59
def prefixEnd_1016320 : Nat := 4983230072969 + 3 ^ 40 * 1016320 * 2
def baseEnd_1016320 : Nat := 521860658777568877026035

theorem tailTrace_1016320 : CollatzResearch.WordTrace tailWord_1016320 prefixEnd_1016320 521860658777568877026035 := by
  unfold tailWord_1016320
  simp only [CollatzResearch.WordTrace]
  refine ⟨18534117839026844241103207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24712157118702458988137609 18534117839026844241103207)
  ·
    refine ⟨27801176758540266361654811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18534117839026844241103207 27801176758540266361654811)
    ·
      refine ⟨41701765137810399542482217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27801176758540266361654811 41701765137810399542482217)
      ·
        refine ⟨31276323853357799656861663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41701765137810399542482217 31276323853357799656861663)
        ·
          refine ⟨46914485780036699485292495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31276323853357799656861663 46914485780036699485292495)
          ·
            refine ⟨70371728670055049227938743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46914485780036699485292495 70371728670055049227938743)
            ·
              refine ⟨105557593005082573841908115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70371728670055049227938743 105557593005082573841908115)
              ·
                refine ⟨158336389507623860762862173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105557593005082573841908115 158336389507623860762862173)
                ·
                  refine ⟨59376146065358947786073315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 158336389507623860762862173 59376146065358947786073315)
                  ·
                    refine ⟨89064219098038421679109973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59376146065358947786073315 89064219098038421679109973)
                    ·
                      refine ⟨521860658777568877026035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 89064219098038421679109973 521860658777568877026035)
                      ·
                        rfl

theorem cell23_1016320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 9].length) (baseStart_1016320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1016320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1016320 prefixEnd_1016320 := by exact prefixLift 1016320
  have htrace : WordTrace (prefixWord ++ tailWord_1016320) baseStart_1016320 baseEnd_1016320 := by
    simpa [prefixWord, tailWord_1016320, baseEnd_1016320] using wordTrace_append hprefix tailTrace_1016320
  have hstable : (prefixWord ++ tailWord_1016320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016320).length < 2 ^ (prefixWord ++ tailWord_1016320).sum := by decide
  have hdescent : baseEnd_1016320 < baseStart_1016320 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016321 : List Nat := [1, 2, 4, 1, 3, 1, 3, 1, 1, 4, 2]
def baseStart_1016321 : Nat := 118140960795 + 1016321 * 2 ^ 59
def prefixEnd_1016321 : Nat := 4983230072969 + 3 ^ 40 * 1016321 * 2
def baseEnd_1016321 : Nat := 521861172258223373113531

theorem tailTrace_1016321 : CollatzResearch.WordTrace tailWord_1016321 prefixEnd_1016321 521861172258223373113531 := by
  unfold tailWord_1016321
  simp only [CollatzResearch.WordTrace]
  refine ⟨37068272151050065652992817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24712181434033377101995211 37068272151050065652992817)
  ·
    refine ⟨27801204113287549239744613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37068272151050065652992817 27801204113287549239744613)
    ·
      refine ⟨5212725771241415482452115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27801204113287549239744613 5212725771241415482452115)
      ·
        refine ⟨7819088656862123223678173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5212725771241415482452115 7819088656862123223678173)
        ·
          refine ⟨2932158246323296208879315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7819088656862123223678173 2932158246323296208879315)
          ·
            refine ⟨4398237369484944313318973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2932158246323296208879315 4398237369484944313318973)
            ·
              refine ⟨1649339013556854117494615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4398237369484944313318973 1649339013556854117494615)
              ·
                refine ⟨2474008520335281176241923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1649339013556854117494615 2474008520335281176241923)
                ·
                  refine ⟨3711012780502921764362885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2474008520335281176241923 3711012780502921764362885)
                  ·
                    refine ⟨695814896344297830818041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3711012780502921764362885 695814896344297830818041)
                    ·
                      refine ⟨521861172258223373113531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 695814896344297830818041 521861172258223373113531)
                      ·
                        rfl

theorem cell23_1016321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 3, 1, 1, 4, 2].length) (baseStart_1016321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1016321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1016321 prefixEnd_1016321 := by exact prefixLift 1016321
  have htrace : WordTrace (prefixWord ++ tailWord_1016321) baseStart_1016321 baseEnd_1016321 := by
    simpa [prefixWord, tailWord_1016321, baseEnd_1016321] using wordTrace_append hprefix tailTrace_1016321
  have hstable : (prefixWord ++ tailWord_1016321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016321).length < 2 ^ (prefixWord ++ tailWord_1016321).sum := by decide
  have hdescent : baseEnd_1016321 < baseStart_1016321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016337 : List Nat := [1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 3]
def baseStart_1016337 : Nat := 118140960795 + 1016337 * 2 ^ 59
def prefixEnd_1016337 : Nat := 4983230072969 + 3 ^ 40 * 1016337 * 2
def baseEnd_1016337 : Nat := 521869387948695310513457

theorem tailTrace_1016337 : CollatzResearch.WordTrace tailWord_1016337 prefixEnd_1016337 521869387948695310513457 := by
  unfold tailWord_1016337
  simp only [CollatzResearch.WordTrace]
  refine ⟨37068855718992100385575265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24712570479328066923716843 37068855718992100385575265)
  ·
    refine ⟨27801641789244075289181449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37068855718992100385575265 27801641789244075289181449)
    ·
      refine ⟨20851231341933056466886087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27801641789244075289181449 20851231341933056466886087)
      ·
        refine ⟨31276847012899584700329131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20851231341933056466886087 31276847012899584700329131)
        ·
          refine ⟨46915270519349377050493697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31276847012899584700329131 46915270519349377050493697)
          ·
            refine ⟨35186452889512032787870273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46915270519349377050493697 35186452889512032787870273)
            ·
              refine ⟨26389839667134024590902705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35186452889512032787870273 26389839667134024590902705)
              ·
                refine ⟨19792379750350518443177029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26389839667134024590902705 19792379750350518443177029)
                ·
                  refine ⟨3711071203190722208095693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19792379750350518443177029 3711071203190722208095693)
                  ·
                    refine ⟨1391651701196520828035885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3711071203190722208095693 1391651701196520828035885)
                    ·
                      refine ⟨521869387948695310513457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1391651701196520828035885 521869387948695310513457)
                      ·
                        rfl

theorem cell23_1016337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 3].length) (baseStart_1016337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1016337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1016337 prefixEnd_1016337 := by exact prefixLift 1016337
  have htrace : WordTrace (prefixWord ++ tailWord_1016337) baseStart_1016337 baseEnd_1016337 := by
    simpa [prefixWord, tailWord_1016337, baseEnd_1016337] using wordTrace_append hprefix tailTrace_1016337
  have hstable : (prefixWord ++ tailWord_1016337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016337).length < 2 ^ (prefixWord ++ tailWord_1016337).sum := by decide
  have hdescent : baseEnd_1016337 < baseStart_1016337 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016357 : List Nat := [1, 3, 1, 2, 2, 1, 3, 1, 4, 5]
def baseStart_1016357 : Nat := 118140960795 + 1016357 * 2 ^ 59
def prefixEnd_1016357 : Nat := 4983230072969 + 3 ^ 40 * 1016357 * 2
def baseEnd_1016357 : Nat := 173959885853928410754455

theorem tailTrace_1016357 : CollatzResearch.WordTrace tailWord_1016357 prefixEnd_1016357 173959885853928410754455 := by
  unfold tailWord_1016357
  simp only [CollatzResearch.WordTrace]
  refine ⟨37069585178919643801303325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24713056785946429200868883 37069585178919643801303325)
  ·
    refine ⟨13901094442094866425488747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37069585178919643801303325 13901094442094866425488747)
    ·
      refine ⟨20851641663142299638233121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13901094442094866425488747 20851641663142299638233121)
      ·
        refine ⟨15638731247356724728674841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20851641663142299638233121 15638731247356724728674841)
        ·
          refine ⟨11729048435517543546506131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15638731247356724728674841 11729048435517543546506131)
          ·
            refine ⟨17593572653276315319759197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11729048435517543546506131 17593572653276315319759197)
            ·
              refine ⟨6597589744978618244909699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17593572653276315319759197 6597589744978618244909699)
              ·
                refine ⟨9896384617467927367364549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6597589744978618244909699 9896384617467927367364549)
                ·
                  refine ⟨1855572115775236381380853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9896384617467927367364549 1855572115775236381380853)
                  ·
                    refine ⟨173959885853928410754455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1855572115775236381380853 173959885853928410754455)
                    ·
                      rfl

theorem cell23_1016357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 1, 4, 5].length) (baseStart_1016357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1016357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1016357 prefixEnd_1016357 := by exact prefixLift 1016357
  have htrace : WordTrace (prefixWord ++ tailWord_1016357) baseStart_1016357 baseEnd_1016357 := by
    simpa [prefixWord, tailWord_1016357, baseEnd_1016357] using wordTrace_append hprefix tailTrace_1016357
  have hstable : (prefixWord ++ tailWord_1016357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016357).length < 2 ^ (prefixWord ++ tailWord_1016357).sum := by decide
  have hdescent : baseEnd_1016357 < baseStart_1016357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016372 : List Nat := [2, 5, 1, 3, 1, 1, 1, 3, 2, 2, 2]
def baseStart_1016372 : Nat := 118140960795 + 1016372 * 2 ^ 59
def prefixEnd_1016372 : Nat := 4983230072969 + 3 ^ 40 * 1016372 * 2
def baseEnd_1016372 : Nat := 521887359771602673575797

theorem tailTrace_1016372 : CollatzResearch.WordTrace tailWord_1016372 prefixEnd_1016372 521887359771602673575797 := by
  unfold tailWord_1016372
  simp only [CollatzResearch.WordTrace]
  refine ⟨18535066136932650681549685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24713421515910200908732913 18535066136932650681549685)
  ·
    refine ⟨1737662450337436001395283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18535066136932650681549685 1737662450337436001395283)
    ·
      refine ⟨2606493675506154002092925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1737662450337436001395283 2606493675506154002092925)
      ·
        refine ⟨977435128314807750784847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2606493675506154002092925 977435128314807750784847)
        ·
          refine ⟨1466152692472211626177271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 977435128314807750784847 1466152692472211626177271)
          ·
            refine ⟨2199229038708317439265907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1466152692472211626177271 2199229038708317439265907)
            ·
              refine ⟨3298843558062476158898861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2199229038708317439265907 3298843558062476158898861)
              ·
                refine ⟨1237066334273428559587073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3298843558062476158898861 1237066334273428559587073)
                ·
                  refine ⟨927799750705071419690305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1237066334273428559587073 927799750705071419690305)
                  ·
                    refine ⟨695849813028803564767729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 927799750705071419690305 695849813028803564767729)
                    ·
                      refine ⟨521887359771602673575797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 695849813028803564767729 521887359771602673575797)
                      ·
                        rfl

theorem cell23_1016372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_1016372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1016372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1016372 prefixEnd_1016372 := by exact prefixLift 1016372
  have htrace : WordTrace (prefixWord ++ tailWord_1016372) baseStart_1016372 baseEnd_1016372 := by
    simpa [prefixWord, tailWord_1016372, baseEnd_1016372] using wordTrace_append hprefix tailTrace_1016372
  have hstable : (prefixWord ++ tailWord_1016372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016372).length < 2 ^ (prefixWord ++ tailWord_1016372).sum := by decide
  have hdescent : baseEnd_1016372 < baseStart_1016372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016394 : List Nat := [3, 1, 2, 1, 1, 4, 1, 3, 2, 1, 4]
def baseStart_1016394 : Nat := 118140960795 + 1016394 * 2 ^ 59
def prefixEnd_1016394 : Nat := 4983230072969 + 3 ^ 40 * 1016394 * 2
def baseEnd_1016394 : Nat := 521898656346001587500695

theorem tailTrace_1016394 : CollatzResearch.WordTrace tailWord_1016394 prefixEnd_1016394 521898656346001587500695 := by
  unfold tailWord_1016394
  simp only [CollatzResearch.WordTrace]
  refine ⟨9267733669946399780100059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24713956453190399413600157 9267733669946399780100059)
  ·
    refine ⟨13901600504919599670150089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9267733669946399780100059 13901600504919599670150089)
    ·
      refine ⟨10426200378689699752612567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13901600504919599670150089 10426200378689699752612567)
      ·
        refine ⟨15639300568034549628918851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10426200378689699752612567 15639300568034549628918851)
        ·
          refine ⟨23458950852051824443378277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15639300568034549628918851 23458950852051824443378277)
          ·
            refine ⟨4398553284759717083133427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23458950852051824443378277 4398553284759717083133427)
            ·
              refine ⟨6597829927139575624700141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4398553284759717083133427 6597829927139575624700141)
              ·
                refine ⟨2474186222677340859262553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6597829927139575624700141 2474186222677340859262553)
                ·
                  refine ⟨1855639667008005644446915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2474186222677340859262553 1855639667008005644446915)
                  ·
                    refine ⟨2783459500512008466670373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1855639667008005644446915 2783459500512008466670373)
                    ·
                      refine ⟨521898656346001587500695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2783459500512008466670373 521898656346001587500695)
                      ·
                        rfl

theorem cell23_1016394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 3, 2, 1, 4].length) (baseStart_1016394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1016394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1016394 prefixEnd_1016394 := by exact prefixLift 1016394
  have htrace : WordTrace (prefixWord ++ tailWord_1016394) baseStart_1016394 baseEnd_1016394 := by
    simpa [prefixWord, tailWord_1016394, baseEnd_1016394] using wordTrace_append hprefix tailTrace_1016394
  have hstable : (prefixWord ++ tailWord_1016394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016394).length < 2 ^ (prefixWord ++ tailWord_1016394).sum := by decide
  have hdescent : baseEnd_1016394 < baseStart_1016394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016407 : List Nat := [1, 1, 3, 2, 2, 2, 2, 1, 2, 1, 6]
def baseStart_1016407 : Nat := 118140960795 + 1016407 * 2 ^ 59
def prefixEnd_1016407 : Nat := 4983230072969 + 3 ^ 40 * 1016407 * 2
def baseEnd_1016407 : Nat := 521905331594510036638135

theorem tailTrace_1016407 : CollatzResearch.WordTrace tailWord_1016407 prefixEnd_1016407 521905331594510036638135 := by
  unfold tailWord_1016407
  simp only [CollatzResearch.WordTrace]
  refine ⟨37071408828738502340623475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24714272552492334893748983 37071408828738502340623475)
  ·
    refine ⟨55607113243107753510935213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37071408828738502340623475 55607113243107753510935213)
    ·
      refine ⟨20852667466165407566600705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55607113243107753510935213 20852667466165407566600705)
      ·
        refine ⟨15639500599624055674950529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20852667466165407566600705 15639500599624055674950529)
        ·
          refine ⟨11729625449718041756212897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15639500599624055674950529 11729625449718041756212897)
          ·
            refine ⟨8797219087288531317159673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11729625449718041756212897 8797219087288531317159673)
            ·
              refine ⟨6597914315466398487869755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8797219087288531317159673 6597914315466398487869755)
              ·
                refine ⟨9896871473199597731804633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6597914315466398487869755 9896871473199597731804633)
                ·
                  refine ⟨7422653604899698298853475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9896871473199597731804633 7422653604899698298853475)
                  ·
                    refine ⟨11133980407349547448280213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7422653604899698298853475 11133980407349547448280213)
                    ·
                      refine ⟨521905331594510036638135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11133980407349547448280213 521905331594510036638135)
                      ·
                        rfl

theorem cell23_1016407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 1, 2, 1, 6].length) (baseStart_1016407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1016407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1016407 prefixEnd_1016407 := by exact prefixLift 1016407
  have htrace : WordTrace (prefixWord ++ tailWord_1016407) baseStart_1016407 baseEnd_1016407 := by
    simpa [prefixWord, tailWord_1016407, baseEnd_1016407] using wordTrace_append hprefix tailTrace_1016407
  have hstable : (prefixWord ++ tailWord_1016407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016407).length < 2 ^ (prefixWord ++ tailWord_1016407).sum := by decide
  have hdescent : baseEnd_1016407 < baseStart_1016407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016438 : List Nat := [5, 1, 1, 2, 3, 1, 1, 2, 3, 4]
def baseStart_1016438 : Nat := 118140960795 + 1016438 * 2 ^ 59
def prefixEnd_1016438 : Nat := 4983230072969 + 3 ^ 40 * 1016438 * 2
def baseEnd_1016438 : Nat := 173973749831599805116831

theorem tailTrace_1016438 : CollatzResearch.WordTrace tailWord_1016438 prefixEnd_1016438 173973749831599805116831 := by
  unfold tailWord_1016438
  simp only [CollatzResearch.WordTrace]
  refine ⟨2317033718226637164687623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24715026327750796423334645 2317033718226637164687623)
  ·
    refine ⟨3475550577339955747031435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2317033718226637164687623 3475550577339955747031435)
    ·
      refine ⟨5213325866009933620547153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3475550577339955747031435 5213325866009933620547153)
      ·
        refine ⟨3909994399507450215410365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5213325866009933620547153 3909994399507450215410365)
        ·
          refine ⟨1466247899815293830778887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3909994399507450215410365 1466247899815293830778887)
          ·
            refine ⟨2199371849722940746168331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1466247899815293830778887 2199371849722940746168331)
            ·
              refine ⟨3299057774584411119252497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2199371849722940746168331 3299057774584411119252497)
              ·
                refine ⟨2474293330938308339439373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3299057774584411119252497 2474293330938308339439373)
                ·
                  refine ⟨927859999101865627289765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2474293330938308339439373 927859999101865627289765)
                  ·
                    refine ⟨173973749831599805116831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 927859999101865627289765 173973749831599805116831)
                    ·
                      rfl

theorem cell23_1016438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 2, 3, 4].length) (baseStart_1016438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1016438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1016438 prefixEnd_1016438 := by exact prefixLift 1016438
  have htrace : WordTrace (prefixWord ++ tailWord_1016438) baseStart_1016438 baseEnd_1016438 := by
    simpa [prefixWord, tailWord_1016438, baseEnd_1016438] using wordTrace_append hprefix tailTrace_1016438
  have hstable : (prefixWord ++ tailWord_1016438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016438).length < 2 ^ (prefixWord ++ tailWord_1016438).sum := by decide
  have hdescent : baseEnd_1016438 < baseStart_1016438 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016457 : List Nat := [1, 2, 1, 1, 4, 1, 1, 1, 2, 4, 5]
def baseStart_1016457 : Nat := 118140960795 + 1016457 * 2 ^ 59
def prefixEnd_1016457 : Nat := 4983230072969 + 3 ^ 40 * 1016457 * 2
def baseEnd_1016457 : Nat := 521931005627234841012905

theorem tailTrace_1016457 : CollatzResearch.WordTrace tailWord_1016457 prefixEnd_1016457 521931005627234841012905 := by
  unfold tailWord_1016457
  simp only [CollatzResearch.WordTrace]
  refine ⟨37073232478557360879943625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24715488319038240586629083 37073232478557360879943625)
  ·
    refine ⟨27804924358918020659957719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37073232478557360879943625 27804924358918020659957719)
    ·
      refine ⟨41707386538377030989936579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27804924358918020659957719 41707386538377030989936579)
      ·
        refine ⟨62561079807565546484904869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41707386538377030989936579 62561079807565546484904869)
        ·
          refine ⟨11730202463918539965919663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62561079807565546484904869 11730202463918539965919663)
          ·
            refine ⟨17595303695877809948879495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11730202463918539965919663 17595303695877809948879495)
            ·
              refine ⟨26392955543816714923319243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17595303695877809948879495 26392955543816714923319243)
              ·
                refine ⟨39589433315725072384978865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26392955543816714923319243 39589433315725072384978865)
                ·
                  refine ⟨29692074986793804288734149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39589433315725072384978865 29692074986793804288734149)
                  ·
                    refine ⟨5567264060023838304137653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29692074986793804288734149 5567264060023838304137653)
                    ·
                      refine ⟨521931005627234841012905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5567264060023838304137653 521931005627234841012905)
                      ·
                        rfl

theorem cell23_1016457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 4, 5].length) (baseStart_1016457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1016457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1016457 prefixEnd_1016457 := by exact prefixLift 1016457
  have htrace : WordTrace (prefixWord ++ tailWord_1016457) baseStart_1016457 baseEnd_1016457 := by
    simpa [prefixWord, tailWord_1016457, baseEnd_1016457] using wordTrace_append hprefix tailTrace_1016457
  have hstable : (prefixWord ++ tailWord_1016457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016457).length < 2 ^ (prefixWord ++ tailWord_1016457).sum := by decide
  have hdescent : baseEnd_1016457 < baseStart_1016457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016468 : List Nat := [2, 4, 2, 2, 1, 3, 1, 2, 6]
def baseStart_1016468 : Nat := 118140960795 + 1016468 * 2 ^ 59
def prefixEnd_1016468 : Nat := 4983230072969 + 3 ^ 40 * 1016468 * 2
def baseEnd_1016468 : Nat := 57992961546048255330595

theorem tailTrace_1016468 : CollatzResearch.WordTrace tailWord_1016468 prefixEnd_1016468 57992961546048255330595 := by
  unfold tailWord_1016468
  simp only [CollatzResearch.WordTrace]
  refine ⟨18536816840758754879297029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24715755787678339839062705 18536816840758754879297029)
  ·
    refine ⟨3475653157642266539868193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18536816840758754879297029 3475653157642266539868193)
    ·
      refine ⟨2606739868231699904901145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3475653157642266539868193 2606739868231699904901145)
      ·
        refine ⟨1955054901173774928675859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2606739868231699904901145 1955054901173774928675859)
        ·
          refine ⟨2932582351760662393013789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1955054901173774928675859 2932582351760662393013789)
          ·
            refine ⟨1099718381910248397380171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2932582351760662393013789 1099718381910248397380171)
            ·
              refine ⟨1649577572865372596070257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1099718381910248397380171 1649577572865372596070257)
              ·
                refine ⟨1237183179649029447052693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1649577572865372596070257 1237183179649029447052693)
                ·
                  refine ⟨57992961546048255330595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1237183179649029447052693 57992961546048255330595)
                  ·
                    rfl

theorem cell23_1016468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 1, 2, 6].length) (baseStart_1016468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1016468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1016468 prefixEnd_1016468 := by exact prefixLift 1016468
  have htrace : WordTrace (prefixWord ++ tailWord_1016468) baseStart_1016468 baseEnd_1016468 := by
    simpa [prefixWord, tailWord_1016468, baseEnd_1016468] using wordTrace_append hprefix tailTrace_1016468
  have hstable : (prefixWord ++ tailWord_1016468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016468).length < 2 ^ (prefixWord ++ tailWord_1016468).sum := by decide
  have hdescent : baseEnd_1016468 < baseStart_1016468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016471 : List Nat := [1, 1, 3, 3, 2, 1, 2, 1, 4, 3, 2]
def baseStart_1016471 : Nat := 118140960795 + 1016471 * 2 ^ 59
def prefixEnd_1016471 : Nat := 4983230072969 + 3 ^ 40 * 1016471 * 2
def baseEnd_1016471 : Nat := 521938194356397786237841

theorem tailTrace_1016471 : CollatzResearch.WordTrace tailWord_1016471 prefixEnd_1016471 521938194356397786237841 := by
  unfold tailWord_1016471
  simp only [CollatzResearch.WordTrace]
  refine ⟨37073743100506641270953267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24715828733671094180635511 37073743100506641270953267)
  ·
    refine ⟨55610614650759961906429901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37073743100506641270953267 55610614650759961906429901)
    ·
      refine ⟨20853980494034985714911213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55610614650759961906429901 20853980494034985714911213)
      ·
        refine ⟨7820242685263119643091705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20853980494034985714911213 7820242685263119643091705)
        ·
          refine ⟨5865182013947339732318779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7820242685263119643091705 5865182013947339732318779)
          ·
            refine ⟨8797773020921009598478169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5865182013947339732318779 8797773020921009598478169)
            ·
              refine ⟨6598329765690757198858627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8797773020921009598478169 6598329765690757198858627)
              ·
                refine ⟨9897494648536135798287941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6598329765690757198858627 9897494648536135798287941)
                ·
                  refine ⟨1855780246600525462178989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9897494648536135798287941 1855780246600525462178989)
                  ·
                    refine ⟨695917592475197048317121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1855780246600525462178989 695917592475197048317121)
                    ·
                      refine ⟨521938194356397786237841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 695917592475197048317121 521938194356397786237841)
                      ·
                        rfl

theorem cell23_1016471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 1, 4, 3, 2].length) (baseStart_1016471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1016471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1016471 prefixEnd_1016471 := by exact prefixLift 1016471
  have htrace : WordTrace (prefixWord ++ tailWord_1016471) baseStart_1016471 baseEnd_1016471 := by
    simpa [prefixWord, tailWord_1016471, baseEnd_1016471] using wordTrace_append hprefix tailTrace_1016471
  have hstable : (prefixWord ++ tailWord_1016471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016471).length < 2 ^ (prefixWord ++ tailWord_1016471).sum := by decide
  have hdescent : baseEnd_1016471 < baseStart_1016471 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016524 : List Nat := [2, 2, 1, 5, 1, 1, 11]
def baseStart_1016524 : Nat := 118140960795 + 1016524 * 2 ^ 59
def prefixEnd_1016524 : Nat := 4983230072969 + 3 ^ 40 * 1016524 * 2
def baseEnd_1016524 : Nat := 6444017392976371344137

theorem tailTrace_1016524 : CollatzResearch.WordTrace tailWord_1016524 prefixEnd_1016524 6444017392976371344137 := by
  unfold tailWord_1016524
  simp only [CollatzResearch.WordTrace]
  refine ⟨18537838084657315661316313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24717117446209754215088417 18537838084657315661316313)
  ·
    refine ⟨13903378563492986745987235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18537838084657315661316313 13903378563492986745987235)
    ·
      refine ⟨20855067845239480118980853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13903378563492986745987235 20855067845239480118980853)
      ·
        refine ⟨1955162610491201261154455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20855067845239480118980853 1955162610491201261154455)
        ·
          refine ⟨2932743915736801891731683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1955162610491201261154455 2932743915736801891731683)
          ·
            refine ⟨4399115873605202837597525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2932743915736801891731683 4399115873605202837597525)
            ·
              refine ⟨6444017392976371344137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 4399115873605202837597525 6444017392976371344137)
              ·
                rfl

theorem cell23_1016524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 11].length) (baseStart_1016524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1016524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1016524 prefixEnd_1016524 := by exact prefixLift 1016524
  have htrace : WordTrace (prefixWord ++ tailWord_1016524) baseStart_1016524 baseEnd_1016524 := by
    simpa [prefixWord, tailWord_1016524, baseEnd_1016524] using wordTrace_append hprefix tailTrace_1016524
  have hstable : (prefixWord ++ tailWord_1016524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016524).length < 2 ^ (prefixWord ++ tailWord_1016524).sum := by decide
  have hdescent : baseEnd_1016524 < baseStart_1016524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016535 : List Nat := [1, 1, 3, 2, 1, 6, 1, 1, 3, 2, 2]
def baseStart_1016535 : Nat := 118140960795 + 1016535 * 2 ^ 59
def prefixEnd_1016535 : Nat := 4983230072969 + 3 ^ 40 * 1016535 * 2
def baseEnd_1016535 : Nat := 521971057118285535837547

theorem tailTrace_1016535 : CollatzResearch.WordTrace tailWord_1016535 prefixEnd_1016535 521971057118285535837547 := by
  unfold tailWord_1016535
  simp only [CollatzResearch.WordTrace]
  refine ⟨37076077372274780201283059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24717384914849853467522039 37076077372274780201283059)
  ·
    refine ⟨55614116058412170301924589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37076077372274780201283059 55614116058412170301924589)
    ·
      refine ⟨20855293521904563863221721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55614116058412170301924589 20855293521904563863221721)
      ·
        refine ⟨15641470141428422897416291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20855293521904563863221721 15641470141428422897416291)
        ·
          refine ⟨23462205212142634346124437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15641470141428422897416291 23462205212142634346124437)
          ·
            refine ⟨1099790869319185984974583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 23462205212142634346124437 1099790869319185984974583)
            ·
              refine ⟨1649686303978778977461875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1099790869319185984974583 1649686303978778977461875)
              ·
                refine ⟨2474529455968168466192813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1649686303978778977461875 2474529455968168466192813)
                ·
                  refine ⟨927948545988063174822305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2474529455968168466192813 927948545988063174822305)
                  ·
                    refine ⟨695961409491047381116729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 927948545988063174822305 695961409491047381116729)
                    ·
                      refine ⟨521971057118285535837547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 695961409491047381116729 521971057118285535837547)
                      ·
                        rfl

theorem cell23_1016535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 1, 1, 3, 2, 2].length) (baseStart_1016535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1016535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1016535 prefixEnd_1016535 := by exact prefixLift 1016535
  have htrace : WordTrace (prefixWord ++ tailWord_1016535) baseStart_1016535 baseEnd_1016535 := by
    simpa [prefixWord, tailWord_1016535, baseEnd_1016535] using wordTrace_append hprefix tailTrace_1016535
  have hstable : (prefixWord ++ tailWord_1016535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016535).length < 2 ^ (prefixWord ++ tailWord_1016535).sum := by decide
  have hdescent : baseEnd_1016535 < baseStart_1016535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016545 : List Nat := [1, 2, 3, 1, 4, 3, 2, 1, 2, 4]
def baseStart_1016545 : Nat := 118140960795 + 1016545 * 2 ^ 59
def prefixEnd_1016545 : Nat := 4983230072969 + 3 ^ 40 * 1016545 * 2
def baseEnd_1016545 : Nat := 173992063974943498904167

theorem tailTrace_1016545 : CollatzResearch.WordTrace tailWord_1016545 prefixEnd_1016545 173992063974943498904167 := by
  unfold tailWord_1016545
  simp only [CollatzResearch.WordTrace]
  refine ⟨37076442102238551909147089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24717628068159034606098059 37076442102238551909147089)
  ·
    refine ⟨27807331576678913931860317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37076442102238551909147089 27807331576678913931860317)
    ·
      refine ⟨10427749341254592724447619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27807331576678913931860317 10427749341254592724447619)
      ·
        refine ⟨15641624011881889086671429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10427749341254592724447619 15641624011881889086671429)
        ·
          refine ⟨2932804502227854203750893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15641624011881889086671429 2932804502227854203750893)
          ·
            refine ⟨1099801688335445326406585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2932804502227854203750893 1099801688335445326406585)
            ·
              refine ⟨824851266251583994804939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1099801688335445326406585 824851266251583994804939)
              ·
                refine ⟨1237276899377375992207409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 824851266251583994804939 1237276899377375992207409)
                ·
                  refine ⟨927957674533031994155557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1237276899377375992207409 927957674533031994155557)
                  ·
                    refine ⟨173992063974943498904167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 927957674533031994155557 173992063974943498904167)
                    ·
                      rfl

theorem cell23_1016545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 2, 1, 2, 4].length) (baseStart_1016545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1016545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1016545 prefixEnd_1016545 := by exact prefixLift 1016545
  have htrace : WordTrace (prefixWord ++ tailWord_1016545) baseStart_1016545 baseEnd_1016545 := by
    simpa [prefixWord, tailWord_1016545, baseEnd_1016545] using wordTrace_append hprefix tailTrace_1016545
  have hstable : (prefixWord ++ tailWord_1016545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016545).length < 2 ^ (prefixWord ++ tailWord_1016545).sum := by decide
  have hdescent : baseEnd_1016545 < baseStart_1016545 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016591 : List Nat := [1, 1, 2, 1, 1, 1, 5, 2, 3, 4, 2]
def baseStart_1016591 : Nat := 118140960795 + 1016591 * 2 ^ 59
def prefixEnd_1016591 : Nat := 4983230072969 + 3 ^ 40 * 1016591 * 2
def baseEnd_1016591 : Nat := 521999812034937316737289

theorem tailTrace_1016591 : CollatzResearch.WordTrace tailWord_1016591 prefixEnd_1016591 521999812034937316737289 := by
  unfold tailWord_1016591
  simp only [CollatzResearch.WordTrace]
  refine ⟨37078119860071901765321627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24718746573381267843547751 37078119860071901765321627)
  ·
    refine ⟨55617179790107852647982441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37078119860071901765321627 55617179790107852647982441)
    ·
      refine ⟨41712884842580889485986831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55617179790107852647982441 41712884842580889485986831)
      ·
        refine ⟨62569327263871334228980247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41712884842580889485986831 62569327263871334228980247)
        ·
          refine ⟨93853990895807001343470371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62569327263871334228980247 93853990895807001343470371)
          ·
            refine ⟨140780986343710502015205557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93853990895807001343470371 140780986343710502015205557)
            ·
              refine ⟨13198217469722859563925521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 140780986343710502015205557 13198217469722859563925521)
              ·
                refine ⟨9898663102292144672944141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13198217469722859563925521 9898663102292144672944141)
                ·
                  refine ⟨3711998663359554252354053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9898663102292144672944141 3711998663359554252354053)
                  ·
                    refine ⟨695999749379916422316385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3711998663359554252354053 695999749379916422316385)
                    ·
                      refine ⟨521999812034937316737289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 695999749379916422316385 521999812034937316737289)
                      ·
                        rfl

theorem cell23_1016591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 2, 3, 4, 2].length) (baseStart_1016591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1016591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1016591 prefixEnd_1016591 := by exact prefixLift 1016591
  have htrace : WordTrace (prefixWord ++ tailWord_1016591) baseStart_1016591 baseEnd_1016591 := by
    simpa [prefixWord, tailWord_1016591, baseEnd_1016591] using wordTrace_append hprefix tailTrace_1016591
  have hstable : (prefixWord ++ tailWord_1016591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016591).length < 2 ^ (prefixWord ++ tailWord_1016591).sum := by decide
  have hdescent : baseEnd_1016591 < baseStart_1016591 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016608 : List Nat := [2, 1, 1, 5, 1, 2, 1, 3, 1, 4, 2]
def baseStart_1016608 : Nat := 118140960795 + 1016608 * 2 ^ 59
def prefixEnd_1016608 : Nat := 4983230072969 + 3 ^ 40 * 1016608 * 2
def baseEnd_1016608 : Nat := 522008541206063750224711

theorem tailTrace_1016608 : CollatzResearch.WordTrace tailWord_1016608 prefixEnd_1016608 522008541206063750224711 := by
  unfold tailWord_1016608
  simp only [CollatzResearch.WordTrace]
  refine ⟨18539369950505156834345239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24719159934006875779126985 18539369950505156834345239)
  ·
    refine ⟨27809054925757735251517859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18539369950505156834345239 27809054925757735251517859)
    ·
      refine ⟨41713582388636602877276789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27809054925757735251517859 41713582388636602877276789)
      ·
        refine ⟨3910648348934681519744699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41713582388636602877276789 3910648348934681519744699)
        ·
          refine ⟨5865972523402022279617049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3910648348934681519744699 5865972523402022279617049)
          ·
            refine ⟨4399479392551516709712787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5865972523402022279617049 4399479392551516709712787)
            ·
              refine ⟨6599219088827275064569181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4399479392551516709712787 6599219088827275064569181)
              ·
                refine ⟨2474707158310228149213443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6599219088827275064569181 2474707158310228149213443)
                ·
                  refine ⟨3712060737465342223820165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2474707158310228149213443 3712060737465342223820165)
                  ·
                    refine ⟨696011388274751666966281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3712060737465342223820165 696011388274751666966281)
                    ·
                      refine ⟨522008541206063750224711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 696011388274751666966281 522008541206063750224711)
                      ·
                        rfl

theorem cell23_1016608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 3, 1, 4, 2].length) (baseStart_1016608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1016608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1016608 prefixEnd_1016608 := by exact prefixLift 1016608
  have htrace : WordTrace (prefixWord ++ tailWord_1016608) baseStart_1016608 baseEnd_1016608 := by
    simpa [prefixWord, tailWord_1016608, baseEnd_1016608] using wordTrace_append hprefix tailTrace_1016608
  have hstable : (prefixWord ++ tailWord_1016608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016608).length < 2 ^ (prefixWord ++ tailWord_1016608).sum := by decide
  have hdescent : baseEnd_1016608 < baseStart_1016608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016691 : List Nat := [1, 1, 1, 2, 2, 1, 4, 2, 5, 4]
def baseStart_1016691 : Nat := 118140960795 + 1016691 * 2 ^ 59
def prefixEnd_1016691 : Nat := 4983230072969 + 3 ^ 40 * 1016691 * 2
def baseEnd_1016691 : Nat := 174017053366795641828943

theorem tailTrace_1016691 : CollatzResearch.WordTrace tailWord_1016691 prefixEnd_1016691 174017053366795641828943 := by
  unfold tailWord_1016691
  simp only [CollatzResearch.WordTrace]
  refine ⟨37081767159709618843961927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24721178106473079229307951 37081767159709618843961927)
  ·
    refine ⟨55622650739564428265942891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37081767159709618843961927 55622650739564428265942891)
    ·
      refine ⟨83433976109346642398914337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55622650739564428265942891 83433976109346642398914337)
      ·
        refine ⟨62575482082009981799185753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83433976109346642398914337 62575482082009981799185753)
        ·
          refine ⟨46931611561507486349389315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62575482082009981799185753 46931611561507486349389315)
          ·
            refine ⟨70397417342261229524083973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46931611561507486349389315 70397417342261229524083973)
            ·
              refine ⟨13199515751673980535765745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70397417342261229524083973 13199515751673980535765745)
              ·
                refine ⟨9899636813755485401824309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13199515751673980535765745 9899636813755485401824309)
                ·
                  refine ⟨928090951289576756421029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9899636813755485401824309 928090951289576756421029)
                  ·
                    refine ⟨174017053366795641828943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 928090951289576756421029 174017053366795641828943)
                    ·
                      rfl

theorem cell23_1016691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 2, 5, 4].length) (baseStart_1016691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1016691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1016691 prefixEnd_1016691 := by exact prefixLift 1016691
  have htrace : WordTrace (prefixWord ++ tailWord_1016691) baseStart_1016691 baseEnd_1016691 := by
    simpa [prefixWord, tailWord_1016691, baseEnd_1016691] using wordTrace_append hprefix tailTrace_1016691
  have hstable : (prefixWord ++ tailWord_1016691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016691).length < 2 ^ (prefixWord ++ tailWord_1016691).sum := by decide
  have hdescent : baseEnd_1016691 < baseStart_1016691 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016735 : List Nat := [1, 1, 2, 5, 2, 2, 2, 1, 2, 2, 3]
def baseStart_1016735 : Nat := 118140960795 + 1016735 * 2 ^ 59
def prefixEnd_1016735 : Nat := 4983230072969 + 3 ^ 40 * 1016735 * 2
def baseEnd_1016735 : Nat := 522073753249184753336627

theorem tailTrace_1016735 : CollatzResearch.WordTrace tailWord_1016735 prefixEnd_1016735 522073753249184753336627 := by
  unfold tailWord_1016735
  simp only [CollatzResearch.WordTrace]
  refine ⟨37083371971550214358563659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24722247981033476239042439 37083371971550214358563659)
  ·
    refine ⟨55625057957325321537845489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37083371971550214358563659 55625057957325321537845489)
    ·
      refine ⟨41718793467993991153384117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55625057957325321537845489 41718793467993991153384117)
      ·
        refine ⟨3911136887624436670629761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41718793467993991153384117 3911136887624436670629761)
        ·
          refine ⟨2933352665718327502972321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3911136887624436670629761 2933352665718327502972321)
          ·
            refine ⟨2200014499288745627229241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2933352665718327502972321 2200014499288745627229241)
            ·
              refine ⟨1650010874466559220421931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2200014499288745627229241 1650010874466559220421931)
              ·
                refine ⟨2475016311699838830632897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1650010874466559220421931 2475016311699838830632897)
                ·
                  refine ⟨1856262233774879122974673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2475016311699838830632897 1856262233774879122974673)
                  ·
                    refine ⟨1392196675331159342231005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1856262233774879122974673 1392196675331159342231005)
                    ·
                      refine ⟨522073753249184753336627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1392196675331159342231005 522073753249184753336627)
                      ·
                        rfl

theorem cell23_1016735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 2, 1, 2, 2, 3].length) (baseStart_1016735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1016735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1016735 prefixEnd_1016735 := by exact prefixLift 1016735
  have htrace : WordTrace (prefixWord ++ tailWord_1016735) baseStart_1016735 baseEnd_1016735 := by
    simpa [prefixWord, tailWord_1016735, baseEnd_1016735] using wordTrace_append hprefix tailTrace_1016735
  have hstable : (prefixWord ++ tailWord_1016735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016735).length < 2 ^ (prefixWord ++ tailWord_1016735).sum := by decide
  have hdescent : baseEnd_1016735 < baseStart_1016735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016748 : List Nat := [2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 3]
def baseStart_1016748 : Nat := 118140960795 + 1016748 * 2 ^ 59
def prefixEnd_1016748 : Nat := 4983230072969 + 3 ^ 40 * 1016748 * 2
def baseEnd_1016748 : Nat := 522080428497693202474067

theorem tailTrace_1016748 : CollatzResearch.WordTrace tailWord_1016748 prefixEnd_1016748 522080428497693202474067 := by
  unfold tailWord_1016748
  simp only [CollatzResearch.WordTrace]
  refine ⟨18541923060251558789393449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24722564080335411719191265 18541923060251558789393449)
  ·
    refine ⟨13906442295188669092045087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18541923060251558789393449 13906442295188669092045087)
    ·
      refine ⟨20859663442783003638067631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13906442295188669092045087 20859663442783003638067631)
      ·
        refine ⟨31289495164174505457101447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20859663442783003638067631 31289495164174505457101447)
        ·
          refine ⟨46934242746261758185652171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31289495164174505457101447 46934242746261758185652171)
          ·
            refine ⟨70401364119392637278478257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46934242746261758185652171 70401364119392637278478257)
            ·
              refine ⟨52801023089544477958858693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70401364119392637278478257 52801023089544477958858693)
              ·
                refine ⟨9900191829289589617286005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52801023089544477958858693 9900191829289589617286005)
                ·
                  refine ⟨928142983995899026620563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9900191829289589617286005 928142983995899026620563)
                  ·
                    refine ⟨1392214475993848539930845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 928142983995899026620563 1392214475993848539930845)
                    ·
                      refine ⟨522080428497693202474067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1392214475993848539930845 522080428497693202474067)
                      ·
                        rfl

theorem cell23_1016748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 3].length) (baseStart_1016748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1016748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1016748 prefixEnd_1016748 := by exact prefixLift 1016748
  have htrace : WordTrace (prefixWord ++ tailWord_1016748) baseStart_1016748 baseEnd_1016748 := by
    simpa [prefixWord, tailWord_1016748, baseEnd_1016748] using wordTrace_append hprefix tailTrace_1016748
  have hstable : (prefixWord ++ tailWord_1016748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016748).length < 2 ^ (prefixWord ++ tailWord_1016748).sum := by decide
  have hdescent : baseEnd_1016748 < baseStart_1016748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016791 : List Nat := [1, 1, 3, 2, 1, 1, 2, 1, 5, 1, 5]
def baseStart_1016791 : Nat := 118140960795 + 1016791 * 2 ^ 59
def prefixEnd_1016791 : Nat := 4983230072969 + 3 ^ 40 * 1016791 * 2
def baseEnd_1016791 : Nat := 522102508165836534236369

theorem tailTrace_1016791 : CollatzResearch.WordTrace tailWord_1016791 prefixEnd_1016791 522102508165836534236369 := by
  unfold tailWord_1016791
  simp only [CollatzResearch.WordTrace]
  refine ⟨37085414459347335922602227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24723609639564890615068151 37085414459347335922602227)
  ·
    refine ⟨55628121689021003883903341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37085414459347335922602227 55628121689021003883903341)
    ·
      refine ⟨20860545633382876456463753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55628121689021003883903341 20860545633382876456463753)
      ·
        refine ⟨15645409225037157342347815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20860545633382876456463753 15645409225037157342347815)
        ·
          refine ⟨23468113837555736013521723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15645409225037157342347815 23468113837555736013521723)
          ·
            refine ⟨35202170756333604020282585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23468113837555736013521723 35202170756333604020282585)
            ·
              refine ⟨26401628067250203015211939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35202170756333604020282585 26401628067250203015211939)
              ·
                refine ⟨39602442100875304522817909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26401628067250203015211939 39602442100875304522817909)
                ·
                  refine ⟨3712728946957059799014179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39602442100875304522817909 3712728946957059799014179)
                  ·
                    refine ⟨5569093420435589698521269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3712728946957059799014179 5569093420435589698521269)
                    ·
                      refine ⟨522102508165836534236369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5569093420435589698521269 522102508165836534236369)
                      ·
                        rfl

theorem cell23_1016791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 5, 1, 5].length) (baseStart_1016791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1016791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1016791 prefixEnd_1016791 := by exact prefixLift 1016791
  have htrace : WordTrace (prefixWord ++ tailWord_1016791) baseStart_1016791 baseEnd_1016791 := by
    simpa [prefixWord, tailWord_1016791, baseEnd_1016791] using wordTrace_append hprefix tailTrace_1016791
  have hstable : (prefixWord ++ tailWord_1016791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016791).length < 2 ^ (prefixWord ++ tailWord_1016791).sum := by decide
  have hdescent : baseEnd_1016791 < baseStart_1016791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016792 : List Nat := [2, 1, 2, 2, 2, 5, 1, 1, 2, 3, 2]
def baseStart_1016792 : Nat := 118140960795 + 1016792 * 2 ^ 59
def prefixEnd_1016792 : Nat := 4983230072969 + 3 ^ 40 * 1016792 * 2
def baseEnd_1016792 : Nat := 522103021646491030323865

theorem tailTrace_1016792 : CollatzResearch.WordTrace tailWord_1016792 prefixEnd_1016792 522103021646491030323865 := by
  unfold tailWord_1016792
  simp only [CollatzResearch.WordTrace]
  refine ⟨18542725466171856546694315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24723633954895808728925753 18542725466171856546694315)
  ·
    refine ⟨27814088199257784820041473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18542725466171856546694315 27814088199257784820041473)
    ·
      refine ⟨20860566149443338615031105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27814088199257784820041473 20860566149443338615031105)
      ·
        refine ⟨15645424612082503961273329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20860566149443338615031105 15645424612082503961273329)
        ·
          refine ⟨11734068459061877970954997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15645424612082503961273329 11734068459061877970954997)
          ·
            refine ⟨1100068918037051059777031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11734068459061877970954997 1100068918037051059777031)
            ·
              refine ⟨1650103377055576589665547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1100068918037051059777031 1650103377055576589665547)
              ·
                refine ⟨2475155065583364884498321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1650103377055576589665547 2475155065583364884498321)
                ·
                  refine ⟨1856366299187523663373741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2475155065583364884498321 1856366299187523663373741)
                  ·
                    refine ⟨696137362195321373765153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1856366299187523663373741 696137362195321373765153)
                    ·
                      refine ⟨522103021646491030323865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 696137362195321373765153 522103021646491030323865)
                      ·
                        rfl

theorem cell23_1016792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 1, 1, 2, 3, 2].length) (baseStart_1016792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1016792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1016792 prefixEnd_1016792 := by exact prefixLift 1016792
  have htrace : WordTrace (prefixWord ++ tailWord_1016792) baseStart_1016792 baseEnd_1016792 := by
    simpa [prefixWord, tailWord_1016792, baseEnd_1016792] using wordTrace_append hprefix tailTrace_1016792
  have hstable : (prefixWord ++ tailWord_1016792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016792).length < 2 ^ (prefixWord ++ tailWord_1016792).sum := by decide
  have hdescent : baseEnd_1016792 < baseStart_1016792 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016799 : List Nat := [1, 1, 2, 3, 5, 1, 2, 3, 1, 1, 3]
def baseStart_1016799 : Nat := 118140960795 + 1016799 * 2 ^ 59
def prefixEnd_1016799 : Nat := 4983230072969 + 3 ^ 40 * 1016799 * 2
def baseEnd_1016799 : Nat := 522106616011072502936333

theorem tailTrace_1016799 : CollatzResearch.WordTrace tailWord_1016799 prefixEnd_1016799 522106616011072502936333 := by
  unfold tailWord_1016799
  simp only [CollatzResearch.WordTrace]
  refine ⟨37085706243318353288893451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24723804162212235525928967 37085706243318353288893451)
  ·
    refine ⟨55628559364977529933340177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37085706243318353288893451 55628559364977529933340177)
    ·
      refine ⟨41721419523733147450005133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55628559364977529933340177 41721419523733147450005133)
      ·
        refine ⟨15645532321399930293751925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41721419523733147450005133 15645532321399930293751925)
        ·
          refine ⟨1466768655131243465039243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15645532321399930293751925 1466768655131243465039243)
          ·
            refine ⟨2200152982696865197558865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1466768655131243465039243 2200152982696865197558865)
            ·
              refine ⟨1650114737022648898169149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2200152982696865197558865 1650114737022648898169149)
              ·
                refine ⟨618793026383493336813431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1650114737022648898169149 618793026383493336813431)
                ·
                  refine ⟨928189539575240005220147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 618793026383493336813431 928189539575240005220147)
                  ·
                    refine ⟨1392284309362860007830221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 928189539575240005220147 1392284309362860007830221)
                    ·
                      refine ⟨522106616011072502936333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1392284309362860007830221 522106616011072502936333)
                      ·
                        rfl

theorem cell23_1016799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 2, 3, 1, 1, 3].length) (baseStart_1016799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1016799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1016799 prefixEnd_1016799 := by exact prefixLift 1016799
  have htrace : WordTrace (prefixWord ++ tailWord_1016799) baseStart_1016799 baseEnd_1016799 := by
    simpa [prefixWord, tailWord_1016799, baseEnd_1016799] using wordTrace_append hprefix tailTrace_1016799
  have hstable : (prefixWord ++ tailWord_1016799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016799).length < 2 ^ (prefixWord ++ tailWord_1016799).sum := by decide
  have hdescent : baseEnd_1016799 < baseStart_1016799 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016801 : List Nat := [1, 2, 3, 1, 2, 1, 1, 2, 3, 1, 6]
def baseStart_1016801 : Nat := 118140960795 + 1016801 * 2 ^ 59
def prefixEnd_1016801 : Nat := 4983230072969 + 3 ^ 40 * 1016801 * 2
def baseEnd_1016801 : Nat := 522107642972381495111323

theorem tailTrace_1016801 : CollatzResearch.WordTrace tailWord_1016801 prefixEnd_1016801 522107642972381495111323 := by
  unfold tailWord_1016801
  simp only [CollatzResearch.WordTrace]
  refine ⟨37085779189311107630466257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24723852792874071753644171 37085779189311107630466257)
  ·
    refine ⟨27814334391983330722849693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37085779189311107630466257 27814334391983330722849693)
    ·
      refine ⟨10430375396993749021068635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27814334391983330722849693 10430375396993749021068635)
      ·
        refine ⟨15645563095490623531602953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10430375396993749021068635 15645563095490623531602953)
        ·
          refine ⟨11734172321617967648702215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15645563095490623531602953 11734172321617967648702215)
          ·
            refine ⟨17601258482426951473053323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11734172321617967648702215 17601258482426951473053323)
            ·
              refine ⟨26401887723640427209579985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17601258482426951473053323 26401887723640427209579985)
              ·
                refine ⟨19801415792730320407184989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26401887723640427209579985 19801415792730320407184989)
                ·
                  refine ⟨7425530922273870152694371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19801415792730320407184989 7425530922273870152694371)
                  ·
                    refine ⟨11138296383410805229041557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7425530922273870152694371 11138296383410805229041557)
                    ·
                      refine ⟨522107642972381495111323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11138296383410805229041557 522107642972381495111323)
                      ·
                        rfl

theorem cell23_1016801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 3, 1, 6].length) (baseStart_1016801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1016801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1016801 prefixEnd_1016801 := by exact prefixLift 1016801
  have htrace : WordTrace (prefixWord ++ tailWord_1016801) baseStart_1016801 baseEnd_1016801 := by
    simpa [prefixWord, tailWord_1016801, baseEnd_1016801] using wordTrace_append hprefix tailTrace_1016801
  have hstable : (prefixWord ++ tailWord_1016801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016801).length < 2 ^ (prefixWord ++ tailWord_1016801).sum := by decide
  have hdescent : baseEnd_1016801 < baseStart_1016801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016802 : List Nat := [3, 3, 3, 1, 1, 2, 1, 3, 1, 5]
def baseStart_1016802 : Nat := 118140960795 + 1016802 * 2 ^ 59
def prefixEnd_1016802 : Nat := 4983230072969 + 3 ^ 40 * 1016802 * 2
def baseEnd_1016802 : Nat := 174036052151011997066273

theorem tailTrace_1016802 : CollatzResearch.WordTrace tailWord_1016802 prefixEnd_1016802 174036052151011997066273 := by
  unfold tailWord_1016802
  simp only [CollatzResearch.WordTrace]
  refine ⟨9271453915576871200313165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24723877108204989867501773 9271453915576871200313165)
  ·
    refine ⟨3476795218341326700117437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9271453915576871200313165 3476795218341326700117437)
    ·
      refine ⟨1303798206877997512544039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3476795218341326700117437 1303798206877997512544039)
      ·
        refine ⟨1955697310316996268816059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1303798206877997512544039 1955697310316996268816059)
        ·
          refine ⟨2933545965475494403224089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1955697310316996268816059 2933545965475494403224089)
          ·
            refine ⟨2200159474106620802418067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2933545965475494403224089 2200159474106620802418067)
            ·
              refine ⟨3300239211159931203627101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2200159474106620802418067 3300239211159931203627101)
              ·
                refine ⟨1237589704184974201360163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3300239211159931203627101 1237589704184974201360163)
                ·
                  refine ⟨1856384556277461302040245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1237589704184974201360163 1856384556277461302040245)
                  ·
                    refine ⟨174036052151011997066273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1856384556277461302040245 174036052151011997066273)
                    ·
                      rfl

theorem cell23_1016802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_1016802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1016802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1016802 prefixEnd_1016802 := by exact prefixLift 1016802
  have htrace : WordTrace (prefixWord ++ tailWord_1016802) baseStart_1016802 baseEnd_1016802 := by
    simpa [prefixWord, tailWord_1016802, baseEnd_1016802] using wordTrace_append hprefix tailTrace_1016802
  have hstable : (prefixWord ++ tailWord_1016802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016802).length < 2 ^ (prefixWord ++ tailWord_1016802).sum := by decide
  have hdescent : baseEnd_1016802 < baseStart_1016802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016815 : List Nat := [1, 1, 2, 1, 4, 3, 3, 2, 2, 4]
def baseStart_1016815 : Nat := 118140960795 + 1016815 * 2 ^ 59
def prefixEnd_1016815 : Nat := 4983230072969 + 3 ^ 40 * 1016815 * 2
def baseEnd_1016815 : Nat := 174038277233848146778753

theorem tailTrace_1016815 : CollatzResearch.WordTrace tailWord_1016815 prefixEnd_1016815 174038277233848146778753 := by
  unfold tailWord_1016815
  simp only [CollatzResearch.WordTrace]
  refine ⟨37086289811260388021475899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24724193207506925347650599 37086289811260388021475899)
  ·
    refine ⟨55629434716890582032213849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37086289811260388021475899 55629434716890582032213849)
    ·
      refine ⟨41722076037667936524160387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55629434716890582032213849 41722076037667936524160387)
      ·
        refine ⟨62583114056501904786240581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41722076037667936524160387 62583114056501904786240581)
        ·
          refine ⟨11734333885594107147420109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62583114056501904786240581 11734333885594107147420109)
          ·
            refine ⟨4400375207097790180282541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11734333885594107147420109 4400375207097790180282541)
            ·
              refine ⟨1650140702661671317605953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4400375207097790180282541 1650140702661671317605953)
              ·
                refine ⟨1237605526996253488204465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1650140702661671317605953 1237605526996253488204465)
                ·
                  refine ⟨928204145247190116153349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1237605526996253488204465 928204145247190116153349)
                  ·
                    refine ⟨174038277233848146778753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 928204145247190116153349 174038277233848146778753)
                    ·
                      rfl

theorem cell23_1016815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 3, 2, 2, 4].length) (baseStart_1016815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1016815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1016815 prefixEnd_1016815 := by exact prefixLift 1016815
  have htrace : WordTrace (prefixWord ++ tailWord_1016815) baseStart_1016815 baseEnd_1016815 := by
    simpa [prefixWord, tailWord_1016815, baseEnd_1016815] using wordTrace_append hprefix tailTrace_1016815
  have hstable : (prefixWord ++ tailWord_1016815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016815).length < 2 ^ (prefixWord ++ tailWord_1016815).sum := by decide
  have hdescent : baseEnd_1016815 < baseStart_1016815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016841 : List Nat := [1, 2, 1, 1, 3, 1, 1, 4, 2, 7]
def baseStart_1016841 : Nat := 118140960795 + 1016841 * 2 ^ 59
def prefixEnd_1016841 : Nat := 4983230072969 + 3 ^ 40 * 1016841 * 2
def baseEnd_1016841 : Nat := 174042727399520446203713

theorem tailTrace_1016841 : CollatzResearch.WordTrace tailWord_1016841 prefixEnd_1016841 174042727399520446203713 := by
  unfold tailWord_1016841
  simp only [CollatzResearch.WordTrace]
  refine ⟨37087238109166194461922377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24724825406110796307948251 37087238109166194461922377)
  ·
    refine ⟨27815428581874645846441783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37087238109166194461922377 27815428581874645846441783)
    ·
      refine ⟨41723142872811968769662675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27815428581874645846441783 41723142872811968769662675)
      ·
        refine ⟨62584714309217953154494013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41723142872811968769662675 62584714309217953154494013)
        ·
          refine ⟨23469267865956732432935255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62584714309217953154494013 23469267865956732432935255)
          ·
            refine ⟨35203901798935098649402883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23469267865956732432935255 35203901798935098649402883)
            ·
              refine ⟨52805852698402647974104325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35203901798935098649402883 52805852698402647974104325)
              ·
                refine ⟨9901097380950496495144561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52805852698402647974104325 9901097380950496495144561)
                ·
                  refine ⟨7425823035712872371358421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9901097380950496495144561 7425823035712872371358421)
                  ·
                    refine ⟨174042727399520446203713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7425823035712872371358421 174042727399520446203713)
                    ·
                      rfl

theorem cell23_1016841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 4, 2, 7].length) (baseStart_1016841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1016841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1016841 prefixEnd_1016841 := by exact prefixLift 1016841
  have htrace : WordTrace (prefixWord ++ tailWord_1016841) baseStart_1016841 baseEnd_1016841 := by
    simpa [prefixWord, tailWord_1016841, baseEnd_1016841] using wordTrace_append hprefix tailTrace_1016841
  have hstable : (prefixWord ++ tailWord_1016841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016841).length < 2 ^ (prefixWord ++ tailWord_1016841).sum := by decide
  have hdescent : baseEnd_1016841 < baseStart_1016841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016842 : List Nat := [3, 1, 2, 2, 3, 2, 2, 2, 1, 2, 3]
def baseStart_1016842 : Nat := 118140960795 + 1016842 * 2 ^ 59
def prefixEnd_1016842 : Nat := 4983230072969 + 3 ^ 40 * 1016842 * 2
def baseEnd_1016842 : Nat := 522128695679215834698635

theorem tailTrace_1016842 : CollatzResearch.WordTrace tailWord_1016842 prefixEnd_1016842 522128695679215834698635 := by
  unfold tailWord_1016842
  simp only [CollatzResearch.WordTrace]
  refine ⟨9271818645540642908177195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24724849721441714421805853 9271818645540642908177195)
  ·
    refine ⟨13907727968310964362265793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9271818645540642908177195 13907727968310964362265793)
    ·
      refine ⟨10430795976233223271699345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13907727968310964362265793 10430795976233223271699345)
      ·
        refine ⟨7823096982174917453774509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10430795976233223271699345 7823096982174917453774509)
        ·
          refine ⟨2933661368315594045165441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7823096982174917453774509 2933661368315594045165441)
          ·
            refine ⟨2200246026236695533874081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2933661368315594045165441 2200246026236695533874081)
            ·
              refine ⟨1650184519677521650405561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2200246026236695533874081 1650184519677521650405561)
              ·
                refine ⟨1237638389758141237804171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1650184519677521650405561 1237638389758141237804171)
                ·
                  refine ⟨1856457584637211856706257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1237638389758141237804171 1856457584637211856706257)
                  ·
                    refine ⟨1392343188477908892529693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1856457584637211856706257 1392343188477908892529693)
                    ·
                      refine ⟨522128695679215834698635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1392343188477908892529693 522128695679215834698635)
                      ·
                        rfl

theorem cell23_1016842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 2, 2, 1, 2, 3].length) (baseStart_1016842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1016842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1016842 prefixEnd_1016842 := by exact prefixLift 1016842
  have htrace : WordTrace (prefixWord ++ tailWord_1016842) baseStart_1016842 baseEnd_1016842 := by
    simpa [prefixWord, tailWord_1016842, baseEnd_1016842] using wordTrace_append hprefix tailTrace_1016842
  have hstable : (prefixWord ++ tailWord_1016842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016842).length < 2 ^ (prefixWord ++ tailWord_1016842).sum := by decide
  have hdescent : baseEnd_1016842 < baseStart_1016842 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016850 : List Nat := [3, 2, 5, 1, 1, 2, 1, 3, 1, 1, 3]
def baseStart_1016850 : Nat := 118140960795 + 1016850 * 2 ^ 59
def prefixEnd_1016850 : Nat := 4983230072969 + 3 ^ 40 * 1016850 * 2
def baseEnd_1016850 : Nat := 522132803524451803398599

theorem tailTrace_1016850 : CollatzResearch.WordTrace tailWord_1016850 prefixEnd_1016850 522132803524451803398599 := by
  unfold tailWord_1016850
  simp only [CollatzResearch.WordTrace]
  refine ⟨9271891591533397249750001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24725044244089059332666669 9271891591533397249750001)
  ·
    refine ⟨6953918693650047937312501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9271891591533397249750001 6953918693650047937312501)
    ·
      refine ⟨651929877529691994123047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6953918693650047937312501 651929877529691994123047)
      ·
        refine ⟨977894816294537991184571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 651929877529691994123047 977894816294537991184571)
        ·
          refine ⟨1466842224441806986776857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 977894816294537991184571 1466842224441806986776857)
          ·
            refine ⟨1100131668331355240082643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1466842224441806986776857 1100131668331355240082643)
            ·
              refine ⟨1650197502497032860123965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1100131668331355240082643 1650197502497032860123965)
              ·
                refine ⟨618824063436387322546487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1650197502497032860123965 618824063436387322546487)
                ·
                  refine ⟨928236095154580983819731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 618824063436387322546487 928236095154580983819731)
                  ·
                    refine ⟨1392354142731871475729597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 928236095154580983819731 1392354142731871475729597)
                    ·
                      refine ⟨522132803524451803398599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1392354142731871475729597 522132803524451803398599)
                      ·
                        rfl

theorem cell23_1016850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_1016850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1016850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1016850 prefixEnd_1016850 := by exact prefixLift 1016850
  have htrace : WordTrace (prefixWord ++ tailWord_1016850) baseStart_1016850 baseEnd_1016850 := by
    simpa [prefixWord, tailWord_1016850, baseEnd_1016850] using wordTrace_append hprefix tailTrace_1016850
  have hstable : (prefixWord ++ tailWord_1016850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016850).length < 2 ^ (prefixWord ++ tailWord_1016850).sum := by decide
  have hdescent : baseEnd_1016850 < baseStart_1016850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016856 : List Nat := [2, 1, 2, 3, 2, 4, 1, 3, 1, 2, 2]
def baseStart_1016856 : Nat := 118140960795 + 1016856 * 2 ^ 59
def prefixEnd_1016856 : Nat := 4983230072969 + 3 ^ 40 * 1016856 * 2
def baseEnd_1016856 : Nat := 522135884408378779923571

theorem tailTrace_1016856 : CollatzResearch.WordTrace tailWord_1016856 prefixEnd_1016856 522135884408378779923571 := by
  unfold tailWord_1016856
  simp only [CollatzResearch.WordTrace]
  refine ⟨18543892602055926011859211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24725190136074568015812281 18543892602055926011859211)
  ·
    refine ⟨27815838903083889017788817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18543892602055926011859211 27815838903083889017788817)
    ·
      refine ⟨20861879177312916763341613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27815838903083889017788817 20861879177312916763341613)
      ·
        refine ⟨7823204691492343786253105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20861879177312916763341613 7823204691492343786253105)
        ·
          refine ⟨5867403518619257839689829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7823204691492343786253105 5867403518619257839689829)
          ·
            refine ⟨1100138159741110844941843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5867403518619257839689829 1100138159741110844941843)
            ·
              refine ⟨1650207239611666267412765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1100138159741110844941843 1650207239611666267412765)
              ·
                refine ⟨618827714854374850279787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1650207239611666267412765 618827714854374850279787)
                ·
                  refine ⟨928241572281562275419681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 618827714854374850279787 928241572281562275419681)
                  ·
                    refine ⟨696181179211171706564761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 928241572281562275419681 696181179211171706564761)
                    ·
                      refine ⟨522135884408378779923571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 696181179211171706564761 522135884408378779923571)
                      ·
                        rfl

theorem cell23_1016856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 1, 3, 1, 2, 2].length) (baseStart_1016856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1016856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1016856 prefixEnd_1016856 := by exact prefixLift 1016856
  have htrace : WordTrace (prefixWord ++ tailWord_1016856) baseStart_1016856 baseEnd_1016856 := by
    simpa [prefixWord, tailWord_1016856, baseEnd_1016856] using wordTrace_append hprefix tailTrace_1016856
  have hstable : (prefixWord ++ tailWord_1016856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016856).length < 2 ^ (prefixWord ++ tailWord_1016856).sum := by decide
  have hdescent : baseEnd_1016856 < baseStart_1016856 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016889 : List Nat := [1, 2, 1, 5, 2, 1, 4, 1, 2, 1, 3]
def baseStart_1016889 : Nat := 118140960795 + 1016889 * 2 ^ 59
def prefixEnd_1016889 : Nat := 4983230072969 + 3 ^ 40 * 1016889 * 2
def baseEnd_1016889 : Nat := 522152829269977150810919

theorem tailTrace_1016889 : CollatzResearch.WordTrace tailWord_1016889 prefixEnd_1016889 522152829269977150810919 := by
  unfold tailWord_1016889
  simp only [CollatzResearch.WordTrace]
  refine ⟨37088988812992298659669721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24725992541994865773113147 37088988812992298659669721)
  ·
    refine ⟨27816741609744223994752291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37088988812992298659669721 27816741609744223994752291)
    ·
      refine ⟨41725112414616335992128437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27816741609744223994752291 41725112414616335992128437)
      ·
        refine ⟨3911729288870281499262041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41725112414616335992128437 3911729288870281499262041)
        ·
          refine ⟨2933796966652711124446531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3911729288870281499262041 2933796966652711124446531)
          ·
            refine ⟨4400695449979066686669797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2933796966652711124446531 4400695449979066686669797)
            ·
              refine ⟨825130396871075003750587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4400695449979066686669797 825130396871075003750587)
              ·
                refine ⟨1237695595306612505625881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 825130396871075003750587 1237695595306612505625881)
                ·
                  refine ⟨928271696479959379219411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1237695595306612505625881 928271696479959379219411)
                  ·
                    refine ⟨1392407544719939068829117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 928271696479959379219411 1392407544719939068829117)
                    ·
                      refine ⟨522152829269977150810919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1392407544719939068829117 522152829269977150810919)
                      ·
                        rfl

theorem cell23_1016889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 4, 1, 2, 1, 3].length) (baseStart_1016889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1016889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1016889 prefixEnd_1016889 := by exact prefixLift 1016889
  have htrace : WordTrace (prefixWord ++ tailWord_1016889) baseStart_1016889 baseEnd_1016889 := by
    simpa [prefixWord, tailWord_1016889, baseEnd_1016889] using wordTrace_append hprefix tailTrace_1016889
  have hstable : (prefixWord ++ tailWord_1016889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016889).length < 2 ^ (prefixWord ++ tailWord_1016889).sum := by decide
  have hdescent : baseEnd_1016889 < baseStart_1016889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016895 : List Nat := [1, 1, 2, 2, 3, 1, 1, 5, 1, 4, 2]
def baseStart_1016895 : Nat := 118140960795 + 1016895 * 2 ^ 59
def prefixEnd_1016895 : Nat := 4983230072969 + 3 ^ 40 * 1016895 * 2
def baseEnd_1016895 : Nat := 522155910153904127335891

theorem tailTrace_1016895 : CollatzResearch.WordTrace tailWord_1016895 prefixEnd_1016895 522155910153904127335891 := by
  unfold tailWord_1016895
  simp only [CollatzResearch.WordTrace]
  refine ⟨37089207650970561684388139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24726138433980374456258759 37089207650970561684388139)
  ·
    refine ⟨55633811476455842526582209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37089207650970561684388139 55633811476455842526582209)
    ·
      refine ⟨41725358607341881894936657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55633811476455842526582209 41725358607341881894936657)
      ·
        refine ⟨31294018955506411421202493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41725358607341881894936657 31294018955506411421202493)
        ·
          refine ⟨11735257108314904282950935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31294018955506411421202493 11735257108314904282950935)
          ·
            refine ⟨17602885662472356424426403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11735257108314904282950935 17602885662472356424426403)
            ·
              refine ⟨26404328493708534636639605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17602885662472356424426403 26404328493708534636639605)
              ·
                refine ⟨2475405796285175122184963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26404328493708534636639605 2475405796285175122184963)
                ·
                  refine ⟨3713108694427762683277445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2475405796285175122184963 3713108694427762683277445)
                  ·
                    refine ⟨696207880205205503114521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3713108694427762683277445 696207880205205503114521)
                    ·
                      refine ⟨522155910153904127335891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 696207880205205503114521 522155910153904127335891)
                      ·
                        rfl

theorem cell23_1016895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 5, 1, 4, 2].length) (baseStart_1016895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1016895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1016895 prefixEnd_1016895 := by exact prefixLift 1016895
  have htrace : WordTrace (prefixWord ++ tailWord_1016895) baseStart_1016895 baseEnd_1016895 := by
    simpa [prefixWord, tailWord_1016895, baseEnd_1016895] using wordTrace_append hprefix tailTrace_1016895
  have hstable : (prefixWord ++ tailWord_1016895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016895).length < 2 ^ (prefixWord ++ tailWord_1016895).sum := by decide
  have hdescent : baseEnd_1016895 < baseStart_1016895 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016908 : List Nat := [2, 2, 1, 3, 1, 1, 1, 2, 4, 2, 4]
def baseStart_1016908 : Nat := 118140960795 + 1016908 * 2 ^ 59
def prefixEnd_1016908 : Nat := 4983230072969 + 3 ^ 40 * 1016908 * 2
def baseEnd_1016908 : Nat := 522162585402412576473331

theorem tailTrace_1016908 : CollatzResearch.WordTrace tailWord_1016908 prefixEnd_1016908 522162585402412576473331 := by
  unfold tailWord_1016908
  simp only [CollatzResearch.WordTrace]
  refine ⟨18544840899961732452305689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24726454533282309936407585 18544840899961732452305689)
  ·
    refine ⟨13908630674971299339229267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18544840899961732452305689 13908630674971299339229267)
    ·
      refine ⟨20862946012456949008843901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13908630674971299339229267 20862946012456949008843901)
      ·
        refine ⟨7823604754671355878316463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20862946012456949008843901 7823604754671355878316463)
        ·
          refine ⟨11735407132007033817474695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7823604754671355878316463 11735407132007033817474695)
          ·
            refine ⟨17603110698010550726212043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11735407132007033817474695 17603110698010550726212043)
            ·
              refine ⟨26404666047015826089318065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17603110698010550726212043 26404666047015826089318065)
              ·
                refine ⟨19803499535261869566988549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26404666047015826089318065 19803499535261869566988549)
                ·
                  refine ⟨3713156162861600543810353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19803499535261869566988549 3713156162861600543810353)
                  ·
                    refine ⟨2784867122146200407857765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3713156162861600543810353 2784867122146200407857765)
                    ·
                      refine ⟨522162585402412576473331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2784867122146200407857765 522162585402412576473331)
                      ·
                        rfl

theorem cell23_1016908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 4, 2, 4].length) (baseStart_1016908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1016908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1016908 prefixEnd_1016908 := by exact prefixLift 1016908
  have htrace : WordTrace (prefixWord ++ tailWord_1016908) baseStart_1016908 baseEnd_1016908 := by
    simpa [prefixWord, tailWord_1016908, baseEnd_1016908] using wordTrace_append hprefix tailTrace_1016908
  have hstable : (prefixWord ++ tailWord_1016908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016908).length < 2 ^ (prefixWord ++ tailWord_1016908).sum := by decide
  have hdescent : baseEnd_1016908 < baseStart_1016908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016965 : List Nat := [1, 3, 1, 1, 6, 1, 1, 1, 1, 7]
def baseStart_1016965 : Nat := 118140960795 + 1016965 * 2 ^ 59
def prefixEnd_1016965 : Nat := 4983230072969 + 3 ^ 40 * 1016965 * 2
def baseEnd_1016965 : Nat := 174063951266572951153523

theorem tailTrace_1016965 : CollatzResearch.WordTrace tailWord_1016965 prefixEnd_1016965 174063951266572951153523 := by
  unfold tailWord_1016965
  simp only [CollatzResearch.WordTrace]
  refine ⟨37091760760716963639436349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24727840507144642426290899 37091760760716963639436349)
  ·
    refine ⟨13909410285268861364788631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37091760760716963639436349 13909410285268861364788631)
    ·
      refine ⟨20864115427903292047182947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13909410285268861364788631 20864115427903292047182947)
      ·
        refine ⟨31296173141854938070774421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20864115427903292047182947 31296173141854938070774421)
        ·
          refine ⟨1467008116024450222067551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 31296173141854938070774421 1467008116024450222067551)
          ·
            refine ⟨2200512174036675333101327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1467008116024450222067551 2200512174036675333101327)
            ·
              refine ⟨3300768261055012999651991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2200512174036675333101327 3300768261055012999651991)
              ·
                refine ⟨4951152391582519499477987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3300768261055012999651991 4951152391582519499477987)
                ·
                  refine ⟨7426728587373779249216981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4951152391582519499477987 7426728587373779249216981)
                  ·
                    refine ⟨174063951266572951153523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7426728587373779249216981 174063951266572951153523)
                    ·
                      rfl

theorem cell23_1016965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 1, 1, 7].length) (baseStart_1016965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1016965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1016965 prefixEnd_1016965 := by exact prefixLift 1016965
  have htrace : WordTrace (prefixWord ++ tailWord_1016965) baseStart_1016965 baseEnd_1016965 := by
    simpa [prefixWord, tailWord_1016965, baseEnd_1016965] using wordTrace_append hprefix tailTrace_1016965
  have hstable : (prefixWord ++ tailWord_1016965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016965).length < 2 ^ (prefixWord ++ tailWord_1016965).sum := by decide
  have hdescent : baseEnd_1016965 < baseStart_1016965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017002 : List Nat := [3, 1, 5, 1, 1, 1, 1, 2, 1, 3, 4]
def baseStart_1017002 : Nat := 118140960795 + 1017002 * 2 ^ 59
def prefixEnd_1017002 : Nat := 4983230072969 + 3 ^ 40 * 1017002 * 2
def baseEnd_1017002 : Nat := 522210852583935208697899

theorem tailTrace_1017002 : CollatzResearch.WordTrace tailWord_1017002 prefixEnd_1017002 522210852583935208697899 := by
  unfold tailWord_1017002
  simp only [CollatzResearch.WordTrace]
  refine ⟨9273277565395729739633315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24728740174388612639022173 9273277565395729739633315)
  ·
    refine ⟨13909916348093594609449973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9273277565395729739633315 13909916348093594609449973)
    ·
      refine ⟨1304054657633774494635935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13909916348093594609449973 1304054657633774494635935)
      ·
        refine ⟨1956081986450661741953903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1304054657633774494635935 1956081986450661741953903)
        ·
          refine ⟨2934122979675992612930855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1956081986450661741953903 2934122979675992612930855)
          ·
            refine ⟨4401184469513988919396283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2934122979675992612930855 4401184469513988919396283)
            ·
              refine ⟨6601776704270983379094425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4401184469513988919396283 6601776704270983379094425)
              ·
                refine ⟨4951332528203237534320819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6601776704270983379094425 4951332528203237534320819)
                ·
                  refine ⟨7426998792304856301481229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4951332528203237534320819 7426998792304856301481229)
                  ·
                    refine ⟨2785124547114321113055461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7426998792304856301481229 2785124547114321113055461)
                    ·
                      refine ⟨522210852583935208697899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2785124547114321113055461 522210852583935208697899)
                      ·
                        rfl

theorem cell23_1017002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_1017002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1017002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1017002 prefixEnd_1017002 := by exact prefixLift 1017002
  have htrace : WordTrace (prefixWord ++ tailWord_1017002) baseStart_1017002 baseEnd_1017002 := by
    simpa [prefixWord, tailWord_1017002, baseEnd_1017002] using wordTrace_append hprefix tailTrace_1017002
  have hstable : (prefixWord ++ tailWord_1017002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017002).length < 2 ^ (prefixWord ++ tailWord_1017002).sum := by decide
  have hdescent : baseEnd_1017002 < baseStart_1017002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017022 : List Nat := [4, 2, 1, 1, 3, 1, 2, 1, 1, 4, 3]
def baseStart_1017022 : Nat := 118140960795 + 1017022 * 2 ^ 59
def prefixEnd_1017022 : Nat := 4983230072969 + 3 ^ 40 * 1017022 * 2
def baseEnd_1017022 : Nat := 522221122197025130447807

theorem tailTrace_1017022 : CollatzResearch.WordTrace tailWord_1017022 prefixEnd_1017022 522221122197025130447807 := by
  unfold tailWord_1017022
  simp only [CollatzResearch.WordTrace]
  refine ⟨4636729965188807796782665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24729226481006974916174213 4636729965188807796782665)
  ·
    refine ⟨3477547473891605847586999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4636729965188807796782665 3477547473891605847586999)
    ·
      refine ⟨5216321210837408771380499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3477547473891605847586999 5216321210837408771380499)
      ·
        refine ⟨7824481816256113157070749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5216321210837408771380499 7824481816256113157070749)
        ·
          refine ⟨2934180681096042433901531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7824481816256113157070749 2934180681096042433901531)
          ·
            refine ⟨4401271021644063650852297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2934180681096042433901531 4401271021644063650852297)
            ·
              refine ⟨3300953266233047738139223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4401271021644063650852297 3300953266233047738139223)
              ·
                refine ⟨4951429899349571607208835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3300953266233047738139223 4951429899349571607208835)
                ·
                  refine ⟨7427144849024357410813253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4951429899349571607208835 7427144849024357410813253)
                  ·
                    refine ⟨1392589659192067014527485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7427144849024357410813253 1392589659192067014527485)
                    ·
                      refine ⟨522221122197025130447807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1392589659192067014527485 522221122197025130447807)
                      ·
                        rfl

theorem cell23_1017022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 1, 1, 4, 3].length) (baseStart_1017022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1017022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1017022 prefixEnd_1017022 := by exact prefixLift 1017022
  have htrace : WordTrace (prefixWord ++ tailWord_1017022) baseStart_1017022 baseEnd_1017022 := by
    simpa [prefixWord, tailWord_1017022, baseEnd_1017022] using wordTrace_append hprefix tailTrace_1017022
  have hstable : (prefixWord ++ tailWord_1017022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017022).length < 2 ^ (prefixWord ++ tailWord_1017022).sum := by decide
  have hdescent : baseEnd_1017022 < baseStart_1017022 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017089 : List Nat := [1, 2, 4, 1, 1, 4, 3, 1, 1, 5]
def baseStart_1017089 : Nat := 118140960795 + 1017089 * 2 ^ 59
def prefixEnd_1017089 : Nat := 4983230072969 + 3 ^ 40 * 1017089 * 2
def baseEnd_1017089 : Nat := 174085175133625456103333

theorem tailTrace_1017089 : CollatzResearch.WordTrace tailWord_1017089 prefixEnd_1017089 174085175133625456103333 := by
  unfold tailWord_1017089
  simp only [CollatzResearch.WordTrace]
  refine ⟨37096283412267732816950321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24730855608178488544633547 37096283412267732816950321)
  ·
    refine ⟨27822212559200799612712741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37096283412267732816950321 27822212559200799612712741)
    ·
      refine ⟨5216664854850149927383639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27822212559200799612712741 5216664854850149927383639)
      ·
        refine ⟨7824997282275224891075459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5216664854850149927383639 7824997282275224891075459)
        ·
          refine ⟨11737495923412837336613189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7824997282275224891075459 11737495923412837336613189)
          ·
            refine ⟨2200780485639907000614973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11737495923412837336613189 2200780485639907000614973)
            ·
              refine ⟨825292682114965125230615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2200780485639907000614973 825292682114965125230615)
              ·
                refine ⟨1237939023172447687845923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 825292682114965125230615 1237939023172447687845923)
                ·
                  refine ⟨1856908534758671531768885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1237939023172447687845923 1856908534758671531768885)
                  ·
                    refine ⟨174085175133625456103333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1856908534758671531768885 174085175133625456103333)
                    ·
                      rfl

theorem cell23_1017089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 3, 1, 1, 5].length) (baseStart_1017089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1017089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1017089 prefixEnd_1017089 := by exact prefixLift 1017089
  have htrace : WordTrace (prefixWord ++ tailWord_1017089) baseStart_1017089 baseEnd_1017089 := by
    simpa [prefixWord, tailWord_1017089, baseEnd_1017089] using wordTrace_append hprefix tailTrace_1017089
  have hstable : (prefixWord ++ tailWord_1017089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017089).length < 2 ^ (prefixWord ++ tailWord_1017089).sum := by decide
  have hdescent : baseEnd_1017089 < baseStart_1017089 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017105 : List Nat := [1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 4]
def baseStart_1017105 : Nat := 118140960795 + 1017105 * 2 ^ 59
def prefixEnd_1017105 : Nat := 4983230072969 + 3 ^ 40 * 1017105 * 2
def baseEnd_1017105 : Nat := 522263741091348305709925

theorem tailTrace_1017105 : CollatzResearch.WordTrace tailWord_1017105 prefixEnd_1017105 522263741091348305709925 := by
  unfold tailWord_1017105
  simp only [CollatzResearch.WordTrace]
  refine ⟨37096866980209767549532769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24731244653473178366355179 37096866980209767549532769)
  ·
    refine ⟨27822650235157325662149577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37096866980209767549532769 27822650235157325662149577)
    ·
      refine ⟨20866987676367994246612183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27822650235157325662149577 20866987676367994246612183)
      ·
        refine ⟨31300481514551991369918275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20866987676367994246612183 31300481514551991369918275)
        ·
          refine ⟨46950722271827987054877413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31300481514551991369918275 46950722271827987054877413)
          ·
            refine ⟨8803260425967747572789515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46950722271827987054877413 8803260425967747572789515)
            ·
              refine ⟨13204890638951621359184273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8803260425967747572789515 13204890638951621359184273)
              ·
                refine ⟨9903667979213716019388205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13204890638951621359184273 9903667979213716019388205)
                ·
                  refine ⟨3713875492205143507270577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9903667979213716019388205 3713875492205143507270577)
                  ·
                    refine ⟨2785406619153857630452933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3713875492205143507270577 2785406619153857630452933)
                    ·
                      refine ⟨522263741091348305709925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2785406619153857630452933 522263741091348305709925)
                      ·
                        rfl

theorem cell23_1017105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 4].length) (baseStart_1017105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1017105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1017105 prefixEnd_1017105 := by exact prefixLift 1017105
  have htrace : WordTrace (prefixWord ++ tailWord_1017105) baseStart_1017105 baseEnd_1017105 := by
    simpa [prefixWord, tailWord_1017105, baseEnd_1017105] using wordTrace_append hprefix tailTrace_1017105
  have hstable : (prefixWord ++ tailWord_1017105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017105).length < 2 ^ (prefixWord ++ tailWord_1017105).sum := by decide
  have hdescent : baseEnd_1017105 < baseStart_1017105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017109 : List Nat := [1, 3, 2, 1, 2, 1, 1, 5, 3, 2, 2]
def baseStart_1017109 : Nat := 118140960795 + 1017109 * 2 ^ 59
def prefixEnd_1017109 : Nat := 4983230072969 + 3 ^ 40 * 1017109 * 2
def baseEnd_1017109 : Nat := 522265795013966290059907

theorem tailTrace_1017109 : CollatzResearch.WordTrace tailWord_1017109 prefixEnd_1017109 522265795013966290059907 := by
  unfold tailWord_1017109
  simp only [CollatzResearch.WordTrace]
  refine ⟨37097012872195276232678381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24731341914796850821785587 37097012872195276232678381)
  ·
    refine ⟨13911379827073228587254393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37097012872195276232678381 13911379827073228587254393)
    ·
      refine ⟨10433534870304921440440795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13911379827073228587254393 10433534870304921440440795)
      ·
        refine ⟨15650302305457382160661193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10433534870304921440440795 15650302305457382160661193)
        ·
          refine ⟨11737726729093036620495895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15650302305457382160661193 11737726729093036620495895)
          ·
            refine ⟨17606590093639554930743843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11737726729093036620495895 17606590093639554930743843)
            ·
              refine ⟨26409885140459332396115765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17606590093639554930743843 26409885140459332396115765)
              ·
                refine ⟨2475926731918062412135853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26409885140459332396115765 2475926731918062412135853)
                ·
                  refine ⟨928472524469273404550945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2475926731918062412135853 928472524469273404550945)
                  ·
                    refine ⟨696354393351955053413209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 928472524469273404550945 696354393351955053413209)
                    ·
                      refine ⟨522265795013966290059907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 696354393351955053413209 522265795013966290059907)
                      ·
                        rfl

theorem cell23_1017109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 5, 3, 2, 2].length) (baseStart_1017109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1017109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1017109 prefixEnd_1017109 := by exact prefixLift 1017109
  have htrace : WordTrace (prefixWord ++ tailWord_1017109) baseStart_1017109 baseEnd_1017109 := by
    simpa [prefixWord, tailWord_1017109, baseEnd_1017109] using wordTrace_append hprefix tailTrace_1017109
  have hstable : (prefixWord ++ tailWord_1017109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017109).length < 2 ^ (prefixWord ++ tailWord_1017109).sum := by decide
  have hdescent : baseEnd_1017109 < baseStart_1017109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017112 : List Nat := [2, 1, 2, 3, 1, 3, 1, 2, 3, 2, 3]
def baseStart_1017112 : Nat := 118140960795 + 1017112 * 2 ^ 59
def prefixEnd_1017112 : Nat := 4983230072969 + 3 ^ 40 * 1017112 * 2
def baseEnd_1017112 : Nat := 522267335455929778322393

theorem tailTrace_1017112 : CollatzResearch.WordTrace tailWord_1017112 prefixEnd_1017112 522267335455929778322393 := by
  unfold tailWord_1017112
  simp only [CollatzResearch.WordTrace]
  refine ⟨18548561145592203872518795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24731414860789605163358393 18548561145592203872518795)
  ·
    refine ⟨27822841718388305808778193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18548561145592203872518795 27822841718388305808778193)
    ·
      refine ⟨20867131288791229356583645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27822841718388305808778193 20867131288791229356583645)
      ·
        refine ⟨7825174233296711008718867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20867131288791229356583645 7825174233296711008718867)
        ·
          refine ⟨11737761349945066513078301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7825174233296711008718867 11737761349945066513078301)
          ·
            refine ⟨4401660506229399942404363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11737761349945066513078301 4401660506229399942404363)
            ·
              refine ⟨6602490759344099913606545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4401660506229399942404363 6602490759344099913606545)
              ·
                refine ⟨4951868069508074935204909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6602490759344099913606545 4951868069508074935204909)
                ·
                  refine ⟨1856950526065528100701841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4951868069508074935204909 1856950526065528100701841)
                  ·
                    refine ⟨1392712894549146075526381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1856950526065528100701841 1392712894549146075526381)
                    ·
                      refine ⟨522267335455929778322393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1392712894549146075526381 522267335455929778322393)
                      ·
                        rfl

theorem cell23_1017112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 2, 3, 2, 3].length) (baseStart_1017112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1017112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1017112 prefixEnd_1017112 := by exact prefixLift 1017112
  have htrace : WordTrace (prefixWord ++ tailWord_1017112) baseStart_1017112 baseEnd_1017112 := by
    simpa [prefixWord, tailWord_1017112, baseEnd_1017112] using wordTrace_append hprefix tailTrace_1017112
  have hstable : (prefixWord ++ tailWord_1017112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017112).length < 2 ^ (prefixWord ++ tailWord_1017112).sum := by decide
  have hdescent : baseEnd_1017112 < baseStart_1017112 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017159 : List Nat := [1, 1, 4, 1, 2, 4, 1, 1, 4, 1, 3]
def baseStart_1017159 : Nat := 118140960795 + 1017159 * 2 ^ 59
def prefixEnd_1017159 : Nat := 4983230072969 + 3 ^ 40 * 1017159 * 2
def baseEnd_1017159 : Nat := 522291469046691094434677

theorem tailTrace_1017159 : CollatzResearch.WordTrace tailWord_1017159 prefixEnd_1017159 522291469046691094434677 := by
  unfold tailWord_1017159
  simp only [CollatzResearch.WordTrace]
  refine ⟨37098836522014134771998531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24732557681342756514665687 37098836522014134771998531)
  ·
    refine ⟨55648254783021202157997797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37098836522014134771998531 55648254783021202157997797)
    ·
      refine ⟨10434047771816475404624587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55648254783021202157997797 10434047771816475404624587)
      ·
        refine ⟨15651071657724713106936881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10434047771816475404624587 15651071657724713106936881)
        ·
          refine ⟨11738303743293534830202661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15651071657724713106936881 11738303743293534830202661)
          ·
            refine ⟨2200931951867537780662999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11738303743293534830202661 2200931951867537780662999)
            ·
              refine ⟨3301397927801306670994499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2200931951867537780662999 3301397927801306670994499)
              ·
                refine ⟨4952096891701960006491749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3301397927801306670994499 4952096891701960006491749)
                ·
                  refine ⟨928518167194117501217203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4952096891701960006491749 928518167194117501217203)
                  ·
                    refine ⟨1392777250791176251825805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 928518167194117501217203 1392777250791176251825805)
                    ·
                      refine ⟨522291469046691094434677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1392777250791176251825805 522291469046691094434677)
                      ·
                        rfl

theorem cell23_1017159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 1, 4, 1, 3].length) (baseStart_1017159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1017159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1017159 prefixEnd_1017159 := by exact prefixLift 1017159
  have htrace : WordTrace (prefixWord ++ tailWord_1017159) baseStart_1017159 baseEnd_1017159 := by
    simpa [prefixWord, tailWord_1017159, baseEnd_1017159] using wordTrace_append hprefix tailTrace_1017159
  have hstable : (prefixWord ++ tailWord_1017159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017159).length < 2 ^ (prefixWord ++ tailWord_1017159).sum := by decide
  have hdescent : baseEnd_1017159 < baseStart_1017159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017176 : List Nat := [2, 1, 2, 2, 1, 1, 7, 1, 2, 1, 3]
def baseStart_1017176 : Nat := 118140960795 + 1017176 * 2 ^ 59
def prefixEnd_1017176 : Nat := 4983230072969 + 3 ^ 40 * 1017176 * 2
def baseEnd_1017176 : Nat := 522300198217817527922099

theorem tailTrace_1017176 : CollatzResearch.WordTrace tailWord_1017176 prefixEnd_1017176 522300198217817527922099 := by
  unfold tailWord_1017176
  simp only [CollatzResearch.WordTrace]
  refine ⟨18549728281476273337683691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24732971041968364450244921 18549728281476273337683691)
  ·
    refine ⟨27824592422214410006525537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18549728281476273337683691 27824592422214410006525537)
    ·
      refine ⟨20868444316660807504894153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27824592422214410006525537 20868444316660807504894153)
      ·
        refine ⟨15651333237495605628670615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20868444316660807504894153 15651333237495605628670615)
        ·
          refine ⟨23476999856243408443005923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15651333237495605628670615 23476999856243408443005923)
          ·
            refine ⟨35215499784365112664508885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23476999856243408443005923 35215499784365112664508885)
            ·
              refine ⟨825363276196057328074427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 35215499784365112664508885 825363276196057328074427)
              ·
                refine ⟨1238044914294085992111641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 825363276196057328074427 1238044914294085992111641)
                ·
                  refine ⟨928533685720564494083731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1238044914294085992111641 928533685720564494083731)
                  ·
                    refine ⟨1392800528580846741125597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 928533685720564494083731 1392800528580846741125597)
                    ·
                      refine ⟨522300198217817527922099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1392800528580846741125597 522300198217817527922099)
                      ·
                        rfl

theorem cell23_1017176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 7, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 7, 1, 2, 1, 3].length) (baseStart_1017176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1017176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1017176 prefixEnd_1017176 := by exact prefixLift 1017176
  have htrace : WordTrace (prefixWord ++ tailWord_1017176) baseStart_1017176 baseEnd_1017176 := by
    simpa [prefixWord, tailWord_1017176, baseEnd_1017176] using wordTrace_append hprefix tailTrace_1017176
  have hstable : (prefixWord ++ tailWord_1017176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017176).length < 2 ^ (prefixWord ++ tailWord_1017176).sum := by decide
  have hdescent : baseEnd_1017176 < baseStart_1017176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017185 : List Nat := [1, 2, 3, 1, 1, 1, 1, 2, 3, 3, 5]
def baseStart_1017185 : Nat := 118140960795 + 1017185 * 2 ^ 59
def prefixEnd_1017185 : Nat := 4983230072969 + 3 ^ 40 * 1017185 * 2
def baseEnd_1017185 : Nat := 522304819543707992709557

theorem tailTrace_1017185 : CollatzResearch.WordTrace tailWord_1017185 prefixEnd_1017185 522304819543707992709557 := by
  unfold tailWord_1017185
  simp only [CollatzResearch.WordTrace]
  refine ⟨37099784819919941212445009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24733189879946627474963339 37099784819919941212445009)
  ·
    refine ⟨27824838614939955909333757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37099784819919941212445009 27824838614939955909333757)
    ·
      refine ⟨10434314480602483466000159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27824838614939955909333757 10434314480602483466000159)
      ·
        refine ⟨15651471720903725199000239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10434314480602483466000159 15651471720903725199000239)
        ·
          refine ⟨23477207581355587798500359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15651471720903725199000239 23477207581355587798500359)
          ·
            refine ⟨35215811372033381697750539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23477207581355587798500359 35215811372033381697750539)
            ·
              refine ⟨52823717058050072546625809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35215811372033381697750539 52823717058050072546625809)
              ·
                refine ⟨39617787793537554409969357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52823717058050072546625809 39617787793537554409969357)
                ·
                  refine ⟨14856670422576582903738509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39617787793537554409969357 14856670422576582903738509)
                  ·
                    refine ⟨5571251408466218588901941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14856670422576582903738509 5571251408466218588901941)
                    ·
                      refine ⟨522304819543707992709557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5571251408466218588901941 522304819543707992709557)
                      ·
                        rfl

theorem cell23_1017185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 3, 3, 5].length) (baseStart_1017185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1017185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1017185 prefixEnd_1017185 := by exact prefixLift 1017185
  have htrace : WordTrace (prefixWord ++ tailWord_1017185) baseStart_1017185 baseEnd_1017185 := by
    simpa [prefixWord, tailWord_1017185, baseEnd_1017185] using wordTrace_append hprefix tailTrace_1017185
  have hstable : (prefixWord ++ tailWord_1017185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017185).length < 2 ^ (prefixWord ++ tailWord_1017185).sum := by decide
  have hdescent : baseEnd_1017185 < baseStart_1017185 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017199 : List Nat := [1, 1, 2, 1, 3, 1, 3, 1, 6, 2, 2]
def baseStart_1017199 : Nat := 118140960795 + 1017199 * 2 ^ 59
def prefixEnd_1017199 : Nat := 4983230072969 + 3 ^ 40 * 1017199 * 2
def baseEnd_1017199 : Nat := 522312008272870937934493

theorem tailTrace_1017199 : CollatzResearch.WordTrace tailWord_1017199 prefixEnd_1017199 522312008272870937934493 := by
  unfold tailWord_1017199
  simp only [CollatzResearch.WordTrace]
  refine ⟨37100295441869221603454651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24733530294579481068969767 37100295441869221603454651)
  ·
    refine ⟨55650443162803832405181977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37100295441869221603454651 55650443162803832405181977)
    ·
      refine ⟨41737832372102874303886483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55650443162803832405181977 41737832372102874303886483)
      ·
        refine ⟨62606748558154311455829725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41737832372102874303886483 62606748558154311455829725)
        ·
          refine ⟨23477530709307866795936147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62606748558154311455829725 23477530709307866795936147)
          ·
            refine ⟨35216296063961800193904221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23477530709307866795936147 35216296063961800193904221)
            ·
              refine ⟨13206111023985675072714083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35216296063961800193904221 13206111023985675072714083)
              ·
                refine ⟨19809166535978512609071125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13206111023985675072714083 19809166535978512609071125)
                ·
                  refine ⟨928554681373992778550209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 19809166535978512609071125 928554681373992778550209)
                  ·
                    refine ⟨696416011030494583912657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 928554681373992778550209 696416011030494583912657)
                    ·
                      refine ⟨522312008272870937934493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 696416011030494583912657 522312008272870937934493)
                      ·
                        rfl

theorem cell23_1017199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 6, 2, 2].length) (baseStart_1017199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1017199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1017199 prefixEnd_1017199 := by exact prefixLift 1017199
  have htrace : WordTrace (prefixWord ++ tailWord_1017199) baseStart_1017199 baseEnd_1017199 := by
    simpa [prefixWord, tailWord_1017199, baseEnd_1017199] using wordTrace_append hprefix tailTrace_1017199
  have hstable : (prefixWord ++ tailWord_1017199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017199).length < 2 ^ (prefixWord ++ tailWord_1017199).sum := by decide
  have hdescent : baseEnd_1017199 < baseStart_1017199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017202 : List Nat := [3, 2, 1, 2, 1, 2, 3, 1, 2, 1, 5]
def baseStart_1017202 : Nat := 118140960795 + 1017202 * 2 ^ 59
def prefixEnd_1017202 : Nat := 4983230072969 + 3 ^ 40 * 1017202 * 2
def baseEnd_1017202 : Nat := 522313548714834426196979

theorem tailTrace_1017202 : CollatzResearch.WordTrace tailWord_1017202 prefixEnd_1017202 522313548714834426196979 := by
  unfold tailWord_1017202
  simp only [CollatzResearch.WordTrace]
  refine ⟨9275101215214588278953465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24733603240572235410542573 9275101215214588278953465)
  ·
    refine ⟨6956325911410941209215099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9275101215214588278953465 6956325911410941209215099)
    ·
      refine ⟨10434488867116411813822649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6956325911410941209215099 10434488867116411813822649)
      ·
        refine ⟨7825866650337308860366987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10434488867116411813822649 7825866650337308860366987)
        ·
          refine ⟨11738799975505963290550481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7825866650337308860366987 11738799975505963290550481)
          ·
            refine ⟨8804099981629472467912861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11738799975505963290550481 8804099981629472467912861)
            ·
              refine ⟨3301537493111052175467323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8804099981629472467912861 3301537493111052175467323)
              ·
                refine ⟨4952306239666578263200985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3301537493111052175467323 4952306239666578263200985)
                ·
                  refine ⟨3714229679749933697400739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4952306239666578263200985 3714229679749933697400739)
                  ·
                    refine ⟨5571344519624900546101109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3714229679749933697400739 5571344519624900546101109)
                    ·
                      refine ⟨522313548714834426196979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5571344519624900546101109 522313548714834426196979)
                      ·
                        rfl

theorem cell23_1017202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 1, 2, 1, 5].length) (baseStart_1017202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1017202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1017202 prefixEnd_1017202 := by exact prefixLift 1017202
  have htrace : WordTrace (prefixWord ++ tailWord_1017202) baseStart_1017202 baseEnd_1017202 := by
    simpa [prefixWord, tailWord_1017202, baseEnd_1017202] using wordTrace_append hprefix tailTrace_1017202
  have hstable : (prefixWord ++ tailWord_1017202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017202).length < 2 ^ (prefixWord ++ tailWord_1017202).sum := by decide
  have hdescent : baseEnd_1017202 < baseStart_1017202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017269 : List Nat := [1, 3, 3, 2, 2, 1, 2, 2, 2, 5]
def baseStart_1017269 : Nat := 118140960795 + 1017269 * 2 ^ 59
def prefixEnd_1017269 : Nat := 4983230072969 + 3 ^ 40 * 1017269 * 2
def baseEnd_1017269 : Nat := 174115983972895221353057

theorem tailTrace_1017269 : CollatzResearch.WordTrace tailWord_1017269 prefixEnd_1017269 174115983972895221353057 := by
  unfold tailWord_1017269
  simp only [CollatzResearch.WordTrace]
  refine ⟨37102848551615623558502861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24735232367743749039001907 37102848551615623558502861)
  ·
    refine ⟨13913568206855858834438573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37102848551615623558502861 13913568206855858834438573)
    ·
      refine ⟨5217588077570947062914465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13913568206855858834438573 5217588077570947062914465)
      ·
        refine ⟨3913191058178210297185849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5217588077570947062914465 3913191058178210297185849)
        ·
          refine ⟨2934893293633657722889387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3913191058178210297185849 2934893293633657722889387)
          ·
            refine ⟨4402339940450486584334081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2934893293633657722889387 4402339940450486584334081)
            ·
              refine ⟨3301754955337864938250561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4402339940450486584334081 3301754955337864938250561)
              ·
                refine ⟨2476316216503398703687921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3301754955337864938250561 2476316216503398703687921)
                ·
                  refine ⟨1857237162377549027765941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2476316216503398703687921 1857237162377549027765941)
                  ·
                    refine ⟨174115983972895221353057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1857237162377549027765941 174115983972895221353057)
                    ·
                      rfl

theorem cell23_1017269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 2, 2, 5].length) (baseStart_1017269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1017269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1017269 prefixEnd_1017269 := by exact prefixLift 1017269
  have htrace : WordTrace (prefixWord ++ tailWord_1017269) baseStart_1017269 baseEnd_1017269 := by
    simpa [prefixWord, tailWord_1017269, baseEnd_1017269] using wordTrace_append hprefix tailTrace_1017269
  have hstable : (prefixWord ++ tailWord_1017269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017269).length < 2 ^ (prefixWord ++ tailWord_1017269).sum := by decide
  have hdescent : baseEnd_1017269 < baseStart_1017269 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
